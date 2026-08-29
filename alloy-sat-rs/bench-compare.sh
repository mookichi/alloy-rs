#!/bin/bash
# Rust vs Java speed comparison for Alloy
set -euo pipefail

REPO_ROOT="/run/media/mookichi/ssd2/dev/alloy-rs"
JAR="$REPO_ROOT/org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar"
JAVA="/home/mookichi/.sdkman/candidates/java/25-amzn/bin/java"
RUST_BIN="$REPO_ROOT/alloy-sat-rs/target/release/als"
MODELS_DIR="$REPO_ROOT/org.alloytools.alloy.extra/extra/models/book/appendixA"

# Models that both Rust and Java can solve
MODELS=(
  "ring.als"
  "tube.als"
  "undirected.als"
  "prison.als"
)

echo "=== Alloy Speed Comparison: Rust vs Java ==="
echo "Java: $($JAVA -version 2>&1 | head -1)"
echo "Rust: $(rustc --version)"
echo ""

# Build Rust binary (release)
echo "--- Building Rust binary (release) ---"
(cd "$REPO_ROOT/alloy-sat-rs" && cargo build -q --release -p alloy-front-rs --bin als 2>&1)
echo ""

# Warm up JVM
echo "--- Warming up JVM ---"
for f in "${MODELS[@]}"; do
  $JAVA -jar "$JAR" exec --quiet --output - "$MODELS_DIR/$f" >/dev/null 2>&1 || true
done
echo ""

echo "--- Benchmark Results (3 runs each, median) ---"
echo ""
printf "%-20s %12s %12s %10s\n" "Model" "Java (ms)" "Rust (ms)" "Speedup"
printf "%-20s %12s %12s %10s\n" "-----" "---------" "---------" "-------"

for f in "${MODELS[@]}"; do
  path="$MODELS_DIR/$f"
  name="${f%.als}"
  
  # Run 3 times, collect times
  java_times=()
  rust_times=()
  
  for run in 1 2 3; do
    # Java timing (stderr from --timing)
    java_out=$($JAVA -jar "$JAR" exec --timing --output - "$path" 2>&1)
    java_ms=$(echo "$java_out" | grep -oP 'total=\K[0-9.]+' || echo "0")
    java_times+=("$java_ms")
    
    # Rust timing (--timing flag)
    rust_out=$($RUST_BIN --timing "$path" 2>&1)
    # Get the total line and sum parse+lower+solve
    rust_total_line=$(echo "$rust_out" | grep '^--- total' || echo "")
    rust_ms="0"
    if [ -n "$rust_total_line" ]; then
      # Extract individual times and sum them
      parse_us=$(echo "$rust_total_line" | grep -oP 'parse=\K[0-9]+' || echo "0")
      lower_us=$(echo "$rust_total_line" | grep -oP 'lower=\K[0-9]+' || echo "0")
      solve_us=$(echo "$rust_total_line" | grep -oP 'solve=\K[0-9]+' || echo "0")
      # Check units
      if echo "$rust_total_line" | grep -qP 'parse=[0-9]+ µs'; then
        parse_us=$(echo "$rust_total_line" | grep -oP 'parse=\K[0-9]+')
        lower_us=$(echo "$rust_total_line" | grep -oP 'lower=\K[0-9]+')
        solve_us=$(echo "$rust_total_line" | grep -oP 'solve=\K[0-9]+')
        total_us=$((parse_us + lower_us + solve_us))
        rust_ms=$(echo "scale=3; $total_us / 1000" | bc -l)
      elif echo "$rust_total_line" | grep -qP 'parse=[0-9.]+ ms'; then
        parse_ms=$(echo "$rust_total_line" | grep -oP 'parse=\K[0-9.]+')
        lower_ms=$(echo "$rust_total_line" | grep -oP 'lower=\K[0-9.]+')
        solve_ms=$(echo "$rust_total_line" | grep -oP 'solve=\K[0-9.]+')
        rust_ms=$(echo "scale=3; $parse_ms + $lower_ms + $solve_ms" | bc -l)
      elif echo "$rust_total_line" | grep -qP 'parse=[0-9.]+ s'; then
        parse_s=$(echo "$rust_total_line" | grep -oP 'parse=\K[0-9.]+')
        lower_s=$(echo "$rust_total_line" | grep -oP 'lower=\K[0-9.]+')
        solve_s=$(echo "$rust_total_line" | grep -oP 'solve=\K[0-9.]+')
        total_s=$(echo "$parse_s + $lower_s + $solve_s" | bc -l)
        rust_ms=$(echo "scale=1; $total_s * 1000" | bc -l)
      fi
    fi
    rust_times+=("$rust_ms")
  done
  
  # Get median (2nd element of sorted)
  java_median=$(printf '%s\n' "${java_times[@]}" | sort -n | sed -n '2p')
  rust_median=$(printf '%s\n' "${rust_times[@]}" | sort -n | sed -n '2p')
  
  # Calculate speedup
  if [ "$(echo "$rust_median > 0" | bc -l)" = "1" ] && [ "$(echo "$java_median > 0" | bc -l)" = "1" ]; then
    speedup=$(echo "scale=1; $java_median / $rust_median" | bc -l)
    printf "%-20s %12s %12s %9sx\n" "$name" "$java_median" "$rust_median" "$speedup"
  else
    printf "%-20s %12s %12s %10s\n" "$name" "$java_median" "$rust_median" "N/A"
  fi
done

echo ""
echo "--- Notes ---"
echo "Java: parse=lex+resolve+lower, solve=Kodkod FOL->CNF->SAT->materialize"
echo "Rust: parse=lex+parse, lower=resolve+lower, solve=FOL->CNF->SAT->materialize"
echo "Java total includes overhead for stdout output generation"
