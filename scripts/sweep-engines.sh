#!/usr/bin/env bash
# Iter 10 acceptance sweep: run every example model through both engines
# (--engine rust vs default Java) and compare outcomes.
# Results: alloy-sat-rs/docs/engine-sweep-results.txt ("name|rust|java").
#
# Usage: ./scripts/sweep-engines.sh   (from the repository root)
set -u
DIST=org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar
JAVA25="${JAVA_HOME:-$HOME/.sdkman/candidates/java/25-amzn}/bin/java"
SO=${ALLOY_ENGINE_SO:-/run/media/mookichi/ssd2/dev/alloy-rs/alloy-sat-rs/target/release/liballoy_engine.so}
OUT=alloy-sat-rs/docs/engine-sweep-results.txt
mkdir -p /tmp/opencode/sweep/rust /tmp/opencode/sweep/java
: > "$OUT"

for f in $(find org.alloytools.alloy.extra/extra/models -name "*.als" | sort); do
  name=$(basename "$f")
  r=$(timeout 120 "$JAVA25" -Dalloy.native.lib.alloy_engine="$SO" -jar "$DIST" \
        exec --engine rust --output /tmp/opencode/sweep/rust -f "$f" 2>&1 \
      | grep -oE "SAT|UNSAT|Error" | head -1)
  j=$(timeout 120 "$JAVA25" -jar "$DIST" \
        exec --output /tmp/opencode/sweep/java -f "$f" 2>&1 \
      | grep -oE "SAT|UNSAT|Error" | head -1)
  echo "$name|$r|$j" >> "$OUT"
done
column -t -s'|' "$OUT"
