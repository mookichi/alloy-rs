package edu.mit.csail.sdg.translator;

import java.io.ByteArrayOutputStream;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryIntExpression;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Comprehension;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.ExprToIntCast;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IfExpression;
import kodkod.ast.IfIntExpression;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.IntToExprCast;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryExpression;
import kodkod.ast.NaryFormula;
import kodkod.ast.NotFormula;
import kodkod.ast.ProjectExpression;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.SumExpression;
import kodkod.ast.UnaryExpression;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprCastOperator;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.IntCompOperator;
import kodkod.ast.operator.IntOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.engine.Solution;
import kodkod.engine.Statistics;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import edu.mit.csail.sdg.alloy4.ErrorAPI;

/**
 * Serializes a kodkod problem (formula + bounds) into the "ARE1" wire format
 * consumed by liballoy_engine, and decodes the engine's answers back into
 * {@link Solution}s.
 *
 * Wire format v1 (see alloy-sat-rs/alloy-engine-rs/src/lib.rs for the Rust
 * side):
 *
 * <pre>
 * problem := "ARE1" bitwidth:u8 atoms rels vars nodes root:u32var
 *   atoms  := n:var (len:u16le utf8)*
 *   rels   := n:var (len:u16 utf8 arity:u8 loTs upTs)*   // request order
 *   vars   := n:var (len:u16 utf8 arity:u8)*             // VarId = index
 *   nodes  := n:var node*                                // children first
 *   ts     := n:var zigzag-tuple-index*
 * answer  := "ASAT" (n:var idx*)*per-relation | "AUNS" | "AERR" len:u16 msg
 * </pre>
 */
public final class RustSerializer {

    private RustSerializer() {}

    // ======================================================================
    // Serialization
    // ======================================================================

    /**
     * Serializes the goal formula and bounds into an ARE1 problem buffer.
     *
     * @throws ErrorAPI if the formula/bounds use constructs the Rust engine
     *             does not support yet (temporal operators, iff/implies,
     *             lone/no/one quantifiers, exotic int operators, ...)
     */
    public static byte[] serialize(Formula goal, Bounds bounds, int bitwidth) throws ErrorAPI {
        Ctx ctx = new Ctx(bounds);
        if (bitwidth < 1 || bitwidth > 30)
            throw new ErrorAPI("engine rust: bitwidth " + bitwidth + " out of range 1..=30");
        collectFormula(goal, ctx);
        W w = new W();
        w.raw("ARE1");
        w.u8(bitwidth);

        Universe uni = bounds.universe();
        w.var(uni.size());
        for (Object atom : uni)
            w.str16(atom.toString());

        List<Relation> relOrder = ctx.relOrder;
        w.var(relOrder.size());
        for (Relation r : relOrder) {
            TupleSet lo = bounds.lowerBound(r), up = bounds.upperBound(r);
            w.str16(r.name());
            w.u8(r.arity());
            writeTupleset(w, lo);
            writeTupleset(w, up);
        }

        w.var(ctx.vars.size());
        for (Variable v : ctx.vars.keySet()) {
            w.str16(v.name());
            w.u8(v.arity());
        }

        int root = emitFormula(goal, ctx, w);
        w.var(ctx.count); // number of nodes emitted
        w.var(root);
        return w.toBytes();
    }

    /** Shared per-serialization state. */
    private static final class Ctx {
        final Bounds                        bounds;
        final List<Relation>                relOrder = new ArrayList<>();
        final Map<Relation,Integer>         relIdx   = new LinkedHashMap<>();
        final Map<Variable,Integer>         vars     = new LinkedHashMap<>();
        final Map<Formula,Integer>          memoF    = new IdentityHashMap<>();
        final Map<Expression,Integer>       memoE    = new IdentityHashMap<>();
        final Map<IntExpression,Integer>    memoI    = new IdentityHashMap<>();
        final Map<Decls,Integer>            memoD    = new IdentityHashMap<>();
        int                                 count;

        Ctx(Bounds bounds) {
            this.bounds = bounds;
            for (Relation r : bounds.relations()) {
                relIdx.put(r, relOrder.size());
                relOrder.add(r);
            }
        }
    }

    private static ErrorAPI unsupported(String what) {
        return new ErrorAPI("engine rust: unsupported construct (" + what + ")");
    }

    // ---- pass 1: collect variables so the var table precedes the nodes ----

    private static void collectFormula(Formula f, Ctx ctx) throws ErrorAPI {
        if (f instanceof ConstantFormula) {
            return;
        } else if (f instanceof NotFormula) {
            collectFormula(((NotFormula) f).formula(), ctx);
        } else if (f instanceof BinaryFormula) {
            BinaryFormula b = (BinaryFormula) f;
            require(b.op());
            collectFormula(b.left(), ctx);
            collectFormula(b.right(), ctx);
        } else if (f instanceof NaryFormula) {
            NaryFormula n = (NaryFormula) f;
            require(n.op());
            for (int i = 0; i < n.size(); i++)
                collectFormula(n.child(i), ctx);
        } else if (f instanceof ComparisonFormula) {
            ComparisonFormula c = (ComparisonFormula) f;
            collectExpr(c.left(), ctx);
            collectExpr(c.right(), ctx);
        } else if (f instanceof IntComparisonFormula) {
            IntComparisonFormula c = (IntComparisonFormula) f;
            collectInt(c.left(), ctx);
            collectInt(c.right(), ctx);
        } else if (f instanceof QuantifiedFormula) {
            QuantifiedFormula q = (QuantifiedFormula) f;
            collectDecls(q.decls(), ctx);
            collectFormula(q.formula(), ctx);
        } else if (f instanceof MultiplicityFormula) {
            MultiplicityFormula m = (MultiplicityFormula) f;
            if (m.multiplicity() == Multiplicity.NO)
                throw unsupported("no-expression formula");
            collectExpr(m.expression(), ctx);
        } else {
            throw unsupported("formula construct " + f.getClass().getSimpleName());
        }
    }

    private static void collectExpr(Expression e, Ctx ctx) throws ErrorAPI {
        if (e instanceof Variable) {
            ctx.vars.putIfAbsent((Variable) e, ctx.vars.size());
        } else if (e instanceof UnaryExpression) {
            collectExpr(((UnaryExpression) e).expression(), ctx);
        } else if (e instanceof BinaryExpression) {
            BinaryExpression b = (BinaryExpression) e;
            collectExpr(b.left(), ctx);
            collectExpr(b.right(), ctx);
        } else if (e instanceof NaryExpression) {
            for (Expression c : (NaryExpression) e)
                collectExpr(c, ctx);
        } else if (e instanceof IfExpression) {
            IfExpression i = (IfExpression) e;
            collectFormula(i.condition(), ctx);
            collectExpr(i.thenExpr(), ctx);
            collectExpr(i.elseExpr(), ctx);
        } else if (e instanceof ProjectExpression) {
            ProjectExpression p = (ProjectExpression) e;
            collectExpr(p.expression(), ctx);
            for (java.util.Iterator<IntExpression> it = p.columns(); it.hasNext();)
                collectInt(it.next(), ctx);
        } else if (e instanceof Comprehension) {
            Comprehension c = (Comprehension) e;
            collectDecls(c.decls(), ctx);
            collectFormula(c.formula(), ctx);
        } else if (e instanceof IntToExprCast) {
            collectInt(((IntToExprCast) e).intExpr(), ctx);
        } else if (!(e == Expression.UNIV || e == Expression.IDEN || e == Expression.NONE
                || e == Expression.INTS || e instanceof Relation)) {
            throw unsupported("expression construct " + e.getClass().getSimpleName());
        }
    }

    private static void collectInt(IntExpression i, Ctx ctx) throws ErrorAPI {
        if (i instanceof ExprToIntCast) {
            collectExpr(((ExprToIntCast) i).expression(), ctx);
        } else if (i instanceof BinaryIntExpression) {
            require(((BinaryIntExpression) i).op());
            collectInt(((BinaryIntExpression) i).left(), ctx);
            collectInt(((BinaryIntExpression) i).right(), ctx);
        } else if (i instanceof IfIntExpression) {
            IfIntExpression x = (IfIntExpression) i;
            collectFormula(x.condition(), ctx);
            collectInt(x.thenExpr(), ctx);
            collectInt(x.elseExpr(), ctx);
        } else if (i instanceof SumExpression) {
            SumExpression s = (SumExpression) i;
            collectDecls(s.decls(), ctx);
            collectInt(s.intExpr(), ctx);
        } else if (!(i instanceof IntConstant)) {
            throw unsupported("integer expression " + i.getClass().getSimpleName());
        }
    }

    private static void collectDecls(Decls d, Ctx ctx) throws ErrorAPI {
        for (Decl decl : d) {
            ctx.vars.putIfAbsent(decl.variable(), ctx.vars.size());
            collectExpr(decl.expression(), ctx);
        }
    }

    private static void require(FormulaOperator op) throws ErrorAPI {
        if (op != FormulaOperator.AND && op != FormulaOperator.OR)
            throw unsupported(op.toString() + " formula");
    }

    private static void require(IntOperator op) throws ErrorAPI {
        switch (op) {
            case PLUS, MINUS, MULTIPLY, DIVIDE, MODULO, AND, OR, XOR, SHL, SHR:
                return;
            default:
                throw unsupported("integer operator " + op);
        }
    }

    // ---- pass 2: emit nodes post-order (children get lower ids) ----

    private static int emitFormula(Formula f, Ctx ctx, W w) throws ErrorAPI {
        Integer m = ctx.memoF.get(f);
        if (m != null)
            return m;
        int id;
        if (f instanceof ConstantFormula) {
            id = ctx.count++;
            w.var(id);
            w.var(0L);
            w.u8((byte) (((ConstantFormula) f).booleanValue() ? 1 : 0));
        } else if (f instanceof NotFormula) {
            int c = emitFormula(((NotFormula) f).formula(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(1L);
            w.var(c);
        } else if (f instanceof BinaryFormula) {
            BinaryFormula b = (BinaryFormula) f;
            require(b.op());
            int l = emitFormula(b.left(), ctx, w), r = emitFormula(b.right(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(2L);
            w.u8((byte) (b.op() == FormulaOperator.AND ? 0 : 1));
            w.var(2);
            w.var(l);
            w.var(r);
        } else if (f instanceof NaryFormula) {
            NaryFormula n = (NaryFormula) f;
            require(n.op());
            int[] kids = new int[n.size()];
            for (int i = 0; i < kids.length; i++)
                kids[i] = emitFormula(n.child(i), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(2L);
            w.u8((byte) (n.op() == FormulaOperator.AND ? 0 : 1));
            w.var(kids.length);
            for (int k : kids)
                w.var(k);
        } else if (f instanceof ComparisonFormula) {
            ComparisonFormula c = (ComparisonFormula) f;
            boolean eq = c.op() == ExprCompOperator.EQUALS;
            if (!eq && c.op() != ExprCompOperator.SUBSET)
                throw unsupported("comparison operator " + c.op());
            int l = emitExpr(c.left(), ctx, w), r = emitExpr(c.right(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(3L);
            w.u8((byte) (eq ? 1 : 0));
            w.var(l);
            w.var(r);
        } else if (f instanceof IntComparisonFormula) {
            IntComparisonFormula c = (IntComparisonFormula) f;
            int l = emitInt(c.left(), ctx, w), r = emitInt(c.right(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(4L);
            w.u8((byte) c.op().ordinal()); // EQ NEQ LT LTE GT GTE
            w.var(l);
            w.var(r);
        } else if (f instanceof QuantifiedFormula) {
            QuantifiedFormula q = (QuantifiedFormula) f;
            if (q.quantifier() != Quantifier.ALL && q.quantifier() != Quantifier.SOME)
                throw unsupported(q.quantifier() + " quantifier");
            int d = emitDecls(q.decls(), ctx, w), b = emitFormula(q.formula(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(5L);
            w.u8((byte) (q.quantifier() == Quantifier.ALL ? 0 : 1));
            w.var(d);
            w.var(b);
        } else if (f instanceof MultiplicityFormula) {
            MultiplicityFormula mf = (MultiplicityFormula) f;
            Multiplicity mult = mf.multiplicity();
            if (mult == Multiplicity.NO)
                throw unsupported("no-expression formula");
            int e = emitExpr(mf.expression(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(6L);
            w.u8((byte) (mult == Multiplicity.SOME ? 0 : mult == Multiplicity.LONE ? 1 : 2));
            w.var(e);
        } else {
            throw unsupported("formula construct " + f.getClass().getSimpleName());
        }
        ctx.memoF.put(f, id);
        return id;
    }

    private static int emitExpr(Expression e, Ctx ctx, W w) throws ErrorAPI {
        Integer m = ctx.memoE.get(e);
        if (m != null)
            return m;
        int id;
        if (e instanceof Relation) {
            Integer ri = ctx.relIdx.get(e);
            if (ri == null)
                throw unsupported("unbounded relation " + ((Relation) e).name());
            id = ctx.count++;
            w.var(id);
            w.var(32L);
            w.var(ri);
        } else if (e instanceof Variable) {
            id = ctx.count++;
            w.var(id);
            w.var(33L);
            w.var(ctx.vars.get(e));
        } else if (e == Expression.UNIV || e == Expression.IDEN || e == Expression.NONE
                || e == Expression.INTS) {
            int code = e == Expression.UNIV ? 0 : e == Expression.IDEN ? 1 : e == Expression.NONE ? 2 : 3;
            id = ctx.count++;
            w.var(id);
            w.var(34L);
            w.u8((byte) code);
        } else if (e instanceof UnaryExpression) {
            UnaryExpression u = (UnaryExpression) e;
            int op;
            switch (u.op()) {
                case TRANSPOSE:
                    op = 0;
                    break;
                case CLOSURE:
                    op = 1;
                    break;
                case REFLEXIVE_CLOSURE:
                    op = 2;
                    break;
                default:
                    throw unsupported("unary operator " + u.op());
            }
            int c = emitExpr(u.expression(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(35L);
            w.u8((byte) op);
            w.var(c);
        } else if (e instanceof BinaryExpression || e instanceof NaryExpression) {
            ExprOperator op;
            Expression[] kids;
            if (e instanceof BinaryExpression) {
                BinaryExpression b = (BinaryExpression) e;
                op = b.op();
                kids = new Expression[] { b.left(), b.right() };
            } else {
                NaryExpression n = (NaryExpression) e;
                op = n.op();
                List<Expression> cs = new ArrayList<>();
                for (Expression c : n)
                    cs.add(c);
                kids = cs.toArray(new Expression[0]);
            }
            if (op != ExprOperator.UNION && op != ExprOperator.INTERSECTION && op != ExprOperator.OVERRIDE
                    && op != ExprOperator.DIFFERENCE && op != ExprOperator.PRODUCT && op != ExprOperator.JOIN)
                throw unsupported("expression operator " + op);
            int[] ks = new int[kids.length];
            for (int i = 0; i < ks.length; i++)
                ks[i] = emitExpr(kids[i], ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(36L);
            w.u8((byte) exprOpCode(op)); // UNION..JOIN, explicit (enum order differs)
            w.var(ks.length);
            for (int k : ks)
                w.var(k);
        } else if (e instanceof IfExpression) {
            IfExpression x = (IfExpression) e;
            int c = emitFormula(x.condition(), ctx, w);
            int t = emitExpr(x.thenExpr(), ctx, w);
            int el = emitExpr(x.elseExpr(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(37L);
            w.var(c);
            w.var(t);
            w.var(el);
        } else if (e instanceof ProjectExpression) {
            ProjectExpression p = (ProjectExpression) e;
            int src = emitExpr(p.expression(), ctx, w);
            List<Integer> cols = new ArrayList<>();
            for (java.util.Iterator<IntExpression> it = p.columns(); it.hasNext();)
                cols.add(emitInt(it.next(), ctx, w));
            id = ctx.count++;
            w.var(id);
            w.var(38L);
            w.var(src);
            w.var(cols.size());
            for (int c : cols)
                w.var(c);
        } else if (e instanceof Comprehension) {
            Comprehension c = (Comprehension) e;
            int d = emitDecls(c.decls(), ctx, w), b = emitFormula(c.formula(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(39L);
            w.var(d);
            w.var(b);
        } else if (e instanceof IntToExprCast) {
            int c = emitInt(((IntToExprCast) e).intExpr(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(40L);
            w.var(c);
        } else {
            throw unsupported("expression construct " + e.getClass().getSimpleName());
        }
        ctx.memoE.put(e, id);
        return id;
    }

    private static int emitInt(IntExpression x, Ctx ctx, W w) throws ErrorAPI {
        Integer m = ctx.memoI.get(x);
        if (m != null)
            return m;
        int id;
        if (x instanceof IntConstant) {
            id = ctx.count++;
            w.var(id);
            w.var(64L);
            w.svar(((IntConstant) x).value());
        } else if (x instanceof ExprToIntCast) {
            ExprToIntCast c = (ExprToIntCast) x;
            boolean sum = c.op() == ExprCastOperator.SUM;
            int e = emitExpr(c.expression(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(65L);
            w.u8((byte) (sum ? 1 : 0)); // CARDINALITY | SUM
            w.var(e);
        } else if (x instanceof BinaryIntExpression) {
            BinaryIntExpression b = (BinaryIntExpression) x;
            require(b.op());
            int l = emitInt(b.left(), ctx, w), r = emitInt(b.right(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(66L);
            w.u8((byte) intOpCode(b.op()));
            w.var(l);
            w.var(r);
        } else if (x instanceof IfIntExpression) {
            IfIntExpression y = (IfIntExpression) x;
            int c = emitFormula(y.condition(), ctx, w);
            int t = emitInt(y.thenExpr(), ctx, w);
            int el = emitInt(y.elseExpr(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(67L);
            w.var(c);
            w.var(t);
            w.var(el);
        } else if (x instanceof SumExpression) {
            SumExpression s = (SumExpression) x;
            int d = emitDecls(s.decls(), ctx, w), b = emitInt(s.intExpr(), ctx, w);
            id = ctx.count++;
            w.var(id);
            w.var(68L);
            w.var(d);
            w.var(b);
        } else {
            throw unsupported("integer expression " + x.getClass().getSimpleName());
        }
        ctx.memoI.put(x, id);
        return id;
    }

    private static int intOpCode(IntOperator op) {
        switch (op) {
            case PLUS:
                return 0;
            case MINUS:
                return 1;
            case MULTIPLY:
                return 2;
            case DIVIDE:
                return 3;
            case MODULO:
                return 4;
            case AND:
                return 5;
            case OR:
                return 6;
            case XOR:
                return 7;
            case SHL:
                return 8;
            case SHR:
                return 9;
            default:
                throw new IllegalStateException(op.toString());
        }
    }

    private static int exprOpCode(ExprOperator op) {
        switch (op) {
            case UNION:
                return 0;
            case INTERSECTION:
                return 1;
            case OVERRIDE:
                return 2;
            case DIFFERENCE:
                return 3; // wire order: DIFFERENCE before PRODUCT
            case PRODUCT:
                return 4;
            case JOIN:
                return 5;
            default:
                throw new IllegalStateException(op.toString());
        }
    }

    private static int emitDecls(Decls d, Ctx ctx, W w) throws ErrorAPI {
        Integer m = ctx.memoD.get(d);
        if (m != null)
            return m;
        List<int[]> entries = new ArrayList<>();
        for (Decl decl : d) {
            Multiplicity mult = decl.multiplicity();
            byte code;
            if (mult == Multiplicity.SOME)
                code = 0;
            else if (mult == Multiplicity.LONE)
                code = 1;
            else if (mult == Multiplicity.ONE)
                code = 2;
            else if (mult == Multiplicity.SET)
                code = 3;
            else
                throw unsupported("declaration multiplicity " + mult);
            Integer vi = ctx.vars.get(decl.variable());
            if (vi == null)
                throw unsupported("undeclared variable " + decl.variable().name());
            int e = emitExpr(decl.expression(), ctx, w);
            entries.add(new int[] { code, vi, e });
        }
        int id = ctx.count++;
        w.var(id);
        w.var(96L);
        w.var(entries.size());
        for (int[] en : entries) {
            w.u8((byte) en[0]);
            w.var(en[1]);
            w.var(en[2]);
        }
        ctx.memoD.put(d, id);
        return id;
    }

    private static void writeTupleset(W w, TupleSet ts) {
        w.var(ts.size());
        for (Tuple t : ts) {
            long dense = 0;
            for (int i = 0; i < t.arity(); i++)
                dense = dense * ts.universe().size() + t.atomIndex(i);
            w.svar(dense);
        }
    }

    // ======================================================================
    // Answer decoding
    // ======================================================================

    /**
     * Decodes an engine answer into a {@link Solution}.
     *
     * @param answer raw engine output (ASAT/AUNS/AERR payload)
     * @param bounds the bounds used at serialization time (relation order must
     *            match)
     * @param translateNs time spent in serialization (for the stats display)
     * @param solveNs time spent inside the native engine
     * @throws ErrorAPI on engine errors or malformed answers
     */
    public static Solution readAnswer(byte[] answer, Bounds bounds, long translateNs,
            long solveNs) throws ErrorAPI {
        if (answer == null)
            throw new ErrorAPI("engine rust: no answer (native call failed)");
        Statistics stats = new Statistics(0, 0, 0, translateNs / 1_000_000L, solveNs / 1_000_000L);
        R r = new R(answer);
        String magic = r.magic();
        switch (magic) {
            case "AUNS":
                return Solution.unsatisfiable(stats, null);
            case "AERR":
                throw new ErrorAPI("engine rust: " + r.str16());
            case "ASAT":
                break;
            default:
                throw new ErrorAPI("engine rust: bad answer magic " + magic);
        }
        Instance inst = new Instance(bounds.universe());
        for (Relation rel : bounds.relations()) {
            int arity = rel.arity();
            int n = (int) r.var();
            TupleSet ts = bounds.universe().factory().noneOf(arity);
            for (int i = 0; i < n; i++) {
                long idx = r.svar();
                ts.add(bounds.universe().factory().tuple(arity, (int) idx));
            }
            inst.add(rel, ts);
        }
        return Solution.satisfiable(stats, inst);
    }

    // ======================================================================
    // Byte helpers
    // ======================================================================

    private static final class W {
        private final ByteArrayOutputStream out = new ByteArrayOutputStream();

        void raw(String s) {
            out.writeBytes(s.getBytes(java.nio.charset.StandardCharsets.US_ASCII));
        }

        byte[] toBytes() {
            return out.toByteArray();
        }

        void u8(int v) {
            out.write(v & 0xff);
        }

        void str16(String s) {
            byte[] b = s.getBytes(java.nio.charset.StandardCharsets.UTF_8);
            if (b.length > 0xffff)
                throw new IllegalArgumentException("string too long: " + s);
            u8(b.length);
            u8(b.length >> 8);
            out.writeBytes(b);
        }

        void var(long v) {
            while (true) {
                int b = (int) (v & 0x7f);
                v >>>= 7;
                if (v == 0) {
                    out.write(b);
                    return;
                }
                out.write(b | 0x80);
            }
        }

        void svar(long v) {
            var((v << 1) ^ (v >> 63));
        }
    }

    private static final class R {
        private final byte[] buf;
        private int          pos;

        R(byte[] buf) {
            this.buf = buf;
        }

        String magic() {
            StringBuilder sb = new StringBuilder(4);
            for (int i = 0; i < 4; i++) {
                if (pos >= buf.length)
                    return "";
                sb.append((char) (buf[pos++] & 0xff));
            }
            return sb.toString();
        }

        String str16() {
            int len = u8() | (u8() << 8);
            String s = new String(buf, pos, len, java.nio.charset.StandardCharsets.UTF_8);
            pos += len;
            return s;
        }

        int u8() {
            return buf[pos++] & 0xff;
        }

        long var() {
            long out = 0;
            int shift = 0;
            while (true) {
                int b = u8();
                out |= (long) (b & 0x7f) << shift;
                if ((b & 0x80) == 0)
                    return out;
                shift += 7;
            }
        }

        long svar() {
            long z = var();
            return (z >>> 1) ^ -(z & 1);
        }
    }
}
