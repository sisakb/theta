package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.Additive;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.Divisible;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.ModExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.PosExpr;
import hu.bme.mit.theta.core.type.abstracttype.RemExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;

import static com.google.common.base.Preconditions.checkArgument;

public class FpType implements Equational<FpType>, Additive<FpType>, Multiplicative<FpType>, Divisible<FpType> {
    private final static int HASH_SEED = 5424;
    private final static String TYPE_LABEL = "Fp";

    private final int exponent;
    private final int significand;

    private volatile int hashCode = 0;

    private FpType(final int exponent, final int significand) {
        checkArgument(exponent > 1);
        checkArgument(significand > 1);
        this.exponent = exponent;
        this.significand = significand;
    }

    public static FpType of(final int exponent, final int significand) {
        return new FpType(exponent, significand);
    }

    public int getExponent() {
        return exponent;
    }

    public int getSignificand() {
        return significand;
    }

    @Override
    public EqExpr<FpType> Eq(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return FpEqExpr.of(leftOp, rightOp);
    }

    @Override
    public NeqExpr<FpType> Neq(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return FpNeqExpr.of(leftOp, rightOp);
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + exponent;
            result = 31 * result + significand;
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof FpType) {
            final FpType that = (FpType) obj;
            return this.getExponent() == that.getExponent() && this.getSignificand() == that.getSignificand();
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(TYPE_LABEL).add(exponent).add(significand).toString();
    }

    @Override
    public AddExpr<FpType> Add(Iterable<? extends Expr<FpType>> ops) {
        return FpExprs.Add(FpRoundingMode.getDefaultRoundingMode(), ops);
    }

    @Override
    public SubExpr<FpType> Sub(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return FpExprs.Sub(FpRoundingMode.getDefaultRoundingMode(), leftOp, rightOp);
    }

    @Override
    public PosExpr<FpType> Pos(Expr<FpType> op) {
        return FpExprs.Pos(op);
    }

    @Override
    public NegExpr<FpType> Neg(Expr<FpType> op) {
        return FpExprs.Neg(op);
    }

    @Override
    public MulExpr<FpType> Mul(Iterable<? extends Expr<FpType>> ops) {
        return FpExprs.Mul(FpRoundingMode.getDefaultRoundingMode(), ops);
    }

    @Override
    public DivExpr<FpType> Div(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return FpExprs.Div(FpRoundingMode.getDefaultRoundingMode(), leftOp, rightOp);
    }

    @Override
    public ModExpr<FpType> Mod(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return FpExprs.Mod();
    }

    @Override
    public RemExpr<FpType> Rem(Expr<FpType> leftOp, Expr<FpType> rightOp) {
        return FpExprs.Rem(leftOp, rightOp);
    }
}
