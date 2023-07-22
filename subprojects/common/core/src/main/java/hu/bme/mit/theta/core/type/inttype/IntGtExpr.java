/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.type.inttype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.GtExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class IntGtExpr extends GtExpr<IntType> {

    private static final int HASH_SEED = 7349;
    private static final String OPERATOR_LABEL = ">";

    private IntGtExpr(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
        super(leftOp, rightOp);
    }

    public static IntGtExpr of(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
        return new IntGtExpr(leftOp, rightOp);
    }

    public static IntGtExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
        final Expr<IntType> newLeftOp = cast(leftOp, Int());
        final Expr<IntType> newRightOp = cast(rightOp, Int());
        return IntGtExpr.of(newLeftOp, newRightOp);
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public BoolLitExpr eval(final Valuation val) {
        final IntLitExpr leftOpVal = (IntLitExpr) getLeftOp().eval(val);
        final IntLitExpr rightOpVal = (IntLitExpr) getRightOp().eval(val);
        return leftOpVal.gt(rightOpVal);
    }

    @Override
    public IntGtExpr with(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return IntGtExpr.of(leftOp, rightOp);
        }
    }

    @Override
    public IntGtExpr withLeftOp(final Expr<IntType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public IntGtExpr withRightOp(final Expr<IntType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final IntGtExpr that = (IntGtExpr) obj;
            return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp()
                    .equals(that.getRightOp());
        } else {
            return false;
        }
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }

}
