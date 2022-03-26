/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.cat.dsl;

import hu.bme.mit.theta.cat.dsl.gen.CatBaseVisitor;
import hu.bme.mit.theta.cat.dsl.gen.CatParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class CatDslVisitor extends CatBaseVisitor<Datalog.Relation> {
    private static final String[] unaryBasicExpressions = new String[] {"W", "R", "F"};
    private static final String[] binaryBasicExpressions = new String[] {"po", "rf"};

    private final Datalog datalogProgram;
    private final Datalog.Relation mustBeEmpty;
    private int ruleNameCnt = 0;

    public CatDslVisitor() {
        this.datalogProgram = Datalog.createProgram();
        mustBeEmpty = datalogProgram.createRelation("mustBeEmpty", 2);

        for (String unaryBasicExpression : unaryBasicExpressions) {
            datalogProgram.createRelation(unaryBasicExpression, 1);
        }
        for (String binaryBasicExpression : binaryBasicExpressions) {
            datalogProgram.createRelation(binaryBasicExpression, 2);
        }
    }

    @Override
    public Datalog.Relation visitAcyclicDefinition(CatParser.AcyclicDefinitionContext ctx) {
        final Datalog.Relation baseRelation = ctx.e.accept(this);
        final Datalog.Relation transitive = datalogProgram.createTransitive(ctx.NAME() == null ? "acyclic_" + ruleNameCnt++ : ctx.NAME().getText(), baseRelation);
        final Datalog.Variable var = datalogProgram.getVariable();
        mustBeEmpty.addRule(TupleN.of(var, var), Set.of(Tuple2.of(transitive, TupleN.of(var, var))));
        return mustBeEmpty;
    }

    @Override
    public Datalog.Relation visitIrreflexiveDefinition(CatParser.IrreflexiveDefinitionContext ctx) {
        final Datalog.Relation baseRelation = ctx.e.accept(this);
        final Datalog.Variable var1 = datalogProgram.getVariable();
        final Datalog.Variable var2 = datalogProgram.getVariable();
        mustBeEmpty.addRule(TupleN.of(var1, var2), Set.of(Tuple2.of(baseRelation, TupleN.of(var1, var2)), Tuple2.of(baseRelation, TupleN.of(var2, var1))));
        return mustBeEmpty;
    }

    @Override
    public Datalog.Relation visitEmptyDefinition(CatParser.EmptyDefinitionContext ctx) {
        final Datalog.Relation baseRelation = ctx.e.accept(this);
        final Datalog.Variable var1 = datalogProgram.getVariable();
        final Datalog.Variable var2 = datalogProgram.getVariable();
        mustBeEmpty.addRule(TupleN.of(var1, var2), Set.of(Tuple2.of(baseRelation, TupleN.of(var1, var2))));
        return mustBeEmpty;
    }

    @Override
    public Datalog.Relation visitLetDefinition(CatParser.LetDefinitionContext ctx) {
        final Datalog.Relation baseRelation = ctx.e.accept(this);
        final Datalog.Relation relation = datalogProgram.createRelation(ctx.n.getText(), baseRelation.getArity());
        List<Datalog.Variable> args = new ArrayList<>();
        for (int i = 0; i < baseRelation.getArity(); i++) {
            args.add(datalogProgram.getVariable());
        }
        relation.addRule(TupleN.of(args), Set.of(Tuple2.of(baseRelation, TupleN.of(args))));
        return relation;
    }

    @Override
    public Datalog.Relation visitLetRecDefinition(CatParser.LetRecDefinitionContext ctx) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Datalog.Relation visitExprCartesian(CatParser.ExprCartesianContext ctx) {
        final Datalog.Relation baseRelation1 = ctx.e1.accept(this);
        final Datalog.Relation baseRelation2 = ctx.e2.accept(this);
        if(baseRelation1.getArity() != 1 || baseRelation2.getArity() != baseRelation1.getArity()) throw new UnsupportedOperationException("Only unary relations are supported");
        final Datalog.Variable var1 = datalogProgram.getVariable();
        final Datalog.Variable var2 = datalogProgram.getVariable();
        final Datalog.Relation relation = datalogProgram.createRelation("rule_" + ruleNameCnt++, 2);
        relation.addRule(TupleN.of(var1, var2), Set.of(Tuple2.of(baseRelation1, TupleN.of(var1)), Tuple2.of(baseRelation2, TupleN.of(var2))));
        return relation;
    }

    @Override
    public Datalog.Relation visitExprRangeIdentity(CatParser.ExprRangeIdentityContext ctx) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public Datalog.Relation visitExprBasic(CatParser.ExprBasicContext ctx) {
        final Map<String, Datalog.Relation> relations = datalogProgram.getRelations();
    }

    @Override
    public Datalog.Relation visitExprMinus(CatParser.ExprMinusContext ctx) {
        return super.visitExprMinus(ctx);
    }

    @Override
    public Datalog.Relation visitExprUnion(CatParser.ExprUnionContext ctx) {
        return super.visitExprUnion(ctx);
    }

    @Override
    public Datalog.Relation visitExprComposition(CatParser.ExprCompositionContext ctx) {
        return super.visitExprComposition(ctx);
    }

    @Override
    public Datalog.Relation visitExprIntersection(CatParser.ExprIntersectionContext ctx) {
        return super.visitExprIntersection(ctx);
    }

    @Override
    public Datalog.Relation visitExprTransitive(CatParser.ExprTransitiveContext ctx) {
        return super.visitExprTransitive(ctx);
    }

    @Override
    public Datalog.Relation visitExprComplement(CatParser.ExprComplementContext ctx) {
        return super.visitExprComplement(ctx);
    }

    @Override
    public Datalog.Relation visitExprInverse(CatParser.ExprInverseContext ctx) {
        return super.visitExprInverse(ctx);
    }

    @Override
    public Datalog.Relation visitExprDomainIdentity(CatParser.ExprDomainIdentityContext ctx) {
        return super.visitExprDomainIdentity(ctx);
    }

    @Override
    public Datalog.Relation visitExprIdentity(CatParser.ExprIdentityContext ctx) {
        return super.visitExprIdentity(ctx);
    }

    @Override
    public Datalog.Relation visitExprTransRef(CatParser.ExprTransRefContext ctx) {
        return super.visitExprTransRef(ctx);
    }

    @Override
    public Datalog.Relation visitExprFencerel(CatParser.ExprFencerelContext ctx) {
        return super.visitExprFencerel(ctx);
    }

    @Override
    public Datalog.Relation visitExpr(CatParser.ExprContext ctx) {
        return super.visitExpr(ctx);
    }

    @Override
    public Datalog.Relation visitExprOptional(CatParser.ExprOptionalContext ctx) {
        return super.visitExprOptional(ctx);
    }
}
