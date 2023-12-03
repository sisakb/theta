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
package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Type;

import java.util.Collection;

final class VarCollectorStmtVisitorWithoutAddrOf implements StmtVisitor<Collection<VarDecl<?>>, Void> {

    private static final class LazyHolder {

        private final static VarCollectorStmtVisitorWithoutAddrOf INSTANCE = new VarCollectorStmtVisitorWithoutAddrOf();
    }

    private VarCollectorStmtVisitorWithoutAddrOf() {
    }

    static VarCollectorStmtVisitorWithoutAddrOf getInstance() {
        return LazyHolder.INSTANCE;
    }

    @Override
    public Void visit(final SkipStmt stmt, final Collection<VarDecl<?>> vars) {
        return null;
    }

    @Override
    public Void visit(final AssumeStmt stmt, final Collection<VarDecl<?>> vars) {
        ExprUtils.collectVarsWithoutAddrOf(stmt.getCond(), vars);
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(final AssignStmt<DeclType> stmt,
                                              final Collection<VarDecl<?>> vars) {
        vars.add(stmt.getVarDecl());
        ExprUtils.collectVarsWithoutAddrOf(stmt.getExpr(), vars);
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(final HavocStmt<DeclType> stmt,
                                              final Collection<VarDecl<?>> vars) {
        vars.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(SequenceStmt stmt, Collection<VarDecl<?>> vars) {
        for (Stmt subStmt : stmt.getStmts()) {
            subStmt.accept(VarCollectorStmtVisitorWithoutAddrOf.getInstance(), vars);
        }
        return null;
    }

    @Override
    public Void visit(NonDetStmt stmt, Collection<VarDecl<?>> vars) {
        for (Stmt subStmt : stmt.getStmts()) {
            subStmt.accept(VarCollectorStmtVisitorWithoutAddrOf.getInstance(), vars);
        }
        return null;
    }

    @Override
    public Void visit(OrtStmt stmt, Collection<VarDecl<?>> vars) {
        for (Stmt subStmt : stmt.getStmts()) {
            subStmt.accept(VarCollectorStmtVisitorWithoutAddrOf.getInstance(), vars);
        }
        return null;
    }

    @Override
    public Void visit(LoopStmt stmt, Collection<VarDecl<?>> vars) {
        ExprUtils.collectVarsWithoutAddrOf(stmt.getFrom(), vars);
        ExprUtils.collectVarsWithoutAddrOf(stmt.getTo(), vars);
        vars.add(stmt.getLoopVariable());
        return stmt.getStmt().accept(VarCollectorStmtVisitorWithoutAddrOf.getInstance(), vars);
    }

    public Void visit(IfStmt stmt, Collection<VarDecl<?>> vars) {
        ExprUtils.collectVarsWithoutAddrOf(stmt.getCond(), vars);
        stmt.getThen().accept(VarCollectorStmtVisitorWithoutAddrOf.getInstance(), vars);
        stmt.getElze().accept(VarCollectorStmtVisitorWithoutAddrOf.getInstance(), vars);
        return null;
    }

    @Override
    public Void visit(DerefWriteStmt stmt, Collection<VarDecl<?>> vars) {
        ExprUtils.collectVarsWithoutAddrOf(stmt.getDeRef(), vars);
        ExprUtils.collectVarsWithoutAddrOf(stmt.getExpr(), vars);
        return null;
    }

    @Override
    public Void visit(PointerDereffedStmt stmt, Collection<VarDecl<?>> param) {
        return null;
    }

}
