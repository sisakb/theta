/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.EdgeContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.LocContext;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.VarDeclContext;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

final class XcfaProcedureSymbol implements Symbol, Scope, Instantiatable<XCFA.Process.Procedure> {


	private final XcfaProcessSymbol scope;
	private final SymbolTable symbolTable;

	private final String name;
	private final boolean main;
	private final Type rtype;
	private final List<XcfaParamSymbol> params;
	private final List<XcfaVariableSymbol> variables;
	private final List<XcfaLocationSymbol> locations;
	private final List<XcfaEdgeDefinition> edges;

	XcfaProcedureSymbol(final XcfaProcessSymbol scope, final XcfaDslParser.ProcedureDeclContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);
		symbolTable = new SymbolTable();

		name = context.id.getText();
		main = (context.main != null);
		variables = createVariables(context.varDecls);
		params = createParams(context.paramDecls.decls);
		locations = createLocations(context.locs);
		edges = createEdges(context.edges);
		rtype = new XcfaType(context.rtype).instantiate();

		declareAll(variables);
		declareAll(params);
		declareAll(locations);
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isMain() {
		return main;
	}

	////

	public XCFA.Process.Procedure instantiate() {
		XCFA.Process.Procedure.Builder builder = XCFA.Process.Procedure.builder();
		builder.setRtype(rtype);
		params.forEach(xcfaParamSymbol -> builder.createParam(xcfaParamSymbol.instantiate()));
		variables.forEach(xcfaVariableSymbol -> builder.createVar(xcfaVariableSymbol.instantiate()));
		locations.forEach(xcfaLocationSymbol -> {
			XCFA.Process.Procedure.Location loc = builder.createLoc(xcfaLocationSymbol.getName(), null); //TODO dictionary
			if(xcfaLocationSymbol.isInit()) builder.setInitLoc(loc);
			else if(xcfaLocationSymbol.isError()) builder.setErrorLoc(loc);
			else if(xcfaLocationSymbol.isFinal()) builder.setFinalLoc(loc);
		});
		edges.forEach(xcfaEdgeDefinition -> {
			List<Stmt> stmts = new ArrayList<>();
			xcfaEdgeDefinition.getStatements().forEach(xcfaStatement -> stmts.add(xcfaStatement.instantiate()));
			XCFA.Process.Procedure.Edge edge = xcfaEdgeDefinition.instantiate();
			builder.addEdge(edge);
		});
		return builder.build();
	}

	////

	@Override
	public Optional<XcfaProcessSymbol> enclosingScope() {
		return Optional.of(scope);
	}

	@Override
	public Optional<? extends Symbol> resolve(final String name) {
		final Optional<Symbol> symbol = symbolTable.get(name);
		if (symbol.isPresent()) {
			return symbol;
		} else {
			return scope.resolve(name);
		}
	}

	////

	private void declareAll(final Iterable<? extends Symbol> symbols) {
		symbolTable.addAll(symbols);
	}

	private List<XcfaVariableSymbol> createVariables(final List<VarDeclContext> varDeclContexts) {
		final List<XcfaVariableSymbol> result = new ArrayList<>();
		for (final VarDeclContext varDeclContext : varDeclContexts) {
			final XcfaVariableSymbol symbol = new XcfaVariableSymbol(varDeclContext);
			result.add(symbol);
		}
		return result;
	}
	private List<XcfaParamSymbol> createParams(final List<XcfaDslParser.DeclContext> declContexts) {
		final List<XcfaParamSymbol> result = new ArrayList<>();
		for (final XcfaDslParser.DeclContext declContext : declContexts) {
			final XcfaParamSymbol symbol = new XcfaParamSymbol(declContext);
			result.add(symbol);
		}
		return result;
	}

	private List<XcfaLocationSymbol> createLocations(final List<LocContext> locContexts) {
		final List<XcfaLocationSymbol> result = new ArrayList<>();

		int nInitLocs = 0;
		int nFinalLocs = 0;
		int nErrorLocs = 0;

		for (final LocContext locContext : locContexts) {
			final XcfaLocationSymbol symbol = new XcfaLocationSymbol(locContext);

			if (symbol.isInit()) {
				nInitLocs++;
			} else if (symbol.isFinal()) {
				nFinalLocs++;
			} else if (symbol.isError()) {
				nErrorLocs++;
			}

			result.add(symbol);
		}

		checkArgument(nInitLocs == 1, "Exactly one initial location must be specififed");
		checkArgument(nFinalLocs == 1, "Exactly one final location must be specififed");
		checkArgument(nErrorLocs == 1, "Exactly one error location must be specififed");

		return result;
	}

	private List<XcfaEdgeDefinition> createEdges(final List<EdgeContext> edgeContexts) {
		final List<XcfaEdgeDefinition> result = new ArrayList<>();
		for (final EdgeContext edgeContext : edgeContexts) {
			final XcfaEdgeDefinition edgeDefinition = new XcfaEdgeDefinition(this, edgeContext);
			result.add(edgeDefinition);
		}
		return result;
	}

}
