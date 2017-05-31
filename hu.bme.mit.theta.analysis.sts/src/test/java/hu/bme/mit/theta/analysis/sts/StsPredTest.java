package hu.bme.mit.theta.analysis.sts;

import static hu.bme.mit.theta.analysis.algorithm.ArgUtils.isWellLabeled;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.Exprs.Prime;
import static hu.bme.mit.theta.core.type.Types.Int;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.pred.ItpRefToSimplePredPrec;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.STS.Builder;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class StsPredTest {

	@Test
	public void test() {
		final Logger logger = new ConsoleLogger(100);

		final VarDecl<IntType> vx = Var("x", Int());
		final Expr<IntType> x = vx.getRef();

		final int mod = 3;

		final Builder builder = STS.builder();

		builder.addInit(Eq(x, Int(0)));
		builder.addTrans(And(Imply(Lt(x, Int(mod)), Eq(Prime(x), Add(x, Int(1)))),
				Imply(Geq(x, Int(mod)), Eq(Prime(x), Int(0)))));
		builder.setProp(Not(Eq(x, Int(mod))));

		final STS sts = builder.build();

		final ItpSolver solver = Z3SolverFactory.getInstace().createItpSolver();

		final Analysis<PredState, ExprAction, PredPrec> analysis = PredAnalysis.create(solver, sts.getInit());
		final Predicate<ExprState> target = new ExprStatePredicate(Not(sts.getProp()), solver);

		final SimplePredPrec prec = SimplePredPrec.create(Collections.singleton(Lt(x, Int(mod))), solver);

		final LTS<State, StsAction> lts = StsLts.create(sts);

		final ArgBuilder<PredState, StsAction, SimplePredPrec> argBuilder = ArgBuilder.create(lts, analysis, target);

		final Abstractor<PredState, StsAction, SimplePredPrec> abstractor = WaitlistBasedAbstractor.create(argBuilder,
				FifoWaitlist.supplier(), logger);

		final ExprTraceChecker<ItpRefutation> exprTraceChecker = ExprTraceFwBinItpChecker.create(sts.getInit(),
				Not(sts.getProp()), solver);

		final SingleExprTraceRefiner<PredState, StsAction, SimplePredPrec, ItpRefutation> refiner = SingleExprTraceRefiner
				.create(exprTraceChecker,
						JoiningPrecRefiner.create(new ItpRefToSimplePredPrec(solver, ItpRefToSimplePredPrec.atoms())),
						logger);

		final SafetyChecker<PredState, StsAction, SimplePredPrec> checker = CegarChecker.create(abstractor, refiner,
				logger);

		final SafetyResult<PredState, StsAction> safetyStatus = checker.check(prec);
		System.out.println(safetyStatus);

		final ARG<PredState, StsAction> arg = safetyStatus.getArg();
		assertTrue(isWellLabeled(arg, solver));

		// System.out.println(new
		// GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
