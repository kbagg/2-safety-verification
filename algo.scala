import com.microsoft.z3
import java.util.HashMap
import scala.collection.immutable._

import scala.collection.mutable.Map
import scala.collection.JavaConverters._
import com.microsoft.z3.enumerations.Z3_lbool
import com.microsoft.z3.enumerations.Z3_decl_kind
import java.io.File
import java.io.PrintWriter

class TransitionSystem(suff:String=""){

  val cfg = new HashMap[String, String]();
  cfg.put("model", "true");
  val ctx = new z3.Context(cfg);
  var suffix = suff;
  var variables = List(ctx.mkInt("x"), ctx.mkInt("y"));
  if(suff !=""){
    variables = List(ctx.mkInt("x_" + suffix), ctx.mkInt("y_" + suffix));
  }
  var sorts = List(ctx.mkIntSort, ctx.mkIntSort);

  def addsuffix(suff:String=""):List[z3.ArithExpr] = {
    var s = "";
    if(suff !=""){
      s = "_"+suff;
    }
    return List(ctx.mkInt("x"+s), ctx.mkInt("y"+s));
    //List(1, 2);
  }

  def initialize(xs:List[z3.ArithExpr]):List[z3.BoolExpr] = {
    return List(ctx.mkEq(xs(0), ctx.mkInt(0)), ctx.mkEq(xs(1), ctx.mkInt(1)));
  }

  def transition(xs:List[z3.ArithExpr]):List[z3.ArithExpr] = {
    return List(ctx.mkAdd(xs(0), ctx.mkInt(1)), ctx.mkAdd(xs(0), xs(1)));
  }
}

class SelfComposedTransitionSystem(modelarg:TransitionSystem){

  val ctx = modelarg.ctx;
  var model = modelarg;
  var vm = modelarg.addsuffix("1");
  var vmprime = modelarg.addsuffix("2");
  var variables = vm ::: vmprime;
  var sorts = modelarg.sorts ::: modelarg.sorts

  def addsuffix(suff:String=""):List[z3.ArithExpr] = {
    var v1 = this.model.addsuffix("1"+suff);
    var v2 = this.model.addsuffix("2"+suff);
    return v1 ::: v2;
  }

  def initialize(xs:List[z3.ArithExpr]):List[z3.BoolExpr] = {
    return this.model.initialize(xs.slice(0, xs.size/2)) ::: this.model.initialize(xs.slice(xs.size/2, xs.size))
  }

  def transition(xs:List[z3.ArithExpr]):List[z3.ArithExpr] = {
    return this.model.transition(xs.slice(0, xs.size/2)) ::: this.model.transition(xs.slice(xs.size/2, xs.size))
  }

  def bad_sc(xs:List[z3.ArithExpr]):List[z3.BoolExpr] = {
    return List(ctx.mkAnd(ctx.mkEq(xs(0), xs(2)), ctx.mkDistinct(xs(1), xs(3))))
  }

}

class CheckModel(){

  def relationalInduction(){

    var m = new TransitionSystem();
    var msc = new SelfComposedTransitionSystem(m);
    val cfg = new HashMap[String, String]()
    cfg.put("model", "true")
    cfg.put("proof", "true")
    val ctx = z3.InterpolationContext.mkContext(cfg)
    
    var xs = msc.variables;
    var xsp = msc.addsuffix("prime");

    var bad = ctx.mkAnd(msc.bad_sc(msc.variables):_*).simplify().asInstanceOf[z3.BoolExpr];
    var init = ctx.mkAnd(msc.initialize(msc.variables):_*).simplify().asInstanceOf[z3.BoolExpr];
    var check = ctx.mkAnd(init, bad).simplify().asInstanceOf[z3.BoolExpr];

    var solver = ctx.mkSolver();

    solver.push();
    solver.add(check);
    var rinit = solver.check();
    solver.pop();
    assert(rinit == z3.Status.UNSATISFIABLE)

  }
}
