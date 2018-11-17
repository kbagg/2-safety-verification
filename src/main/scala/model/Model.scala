package model

import com.microsoft.z3
import java.util.HashMap
import scala.collection.immutable._
import scala.util.control.Breaks._ 
import scala.language.postfixOps

import scala.collection.mutable.Map
import scala.collection.JavaConverters._
import com.microsoft.z3.enumerations.Z3_lbool
import com.microsoft.z3.enumerations.Z3_decl_kind
import java.io.File
import java.io.PrintWriter

// Transition system: x' -> x + 1, y' -> x + y
// class TransitionSystem(suff:String, ctx:z3.Context){

//   var suffix = suff;
//   var variables = List(ctx.mkIntConst("x"), ctx.mkIntConst("y"));
//   if(suff !=""){
//     variables = List(ctx.mkIntConst("x_" + suffix), ctx.mkIntConst("y_" + suffix));
//   }
//   var sorts = Array[z3.Sort](ctx.mkIntSort(), ctx.mkIntSort());

//   def addsuffix(suff:String=""):List[z3.ArithExpr] = {
//     var s = "";
//     if(suff!=""){
//       s = "_"+suff;
//     }
//     return List(ctx.mkIntConst("x"+s), ctx.mkIntConst("y"+s));
//     //List(1, 2);
//   }

//   def initialize(xs:List[z3.ArithExpr]):List[z3.BoolExpr] = {
//     return List(ctx.mkEq(xs(0), ctx.mkInt(0)), ctx.mkEq(xs(1), ctx.mkInt(1)));
//   }

//   def transition(xs:List[z3.ArithExpr]):List[z3.ArithExpr] = {
//     return List(ctx.mkAdd(xs(0), ctx.mkInt(1)), ctx.mkAdd(xs(0), xs(1)));
//   }
// }


// Transition system: x' -> y, y' -> x + y, fibonacci
class TransitionSystem(suff:String, ctx:z3.Context){

  var suffix = suff;
  var variables = List(ctx.mkIntConst("x"), ctx.mkIntConst("y"));
  if(suff !=""){
    variables = List(ctx.mkIntConst("x_" + suffix), ctx.mkIntConst("y_" + suffix));
  }
  var sorts = Array[z3.Sort](ctx.mkIntSort(), ctx.mkIntSort());

  def addsuffix(suff:String=""):List[z3.ArithExpr] = {
    var s = "";
    if(suff!=""){
      s = "_"+suff;
    }
    return List(ctx.mkIntConst("x"+s), ctx.mkIntConst("y"+s));
    //List(1, 2);
  }

  def initialize(xs:List[z3.ArithExpr]):List[z3.BoolExpr] = {
    //return List(ctx.mkEq(xs(0), ctx.mkInt(0)), ctx.mkEq(xs(1), ctx.mkInt(1)));
    return List(ctx.mkEq(xs(0), ctx.mkInt(1)), ctx.mkEq(xs(1), ctx.mkInt(1)));
  }

  def transition(xs:List[z3.ArithExpr]):List[z3.ArithExpr] = {
    //return List(xs(1), ctx.mkAdd(xs(0), xs(1)));
    //return List(ctx.mkAdd(xs(0), ctx.mkInt(1)), ctx.mkAdd(xs(0), xs(1)))
    return List(ctx.mkAdd(xs(0), ctx.mkInt(1)), ctx.mkMul(ctx.mkAdd(xs(0), ctx.mkInt(1)), xs(1)))
  }
}

class SelfComposedTransitionSystem(modelarg:TransitionSystem, ctx:z3.Context){

  var model = modelarg;
  var vm = modelarg.addsuffix("1");
  var vmprime = modelarg.addsuffix("2");
  var variables = vm ::: vmprime;
  var sorts = modelarg.sorts ++ modelarg.sorts;
  var arity = 4;

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
    //return List(ctx.mkAnd(ctx.mkEq(xs(0), xs(2)), ctx.mkDistinct(xs(1), xs(3))))
    return List(ctx.mkAnd(ctx.mkLt(xs(0), xs(2)), ctx.mkGe(xs(1), xs(3))))
  }

}

class CheckModel(){

  def relationalInduction(){

    val cfg = new HashMap[String, String]();
    cfg.put("model", "true");
    cfg.put("proof", "true");
    val ctx = z3.InterpolationContext.mkContext(cfg); 
    var m = new TransitionSystem("", ctx);
    var msc = new SelfComposedTransitionSystem(m, ctx);

    var xs = msc.variables;
    var xst = msc.transition(xs);
    var xsp = msc.addsuffix("prime");

    var bad = ctx.mkAnd(msc.bad_sc(xs):_*).simplify().asInstanceOf[z3.BoolExpr];
    var init = ctx.mkAnd(msc.initialize(xs):_*).simplify().asInstanceOf[z3.BoolExpr];
    var check = ctx.mkAnd(init, bad).simplify().asInstanceOf[z3.BoolExpr];

    var solver = ctx.mkSolver();

    solver.push();
    solver.add(check);
    var rinit = solver.check();
    solver.pop();
    assert(rinit == z3.Status.UNSATISFIABLE)

    solver.push();

    var bad_proofob = ctx.mkAnd(msc.bad_sc(xsp):_*).simplify().asInstanceOf[z3.BoolExpr];
    var trx = ctx.mkBool(true);
    for (i <- 0 until msc.arity){
      trx = ctx.mkAnd(trx, ctx.mkEq(xsp(i), xst(i))).simplify().asInstanceOf[z3.BoolExpr];
    }

    solver.add(bad);
    solver.add(trx);
    solver.add(bad_proofob);

    var n = xs.size/2;
    var unsafe = false;

    breakable{
      while(solver.check() == z3.Status.SATISFIABLE){
        breakable{
          var model = solver.getModel();
          var xm1 = xs.slice(0, xs.size/2).map(xsi => model.eval(xsi, true))
          var xm2 = xs.slice(xs.size/2, xs.size).map(xsi => model.eval(xsi, true))
          val range = 0 until xm1.size toList;
          var bad1 = (xs1:List[z3.ArithExpr]) => List(ctx.mkAnd((range.map((i=>ctx.mkEq(xs1(i), xm1(i))))):_*));
          var bad2 = (xs2:List[z3.ArithExpr]) => List(ctx.mkAnd((range.map((i=>ctx.mkEq(xs2(i), xm2(i))))):_*));

          println("xm1", xm1)
          println("xm2", xm2)
          // These 3 values are returned by the getLength function
          var (r1:Any, arg1:List[z3.Expr], expr1:z3.BoolExpr, length:Int) = getLength(m, bad1, ctx);
          println("length", length)
          println("r1", r1)
          println("arg1", arg1)
          println("expr1", expr1)

          if(r1 == z3.Status.UNSATISFIABLE){
            // Can we work without the need to substitute?
            var xstemp = xs.slice(0, xs.size/2);
            var p1 = expr1;
            for (i <- 0 until xs.size/2){
              p1 = p1.substitute(arg1(i), xstemp(i)).asInstanceOf[z3.BoolExpr];
            }
            xstemp = xs.slice(xs.size/2, xs.size);
            var p2 = expr1;
            for (i <- 0 until xs.size/2){
              p2 = p2.substitute(arg1(i), xstemp(i)).asInstanceOf[z3.BoolExpr];
            }
            solver.add(p1);
            solver.add(p2);
            break;
          }
          // var (r2:Any, arg2:List[z3.Expr], expr2either:Either[z3.InterpolationContext#ComputeInterpolantResult, None.type]) = checkLength(m, msc, bad2, xm1(0).toString().toInt+1, ctx);
          var (r2:Any, arg2:List[z3.Expr], expr2either:Either[z3.InterpolationContext#ComputeInterpolantResult, None.type]) = checkLength(m, msc, bad2, length, ctx);

          println("r2", r2)
          println("arg2", arg2)
          expr2either match{
            case Left(expr2Inter) => {
              var expr2Array = expr2Inter.interp;
              println("expr2", expr2Array(0))
              println("xs", xs)
              var p = expr2Array(0);
              for (i <- 0 until xs.size){
                p = p.substitute(arg2(i), xs(i)).asInstanceOf[z3.BoolExpr];
              }
              println("p", p)
              solver.add(p);
              println("solver.check", solver.check())
              break;
            }
            case Right(None) => {
              unsafe = true;
              break;
            }
          }
        }
        if(unsafe == true){
          break;
        }
      }
    }

    if(unsafe == true){
      println("UNSAFE");
    }
    else{
      println("SAFE");
    }
  }

  def getLength(m:TransitionSystem, bad:List[z3.ArithExpr]=>List[z3.BoolExpr], ctx:z3.Context):Tuple4[Any, List[z3.Expr], z3.BoolExpr, Int] = {
    z3.Global.setParameter("fixedpoint.engine", "pdr")
    val fp = ctx.mkFixedpoint();
    val params = ctx.mkParams();
    params.add("fixedpoint.engine", "spcaer");
    fp.setParameters(params);
    var mp = new TransitionSystem("prime", ctx);
    val sorts = m.sorts;
    val range = 0 until sorts.size toList;
    var xs = range.map(i=>ctx.mkBound(i, sorts(i)).asInstanceOf[z3.ArithExpr]);
    var xst = m.transition(xs);
    val invDecl = ctx.mkFuncDecl("inv", sorts, ctx.mkBoolSort());
    val errDecl = ctx.mkFuncDecl("error", Array[z3.Sort](), ctx.mkBoolSort());
    var symbols = new Array[z3.Symbol](xs.size)
    for(i<- 0 until xs.size){
      symbols(i) = ctx.mkSymbol(i).asInstanceOf[z3.Symbol];
    }
    fp.registerRelation(invDecl);
    fp.registerRelation(errDecl);
    // for(x<-xs:::xsp){
    //   fp.declareVar(x);
    // }

    var qId = 0;
    var skId = 0;

    def createForAll(sorts:Array[z3.Sort], symbols:Array[z3.Symbol], e:z3.Expr):z3.BoolExpr = {
      qId +=1;
      skId +=1;
      ctx.mkForall(sorts, symbols, e, 0, Array[z3.Pattern](), Array[z3.Expr](), ctx.mkSymbol(qId), ctx.mkSymbol(skId))
    }

    val initCond = ctx.mkAnd(m.initialize(xs):_*);
    val invxs = invDecl.apply(xs:_*).asInstanceOf[z3.BoolExpr];
    var initRule = ctx.mkImplies(initCond, invxs);
    initRule = createForAll(sorts, symbols, initRule);

    val trxAfter = invDecl.apply(xst:_*).asInstanceOf[z3.BoolExpr];
    var trxRule = ctx.mkImplies(invxs, trxAfter);
    trxRule = createForAll(sorts, symbols, trxRule);

    val badxs = ctx.mkAnd(bad(xs):_*);
    val badInv = ctx.mkAnd(badxs, invxs);
    var badRule = ctx.mkImplies(badInv, errDecl.apply().asInstanceOf[z3.BoolExpr]);
    badRule = createForAll(sorts, symbols, badRule);

    fp.addRule(initRule, ctx.mkSymbol("initRule"));
    fp.addRule(trxRule, ctx.mkSymbol("trxRule"));
    fp.addRule(badRule, ctx.mkSymbol("badRule"));
    println("fp", fp.toString)
    val rfp = fp.query(Array(errDecl));
    println("rfp", rfp)
    if(rfp == z3.Status.UNSATISFIABLE){
      val ans = fp.getAnswer();
      val body = ans.asInstanceOf[z3.Quantifier].getBody();
      val args = body.getArgs();
      var varlist = args(0).getArgs().toList
      var expr = args(1).simplify().asInstanceOf[z3.BoolExpr]

      return (z3.Status.UNSATISFIABLE, varlist, expr, -1)
    }

    // This is the trace length. Why is a +1 needed?
    var length = fp.getAnswer().getArgs().size + 1

    return (z3.Status.SATISFIABLE, m.variables, ctx.mkBool(true), length)
  }

  def checkLength(m:TransitionSystem, msc:SelfComposedTransitionSystem, bad:List[z3.ArithExpr]=>List[z3.BoolExpr], count:Int, ctx:z3.InterpolationContext):Tuple3[Any, List[z3.ArithExpr], Either[z3.InterpolationContext#ComputeInterpolantResult, None.type]] = {
    var x = List(m.addsuffix("0"));
    for(i<-1 until count){
      x = x ::: List(m.addsuffix(i.toString()))
    }
    var badfinal = ctx.mkAnd(bad(x.reverse(0)):_*).simplify().asInstanceOf[z3.BoolExpr]
    var init = ctx.mkAnd(m.initialize(x(0)):_*).simplify().asInstanceOf[z3.BoolExpr]
    var trx = ctx.mkBool(true)
    val range = 0 until x(0).size toList;
    var temp = m.transition(x(0));
    var temp1 = ctx.mkBool(true)
    for(i<-0 until count-1){
      temp = m.transition(x(i));
      temp1 = ctx.mkAnd((range.map(j=>ctx.mkEq(temp(j), x(i+1)(j)))):_*).asInstanceOf[z3.BoolExpr];
      trx = ctx.mkAnd(temp1, trx).asInstanceOf[z3.BoolExpr];
    }

    var s = ctx.mkSolver();
    s.add(init);
    s.add(trx);
    s.add(badfinal);
    var rbmc = s.check();

    if(rbmc == z3.Status.UNSATISFIABLE){
      var formula1 = ctx.mkBool(true);
      var formula2 = ctx.mkBool(true);
      var xprime = List(m.addsuffix("0_prime"));
      for(i<-1 until count){
        xprime = xprime ::: List(m.addsuffix(i.toString()+"_prime"))
      }
      formula1 = ctx.mkAnd(init, trx).asInstanceOf[z3.BoolExpr];
      var initprime = ctx.mkAnd(m.initialize(xprime(0)):_*).simplify().asInstanceOf[z3.BoolExpr]
      var trxprime = ctx.mkBool(true)
      temp = m.transition(xprime(0));
      temp1 = ctx.mkBool(true)
      for(i<-0 until count-1){
        temp = m.transition(xprime(i));
        temp1 = ctx.mkAnd((range.map(j=>ctx.mkEq(temp(j), xprime(i+1)(j)))):_*).asInstanceOf[z3.BoolExpr];
        trxprime = ctx.mkAnd(temp1, trxprime).asInstanceOf[z3.BoolExpr];
      }
      formula1 = ctx.mkAnd(initprime, trxprime, formula1).asInstanceOf[z3.BoolExpr]
      // xval are the exact values that consecutive states of M take
      var xval = List(List(ctx.mkInt(0), ctx.mkInt(1)));
      for(i<-0 until count-1){
        xval = xval ::: List(m.transition(xval(i))).asInstanceOf[List[List[z3.IntNum]]]
      }
      for(i<-1 until count){
        formula1 = ctx.mkAnd(formula1, ctx.mkAnd((range.map(j=>ctx.mkEq(x(i)(j), xval(i)(j)))):_*).asInstanceOf[z3.BoolExpr]).asInstanceOf[z3.BoolExpr]
      }
      println("formula1", formula1)
      val i1 = ctx.MkInterpolant(formula1);
      println(i1)
      formula2 = ctx.mkAnd(msc.bad_sc(x(count-1):::xprime(count-1)):_*).simplify().asInstanceOf[z3.BoolExpr];
      println("formula2", formula2)
      val result = ctx.ComputeInterpolant(ctx.mkAnd(i1, formula2), ctx.mkParams())
      println("interpolant", result.interp(0))
      return (z3.Status.UNSATISFIABLE, x(count-1):::xprime(count-1), Left(result))
    }
    return (z3.Status.SATISFIABLE, m.variables, Right(None))
  }
}
