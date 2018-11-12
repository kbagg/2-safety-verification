import com.microsoft.z3
import java.util.HashMap
import scala.collection.immutable._

import scala.collection.mutable.Map
import scala.collection.JavaConverters._
import com.microsoft.z3.enumerations.Z3_lbool
import com.microsoft.Z3.enumerations.Z3_decl_kind
import com.typesafe.scalalogging.Logger
import java.io.File
import java.io.PrintWriter

class TransitionSystem(suff:String){
  val ctx = new z3.Context();
  var suffix = suff;
  var variables = List(ctx.mkInt('x' + suffix), ctx.mkInt('y' + suffix));
  var sorts = List(ctx.mkIntSort(), ctx.mkIntSort());

  def initialize(xs:List[z3.Int]):List[z3.IntExpr] = {
    List(xs(0) == 0, xs(1) == 1);
  }

  def transition(xs:List[z3.Int]):List[z3.Int] = {
    List(xs(0)+1, xs(0)+xs(1));
  }

}
