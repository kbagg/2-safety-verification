package check

import model.CheckModel

object Check{
  def main(args:Array[String]){
    var checkmod = new CheckModel;
    checkmod.relationalInduction();
  }
}
