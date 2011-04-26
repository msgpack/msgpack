package org.msgpack

import annotation.MessagePackMessage
import annotation.{Optional, Index}
import java.util.Date
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/10
 * Time: 1:35
 */

@MessagePackMessage
class SampleClass {
  var name : String = "hoge"
  var number : Int = 2

}

trait SampleTrait {

  var traitName : String = ""

  var traitNum : Int = 12

}

class SampleClass2 extends SampleClass with SampleTrait {


  @Index(3)
  var sampleClass2Name : String = "sampleclass2"

  // Support getter/setter but must have _{name} field!
  private var _sampleClass2Num : Int = 0
  @Index(0)
  def sampleClass2Num : Int = _sampleClass2Num
  def sampleClass2Num_=(v : Int) = {_sampleClass2Num = v}

  val notProperty : String ="This is not prop.Only getter"

  private var _wrongValue : Int = 0
  // wrong property
  def wrongValue : Int = 53
  def wrongValue_=(v : String) = {}

}

object NotDefaultCons{

  def apply() : NotDefaultCons2 = {
    new NotDefaultCons2()
  }
}
@MessagePackMessage
class NotDefaultCons(var name : String){
}

class NotDefaultCons2 extends NotDefaultCons("hoge")

@MessagePackMessage
class BasicalTypes{

  var intVar : Int = 0
  var longVar : Long = 0
  var shortVar : Short = 0
  var byteVar : Byte = 0
  var boolVar : Boolean = false

  var floatVar : Float = 0
  var doubleVar : Double = 0

  var strVar : String = ""

  var dateVar : Date = null

  var intArray : Array[Int] = Array()

}

object FieldOrder{
  val None = 0
  val Offering = 11
  val BeOffered = 12
  val Friend = 13
  val Block = 21
}

@MessagePackMessage
class FieldOrder{

  var one : Int = 0
  var two : String = "aaa"
  var three : String = "bbb"
  var four : String = ""
  var five : Boolean = false

  def six : Int = 1
  def six_=(v : Int) = one = v

  override def toString = "hogehoge"

}