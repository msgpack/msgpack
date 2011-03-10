package org.msgpack

import annotation.{Optional, Index}
import reflect.BeanProperty
import scala.annotation.target.getter
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/10
 * Time: 17:12
 */

class SampleClass2 extends SampleClass with SampleTrait {


  var sampleClass2Name : String = "sampleclass2"

  @Index(0)
  def sampleClass2Num : Int = 22
  def sampleClass2Num_=(v : Int) = {}

  val notProperty : String ="This is not prop.Only getter"

  // wrong property
  def wrongValue : Int = 53
  def wrongValue_=(v : String) = {}

}

final class MyAnno extends StaticAnnotation