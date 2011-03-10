package org.msgpack

import org.junit.runner.RunWith
import org.specs._
import org.specs.matcher._
import org.specs.runner.{ JUnitSuiteRunner, JUnit }
//import org.scalacheck.Gen

/**
 * Sample specification.
 * 
 * This specification can be executed with: scala -cp <your classpath=""> ${package}.SpecsTest
 * Or using maven: mvn test
 *
 * For more information on how to write or run specifications, please visit: http://code.google.com/p/specs.
 *
 */
@RunWith(classOf[JUnitSuiteRunner])
class PackSpecTest extends Specification with JUnit /*with ScalaCheck*/ {

  "MessagePack" should {
    "pack " in {

      val sc = new SampleClass()
      sc.name = "wahoo"
      val b = MessagePack.pack(sc)
      val des = MessagePack.unpack(b,classOf[SampleClass])

      des.name must be_==(sc.name)
    }
  }


}

