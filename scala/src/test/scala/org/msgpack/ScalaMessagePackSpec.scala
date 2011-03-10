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
class ScalaMessagePackTest extends Specification with JUnit /*with ScalaCheck*/ {

  "ScalaMessagePackTest" should {
    "pack " in {

      val sc = new SampleClass()
      sc.name = "Test object"
      sc.number = 123456
      val b = ScalaMessagePack.pack(sc)

      val deser = ScalaMessagePack.unpack[SampleClass](b)

      deser.name must be_==(sc.name)
      deser.number must be_==(sc.number)
    }
  }


}

