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
    "pack and unpack" in {

      val sc = new SampleClass()
      sc.name = "Test object"
      sc.number = 123456

      println("Sampleclass is inherit ScalaObject " + classOf[ScalaObject].isAssignableFrom(classOf[SampleClass]))
      new ScalaTemplateBuilderSelector().matchType(classOf[SampleClass]) must be_==(true)
      val b = ScalaMessagePack.pack(sc)

      val deser = ScalaMessagePack.unpack[SampleClass](b)

      deser.name must be_==(sc.name)
      deser.number must be_==(sc.number)

      val mso = ScalaMessagePack.unpackD(b)
      val conv = mso.convert(classOf[SampleClass])
      conv.name must be_==(sc.name)
      conv.number must be_==(sc.number)
    }

    "pack and unpack none-default constructor class" in {

      val sc = new NotDefaultCons("hehehehe")

      val b = ScalaMessagePack.pack(sc)

      val deser = ScalaMessagePack.unpack[NotDefaultCons](b)

      deser.name must be_==(sc.name)

      val mso = ScalaMessagePack.unpackD(b)
      val conv = mso.convert(classOf[NotDefaultCons])
      conv.name must be_==(sc.name)
    }


  }


}

