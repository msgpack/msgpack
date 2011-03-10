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
class ScalaFieldEntryReaderSpec extends Specification with JUnit  {

  "ScalaFieldEntryReader" should {
    "check setter " in {
      val reader = new ScalaFieldEntryReader()

      val c = classOf[SampleClass]

      reader.setter_?(c.getMethod("name")) must be_==(false)
      reader.setter_?(c.getMethod("name_$eq",classOf[String])) must be_==(true)
    }
    "check getter " in {
      val reader = new ScalaFieldEntryReader()

      val c = classOf[SampleClass]

      reader.getter_?(c.getMethod("name")) must be_==(true)
      reader.getter_?(c.getMethod("name_$eq",classOf[String])) must be_==(false)
    }

    "find props " in {
      val reader = new ScalaFieldEntryReader()

      {
        val c = classOf[SampleClass]

        val props = reader.findPropertyMethods(c)

        props.size must be_==(2)
        props must haveKey("name")
        props must haveKey("number")
      }

      {
        val c = classOf[SampleClass2]

        val props = reader.findPropertyMethods(c)

        println(props.keys)

        props.size must be_==(6)
        props must haveKey("name")
        props must haveKey("number")
        props must haveKey("traitName")
        props must haveKey("traitNum")
        props must haveKey("sampleClass2Name")
        props must haveKey("sampleClass2Num")
      }

    }

    "indexing " in {
      val reader = new ScalaFieldEntryReader()

      val c = classOf[SampleClass2]

      def printDecs(c : Class[_]) : Unit = {
        println(c.getName + "---")
        val ds = c.getDeclaredMethods
        ds.foreach(m => {println(m)
          println(m.getAnnotations.toList)
        })
        if(c.getSuperclass != classOf[Object]){
          printDecs(c.getSuperclass)
        }
      }
      printDecs(c)



      val props = reader.findPropertyMethods(c)

      val indexed = reader.indexing(props)

      println(indexed.map(_._1).toList)

      indexed.size must be_==(6)
      indexed(0)._1 must be_==("sampleClass2Num")
      indexed must notContain(null)

    }

    "read entries" in {
      val reader = new ScalaFieldEntryReader()

      val c = classOf[SampleClass2]
      import org.msgpack.template.FieldOption

      val e = reader.readFieldEntries(c, FieldOption.NULLABLE)

      e.size must be_==(6)

    }

  }




}

