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
class ScalaFieldEntryReaderTest extends Specification with JUnit  {

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

        println("props=" + props.keys)

        props.size must be_==(6)
        val l = props.toList
        l(0)._1 must_== "name"
        l(1)._1 must_== "number"
        l(2)._1 must_== "sampleClass2Name"
        l(3)._1 must_== "sampleClass2Num"
        l(4)._1 must_== "traitName"
        l(5)._1 must_== "traitNum"
      }

    }

    "field order" in {
      var reader = new ScalaFieldEntryReader
      val c = classOf[FieldOrder]

      println("Methods of FieldOrder class")
      c.getMethods.foreach(println(_))
      println("-- end --")

      val props = reader.findPropertyMethods(c)

      var index : Int = 0
      val names = List("one","two","three","four","five","six")
      for( p <- props.values){
        p._1.getName must_== names(index)
        index += 1
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
      indexed(3)._1 must be_==("sampleClass2Name")
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

