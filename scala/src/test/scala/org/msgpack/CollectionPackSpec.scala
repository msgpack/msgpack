package org.msgpack

import org.junit.runner.RunWith
import org.specs._
import org.specs.matcher._
import org.specs.runner.{ JUnitSuiteRunner, JUnit }
import scala.collection.mutable.LinkedList

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
class CollectionPackSpec extends Specification with JUnit  {

  "ScalaMessagePack" should {
    "pack scala-list" in {
      val c = new ClassWithList

      c.immutable = List("a","b","c")
      c.mutable = LinkedList("a","b","d")

      val b = ScalaMessagePack.pack(c)
      val des = ScalaMessagePack.unpack[ClassWithList](b)

      des.immutable must be_==(c.immutable)
      des.mutable must be_==(c.mutable)

    }
    "pack scala-map" in {
      val c = new ClassWithMap
      c.immutable = Map("a" -> "hoge","b" -> "fuga","c" -> "hehe")
      c.mutable = scala.collection.mutable.Map("d" -> "oo" , "e" -> "aa")

      val b = ScalaMessagePack.pack(c)
      val des = ScalaMessagePack.unpack[ClassWithList](b)

      des.immutable must be_==(c.immutable)
      des.mutable must be_==(c.mutable)
    }

  }




}

