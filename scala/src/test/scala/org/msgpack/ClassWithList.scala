package org.msgpack;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/11
 * Time: 2:13
 */

import annotation.MessagePackMessage
import collection.mutable.{MutableList, LinkedList}

@MessagePackMessage
class ClassWithList {
  var immutable : List[String] = Nil

  var mutable : LinkedList[String] = LinkedList.empty

  var mutable2 : MutableList[String] = new MutableList

  //var tuple2 : (String,String) = (null,null)
}