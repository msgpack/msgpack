package org.msgpack;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/11
 * Time: 2:13
 */

import annotation.MessagePackMessage
import scala.collection.mutable.LinkedList

@MessagePackMessage
class ClassWithList {
  var immutable : List[String] = Nil

  var mutable : LinkedList[String] = LinkedList.empty

}