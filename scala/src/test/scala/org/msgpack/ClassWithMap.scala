package org.msgpack;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/11
 * Time: 2:22
 */

import annotation.MessagePackMessage
import scala.collection.mutable.{Map => MMap}

@MessagePackMessage
class ClassWithMap {

  var immutable : Map[String,String] = Map.empty

  var mutable : MMap[String,String] = MMap.empty

}