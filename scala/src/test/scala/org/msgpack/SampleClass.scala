package org.msgpack

import annotation.MessagePackMessage
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/10
 * Time: 1:35
 */

@MessagePackMessage
class SampleClass {
  var name : String = "hoge"
  var number : Int = 2

}