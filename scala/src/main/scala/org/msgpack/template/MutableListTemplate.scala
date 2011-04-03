package org.msgpack.template

import org.msgpack.{MessagePackObject, Packer, Unpacker, Template}
import collection.mutable.{MutableList, LinearSeq, LinkedList}
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/11
 * Time: 2:37
 */

abstract class MutableListTemplate[T <: LinearSeq[_]](elementTemplate : Template)  extends Template{
  def unpack(pac: Unpacker, to: AnyRef) = {

    val length = pac.unpackArray();

    var list : LinearSeq[_] = if(to == null){
      toList(new Array[Object](0))
    }else{
      to.asInstanceOf[T]
    }
    for(i <- 0 until length){
      list = list :+ elementTemplate.unpack(pac,null)
    }

    list

  }
  def toList(array : Array[Object]) : T

  def pack(pk: Packer, target: AnyRef) = {

    val list = target.asInstanceOf[LinearSeq[_]]
		pk.packArray(list.size)
    for( e <- list){
      elementTemplate.pack(pk,e)
    }

  }

  def convert(from: MessagePackObject, to: AnyRef) = {
    toList(from.asArray.map(elementTemplate.convert(_,null)))
  }
}

class LinkedListTemplate(elementTemplate : Template)   extends MutableListTemplate[LinkedList[_]](elementTemplate){
  def toList(array : Array[Object]) = LinkedList(array :_*)
}
class MutableListCTemplate(elementTemplate : Template)   extends MutableListTemplate[MutableList[_]](elementTemplate){
  def toList(array : Array[Object]) = {
    val list : MutableList[Object] = new MutableList
    list ++= array
    list
  }
}