package org.msgpack.template;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/11
 * Time: 12:06
 */

import org.msgpack._
import collection.mutable.{HashMap,Map => MMap}
import scala.collection.JavaConverters._

abstract class MutableMapTemplate[T <: MMap[_,_]](keyTemplate : Template , valueTemplate : Template) extends Template {

  def unpack(pac: Unpacker, to: AnyRef) = {

    val length = pac.unpackMap()
    val array : Array[(Object,Object)] = new Array(length)

    for(i <- 0 until length){
      array(i) = (keyTemplate.unpack(pac,null),valueTemplate.unpack(pac,null))
    }

    toMap(array)

  }

  def toMap(array : Array[(Object,Object)]) : T


  def pack(pk: Packer, target: AnyRef) = {

    val map = try{target.asInstanceOf[MMap[_,_]]}
    catch{
      case e : ClassCastException => {
        throw new MessageTypeException("target is not List type: " + target.getClass());
      }
      case e : NullPointerException => {
        throw new MessageTypeException(new NullPointerException("target is null."));
      }
    }
		pk.packMap(map.size)
    for( e <- map){
      keyTemplate.pack(pk,e._1)
      valueTemplate.pack(pk,e._2)
    }


  }

  def convert(from: MessagePackObject, to: AnyRef) = {
    toMap(from.asMap.asScala.map(p => (keyTemplate.convert(p._1,null),valueTemplate.convert(p._2,null))).toArray)

  }



}


class MutableHashMapTemplate(keyTemplate : Template , valueTemplate : Template)
  extends MutableMapTemplate[HashMap[_,_]](keyTemplate,valueTemplate ) {

  def toMap(array : Array[(Object,Object)]) = {
    HashMap(array :_*)
  }



}
