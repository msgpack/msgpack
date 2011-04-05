package org.msgpack.template

import org.msgpack._

;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/11
 * Time: 2:25
 */

class ImmutableListTemplate(elementTemplate : Template) extends Template{
  def unpack(pac: Unpacker, to: AnyRef) = {

    val length = pac.unpackArray();
    val array : Array[Object] = new Array(length)

    for(i <- 0 until length){
      array(i) = elementTemplate.unpack(pac,null)
    }

    array.toList

  }

  def pack(pk: Packer, target: AnyRef) = {

    val list = try{target.asInstanceOf[List[_]]}
    catch{
      case e : ClassCastException => {
        throw new MessageTypeException("target is not List type: " + target.getClass());
      }
      case e : NullPointerException => {
        throw new MessageTypeException(new NullPointerException("target is null."));
      }
    }

		pk.packArray(list.size)
    for( e <- list){
      elementTemplate.pack(pk,e)
    }

  }

  def convert(from: MessagePackObject, to: AnyRef) = {
    from.asArray.map(elementTemplate.convert(_,null)).toList
  }
}
