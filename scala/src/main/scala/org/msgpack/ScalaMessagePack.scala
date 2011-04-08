package org.msgpack

import template._
import builder.{AnnotationTemplateBuilderSelector, BuilderSelectorRegistry, BuildContextFactory}
import collection.mutable.{MutableList, LinkedList}
import collection.mutable.{Map => MMap, HashMap => MHashMap}
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/10
 * Time: 1:34
 */

object ScalaMessagePack {

  {
    // for scala object
    BuilderSelectorRegistry.getInstance.insertBefore(
      AnnotationTemplateBuilderSelector.NAME,
      new ScalaTemplateBuilderSelector)

    // register scala's list classes
    TemplateRegistry.register(classOf[List[_]],new ImmutableListTemplate(AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[List[_]],new GenericTemplate1(classOf[ImmutableListTemplate]))
    TemplateRegistry.register(classOf[Seq[_]],new ImmutableListTemplate(AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[Seq[_]],new GenericTemplate1(classOf[ImmutableListTemplate]))
    TemplateRegistry.register(classOf[LinkedList[_]],new LinkedListTemplate(AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[LinkedList[_]],new GenericTemplate1(classOf[LinkedListTemplate]))
    TemplateRegistry.register(classOf[MutableList[_]],new MutableListCTemplate(AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[MutableList[_]],new GenericTemplate1(classOf[MutableListCTemplate]))

    // register scala's map classes
    TemplateRegistry.register(classOf[Map[_,_]],new ImmutableMapTemplate(
      AnyTemplate.getInstance,AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[Map[_,_]],new GenericTemplate2(
      classOf[ImmutableMapTemplate]))
    TemplateRegistry.register(classOf[MMap[_,_]],new MutableHashMapTemplate(
      AnyTemplate.getInstance,AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[MMap[_,_]],new GenericTemplate2(
      classOf[MutableHashMapTemplate]))
    TemplateRegistry.register(classOf[MHashMap[_,_]],new MutableHashMapTemplate(
      AnyTemplate.getInstance,AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[MHashMap[_,_]],new GenericTemplate2(
      classOf[MutableHashMapTemplate]))




  }

  /**
   * dammy method for initialize
   */
  def init() = {}


  def pack( obj : Any) = {
    MessagePack.pack(obj.asInstanceOf[AnyRef])
  }

  def unpack[T]( buffer : Array[Byte])(implicit manifest : ClassManifest[T]) : T = {
    MessagePack.unpack[T]( buffer, manifest.erasure.asInstanceOf[Class[T]])
  }

  def unpackD(buffer : Array[Byte]) = {
    MessagePack.unpack(buffer)
  }






}