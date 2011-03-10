package org.msgpack

import template._
import template.javassist.BuildContextFactory
import collection.mutable.{MutableList, LinkedList}
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/10
 * Time: 1:34
 */

object ScalaMessagePack {

  {
    JavassistTemplateBuilder.getInstance.setFieldEntryReader(new ScalaFieldEntryReader)
    JavassistTemplateBuilder.getInstance.setBuildContextFactory(new BuildContextFactory{
      def createBuildContext(builder: JavassistTemplateBuilder) = new BuildContextForScala(builder)
    })

    TemplateRegistry.register(classOf[List[_]],new ImmutableListTemplate(AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[List[_]],new GenericTemplate1(classOf[ImmutableListTemplate]))
    TemplateRegistry.register(classOf[LinkedList[_]],new LinkedListTemplate(AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[LinkedList[_]],new GenericTemplate1(classOf[LinkedListTemplate]))
    TemplateRegistry.register(classOf[MutableList[_]],new MutableListCTemplate(AnyTemplate.getInstance))
    TemplateRegistry.registerGeneric(classOf[MutableList[_]],new GenericTemplate1(classOf[MutableListCTemplate]))



  }


  def pack( obj : Any) = {
    MessagePack.pack(obj.asInstanceOf[AnyRef])
  }

  def unpack[T]( buffer : Array[Byte])(implicit manifest : ClassManifest[T]) : T = {
    println(manifest.erasure)
    MessagePack.unpack[T]( buffer, manifest.erasure.asInstanceOf[Class[T]])
  }






}