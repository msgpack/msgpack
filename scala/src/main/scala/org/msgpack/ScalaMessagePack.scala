package org.msgpack

import template.javassist.BuildContextFactory
import template.JavassistTemplateBuilder
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

  }


  def pack( obj : Any) = {
    MessagePack.pack(obj.asInstanceOf[AnyRef])
  }

  def unpack[T]( buffer : Array[Byte])(implicit manifest : ClassManifest[T]) : T = {
    println(manifest.erasure)
    MessagePack.unpack[T]( buffer, manifest.erasure.asInstanceOf[Class[T]])
  }






}