package org.msgpack

import annotation.MessagePackMessage
import template.builder.BuilderSelector
import java.lang.reflect.Type
import template.builder.{JavassistTemplateBuilder, BuildContextFactory}
import java.lang.annotation.{Annotation => JAnnotation}
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/14
 * Time: 17:59
 */

class ScalaTemplateBuilderSelector extends BuilderSelector
{
  val b = new JavassistTemplateBuilder()

  {
    b.setFieldEntryReader(new ScalaFieldEntryReader)
    b.setBuildContextFactory(new BuildContextFactory{
      def createBuildContext(builder: JavassistTemplateBuilder) = {
        new BuildContextForScala(builder)
      }
    })
  }

  def getName = "ScalaMessagePackMessageTemplateBuilderSelector";

  def getTemplateBuilder(targetType: Type) = {
    b
  }

  def matchType(targetType: Type) = {
    val c : Class[_] = targetType.asInstanceOf[Class[Object]]
    isAnnotated(c, classOf[MessagePackMessage]) &&
    classOf[ScalaObject].isAssignableFrom(c)//c.isAssignableFrom(classOf[ScalaObject])

  }

  private def isAnnotated(targetType : Class[_], annotation : Class[_ <: JAnnotation]) = {
    targetType.getAnnotation(annotation) != null

  }

}