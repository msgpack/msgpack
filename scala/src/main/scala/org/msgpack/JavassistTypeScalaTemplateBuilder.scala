package org.msgpack

import annotation._
import template._
import template.javassist.BuildContext
import java.lang.Class
import collection.immutable.{ListMap, TreeMap}
import java.lang.reflect.{Type, Modifier, Method}
import java.lang.annotation.{Annotation => JavaAnnotation}
import scala.collection.JavaConverters._
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/10
 * Time: 12:29
 */


  class BuildContextForScala(builder : JavassistTemplateBuilder) extends BuildContext(builder){

    protected override def buildPackMethodBody() : String = {
      resetStringBuilder();
      buildString("{");
      buildString("%s _$$_t = (%s)$2;", this.origName, this.origName);
      buildString("$1.packArray(%d);", entries.length.asInstanceOf[AnyRef]);
      for(i <- 0 until entries.length) {
        val e = entries(i);
        if(!e.isAvailable()) {
          buildString("$1.packNil();");
        }else{
          val t = e.getType();
          if(t.isPrimitive()) {
            buildString("$1.%s(_$$_t.%s());", primitivePackName(t), e.getName());
          } else {
            buildString("if(_$$_t.%s() == null) {", e.getName());
            if(!e.isNullable() && !e.isOptional()) {
              buildString("throw new %s();", classOf[MessageTypeException].getName());
            } else {
              buildString("$1.packNil();");
            }
            buildString("} else {");
            buildString("  this.templates[%d].pack($1, _$$_t.%s());", i.asInstanceOf[AnyRef], e.getName());
            buildString("}");
          }
        }

      }
      buildString("}");
      return getBuiltString();
    }


      protected override def buildUnpackMethodBody() : String = {
        resetStringBuilder();
        buildString("{ ");

        buildString("%s _$$_t;", this.origName);
        buildString("if($2 == null) {");
        buildString("  _$$_t = new %s();", this.origName);
        buildString("} else {");
        buildString("  _$$_t = (%s)$2;", this.origName);
        buildString("}");

        buildString("int length = $1.unpackArray();");
        buildString("if(length < %d) {", this.minimumArrayLength.asInstanceOf[AnyRef]);
        buildString("  throw new %s();", classOf[MessageTypeException].getName());
        buildString("}");

        for(i <- 0 until this.minimumArrayLength) {
          val e = entries(i);
          if(!e.isAvailable()) {
            buildString("$1.unpackObject();");
          }else{

            buildString("if($1.tryUnpackNull()) {");
              if(e.isRequired()) {
                // Required + nil => exception
                buildString("throw new %s();", classOf[MessageTypeException].getName());
              } else if(e.isOptional()) {
                // Optional + nil => keep default value
              } else {  // Nullable
                // Nullable + nil => set null
                buildString("_$$_t.%s_$eq(null);", e.getName());
              }
            buildString("} else {");
              val t = e.getType();
              if(t.isPrimitive()) {
                buildString("_$$_t.%s_$eq( $1.%s() );", e.getName(), primitiveUnpackName(t));
              } else {
                buildString("_$$_t.%s_$eq( (%s)this.templates[%d].unpack($1, _$$_t.%s()));", e.getName(), e.getJavaTypeName(), i.asInstanceOf[AnyRef], e.getName());
              }
            buildString("}");
          }
        }

        for(i <- this.minimumArrayLength until entries.length) {
          buildString("if(length <= %d) { return _$$_t; }", i.asInstanceOf[AnyRef]);

          val e = entries(i);
          if(!e.isAvailable()) {
            buildString("$1.unpackObject();");
          }else{

            buildString("if($1.tryUnpackNull()) {");
              // this is Optional field becaue i >= minimumArrayLength
              // Optional + nil => keep default value
            buildString("} else {");
              val t = e.getType();
              if(t.isPrimitive()) {
                buildString("_$$_t.%s_$eq( $1.%s());", e.getName(), primitiveUnpackName(t));
              } else {
                buildString("_$$_t.%s_$eq( (%s)this.templates[%d].unpack($1, _$$_t.%s) );", e.getName(), e.getJavaTypeName(), i.asInstanceOf[AnyRef], e.getName());
              }
            buildString("}");
          }
        }

        // latter entries are all Optional + nil => keep default value

        buildString("for(int i=%d; i < length; i++) {", entries.length.asInstanceOf[AnyRef]);
        buildString("  $1.unpackObject();");
        buildString("}");

        buildString("return _$$_t;");

        buildString("}");
        return getBuiltString();
      }

    protected override def buildConvertMethodBody() : String = {
      resetStringBuilder();
      buildString("{ ");

      buildString("%s _$$_t;", this.origName);
      buildString("if($2 == null) {");
      buildString("  _$$_t = new %s();", this.origName);
      buildString("} else {");
      buildString("  _$$_t = (%s)$2;", this.origName);
      buildString("}");

      buildString("%s[] array = $1.asArray();", classOf[MessagePackObject].getName());
      buildString("int length = array.length;");
      buildString("if(length < %d) {", this.minimumArrayLength.asInstanceOf[AnyRef]);
      buildString("  throw new %s();", classOf[MessageTypeException].getName());
      buildString("}");

      buildString("%s obj;", classOf[MessagePackObject].getName());

      for(i <- 0 until this.minimumArrayLength) {
        val e = entries(i);
        if(e.isAvailable()) {
          buildString("obj = array[%d];", i.asInstanceOf[AnyRef]);
          buildString("if(obj.isNil()) {");
            if(e.isRequired()) {
              // Required + nil => exception
              buildString("throw new %s();", classOf[MessageTypeException].getName());
            } else if(e.isOptional()) {
              // Optional + nil => keep default value
            } else {  // Nullable
              // Nullable + nil => set null
              buildString("_$$_t.%s_$eq( null );", e.getName());
            }
          buildString("} else {");
            val t = e.getType();
            if(t.isPrimitive()) {
              buildString("_$$_t.%s_$eq( obj.%s());", e.getName(), primitiveConvertName(t));
            } else {
              buildString("_$$_t.%s_$eq( (%s)this.templates[%d].convert(obj, _$$_t.%s()) );", e.getName(), e.getJavaTypeName(), i.asInstanceOf[AnyRef], e.getName());
            }
          buildString("}");
        }
      }

      for(i <- this.minimumArrayLength until entries.length) {
        buildString("if(length <= %d) { return _$$_t; }", i.asInstanceOf[AnyRef]);

        val e = entries(i);
        if(e.isAvailable()) {


          buildString("obj = array[%d];", i.asInstanceOf[AnyRef]);
          buildString("if(obj.isNil()) {");
            // this is Optional field becaue i >= minimumArrayLength
            // Optional + nil => keep default value
          buildString("} else {");
            val t = e.getType();
            if(t.isPrimitive()) {
              buildString("_$$_t.%s_$eq( obj.%s());", e.getName(), primitiveConvertName(t));
            } else {
              buildString("_$$_t.%s_$eq( (%s)this.templates[%d].convert(obj, _$$_t.%s) );", e.getName(), e.getJavaTypeName(), i.asInstanceOf[AnyRef], e.getName());
            }
          buildString("}");
        }
      }

      // latter entries are all Optional + nil => keep default value

      buildString("return _$$_t;");

      buildString("}");
      return getBuiltString();
    }
  }

class ScalaFieldEntryReader extends IFieldEntryReader{

  type Property = (Method,Method)
  type PropertySet = (String,Property)

  def readImplicitFieldOption(targetClass: Class[_]) = {
    FieldOption.NULLABLE
  }

  def convertFieldEntries(targetClass: Class[_], flist: FieldList) = {

    val list : List[FieldList.Entry] = flist.getList.asScala.toList

    list.map( s => {
      if(s.isAvailable){
        val getter = targetClass.getMethod(s.getName)
        if(getter.getReturnType.getName != "void"){
          val setter = targetClass.getMethod(s.getName + "_$eq",getter.getReturnType)
          if(setter.getReturnType.getName == "void"){
            val prop = (s.getName,(getter,setter))
            convertToScalaFieldEntry(prop)
          }else{
            new ScalaFieldEntry("")
          }
        }else new ScalaFieldEntry("")
      }else{
        new ScalaFieldEntry("")
      }
    }).toArray
  }

  def readFieldEntries(targetClass: Class[_], implicitOption: FieldOption) = {
    val props = findPropertyMethods(targetClass) filter( !hasAnnotation(_,classOf[Ignore]))

    val indexed = indexing(props)
    indexed.map(convertToScalaFieldEntry(_))
  }


  def setter_?(method : Method) : Boolean = {
    Modifier.isPublic(method.getModifiers) &&
    method.getReturnType.getName == "void" &&
    method.getName.endsWith("_$eq") &&
    method.getParameterTypes.length == 1
  }

  def getter_?(method : Method) : Boolean = {
    Modifier.isPublic(method.getModifiers) &&
    method.getReturnType.getName != "void" &&
    method.getParameterTypes.length == 0

  }




  def findPropertyMethods(targetClass: Class[_]) : Map[String,(Method,Method)] = {
    var getters : Map[String,Method] = ListMap.empty
    var setters : Map[String,Method] = ListMap.empty

    def extractName( n : String) = {
      n.substring(0,n.length - 4)
    }

    //Find getters and setters
    for( m <- targetClass.getMethods){
      if(setter_?(m)){
        setters +=(extractName(m.getName) -> m)
      }else if(getter_?(m)){
        getters +=(m.getName -> m)
      }
    }

    var props : Map[String,Property] = ListMap.empty

    def sameType_?( getter : Method,setter : Method) = {
      getter.getReturnType == setter.getParameterTypes()(0)
    }

    for(g <- getters){
      setters.get(g._1).map( s => {
        if(sameType_?(g._2,s)){
          props +=( g._1 -> (g._2,s))
        }
      })
    }
    props
  }

  def indexing( props : Map[String , Property]) : Array[PropertySet] = {
    val indexed = new Array[PropertySet](props.size)

    var notIndexed : List[PropertySet]  = Nil

    for(s <- props){
      val i = getAnnotation(s,classOf[Index])
      if(i == null){
        notIndexed = notIndexed :+ s
      }else{
        val index = i.value
        if(indexed(index) != null){
          throw new TemplateBuildException("duplicated index: "+index);
        }else{
          try{
            indexed(index) = s
          }catch{
            case e : Exception => {
              throw new TemplateBuildException("invalid index: %s index must be 0 <= x < %s".format(index,indexed.length));
            }
          }
        }
      }
    }

    for( i <- 0 until indexed.length ){
      if(indexed(i) == null){
        indexed(i) = notIndexed.head
        notIndexed = notIndexed.drop(1)
      }
    }


    indexed
  }

  def convertToScalaFieldEntry( propInfo : PropertySet) = {
    val entry = new ScalaFieldEntry(propInfo._1)
    entry.getOption = readFieldOption(propInfo,FieldOption.NULLABLE)
    entry.getType = readValueType(propInfo)
    entry.getGenericType = readGenericType(propInfo)

    entry
  }


  def hasAnnotation[T <: JavaAnnotation](prop : PropertySet , classOfAnno : Class[T]) : Boolean = {
    val getter = prop._2._1
    val setter = prop._2._2

    getter.getAnnotation(classOfAnno) != null ||
    setter.getAnnotation(classOfAnno) != null
  }
  def getAnnotation[T <: JavaAnnotation](prop : PropertySet , classOfAnno : Class[T]) : T = {
    val getter = prop._2._1
    val setter = prop._2._2

    val a = getter.getAnnotation(classOfAnno)
    if(a != null){
      a
    }else{
      setter.getAnnotation(classOfAnno)
    }
  }

  def readFieldOption(prop : PropertySet , implicitOption : FieldOption) = {
    if(hasAnnotation(prop,classOf[Required])){
      FieldOption.REQUIRED
    } else if(hasAnnotation(prop,classOf[Optional])){
      FieldOption.OPTIONAL
    } else if(hasAnnotation(prop,classOf[Nullable])){
      if(readValueType(prop).isPrimitive){
        FieldOption.REQUIRED
      }else{
        FieldOption.NULLABLE
      }
    } else{
      if(implicitOption == FieldOption.NULLABLE){
        if(readValueType(prop).isPrimitive){
          FieldOption.REQUIRED
        }else{
          FieldOption.NULLABLE
        }
      }else{
        implicitOption
      }
    }

  }

  def readValueType(prop : PropertySet) = {
    prop._2._1.getReturnType
  }
  def readGenericType(prop : PropertySet) = {
    prop._2._1.getGenericReturnType
  }
}

class ScalaFieldEntry(var getName : String) extends IFieldEntry{

  def isNullable = {getOption == FieldOption.NULLABLE}

  def isOptional = {getOption == FieldOption.OPTIONAL}

  def isRequired = {getOption == FieldOption.REQUIRED}

  def isAvailable = {getOption != FieldOption.IGNORE}

  var getOption : FieldOption = null

  var getGenericType : Type = null

  def getJavaTypeName = {
    if(getType.isArray){
      getType.getName()
    }else{
      getType.getName()
    }

  }

  var getType : Class[_] = null

}