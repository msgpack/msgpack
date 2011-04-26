package org.msgpack

import _root_.javassist.{CtClass, CtNewConstructor}
import annotation._
import template._
import builder.JavassistTemplateBuilder.JavassistTemplate
import builder.{BuildContextBase, JavassistTemplateBuilder}
import java.lang.Class
import collection.immutable.{ListMap, TreeMap}
import java.lang.reflect.{Type, Modifier, Method, Field}
import java.lang.annotation.{Annotation => JavaAnnotation}
import scala.collection.JavaConverters._
;
/*
 * Created by IntelliJ IDEA.
 * User: takeshita
 * Date: 11/03/10
 * Time: 12:29
 */


  class BuildContextForScala(builder : JavassistTemplateBuilder) extends BuildContextBase[IFieldEntry](builder){

    var entries : Array[IFieldEntry] = null
    var origClass : Class[_] = null
    var origName : String = null
    var templates : Array[Template] = null
    var minimumArrayLength : Int = 0

    def writeTemplate(targetClass : Class[_] ,  entries : Array[IFieldEntry],
      templates : Array[Template], directoryName : String) = {
      this.entries = entries;
      this.templates = templates;
      this.origClass = targetClass;
      this.origName = this.origClass.getName();
      write(this.origName, directoryName);
	}

    def loadTemplate(targetClass : Class[_] ,  entries : Array[IFieldEntry], templates : Array[Template]) = {
      this.entries = entries;
      this.templates = templates;
      this.origClass = targetClass;
      this.origName = this.origClass.getName();
	  load(this.origName);
	}

    def buildTemplate(targetClass : Class[_] ,  entries : Array[IFieldEntry],  templates : Array[Template]) = {
      this.entries = entries;
      this.templates = templates;
      this.origClass = targetClass;
      this.origName = this.origClass.getName();
      build(this.origName);
	}

    def setSuperClass() = {
      tmplCtClass.setSuperclass(director.getCtClass(classOf[JavassistTemplate].getName))
    }

    def buildConstructor() = {
      val newCtCons = CtNewConstructor.make(
        Array[CtClass](
          director.getCtClass(classOf[Class[_]].getName),
          director.getCtClass(classOf[Template].getName + "[]")
        ),
      new Array[CtClass](0),
      tmplCtClass
      )
      this.tmplCtClass.addConstructor(newCtCons)
    }
    def buildInstance(c : Class[_]) = {
      val cons = c.getConstructor(classOf[Class[_]], classOf[Array[Template]])
      val tmpl = cons.newInstance(origClass,templates)
      tmpl.asInstanceOf[Template]
    }
    override def buildMethodInit() = {
      this.minimumArrayLength = 0;
      var i : Int = 0
      for(e <- entries) {
        if(e.isRequired() || e.isNullable()) {
          this.minimumArrayLength = i+1;
        }
        i += 1
      }
    }

    lazy val newInstanceDeclaration : String = {

      def defCon = "new " + origClass.getName + "();"
      try{
        val c = origClass.getClassLoader.loadClass(origClass.getName + "$")
        if(Modifier.isPublic(c.getModifiers)){
          val method = c.getMethod("apply")

          if(Modifier.isPublic(method.getModifiers) &&
            origClass.isAssignableFrom(method.getReturnType)){
            val staticField = c.getDeclaredField("MODULE$")
             "%s.%s.apply();".format(c.getName,staticField.getName)
          }else{
            defCon
          }
        }else{
          defCon
        }
      }catch{
        case e : ClassNotFoundException => {
          defCon
        }
        case e : NoSuchMethodException => {
          defCon
        }
      }
    }

    protected def buildPackMethodBody() : String = {
      resetStringBuilder();
      buildString("{");
      buildString("%s _$$_t = (%s)$2;", this.origName, this.origName);
      buildString("$1.packArray(%d);", entries.length.asInstanceOf[AnyRef]);
      for(i <- 0 until entries.length) {
        val e = entries(i)

        if(!e.isAvailable) {
          buildString("$1.packNil();");
        }else{
          val t = e.getType;
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


    def buildUnpackMethodBody() : String = {
        resetStringBuilder();
        buildString("{ ");

        buildString("%s _$$_t;", this.origName);
        buildString("if($2 == null) {");
        buildString("  _$$_t = " + newInstanceDeclaration) //new %s();", this.origName);
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
      buildString("  _$$_t = " + newInstanceDeclaration) //new %s();", this.origName);
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

  type Property = (Method,Method,Field)
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
            val f = try{targetClass.getDeclaredField(s.getName)}
            catch{
              case e : NoSuchFieldException => null
            }
            val prop = (s.getName,(getter,setter,f))
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




  def findPropertyMethods(targetClass: Class[_]) : Map[String,Property] = {
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
    /*
    for(g <- getters){
      setters.get(g._1).map( s => {
        if(sameType_?(g._2,s)){

          val name = g._1
          val f = try{targetClass.getDeclaredField(name)}
          catch{
            case e : NoSuchFieldException => null
          }

          //TODO add validation for field
          props +=( name -> (g._2,s,f))
        }
      })
    }*/
    // In some situation, reflection returns wrong ordered getter methods compare with declaration order.
    // So to avoid such situation, list up props with setter methods
    /*for(s <- setters){
      getters.get(s._1).map( g => {
        if(sameType_?(g,s._2)){
          val name = s._1
          val f = try{
            targetClass.getDeclaredField(name)
          }catch{
            case e : NoSuchFieldException => null
          }

          props +=(name -> (g,s._2,f))
        }
      })
    }*/
    // order of methods changes depends on call order, NOT declaration.

    def getterAndSetter(name : String) : Option[(Method,Method)] = {
      if(getters.contains(name) && setters.contains(name)){
        val getter = getters(name)
        val setter = setters(name)
        if(getter.getReturnType == setter.getParameterTypes()(0)){
          Some(getter -> setter)
        }else{
          None
        }
      }else None
    }
    def recursiveFind( clazz : Class[_]) : Unit = {
      if(clazz.getSuperclass != classOf[Object]){
        recursiveFind(clazz.getSuperclass)
      }
      for(f <- clazz.getDeclaredFields){
        val name =f.getName
        getterAndSetter(name) match{
          case Some((g,s)) => props +=( name -> (g,s,f))
          case None => {
            if(name.startsWith("_")){
              val sname = name.substring(1)
              getterAndSetter(sname) match{
                case Some((g,s)) => props +=( sname -> (g,s,f))
                case None =>
              }
            }
          }
        }
      }
    }
    recursiveFind(targetClass)

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
    entry.option = readFieldOption(propInfo,FieldOption.NULLABLE)
    entry.normalType = readValueType(propInfo)
    entry.genericType = readGenericType(propInfo)

    entry
  }


  def hasAnnotation[T <: JavaAnnotation](prop : PropertySet , classOfAnno : Class[T]) : Boolean = {
    val getter = prop._2._1
    val setter = prop._2._2
    val field = prop._2._3
    getter.getAnnotation(classOfAnno) != null ||
    setter.getAnnotation(classOfAnno) != null ||
      {if(field != null) field.getAnnotation(classOfAnno) != null
    else false}
  }
  def getAnnotation[T <: JavaAnnotation](prop : PropertySet , classOfAnno : Class[T]) : T = {
    val getter = prop._2._1
    val setter = prop._2._2
    val field = prop._2._3



    val a = getter.getAnnotation(classOfAnno)
    if(a != null){
      a
    }else{
      val b = setter.getAnnotation(classOfAnno)
      if(b != null){
        b
      }else if(field != null){
        field.getAnnotation(classOfAnno)
      }else{
        null.asInstanceOf[T]
      }
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

class ScalaFieldEntry(name : String) extends IFieldEntry{

  def getName() = name

  def isNullable() = {getOption == FieldOption.NULLABLE}

  def isOptional = {getOption == FieldOption.OPTIONAL}

  def isRequired = {getOption == FieldOption.REQUIRED}

  def isAvailable = {getOption != FieldOption.IGNORE}

  var option : FieldOption = null

  var genericType : Type = null

  def getJavaTypeName = {
    if(getType.isArray){
      getType.getComponentType.getName + "[]"

    }else{
      getType.getName()
    }

  }

  var normalType : Class[_] = null

  def getOption() = option
  def getType() = normalType
  def getGenericType() = genericType

}