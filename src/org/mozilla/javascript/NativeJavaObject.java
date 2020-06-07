/* -*- Mode: java; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

package org.mozilla.javascript;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.reflect.Method;
import java.util.Map;

/**
 * This class reflects non-Array Java objects into the JavaScript environment.  It
 * reflect fields directly, and uses NativeJavaMethod objects to reflect (possibly
 * overloaded) methods.<p>
 *
 * @author Mike Shaver
 * @see NativeJavaArray
 * @see NativeJavaPackage
 * @see NativeJavaClass
 */

public class NativeJavaObject
    implements Scriptable, SymbolScriptable, Wrapper, Serializable
{
    private static final long serialVersionUID = -6948590651130498591L;

    public NativeJavaObject() { }

    public NativeJavaObject(Scriptable scope, Object javaObject,
                            Class<?> staticType)
    {
        this(scope, javaObject, staticType, false);
    }

    public NativeJavaObject(Scriptable scope, Object javaObject,
                            Class<?> staticType, boolean isAdapter)
    {
        this.parent = scope;
        this.javaObject = javaObject;
        this.staticType = staticType;
        this.isAdapter = isAdapter;
        initMembers();
    }

    protected void initMembers() {
        Class<?> dynamicType;
        if (javaObject != null) {
            dynamicType = javaObject.getClass();
        } else {
            dynamicType = staticType;
        }
        members = JavaMembers.lookupClass(parent, dynamicType, staticType,
                                          isAdapter);
        fieldAndMethods
            = members.getFieldAndMethodsObjects(this, javaObject, false);
    }

    @Override
    public boolean has(String name, Scriptable start) {
        return members.has(name, false);
    }

    @Override
    public boolean has(int index, Scriptable start) {
        return false;
    }

    @Override
    public boolean has(Symbol key, Scriptable start) {
        return false;
    }

    @Override
    public Object get(String name, Scriptable start) {
        if (fieldAndMethods != null) {
            Object result = fieldAndMethods.get(name);
            if (result != null) {
                return result;
            }
        }
        // TODO: passing 'this' as the scope is bogus since it has
        //  no parent scope
        return members.get(this, name, javaObject, false);
    }

    @Override
    public Object get(Symbol key, Scriptable start) {
        // Native Java objects have no Symbol members
        return Scriptable.NOT_FOUND;
    }

    @Override
    public Object get(int index, Scriptable start) {
        throw members.reportMemberNotFound(Integer.toString(index));
    }

    @Override
    public void put(String name, Scriptable start, Object value) {
        // We could be asked to modify the value of a property in the
        // prototype. Since we can't add a property to a Java object,
        // we modify it in the prototype rather than copy it down.
        if (prototype == null || members.has(name, false))
            members.put(this, name, javaObject, value, false);
        else
            prototype.put(name, prototype, value);
    }

    @Override
    public void put(Symbol symbol, Scriptable start, Object value) {
        // We could be asked to modify the value of a property in the
        // prototype. Since we can't add a property to a Java object,
        // we modify it in the prototype rather than copy it down.
        String name = symbol.toString();
        if (prototype == null || members.has(name, false)) {
            members.put(this, name, javaObject, value, false);
        } else if (prototype instanceof SymbolScriptable) {
            ((SymbolScriptable)prototype).put(symbol, prototype, value);
        }
    }

    @Override
    public void put(int index, Scriptable start, Object value) {
        throw members.reportMemberNotFound(Integer.toString(index));
    }

    @Override
    public boolean hasInstance(Scriptable value) {
        // This is an instance of a Java class, so always return false
        return false;
    }

    @Override
    public void delete(String name) {
    }

    @Override
    public void delete(Symbol key) {
    }

    @Override
    public void delete(int index) {
    }

    @Override
    public Scriptable getPrototype() {
        if (prototype == null && javaObject instanceof String) {
            return TopLevel.getBuiltinPrototype(
                    ScriptableObject.getTopLevelScope(parent),
                    TopLevel.Builtins.String);
        }
        return prototype;
    }

    /**
     * Sets the prototype of the object.
     */
    @Override
    public void setPrototype(Scriptable m) {
        prototype = m;
    }

    /**
     * Returns the parent (enclosing) scope of the object.
     */
    @Override
    public Scriptable getParentScope() {
        return parent;
    }

    /**
     * Sets the parent (enclosing) scope of the object.
     */
    @Override
    public void setParentScope(Scriptable m) {
        parent = m;
    }

    @Override
    public Object[] getIds() {
        return members.getIds(false);
    }

    /**
     * @deprecated Use {@link Context#getWrapFactory()} together with calling {@link
     * WrapFactory#wrap(Context, Scriptable, Object, Class)}
     */
    @Deprecated
    public static Object wrap(Scriptable scope, Object obj, Class<?> staticType) {

        Context cx = Context.getContext();
        return cx.getWrapFactory().wrap(cx, scope, obj, staticType);
    }

    @Override
    public Object unwrap() {
        return javaObject;
    }

    @Override
    public String getClassName() {
        return "JavaObject";
    }

    @Override
    public Object getDefaultValue(Class<?> hint)
    {
        Object value;
        if (hint == null) {
            if (javaObject instanceof Boolean) {
                hint = ScriptRuntime.BooleanClass;
            }
            if (javaObject instanceof Number) {
                hint = ScriptRuntime.NumberClass;
            }
        }
        if (hint == null || hint == ScriptRuntime.StringClass) {
            value = javaObject.toString();
        } else {
            String converterName;
            if (hint == ScriptRuntime.BooleanClass) {
                converterName = "booleanValue";
            } else if (hint == ScriptRuntime.NumberClass) {
                converterName = "doubleValue";
            } else {
                throw Context.reportRuntimeError0("msg.default.value");
            }
            Object converterObject = get(converterName, this);
            if (converterObject instanceof Function) {
                Function f = (Function)converterObject;
                value = f.call(Context.getContext(), f.getParentScope(),
                               this, ScriptRuntime.emptyArgs);
            } else {
                if (hint == ScriptRuntime.NumberClass
                    && javaObject instanceof Boolean)
                {
                    boolean b = ((Boolean)javaObject).booleanValue();
                    value = ScriptRuntime.wrapNumber(b ? 1.0 : 0.0);
                } else {
                    value = javaObject.toString();
                }
            }
        }
        return value;
    }

    /**
     * Determine whether we can/should convert between the given type and the
     * desired one.  This should be superceded by a conversion-cost calculation
     * function, but for now I'll hide behind precedent.
     */
    public static boolean canConvert(Object fromObj, Class<?> to) {
        return Context.getLinker()
                .getLinkerServices()
                .canConvert(Context.getClassLink(fromObj), to);
    }

    /**
     * Not intended for public use. Callers should use the
     * public API Context.toType.
     * @deprecated as of 1.5 Release 4
     * @see org.mozilla.javascript.Context#jsToJava(Object, Class)
     */
    @Deprecated
    public static Object coerceType(Class<?> type, Object value)
    {
        return coerceTypeImpl(type, value);
    }

    /**
     * Type-munging for field setting and method invocation.
     * Conforms to LC3 specification
     */
    static Object coerceTypeImpl(Class<?> type, Object value) {
        try {
            MethodHandle handle = Context.getLinker()
                .getLinkerServices()
                .getTypeConverter(Context.getClassLink(value), type);
            handle = MethodHandles.explicitCastArguments(handle, MethodType.methodType(Object.class, Object.class));
            return handle.invokeExact(value);
        } catch (Error | RuntimeException e) {
            throw e;
        } catch (Throwable e) {
            throw new RuntimeException(e);
        }
    }

    protected static Object createInterfaceAdapter(Class<?>type, ScriptableObject so) {
        // XXX: Currently only instances of ScriptableObject are
        // supported since the resulting interface proxies should
        // be reused next time conversion is made and generic
        // Callable has no storage for it. Weak references can
        // address it but for now use this restriction.

        Object key = Kit.makeHashKeyFromPair(COERCED_INTERFACE_KEY, type);
        Object old = so.getAssociatedValue(key);
        if (old != null) {
            // Function was already wrapped
            return old;
        }
        Context cx = Context.getContext();
        Object glue = InterfaceAdapter.create(cx, type, so);
        // Store for later retrieval
        glue = so.associateValue(key, glue);
        return glue;
    }


    private void writeObject(ObjectOutputStream out)
        throws IOException
    {
        out.defaultWriteObject();

        out.writeBoolean(isAdapter);
        if (isAdapter) {
            if (adapter_writeAdapterObject == null) {
                throw new IOException();
            }
            Object[] args = { javaObject, out };
            try {
                adapter_writeAdapterObject.invoke(null, args);
            } catch (Exception ex) {
                throw new IOException();
            }
        } else {
            out.writeObject(javaObject);
        }

        if (staticType != null) {
            out.writeObject(staticType.getName());
        } else {
            out.writeObject(null);
        }
    }

    private void readObject(ObjectInputStream in)
        throws IOException, ClassNotFoundException
    {
        in.defaultReadObject();

        isAdapter = in.readBoolean();
        if (isAdapter) {
            if (adapter_readAdapterObject == null)
                throw new ClassNotFoundException();
            Object[] args = { this, in };
            try {
                javaObject = adapter_readAdapterObject.invoke(null, args);
            } catch (Exception ex) {
                throw new IOException();
            }
        } else {
            javaObject = in.readObject();
        }

        String className = (String)in.readObject();
        if (className != null) {
            staticType = Class.forName(className);
        } else {
            staticType = null;
        }

        initMembers();
    }

    /**
     * The prototype of this object.
     */
    protected Scriptable prototype;

    /**
     * The parent scope of this object.
     */
    protected Scriptable parent;

    protected transient Object javaObject;

    protected transient Class<?> staticType;
    protected transient JavaMembers members;
    private transient Map<String,FieldAndMethods> fieldAndMethods;
    protected transient boolean isAdapter;

    private static final Object COERCED_INTERFACE_KEY = "Coerced Interface";
    private static Method adapter_writeAdapterObject;
    private static Method adapter_readAdapterObject;

    static {
        // Reflection in java is verbose
        Class<?>[] sig2 = new Class[2];
        Class<?> cl = Kit.classOrNull("org.mozilla.javascript.JavaAdapter");
        if (cl != null) {
            try {
                sig2[0] = ScriptRuntime.ObjectClass;
                sig2[1] = Kit.classOrNull("java.io.ObjectOutputStream");
                adapter_writeAdapterObject = cl.getMethod("writeAdapterObject",
                                                          sig2);

                sig2[0] = ScriptRuntime.ScriptableClass;
                sig2[1] = Kit.classOrNull("java.io.ObjectInputStream");
                adapter_readAdapterObject = cl.getMethod("readAdapterObject",
                                                         sig2);

            } catch (NoSuchMethodException e) {
                adapter_writeAdapterObject = null;
                adapter_readAdapterObject = null;
            }
        }
    }

}
