/* -*- Mode: java; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

package org.mozilla.javascript;

import org.dynalang.dynalink.CallSiteDescriptor;
import org.dynalang.dynalink.linker.ConversionComparator;
import org.dynalang.dynalink.linker.LinkerServices;
import org.dynalang.dynalink.support.TypeUtilities;

import java.lang.reflect.Array;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.function.BiPredicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * This class reflects Java methods into the JavaScript environment and
 * handles overloading of methods.
 *
 * @author Mike Shaver
 * @see NativeJavaArray
 * @see NativeJavaPackage
 * @see NativeJavaClass
 */

public class NativeJavaMethod extends BaseFunction
{
    private static final long serialVersionUID = -3440381785576412928L;

    NativeJavaMethod(MemberBox[] methods)
    {
        this.functionName = methods[0].getName();
        this.methods = methods;
    }

    NativeJavaMethod(MemberBox[] methods, String name)
    {
        this.functionName = name;
        this.methods = methods;
    }

    NativeJavaMethod(MemberBox method, String name)
    {
        this.functionName = name;
        this.methods = new MemberBox[] { method };
    }

    public NativeJavaMethod(Method method, String name)
    {
        this(new MemberBox(method), name);
    }

    @Override
    public String getFunctionName()
    {
        return functionName;
    }

    static String scriptSignature(Object[] values)
    {
        StringBuilder sig = new StringBuilder();
        for (int i = 0; i != values.length; ++i) {
            Object value = values[i];

            String s;
            if (value == null) {
                s = "null";
            } else if (value instanceof Boolean) {
                s = "boolean";
            } else if (value instanceof String) {
                s = "string";
            } else if (value instanceof Number) {
                s = "number";
            } else if (value instanceof Scriptable) {
                if (value instanceof Undefined) {
                    s = "undefined";
                } else if (value instanceof Wrapper) {
                    Object wrapped = ((Wrapper)value).unwrap();
                    s = wrapped.getClass().getName();
                } else if (value instanceof Function) {
                    s = "function";
                } else {
                    s = "object";
                }
            } else {
                s = JavaMembers.javaSignature(value.getClass());
            }

            if (i != 0) {
                sig.append(',');
            }
            sig.append(s);
        }
        return sig.toString();
    }

    @Override
    String decompile(int indent, int flags)
    {
        StringBuilder sb = new StringBuilder();
        boolean justbody = (0 != (flags & Decompiler.ONLY_BODY_FLAG));
        if (!justbody) {
            sb.append("function ");
            sb.append(getFunctionName());
            sb.append("() {");
        }
        sb.append("/*\n");
        sb.append(toString());
        sb.append(justbody ? "*/\n" : "*/}\n");
        return sb.toString();
    }

    @Override
    public String toString()
    {
        StringBuilder sb = new StringBuilder();
        for (int i = 0, N = methods.length; i != N; ++i) {
            // Check member type, we also use this for overloaded constructors
            if (methods[i].isMethod()) {
                Method method = methods[i].method();
                sb.append(JavaMembers.javaSignature(method.getReturnType()));
                sb.append(' ');
                sb.append(method.getName());
            } else {
                sb.append(methods[i].getName());
            }
            sb.append(JavaMembers.liveConnectSignature(methods[i].argTypes));
            sb.append('\n');
        }
        return sb.toString();
    }

    @Override
    public Object call(Context cx, Scriptable scope, Scriptable thisObj,
                       Object[] args)
    {
        // Find a method that matches the types given.
        if (methods.length == 0) {
            throw new RuntimeException("No methods defined for call");
        }

        int index = findCachedFunction(cx, args);
        if (index < 0) {
            Class<?> c = methods[0].method().getDeclaringClass();
            String sig = c.getName() + '.' + getFunctionName() + '(' +
                         scriptSignature(args) + ')';
            throw Context.reportRuntimeError1("msg.java.no_such_method", sig);
        }

        MemberBox meth = methods[index];
        Class<?>[] argTypes = meth.argTypes;

        if (meth.vararg) {
            // marshall the explicit parameters
            Object[] newArgs = new Object[argTypes.length];
            for (int i = 0; i < argTypes.length-1; i++) {
                newArgs[i] = Context.jsToJava(args[i], argTypes[i]);
            }

            Object varArgs;

            // Handle special situation where a single variable parameter
            // is given and it is a Java or ECMA array or is null.
            if (args.length == argTypes.length &&
                (args[args.length-1] == null ||
                 args[args.length-1] instanceof NativeArray ||
                 args[args.length-1] instanceof NativeJavaArray))
            {
                // convert the ECMA array into a native array
                varArgs = Context.jsToJava(args[args.length-1],
                                           argTypes[argTypes.length - 1]);
            } else {
                // marshall the variable parameters
                Class<?> componentType = argTypes[argTypes.length - 1].
                                         getComponentType();
                varArgs = Array.newInstance(componentType,
                                            args.length - argTypes.length + 1);
                for (int i = 0; i < Array.getLength(varArgs); i++) {
                    Object value = Context.jsToJava(args[argTypes.length-1 + i],
                                                    componentType);
                    Array.set(varArgs, i, value);
                }
            }

            // add varargs
            newArgs[argTypes.length-1] = varArgs;
            // replace the original args with the new one
            args = newArgs;
        } else {
            // First, we marshall the args.
            Object[] origArgs = args;
            for (int i = 0; i < args.length; i++) {
                Object arg = args[i];
                Object coerced = Context.jsToJava(arg, argTypes[i]);
                if (coerced != arg) {
                    if (origArgs == args) {
                        args = args.clone();
                    }
                    args[i] = coerced;
                }
            }
        }
        Object javaObject;
        if (meth.isStatic()) {
            javaObject = null;  // don't need an object
        } else {
            Scriptable o = thisObj;
            Class<?> c = meth.getDeclaringClass();
            for (;;) {
                if (o == null) {
                    throw Context.reportRuntimeError3(
                        "msg.nonjava.method", getFunctionName(),
                        ScriptRuntime.toString(thisObj), c.getName());
                }
                if (o instanceof Wrapper) {
                    javaObject = ((Wrapper)o).unwrap();
                    if (c.isInstance(javaObject)) {
                        break;
                    }
                }
                o = o.getPrototype();
            }
        }
        if (debug) {
            printDebug("Calling ", meth, args);
        }

        Object retval = meth.invoke(javaObject, args);
        Class<?> staticType = meth.method().getReturnType();

        if (debug) {
            Class<?> actualType = (retval == null) ? null
                                                : retval.getClass();
            System.err.println(" ----- Returned " + retval +
                               " actual = " + actualType +
                               " expect = " + staticType);
        }

        Object wrapped = cx.getWrapFactory().wrap(cx, scope,
                                                  retval, staticType);
        if (debug) {
            Class<?> actualType = (wrapped == null) ? null
                                                 : wrapped.getClass();
            System.err.println(" ----- Wrapped as " + wrapped +
                               " class = " + actualType);
        }

        if (wrapped == null && staticType == Void.TYPE) {
            wrapped = Undefined.instance;
        }
        return wrapped;
    }

    int findCachedFunction(Context cx, Object[] args) {
        if (methods.length > 1) {
            for (ResolvedOverload ovl : overloadCache) {
                if (ovl.matches(args)) {
                    return ovl.index;
                }
            }
            int index = findFunction(cx, methods, args);
            // As a sanity measure, don't let the lookup cache grow longer
            // than twice the number of overloaded methods
            if (overloadCache.size() < methods.length * 2) {
                ResolvedOverload ovl = new ResolvedOverload(args, index);
                overloadCache.addIfAbsent(ovl);
            }
            return index;
        }
        return findFunction(cx, methods, args);
    }

    //////////// start source code based on BSD license ////////////
    /*
    this part of source code obtain the modified copy of source code of the private part of dynalink.
    the dynalink is released under 3-cause BSD License.
    the copy of 3-cause BSD License is shown below:

       Copyright 2009-2013 Attila Szegedi

       Redistribution and use in source and binary forms, with or without
       modification, are permitted provided that the following conditions are
       met:
       * Redistributions of source code must retain the above copyright
         notice, this list of conditions and the following disclaimer.
       * Redistributions in binary form must reproduce the above copyright
         notice, this list of conditions and the following disclaimer in the
         documentation and/or other materials provided with the distribution.
       * Neither the name of the copyright holder nor the names of
         contributors may be used to endorse or promote products derived from
         this software without specific prior written permission.

       THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
       IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
       TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
       PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDER
       BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
       CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
       SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
       BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
       WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
       OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
       ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
     */

    /**
     * Find the index of the correct function to call given the set of methods
     * or constructors and the arguments.
     * If no function can be found to call, return -1.
     * 
     * most part of this function is copied from {@link org.dynalang.dynalink.beans.OverloadedDynamicMethod#getInvocation(CallSiteDescriptor, LinkerServices)}
     */
    static int findFunction(Context cx,
                            MemberBox[] methods, Object[] args) {
        LinkerServices linkerServices = Context.getLinker().getLinkerServices();
        Class<?>[] argTypes = Arrays.stream(args).map(Context::getClassLink).toArray(Class[]::new);

        // First, find all methods applicable to the call site by subtyping (JLS 15.12.2.2)
        final List<MemberBox> subtypingApplicables = getApplicables(argTypes, methods, APPLICABLE_BY_SUBTYPING);
        // Next, find all methods applicable by method invocation conversion to the call site (JLS 15.12.2.3).
        final List<MemberBox> methodInvocationApplicables = getApplicables(argTypes, methods, APPLICABLE_BY_METHOD_INVOCATION_CONVERSION);
        // Finally, find all methods applicable by variable arity invocation. (JLS 15.12.2.4).
        final List<MemberBox> variableArityApplicables = getApplicables(argTypes, methods, APPLICABLE_BY_VARIABLE_ARITY);

        // Find the methods that are maximally specific based on the call site signature
        
        List<MemberBox> maximallySpecifics = getMaximallySpecificMethods(subtypingApplicables, false, argTypes, linkerServices);
        if(maximallySpecifics.isEmpty()) {
            maximallySpecifics = getMaximallySpecificMethods(methodInvocationApplicables, false, argTypes, linkerServices);
            if(maximallySpecifics.isEmpty()) {
                maximallySpecifics = getMaximallySpecificMethods(variableArityApplicables, false, argTypes, linkerServices);
            }
        }

        // Now, get a list of the rest of the methods; those that are *not* applicable to the call site signature based
        // on JLS rules. As paradoxical as that might sound, we have to consider these for dynamic invocation, as they
        // might match more concrete types passed in invocations. That's why we provisionally call them "invokables".
        // This is typical for very generic signatures at call sites. Typical example: call site specifies
        // (Object, Object), and we have a method whose parameter types are (String, int). None of the JLS applicability
        // rules will trigger, but we must consider the method, as it can be the right match for a concrete invocation.
        List<MemberBox> invokables = new ArrayList<>(Arrays.asList(methods));
        invokables.removeAll(subtypingApplicables);
        invokables.removeAll(methodInvocationApplicables);
        invokables.removeAll(variableArityApplicables);

        invokables.removeIf(m -> !isApplicableDynamically(linkerServices, argTypes, m));

        // If no additional methods can apply at invocation time, and there's more than one maximally specific method
        // based on call site signature, that is a link-time ambiguity. In a static scenario, javac would report an
        // ambiguity error.
        if (!invokables.isEmpty() || maximallySpecifics.size() <= 1) {
            // Merge them all.
            invokables.addAll(maximallySpecifics);
            switch (invokables.size()) {
                case 0: {
                    // No overloads can ever match the call site type
                    return -1;
                }
                case 1: {
                    // Very lucky, we ended up with a single candidate method handle based on the call site signature; we
                    // can link it very simply by delegating to the SingleDynamicMethod.
                    return Arrays.asList(methods).indexOf(invokables.iterator().next());
                }
                default: {
                    // We have more than one candidate. We have no choice but to link to a method that resolves overloads on
                    // every invocation (alternatively, we could opportunistically link the one method that resolves for the
                    // current arguments, but we'd need to install a fairly complex guard for that and when it'd fail, we'd
                    // go back all the way to candidate selection. Note that we're resolving any potential caller sensitive
                    // methods here to their handles, as the OverloadedMethod instance is specific to a call site, so it
                    // has an already determined Lookup.
                    final List<MemberBox> methodHandles = invokables;

                    final List<MemberBox> selected = selectMethod(argTypes, methodHandles, linkerServices);
                    if (selected.size() == 0) return -1;
                    if (selected.size() == 1) return Arrays.asList(methods).indexOf(selected.iterator().next());

                    // for error, use selected
                    invokables = selected;
                }
            }
        } else {
            invokables.addAll(maximallySpecifics);
        }


        // report remaining ambiguity
        StringBuilder buf = new StringBuilder();
        for (MemberBox invokable : invokables) {
            buf.append("\n    ");
            buf.append(invokable.toJavaDeclaration());
        }

        MemberBox firstFitMember = invokables.iterator().next();
        String memberName = firstFitMember.getName();
        String memberClass = firstFitMember.getDeclaringClass().getName();

        if (methods[0].isCtor()) {
            throw Context.reportRuntimeError3(
                "msg.constructor.ambiguous",
                memberName, scriptSignature(args), buf.toString());
        }
        throw Context.reportRuntimeError4(
            "msg.method.ambiguous", memberClass,
            memberName, scriptSignature(args), buf.toString());
    }

    /**
     * this is based on a copy of {@link org.dynalang.dynalink.beans.OverloadedMethod#selectMethod(Object[])}
     */
    @SuppressWarnings("unused")
    private static List<MemberBox> selectMethod(Class<?>[] argTypes, List<MemberBox> methodsIn, LinkerServices linkerServices) {
        List<MemberBox> fixArgMethods = methodsIn.stream().filter(it -> !it.vararg).collect(Collectors.toList());
        List<MemberBox> varArgMethods = methodsIn.stream().filter(it -> it.vararg).collect(Collectors.toList());
        
        List<MemberBox> methods = getMaximallySpecificMethods(fixArgMethods, false, argTypes, linkerServices);
        if(methods.isEmpty()) {
            methods = getMaximallySpecificMethods(varArgMethods, true, argTypes, linkerServices);
        }
        return methods;
        // no cache
    }

    private static final BiPredicate<Class<?>[], MemberBox> APPLICABLE_BY_SUBTYPING = (callSiteType, method) -> {
        int methodArity = method.argTypes.length;
        if (methodArity != callSiteType.length) {
            return false;
        } else {
            for (int i = 0; i < methodArity; ++i) {
                if (!TypeUtilities.isSubtype(callSiteType[i], method.argTypes[i])) {
                    return false;
                }
            }

            return true;
        }
    };

    private static final BiPredicate<Class<?>[], MemberBox> APPLICABLE_BY_METHOD_INVOCATION_CONVERSION = (callSiteType, method) -> {
        int methodArity = method.argTypes.length;
        if (methodArity != callSiteType.length) {
            return false;
        } else {
            for (int i = 0; i < methodArity; ++i) {
                if (!TypeUtilities.isMethodInvocationConvertible(callSiteType[i], method.argTypes[i])) {
                    return false;
                }
            }

            return true;
        }
    };

    private static final BiPredicate<Class<?>[], MemberBox> APPLICABLE_BY_VARIABLE_ARITY = (callSiteType, method) -> {
        if (!method.vararg) return false;

        int methodArity = method.argTypes.length;
        int fixArity = methodArity - 1;
        int callSiteArity = callSiteType.length;
        if (fixArity > callSiteArity) {
            return false;
        } else {
            for (int i = 0; i < fixArity; ++i) {
                if (!TypeUtilities.isMethodInvocationConvertible(callSiteType[i], method.argTypes[i])) {
                    return false;
                }
            }

            Class<?> varArgType = method.argTypes[fixArity].getComponentType();

            for (int ix = fixArity; ix < callSiteArity; ++ix) {
                if (!TypeUtilities.isMethodInvocationConvertible(callSiteType[ix], varArgType)) {
                    return false;
                }
            }

            return true;
        }
    };

    private static List<MemberBox> getApplicables(Class<?>[] argTypes, MemberBox[] methods, BiPredicate<Class<?>[], MemberBox> condition) {
        return Arrays.stream(methods)
                .filter(it -> condition.test(argTypes, it))
                .collect(Collectors.toList());
    }

    private static List<MemberBox> getMaximallySpecificMethods(List<MemberBox> methods, boolean varArgs, Class<?>[] argTypes, LinkerServices ls) {
        if (methods.size() < 2) {
            // empty array or 0
            return methods;
        } else {
            LinkedList<MemberBox> maximals = new LinkedList<>();
            for (MemberBox m : methods) {
                Class<?>[] mArgTypes = m.argTypes;
                boolean lessSpecific = false;
                Iterator<MemberBox> maximal = maximals.iterator();

                while (maximal.hasNext()) {
                    MemberBox max = maximal.next();
                    switch (isMoreSpecific(mArgTypes, max.argTypes, varArgs, argTypes, ls)) {
                        case TYPE_1_BETTER:
                            maximal.remove();
                            break;
                        case TYPE_2_BETTER:
                            lessSpecific = true;
                        case INDETERMINATE:
                            break;
                        default:
                            throw new AssertionError();
                    }
                }

                if (!lessSpecific) {
                    maximals.addLast(m);
                }
            }

            return maximals;
        }
    }

    private static ConversionComparator.Comparison isMoreSpecific(Class<?>[] t1, Class<?>[] t2, boolean varArgs, Class<?>[] argTypes, LinkerServices ls) {
        int pc1 = t1.length;
        int pc2 = t2.length;

        assert varArgs || pc1 == pc2 && (argTypes == null || argTypes.length == pc1);

        assert argTypes == null == (ls == null);

        int maxPc = Math.max(Math.max(pc1, pc2), argTypes == null ? 0 : argTypes.length);
        boolean t1MoreSpecific = false;
        boolean t2MoreSpecific = false;

        for(int i = 0; i < maxPc; ++i) {
            Class<?> c1 = getParameterClass(t1, pc1, i, varArgs);
            Class<?> c2 = getParameterClass(t2, pc2, i, varArgs);
            if (c1 != c2) {
                ConversionComparator.Comparison cmp = compare(c1, c2, argTypes, i, ls);
                if (cmp == ConversionComparator.Comparison.TYPE_1_BETTER && !t1MoreSpecific) {
                    t1MoreSpecific = true;
                    if (t2MoreSpecific) {
                        return ConversionComparator.Comparison.INDETERMINATE;
                    }
                }

                if (cmp == ConversionComparator.Comparison.TYPE_2_BETTER && !t2MoreSpecific) {
                    t2MoreSpecific = true;
                    if (t1MoreSpecific) {
                        return ConversionComparator.Comparison.INDETERMINATE;
                    }
                }
            }
        }

        if (t1MoreSpecific) {
            return ConversionComparator.Comparison.TYPE_1_BETTER;
        } else if (t2MoreSpecific) {
            return ConversionComparator.Comparison.TYPE_2_BETTER;
        } else {
            return ConversionComparator.Comparison.INDETERMINATE;
        }
    }

    private static ConversionComparator.Comparison compare(Class<?> c1, Class<?> c2, Class<?>[] argTypes, int i, LinkerServices cmp) {
        if (cmp != null) {
            ConversionComparator.Comparison c = cmp.compareConversion(argTypes[i], c1, c2);
            if (c != ConversionComparator.Comparison.INDETERMINATE) {
                return c;
            }
        }

        if (TypeUtilities.isSubtype(c1, c2)) {
            return ConversionComparator.Comparison.TYPE_1_BETTER;
        } else {
            return TypeUtilities.isSubtype(c2, c1) ? ConversionComparator.Comparison.TYPE_2_BETTER : ConversionComparator.Comparison.INDETERMINATE;
        }
    }

    private static Class<?> getParameterClass(Class<?>[] argTypes, int l, int i, boolean varArgs) {
        return varArgs && i >= l - 1 ? argTypes[l - 1].getComponentType() : argTypes[i];
    }

    private static boolean isApplicableDynamically(LinkerServices linkerServices, Class<?>[] callSiteType, MemberBox m) {
        Class<?>[] methodArgTypes = m.argTypes;
        boolean varArgs = m.vararg;
        int minArgLength = methodArgTypes.length - (varArgs ? 1 : 0);
        int callSiteArgLen = callSiteType.length;

        if (varArgs) {
            if (callSiteArgLen < minArgLength) {
                return false;
            }
        } else if (callSiteArgLen != minArgLength) {
            return false;
        }

        if (!IntStream.range(0, minArgLength)
                .allMatch(i -> isApplicableDynamically(linkerServices, callSiteType[i], methodArgTypes[i])))
            return false;

        if (varArgs) {
            Class<?> varArgArrayType = methodArgTypes[minArgLength];
            Class<?> varArgType = varArgArrayType.getComponentType();
            if (minArgLength + 1 == callSiteArgLen) {
                // if length of parameters and arguments are same, it may be array
                Class<?> callSiteArgType = callSiteType[minArgLength];
                return isApplicableDynamically(linkerServices, callSiteArgType, varArgArrayType)
                        || isApplicableDynamically(linkerServices, callSiteArgType, varArgType);
            } else {
                for(int i = minArgLength; i < callSiteArgLen; ++i) {
                    if (!isApplicableDynamically(linkerServices, callSiteType[i], varArgType)) {
                        return false;
                    }
                }

                return true;
            }
        } else {
            return true;
        }
    }

    private static boolean isApplicableDynamically(LinkerServices linkerServices, Class<?> callSiteType, Class<?> methodType) {
        return TypeUtilities.isPotentiallyConvertible(callSiteType, methodType) || linkerServices.canConvert(callSiteType, methodType);
    }

    ////////////  end source code based on BSD license  ////////////


    private static final boolean debug = false;

    private static void printDebug(String msg, MemberBox member,
                                   Object[] args)
    {
        if (debug) {
            StringBuilder sb = new StringBuilder();
            sb.append(" ----- ");
            sb.append(msg);
            sb.append(member.getDeclaringClass().getName());
            sb.append('.');
            if (member.isMethod()) {
                sb.append(member.getName());
            }
            sb.append(JavaMembers.liveConnectSignature(member.argTypes));
            sb.append(" for arguments (");
            sb.append(scriptSignature(args));
            sb.append(')');
            System.out.println(sb);
        }
    }

    MemberBox[] methods;
    private String functionName;
    private transient final CopyOnWriteArrayList<ResolvedOverload> overloadCache = new CopyOnWriteArrayList<>();
}

class ResolvedOverload {
    final Class<?>[] types;
    final int index;

    ResolvedOverload(Object[] args, int index) {
        this.index = index;
        types = new Class<?>[args.length];
        for (int i = 0, l = args.length; i < l; i++) {
            Object arg = args[i];
            if (arg instanceof Wrapper)
                arg = ((Wrapper)arg).unwrap();
            types[i] = arg == null ? null : arg.getClass();
        }
    }

    boolean matches(Object[] args) {
        if (args.length != types.length) {
            return false;
        }
        for (int i = 0, l = args.length; i < l; i++) {
            Object arg = args[i];
            if (arg instanceof Wrapper)
                arg = ((Wrapper)arg).unwrap();
            if (arg == null) {
                if (types[i] != null) return false;
            } else if (arg.getClass() != types[i]) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof ResolvedOverload)) {
            return false;
        }
        ResolvedOverload ovl = (ResolvedOverload) other;
        return Arrays.equals(types, ovl.types) && index == ovl.index;
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(types);
    }
}
