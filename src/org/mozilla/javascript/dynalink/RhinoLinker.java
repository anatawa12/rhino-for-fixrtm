package org.mozilla.javascript.dynalink;

import jdk.nashorn.internal.runtime.ECMAErrors;
import org.dynalang.dynalink.linker.ConversionComparator;
import org.dynalang.dynalink.linker.GuardedInvocation;
import org.dynalang.dynalink.linker.GuardingDynamicLinker;
import org.dynalang.dynalink.linker.GuardingTypeConverterFactory;
import org.dynalang.dynalink.linker.LinkRequest;
import org.dynalang.dynalink.linker.LinkerServices;
import org.dynalang.dynalink.support.Guards;
import org.dynalang.dynalink.support.TypeUtilities;
import org.mozilla.javascript.ArrowFunction;
import org.mozilla.javascript.Context;
import org.mozilla.javascript.NativeArray;
import org.mozilla.javascript.NativeFunction;
import org.mozilla.javascript.NativeJavaObject;
import org.mozilla.javascript.NativeObject;
import org.mozilla.javascript.ScriptRuntime;
import org.mozilla.javascript.ScriptableObject;
import org.mozilla.javascript.Undefined;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.reflect.Array;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

/**
 * linker like NashornLinker.
 */
public class RhinoLinker implements GuardingDynamicLinker, GuardingTypeConverterFactory, ConversionComparator {
    @Override
    public GuardedInvocation getGuardedInvocation(LinkRequest linkRequest, LinkerServices linkerServices) {
        return null;
    }

    @Override
    public Comparison compareConversion(Class<?> sourceType, Class<?> targetType1, Class<?> targetType2) {
        // for array
        if (sourceType == NativeArray.class) {
            if (isArrayPreferredTarget(targetType1)) {
                if (!isArrayPreferredTarget(targetType2)) {
                    return Comparison.TYPE_1_BETTER;
                }
            } else if (isArrayPreferredTarget(targetType2)) {
                return Comparison.TYPE_2_BETTER;
            }

            if (targetType1.isArray()) {
                if (!targetType2.isArray()) {
                    return Comparison.TYPE_1_BETTER;
                }
            } else if (targetType2.isArray()) {
                return Comparison.TYPE_2_BETTER;
            }
        }

        // interface adapter
        if (isInterfaceAdapterSource(sourceType)) {
            if (targetType1.isInterface()) {
                if (!targetType2.isInterface()) {
                    return Comparison.TYPE_1_BETTER;
                }
            } else if (targetType2.isInterface()) {
                return Comparison.TYPE_2_BETTER;
            }
        }

        // 
        Class<?> wrapper1 = getWrapperTypeOrSelf(targetType1);
        if (sourceType == wrapper1) return Comparison.TYPE_1_BETTER;
        Class<?> wrapper2 = getWrapperTypeOrSelf(targetType2);
        if (sourceType == wrapper2) return Comparison.TYPE_2_BETTER;

        // source is instanceof Number
        if (Number.class.isAssignableFrom(sourceType)) {
            // Number is better.
            if (Number.class.isAssignableFrom(wrapper1)) {
                if (!Number.class.isAssignableFrom(wrapper2)) {
                    return Comparison.TYPE_1_BETTER;
                }
            } else if (Number.class.isAssignableFrom(wrapper2)) {
                return Comparison.TYPE_2_BETTER;
            }

            // or Character is better.
            if (Character.class == wrapper1) {
                return Comparison.TYPE_1_BETTER;
            }

            if (Character.class == wrapper2) {
                return Comparison.TYPE_2_BETTER;
            }
        }

        // source is String, Boolean or Number
        if (sourceType == String.class || sourceType == Boolean.class || Number.class.isAssignableFrom(sourceType)) {
            Class<?> primitiveType1 = getPrimitiveTypeOrSelf(targetType1);
            Class<?> primitiveType2 = getPrimitiveTypeOrSelf(targetType2);

            // size of primitive value is primitiveType1 < primitiveType2
            if (TypeUtilities.isMethodInvocationConvertible(primitiveType1, primitiveType2)) {
                return Comparison.TYPE_2_BETTER;
            }

            // size of primitive value is  primitiveType2 < primitiveType2
            if (TypeUtilities.isMethodInvocationConvertible(primitiveType2, primitiveType1)) {
                return Comparison.TYPE_1_BETTER;
            }

            if (targetType1 == String.class) {
                return Comparison.TYPE_1_BETTER;
            }

            if (targetType2 == String.class) {
                return Comparison.TYPE_2_BETTER;
            }
        }

        return Comparison.INDETERMINATE;
    }

    private static Class<?> getPrimitiveTypeOrSelf(Class<?> type) {
        Class<?> primitive = jdk.internal.dynalink.support.TypeUtilities.getPrimitiveType(type);
        return primitive == null ? type : primitive;
    }

    private static Class<?> getWrapperTypeOrSelf(Class<?> type) {
        Class<?> wrapper = jdk.internal.dynalink.support.TypeUtilities.getWrapperType(type);
        return wrapper == null ? type : wrapper;
    }

    private static boolean isArrayPreferredTarget(Class<?> clazz) {
        return clazz == List.class || clazz == Collection.class || clazz == Queue.class || clazz == Deque.class;
    }
    
    private static boolean isInterfaceAdapterSource(Class<?> clazz) {
        return NativeObject.class.isAssignableFrom(clazz) || NativeFunction.class.isAssignableFrom(clazz) || ArrowFunction.class.isAssignableFrom(clazz);
    }

    private static final MethodHandle IS_NATIVE_ARRAY = Guards.isInstance(NativeArray.class, MethodType.methodType(Boolean.TYPE, Object.class));
    private static final MethodHandle TO_LIST = MethodHandles.identity(NativeArray.class).asType(MethodType.methodType(List.class, NativeArray.class));
    private static final MethodHandle TO_JAVA_ARRAY = findMH(RhinoLinker.class, "toJavaArray", Object.class, Object.class, Class.class);

    private static final MethodHandle NUMBER_TO_LONG_OR_DOUBLE = findMH(RhinoLinker.class, "numberToLongOrDouble", Object.class, Number.class);
    private static final MethodHandle NUMBER_TO_DOUBLE = findMH(RhinoLinker.class, "numberToDouble", Object.class, Number.class);
    
    private static final MethodHandle CREATE_INTERFACE_ADAPTER = findMH(NativeJavaObject.class, "createInterfaceAdapter", Object.class, Class.class, ScriptableObject.class);

    private static final MethodHandle IDENTITY_CONVERSION = MethodHandles.identity(Object.class);

    private static final ClassValue<MethodHandle> ARRAY_CONVERTERS = new ClassValue<MethodHandle>() {
        @Override
        protected MethodHandle computeValue(Class<?> type) {
            MethodHandle converter = MethodHandles.insertArguments(TO_JAVA_ARRAY, 1, type.getComponentType());
            return converter.asType(converter.type().changeReturnType(type));
        }
    };

    @SuppressWarnings("unused") // used by method handle
    public static Object toJavaArray(Object obj, Class<?> componentType) {
        NativeArray array = (NativeArray)obj;
        Object javaArray = Array.newInstance(componentType, array.size());
        MethodHandle converter = Context.getLinker().getLinkerServices().getTypeConverter(Object.class, componentType);
        for (int i = 0; i < array.size(); i++) {
            Array.set(javaArray, i, invoke(converter, array.get(i)));
        }
        return javaArray;
    }

    @Override
    public GuardedInvocation convertToType(Class<?> sourceType, Class<?> targetType) {
        MethodType methodType = MethodType.methodType(targetType, sourceType);
        // first, convert primitive
        MethodHandle primitiveConvert = PrimitiveConvert.PRIMITIVE_CONVERTERS.get(targetType);
        if (primitiveConvert != null) return new GuardedInvocation(primitiveConvert.asType(methodType), null);

        // next, convert array
        if (sourceType.isAssignableFrom(NativeArray.class)) {
            MethodHandle guard = sourceType == NativeArray.class ? null : IS_NATIVE_ARRAY;

            if (targetType.isArray()) {
                return new GuardedInvocation(ARRAY_CONVERTERS.get(targetType).asType(methodType), guard);
            }

            if (targetType == List.class) {
                return new GuardedInvocation(TO_LIST.asType(methodType), guard);
            }
        }

        // for void, return undefiend
        if (targetType == Object.class && sourceType == Void.TYPE)
            return new GuardedInvocation(MethodHandles.constant(Object.class, Undefined.instance).asType(methodType), null);

        // if target is object and source is Number
        if (targetType == Object.class && Number.class.isAssignableFrom(sourceType)) {
            Context ctx = Context.getCurrentContext();
            if (ctx != null && ctx.hasFeature(Context.FEATURE_INTEGER_WITHOUT_DECIMAL_PLACE)) {
                return new GuardedInvocation(NUMBER_TO_LONG_OR_DOUBLE.asType(methodType), null);
            } else {
                return new GuardedInvocation(NUMBER_TO_DOUBLE.asType(methodType), null);
            }
        }

        if (targetType.isAssignableFrom(sourceType)) {
            return new GuardedInvocation(IDENTITY_CONVERSION.asType(methodType), null);
        }

        if (targetType.isInterface() && isInterfaceAdapterSource(sourceType)) {
            return new GuardedInvocation(CREATE_INTERFACE_ADAPTER.bindTo(targetType).asType(methodType), null);
        }

        return null;
    }

    @SuppressWarnings("unused")
    public static Object numberToLongOrDouble(Number arg) {
        double doubleValue = PrimitiveConvert.numberToDouble(arg);
        if (Math.round(doubleValue) == doubleValue) {
            return PrimitiveConvert.numberToLong(arg);
        }
        return doubleValue;
    }

    @SuppressWarnings("unused")
    public static Object numberToDouble(Number arg) {
        return PrimitiveConvert.numberToDouble(arg);
    }

    // utilities

    public static Object invoke(MethodHandle mh, Object arg) {
        try {
            return mh.invoke(arg);
        } catch (Error | RuntimeException var3) {
            throw var3;
        } catch (Throwable var4) {
            throw sneakyThrow(var4);
        }
    }

    private static <Throws extends Throwable> RuntimeException sneakyThrow(Throwable throwable) throws Throws {
        //noinspection unchecked
        throw (Throws) throwable;
    }

    private static MethodHandle findMH(Class<?> owner, String name, Class<?> rtype, Class<?>... types) {
        try {
            return MethodHandles.lookup().findStatic(owner, name, MethodType.methodType(rtype, types));
        } catch (NoSuchMethodException | IllegalAccessException e) {
            throw new AssertionError(e);
        }
    }

    static class PrimitiveConvert {
        private static MethodHandle findMH(Class<?> owner, String name, Class<?> rtype, Class<?>... types) {
            try {
                return MethodHandles.lookup().findStatic(owner, name, MethodType.methodType(rtype, types));
            } catch (NoSuchMethodException | IllegalAccessException e) {
                throw new AssertionError(e);
            }
        }

        // Number to Wrapper utilities

        @SuppressWarnings("unused") // used by numberToWrappedPrimitive
        private static Double numberToDouble(Number value) {
            return value == null ? null : value.doubleValue();
        }

        @SuppressWarnings("unused") // used by numberToWrappedPrimitive
        static Float numberToFloat(Number value) {
            return value == null ? null : value.floatValue();
        }

        @SuppressWarnings("unused") // used by numberToWrappedPrimitive
        static Byte numberToByte(Number value) {
            return value == null ? null : value.byteValue();
        }

        @SuppressWarnings("unused") // used by numberToWrappedPrimitive
        static Short numberToShort(Number value) {
            return value == null ? null : value.shortValue();
        }

        @SuppressWarnings("unused") // used by numberToWrappedPrimitive
        static Integer numberToInteger(Number value) {
            return value == null ? null : value.intValue();
        }

        @SuppressWarnings("unused") // used by numberToWrappedPrimitive
        static Long numberToLong(Number value) {
            return value == null ? null : value.longValue();
        }

        @SuppressWarnings("unused") // used by method handle
        static String toString(Object value) {
            return value == null ? null : ScriptRuntime.toString(value);
        }

        @SuppressWarnings("unused") // used by method handle
        private static Character toChar(Object o) {
            if (o == null) {
                return null;
            } else if (o instanceof Number) {
                int ival = ((Number)o).intValue();
                if (ival >= 0 && ival <= 65535) {
                    return (char)ival;
                } else {
                    throw ECMAErrors.typeError("cant.convert.number.to.char", new String[0]);
                }
            } else {
                String s = toString(o);
                if (s == null) {
                    return null;
                } else if (s.length() != 1) {
                    throw ECMAErrors.typeError("cant.convert.string.to.char", new String[0]);
                } else {
                    return s.charAt(0);
                }
            }
        }

        @SuppressWarnings("unused") // used by method handle
        static char toCharPrimitive(Object obj0) {
            Character c = toChar(obj0);
            return c == null ? '\u0000' : c;
        }

        private static MethodHandle numberToWrappedPrimitive(MethodHandle toNumber, Class<?> wrapper) {
            MethodHandle convert = findMH(PrimitiveConvert.class, "numberTo" + wrapper.getSimpleName(), wrapper, Number.class);
            return MethodHandles.filterReturnValue(toNumber, convert);
        }

        private final static MethodHandle TO_NUMBER_OBJECT = findMH(ScriptRuntime.class, "toNumberObject", Number.class, Object.class);
        private final static MethodHandle TO_NUMBER = findMH(ScriptRuntime.class, "toNumber", double.class, Object.class);

        /**
         * convert from object to primitive type and primitive-like types.
         * list of primitive-like types shown below:
         * <ul>
         *     <li>{@link String}</li>
         *     <li>{@link Number}</li>
         *     <li>wrapper types of the primitive values</li>
         * </ul>
         */
        // 8: count of primitives, 2: string and number.
        private static final Map<Class<?>, MethodHandle> PRIMITIVE_CONVERTERS = new HashMap<>(8 * 2 + 2, 1f);

        private static void putNumberPrimitiveConverter(Class<?> primitive) {
            Class<?> wrapper = TypeUtilities.getWrapperType(primitive);
            MethodHandle handle = TO_NUMBER;
            handle = MethodHandles.explicitCastArguments(handle, TO_NUMBER.type().changeReturnType(primitive));
            PRIMITIVE_CONVERTERS.put(primitive, handle);
            PRIMITIVE_CONVERTERS.put(wrapper, numberToWrappedPrimitive(TO_NUMBER_OBJECT, wrapper));
        }

        static {
            // for boolean types
            PRIMITIVE_CONVERTERS.put(Boolean.class, findMH(ScriptRuntime.class, "toBooleanObject", Boolean.class, Object.class));
            PRIMITIVE_CONVERTERS.put(boolean.class, findMH(ScriptRuntime.class, "toBoolean", boolean.class, Object.class));

            // for Number and String
            PRIMITIVE_CONVERTERS.put(Number.class, TO_NUMBER_OBJECT);
            PRIMITIVE_CONVERTERS.put(String.class, findMH(PrimitiveConvert.class, "toString", String.class, Object.class));

            // for Number and String
            PRIMITIVE_CONVERTERS.put(char.class, findMH(PrimitiveConvert.class, "toCharPrimitive", char.class, Object.class));
            PRIMITIVE_CONVERTERS.put(Character.class, findMH(PrimitiveConvert.class, "toChar", Character.class, Object.class));

            // numeric primitives
            putNumberPrimitiveConverter(byte.class);
            putNumberPrimitiveConverter(short.class);
            putNumberPrimitiveConverter(int.class);
            putNumberPrimitiveConverter(long.class);
            putNumberPrimitiveConverter(float.class);
            putNumberPrimitiveConverter(double.class);
        }
    }
}
