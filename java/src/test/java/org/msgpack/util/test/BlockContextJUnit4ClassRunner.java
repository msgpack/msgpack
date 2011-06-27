package org.msgpack.util.test;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Ignore;
import org.junit.internal.AssumptionViolatedException;
import org.junit.internal.runners.model.EachTestNotifier;
import org.junit.internal.runners.model.ReflectiveCallable;
import org.junit.internal.runners.statements.Fail;
import org.junit.internal.runners.statements.RunAfters;
import org.junit.internal.runners.statements.RunBefores;
import org.junit.runner.notification.RunNotifier;
import org.junit.runner.notification.StoppedByUserException;
import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.Statement;
import org.junit.runners.model.TestClass;

@Ignore
public final class BlockContextJUnit4ClassRunner extends BlockJUnit4ClassRunner {

	private TestClass tClass = null;

	public BlockContextJUnit4ClassRunner(Class<?> c) throws InitializationError {
		this(c, null);
	}

	public BlockContextJUnit4ClassRunner(Class<?> c, TestClass tClass) throws InitializationError {
		super(c);
		this.tClass = tClass;
	}

	@Override
	protected void collectInitializationErrors(List<Throwable> errors) {
		super.collectInitializationErrors(errors);
	}

	@Override
	public void run(final RunNotifier notifier) {
		EachTestNotifier testNotifier = new EachTestNotifier(notifier, getDescription());
		try {
			Statement statement = classBlock(notifier);
			statement.evaluate();
		} catch (AssumptionViolatedException e) {
			testNotifier.fireTestIgnored();
		} catch (StoppedByUserException e) {
			throw e;
		} catch (Throwable e) {
			testNotifier.addFailure(e);
		}
	}

	@Override
	protected Statement classBlock(final RunNotifier notifier) {
		return super.classBlock(notifier);
	}

	@Override
	protected Statement withBeforeClasses(Statement statement) {
		Statement befores = super.withBeforeClasses(statement);
		if (tClass == null) {
			return befores;
		} else {
			List<FrameworkMethod> nestedBefores= tClass.getAnnotatedMethods(BeforeClass.class);
			return nestedBefores.isEmpty() ? befores : new RunBefores(befores, nestedBefores, null);
		}
	}

	@Override
	protected Statement withAfterClasses(Statement statement) {
		Statement afters = super.withAfterClasses(statement);
		if (tClass == null) {
			return afters;
		} else {
			List<FrameworkMethod> nestedAfters= tClass.getAnnotatedMethods(AfterClass.class);
			return nestedAfters.isEmpty() ? afters : new RunAfters(afters, nestedAfters, null); 

		}
	}

	@Override
	protected void runChild(FrameworkMethod method, RunNotifier notifier) {
		super.runChild(method, notifier);
	}

	@Override
	protected Object createTest() throws Exception {
		return getTestClass().getOnlyConstructor().newInstance();
	}

	protected Object createNestedTest() {
		try {
			return tClass.getOnlyConstructor().newInstance();
		} catch (Throwable t) {
			return new Fail(t);
		}
	}

	@Override
	protected Statement methodBlock(FrameworkMethod method) {
		Object test;
		try {
			test = new ReflectiveCallable() {
				@Override
				protected Object runReflectiveCall() throws Throwable {
					return createTest();
				}
			}.run();
		} catch (Throwable e) {
			return new Fail(e);
		}

		Statement statement = methodInvoker(method, test);
		statement = possiblyExpectingExceptions(method, test, statement);
		statement = withPotentialTimeout(method, test, statement);
		statement = withBeforeMethods(method, test, statement);
		statement = withBefores(method, test, statement);
		statement = withAfterMethods(method, test, statement);
		statement = withAfters(method, test, statement);
		statement = withRules0(method, test, statement);
		return statement;
	}

	@Override
	protected Statement methodInvoker(FrameworkMethod method, Object test) {
		return super.methodInvoker(method, test);
	}

	@Override @Deprecated
	protected Statement possiblyExpectingExceptions(FrameworkMethod method,
			Object test, Statement next) {
		return super.possiblyExpectingExceptions(method, test, next);
	}

	@Override @Deprecated
	protected Statement withPotentialTimeout(FrameworkMethod method,
			Object test, Statement next) {
		return super.withPotentialTimeout(method, test, next);
	}

	protected Statement withBeforeMethods(FrameworkMethod method, Object target, Statement statement) {
		Statement beforeMethods = withBeforeMethods0(getTestClass(), method, target, statement);
		if (tClass == null) {
			return beforeMethods;
		} else {
			return withBeforeMethods0(tClass, method, target, beforeMethods);
		}
	}

	private Statement withBeforeMethods0(TestClass tc, FrameworkMethod method, Object target, Statement statement) {
		List<FrameworkMethod> fms = new ArrayList<FrameworkMethod>();
		for (FrameworkMethod fm : tc.getAnnotatedMethods(BeforeMethod.class)) {
			String targetMethodName = ((BeforeMethod) fm.getAnnotation(BeforeMethod.class)).value();
			if (method.getName().equals(targetMethodName)) {
				fms.add(0, fm);
			}
		}
		return fms.isEmpty() ? statement : new RunBefores(statement, fms, target);
	}

	@Override @Deprecated
	protected Statement withBefores(FrameworkMethod method, Object target, Statement statement) {
		Statement befores = super.withBefores(method, target, statement);
		if (tClass == null) {
			return befores;
		} else {
			List<FrameworkMethod> nestedBefores= tClass.getAnnotatedMethods(Before.class);
			return nestedBefores.isEmpty() ? befores : new RunBefores(befores, nestedBefores, target); 
				
		}
	}

	protected Statement withAfterMethods(FrameworkMethod method, Object target, Statement statement) {
		Statement afterMethods = withAfterMethods0(getTestClass(), method, target, statement);
		if (tClass == null) {
			return afterMethods;
		} else {
			return withAfterMethods0(tClass, method, target, afterMethods);
		}
	}

	private Statement withAfterMethods0(TestClass tc, FrameworkMethod method, Object target, Statement statement) {
		List<FrameworkMethod> fms = new ArrayList<FrameworkMethod>();
		for (FrameworkMethod fm : tc.getAnnotatedMethods(AfterMethod.class)) {
			String targetMethodName = ((AfterMethod) fm.getAnnotation(AfterMethod.class)).value();
			if (method.getName().equals(targetMethodName)) {
				fms.add(fm);
			}
		}
		return fms.isEmpty() ? statement : new RunAfters(statement, fms, target);
	}

	@Override @Deprecated
	protected Statement withAfters(FrameworkMethod method, Object target, Statement statement) {
		Statement afters = super.withAfters(method, target, statement);
		if (tClass == null) {
			return afters;
		} else {
			List<FrameworkMethod> nestedAfters= tClass.getAnnotatedMethods(After.class);
			return nestedAfters.isEmpty() ? afters : new RunAfters(afters, nestedAfters, target);
		}
	}

	private Statement withRules0(FrameworkMethod method, Object test, Statement statement) {
		Statement ret = null;
		try {
			Method m = BlockJUnit4ClassRunner.class.getDeclaredMethod(
					"withRules", new Class[] { FrameworkMethod.class,
							Object.class, Statement.class });
			m.setAccessible(true);
			ret = (Statement) m.invoke(this, new Object[] { method, test, statement });
			m.setAccessible(false);
		} catch (SecurityException e) {
			e.printStackTrace();
		} catch (NoSuchMethodException e) {
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			e.printStackTrace();
		} catch (InvocationTargetException e) {
			e.printStackTrace();
		}
		return ret;
	}
}
