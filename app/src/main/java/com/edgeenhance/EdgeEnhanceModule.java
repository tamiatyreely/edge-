package com.edgeenhance;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.content.Context;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.DialogInterface;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.view.KeyEvent;
import android.view.View;
import android.view.ViewGroup;
import android.widget.PopupWindow;
import android.widget.EditText;
import android.view.Window;
import android.widget.TextView;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.HashSet;
import java.util.Locale;
import java.util.Set;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.WeakHashMap;

import de.robv.android.xposed.IXposedHookLoadPackage;
import de.robv.android.xposed.XC_MethodHook;
import de.robv.android.xposed.XposedBridge;
import de.robv.android.xposed.XposedHelpers;
import de.robv.android.xposed.callbacks.XC_LoadPackage;

/**
 * EdgeEnhance experimental adapter for Microsoft Edge Android 152.x.
 * The app is not modified; hooks are applied in the Edge process only.
 */
public final class EdgeEnhanceModule implements IXposedHookLoadPackage {
    private static final String TAG = "[EdgeEnhance] ";
    private static final String TARGET = "com.microsoft.emmx";
    private static final Set<Activity> EXIT_DIALOGS = Collections.newSetFromMap(new WeakHashMap<>());
    private static final Set<String> HOOKED_CLASSES = Collections.synchronizedSet(new HashSet<>());
    private static final Handler MAIN = new Handler(Looper.getMainLooper());
    // Rolling diagnostic buffer. Clipboard updates are debounced and only attempted
    // while Edge is foreground, so rapid View hooks do not continuously fight the user.
    private static final Deque<String> LOG_BUFFER = new ArrayDeque<>();
    private static final int MAX_LOG_LINES = 240;
    private static volatile Activity foregroundActivity;
    private static long lastClipboardCopyAt;
    private static final Runnable CLIPBOARD_COPY_TASK = EdgeEnhanceModule::copyDiagnosticsToClipboard;

    @Override
    public void handleLoadPackage(XC_LoadPackage.LoadPackageParam lpparam) {
        if (!TARGET.equals(lpparam.packageName)) return;
        log("Loaded in Edge process: " + lpparam.processName);
        hookActivityLifecycle();
        hookActivityBackDispatch();
        hookDialogs(lpparam.classLoader);
        hookPopupWindows();
        hookViewLongPress(lpparam.classLoader);
        inspectImportantClasses(lpparam.classLoader);
    }

    private static void hookActivityLifecycle() {
        try {
            XposedBridge.hookAllMethods(Activity.class, "onResume", new XC_MethodHook() {
                @Override protected void afterHookedMethod(MethodHookParam param) {
                    Activity a = (Activity) param.thisObject;
                    if (isEdgeBrowserActivity(a)) {
                        foregroundActivity = a;
                        log("Edge activity resumed: " + a.getClass().getName());
                        scheduleClipboardCopy();
                    }
                }
            });
            XposedBridge.hookAllMethods(Activity.class, "onPause", new XC_MethodHook() {
                @Override protected void beforeHookedMethod(MethodHookParam param) {
                    Activity a = (Activity) param.thisObject;
                    if (foregroundActivity == a) foregroundActivity = null;
                }
            });
            log("Hooked Activity lifecycle for foreground diagnostics");
        } catch (Throwable t) { log("Activity lifecycle hook failed: " + t); }
    }

    private static void hookActivityBackDispatch() {
        try {
            XposedBridge.hookAllMethods(Activity.class, "dispatchKeyEvent", new XC_MethodHook() {
                @Override protected void beforeHookedMethod(MethodHookParam param) {
                    if (!(param.thisObject instanceof Activity)) return;
                    Activity activity = (Activity) param.thisObject;
                    if (!isEdgeBrowserActivity(activity)) return;
                    KeyEvent event = (KeyEvent) param.args[0];
                    if (event == null || event.getKeyCode() != KeyEvent.KEYCODE_BACK
                            || event.getAction() != KeyEvent.ACTION_UP || event.isCanceled()) return;
                    try {
                        BackResult result = handleSmartBack(activity);
                        if (result.consumed) {
                            param.setResult(true);
                        }
                    } catch (Throwable t) {
                        log("Back hook error: " + t);
                    }
                }
            });
            log("Hooked Activity.dispatchKeyEvent for smart back handling");
        } catch (Throwable t) {
            log("Cannot hook dispatchKeyEvent: " + t);
        }
    }

    private static boolean isEdgeBrowserActivity(Activity a) {
        String n = a.getClass().getName();
        return n.contains("ChromeTabbedActivity") || n.contains("TabbedActivity");
    }

    private static final class BackResult {
        final boolean consumed;
        BackResult(boolean c) { consumed = c; }
    }

    private static BackResult handleSmartBack(Activity activity) throws Exception {
        Object tab = findCurrentTab(activity);
        if (tab == null) {
            log("SmartBack: current Tab not resolved; allow Edge default handling");
            return new BackResult(false);
        }
        Object webContents = callNoArg(tab, "getWebContents");
        Boolean canBack = readCanGoBack(webContents);
        if (canBack == null) {
            log("SmartBack: WebContents history state unresolved; allow Edge default handling");
            return new BackResult(false);
        }
        if (canBack) {
            log("SmartBack: web history exists; allow native back");
            return new BackResult(false);
        }
        Object selector = findTabModelSelector(activity);
        Object model = selector == null ? null : callNoArg(selector, "getCurrentModel");
        Integer count = model == null ? null : readIntNoArg(model, "getCount");
        if (count == null) {
            log("SmartBack: TabModel count unresolved; allow Edge default handling");
            return new BackResult(false);
        }
        if (count > 1) {
            boolean closed = closeTab(model, tab);
            log("SmartBack: close current tab result=" + closed + ", remaining-before=" + count);
            return new BackResult(closed);
        }
        showExitConfirmation(activity);
        log("SmartBack: last tab; showing exit confirmation");
        return new BackResult(true);
    }

    private static Object findCurrentTab(Activity activity) {
        String[] getters = {"getActivityTab", "getCurrentTab", "getActiveTab", "getTab"};
        for (String getter : getters) {
            Object value = callNoArg(activity, getter);
            if (looksLikeTab(value)) return value;
        }
        Object selector = findTabModelSelector(activity);
        Object model = selector == null ? null : callNoArg(selector, "getCurrentModel");
        if (model != null) {
            Integer index = readIntNoArg(model, "index");
            if (index == null) index = readIntNoArg(model, "getSelectedIndex");
            if (index != null && index >= 0) {
                Object tab = callOneArg(model, "getTabAt", index);
                if (looksLikeTab(tab)) return tab;
            }
        }
        return null;
    }

    private static boolean looksLikeTab(Object value) {
        if (value == null) return false;
        String n = value.getClass().getName();
        return n.endsWith(".Tab") || n.contains("chrome.browser.tab") || hasMethod(value.getClass(), "getWebContents");
    }

    private static Object findTabModelSelector(Activity activity) {
        Object v = callNoArg(activity, "getTabModelSelector");
        if (v != null) return v;
        for (Class<?> c = activity.getClass(); c != null; c = c.getSuperclass()) {
            for (Field f : c.getDeclaredFields()) {
                if (f.getType().getName().contains("TabModelSelector")) {
                    try { f.setAccessible(true); v = f.get(activity); if (v != null) return v; }
                    catch (Throwable ignored) { }
                }
            }
        }
        return null;
    }

    private static Boolean readCanGoBack(Object webContents) {
        if (webContents == null) return null;
        Object b = callNoArg(webContents, "canGoBack");
        if (b instanceof Boolean) return (Boolean) b;
        Object nav = callNoArg(webContents, "getNavigationController");
        b = callNoArg(nav, "canGoBack");
        return b instanceof Boolean ? (Boolean) b : null;
    }

    private static boolean closeTab(Object model, Object tab) {
        if (model == null || tab == null) return false;
        for (Method m : model.getClass().getMethods()) {
            if (!m.getName().equals("closeTab")) continue;
            Class<?>[] p = m.getParameterTypes();
            if (p.length == 0 || !p[0].isAssignableFrom(tab.getClass())) continue;
            try {
                m.setAccessible(true);
                Object[] args = new Object[p.length];
                args[0] = tab;
                for (int i = 1; i < p.length; i++) args[i] = defaultValue(p[i]);
                m.invoke(model, args);
                return true;
            } catch (Throwable t) { log("closeTab overload failed " + m + ": " + t); }
        }
        // Some Chromium builds expose closeTab(Tab, boolean, boolean) on a bridge/supertype.
        for (Class<?> c = model.getClass(); c != null; c = c.getSuperclass()) {
            for (Method m : c.getDeclaredMethods()) {
                if (!m.getName().equals("closeTab")) continue;
                Class<?>[] p = m.getParameterTypes();
                if (p.length == 0 || !p[0].isAssignableFrom(tab.getClass())) continue;
                try {
                    m.setAccessible(true);
                    Object[] args = new Object[p.length]; args[0] = tab;
                    for (int i = 1; i < p.length; i++) args[i] = defaultValue(p[i]);
                    m.invoke(model, args); return true;
                } catch (Throwable t) { log("declared closeTab failed: " + t); }
            }
        }
        return false;
    }

    private static Object defaultValue(Class<?> t) {
        if (!t.isPrimitive()) return null;
        if (t == boolean.class) return false;
        if (t == char.class) return '\0';
        if (t == byte.class) return (byte) 0;
        if (t == short.class) return (short) 0;
        if (t == int.class) return 0;
        if (t == long.class) return 0L;
        if (t == float.class) return 0f;
        if (t == double.class) return 0d;
        return null;
    }

    private static void showExitConfirmation(final Activity activity) {
        if (activity.isFinishing() || activity.isDestroyed()) return;
        synchronized (EXIT_DIALOGS) { if (EXIT_DIALOGS.contains(activity)) return; EXIT_DIALOGS.add(activity); }
        MAIN.post(() -> {
            try {
                new AlertDialog.Builder(activity)
                        .setTitle("退出 Microsoft Edge？")
                        .setMessage("当前只剩最后一个标签页，是否退出浏览器？")
                        .setNegativeButton("取消", (d, w) -> { })
                        .setPositiveButton("退出", (d, w) -> {
                            try { activity.finishAndRemoveTask(); }
                            catch (Throwable ignored) { activity.finish(); }
                        })
                        .setOnDismissListener(d -> { synchronized (EXIT_DIALOGS) { EXIT_DIALOGS.remove(activity); } })
                        .show();
            } catch (Throwable t) {
                synchronized (EXIT_DIALOGS) { EXIT_DIALOGS.remove(activity); }
                log("Cannot show exit dialog: " + t);
            }
        });
    }

    private static void hookDialogs(ClassLoader cl) {
        try {
            XposedBridge.hookAllMethods(Dialog.class, "show", new XC_MethodHook() {
                @Override protected void afterHookedMethod(MethodHookParam param) {
                    Dialog dialog = (Dialog) param.thisObject;
                    MAIN.post(() -> inspectAndDismissPromoDialog(dialog));
                }
            });
            log("Hooked Dialog.show for conservative promo filtering");
        } catch (Throwable t) { log("Dialog hook failed: " + t); }

        // Observe Edge/Chromium promotion-specific layouts without blanket-blocking educational tips.
        hookAttachForPromoViews(cl);
    }

    private static void inspectAndDismissPromoDialog(Dialog dialog) {
        try {
            if (dialog == null || !dialog.isShowing()) return;
            Window w = dialog.getWindow();
            if (w == null) return;
            Activity owner = findActivity(w.getDecorView().getContext());
            if (owner == null || !isEdgeBrowserActivity(owner)) return;
            String rawText = collectText(w.getDecorView());
            String text = rawText.toLowerCase(Locale.ROOT);
            if (text.isEmpty()) {
                log("Popup monitor: unknown dialog class=" + dialog.getClass().getName() + " (no visible text)");
                return;
            }
            if (containsAny(text, "新功能", "功能介绍", "使用技巧", "了解新功能", "功能导览", "what's new", "new feature", "feature tour", "learn about")) {
                log("Promo filter: kept educational/feature dialog");
                return;
            }
            if (isMarketingText(text)) {
                log("Promo filter: dismissed marketing dialog; sample=" + abbreviate(rawText, 180));
                dialog.dismiss();
            } else {
                log("Popup monitor: unknown/unclassified dialog class=" + dialog.getClass().getName()
                        + "; sample=" + abbreviate(rawText, 180) + "; kept (not auto-blocked)");
            }
        } catch (Throwable t) { log("Dialog inspect failed: " + t); }
    }

    private static boolean isMarketingText(String text) {
        return containsAny(text,
                "设为默认浏览器", "设置为默认浏览器", "默认浏览器", "邀请好友", "邀请朋友",
                "邀请有礼", "邀请好友领", "领取积分", "赚取积分", "积分奖励", "领积分",
                "活动奖励", "限时活动", "立即邀请", "赢取奖励", "兑换奖励", "专属优惠",
                "邀请您", "好友邀请", "推荐好友", "推广活动", "活动中心",
                "set as default browser", "make edge your default", "invite friends", "refer a friend",
                "earn points", "claim your reward", "rewards campaign", "limited-time offer", "special offer");
    }

    private static boolean containsAny(String s, String... keys) {
        for (String k : keys) if (s.contains(k.toLowerCase(Locale.ROOT))) return true;
        return false;
    }

    private static String collectText(View root) {
        StringBuilder b = new StringBuilder();
        collectTextRecursive(root, b, 0);
        return b.toString();
    }

    private static void collectTextRecursive(View v, StringBuilder b, int depth) {
        if (v == null || depth > 20) return;
        // EditText is a TextView subclass; never copy user-entered form contents.
        if (v instanceof TextView && !(v instanceof EditText)) {
            CharSequence s = ((TextView) v).getText();
            if (s != null) b.append(' ').append(s);
        }
        CharSequence d = v.getContentDescription();
        if (d != null) b.append(' ').append(d);
        if (v instanceof ViewGroup) {
            ViewGroup g = (ViewGroup) v;
            for (int i = 0; i < g.getChildCount(); i++) collectTextRecursive(g.getChildAt(i), b, depth + 1);
        }
    }

    private static void hookPopupWindows() {
        try {
            for (String method : new String[]{"show", "showAtLocation", "showAsDropDown"}) {
                XposedBridge.hookAllMethods(PopupWindow.class, method, new XC_MethodHook() {
                    @Override protected void afterHookedMethod(MethodHookParam param) {
                        PopupWindow popup = (PopupWindow) param.thisObject;
                        MAIN.post(() -> inspectPopupWindow(popup));
                    }
                });
            }
            log("Hooked PopupWindow show methods for dynamic promo monitoring");
        } catch (Throwable t) { log("PopupWindow hook failed: " + t); }
    }

    private static void inspectPopupWindow(PopupWindow popup) {
        try {
            if (popup == null || !popup.isShowing()) return;
            View content = popup.getContentView();
            if (content == null) return;
            Activity owner = findActivity(content.getContext());
            if (owner == null || !isEdgeBrowserActivity(owner)) return;
            String raw = collectText(content);
            if (raw.trim().isEmpty()) {
                log("Popup monitor: PopupWindow class=" + content.getClass().getName() + " (no visible text)");
                return;
            }
            String lower = raw.toLowerCase(Locale.ROOT);
            if (containsAny(lower, "新功能", "功能介绍", "使用技巧", "了解新功能", "功能导览", "what's new", "new feature", "feature tour", "learn about")) {
                log("Popup monitor: kept feature guide PopupWindow; sample=" + abbreviate(raw, 160));
                return;
            }
            if (isMarketingText(lower)) {
                log("Promo filter: dismissing marketing PopupWindow; sample=" + abbreviate(raw, 180));
                popup.dismiss();
            } else {
                log("Popup monitor: unknown/unclassified PopupWindow class=" + content.getClass().getName()
                        + "; sample=" + abbreviate(raw, 160) + "; kept");
            }
        } catch (Throwable t) { log("PopupWindow inspect failed: " + t); }
    }

    private static void hookAttachForPromoViews(ClassLoader cl) {
        try {
            XposedBridge.hookAllMethods(View.class, "onAttachedToWindow", new XC_MethodHook() {
                @Override protected void afterHookedMethod(MethodHookParam param) {
                    View v = (View) param.thisObject;
                    Activity owner = findActivity(v.getContext());
                    if (owner != null && isEdgeBrowserActivity(owner) && isMoreToolbarButton(v)) {
                        // Make the toolbar target eligible for the platform long-press gesture.
                        v.setLongClickable(true);
                    }
                    String cn = v.getClass().getName().toLowerCase(Locale.ROOT);
                    if (!(cn.contains("promo") || cn.contains("campaign") || cn.contains("referral") || cn.contains("defaultbrowser"))) return;
                    MAIN.post(() -> {
                        try {
                            if (!v.isAttachedToWindow()) return;
                            String txt = collectText(v).toLowerCase(Locale.ROOT);
                            if (containsAny(txt, "新功能", "功能介绍", "使用技巧", "what's new", "new feature", "feature tour")) return;
                            if (isMarketingText(txt) && v.getParent() instanceof ViewGroup) {
                                ((ViewGroup) v.getParent()).removeView(v);
                                log("Removed promo-specific view " + cn);
                            }
                        } catch (Throwable t) { log("Promo view inspect failed: " + t); }
                    });
                }
            });
            log("Hooked promo-specific view attach observer");
        } catch (Throwable t) { log("Promo view hook failed: " + t); }
    }

    private static void hookViewLongPress(ClassLoader cl) {
        try {
            XposedBridge.hookAllMethods(View.class, "performLongClick", new XC_MethodHook() {
                @Override protected void beforeHookedMethod(MethodHookParam param) {
                    View v = (View) param.thisObject;
                    Activity a = findActivity(v.getContext());
                    if (a == null || !isEdgeBrowserActivity(a) || !isMoreToolbarButton(v)) return;
                    boolean opened = openQuickExtensionsPanel(a, v, cl);
                    if (opened) {
                        param.setResult(true);
                        log("Long-press More: opened native extensions quick panel");
                    }
                }
            });
            log("Hooked View.performLongClick for More button");
        } catch (Throwable t) { log("Long-press hook failed: " + t); }
    }

    private static boolean isMoreToolbarButton(View v) {
        String id = "";
        try { if (v.getId() != View.NO_ID) id = v.getResources().getResourceEntryName(v.getId()); }
        catch (Throwable ignored) { }
        String desc = v.getContentDescription() == null ? "" : v.getContentDescription().toString();
        String all = (id + " " + desc).toLowerCase(Locale.ROOT);
        boolean match = containsAny(all, "more_button", "menu_button", "overflow_menu", "toolbar_menu", "more options", "更多", "更多选项");
        if (match) log("More candidate view: id=" + id + ", desc=" + desc + ", class=" + v.getClass().getName());
        return match;
    }

    private static boolean openQuickExtensionsPanel(Activity activity, View anchor, ClassLoader cl) {
        String[] classNames = {
                "com.microsoft.edge.extensions.ExtensionDialogManager",
                "org.chromium.chrome.browser.ui.extensions.ExtensionsMenuBridge",
                "org.chromium.chrome.browser.ui.extensions.ExtensionsMenuCoordinator",
                "org.chromium.chrome.browser.extensions.ExtensionsMenuCoordinator"
        };
        String[] preferredNames = {"showExtensionsMenu", "showExtensions", "showExtensionMenu", "showMenu", "showDialog"};
        for (String name : classNames) {
            try {
                Class<?> c = Class.forName(name, false, cl);
                log("Extension panel class found: " + name);
                Object instance = obtainSingletonOrInstance(c, activity);
                for (String methodName : preferredNames) {
                    for (Method m : c.getDeclaredMethods()) {
                        if (!m.getName().equalsIgnoreCase(methodName)) continue;
                        try {
                            Object receiver = Modifier.isStatic(m.getModifiers()) ? null : instance;
                            if (receiver == null && !Modifier.isStatic(m.getModifiers())) continue;
                            Object[] args = buildArgs(m.getParameterTypes(), activity, anchor);
                            if (args == null) continue;
                            m.setAccessible(true);
                            m.invoke(receiver, args);
                            log("Invoked extension panel candidate: " + m);
                            return true;
                        } catch (Throwable t) { log("Extension candidate failed " + m + ": " + t); }
                    }
                }
                dumpCandidateMethods(c);
            } catch (ClassNotFoundException ignored) {
            } catch (Throwable t) { log("Extension class inspect failed " + name + ": " + t); }
        }
        log("Native quick extension panel entry not resolved; long-press left unconsumed");
        return false;
    }

    private static Object obtainSingletonOrInstance(Class<?> c, Activity a) {
        for (Method m : c.getDeclaredMethods()) {
            if (!Modifier.isStatic(m.getModifiers()) || m.getParameterTypes().length != 0 || !c.isAssignableFrom(m.getReturnType())) continue;
            try { m.setAccessible(true); Object o = m.invoke(null); if (o != null) return o; } catch (Throwable ignored) { }
        }
        for (Constructor<?> k : c.getDeclaredConstructors()) {
            Class<?>[] p = k.getParameterTypes();
            if (p.length == 1 && Context.class.isAssignableFrom(p[0]) && p[0].isAssignableFrom(a.getClass())) {
                try { k.setAccessible(true); return k.newInstance(a); } catch (Throwable ignored) { }
            }
            if (p.length == 1 && Context.class.isAssignableFrom(p[0])) {
                try { k.setAccessible(true); return k.newInstance(a); } catch (Throwable ignored) { }
            }
            if (p.length == 0) {
                try { k.setAccessible(true); return k.newInstance(); } catch (Throwable ignored) { }
            }
        }
        return null;
    }

    private static Object[] buildArgs(Class<?>[] types, Activity a, View v) {
        Object[] args = new Object[types.length];
        for (int i = 0; i < types.length; i++) {
            Class<?> t = types[i];
            if (Context.class.isAssignableFrom(t) && t.isAssignableFrom(a.getClass())) args[i] = a;
            else if (View.class.isAssignableFrom(t) && t.isAssignableFrom(v.getClass())) args[i] = v;
            else if (t == boolean.class || t == Boolean.class) args[i] = false;
            else if (t.isPrimitive()) args[i] = defaultValue(t);
            else return null;
        }
        return args;
    }

    private static Activity findActivity(Context c) {
        while (c instanceof android.content.ContextWrapper) {
            if (c instanceof Activity) return (Activity) c;
            c = ((android.content.ContextWrapper) c).getBaseContext();
        }
        return c instanceof Activity ? (Activity) c : null;
    }

    private static void inspectImportantClasses(ClassLoader cl) {
        String[] names = {
                "org.chromium.chrome.browser.ChromeTabbedActivity",
                "org.chromium.chrome.browser.tabmodel.TabModel",
                "org.chromium.chrome.browser.ui.extensions.ExtensionsMenuBridge",
                "com.microsoft.edge.extensions.ExtensionDialogManager",
                "org.chromium.components.browser_ui.widget.PromoDialogLayout"
        };
        for (String n : names) {
            try {
                Class<?> c = Class.forName(n, false, cl);
                log("Class present: " + n);
                dumpCandidateMethods(c);
            } catch (Throwable t) { log("Class not loaded/resolved: " + n + " (" + t.getClass().getSimpleName() + ")"); }
        }
    }

    private static void dumpCandidateMethods(Class<?> c) {
        if (c == null || !HOOKED_CLASSES.add(c.getName())) return;
        int shown = 0;
        for (Method m : c.getDeclaredMethods()) {
            String n = m.getName().toLowerCase(Locale.ROOT);
            if (containsAny(n, "back", "tab", "close", "extension", "menu", "show", "promo", "dialog", "dismiss")) {
                log("METHOD " + c.getName() + "#" + m.getName() + signature(m.getParameterTypes()) + " -> " + m.getReturnType().getName());
                if (++shown >= 80) break;
            }
        }
    }

    private static String signature(Class<?>[] p) {
        StringBuilder b = new StringBuilder("(");
        for (int i = 0; i < p.length; i++) { if (i > 0) b.append(','); b.append(p[i].getName()); }
        return b.append(')').toString();
    }

    private static Object callNoArg(Object target, String name) {
        if (target == null) return null;
        for (Class<?> c = target.getClass(); c != null; c = c.getSuperclass()) {
            try { Method m = c.getDeclaredMethod(name); m.setAccessible(true); return m.invoke(target); }
            catch (NoSuchMethodException ignored) { }
            catch (Throwable t) { log("Call " + name + " failed: " + t); return null; }
        }
        return null;
    }

    private static Object callOneArg(Object target, String name, Object arg) {
        if (target == null) return null;
        for (Method m : target.getClass().getMethods()) {
            if (!m.getName().equals(name) || m.getParameterTypes().length != 1) continue;
            try { m.setAccessible(true); return m.invoke(target, arg); } catch (Throwable ignored) { }
        }
        return null;
    }

    private static Integer readIntNoArg(Object target, String name) {
        Object v = callNoArg(target, name);
        return v instanceof Number ? ((Number) v).intValue() : null;
    }

    private static boolean hasMethod(Class<?> c, String name) {
        for (Class<?> k = c; k != null; k = k.getSuperclass())
            for (Method m : k.getDeclaredMethods()) if (m.getName().equals(name)) return true;
        return false;
    }

    private static String abbreviate(String s, int max) { return s.length() <= max ? s : s.substring(0, max) + "…"; }

    private static void log(String s) {
        String line = "[" + System.currentTimeMillis() + "] " + TAG + s;
        XposedBridge.log(line);
        synchronized (LOG_BUFFER) {
            LOG_BUFFER.addLast(line);
            while (LOG_BUFFER.size() > MAX_LOG_LINES) LOG_BUFFER.removeFirst();
        }
        if (shouldAutoCopy(s)) scheduleClipboardCopy();
    }

    private static boolean shouldAutoCopy(String s) {
        String v = s.toLowerCase(Locale.ROOT);
        return v.contains("loaded in edge process")
                || v.contains("popup monitor:")
                || v.contains("promo filter:")
                || v.contains("smartback:")
                || v.contains("long-press more:")
                || v.contains("extension panel entry not resolved")
                || v.contains("hook failed")
                || v.contains("hook error")
                || v.contains("clipboard copy failed");
    }

    private static void scheduleClipboardCopy() {
        // Debounce to one clipboard update per short burst. This is intentionally
        // foreground-only; Android may reject clipboard writes from background apps.
        if (foregroundActivity == null) return;
        MAIN.removeCallbacks(CLIPBOARD_COPY_TASK);
        long wait = Math.max(350L, 1800L - (System.currentTimeMillis() - lastClipboardCopyAt));
        MAIN.postDelayed(CLIPBOARD_COPY_TASK, wait);
    }

    private static void copyDiagnosticsToClipboard() {
        Activity a = foregroundActivity;
        if (a == null || a.isFinishing() || a.isDestroyed()) return;
        StringBuilder all = new StringBuilder();
        synchronized (LOG_BUFFER) {
            for (String line : LOG_BUFFER) all.append(line).append('\n');
        }
        if (all.length() == 0) return;
        try {
            ClipboardManager cm = (ClipboardManager) a.getSystemService(Context.CLIPBOARD_SERVICE);
            if (cm == null) return;
            cm.setPrimaryClip(ClipData.newPlainText("EdgeEnhance diagnostics", all.toString()));
            lastClipboardCopyAt = System.currentTimeMillis();
            // Avoid calling log() here: that would schedule an endless copy loop.
            int lineCount;
            synchronized (LOG_BUFFER) { lineCount = LOG_BUFFER.size(); }
            XposedBridge.log(TAG + "Diagnostics copied to clipboard; lines=" + lineCount);
        } catch (Throwable t) {
            XposedBridge.log(TAG + "Clipboard copy failed: " + t);
        }
    }
}
