/*
 * Copyright (C) 2010 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.systemui.statusbar.policy;

import android.content.BroadcastReceiver;
import android.content.ContentResolver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.database.ContentObserver;
import android.graphics.drawable.Animatable;
import android.graphics.Rect;
import android.os.BatteryManager;
import android.os.Handler;
import android.provider.Settings;
import android.util.AttributeSet;
import android.util.DisplayMetrics;
import android.util.Log;
import android.view.View;
import android.view.animation.AccelerateInterpolator;
import android.view.animation.Animation;
import android.view.animation.TranslateAnimation;
import android.widget.LinearLayout;
import android.widget.RelativeLayout;

import com.android.systemui.Dependency;
import com.android.systemui.statusbar.policy.DarkIconDispatcher.DarkReceiver;

import ru.baikalos.gear.util.BaikalOSUtils;

public class BatteryBar extends RelativeLayout implements Animatable, DarkReceiver {

    private static final String TAG = BatteryBar.class.getSimpleName();

    // Total animation duration
    private static final int ANIM_DURATION = 1000; // 5 seconds

    private boolean mAttached = false;
    private int mBatteryLevel = 0;
    private int mChargingLevel = -1;
    private boolean mBatteryCharging = false;
    private boolean shouldAnimateCharging = true;
    private boolean isAnimating = false;
    private boolean isDark;

    private int mColor = 0xFFFFFFFF;
    private int mChargingColor = 0xFFFFFF00;
    private int mBatteryLowColor = 0xFFFFFFFF;
    private int mDarkColor = 0x99000000;
    private int mChargingDarkColor = 0xFF0D47A1;
    private int mBatteryLowDarkColor = 0x99000000;
    private boolean mUseChargingColor = true;
    private boolean mBlendColorsReversed = false;
    private boolean mBlendDarkColorsReversed = false;

    private Handler mHandler = new Handler();

    LinearLayout mBatteryBarLayout;
    View mBatteryBar;

    LinearLayout mChargerLayout;
    View mCharger;

    public static final int STYLE_REGULAR = 0;
    public static final int STYLE_SYMMETRIC = 1;

    boolean vertical = false;

    class SettingsObserver extends ContentObserver {

        public SettingsObserver(Handler handler) {
            super(handler);
        }

        void observer() {
            ContentResolver resolver = mContext.getContentResolver();
            resolver.registerContentObserver(
                    Settings.System.getUriFor(Settings.System.STATUSBAR_BATTERY_BAR), false, this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(Settings.System.STATUSBAR_BATTERY_BAR_COLOR), false,
                    this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(Settings.System.STATUSBAR_BATTERY_BAR_DARK_COLOR),
                    false, this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(Settings.System.STATUSBAR_BATTERY_BAR_CHARGING_COLOR),
                    false, this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(
                        Settings.System.STATUSBAR_BATTERY_BAR_CHARGING_DARK_COLOR),
                    false, this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(
                            Settings.System.STATUSBAR_BATTERY_BAR_BATTERY_LOW_COLOR), false, this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(
                            Settings.System.STATUSBAR_BATTERY_BAR_BATTERY_LOW_DARK_COLOR),
                    false, this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(Settings.System.STATUSBAR_BATTERY_BAR_ANIMATE),
                    false, this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(
                            Settings.System.STATUSBAR_BATTERY_BAR_ENABLE_CHARGING_COLOR), false,
                    this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(
                            Settings.System.STATUSBAR_BATTERY_BAR_BLEND_COLORS_REVERSE), false,
                    this);
            resolver.registerContentObserver(
                    Settings.System.getUriFor(
                            Settings.System.STATUSBAR_BATTERY_BAR_BLEND_DARK_COLORS_REVERSE), false,
                    this);
        }

        @Override
        public void onChange(boolean selfChange) {
            updateSettings();
        }
    }

    public BatteryBar(Context context) {
        this(context, null);
    }

    public BatteryBar(Context context, boolean isCharging, int currentCharge) {
        this(context, null);

        mBatteryLevel = currentCharge;
        mBatteryCharging = isCharging;
    }

    public BatteryBar(Context context, boolean isCharging, int currentCharge, boolean isVertical) {
        this(context, null);

        mBatteryLevel = currentCharge;
        mBatteryCharging = isCharging;
        vertical = isVertical;
    }

    public BatteryBar(Context context, AttributeSet attrs) {
        this(context, attrs, 0);
    }

    public BatteryBar(Context context, AttributeSet attrs, int defStyle) {
        super(context, attrs, defStyle);
    }

    @Override
    protected void onAttachedToWindow() {
        super.onAttachedToWindow();
        if (!mAttached) {
            mAttached = true;

            mBatteryBarLayout = new LinearLayout(mContext);
            addView(mBatteryBarLayout, new RelativeLayout.LayoutParams(LayoutParams.MATCH_PARENT,
                    LayoutParams.MATCH_PARENT));

            mBatteryBar = new View(mContext);
            mBatteryBarLayout.addView(mBatteryBar, new LinearLayout.LayoutParams(
                    LayoutParams.MATCH_PARENT, LayoutParams.MATCH_PARENT));

            DisplayMetrics metrics = getContext().getResources().getDisplayMetrics();
            float dp = 4f;
            int pixels = (int) (metrics.density * dp + 0.5f);

            // charger
            mChargerLayout = new LinearLayout(mContext);

            if (vertical)
                addView(mChargerLayout, new RelativeLayout.LayoutParams(LayoutParams.MATCH_PARENT,
                        pixels));
            else
                addView(mChargerLayout, new RelativeLayout.LayoutParams(pixels,
                        LayoutParams.MATCH_PARENT));

            mCharger = new View(mContext);
            mChargerLayout.setVisibility(View.GONE);
            mChargerLayout.addView(mCharger, new LinearLayout.LayoutParams(
                    LayoutParams.MATCH_PARENT, LayoutParams.MATCH_PARENT));

            IntentFilter filter = new IntentFilter();
            filter.addAction(Intent.ACTION_BATTERY_CHANGED);
            filter.addAction(Intent.ACTION_SCREEN_OFF);
            filter.addAction(Intent.ACTION_SCREEN_ON);
            getContext().registerReceiver(mIntentReceiver, filter, null, getHandler());

            SettingsObserver observer = new SettingsObserver(mHandler);
            observer.observer();
            updateSettings();
        }
        Dependency.get(DarkIconDispatcher.class).addDarkReceiver(this);
    }

    @Override
    protected void onDetachedFromWindow() {
        super.onDetachedFromWindow();
        if (mAttached) {
            mAttached = false;
            getContext().unregisterReceiver(mIntentReceiver);
        }
        Dependency.get(DarkIconDispatcher.class).removeDarkReceiver(this);
    }

    private final BroadcastReceiver mIntentReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            String action = intent.getAction();

            if (Intent.ACTION_BATTERY_CHANGED.equals(action)) {
                mBatteryLevel = intent.getIntExtra(BatteryManager.EXTRA_LEVEL, 0);
                mBatteryCharging = intent.getIntExtra(BatteryManager.EXTRA_STATUS, 0) == BatteryManager.BATTERY_STATUS_CHARGING;
                if (mBatteryCharging && mBatteryLevel < 100) {
                    start();
                } else {
                    stop();
                }
                setProgress(mBatteryLevel);
            } else if (Intent.ACTION_SCREEN_OFF.equals(action)) {
                stop();
            } else if (Intent.ACTION_SCREEN_ON.equals(action)) {
                if (mBatteryCharging && mBatteryLevel < 100) {
                    start();
                }
            }
        }
    };

    private void updateSettings() {
        ContentResolver resolver = getContext().getContentResolver();

        mColor = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_COLOR, 0xFFFFFFFF);
        mDarkColor = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_DARK_COLOR, 0x99000000);
        mChargingColor = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_CHARGING_COLOR, 0xFFFFFF00);
        mChargingDarkColor = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_CHARGING_DARK_COLOR, 0xFF0D47A1);
        mBatteryLowColor = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_BATTERY_LOW_COLOR, 0xFFFFFFFF);
        mBatteryLowDarkColor = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_BATTERY_LOW_DARK_COLOR, 0x99000000);

        shouldAnimateCharging = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_ANIMATE, 0) == 1;

        mUseChargingColor = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_ENABLE_CHARGING_COLOR, 1) == 1;
        mBlendColorsReversed = Settings.System.getInt(resolver,
                Settings.System.STATUSBAR_BATTERY_BAR_BLEND_COLORS_REVERSE, 0) == 1;

        if (mBatteryCharging && mBatteryLevel < 100 && shouldAnimateCharging) {
            start();
        } else {
            stop();
        }
        setProgress(mBatteryLevel);
    }

    private void setProgress(int n) {
        if (vertical) {
            int w = (int) (((getHeight() / 100.0) * n) + 0.5);
            RelativeLayout.LayoutParams params = (RelativeLayout.LayoutParams) mBatteryBarLayout
                    .getLayoutParams();
            params.height = w;
            mBatteryBarLayout.setLayoutParams(params);

        } else {
            int w = (int) (((getWidth() / 100.0) * n) + 0.5);
            RelativeLayout.LayoutParams params = (RelativeLayout.LayoutParams) mBatteryBarLayout
                    .getLayoutParams();
            params.width = w;
            mBatteryBarLayout.setLayoutParams(params);
        }
        // Update color
        int color = getColorForPercent(n);
        mBatteryBar.setBackgroundColor(color);
        mCharger.setBackgroundColor(color);
    }

    @Override
    public void start() {
        if (!shouldAnimateCharging)
            return;

        if (vertical) {
            TranslateAnimation a = new TranslateAnimation(getX(), getX(), getHeight(),
                    mBatteryBarLayout.getHeight());
            a.setInterpolator(new AccelerateInterpolator());
            a.setDuration(ANIM_DURATION);
            a.setRepeatCount(Animation.INFINITE);
            mChargerLayout.startAnimation(a);
            mChargerLayout.setVisibility(View.VISIBLE);
        } else {
            TranslateAnimation a = new TranslateAnimation(getWidth(), mBatteryBarLayout.getWidth(),
                    getTop(), getTop());
            a.setInterpolator(new AccelerateInterpolator());
            a.setDuration(ANIM_DURATION);
            a.setRepeatCount(Animation.INFINITE);
            mChargerLayout.startAnimation(a);
            mChargerLayout.setVisibility(View.VISIBLE);
        }
        isAnimating = true;
    }

    @Override
    public void stop() {
        mChargerLayout.clearAnimation();
        mChargerLayout.setVisibility(View.GONE);
        isAnimating = false;
    }

    @Override
    public boolean isRunning() {
        return isAnimating;
    }

    private int getColorForPercent(int percentage) {
        if (mBatteryCharging && mUseChargingColor) {
            return isDark ? mChargingDarkColor : mChargingColor;
        } else {
            if (isDark) {
                return BaikalOSUtils.getBlendColorForPercent(mDarkColor, mBatteryLowDarkColor,
                        mBlendDarkColorsReversed, percentage);
            } else {
                return BaikalOSUtils.getBlendColorForPercent(mColor, mBatteryLowColor,
                        mBlendColorsReversed, percentage);
            }
        }
    }


    @Override
    public void onDarkChanged(Rect area, float darkIntensity, int tint) {
        float intensity = DarkIconDispatcher.isInArea(area, this) ? darkIntensity : 0;
        isDark = intensity > 0.5;
        // Update colors
        setProgress(mBatteryLevel);
    }

}
