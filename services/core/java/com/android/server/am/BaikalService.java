/*
 * Copyright (C) 2015 The Android Open Source Project
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

package com.android.server.am;

import android.app.Service;
import android.app.AlarmManager;
import android.app.AppOpsManager;
import android.app.Activity;
import android.app.ActivityManager;

import android.content.ComponentName;
import android.content.Context;
import android.content.ContentResolver;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.ResolveInfo;
import android.content.pm.ServiceInfo;
import android.content.BroadcastReceiver;
import android.database.ContentObserver;
import android.os.Binder;
import android.os.IBinder;
import android.os.SystemProperties;
import android.os.Handler;
import android.os.HandlerThread;
import android.os.Looper;
import android.os.Message;
import android.os.PowerManager;
import android.os.PowerManagerInternal;
import android.os.UserHandle;
import android.os.Process;
import android.os.SystemClock;
import android.os.IBaikalServiceController;
import android.os.BaikalServiceManager;
import android.util.Slog;
import android.util.ArrayMap;
import android.net.NetworkInfo;
import android.net.Uri;
import com.android.internal.os.BackgroundThread;
import com.android.internal.util.ArrayUtils;
import com.android.server.power.PowerManagerService;
import com.android.server.power.PowerManagerService.WakeLock;
import com.android.server.am.ProcessRecord;
import com.android.server.am.ServiceRecord;
import com.android.server.am.BroadcastRecord;
import com.android.server.am.BroadcastFilter;
import com.android.server.am.ReceiverList;
import com.android.server.am.ActivityManagerService;
import com.android.server.DeviceIdleController;
import com.android.server.AlarmManagerService;
import com.android.server.AppOpsService;
import com.android.server.SystemService;

import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;


import android.os.Environment;
import android.os.FileUtils;

import android.util.Xml;

import com.android.internal.annotations.GuardedBy;
import com.android.internal.app.IBatteryStats;
import com.android.internal.os.AtomicFile;
import com.android.internal.os.BackgroundThread;
import com.android.internal.util.DumpUtils;
import com.android.internal.util.FastXmlSerializer;
import com.android.internal.util.Preconditions;
import com.android.internal.util.XmlUtils;



import org.xmlpull.v1.XmlPullParser;
import org.xmlpull.v1.XmlPullParserException;
import org.xmlpull.v1.XmlSerializer;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileDescriptor;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.ArrayList;

import android.util.ArrayMap;
import android.util.ArraySet;
import android.util.KeyValueListParser;
import android.util.MutableLong;
import android.util.Pair;


import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.hardware.SystemSensorManager;

import android.telephony.PhoneStateListener;
import android.telephony.ServiceState;
import android.telephony.TelephonyManager;
import android.telephony.CellLocation;
import android.telephony.CellInfo;
import android.telephony.SignalStrength;
import android.telephony.PreciseCallState;
import android.telephony.PreciseDataConnectionState;
import android.telephony.DataConnectionRealTimeInfo;
import android.telephony.VoLteServiceState;

import android.hardware.camera2.CameraAccessException;
import android.hardware.camera2.CameraCharacteristics;
import android.hardware.camera2.CameraManager;

import android.provider.Settings;

import java.util.List;

// Changed from VSCode

public class BaikalService extends SystemService {

    private static final String TAG = "BaikalService";

    private static final boolean DEBUG = false;
    private static final boolean DEBUG_PROFILE = DEBUG | true;

    private static final int SENSOR_HALL_TYPE=33171016;

    private static final int MESSAGE_DEVICE_IDLE_CHANGED = 100;
    private static final int MESSAGE_LIGHT_DEVICE_IDLE_CHANGED = 101;

    private static final int MESSAGE_TOP_APP_CHANGED = 150;
    private static final int MESSAGE_BRIGHTNESS_CHANGED = 151;

    private static final int MESSAGE_PROXIMITY_WAKELOCK_TIMEOUT = 200;

    private static final int MESSAGE_WRITE_CONFIG = 900;

    private static final int MESSAGE_WAKEFULNESS_CHANGED = 300;



    private final String [] mGoogleServicesIdleBlackListed = {
        "com.google.android.location.geocode.GeocodeService",
        "com.google.android.location.geofencer.service.GeofenceProviderService",
        "com.google.android.location.network.NetworkLocationService",
        "com.google.android.location.internal.GoogleLocationManagerService",
        "com.google.android.location.reporting.service.ReportingAndroidService",
        "com.google.android.location.internal.server.GoogleLocationService",
        "com.google.android.location.fused.FusedLocationService",
        "com.google.android.location.internal.server.HardwareArProviderService",
        "com.google.android.location.places.service.PlaceDetectionAsyncService",
        "com.google.android.gms.tron.CollectionService",
        "com.google.location.nearby.direct.service.NearbyDirectService",
        ".lockbox.service.LockboxBrokerService",
        ".usagereporting.service.UsageReportingService"
    };


    private boolean mSystemReady = false;

    private boolean mDeviceIdleMode;
    private boolean mLightDeviceIdleMode;
    private int mWakefulness = 1;
    private int mWakefulnessReason;
    private String mLastWakeupReason;
    private String mLastSleepReason;
    private boolean mSleeping;

    private boolean mTorchLongPressPowerEnabled;
    private boolean mTorchIncomingCall;
    private boolean mTorchNotification;
    private boolean mActiveIncomingCall;
    private boolean mIsReaderModeActive;
    private int mBrightnessOverride = -1;

    private boolean mExtremeSaverEnabled;
    private boolean mExtremeSaverActive;

    private boolean mLowPowerState;

    private boolean mTorchEnabled;

    private boolean mIdleAggressive;
    private boolean mLimitServices = true;
    private boolean mLimitBroadcasts = true;

    private boolean mApplyRestrictionsScreenOn = false;

    private boolean mProximityServiceWakeupEnabled = false;
    private boolean mProximityServiceSleepEnabled = false;
    private boolean mHallSensorServiceEnabled = false;
    
    private boolean mThrottleAlarms;
    private boolean mQtiBiometricsInitialized;

    private boolean mWlBlockEnabled;


    private final ArrayMap<String, ApplicationProfileInfo> mApplicationProfiles = new ArrayMap<>();


    Thread mTorchThread = null;

    private final Context mContext;
    private Constants mConstants;
    final MyHandler mHandler;
    final MyHandlerThread mHandlerThread;


    private CameraManager mCameraManager;
    private String mRearFlashCameraId;


    // The sensor manager.
    private SensorManager mSensorManager;

    private ProximityService mProximityService;
    private HallSensorService mHallSensorService;
    PowerManager.WakeLock mProximityWakeLock;


    AppOpsService mAppOpsService;

    AlarmManagerService mAlarmManagerService;
    PowerManager mPowerManager;
    PowerManagerService mPowerManagerService;
    ActivityManagerService mActivityManagerService;

    private boolean mNetworkAllowedWhileIdle;

    Object mProfileSync = new Object();
    Object mCurrentProfileSync = new Object();
    public final AtomicFile mAppsConfigFile;


    private final Intent mReaderOnIntent;
    private final Intent mReaderOffIntent;
    private final Intent mBrightnessOverrideIntent;


    Object mWhitelistSync = new Object();
    // Set of app ids that we will always respect the wake locks for.
    int[] mDeviceIdleWhitelist = new int[0];

    // Set of app ids that are temporarily allowed to acquire wakelocks due to high-pri message
    int[] mDeviceIdleTempWhitelist = new int[0];

    final ArrayMap<String, RestrictionStatistics> mRestrictionStatistics = new ArrayMap<String, RestrictionStatistics>();

    public BaikalService(Context context) {
        super(context);
        mContext = context;
        if( DEBUG ) {
            Slog.i(TAG,"BaikalService()");
        }

        mHandlerThread = new MyHandlerThread();
        mHandlerThread.start();
        mHandler = new MyHandler(mHandlerThread.getLooper());

        mAppsConfigFile = new AtomicFile(new File(getSystemDir(), "baikal_service_apps.xml"));

        mReaderOnIntent = new Intent(BaikalServiceManager.ACTION_READER_ON);
        mReaderOnIntent.addFlags(
                Intent.FLAG_RECEIVER_REGISTERED_ONLY | Intent.FLAG_RECEIVER_FOREGROUND
                | Intent.FLAG_RECEIVER_VISIBLE_TO_INSTANT_APPS);
        mReaderOffIntent = new Intent(BaikalServiceManager.ACTION_READER_OFF);
        mReaderOffIntent.addFlags(
                Intent.FLAG_RECEIVER_REGISTERED_ONLY | Intent.FLAG_RECEIVER_FOREGROUND
                | Intent.FLAG_RECEIVER_VISIBLE_TO_INSTANT_APPS);

        mBrightnessOverrideIntent = new Intent(BaikalServiceManager.ACTION_BRIGHTNESS_CHANGED);
        mBrightnessOverrideIntent.addFlags(
                Intent.FLAG_RECEIVER_REGISTERED_ONLY | Intent.FLAG_RECEIVER_FOREGROUND
                | Intent.FLAG_RECEIVER_VISIBLE_TO_INSTANT_APPS);


    }

    @Override
    public void onStart() {
        if( DEBUG ) {
            Slog.i(TAG,"onStart()");
        }
        mBinderService = new BinderService();
        publishBinderService(Context.BAIKAL_SERVICE_CONTROLLER, mBinderService);
        publishLocalService(BaikalService.class, this);

        readConfigFileLocked();
    }

    @Override
    public void onBootPhase(int phase) {
        if( DEBUG ) {
            Slog.i(TAG,"onBootPhase(" + phase + ")");
        }

        if (phase == PHASE_BOOT_COMPLETED) {

            synchronized(this) {
                mConstants = new Constants(mHandler, getContext().getContentResolver());

                // get notified of phone state changes
                TelephonyManager telephonyManager =
                        (TelephonyManager) mContext.getSystemService(Context.TELEPHONY_SERVICE);
                telephonyManager.listen(mPhoneStateListener, 0xFFFFFFF);

                mCameraManager = (CameraManager) mContext.getSystemService(Context.CAMERA_SERVICE);
                mCameraManager.registerTorchCallback(new TorchModeCallback(), mHandler);

                mSensorManager = (SensorManager) mContext.getSystemService(Context.SENSOR_SERVICE);
                Slog.i(TAG,"SensorManager initialized");
    
                mPowerManager = (PowerManager) getContext().getSystemService(Context.POWER_SERVICE);
                mProximityWakeLock = mPowerManager.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "*baikal_proximity*");


                mProximityService = new ProximityService();
                mProximityService.Initialize();

                mHallSensorService = new HallSensorService();
                mHallSensorService.Initialize();

                final PackageManager pm = getContext().getPackageManager();

                try {
                    ApplicationInfo ai = pm.getApplicationInfo("com.google.android.gms",
                               PackageManager.MATCH_ALL);
                    if( ai != null ) {
                        setGmsUid(ai.uid);
                        Slog.i(TAG,"onBootPhase(" + phase + "): Google Play Services uid=" + ai.uid);
                    }
                } catch(Exception e) {
                    Slog.i(TAG,"onBootPhase(" + phase + "): Google Play Services not found on this device.");
                }

                mConstants.updateConstantsLocked();

                setBrightnessOverrideLocked(0);
                setPerformanceProfile("default");
                setThermalProfile("default");
                mCurrentThermalProfile = "";
                mCurrentPerformanceProfile = "";


                IntentFilter btFilter = new IntentFilter();
                btFilter.addAction(BluetoothDevice.ACTION_ACL_CONNECTED);
                btFilter.addAction(BluetoothDevice.ACTION_ACL_DISCONNECTED);
                btFilter.addAction(BluetoothDevice.ACTION_ACL_DISCONNECT_REQUESTED);
                mContext.registerReceiver(mBluetoothReceiver, btFilter);
            }

        }
    }

    private final BroadcastReceiver mBluetoothReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            synchronized (BaikalService.this) {
                String action = intent.getAction();
                BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);
                if (BluetoothDevice.ACTION_ACL_CONNECTED.equals(action)) {
                    updateBluetoothDeviceState(0,device);
                } else if(BluetoothDevice.ACTION_ACL_DISCONNECTED.equals(action)) {
                    updateBluetoothDeviceState(1,device);
                } else if(BluetoothDevice.ACTION_ACL_DISCONNECT_REQUESTED.equals(action)) {
                    updateBluetoothDeviceState(2,device);
                }
            }
        }
    };


    private void updateBluetoothDeviceState(int state, BluetoothDevice device) {
        Slog.i(TAG,"updateBluetoothDeviceState: state=" + state + ", device=" + device);                
    }

    public void setAlarmManagerService(AlarmManagerService service) {
        synchronized (this) {
            mAlarmManagerService = service;
        }
    }

    public void setPowerManagerService(PowerManagerService service) {
        synchronized (this) {
            mPowerManagerService = service;
        }
    }

    public void setActivityManagerService(ActivityManagerService service, AppOpsService appOps) {
        synchronized (this) {
            mActivityManagerService = service;
            mAppOpsService = appOps;
        }
    }

    /*
    public void setDeviceIdleController(DeviceIdleController service) {
        synchronized (this) {
            mDeviceIdleController = service;
        }
    }*/

    @Override
    public void onSwitchUser(int userHandle) {
        if( DEBUG ) {
            Slog.i(TAG,"onSwitchUser()");
        }
    }

    @Override
    public void onUnlockUser(int userHandle) {
        if( DEBUG ) {
            Slog.i(TAG,"onUnlockUser()");
        }
    }

    final class MyHandler extends Handler {
        MyHandler(Looper looper) {
            super(looper);
        }

        @Override public void handleMessage(Message msg) {
            switch (msg.what) {
                case MESSAGE_DEVICE_IDLE_CHANGED:
                onDeviceIdleModeChanged();
                break;
                case MESSAGE_LIGHT_DEVICE_IDLE_CHANGED:
                onLightDeviceIdleModeChanged();
                break;
                case MESSAGE_PROXIMITY_WAKELOCK_TIMEOUT:
                if( mProximityService != null ) {
                    mProximityService.handleProximityTimeout();
                }
                break;
                case MESSAGE_WRITE_CONFIG: {
                    // Does not hold a wakelock. Just let this happen whenever.
                    handleWriteConfigFile();
                } break;
                case MESSAGE_WAKEFULNESS_CHANGED: {
                    onWakefulnessChanged();
                } break;
                case MESSAGE_TOP_APP_CHANGED: {
                    onTopAppChanged();
                } break;
                case MESSAGE_BRIGHTNESS_CHANGED:{
                    onBrightnessChanged();
                } break;
            }
        }
    }

    private final class Constants extends ContentObserver {

        private final ContentResolver mResolver;

        public Constants(Handler handler, ContentResolver resolver) {
            super(handler);
            mResolver = resolver;

            try {
            resolver.registerContentObserver(Settings.System.getUriFor(
                    Settings.System.TORCH_LONG_PRESS_POWER_GESTURE), false, this,
                    UserHandle.USER_ALL);

            resolver.registerContentObserver(Settings.System.getUriFor(
                    Settings.System.TORCH_ON_INCOMING_CALL), false, this,
                    UserHandle.USER_ALL);

            resolver.registerContentObserver(Settings.System.getUriFor(
                    Settings.System.TORCH_ON_NOTIFICATION), false, this,
                    UserHandle.USER_ALL);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.POWERSAVE_THROTTLE_ALARMS_ENABLED),
                    false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.DEVICE_IDLE_AGGRESSIVE_ENABLED),
                    false, this);

            resolver.registerContentObserver(Settings.Global.getUriFor(
                    Settings.Global.POWERSAVE_WL_BLOCK_ENABLED), false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.POWERSAVE_RESTRICT_SCREEN_ON),
                    false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.BAIKAL_WAKEUP_PROXIMITY),
                    false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.BAIKAL_SLEEP_PROXIMITY),
                    false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.BAIKAL_HALL_SENSOR),
                    false, this);

            //resolver.registerContentObserver(
            //        Settings.Global.getUriFor(Settings.Global.BAIKAL_EXTREME_SAVER_ACTIVE),
            //        false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.BAIKAL_EXTREME_SAVER_ENABLED),
                    false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.POWERSAVE_BLOCK_GMS1_ENABLED),
                    false, this);

            resolver.registerContentObserver(
                    Settings.Global.getUriFor(Settings.Global.POWERSAVE_BLOCK_GMS2_ENABLED),
                    false, this);

            } catch( Exception e ) {
            }

            updateConstants();
        }

        @Override
        public void onChange(boolean selfChange, Uri uri) {
            updateConstants();
        }

        private void updateConstants() {
            synchronized (BaikalService.this) {
                updateConstantsLocked();
            }

            synchronized (mStaticMembersLock) {
                updateStaticConstantsLocked();
	        }
        }

        public void updateConstantsLocked() {
            try {
                mTorchLongPressPowerEnabled = Settings.System.getIntForUser(
                        mResolver, Settings.System.TORCH_LONG_PRESS_POWER_GESTURE, 0,
                        UserHandle.USER_CURRENT) == 1;


                mTorchIncomingCall = Settings.System.getIntForUser(
                        mResolver, Settings.System.TORCH_ON_INCOMING_CALL, 0,
                        UserHandle.USER_CURRENT) == 1;


                mTorchNotification = Settings.System.getIntForUser(
                        mResolver, Settings.System.TORCH_ON_NOTIFICATION, 0,
                        UserHandle.USER_CURRENT) == 1;


                mIdleAggressive = Settings.Global.getInt(mResolver,
                        Settings.Global.DEVICE_IDLE_AGGRESSIVE_ENABLED) == 1;

                mThrottleAlarms = Settings.Global.getInt(mResolver, 
                        Settings.Global.POWERSAVE_THROTTLE_ALARMS_ENABLED) == 1;

                mWlBlockEnabled = Settings.Global.getInt(mResolver, 
                        Settings.Global.POWERSAVE_WL_BLOCK_ENABLED) == 1;

                mApplyRestrictionsScreenOn = Settings.Global.getInt(mResolver, 
                        Settings.Global.POWERSAVE_RESTRICT_SCREEN_ON) == 1;

                mProximityServiceWakeupEnabled = Settings.Global.getInt(mResolver, 
                        Settings.Global.BAIKAL_WAKEUP_PROXIMITY) == 1;

                mProximityServiceSleepEnabled = Settings.Global.getInt(mResolver, 
                        Settings.Global.BAIKAL_SLEEP_PROXIMITY) == 1;

                mHallSensorServiceEnabled = Settings.Global.getInt(mResolver, 
                        Settings.Global.BAIKAL_HALL_SENSOR) == 1;


                if( mProximityService != null ) {
                    mProximityService.setProximitySensorEnabled(mProximityServiceWakeupEnabled | mProximityServiceSleepEnabled | mHallSensorServiceEnabled);
                }
                if( mHallSensorService != null ) {
                    mHallSensorService.setHallSensorEnabled(mHallSensorServiceEnabled);
                }


	        //mExtremeSaverActive = Settings.Global.getInt(mResolver, 
	        //    Settings.Global.BAIKAL_EXTREME_SAVER_ACTIVE) == 1;

	            mExtremeSaverEnabled = Settings.Global.getInt(mResolver, 
	                    Settings.Global.BAIKAL_EXTREME_SAVER_ENABLED) == 1;

                    //mParser.setString(Settings.Global.getString(mResolver,
                    //        Settings.Global.DEVICE_IDLE_CONSTANTS));


            } catch (Exception e) {
                    // Failed to parse the settings string, log this and move on
                    // with defaults.
                Slog.e(TAG, "Bad BaikalService settings", e);
            }

            Slog.d(TAG, "updateConstantsLocked: mTorchLongPressPowerEnabled=" + mTorchLongPressPowerEnabled +
                        ", mTorchIncomingCall=" + mTorchIncomingCall +
                        ", mTorchNotification=" + mTorchNotification +
                        ", mIdleAggressive=" + mIdleAggressive +
                        ", mApplyRestrictionsScreenOn=" + mApplyRestrictionsScreenOn +
                        ", mProximityServiceWakeupEnabled=" + mProximityServiceWakeupEnabled +
                        ", mProximityServiceSleepEnabled=" + mProximityServiceSleepEnabled +
                        ", mHallSensorServiceEnabled=" + mHallSensorServiceEnabled +
                        ", mThrottleAlarms=" + mThrottleAlarms);

        }

    

        public void updateStaticConstantsLocked() {
            try {
	        mHideIdleFromGms = Settings.Global.getInt(mResolver, 
	            Settings.Global.POWERSAVE_BLOCK_GMS1_ENABLED) == 1;

	        mUnrestrictedNetwork = Settings.Global.getInt(mResolver, 
	            Settings.Global.POWERSAVE_BLOCK_GMS2_ENABLED) == 1;


            } catch (Exception e) {
                    // Failed to parse the settings string, log this and move on
                    // with defaults.
                Slog.e(TAG, "Bad BaikalService static settings", e);
            }

            Slog.d(TAG, "updateStaticConstantsLocked: mHideIdleFromGms=" + mHideIdleFromGms +
                        ", mUnrestrictedNetwork=" + mUnrestrictedNetwork);

        }

    }

    PhoneStateListener mPhoneStateListener = new PhoneStateListener() {
        @Override
        public void onServiceStateChanged(ServiceState serviceState) {
            //if (!mHasTelephony) return;
            //final boolean inAirplaneMode = serviceState.getState() == ServiceState.STATE_POWER_OFF;
            //mAirplaneState = inAirplaneMode ? ToggleAction.State.On : ToggleAction.State.Off;
            //mAirplaneModeOn.updateState(mAirplaneState);
            //mAdapter.notifyDataSetChanged();
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onServiceStateChanged(" + serviceState + ")");
            }

        }

        /**
         * Callback invoked when network signal strength changes.
         *
         * @see ServiceState#STATE_EMERGENCY_ONLY
         * @see ServiceState#STATE_IN_SERVICE
         * @see ServiceState#STATE_OUT_OF_SERVICE
         * @see ServiceState#STATE_POWER_OFF
         * @deprecated Use {@link #onSignalStrengthsChanged(SignalStrength)}
         */
        @Override
        public void onSignalStrengthChanged(int asu) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onSignalStrengthChanged(" + asu + ")");
            }

            // default implementation empty
        }

        /**
         * Callback invoked when the message-waiting indicator changes.
         */
        @Override
        public void onMessageWaitingIndicatorChanged(boolean mwi) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onMessageWaitingIndicatorChanged(" + mwi + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when the call-forwarding indicator changes.
         */
        @Override
        public void onCallForwardingIndicatorChanged(boolean cfi) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onCallForwardingIndicatorChanged(" + cfi + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when device cell location changes.
         */
        @Override
        public void onCellLocationChanged(CellLocation location) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onCellLocationChanged(" + location + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when device call state changes.
         * @param state call state
         * @param incomingNumber incoming call phone number. If application does not have
         * {@link android.Manifest.permission#READ_PHONE_STATE READ_PHONE_STATE} permission, an empty
         * string will be passed as an argument.
         *
         * @see TelephonyManager#CALL_STATE_IDLE
         * @see TelephonyManager#CALL_STATE_RINGING
         * @see TelephonyManager#CALL_STATE_OFFHOOK
         */
        @Override
        public void onCallStateChanged(int state, String incomingNumber) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onCallStateChanged(" + state + "," + incomingNumber + ")");
            }

            synchronized (this) {
                onCallStateChangedLocked(state,incomingNumber);
            }

        // default implementation empty
        }

        /**
         * Callback invoked when connection state changes.
         *
         * @see TelephonyManager#DATA_DISCONNECTED
         * @see TelephonyManager#DATA_CONNECTING
         * @see TelephonyManager#DATA_CONNECTED
         * @see TelephonyManager#DATA_SUSPENDED
         */
        @Override
        public void onDataConnectionStateChanged(int state) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onDataConnectionStateChanged(" + state + ")");
            }
            // default implementation empty
        }

        /**
         * same as above, but with the network type.  Both called.
         */
        @Override
        public void onDataConnectionStateChanged(int state, int networkType) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onDataConnectionStateChanged(" + state + "," + networkType + ")");
            }
        }

        /**
         * Callback invoked when data activity state changes.
         *
         * @see TelephonyManager#DATA_ACTIVITY_NONE
         * @see TelephonyManager#DATA_ACTIVITY_IN
         * @see TelephonyManager#DATA_ACTIVITY_OUT
         * @see TelephonyManager#DATA_ACTIVITY_INOUT
         * @see TelephonyManager#DATA_ACTIVITY_DORMANT
         */
        @Override
        public void onDataActivity(int direction) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onDataActivity(" + direction + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when network signal strengths changes.
         *
         * @see ServiceState#STATE_EMERGENCY_ONLY
         * @see ServiceState#STATE_IN_SERVICE
         * @see ServiceState#STATE_OUT_OF_SERVICE
         * @see ServiceState#STATE_POWER_OFF
         */
        @Override
        public void onSignalStrengthsChanged(SignalStrength signalStrength) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onSignalStrengthsChanged(" + signalStrength + ")");
            }
            // default implementation empty
        }


        /**
         * The Over The Air Service Provisioning (OTASP) has changed. Requires
         * the READ_PHONE_STATE permission.
         * @param otaspMode is integer <code>OTASP_UNKNOWN=1<code>
         *   means the value is currently unknown and the system should wait until
         *   <code>OTASP_NEEDED=2<code> or <code>OTASP_NOT_NEEDED=3<code> is received before
         *   making the decision to perform OTASP or not.
         *
         * @hide
         */
        @Override
        public void onOtaspChanged(int otaspMode) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onOtaspChanged(" + otaspMode + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when a observed cell info has changed,
         * or new cells have been added or removed.
         * @param cellInfo is the list of currently visible cells.
         */
        @Override
        public void onCellInfoChanged(List<CellInfo> cellInfo) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onCellInfoChanged(" + cellInfo + ")");
            }
        }

        /**
         * Callback invoked when precise device call state changes.
         *
         * @hide
         */
        @Override
        public void onPreciseCallStateChanged(PreciseCallState callState) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onPreciseCallStateChanged(" + callState + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when data connection state changes with precise information.
         *
         * @hide
         */
        @Override
        public void onPreciseDataConnectionStateChanged(
                PreciseDataConnectionState dataConnectionState) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onPreciseDataConnectionStateChanged(" + dataConnectionState + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when data connection state changes with precise information.
         *
         * @hide
         */
        @Override
        public void onDataConnectionRealTimeInfoChanged(
                DataConnectionRealTimeInfo dcRtInfo) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onDataConnectionRealTimeInfoChanged(" + dcRtInfo + ")");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when the service state of LTE network
         * related to the VoLTE service has changed.
         * @param stateInfo is the current LTE network information
         * @hide
         */
        @Override
        public void onVoLteServiceStateChanged(VoLteServiceState stateInfo) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onVoLteServiceStateChanged(" + stateInfo + ")");
            }
        }

        /**
         * Callback invoked when the SIM voice activation state has changed
         * @param state is the current SIM voice activation state
         * @hide
         */
        @Override
        public void onVoiceActivationStateChanged(int state) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onVoiceActivationStateChanged(" + state + ")");
            }
   
        }

        /**
         * Callback invoked when the SIM data activation state has changed
         * @param state is the current SIM data activation state
         * @hide
         */
        @Override
        public void onDataActivationStateChanged(int state) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onDataActivationStateChanged(" + state + ")");
            }
    
        }

        /**
         * Callback invoked when OEM hook raw event is received. Requires
         * the READ_PRIVILEGED_PHONE_STATE permission.
         * @param rawData is the byte array of the OEM hook raw data.
         * @hide
         */
        @Override
        public void onOemHookRawEvent(byte[] rawData) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onOemHookRawEvent( raw )");
            }
            // default implementation empty
        }

        /**
         * Callback invoked when telephony has received notice from a carrier
         * app that a network action that could result in connectivity loss
         * has been requested by an app using
         * {@link android.telephony.TelephonyManager#notifyCarrierNetworkChange(boolean)}
         *
         * @param active Whether the carrier network change is or shortly
         *               will be active. This value is true to indicate
         *               showing alternative UI and false to stop.
         *
         * @hide
         */
        @Override
        public void onCarrierNetworkChange(boolean active) {
            if( DEBUG ) {
                Slog.i(TAG,"PhoneStateListener: onCarrierNetworkChange(" + active + ")");
            }
            // default implementation empty
        }

    };



    private void onCallStateChangedLocked(int state, String phoneNumber) {
        if( state == 1 ) {
            mActiveIncomingCall = true;
        } else {
            mActiveIncomingCall = false;
        }
        if( mActiveIncomingCall && mTorchIncomingCall && mTorchThread == null ) {
            mTorchThread = new Thread(() -> {
                while( true ) {
                    try {
                        toggleTorch(true);
                        Thread.sleep(30);
                        toggleTorch(false);
                        Thread.sleep(50);

                        toggleTorch(true);
                        Thread.sleep(30);
                        toggleTorch(false);
                        Thread.sleep(50);
                    
                        toggleTorch(true);
                        Thread.sleep(30);
                        toggleTorch(false);
                        Thread.sleep(1500);
                    } catch( Exception e ) {
                    }

                    synchronized(BaikalService.this) {
                        if( !mActiveIncomingCall ) {
                            mTorchThread = null;
                            return;
                        }
                    }
                }
            }); 
            mTorchThread.start();
        }
    }


    private BroadcastReceiver mRingerModeReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            //if (intent.getAction().equals(AudioManager.RINGER_MODE_CHANGED_ACTION)) {
                //mHandler.sendEmptyMessage(MESSAGE_REFRESH);
            //}

            if( DEBUG ) {
                Slog.i(TAG,"mRingerModeReceiver: onReceive(" + intent + ")");
            }

        }
    };


    private int getBrightnessOverrideInternal() {
        synchronized(this) {
            return getBrightnessOverrideLocked();
        }
    }

    private boolean isReaderModeInternal() {
        synchronized(this) {
            return isReaderModeLocked();
        }
    }

    private boolean isDeviceIdleModeInternal() {
        synchronized(this) {
            return isDeviceIdleModeLocked();
        }
    }

    private boolean isAggressiveDeviceIdleModeInternal() {
        synchronized(this) {
            return isAggressiveDeviceIdleModeLocked();
        }
    }

    private boolean isLightDeviceIdleModeInternal() {
        synchronized(this) {
            return isLightDeviceIdleModeLocked();
        }
    }

    private void setDeviceIdleModeInternal(boolean mode) {
        synchronized(this) {
            setDeviceIdleModeLocked(mode);
        }
    }

    private void setLightDeviceIdleModeInternal(boolean mode) {
        synchronized(this) {
            setLightDeviceIdleModeLocked(mode);
        }
    }

    private boolean isNetworkAllowedWhileIdleInternal() {
        return false;
    }

    private boolean isExtremeSaverActiveInternal() {
        synchronized(this) {
            return isExtremeSaverActiveLocked();
        }
    }

    private int isRestrictedAppInternal(int requestId, int uid, String packageName, boolean useTempWhitelistToo, boolean exemptOnBatterySaver) {
	return 0;
    }

    void wakefulnessChanged() {
        mHandler.removeMessages(MESSAGE_WAKEFULNESS_CHANGED);
        mHandler.sendEmptyMessage(MESSAGE_WAKEFULNESS_CHANGED);
    }

    private void setWakefulnessInternal(int wakefulness, int reason) {
        synchronized(this) {
            setWakefulnessLocked(wakefulness,reason);
        }
    }

    private int getWakefulnessInternal() {
        synchronized(this) {
            return getWakefulnessLocked(); 
        }        
    }

    private int getWakefulnessReasonInternal() {
        synchronized(this) {
            return getWakefulnessReasonLocked(); 
        }        
    }


    private String lastWakeupReasonInternal() {
        synchronized(this) {
            return lastWakeupReasonLocked();
        }
    }

    private void setLastWakeupReasonInternal(String reason) {
        synchronized(this) {
            setLastWakeupReasonLocked(reason);
        }
    }

    public void setDeviceIdleWhitelist(int[] appids) {
        synchronized (mWhitelistSync) {
            mDeviceIdleWhitelist = appids;
        }
    }

    public void setDeviceIdleTempWhitelist(int[] appids) {
        synchronized (mWhitelistSync) {
            mDeviceIdleTempWhitelist = appids;
        }
    }

    public boolean [] setWakeLockDisabledState(WakeLock wakeLock) {
        boolean [] retval = new boolean[2];
        retval[0] = false;
        retval[1] = false;

        synchronized (this) {
            if( !mWlBlockEnabled ) {
                retval[0] = true;
                if( wakeLock.mDisabled ) {
                    wakeLock.mDisabled = false;
                    retval[1] = true;
                }
                return retval;
            }
        }
        return retval;
    }

    public boolean throttleAlarms() {
        synchronized (this) {
            return mThrottleAlarms;
        }
    }


    public boolean isAggressiveIdle() {
        synchronized (this) {
            return mIdleAggressive;
        }
    }

    public boolean processAlarm(AlarmManagerService.Alarm a, AlarmManagerService.Alarm pendingUntil) {

        if ( a == pendingUntil ) {
            if( DEBUG ) {
                Slog.i(TAG,"DeviceIdleAlarm: unrestricted:" + a.statsTag + ":" + a.toStringLong());
            }
            return false;
        }

        a.wakeup = a.type == AlarmManager.ELAPSED_REALTIME_WAKEUP
                || a.type == AlarmManager.RTC_WAKEUP;

        if ( a.uid < Process.FIRST_APPLICATION_UID && 
            ((a.flags&(AlarmManager.FLAG_ALLOW_WHILE_IDLE_UNRESTRICTED | AlarmManager.FLAG_WAKE_FROM_IDLE)) != 0 
            || a.wakeup)) {

            if( restrictSystemIdleAlarm(a) ) {
                if( DEBUG ) {
                    Slog.i(TAG,"SystemAlarm: throttle IDLE alarm:" + a.statsTag + ":" + a.toStringLong());
                }
                return true;
            }
            
            if( DEBUG ) {
                Slog.i(TAG,"SystemAlarm: unrestricted:" + a.statsTag + ":" + a.toStringLong());
            }
            return false;    
        }

        if( ((a.flags&(AlarmManager.FLAG_ALLOW_WHILE_IDLE_UNRESTRICTED | AlarmManager.FLAG_WAKE_FROM_IDLE)) != 0
            || a.wakeup) ) {

            if( restrictAppIdleAlarm(a) ) {
                if( DEBUG ) {
                    Slog.i(TAG,"AppAlarm: throttle IDLE alarm:" + a.statsTag + ":" + a.toStringLong());
                }
                return true;
            }

            if( DEBUG ) {
                Slog.i(TAG,"AppAlarm: unrestricted:" + a.statsTag + ":" + a.toStringLong());
            }
            return false;
        }

        if( ((a.flags&(AlarmManager.FLAG_ALLOW_WHILE_IDLE)) != 0 || a.wakeup) && a.alarmClock == null ) {
            synchronized (this) {
                if( mThrottleAlarms ) {
                    if( DEBUG ) {
                        Slog.i(TAG,"AppAlarm: throttle IDLE alarm:" + a.statsTag + ":" + a.toStringLong());
                    }
                    a.flags &= ~(AlarmManager.FLAG_WAKE_FROM_IDLE 
                    | AlarmManager.FLAG_ALLOW_WHILE_IDLE
                    | AlarmManager.FLAG_ALLOW_WHILE_IDLE_UNRESTRICTED);
                    a.wakeup = false;
                    return true;
                }
            }
        }

        return false;
    }

    private boolean restrictAppIdleAlarm(AlarmManagerService.Alarm a) {
        synchronized (this) {
            if( !mThrottleAlarms ) {
                return false;
            }
        }

        boolean block = false;

        if( a.alarmClock != null ) {

        } else if( a.packageName.startsWith("com.google.android.gms") ) {
            block = true;
        } else if( a.packageName.startsWith("com.google.android.wearable.app") ) {
            if( a.statsTag.contains("com.google.android.clockwork.TIME_SYNC") || 
                a.statsTag.contains("com.google.android.clockwork.TIME_ZONE_SYNC") ||
                a.statsTag.contains("com.google.android.clockwork.calendar.action.REFRESH")) {
                block = true;
            }
        } else if( ((a.flags&(AlarmManager.FLAG_ALLOW_WHILE_IDLE_UNRESTRICTED | AlarmManager.FLAG_WAKE_FROM_IDLE)) == 0)) {
            synchronized(mWhitelistSync) {
                if( Arrays.binarySearch(mDeviceIdleWhitelist, a.uid) < 0 ) {
                    block = true;
                }
            }
        }

        if( block ) {
            a.flags &= ~(AlarmManager.FLAG_WAKE_FROM_IDLE 
                    | AlarmManager.FLAG_ALLOW_WHILE_IDLE
                    | AlarmManager.FLAG_ALLOW_WHILE_IDLE_UNRESTRICTED);
            a.wakeup = false;
            return true;
        }
        return false;
    }


    private boolean restrictSystemIdleAlarm(AlarmManagerService.Alarm a) {
        synchronized (this) {
            if( !mThrottleAlarms ) {
                return false;
            }
        }

        boolean block = false;

        if( a.statsTag.contains("NETWORK_LINGER_COMPLETE") ||
            a.statsTag.contains("WifiConnectivityManager Restart Scan") ) {
            a.flags &= ~(AlarmManager.FLAG_WAKE_FROM_IDLE);
            a.wakeup = false;
            return true;
        } 


        if( a.statsTag.contains("*sync") ||
            a.statsTag.contains("*job") || 
            a.statsTag.contains("com.android.server.NetworkTimeUpdateService.action.POLL") ||
            a.statsTag.contains("APPWIDGET_UPDATE") ) {
            block = true;
        } 

        if( block ) {
            a.flags &= ~(AlarmManager.FLAG_WAKE_FROM_IDLE 
                    | AlarmManager.FLAG_ALLOW_WHILE_IDLE
                    | AlarmManager.FLAG_ALLOW_WHILE_IDLE_UNRESTRICTED);
            a.wakeup = false;
            return true;
        }

        return false;
    }

    public boolean adjustAlarm(AlarmManagerService.Alarm a) {
        if( !a.wakeup ) return false;
        synchronized (this) {
            if( !mThrottleAlarms ) {
                return false;
            }
        }

        if( a.statsTag.contains("com.qualcomm.qti.biometrics.fingerprint.service") ) {
            if( mQtiBiometricsInitialized ) {
                a.when += 25*60*1000;
                long whenElapsed = AlarmManagerService.convertToElapsed(a.when, a.type);
                a.whenElapsed = whenElapsed;
                a.maxWhenElapsed = whenElapsed;
                a.origWhen = a.when;
                if( DEBUG ) {
                    Slog.i(TAG,"AdjustAlarm: unrestricted:" + a.statsTag + ":" + a.toStringLong());
                }
                return true;
            } else {
                mQtiBiometricsInitialized = true;
            }
        }
        if( a.statsTag.contains("WifiConnectivityManager Schedule Periodic Scan Timer") ) {
            final long now = SystemClock.elapsedRealtime();
            if( (a.when - now)  < 15*60*1000 ) {
                a.when = a.whenElapsed = a.maxWhenElapsed = a.origWhen = now + 15*60*1000;
            } 
            if( DEBUG ) {
                Slog.i(TAG,"AdjustAlarm: unrestricted:" + a.statsTag + ":" + a.toStringLong());
            }
            return true;
        }
        return false;
    }

    public boolean isWakelockWhitelisted(PowerManagerService.WakeLock wakelock, int callingUid, String callingPackageName) {
        return false;
    }

    public boolean isWakelockBlacklisted(PowerManagerService.WakeLock wakelock, int callingUid, String callingPackageName) {
        return false;
    }

    public boolean isAlarmWhitelisted(String tag, int callingUid, String callingPackageName) {
        return false;
    }

    public boolean isAlarmBlacklisted(String tag, int callingUid, String callingPackageName) {
        return false;
    }

    
    public boolean isBroadcastFilterWhitelisted(BroadcastRecord r, BroadcastFilter filter) {
        //Slog.i(TAG,"isBroadcastFilterWhitelisted: from " + r.callerPackage + "/" + r.callingUid + "/" + r.callingPid + 
        //" to " + filter.receiverList.app + "/" + filter.receiverList.uid + "/" + filter.receiverList.pid + ">" + r.intent);

        return isBroadcastWhitelisted(r,null);
        //return false;
    }

    public boolean isBroadcastFilterBlacklisted(BroadcastRecord r,  BroadcastFilter filter) {
        //Slog.i(TAG,"isBroadcastFilterBlacklisted: from " + r.callerPackage + "/" + r.callingUid + "/" + r.callingPid + 
        //" to " + filter.receiverList.app + "/" + filter.receiverList.uid + "/" + filter.receiverList.pid + ">" + r.intent);

            if( DEBUG ) {
                Slog.i(TAG,"isBroadcastFilterBlacklisted: from " + r.callerPackage + "/" + r.callingUid + "/" + r.callingPid + " to " + r.intent);
            }
            if( !mDeviceIdleMode && !mApplyRestrictionsScreenOn ) {
                return false; 
            }
            if( filter == null || filter.receiverList == null ) {
                 Slog.i(TAG,"isBroadcastFilterBlacklisted: BroadcastFilter info NULL for " + r.callerPackage + "/" + r.callingUid + "/" + r.callingPid + " to " + r.intent);
                 return false;
            }
            if( isAppRestricted(filter.receiverList.uid, filter.packageName) == 2 ) return true;

            return false;

    }

    public boolean isBroadcastWhitelisted(BroadcastRecord r, ResolveInfo info) {
        if( DEBUG ) {
            Slog.i(TAG,"isBroadcastWhitelisted: from " + r.callerPackage + "/" + r.callingUid + "/" + r.callingPid + " to " + r.intent);
        }
        String act = r.intent.getAction();
        if( act == null ) return false;
        if( act.contains("com.google.android.c2dm") ) return true;
        if( act.startsWith("android.bluetooth") ) return true;

        if( act.equals("android.os.action.DEVICE_IDLE_MODE_CHANGED") ) return true;
    	if( act.equals("android.os.action.LIGHT_DEVICE_IDLE_MODE_CHANGED") ) return true;
    	if( act.equals("android.intent.action.SCREEN_OFF") ) return true;
    	if( act.equals("android.intent.action.SCREEN_ON") ) return true;
    	if( act.equals("android.intent.action.ACTION_POWER_CONNECTED") ) return true;
    	if( act.equals("android.intent.action.ACTION_POWER_DISCONNECTED") ) return true;

        if( act.startsWith("com.google.android.gms.auth") ) return true;
        if( act.contains("com.google.android.gcm.intent") ) return true;

        //if( !mDeviceIdleMode ) {
            if( act.startsWith("android.intent.action.DOWNLOAD") ) return true;
            if( act.startsWith("android.intent.action.PACKAGE") ) return true;
            if( act.startsWith("android.intent.action.INTENT_FILTER") ) return true;
            if( act.startsWith("com.android.vending.INTENT_PACKAGE") ) return true;
        //}

        return false;
    }

    public boolean isBroadcastBlacklisted(BroadcastRecord r, ResolveInfo info) {
            if( DEBUG ) {
                Slog.i(TAG,"isBroadcastBlacklisted: from " + r.callerPackage + "/" + r.callingUid + "/" + r.callingPid + " to " + r.intent);
            }
            if( !mDeviceIdleMode && !mApplyRestrictionsScreenOn ) {
                return false; 
            }
            if( info == null || info.activityInfo == null ) {
                 Slog.i(TAG,"isBroadcastBlacklisted: ResolveInfo info NULL for " + r.callerPackage + "/" + r.callingUid + "/" + r.callingPid + " to " + r.intent);
                 return false;
            }
            if( isAppRestricted(info.activityInfo.applicationInfo.uid, info.activityInfo.applicationInfo.packageName) == 2 ) return true;

            return false;
    }

    public boolean isServiceWhitelisted(ServiceRecord service, int callingUid, int callingPid, String callingPackageName, boolean isStarting) {
            if( DEBUG ) {
                Slog.i(TAG,"isServiceWhitelisted: from " + callingPackageName + "/" + callingUid + "/" + callingPid + " to " + service.name.getClassName());
            }
            if( !isGmsUid(service.appInfo.uid) ) return false;
            if( !mDeviceIdleMode && !mApplyRestrictionsScreenOn) {
                if( DEBUG ) {
                    Slog.i(TAG,"GmsService: unrestricted (not idle):" + service.name.getClassName());
                }
                return true;
            }

	    if( isGmsUid(service.appInfo.uid) && mExtremeSaverActive ) {
	        if( service.name.getClassName().contains(".gcm") ||
	    	    service.name.getClassName().contains(".fcm") ||
		    service.name.getClassName().contains(".deviceconnection") ||
		    service.name.getClassName().contains(".wearable") ||
		    service.name.getClassName().contains(".chimera") || 
		    service.name.getClassName().contains(".auth") ) {
			return false;
		} else {
		    return true;
		}
	    }

            for( String srv:mGoogleServicesIdleBlackListed ) {
                if( service.name.getClassName().equals(srv) ) {
                    return false;
                } 
            }
            if( DEBUG ) {
                Slog.i(TAG,"GmsService: unrestricted (wl):" + service.name.getClassName());
            }
            return true;
    }
    
    public boolean isServiceBlacklisted(ServiceRecord service, int callingUid, int callingPid, String callingPackageName, boolean isStarting) {
        if( DEBUG ) {
            Slog.i(TAG,"isServiceBlacklisted: from " + callingPackageName + "/" + callingUid + "/" + callingPid + " to " + service.name.getClassName());
        }

	    if( isGmsUid(service.appInfo.uid) && mExtremeSaverActive ) {
	        if( service.name.getClassName().contains(".gcm") ||
	    	    service.name.getClassName().contains(".fcm") ||
		    service.name.getClassName().contains(".deviceconnection") ||
		    service.name.getClassName().contains(".wearable") ||
		    service.name.getClassName().contains(".chimera") || 
		    service.name.getClassName().contains(".auth") ) {
			    return false;
		    } else {
		        return true;
		    }
	    }

        if( !mDeviceIdleMode && !mApplyRestrictionsScreenOn) {
            if( DEBUG ) {
                Slog.i(TAG,"GmsService: unblocked (not idle):" + service.name.getClassName());
            }
            return false; 
        }

        if( isAppRestricted(service.appInfo.uid, service.appInfo.packageName) == 2 ) return true;
        if( !isGmsUid(service.appInfo.uid) ) return false;
        if( mDeviceIdleMode ) {
            for( String srv:mGoogleServicesIdleBlackListed ) {
                if( service.name.getClassName().equals(srv) ) {
                    if( DEBUG ) {
                        Slog.i(TAG,"GmsService: restricted:" + service.name.getClassName());
                    }
                    return true;
                } 
            }
        }
        return false;
    }


    public int killByOOM(ProcessRecord app, ProcessRecord top_app, ProcessRecord home_app, ProcessRecord prev_app ) {

        if( app == top_app ) return 1;
        if( app == home_app ) return 1;
        if( app.info.uid < Process.FIRST_APPLICATION_UID  ) return 1;

    	if( isAppPackageWhitelisted(app.info.packageName) ) return 1;

        ApplicationProfileInfo appInfo = getAppProfileInternal(app.info.packageName);

        int restriction = isAppRestricted(appInfo, app.info.uid, app.info.packageName);
        
        if( restriction == 1 ) return 1;

        if( !mExtremeSaverActive ) {
            if( getWakefulnessLocked() == 1 ) return 0;
	    if( !mIdleAggressive ) return 0;
	    if( !mDeviceIdleMode ) return 0;
	}

        if( isGmsUid(app.info.uid) ) { 
	        if( (mDeviceIdleMode && mIdleAggressive) || mExtremeSaverActive ) {
	            ArrayList<ServiceRecord> stopping = null;
                try {
                    for (int is = app.services.size()-1;is >= 0; is--) {
                        ServiceRecord s = app.services.valueAt(is);
			            if( mExtremeSaverActive ) {
			                if( s.name.getClassName().contains(".gcm") ||
				                s.name.getClassName().contains(".fcm") ||
				                s.name.getClassName().contains(".deviceconnection") ||
				                s.name.getClassName().contains(".wearable") ||
				                s.name.getClassName().contains(".chimera") || 
				                s.name.getClassName().contains(".auth") ) {
			                } else {
                                if (stopping == null) {
                                    stopping = new ArrayList<>();
                                }
                                stopping.add(s);
			                }
			            } else {
			                if( !isServiceWhitelisted(s,app.info.uid,app.pid,app.info.packageName,false) ) {
                                if (stopping == null) {
                                    stopping = new ArrayList<>();
                                }
                                stopping.add(s);
            			    }
                        }
                    } 
	                if (stopping != null) {
        	            for (int i=stopping.size()-1; i>=0; i--) {
                	        ServiceRecord service = stopping.get(i);
    	                    service.delayed = false;
	                        service.stopIfKilled = true;
	                    
	                        try {
    	                        mActivityManagerService.mServices.bringDownServiceLocked(service);
	                        } catch(Exception e) {
	                        }
	                    }
        	        }
                } catch (Exception e) {
                }
	        }
	        return 1;
	    }

        
        if( restriction == 0 ) return 0;

        switch (app.curProcState) {
            case ActivityManager.PROCESS_STATE_BOUND_FOREGROUND_SERVICE:
            case ActivityManager.PROCESS_STATE_FOREGROUND_SERVICE:
            case ActivityManager.PROCESS_STATE_IMPORTANT_FOREGROUND:
            case ActivityManager.PROCESS_STATE_IMPORTANT_BACKGROUND:
            case ActivityManager.PROCESS_STATE_TRANSIENT_BACKGROUND:
            case ActivityManager.PROCESS_STATE_BACKUP:
                if( !mDeviceIdleMode && !mExtremeSaverActive ) break;
            case ActivityManager.PROCESS_STATE_HEAVY_WEIGHT:
            case ActivityManager.PROCESS_STATE_RECEIVER:
            case ActivityManager.PROCESS_STATE_SERVICE:
            case ActivityManager.PROCESS_STATE_CACHED_ACTIVITY:
            case ActivityManager.PROCESS_STATE_LAST_ACTIVITY:
            case ActivityManager.PROCESS_STATE_CACHED_ACTIVITY_CLIENT:
            case ActivityManager.PROCESS_STATE_CACHED_EMPTY:
                try {
                    for (int is = app.services.size()-1;is >= 0; is--) {
                        ServiceRecord s = app.services.valueAt(is);
                        s.stopIfKilled = true;
                    } 
                } catch (Exception e) {
                }
                return 2;
        }

        return 0;
    }

    public void noteRestrictionStatistics(boolean allowed, String type, String callerName, int callerUid, int callerPid, 
                            String calledName, int calledUid, int calledPid, String Tag) {
        final String recordName =  mDeviceIdleMode + "/" + type + "/" + callerName  + "->" + calledName + "/" + Tag;

        if( DEBUG ) {
            synchronized(mRestrictionStatistics) {
                RestrictionStatistics stat = mRestrictionStatistics.get(recordName);
                if( stat == null ) {
                    stat = new RestrictionStatistics(type, callerName, callerUid, callerPid,
                                                calledName, calledUid, calledPid, Tag);
                    mRestrictionStatistics.put(recordName, stat);
                }
                if( allowed ) stat.allowed++;
                else stat.blocked++;
                stat.deviceIdleMode = mDeviceIdleMode;
            }
            Slog.i(TAG,"noteRestrictionStatistics:" + allowed + ":" + recordName);
        }
    }

    public void logRestrictionStatistics() {
        if( DEBUG ) {
            synchronized(mRestrictionStatistics) {
                for(int i=0;i<mRestrictionStatistics.size();i++) {
                    RestrictionStatistics stat = mRestrictionStatistics.valueAt(i);
                    if( stat.allowed > 0 ) {
                        if( DEBUG ) {
                            Slog.i(TAG,"RestrictionStatistics: allowed :" + stat.getLog() + "; allowed=" + stat.allowed);
                        }
                    }
                }
    
                for(int i=0;i<mRestrictionStatistics.size();i++) {
                    RestrictionStatistics stat = mRestrictionStatistics.valueAt(i);
                    if( stat.blocked > 0 ) {
                        if( DEBUG ) {
                            Slog.i(TAG,"RestrictionStatistics: blocked :" + stat.getLog() + "; blocked=" + stat.blocked);
                        }
                    }
                }
            }
        }
    }

    public boolean isAppPackageWhitelisted(String packageName) {
	    if( packageName.startsWith("com.android.") ) return true;
	    if( packageName.startsWith("com.qualcomm.") ) return true;
	    if( packageName.startsWith("com.qti.") ) return true;
	    if( packageName.startsWith("org.codeaurora.ims") ) return true;
	    if( packageName.startsWith("ru.baikalos.") ) return true;
	    return false;
    }

    public int isAppRestricted(int uid, String packageName) {
        ApplicationProfileInfo info = getAppProfileLocked(packageName);
        return isAppRestricted(info,uid,packageName);
    }

    private int isAppRestricted(ApplicationProfileInfo info, int uid, String packageName) {
        synchronized(mWhitelistSync) {
            if( Arrays.binarySearch(mDeviceIdleWhitelist, uid) >= 0) return 1;
            if( Arrays.binarySearch(mDeviceIdleTempWhitelist, uid) >= 0) return 1;
        }

        if( info != null )
        {
            if( info.getAppOption(BaikalServiceManager.OP_PINNED) != 0 ) return 1;
	        switch(info.priority)
	        {
	            case BaikalServiceManager.PRIO_UNRESTRICTED:
		            return 1;
	            case BaikalServiceManager.PRIO_REGULAR:
	    	        if( mExtremeSaverActive ) return 2;
    	        case BaikalServiceManager.PRIO_GAME:
		            break;
	            case BaikalServiceManager.PRIO_RESTRICTED:
	            case BaikalServiceManager.PRIO_TOP_ONLY:
		            return 2;
            }
        }

        if( mAppOpsService == null ) return 0;
        final int mode = mAppOpsService.checkOperation(AppOpsManager.OP_RUN_ANY_IN_BACKGROUND,
                uid, packageName);

        if( mode != AppOpsManager.MODE_ALLOWED ) return 2;
	    return 0;
    }


    public void setLowPowerState(int data) {
	synchronized(this) {
	    setLowPowerStateLocked(data);
	}
    }

    public void setLowPowerStateLocked(int data) {
	boolean lowPowerState = data != 0;
	if( lowPowerState != mLowPowerState ) {
	    if( lowPowerState ) {
		if( mExtremeSaverEnabled && !mExtremeSaverActive ) setExtremeSaverState(true);
	    } else {
		if( mExtremeSaverActive ) setExtremeSaverState(false);
	    }
	}
    }

    private void setExtremeSaverState(boolean state) {
	mExtremeSaverActive = state;
    }

    
    public int getBrightnessOverrideLocked() {
        return mBrightnessOverride;
    }

    public boolean isReaderModeLocked() {
        return mIsReaderModeActive;
    }

    public boolean isExtremeSaverActiveLocked() {
        return mExtremeSaverActive;
    }

    public boolean isDeviceIdleModeLocked() {
        return mDeviceIdleMode;
    }

    public boolean isAggressiveDeviceIdleModeLocked() {
        return mDeviceIdleMode && mIdleAggressive;
    }

    public boolean isLightDeviceIdleModeLocked() {
        return mLightDeviceIdleMode;
    }

    public void setDeviceIdleModeLocked(boolean mode) {
        if( mDeviceIdleMode != mode ) {
            if( DEBUG ) {
                Slog.i(TAG,"setDeviceIdleModeLocked: " + mode);
            }
            mDeviceIdleMode = mode;
            Message msg = mHandler.obtainMessage(MESSAGE_DEVICE_IDLE_CHANGED);
            mHandler.sendMessage(msg);
            logRestrictionStatistics();
        }
    }

    public void setLightDeviceIdleModeLocked(boolean mode) {
        if( mLightDeviceIdleMode != mode ) {
            if( DEBUG ) {
                Slog.i(TAG,"setLightDeviceIdleModeLocked: " + mode);
            }
            mLightDeviceIdleMode = mode;
            Message msg = mHandler.obtainMessage(MESSAGE_LIGHT_DEVICE_IDLE_CHANGED);
            mHandler.sendMessage(msg);
        }
    }

    private void onDeviceIdleModeChanged() {
        mActivityManagerService.setDeviceIdleMode(mDeviceIdleMode);
    }

    private void onLightDeviceIdleModeChanged() {
    }


    private void updateSleepStateLocked() {
	final int wakefulness = getWakefulnessLocked();
	if( wakefulness != 1 && !mSleeping ) {
	    mSleeping = true;
	    onSleepStateChangedLocked(mSleeping);
	} else if(  wakefulness == 1 && mSleeping ) {
	    mSleeping = false;
	    onSleepStateChangedLocked(mSleeping);
	}
    }
	

    public void setWakefulnessLocked(int wakefulness, int reason) {
        mWakefulness = wakefulness;
        mWakefulnessReason = reason;
        wakefulnessChanged();
    }

    public int getWakefulnessLocked() {
        return mWakefulness;
    }

    public int getWakefulnessReasonLocked() {
        return mWakefulnessReason;
    }


    public String lastWakeupReasonLocked() {
        return mLastWakeupReason;
    }

    public void setLastWakeupReasonLocked(String reason) {
        mLastWakeupReason = reason;
    }

    void goToSleep() {
        if( mPowerManager != null ) {
            mPowerManager.goToSleep(SystemClock.uptimeMillis(), PowerManager.GO_TO_SLEEP_REASON_POWER_BUTTON, 0);
        }
    }

    void wakeUp() {
        if( mPowerManager != null ) {
            mPowerManager.wakeUp(SystemClock.uptimeMillis(), "android.policy:LID");
        }
    }

    private void onWakefulnessChanged() {
	updateSleepStateLocked();
    }

    private String awakePerformanceProfile = "default"; 
    private String awakeThermalProfile = "default"; 

    private void onSleepStateChangedLocked(boolean sleeping) {
        if( DEBUG_PROFILE ) {
            Slog.i(TAG,"onSleepStateChangedLocked");
        }

        synchronized(mCurrentProfileSync) {
            if( getWakefulnessLocked() != 1 ) {
                awakePerformanceProfile = mCurrentPerformanceProfile;
                awakeThermalProfile = mCurrentThermalProfile;
                setPerformanceProfile("battery");
                setThermalProfile("cool");
            } else {
                setPerformanceProfile(awakePerformanceProfile);
                setThermalProfile(awakeThermalProfile);
            }
        }
    }


    int currentUid=-1, currentWakefulness=-1;
    int mTopAppUid;
    String mTopAppPackageName;
    public void topAppChanged(ActivityRecord act) {
        mTopAppUid = -1;
        mTopAppPackageName = null;
        if( act != null ) {
            mTopAppUid = act.info.applicationInfo.uid;
            mTopAppPackageName = act.packageName;
        }

        mHandler.sendEmptyMessage(MESSAGE_TOP_APP_CHANGED);
    }

    private void onTopAppChanged() {
        onTopAppChangedLocked();
    }

    
    private void onTopAppChangedLocked() {

        currentWakefulness = getWakefulnessLocked();
        if( currentWakefulness != 1 ) {
            return;
        }

        if( currentUid == mTopAppUid && currentWakefulness == getWakefulnessLocked() ) {
            return;
        }
   
        if( mTopAppUid == -1 ) {
            if( DEBUG_PROFILE ) {
                Slog.i(TAG,"topAppChanged: empty top activity");
            }
            if( currentWakefulness == 1 ) {
                setPerformanceProfile("default");
                setThermalProfile("default");
            }
            currentUid = -1;
            currentWakefulness = getWakefulnessLocked();
            return;
        }


        currentUid = mTopAppUid;    

        if( DEBUG_PROFILE ) {
            Slog.i(TAG,"topAppChanged: top activity=" + mTopAppPackageName);
        }

        ApplicationProfileInfo info = null;
        synchronized(mProfileSync) {
            info = getAppProfileLocked(mTopAppPackageName);
        }

        if( info == null ) {
            if( DEBUG_PROFILE ) {
                Slog.i(TAG,"topAppChanged: default top activity");
            }
            setBrightnessOverrideLocked(0);
            setPerformanceProfile("default");
            setThermalProfile("default");
            return;   
        }

        setPerformanceProfile(info.perfProfile);
        setThermalProfile(info.thermProfile);
        setBrightnessOverrideLocked(info.brightness);
    }

    private String mCurrentPerformanceProfile = "none";
    private void setPerformanceProfile(String profile) {

        if( DEBUG_PROFILE ) {
            Slog.i(TAG,"setPerformanceProfile: profile=" + profile);
        }

        synchronized(mCurrentPerformanceProfile) {
            if ( !mCurrentPerformanceProfile.equals(profile) ) {
                if( profile.equals("reader") ) {
                    if( DEBUG_PROFILE ) {
                        Slog.i(TAG,"setPerformanceProfile: reader mode activated");
                    }
                    updateReaderModeLocked(true);
                } else {
                    updateReaderModeLocked(false);
                }
                mCurrentPerformanceProfile = profile;
                setPerformanceProfileInternal(profile);
            } else {
                if( DEBUG_PROFILE ) {
                    Slog.i(TAG,"setPerformanceProfile: ignore already active profile=" + profile);
                }   
            }
        }
    }

    void updateReaderModeLocked(boolean mode) {
        if( mode != mIsReaderModeActive ) {
            mIsReaderModeActive = mode;
            if( mode ) {
                //mContext.sendBroadcast(mReaderOnIntent);
            } else {
                //mContext.sendBroadcast(mReaderOffIntent);
            }
        }
    }

/*
    public static final int SCREEN_BRIGHTNESS_DEFAULT = 0;
    public static final int SCREEN_BRIGHTNESS_10 = 1;
    public static final int SCREEN_BRIGHTNESS_20 = 2;
    public static final int SCREEN_BRIGHTNESS_30 = 3;
    public static final int SCREEN_BRIGHTNESS_40 = 4;
    public static final int SCREEN_BRIGHTNESS_50 = 5;
    public static final int SCREEN_BRIGHTNESS_60 = 6;
    public static final int SCREEN_BRIGHTNESS_70 = 7;
    public static final int SCREEN_BRIGHTNESS_80 = 8;
    public static final int SCREEN_BRIGHTNESS_90 = 9;
    public static final int SCREEN_BRIGHTNESS_AUTO_LOW = 10;
    public static final int SCREEN_BRIGHTNESS_FULL = 11;
*/

    void setBrightnessOverrideLocked(int brightness) {
    switch( brightness ) {
        case BaikalServiceManager.SCREEN_BRIGHTNESS_DEFAULT:
            mBrightnessOverride = -1;
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_AUTO_LOW:
            mBrightnessOverride = -2;
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_AUTO_QUARTER:
            mBrightnessOverride = -3;
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_FULL:
            mBrightnessOverride = PowerManager.BRIGHTNESS_ON;
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_10:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 2)/100; // 3
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_20:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 3)/100; // 4
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_30:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 4)/100; // 6
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_40:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 6)/100; // 8
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_50:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 8)/100; // 10
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_60:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 15)/100; // 20
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_70:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 30)/100; // 35
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_80:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 60)/100; // 60
            break;
        case BaikalServiceManager.SCREEN_BRIGHTNESS_90:
            mBrightnessOverride = (PowerManager.BRIGHTNESS_ON * 80)/100; // 100
            break;
        default:
            mBrightnessOverride = -1;
        }
        //mContext.sendBroadcast(mBrightnessOverrideIntent);
        Message msg = mHandler.obtainMessage(MESSAGE_BRIGHTNESS_CHANGED);
        mHandler.sendMessage(msg);
}

    private void onBrightnessChanged() {
        mContext.sendBroadcast(mBrightnessOverrideIntent);
    }

    private String mCurrentThermalProfile = "none";
    private void setThermalProfile(String profile) {

        if( DEBUG_PROFILE ) {
            Slog.i(TAG,"setThermalProfile: profile=" + profile);
        }

        synchronized(mCurrentThermalProfile) {
            if ( !mCurrentThermalProfile.equals(profile) ) {
                mCurrentThermalProfile = profile;
                SystemPropertiesSet("baikal.therm.profile","");
                SystemPropertiesSet("baikal.therm.profile",profile);
            } else {
                if( DEBUG_PROFILE ) {
                    Slog.i(TAG,"setThermalProfile: ignore already active profile=" + profile);
                }   
            }
        }
    }
  

    private void setPerformanceProfileInternal(String profile)
    {
        if( isBaikalPerformanceProfiles() ) {
            if( DEBUG_PROFILE ) {
                Slog.i(TAG,"setPerformanceProfileInternal: set baikal profile=" + profile);
            }   
            SystemPropertiesSet("baikal.perf.profile","");
            SystemPropertiesSet("baikal.perf.profile",profile);
        } 
        else if( isSpectrumProfiles() ) {
            if( DEBUG_PROFILE ) {
                Slog.i(TAG,"setPerformanceProfileInternal: set spectrum profile=" + profile);
            }   
            SystemPropertiesSet("baikal.perf.profile","");
            SystemPropertiesSet("persist.spectrum.profile",mapBaikalToSpectrumProfile(profile, true));
        }
        else {
            if( DEBUG_PROFILE ) {
                Slog.i(TAG,"setPerformanceProfileInternal: no perf engine defined profile=" + profile);
            }   
        }
    }

    private boolean isBaikalPerformanceProfiles() {
        return (SystemProperties.get("baikal.eng.perf","0")).equals("1");
    }

    private boolean isSpectrumProfiles() {
        return (SystemProperties.get("spectrum.support","0")).equals("1");
    }

    private String mapBaikalToSpectrumProfile(String profile, boolean defmap) {

        Slog.i(TAG,"spectrum: profile=" + profile);
        if(profile.equals("balance")) {
                return "0";
        } else if(profile.equals("performance")) {
                return "1";
        } else if(profile.equals("battery")) {
                return "2";
        } else if(profile.equals("gaming")) {
                return "3";
        } else if(profile.equals("reader")) {
                return "2";
        } else {
            if( defmap ) {
                return mapBaikalToSpectrumProfile(SystemProperties.get("persist.baikal.perf.default","balance"), false);
            } else {
                return "0";
            }
        }
    }

    private void SystemPropertiesSet(String key, String value) {
        if( DEBUG ) {
            Slog.d(TAG, "SystemProperties.set("+key+","+value+")");
        }
        try {
            SystemProperties.set(key,value);
        }
        catch( Exception e ) {
            Slog.e(TAG, "SystemPropertiesSet: unable to set property "+key+" to "+value);
        }
    }

    private ApplicationProfileInfo getAppProfileInternal(String packageName) {
        synchronized(mProfileSync) {
            if( mApplicationProfiles.containsKey(packageName) ) {
                return mApplicationProfiles.get(packageName);
            }
        }
        if( DEBUG ) {
            Slog.i(TAG,"getAppProfileLocked package not found package=" + packageName);
        }
        return null;
    }


    private ApplicationProfileInfo getOrCreateAppProfileLocked(String packageName) {
        if( mApplicationProfiles.containsKey(packageName) ) {
            return mApplicationProfiles.get(packageName);
        }
        ApplicationProfileInfo info = new ApplicationProfileInfo();
        info.packageName = packageName;
        mApplicationProfiles.put(packageName, info);
        if( DEBUG ) {
           Slog.i(TAG,"getAppProfileLocked created profile for package=" + packageName);
        }
        return info;
    }


    private ApplicationProfileInfo getAppProfileLocked(String packageName) {
        if( mApplicationProfiles.containsKey(packageName) ) {
            return mApplicationProfiles.get(packageName);
        }
        if( DEBUG ) {
            Slog.i(TAG,"getAppProfileLocked package not found package=" + packageName);
        }
        return null;
    }

    private void setAppProfileLocked(ApplicationProfileInfo info) {
        if( DEBUG ) {
            Slog.i(TAG,"setAppProfileLocked set info for package=" + info.packageName);
        }
        mApplicationProfiles.put(info.packageName, info);
        writeConfigFileLocked();
    }


    public String getAppPerfProfileInternal(String packageName) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getAppProfileLocked(packageName);
            if( info != null ) {
                if( DEBUG ) {
                    Slog.i(TAG,"getAppPerfProfile for package=" + packageName + ", perfProfile=" + info.perfProfile);
                }
                return info.perfProfile;
            }
        }
        if( DEBUG ) {
            Slog.i(TAG,"getAppPerfProfile default for package=" + packageName);
        }
        return "default";

    }
    public String getAppThermProfileInternal(String packageName) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getAppProfileLocked(packageName);
            if( info != null ) {
                if( DEBUG ) {
                    Slog.i(TAG,"getAppThermProfile for package=" + packageName + ", perfProfile=" + info.thermProfile);
                }
                return info.thermProfile;
            }
        }
        if( DEBUG ) {
            Slog.i(TAG,"getAppThermProfile default for package=" + packageName);
        }
        return "default";
    }
    public void setAppPerfProfileInternal(String packageName, String profile) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getOrCreateAppProfileLocked(packageName);
            info.perfProfile = profile;
            setAppProfileLocked(info);
        }
        if( DEBUG ) {
            Slog.i(TAG,"setAppPerfProfile package=" + packageName + ", profile=" + profile);
        }
    }

    public void setAppThermProfileInternal(String packageName, String profile) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getOrCreateAppProfileLocked(packageName);
            info.thermProfile = profile;
            setAppProfileLocked(info);
        }
        if( DEBUG ) {
            Slog.i(TAG,"setAppThermProfile package=" + packageName + ", profile=" + profile);
        }
    }
    
    public boolean isAppRestrictedProfileInternal(String packageName) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getAppProfileLocked(packageName);
            if( info != null ) return  info.isRestricted;
        }
        if( DEBUG ) {
            Slog.i(TAG,"getAppThermProfile package=" + packageName);
        }
        return false;
    }

    public void setAppRestrictedProfileInternal(String packageName, boolean restricted) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getOrCreateAppProfileLocked(packageName);
            info.isRestricted = restricted;
            setAppProfileLocked(info);
        }
    }

    public int getAppPriorityInternal(String packageName) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getAppProfileLocked(packageName);
            if( info != null ) return  info.priority;
        }
        if( DEBUG ) {
            Slog.i(TAG,"getAppPriority package=" + packageName);
        }
        return 0;
    }

    public int setAppPriorityInternal(String packageName, int priority) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getOrCreateAppProfileLocked(packageName);
            if( priority == -1 ) {
                info.isRestricted = true;
            } else {
                info.isRestricted = false;
                info.priority = priority;
            }
            setAppProfileLocked(info);
        }
        if( DEBUG ) {
            Slog.i(TAG,"setAppPriority package=" + packageName + ", priority=" + priority);
        }
        return 0;
    }

    public int getAppBrightnessInternal(String packageName) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getAppProfileLocked(packageName);
            if( info != null ) {
                Slog.i(TAG,"getAppBrightness package=" + packageName + ", brightness=" + info.brightness);
                return  info.brightness;
            }
        }
        //if( DEBUG ) {
            Slog.i(TAG,"getAppBrightness package=" + packageName);
        //}
        return 0;
    }

    public int setAppBrightnessInternal(String packageName, int brightness) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getOrCreateAppProfileLocked(packageName);
            info.brightness = brightness;
            setAppProfileLocked(info);
        }
        //if( DEBUG ) {
            Slog.i(TAG,"setAppBrightness package=" + packageName + ", brightness=" + brightness);
        //}
        return 0;
    }

    public String getDefaultPerfProfileInternal() {
        return SystemProperties.get("persist.baikal.perf.default","balance");
    }

    public void setDefaultPerfProfileInternal(String profile) {
        SystemPropertiesSet("persist.baikal.perf.default",profile);
        SystemPropertiesSet("baikal.perf.profile","");
        SystemPropertiesSet("baikal.perf.profile",mCurrentPerformanceProfile);
    }

    public String getDefaultThermProfileInternal() {
        return SystemProperties.get("persist.baikal.therm.default","balance");
    }

    public void setDefaultThermProfileInternal(String profile) {
        SystemPropertiesSet("persist.baikal.therm.default",profile);
        SystemPropertiesSet("baikal.therm.profile","");
        SystemPropertiesSet("baikal.therm.profile",mCurrentThermalProfile);
    }


    public void setAppOptionInternal(String packageName, int option, int value) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getOrCreateAppProfileLocked(packageName);
            info.setAppOption(option,value);
            setAppProfileLocked(info);
        }
        if( DEBUG ) {
            Slog.i(TAG,"setAppOptionInternal package=" + packageName + ", option=" + option + ", value=" + value);
        }

    }

    public int getAppOptionInternal(String packageName, int option) {
        synchronized(mProfileSync) {
            ApplicationProfileInfo info = getAppProfileLocked(packageName);
            if( info != null ) return  info.getAppOption(option);
        }
        if( DEBUG ) {
            Slog.i(TAG,"getAppOption package=" + packageName);
        }
        return 0;
        
    }


    void readConfigFileLocked() {
        Slog.d(TAG, "Reading config from " + mAppsConfigFile.getBaseFile());
        mApplicationProfiles.clear();
        FileInputStream stream;
        try {
            stream = mAppsConfigFile.openRead();
        } catch (FileNotFoundException e) {
            Slog.d(TAG, "Reading config failed! ", e);
            return;
        }
        try {
            XmlPullParser parser = Xml.newPullParser();
            parser.setInput(stream, StandardCharsets.UTF_8.name());
            readConfigFileLocked(parser);
        } catch (XmlPullParserException e) {
            Slog.d(TAG, "Parsing config failed! ", e);
        } finally {
            try {
                stream.close();
            } catch (IOException e) {
            }
        }
    }

    private void readConfigFileLocked(XmlPullParser parser) {
        final PackageManager pm = getContext().getPackageManager();

        try {
            int type;
            while ((type = parser.next()) != XmlPullParser.START_TAG
                    && type != XmlPullParser.END_DOCUMENT) {
                ;
            }

            if (type != XmlPullParser.START_TAG) {
                throw new IllegalStateException("no start tag found");
            }

            int outerDepth = parser.getDepth();
            while ((type = parser.next()) != XmlPullParser.END_DOCUMENT
                    && (type != XmlPullParser.END_TAG || parser.getDepth() > outerDepth)) {
                if (type == XmlPullParser.END_TAG || type == XmlPullParser.TEXT) {
                    continue;
                }

                String tagName = parser.getName();
                switch (tagName) {
                    case "app":
                        ApplicationProfileInfo info = new ApplicationProfileInfo();
                        int count = parser.getAttributeCount();
                        for(int j=0;j<count;j++) {
                            String attrName = parser.getAttributeName(j);
                            String attrValue = parser.getAttributeValue(j);
                            if( attrName.equals("pn") ) {
                                info.packageName = attrValue;
                            } else if( attrName.equals("pp") ) {
                                info.perfProfile = attrValue;
                            } else if( attrName.equals("tp") ) {
                                info.thermProfile = attrValue;
                            } else if( attrName.equals("rs") ) {
                                info.isRestricted = Boolean.parseBoolean(attrValue);
                            } else if( attrName.equals("pr") ) {
                                info.priority = Integer.parseInt(attrValue);
                            } else if( attrName.equals("br") ) {
                                info.brightness = Integer.parseInt(attrValue);
                            } else if( attrName.startsWith("op_") ) {
                                int opt = Integer.parseInt(attrName.substring(3));
                                int value = Integer.parseInt(attrValue);
                                info.setAppOption(opt,value);
                            }
                        }
                        setAppProfileLocked(info);
                        break;
                    default:
                        Slog.w(TAG, "Unknown element under <config>: "
                                + parser.getName());
                        XmlUtils.skipCurrentTag(parser);
                        break;
                }
            }

        } catch (IllegalStateException e) {
            Slog.w(TAG, "Failed parsing config " + e);
        } catch (NullPointerException e) {
            Slog.w(TAG, "Failed parsing config " + e);
        } catch (NumberFormatException e) {
            Slog.w(TAG, "Failed parsing config " + e);
        } catch (XmlPullParserException e) {
            Slog.w(TAG, "Failed parsing config " + e);
        } catch (IOException e) {
            Slog.w(TAG, "Failed parsing config " + e);
        } catch (IndexOutOfBoundsException e) {
            Slog.w(TAG, "Failed parsing config " + e);
        }
    }

    void writeConfigFileLocked() {
        mHandler.removeMessages(MESSAGE_WRITE_CONFIG);
        mHandler.sendEmptyMessageDelayed(MESSAGE_WRITE_CONFIG, 5000);
    }

    void handleWriteConfigFile() {
        final ByteArrayOutputStream memStream = new ByteArrayOutputStream();

        try {
            synchronized (mProfileSync) {
                XmlSerializer out = new FastXmlSerializer();
                out.setOutput(memStream, StandardCharsets.UTF_8.name());
                writeConfigFileLocked(out);
            }
        } catch (IOException e) {
        }

        synchronized (mAppsConfigFile) {
            FileOutputStream stream = null;
            try {
                stream = mAppsConfigFile.startWrite();
                memStream.writeTo(stream);
                stream.flush();
                FileUtils.sync(stream);
                stream.close();
                mAppsConfigFile.finishWrite(stream);
            } catch (IOException e) {
                Slog.w(TAG, "Error writing config file", e);
                mAppsConfigFile.failWrite(stream);
            }
        }
    }

    void writeConfigFileLocked(XmlSerializer out) throws IOException {
        out.startDocument(null, true);
        out.startTag(null, "config");
        for (int i=0; i<mApplicationProfiles.size(); i++) {
            ApplicationProfileInfo info = mApplicationProfiles.valueAt(i);
            out.startTag(null, "app");
                out.attribute(null, "pn",info.packageName);
                out.attribute(null, "pp",info.perfProfile);
                out.attribute(null, "tp",info.thermProfile);
                out.attribute(null, "rs",Boolean.toString(info.isRestricted));
                out.attribute(null, "pr",Integer.toString(info.priority));
                out.attribute(null, "br",Integer.toString(info.brightness));

                ArrayMap<Integer, Integer> appOps = info.getOpArray();
                for (int j = 0; j < appOps.size(); j++) {
                    Integer key = appOps.keyAt(j);
                    Integer value = appOps.valueAt(j);
                    String attrName = "op_" + Integer.toString(key);
                    out.attribute(null, attrName,Integer.toString(value));
                }
                
            out.endTag(null, "app");
        }
        out.endTag(null, "config");
        out.endDocument();
    }


    private void toggleTorch(boolean on) {
        //cancelTorchOff();
        final boolean origEnabled = mTorchEnabled;
        try {
            final String rearFlashCameraId = getRearFlashCameraId();
            if (rearFlashCameraId != null) {
                mCameraManager.setTorchMode(rearFlashCameraId, on);
                mTorchEnabled = on;
            }
        } catch (CameraAccessException e) {
            // Ignore
        }
    }


    private String getRearFlashCameraId() throws CameraAccessException {
        if (mRearFlashCameraId != null) return mRearFlashCameraId;
        for (final String id : mCameraManager.getCameraIdList()) {
            CameraCharacteristics c = mCameraManager.getCameraCharacteristics(id);
            boolean flashAvailable = c.get(CameraCharacteristics.FLASH_INFO_AVAILABLE);
            int lensDirection = c.get(CameraCharacteristics.LENS_FACING);
            if (flashAvailable && lensDirection == CameraCharacteristics.LENS_FACING_BACK) {
                mRearFlashCameraId = id;
            }
        }
        return mRearFlashCameraId;
    }
    private class TorchModeCallback extends CameraManager.TorchCallback {
        @Override
        public void onTorchModeChanged(String cameraId, boolean enabled) {
            //if (!cameraId.equals(mRearFlashCameraId)) return;
            //mTorchEnabled = enabled;
            //if (!mTorchEnabled) {
            //    cancelTorchOff();
            //}
        }
        @Override
        public void onTorchModeUnavailable(String cameraId) {
            //if (!cameraId.equals(mRearFlashCameraId)) return;
            //mTorchEnabled = false;
            //cancelTorchOff();
        }
    }

    private static Object mStaticMembersLock = new Object();

    private static boolean mHideIdleFromGms;
    private static boolean mUnrestrictedNetwork;
	
    private static int mGmsUid = -1;
    static void setGmsUid(int uid) {
        synchronized(mStaticMembersLock) {
            mGmsUid = uid;
        }
    }


    public static boolean isGmsUid(int uid) {
        synchronized(mStaticMembersLock) {
            return mGmsUid == uid;
        }
    }

    public static boolean isGmsAppid(int appid) {
        synchronized(mStaticMembersLock) {
            return UserHandle.getAppId(mGmsUid) == appid;
        }
    }

    public static int gmsAppid() {
        synchronized(mStaticMembersLock) {
            return UserHandle.getAppId(mGmsUid);
        }
    }

    public static int gmsUid() {
        synchronized(mStaticMembersLock) {
            return mGmsUid;
        }
    }

    public static boolean gmsHideIdle() {
        synchronized(mStaticMembersLock) {
   	    //Slog.i(TAG, "gmsHideIdle=" + mHideIdleFromGms); 
            return mHideIdleFromGms;
        }
    }

    public static boolean idleUnrestrictedNetwork() {
        synchronized(mStaticMembersLock) {
   	    //Slog.i(TAG, "idleUnrestrictedNetwork=" + mUnrestrictedNetwork); 
            return mUnrestrictedNetwork;
        }
    }

    final class RestrictionStatistics {
        public String type;
        public String callerName;
        public int callerUid;
        public int callerPid;
        public String calledName;
        public int calledUid;
        public int calledPid;
        public String RecordName;
        public String Tag;
        public int allowed;
        public int blocked;
        public boolean deviceIdleMode;

        public RestrictionStatistics(String _type, String _callerName, int _callerUid, int _callerPid, 
            String _calledName, int _calledUid, int _calledPid, String _Tag) {
            type = _type;
            callerName = _callerName;
            callerUid = _callerUid;
            callerPid = _callerPid;
            calledName = _calledName;
            calledUid = _calledUid;
            calledPid = _calledPid;
            Tag = _Tag;
        }

        public String getLog() {
            String log = deviceIdleMode + "/" + type + "/" + callerName + "->" + calledName + "/" + Tag; 
            return log;
        }
    }

    final class ProximityService {
        // The proximity sensor, or null if not available or needed.
        private Sensor mProximitySensor;
        private float  mProximityThreshold;
        private boolean mProximitySensorEnabled;

        private long proximityPositiveTime;
        private long proximityNegativeTime;
        private long proximityClickStart;
        private long proximityClickCount;


        private final SensorEventListener mProximitySensorListener = new SensorEventListener() {
            @Override
            public void onSensorChanged(SensorEvent event) {
                if (mProximitySensorEnabled) {
                    final long time = SystemClock.uptimeMillis();
                    final float distance = event.values[0];
                    boolean positive = distance >= 0.0f && distance < mProximityThreshold;
                    handleProximitySensorEvent(time, positive);
                }
            }

            @Override
            public void onAccuracyChanged(Sensor sensor, int accuracy) {
                // Not used.
            }
        };


        void Initialize() {
            mProximitySensor = mSensorManager.getDefaultSensor(Sensor.TYPE_PROXIMITY,true);
            if( mProximitySensor != null ) { 
                mProximityThreshold = mProximitySensor.getMaximumRange();
            }
            if( DEBUG ) {
                Slog.i(TAG,"Proximity Initialize: sensor=" + mProximitySensor);
            }
        }

        void setProximitySensorEnabled(boolean enable) {
            if( DEBUG ) {
                Slog.i(TAG,"setProximitySensorEnabled: enable=" + enable);
            }
            if( mProximitySensor == null ) return; 
            if (enable) {
                if (!mProximitySensorEnabled) {
                    mProximitySensorEnabled = true;
                    mSensorManager.registerListener(mProximitySensorListener, mProximitySensor,
                        SensorManager.SENSOR_DELAY_FASTEST, 1000000);
                }
            } else {
                if (mProximitySensorEnabled) {
                    mProximitySensorEnabled = false;
                    mSensorManager.unregisterListener(mProximitySensorListener);
                }
            }
        }

        private void handleProximitySensorEvent(long time, boolean positive) {
            if (mProximitySensorEnabled) {

                boolean isInteractive = mPowerManager.isInteractive();

                if( DEBUG ) {
                    Slog.i(TAG,"handleProximitySensorEvent: value=" + positive + ", time=" + time);
                }

                if( (!mProximityServiceWakeupEnabled && !isInteractive) ||
                    (!mProximityServiceSleepEnabled && isInteractive) ) {
                    AcquireWakelock(true);
                    return;
                }

                AcquireWakelock(false);

                //final long now = SystemClock.elapsedRealtime();
                if( positive == false ) {
                    proximityNegativeTime = time;
                    if( (time - proximityClickStart) < 2500 ) {
                        proximityClickCount++;
                        if( DEBUG ) {
                            Slog.i(TAG,"handleProximitySensorEvent: open <2000 :" + (time-proximityClickStart) + ":" + proximityClickCount);
                        }
                        if( proximityClickCount == 2 ) {
                            handleWakeup(isInteractive);
                        }
                    } else {
                        if( DEBUG ) {
                            Slog.i(TAG,"handleProximitySensorEvent: open >2000 :" + (time-proximityClickStart) + ":0");
                        }
                        proximityClickCount = 0;
                    }
                } else {
                    proximityPositiveTime = time;
                    if( (time - proximityClickStart) > 2500 ) {
                        proximityClickStart = time;
                        proximityClickCount = 0;
                        if( DEBUG ) {
                            Slog.i(TAG,"handleProximitySensorEvent: closed > 2000 :" + (time-proximityClickStart) + ":0");
                        }
                    } else {
                        if( DEBUG ) {
                            Slog.i(TAG,"handleProximitySensorEvent: closed < 2000 :" + (time-proximityClickStart) + ":" + proximityClickCount);
                        }
                    }
                }
            }
        }

        void handleWakeup(boolean interactive) {
            if( DEBUG ) {
                Slog.i(TAG,"handleProximitySensorWakeup()");
            }
            if( mPowerManager != null && interactive ) {
                goToSleep();
            } else {
                wakeUp();
            }
        }
        
        void handleProximityTimeout() {
            ReleaseWakelock();
        }

        void setProximityTimeout(boolean wakeonly) {
            final long timeout = wakeonly?500:3000; 
            mHandler.removeMessages(MESSAGE_PROXIMITY_WAKELOCK_TIMEOUT);
            Message msg = mHandler.obtainMessage(MESSAGE_PROXIMITY_WAKELOCK_TIMEOUT);
            mHandler.sendMessageDelayed(msg,timeout);
        }

        private void ReleaseWakelock() {
            if (mProximityWakeLock.isHeld()) {
                if( DEBUG ) {
                    Slog.i(TAG,"ProximitySensor: ReleaseWakelock()");
                }
                mProximityWakeLock.release();
            }
        }

        private void AcquireWakelock(boolean wakeonly) {
            setProximityTimeout(wakeonly);
            if (!mProximityWakeLock.isHeld()) {
                if( DEBUG ) {
                    Slog.i(TAG,"ProximitySensor: AcquireWakelock()");
                }
                mProximityWakeLock.acquire();
            }
        }

    }

    final class HallSensorService {
        // The hall sensor, or null if not available or needed.
        private Sensor mHallSensor;
        private boolean mHallSensorEnabled;

        private final SensorEventListener mHallSensorListener = new SensorEventListener() {
            @Override
            public void onSensorChanged(SensorEvent event) {
                if (mHallSensorEnabled) {
                    final long time = SystemClock.uptimeMillis();
                    final float distance = event.values[0];
                    boolean positive = distance > 0.0f;
                    handleHallSensorEvent(time, positive);
                }
            }

            @Override
            public void onAccuracyChanged(Sensor sensor, int accuracy) {
                // Not used.
            }
        };


        void Initialize() {
            mHallSensor = mSensorManager.getDefaultSensor(SENSOR_HALL_TYPE, true);
            if( DEBUG ) {
                Slog.i(TAG,"Hall Initialize: sensor=" + mHallSensor);
            }
        }

        void setHallSensorEnabled(boolean enable) {
            if( DEBUG ) {
                Slog.i(TAG,"setHallSensorEnabled: enable=" + enable);
            }
            if( mHallSensor == null ) return; 
            if (enable) {
                if (!mHallSensorEnabled) {
                    mHallSensorEnabled = true;
                    mSensorManager.registerListener(mHallSensorListener, mHallSensor,
                        SensorManager.SENSOR_DELAY_FASTEST, 1000000);
                }
            } else {
                if (mHallSensorEnabled) {
                    mHallSensorEnabled = false;
                    mSensorManager.unregisterListener(mHallSensorListener);
                }
            }
        }

        private void handleHallSensorEvent(long time, boolean positive) {
            if (mHallSensorEnabled) {
                if( DEBUG ) {
                    Slog.i(TAG,"handleHallSensorEvent: value=" + positive + ", time=" + time);
                }
                handleWakeup(!positive);
            }
        }

        void handleWakeup(boolean wakeup) {
            if( DEBUG ) {
                Slog.i(TAG,"handleHallSensorWakeup()");
            }
            if( wakeup ) {
                wakeUp();
            } else {
                goToSleep();
            }
        }
    }


    private class MyHandlerThread extends HandlerThread {

        Handler handler;

        public MyHandlerThread() {
            super("baikal.handler", android.os.Process.THREAD_PRIORITY_FOREGROUND);
        }
    }


    BinderService mBinderService;

    private final class BinderService extends IBaikalServiceController.Stub {

        @Override public String getAppPerfProfile(String packageName) {
            long ident = Binder.clearCallingIdentity();
            try {
                return getAppPerfProfileInternal(packageName);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }
        @Override public String getAppThermProfile(String packageName) {
            long ident = Binder.clearCallingIdentity();
            try {
                return getAppThermProfileInternal(packageName);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }
        @Override public void setAppPerfProfile(String packageName, String profile) {
            long ident = Binder.clearCallingIdentity();
            try {
                setAppPerfProfileInternal(packageName,profile);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setAppThermProfile(String packageName, String profile) {
            long ident = Binder.clearCallingIdentity();
            try {
                setAppThermProfileInternal(packageName,profile);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }
        @Override public boolean isAppRestrictedProfile(String packageName) {
            long ident = Binder.clearCallingIdentity();
            try {
                return isAppRestrictedProfileInternal(packageName);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setAppRestrictedProfile(String packageName, boolean restricted) {
            long ident = Binder.clearCallingIdentity();
            try {
                setAppRestrictedProfile(packageName,restricted);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public int getAppPriority(String packageName) {
            long ident = Binder.clearCallingIdentity();
            try {
                return getAppPriorityInternal(packageName);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setAppPriority(String packageName, int priority) {
            long ident = Binder.clearCallingIdentity();
            try {
                setAppPriorityInternal(packageName,priority);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public int getAppBrightness(String packageName) {
            long ident = Binder.clearCallingIdentity();
            try {
                return getAppBrightnessInternal(packageName);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setAppBrightness(String packageName, int brightness) {
            long ident = Binder.clearCallingIdentity();
            try {
                setAppBrightnessInternal(packageName,brightness);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public String getDefaultPerfProfile() {
            long ident = Binder.clearCallingIdentity();
            try {
                return getDefaultPerfProfileInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }
        @Override public void setDefaultPerfProfile(String profile) {
            long ident = Binder.clearCallingIdentity();
            try {
                setDefaultPerfProfileInternal(profile);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public String getDefaultThermProfile() {
            long ident = Binder.clearCallingIdentity();
            try {
                return getDefaultThermProfileInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setDefaultThermProfile(String profile) {
            long ident = Binder.clearCallingIdentity();
            try {
                setDefaultThermProfileInternal(profile);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setAppOption(String profile, int option, int value) {
            long ident = Binder.clearCallingIdentity();
            try {
                setAppOptionInternal(profile, option, value);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public int getAppOption(String profile, int option) {
            long ident = Binder.clearCallingIdentity();
            try {
                return getAppOptionInternal(profile, option);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public int getBrightnessOverride() {
            long ident = Binder.clearCallingIdentity();
            try {
                return getBrightnessOverrideInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }


        @Override public boolean isReaderMode() {
            long ident = Binder.clearCallingIdentity();
            try {
                return isReaderModeInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public boolean isDeviceIdleMode() {
            long ident = Binder.clearCallingIdentity();
            try {
                return isDeviceIdleModeInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public boolean isLightDeviceIdleMode() {
            long ident = Binder.clearCallingIdentity();
            try {
                return isLightDeviceIdleModeInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setDeviceIdleMode(boolean enabled) {
            long ident = Binder.clearCallingIdentity();
            try {
                setDeviceIdleModeInternal(enabled);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setLightDeviceIdleMode(boolean enabled) {
            long ident = Binder.clearCallingIdentity();
            try {
                setLightDeviceIdleModeInternal(enabled);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }


        @Override public boolean isAggressiveDeviceIdleMode() {
            long ident = Binder.clearCallingIdentity();
            try {
                return isAggressiveDeviceIdleModeInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public void setWakefulness(int wakefulness,int reason){
            long ident = Binder.clearCallingIdentity();
            try {
                setWakefulnessInternal(wakefulness, reason);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }

        @Override public boolean isExtremeSaverActive() {
            long ident = Binder.clearCallingIdentity();
            try {
                return isExtremeSaverActiveInternal();
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
        }


        @Override public int isRestrictedApp(int requestId, int uid, String packageName, boolean useTempWhitelistToo, boolean exemptOnBatterySaver) {
            long ident = Binder.clearCallingIdentity();
            try {
                return isRestrictedAppInternal(requestId, uid, packageName, useTempWhitelistToo, exemptOnBatterySaver);
            } finally {
                Binder.restoreCallingIdentity(ident);
            }
	}

    }

    class ApplicationProfileInfo {
        public String packageName;
        public String perfProfile;
        public String thermProfile;
        public boolean isRestricted;
        public int priority;
        public int brightness; 
      

        private ArrayMap<Integer, Integer> mAppOps = new ArrayMap<>();

        public ApplicationProfileInfo() {
            perfProfile = "default";
            thermProfile = "default";
            brightness = 0;
        }

        public int getAppOption(int option) {
            if( mAppOps.containsKey(option) ) {
                return mAppOps.get(option);
            }
            return 0;
        }

        public void setAppOption(int option,int value) {
            mAppOps.put(option,value);
        }

        public ArrayMap<Integer, Integer> getOpArray() {
            return mAppOps;
        }

        @Override
        public String toString() {
            String ret = "packageName=" + packageName +
            ", perfProfile=" + perfProfile +
            ", thermProfile=" + thermProfile +
            ", isRestricted=" + isRestricted +
            ", priority=" + priority +
            ", brightness=" + brightness;
            return ret;
        }

        

    }

    private static File getSystemDir() {
        return new File(Environment.getDataDirectory(), "system");
    }

}
