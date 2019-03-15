/**
 * Copyright (c) 2015, The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package android.os;

import android.os.UserHandle;


/** @hide */
interface IBaikalServiceController {
    String getAppPerfProfile(String packageName);
    String getAppThermProfile(String packageName);
    void setAppPerfProfile(String packageName, String profile);
    void setAppThermProfile(String packageName, String profile);
    boolean isAppRestrictedProfile(String packageName);
    void setAppRestrictedProfile(String packageName, boolean restricted);
    int getAppPriority(String packageName);
    void setAppPriority(String packageName, int priority);
    int getAppBrightness(String packageName);
    void setAppBrightness(String packageName, int brightness);
    String getDefaultPerfProfile();
    void setDefaultPerfProfile(String profile);
    String getDefaultThermProfile();
    void setDefaultThermProfile(String profile);
    int getAppOption(String packageName,int option);
    void setAppOption(String packageName,int option, int value);
    int getBrightnessOverride();

    boolean isReaderMode();
    boolean isDeviceIdleMode();
    boolean isLightDeviceIdleMode();
    void setDeviceIdleMode(boolean enabled);
    void setLightDeviceIdleMode(boolean enabled);

    boolean isAggressiveDeviceIdleMode();
    void setWakefulness(int wakefulness,int reason);
}
