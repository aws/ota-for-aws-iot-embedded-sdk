# Changelog for AWS IoT Over-the-air Update Library
### v3.3.0 (December 2021)
 - Added CBMC proofs of all public and private functions in the OTA library. 
 - [#373](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/373) Updated compiler flag for tinycbor source files
 - [#407](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/407) Added checks to prevent arithmetic overflows
 - [#390](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/390) Make OTA file type configurable.
 - [#329](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/329) Misc fixes to remove build warnings 
 - [#356](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/356) Add type cast to event functions as per POSIX spec
 
### v3.2.0 (November 2021)
 - [#275](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/276) Updated the doxygen version from 1.8.20 to 1.9.2 
 - [#236](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/236) Added C++ guards
 - [#231](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/231) Added checks for http interface functions. 

### v3.1.0 (August 2021)
 - [#232](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/232) Add updater version to the status details when job succeeds
 - [#216](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/216), [#213](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/213), [#226](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/226), [#234](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/234) Misc fixes to remove compiler warnings and resolve build failures on certain platforms.
 - [#200](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/200) Add type cast for logging variable of type size_t
## v3.0.0 (March 2021)

### Updates

 - The AWS IoT Over-the-air Update library is now generally available.
 - [#154](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/154) Update `Ota_Shutdown` API. `Ota_Shutdown` now takes a parameter `unsubscribeFlag` which  indicates if unsubscribe operations should be performed from the job topics when shutdown is called.
 - [#174](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/174), [#186](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/186) Add support for different filetypes. `configOTA_FIRMWARE_UPDATE_FILE_TYPE_ID` config can be used to define the default firmware filetype id.

### Other
 - [#186](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/186) Add OtaAppCallback for job and update completion.
 - [#178](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/178), [#164](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/164), [#160](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/160) Update custom job and active job logic flow.
 - [#177](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/177) Add code example documentation for OTA APIs.
 - [#155](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/155) Remove subscription from accepted topics of AWS IoT Jobs service. AWS IoT Jobs service publishes messages on response topics without needing devices to subscribe to response topics.
 - [#183](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/183), [#158](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/158), [#157](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/157), [#153](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/153) Other fixes to execution flow and improving logs.

## v2.0.0 (Release Candidate) (December 2020)
- This is a release candidate of the AWS IoT Over-the-air (OTA) Update library in this repository. You can use the OTA library with your chosen MQTT library, HTTP library, and operating system (e.g. Linux, FreeRTOS).
