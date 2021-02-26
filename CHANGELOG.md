# Changelog for AWS IoT Over-the-air Update Library

## v3.0.0 (February 2021)

### Updates

 - [#154](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/154) Updated `Ota_Shutdown` API. `Ota_Shutdown` now takes a parameter `unsubscribeFlag` which  indicates if unsubscribe operations should be performed from the job topics when shutdown is called.
 - [#174](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/174), [#186](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/186) Adding support for different filetypes. `configOTA_FIRMWARE_UPDATE_FILE_TYPE_ID` config can be used to define the default firmware filetype id.
### Other
 - [#186](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/186) Adding OtaAppCallback for job and update completion.
 - [#178](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/178), [#164](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/164), [#160](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/160) Updating custom job and active job logic flow.
 - [#177](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/177) Adding example documentation for OTA APIs.
 - [#155](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/155) Removing subscription to accepted topics i.e. "/jobs/$next/get/accepted"
 - [#183](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/183), [#158](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/158), [#157](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/157), [#153](https://github.com/aws/ota-for-aws-iot-embedded-sdk/pull/153) Other fixes to execution flow and improving logs.
## v2.0.0 (Release Candidate) (December 2020)
This is a release candidate of the AWS IoT Over-the-air (OTA) Update library in this repository. You can use the OTA library with your chosen MQTT library, HTTP library, and operating system (e.g. Linux, FreeRTOS).