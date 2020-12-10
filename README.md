# AWS IoT Over-the-Air (OTA) Updates

The OTA library enables you to manage the notification of a newly available update, download the update, and perform cryptographic verification of the firmware update. Using the library, you can logically separate firmware updates from the application running on your devices. The OTA library can share a network connection with the application, saving memory in resource-constrained devices. In addition, the OTA library lets you define application-specific logic for testing, committing, or rolling back a firmware update. The library supports different application protocols like Message Queuing Telemetry Transport (MQTT) and Hypertext Transfer Protocol (HTTP), and provides various configuration options you can fine tune depending on network type and conditions.

This library is distributed under the [MIT Open Source License](LICENSE).

This library has gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score over 8. This library has also undergone static code analysis from [Coverity static analysis](https://scan.coverity.com/).

See memory requirements for this library [here](https://docs.aws.amazon.com/embedded-csdk/202012.00/lib-ref/libraries/aws/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#ota_memory_requirements).

### AWS IoT Over-the-Air (OTA) Updates Config File

The AWS IoT Over-the-Air (OTA) Updates library exposes configuration macros that are required for building the library. A list of all the configurations and their default values are defined in [ota_config_defaults.h](source/include/ota_config_defaults.h). To provide custom values for the configuration macros, a custom config file named `ota_config.h` can be provided by the user application to the library.

By default, a `ota_config.h` custom config is required to build the library. To disable this requirement and build the library with default configuration values, provide `OTA_DO_NOT_USE_CUSTOM_CONFIG` as a compile time preprocessor macro.

## Building the Library
The [otaFilePaths.cmake](shadowFilePaths.cmake) file contains the information of all source files and the header include paths required to build the AWS IoT Over the Air (OTA) Updates library.

As mentioned in the previous section, either a custom config file (i.e. `ota_config.h`) OR the `OTA_DO_NOT_USE_CUSTOM_CONFIG` macro needs to be provided to build the AWS IoT Over the Air (OTA) Updates library.

For a CMake example of building the AWS IoT Over the Air (OTA) Updates library with the `otaFilePaths.cmake` file, refer to the `coverity_analysis` library target in the [test/CMakeLists.txt](test/CMakeLists.txt) file.

## Building Unit Tests
### Checkout CMock Submodule
By default, the submodules in this repository are configured with `update=none` in [.gitmodules](.gitmodules) to avoid increasing clone time and disk space usage of other repositories (like [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C) that submodules this repository).


To build unit tests, the submodule dependency of CMock is required. Use the following command to clone the submodule:
```
git submodule update --checkout --init --recursive --test/unit-test/CMock
```

### Platform Prerequisites

- For building the library, **CMake 3.13.0** or later and a **C90 compiler**.
- For running unit tests, **Ruby 2.0.0** or later is additionally required for the CMock test framework (that we use).
- For running the coverage target, **gcov** and **lcov** are additionally required.

### Steps to build unit tests

1. Go to the root directory of this repository. (Make sure that the **CMock** submodule is cloned as described [above](#checkout-cmock-submodule).)

1. Run the *cmake* command: `cmake -S test -B build`

1. Run this command to build the library and unit tests: `make -C build all`

1. The generated test executables will be present in `build/bin/tests` folder.

1. Run `cd build && ctest` to execute all tests and view the test run summary.

## Reference examples

Please refer to the demos of the AWS IoT Device Shadow library in the following locations for reference examples on POSIX and FreeRTOS platforms:

| Platform | Location |
| :-: | :-: | :-: |
| POSIX | [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main/demos/ota)
| FreeRTOS | FreeRTOS/FreeRTOS | FreeRTOS+TCP for TCP/IP and mbedTLS for TLS stack


## Generating documentation

The Doxygen references were created using Doxygen version 1.8.20. To generate the
Doxygen pages, please run the following command from the root of this repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Porting

In order to support AWS IoT Over-the-Air (OTA) Updates on your microcontroller, it is necessary to implement the Portable Application Layer (PAL). The PAL interface is defined in [ota_platform_interface.h](source/include/ota_platform_interface.h).

PAL interface documentation is in https://docs.aws.amazon.com/freertos/latest/portingguide/afr-porting-ota.html.

## AWS IoT Device Setup

As a prerequisite to integration testing, you must configure your device as an AWS IoT "Thing".

1. Follow these instructions, https://docs.aws.amazon.com/freertos/latest/userguide/freertos-prereqs.html. For an alternative description of getting started with AWS IoT, you can also use these steps https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html, up to and including the web page entitled _Attach a Certificate to a Thing_.
2. Check your configuration using https://docs.aws.amazon.com/freertos/latest/userguide/getting_started_windows.html and our _MQTT Hello World_ demo app.
Transfer your client configuration to your port and run “MQTT Hello World” from your board.

## Integration Testing for an OTA PAL

1. Once you’ve confirmed that the previous step is working, open aws_demo_runner.c, comment out the two references to vStartMQTTEchoDemo(), and uncomment the two references to vStartOTAUpdateDemoTask().
Build and run vStartOTAUpdateDemoTask on your IoT Module board. The expected behavior of that app is to start the OTA Agent and then wait forever for a job notification from the cloud.
2. To create an OTA job, following these steps:
    1. https://docs.aws.amazon.com/freertos/latest/userguide/freertos-ota-dev.html
    2. https://docs.aws.amazon.com/freertos/latest/userguide/ota-prereqs.html
    3. https://docs.aws.amazon.com/freertos/latest/userguide/dg-ota-create-update.html
    4. https://docs.aws.amazon.com/freertos/latest/userguide/ota-console-workflow.html
3. After you publish the job created in the last step above, the OTA agent on the aboard should receive the JSON job document and immediately start downloading the new firmware block-by-block via MQTT. Errors encountered during that procedure are logged by the agent to the serial output from the device.
