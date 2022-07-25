# MISRA Compliance

The AWS IoT Over-the-air Update library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
Deviations from the MISRA standard are listed below:

### Ignored by [Coverity Configuration](tools/coverity/misra.config)
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Directive 4.5 | Advisory | Allow names that MISRA considers ambiguous (such as LogInfo and LogError). |
| Directive 4.8 | Advisory | Allow inclusion of unused types. Header files for a specific port, which are needed by all files, may define types that are not used by a specific file. |
| Directive 4.9 | Advisory | Allow inclusion of function like macros. The `assert` macro is used throughout the library for parameter validation, and logging is done using function like macros. |
| Rule 2.4 | Advisory | Allow unused tags. Some compilers warn if types are not tagged. |
| Rule 2.5 | Advisory | Allow unused macros. Library headers may define macros intended for the application's use, but are not used by a specific file. |
| Rule 3.1 | Required | Allow nested comments. C++ style `//` comments are used in example code within Doxygen documentation blocks. |
| Rule 5.8 | Required | As part of building the coverity_analysis target a copy of the files is made with some of the static keywords removed, coverity will then incorrectly flag doubles of function declerations because of this.
| Rule 8.6  | Required | `OTA_JsonFileSignatureKey` is an extern variable declared but not defined in OTA library. This variable shall be defined in OTA platform abstraction layer implementation, which is found in other repositories. |
| Rule 8.7 | Advisory | API functions are not used by the library; however, they must be externally visible in order to be used by an application. |
| Rule 8.9 | Advisory | For ease, configuration parameters are defined at a global scope even when used only once. |
| Rule 11.5 | Advisory | Allow casts from `void *`. Fields may be passed as `void *`, requiring a cast to the correct data type before use. |
| Rule 12.3 | Advisory | Allow use of `assert()` macro, expansion of which uses comma operator. |
| Rule 15.6 | Required | Allow use of `assert()` macro, expansion of which contains non-compound if statements. |
| Rule 20.12 | Required | Allow use of `assert()`, which uses a parameter in both expanded and raw forms. |
| Rule 21.1 | Required | Allow use of all macro names. For compatibility, libraries may define macros introduced in C99 for use with C90 compilers. |
| Rule 21.2 | Required | Allow use of all macro and identifier names. For compatibility, libraries may define macros introduced in C99 for use with C90 compilers. |
| Rule 21.5 | Required | This rule prohibits the use of signal.h because of undefined behavior. However, the warning is in OS porting implementation on POSIX, which has well defined behavior. We're using the timer functionality from POSIX so we deviate from this rule. |

### Flagged by Coverity
| Deviation | Category | Justification |
| :-: | :-: | :-: |

### Suppressed with Coverity Comments
| Deviation | Category | Justification |
| :-: | :-: | :-: |
| Directive 4.6 | Advisory | The uses of a 3rd party macro cbor_value_get_int requires the use of ints |
| Rule 2.2 | Required | This rule prohibits dead code for the string arrays `pOtaAgentStateStrings` and `pOtaEventStrings`. These are used only for logging which is disabled during static analysis. |
| Rule 8.13 | Required | Coverity falsely believes that there are variables in some of the functions that can be made const. |
| Rule 10.1 | Required | Use of POSIX specific macro `O_CREAT` and `O_RDWR` is flagged for this violation. We use these 2 macros with one POSIX API `mq_open` in the POSIX OS implementation. |
| Rule 11.8 | Required | Coverity scans will raise an error if certain variables are not marked as const, even if the variables do get modified in that function. As such there are two occurences where to get around that error, we supress this one. |
| Rule 14.3 | Required | This is a warning on `otaconfigAllowDowngrade` being a constant and used in controlling expression. This macro is one of the OTA library configuration and it's set to 0 when running the static analysis. But users can change it when they build their application. So this is a false positive. |
| Rule 19.2 | Advisory | Unions are used to reduce the memory footprint and to represent packet formats in the FreeRTOS network stack. |
| Rule 21.3 | Required | This is explained in rule 4.12 from section above. We define a malloc and free interface so that our OTA library can be ported to any OS. |
| Rule 21.8 | Required | One of the OTA platform abstraction layer interfaces `abort` is flagged for this violation. This is implemented by a platform abstraction layer and always called through the OTA PAL interface. |