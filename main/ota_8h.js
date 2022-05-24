var ota_8h =
[
    [ "OtaAgentContext_t", "struct_ota_agent_context__t.html", "struct_ota_agent_context__t" ],
    [ "CONST_STRLEN", "ota_8h.html#a2714f6afa56c8777b5e570a390a69a58", null ],
    [ "OTA_FILE_SIG_KEY_STR_MAX_LENGTH", "ota_8h.html#a8baee291088322fecd736ff0b03fb730", null ],
    [ "OtaAppCallback_t", "group__ota__callback__types.html#ga3bedd7e278f89d555a32a7efa8023a28", null ],
    [ "OtaErr_t", "group__ota__enum__types.html#ga7ab3c74dc057383c56c6cb9aa6bf0b2d", [
      [ "OtaErrNone", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da0c644255eee375cb8e6bd9def0772e02", null ],
      [ "OtaErrUninitialized", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da0c1dd94b8875896b0a9dd383ba239774", null ],
      [ "OtaErrPanic", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da096a4af841716cf1ee881826d30b5406", null ],
      [ "OtaErrInvalidArg", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2dae8b91d2bcdd38b2c79bc67122681d5b9", null ],
      [ "OtaErrAgentStopped", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da2e43587b6c8d6abbdeed09232b8b9696", null ],
      [ "OtaErrSignalEventFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da8de27454ca774732ca584803d1ab5888", null ],
      [ "OtaErrRequestJobFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da494a5dcbd62a41249e5ae1c177b442cb", null ],
      [ "OtaErrInitFileTransferFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da750fde72ae523e47fa838cb781dba75f", null ],
      [ "OtaErrRequestFileBlockFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da6d94255e998ae49d916648bb94b7da84", null ],
      [ "OtaErrCleanupControlFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2daa7c1391bb361ec9857470b984cd31346", null ],
      [ "OtaErrCleanupDataFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2dae40f5144d7881fb9d8a7f403c44a3133", null ],
      [ "OtaErrUpdateJobStatusFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2dad4008e18cf533002f2f194a491f859e1", null ],
      [ "OtaErrJobParserError", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da525ecca44a574d8917760f869853a6ee", null ],
      [ "OtaErrInvalidDataProtocol", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da06fb88bd9ddb49038227c63e15a83523", null ],
      [ "OtaErrMomentumAbort", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da48fcd14a5554b8c0e447403c059bc786", null ],
      [ "OtaErrDowngradeNotAllowed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da0e99db7052f9c7007083ecc3fc08604c", null ],
      [ "OtaErrSameFirmwareVersion", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2dad8a8f3c4637db28866f53fbc91fe6427", null ],
      [ "OtaErrImageStateMismatch", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da38b24044cf02652dbb60efe38864e527", null ],
      [ "OtaErrNoActiveJob", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da7dc1d1638189d537ce31ee3ce2d6d55e", null ],
      [ "OtaErrUserAbort", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2dafbd1a370f69e3eb88eff25d4fe9facbd", null ],
      [ "OtaErrFailedToEncodeCbor", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2dad57de41d65cd3bd5de28228883e83084", null ],
      [ "OtaErrFailedToDecodeCbor", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da7fa31caf9e7a68df47ddbdb657f7f35d", null ],
      [ "OtaErrActivateFailed", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2daf5d3845d8b68e0c91cff60d2a38a2678", null ],
      [ "OtaErrFileSizeOverflow", "group__ota__enum__types.html#gga7ab3c74dc057383c56c6cb9aa6bf0b2da124b86050f54ae91942e693de587b914", null ]
    ] ],
    [ "OtaState_t", "group__ota__enum__types.html#ga1cb476a5e0ee81fa486f605e64419dcc", [
      [ "OtaAgentStateNoTransition", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dccac587715b1ba932ee624384dde28a24f2", null ],
      [ "OtaAgentStateInit", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dccaac0d4b1bde4499c411fed16dc408ba72", null ],
      [ "OtaAgentStateReady", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dcca8b9e78962c5635890f6dd59bf74a4587", null ],
      [ "OtaAgentStateRequestingJob", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dccac15bad1565ec8612b66973849663ee1f", null ],
      [ "OtaAgentStateWaitingForJob", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dccaa90c9266bf1de5228358411b0e51714c", null ],
      [ "OtaAgentStateCreatingFile", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dccab89e2abec6b301afe88d561fe1802f82", null ],
      [ "OtaAgentStateRequestingFileBlock", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dcca4570ff027eb6e9824e7e87fe5131cf69", null ],
      [ "OtaAgentStateWaitingForFileBlock", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dcca12e77d6a6992070a549adf06893e8c3d", null ],
      [ "OtaAgentStateClosingFile", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dcca8966311cb03f6117d6c7f2bb6bef4f57", null ],
      [ "OtaAgentStateSuspended", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dccab45d68539796336c966e0b98585c0504", null ],
      [ "OtaAgentStateShuttingDown", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dcca392412cdc15086dd23654b342f46b17c", null ],
      [ "OtaAgentStateStopped", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dcca74eaa10dc13570657ac0a4dc9e46fec2", null ],
      [ "OtaAgentStateAll", "group__ota__enum__types.html#gga1cb476a5e0ee81fa486f605e64419dccad4d076a2211d90f2d51469324ad981ab", null ]
    ] ],
    [ "OtaJobParseErr_t", "group__ota__enum__types.html#gab8e370b46d0ae5d51879710d533a7314", [
      [ "OtaJobParseErrUnknown", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314a3c1411a5f15ec40414e2519eed60616e", null ],
      [ "OtaJobParseErrNone", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314a1021c6312e3f91433224eb6e70177b15", null ],
      [ "OtaJobParseErrNullJob", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314ab820f2a328178dda0b6751cb07bd4dc3", null ],
      [ "OtaJobParseErrUpdateCurrentJob", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314a1fffbd453c627f57dd2e30c906fb0b2e", null ],
      [ "OtaJobParseErrZeroFileSize", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314a3e0cdbf1964979739be090007ec71ead", null ],
      [ "OtaJobParseErrNonConformingJobDoc", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314a0f02459a8c6e25c6c715fba92b4b733a", null ],
      [ "OtaJobParseErrBadModelInitParams", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314af35bcb742f0b9af7b75b544cfdd5651f", null ],
      [ "OtaJobParseErrNoContextAvailable", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314a39b9869686bca7fd811225c277c7516d", null ],
      [ "OtaJobParseErrNoActiveJobs", "group__ota__enum__types.html#ggab8e370b46d0ae5d51879710d533a7314a361a2805800978dad2ca32335d5615e9", null ]
    ] ],
    [ "OtaJobEvent_t", "group__ota__enum__types.html#ga96a2e1f5cfad783897e805196eee39a7", [
      [ "OtaJobEventActivate", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7aaf02fd22119771d2980c7af439fa3280", null ],
      [ "OtaJobEventFail", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7a549e2b4c48aadc3c2f354647b8fd5728", null ],
      [ "OtaJobEventStartTest", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7a04e2c9b7143d34f63905cd052bf9763b", null ],
      [ "OtaJobEventProcessed", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7abd5b42406265a448d9250890c0360c10", null ],
      [ "OtaJobEventSelfTestFailed", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7a26b36eee239cace8df37d0a9e5874212", null ],
      [ "OtaJobEventParseCustomJob", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7a8e314e0d83b5dcd572b08d9f205ab658", null ],
      [ "OtaJobEventReceivedJob", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7a5cf84ad545b4e47c7bc2fe36b4b83fdd", null ],
      [ "OtaJobEventUpdateComplete", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7a2ea5dedb25b574c14f379ae6b530dfff", null ],
      [ "OtaJobEventNoActiveJob", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7a2545ed736348e8d3f14746792ed40744", null ],
      [ "OtaLastJobEvent", "group__ota__enum__types.html#gga96a2e1f5cfad783897e805196eee39a7afd4ce3f42084241df27353d4f0e4c614", null ]
    ] ],
    [ "OtaJobStatus_t", "group__ota__enum__types.html#gabf6d6b1d2bca4c54f58bd622ca6242d0", [
      [ "JobStatusInProgress", "group__ota__enum__types.html#ggabf6d6b1d2bca4c54f58bd622ca6242d0a1602a6b97ecd3dcc06b3b3157009d8b5", null ],
      [ "JobStatusFailed", "group__ota__enum__types.html#ggabf6d6b1d2bca4c54f58bd622ca6242d0a8c44d31ae1d41e92836f6e072fbf39db", null ],
      [ "JobStatusSucceeded", "group__ota__enum__types.html#ggabf6d6b1d2bca4c54f58bd622ca6242d0a4ce9ff23f691ab8ff0ab14ba7e38aea1", null ],
      [ "JobStatusRejected", "group__ota__enum__types.html#ggabf6d6b1d2bca4c54f58bd622ca6242d0ad73161088bbd8bd4ad101d3d24e6ded7", null ],
      [ "JobStatusFailedWithVal", "group__ota__enum__types.html#ggabf6d6b1d2bca4c54f58bd622ca6242d0a4965780a768288c0f1cb758206e10186", null ],
      [ "NumJobStatusMappings", "group__ota__enum__types.html#ggabf6d6b1d2bca4c54f58bd622ca6242d0a9bedf4d3fc48cf5d504864b3c3505362", null ]
    ] ],
    [ "OTA_Init", "ota_8h.html#a9011a6007328dfb3bfde5fdb645fa52f", null ],
    [ "OTA_Shutdown", "ota_8h.html#ac779291eb93f4e0e6459816e60e13b09", null ],
    [ "OTA_GetState", "ota_8h.html#a6db3f9cb417cb135cb0e68f5b5f2b11f", null ],
    [ "OTA_ActivateNewImage", "ota_8h.html#a5169ba09148e7f5668a90e776e712f8b", null ],
    [ "OTA_SetImageState", "ota_8h.html#ab68cdf65934474e1f3d2cd1046314bea", null ],
    [ "OTA_GetImageState", "ota_8h.html#a9c5b25f9a7eff3ded8cdf088c2011742", null ],
    [ "OTA_CheckForUpdate", "ota_8h.html#a1178e8009eb05e6f55f6506b625c9fc2", null ],
    [ "OTA_Suspend", "ota_8h.html#a65b61ae5dd477e8b2e6c88ea0473c62b", null ],
    [ "OTA_Resume", "ota_8h.html#ae9d40388ac87e4ac93288de37c98a138", null ],
    [ "OTA_EventProcessingTask", "ota_8h.html#ab3a0cfdc8694a606a1d736b2f54fb113", null ],
    [ "OTA_SignalEvent", "ota_8h.html#a2564144f284db077b8947ba58a6a72bb", null ],
    [ "OTA_GetStatistics", "ota_8h.html#a63182243ef3c18d5f36cd427b83a1a22", null ],
    [ "OTA_Err_strerror", "ota_8h.html#a39a9b75e749cf89593c4cf411327ce47", null ],
    [ "OTA_JobParse_strerror", "ota_8h.html#aaf68d300d6ff9a8b4728b3d9e5f52b6d", null ],
    [ "OTA_PalStatus_strerror", "ota_8h.html#a5a58be1ac41b7d619eeeb4861be37c89", null ],
    [ "OTA_OsStatus_strerror", "ota_8h.html#a4951f4bb1bfbb7312850454ca2b282a4", null ],
    [ "OTA_JsonFileSignatureKey", "ota_8h.html#a3b34dcda67d1fd023ced9257eb00cdcb", null ]
];