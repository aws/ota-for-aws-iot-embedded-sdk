/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file updateJobStatus_Mqtt_harness.c
 * @brief Implements the proof harness for updateJobStatus_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Stub required to publish status message over mqtt. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_publishStatusMessage( OtaAgentContext_t * pAgentCtx,
                                                                      const char * pMsg,
                                                                      uint32_t msgSize,
                                                                      uint8_t qos )
{
    OtaMqttStatus_t mqttStatus;

    /* The pMsg buffer is always initialized before passing it to
     * publishStatusMessage function and thus it cannot be NULL. */
    __CPROVER_assert( pMsg != NULL,
                      "Unable to use pMsg: passed pointer value is NULL." );

    return mqttStatus;
}

/* Stub to populate the buffer with job status message and return the msfbufferSize. */
uint32_t __CPROVER_file_local_ota_mqtt_c_buildStatusMessageReceiving( char * pMsgBuffer,
                                                                      size_t msgBufferSize,
                                                                      OtaJobStatus_t status,
                                                                      const OtaFileContext_t * pOTAFileCtx )
{
    uint32_t bufferSize;

    /* The pMsg buffer is always initialized before passing it to
     * buildStatusMessageReceiving function and thus it cannot be NULL. */
    __CPROVER_assert( pMsgBuffer != NULL,
                      "Unable to use pMsg: passed pointer value is NULL." );

    /* The buildStatusMessageReceiving function always returns the number of elements
     * written in the pMsgBuffer. Since the maximum size of the pMsgBuffer is given by
     * msgBufferSize and the return value cannot exceed it. */
    __CPROVER_assume( bufferSize >= 0 && bufferSize < msgBufferSize );

    return bufferSize;
}

/* populate the message buffer with status to indicate device in self test. */
uint32_t __CPROVER_file_local_ota_mqtt_c_prvBuildStatusMessageSelfTest( char * pMsgBuffer,
                                                                        size_t msgBufferSize,
                                                                        OtaJobStatus_t status,
                                                                        int32_t reason )
{
    uint32_t bufferSize;

    /* The pMsg buffer is always initialized before passing it to
     * prvBuildStatusMessageSelfTest function and thus it cannot be NULL. */
    __CPROVER_assert( pMsgBuffer != NULL,
                      "Unable to use pMsg: passed pointer value is NULL." );

    /* The prvBuildStatusMessageSelfTest function always returns the number of elements
     * written in the pMsgBuffer. Since the maximum size of the pMsgBuffer is given by
     * msgBufferSize and the return value cannot exceed it. */
    __CPROVER_assume( bufferSize >= 0 && bufferSize < msgBufferSize );

    return bufferSize;
}

/* populate the buffer with response message with the status of job. */
uint32_t __CPROVER_file_local_ota_mqtt_c_prvBuildStatusMessageFinish( char * pMsgBuffer,
                                                                      size_t msgBufferSize,
                                                                      OtaJobStatus_t status,
                                                                      int32_t reason,
                                                                      int32_t subReason,
                                                                      uint32_t previousVersion )
{
    uint32_t bufferSize;

    /* The pMsg buffer is always initialized before passing it to
     * prvBuildStatusMessageFinish function and thus it cannot be NULL. */
    __CPROVER_assert( pMsgBuffer != NULL,
                      "Unable to use pMsg: passed pointer value is NULL." );

    /* The prvBuildStatusMessageFinish function always returns the number of elements
     * written in the pMsgBuffer. Since the maximum size of the pMsgBuffer is given by
     * msgBufferSize and the return value cannot exceed it. */
    __CPROVER_assume( bufferSize >= 0 && bufferSize < msgBufferSize );

    return bufferSize;
}

void updateJobStatus_Mqtt_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaJobStatus_t status;
    int32_t reason;
    int32_t subReason;
    OtaAgentContext_t agent;

    /* OTA agent is defined globally in ota.c and thus can never be NULL. */
    pAgentCtx = &agent;

    /* status can only have the first 5 values from the OtaJobStatus_t enum. */
    __CPROVER_assume( status >= 0 && status < 5 );

    updateJobStatus_Mqtt( pAgentCtx, status, reason, subReason );
}
