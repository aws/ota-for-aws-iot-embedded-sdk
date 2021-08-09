# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY = stringBuilderUInt32Hex_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = stringBuilderUInt32Hex

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET += stringBuilderUInt32Hex.unwind.0:10

CBMC_FLAG_UNWINDING_ASSERTIONS =

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/source/ota_mqtt.c


# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
