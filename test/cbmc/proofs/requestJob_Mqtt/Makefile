
HARNESS_ENTRY = requestJob_Mqtt_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = requestJob_Mqtt

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(PROOF_STUB)/strnlen.c
PROJECT_SOURCES += $(SRCDIR)/source/ota_mqtt.c

# The strncpy bound is large due to requestJob_Mqtt copying message pieces
# into a buffer. This is much higher than the 84 characters of the buffer
# as null characters are used after the copied in strin to fill the buffer.
UNWINDSET += strncpy.0:220
# The strnlen function is used when calculating the maximum thingname length
# which can be used to generate the client token.
UNWINDSET += strnlen.0:54

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
