#pragma once

#include <inttypes.h>
#include <string.h>
#include <stdlib.h>

int ota_base64_decode(unsigned char* dst, size_t dlen, size_t* olen, const unsigned char* src, size_t slen);
