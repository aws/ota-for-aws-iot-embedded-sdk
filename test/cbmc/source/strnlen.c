/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * FUNCTION: strlen
 *
 * This function overrides the original implementation of the strlen function
 * from string.h. It copies the values of n bytes from the *src to the *dst.
 * It also checks if the size of the arrays pointed to by both the *dst and
 * *src parameters are at least n bytes and if they overlap.
 */


#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#include <stdlib.h>

#undef strnlen


/**
 * Override the version of memcpy used by CBMC.
 */
size_t strnlen_impl(const char *s, size_t maxlen) {
    __CPROVER_HIDE:;
    #ifdef __CPROVER_STRING_ABSTRACTION
        __CPROVER_precondition(__CPROVER_is_zero_string(s), "strlen zero-termination");
        return __CPROVER_zero_string_length(s);
    #else
        __CPROVER_size_t len=0;
        while(s[len]!=0 && len < maxlen ) len++;
        return len;
  #endif
}

size_t strnlen(const char *s, size_t maxlen) {
    return strnlen_impl(s,maxlen);
}

size_t __builtin___strnlen_chk(const char *s, size_t maxlen) {
    return strnlen_impl(s, maxlen);
}