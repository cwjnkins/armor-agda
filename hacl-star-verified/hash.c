#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Hash_MD5.h"
#include "Hacl_Hash_SHA1.h"

#define BUFFER_SIZE 2048

// Validate hex string
int is_valid_hex(const char *hex) {
    for (size_t i = 0; hex[i] != '\0'; i++) {
        if (!((hex[i] >= '0' && hex[i] <= '9') || 
              (hex[i] >= 'a' && hex[i] <= 'f') || 
              (hex[i] >= 'A' && hex[i] <= 'F'))) {
            return 0;
        }
    }
    return 1;
}

uint8_t hex_char_to_byte(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return 0; // Handle invalid characters safely
}

void hex_to_bytes(const char *hex, uint8_t *bytes, size_t hex_len) {
    for (size_t i = 0; i < hex_len / 2; i++) {
        bytes[i] = (hex_char_to_byte(hex[i * 2]) << 4) | hex_char_to_byte(hex[i * 2 + 1]);
    }
}

char byte_to_hex_char(uint8_t nibble) {
    return (nibble < 10) ? ('0' + nibble) : ('A' + nibble - 10);
}

void bytes_to_hex(const uint8_t *bytes, char *hex, size_t byte_len) {
    for (size_t i = 0; i < byte_len; i++) {
        hex[i * 2]     = byte_to_hex_char((bytes[i] >> 4) & 0x0F);  // High nibble
        hex[i * 2 + 1] = byte_to_hex_char(bytes[i] & 0x0F);         // Low nibble
    }
}

int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <hash_type> <hex-encoded input>\n", argv[0]);
        return 1;
    }

    char *hash_type = argv[1];
    char *hex_input_dash = argv[2];
    char *hex_input = NULL;
    size_t hex_len = 0;

    if (strcmp(hex_input_dash, "-") == 0) {
        // Read from stdin
        size_t size = BUFFER_SIZE;
        hex_input = malloc(size);
        if (!hex_input) {
            fprintf(stderr, "Memory allocation error\n");
            return 1;
        }

        size_t len = 0;
        int c;
        while ((c = getchar()) != EOF) {
            if (len + 1 >= size) {
                size *= 2;
                hex_input = realloc(hex_input, size);
                if (!hex_input) {
                    fprintf(stderr, "Memory reallocation error\n");
                    return 1;
                }
            }
            hex_input[len++] = (char)c;
        }
        hex_input[len] = '\0';
        hex_len = len;
    }

    if (hex_len == 0 || hex_len % 2 != 0) {
        fprintf(stderr, "Error: Invalid hex input length\n");
        return 1;
    }

    if (!is_valid_hex(hex_input)) {
        fprintf(stderr, "Error: Input contains non-hex characters\n");
        free(hex_input);
        return 1;
    }

    size_t byte_len = hex_len / 2;
    if (byte_len == 0) {
        fprintf(stderr, "Error: Input cannot be empty\n");
        free(hex_input);
        return 1;
    }

    uint8_t *input_bytes = malloc(byte_len);
    if (!input_bytes) {
        fprintf(stderr, "Memory allocation error\n");
        return 1;
    }

    hex_to_bytes(hex_input, input_bytes, hex_len);

    uint8_t output_bytes[64]; // Max size needed for SHA-512
    size_t output_bytes_size = 0;

    if (strcmp(hash_type, "md5") == 0) {
        Hacl_Hash_MD5_hash(output_bytes, input_bytes, (uint32_t)byte_len);
        output_bytes_size = 16;
    } else if (strcmp(hash_type, "sha1") == 0) {
        Hacl_Hash_SHA1_hash(output_bytes, input_bytes, (uint32_t)byte_len);
        output_bytes_size = 20;
    } else if (strcmp(hash_type, "sha224") == 0) {
        Hacl_Hash_SHA2_hash_224(output_bytes, input_bytes, (uint32_t)byte_len);
        output_bytes_size = 28;
    } else if (strcmp(hash_type, "sha256") == 0) {
        Hacl_Hash_SHA2_hash_256(output_bytes, input_bytes, (uint32_t)byte_len);
        output_bytes_size = 32;
    } else if (strcmp(hash_type, "sha384") == 0) {
        Hacl_Hash_SHA2_hash_384(output_bytes, input_bytes, (uint32_t)byte_len);
        output_bytes_size = 48;
    } else if (strcmp(hash_type, "sha512") == 0) {
        Hacl_Hash_SHA2_hash_512(output_bytes, input_bytes, (uint32_t)byte_len);
        output_bytes_size = 64;
    } else {
        fprintf(stderr, "Error: Unsupported hash type\n");
        free(input_bytes);
        return 1;
    }

    char hex_output[output_bytes_size * 2];  // Allocate enough space for hex
    bytes_to_hex(output_bytes, hex_output, output_bytes_size);

    fwrite(hex_output, 1, output_bytes_size * 2, stdout);
    fprintf(stderr, "\n");

    free(hex_input);
    free(input_bytes);
    return 0;
}