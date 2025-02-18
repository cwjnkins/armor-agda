#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Hash_MD5.h"
#include "Hacl_Hash_SHA1.h"

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

// Convert hex to raw bytes
void hex_to_bytes(const char *hex, uint8_t *bytes, size_t hex_len) {
    for (size_t i = 0; i < hex_len / 2; i++) {
        sscanf(hex + (i * 2), "%2hhx", &bytes[i]);
    }
}

int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s <hash_type> <hex-encoded input>\n", argv[0]);
        return 1;
    }

    char *hash_type = argv[1];
    char *hex_input = argv[2];
    size_t hex_len = strlen(hex_input);

    if (hex_len % 2 != 0) {
        fprintf(stderr, "Error: Invalid hex input length\n");
        return 1;
    }

    if (!is_valid_hex(hex_input)) {
        fprintf(stderr, "Error: Input contains non-hex characters\n");
        return 1;
    }

    size_t byte_len = hex_len / 2;
    if (byte_len == 0) {
        fprintf(stderr, "Error: Input cannot be empty\n");
        return 1;
    }

    uint8_t *input_bytes = malloc(byte_len);
    if (!input_bytes) {
        fprintf(stderr, "Memory allocation error\n");
        return 1;
    }

    hex_to_bytes(hex_input, input_bytes, hex_len);

    uint8_t output[64]; // Max size needed for SHA-512
    size_t output_size = 0;

    if (strcmp(hash_type, "md5") == 0) {
        Hacl_Hash_MD5_hash(output, input_bytes, (uint32_t)byte_len);
        output_size = 16;
    } else if (strcmp(hash_type, "sha1") == 0) {
        Hacl_Hash_SHA1_hash(output, input_bytes, (uint32_t)byte_len);
        output_size = 20;
    } else if (strcmp(hash_type, "sha224") == 0) {
        Hacl_Hash_SHA2_hash_224(output, input_bytes, (uint32_t)byte_len);
        output_size = 28;
    } else if (strcmp(hash_type, "sha256") == 0) {
        Hacl_Hash_SHA2_hash_256(output, input_bytes, (uint32_t)byte_len);
        output_size = 32;
    } else if (strcmp(hash_type, "sha384") == 0) {
        Hacl_Hash_SHA2_hash_384(output, input_bytes, (uint32_t)byte_len);
        output_size = 48;
    } else if (strcmp(hash_type, "sha512") == 0) {
        Hacl_Hash_SHA2_hash_512(output, input_bytes, (uint32_t)byte_len);
        output_size = 64;
    } else {
        fprintf(stderr, "Error: Unsupported hash type\n");
        free(input_bytes);
        return 1;
    }

    fwrite(output, 1, output_size, stdout);
    fprintf(stderr, "\n");

    free(input_bytes);
    return 0;
}
