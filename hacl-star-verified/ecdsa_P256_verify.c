#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "Hacl_P256.h"
#include "Hacl_Hash_SHA2.h"

// Function to convert hex string to raw bytes
void hex_to_bytes(const char *hex, uint8_t *bytes, size_t hex_len) {
    for (size_t i = 0; i < hex_len / 2; i++) {
        sscanf(hex + (i * 2), "%2hhx", &bytes[i]);
    }
}

int main(int argc, char *argv[]) {
    if (argc != 6) {
        fprintf(stderr, "Usage: %s <hash_algo> <hashed_msg_hex> <public_key_hex> <signature_r_hex> <signature_s_hex>\n", argv[0]);
        return -1;
    }

    // Read command-line arguments
    char *hash_algo = argv[1];
    char *hashed_msg_hex = argv[2];
    char *public_key_hex = argv[3];
    char *signature_r_hex = argv[4];
    char *signature_s_hex = argv[5];

    // Convert hex input to raw bytes
    size_t msg_len = strlen(hashed_msg_hex) / 2;
    size_t pubkey_len = strlen(public_key_hex) / 2;
    size_t sig_r_len = strlen(signature_r_hex) / 2;
    size_t sig_s_len = strlen(signature_s_hex) / 2;

    if (pubkey_len != 64 || sig_r_len != 32 || sig_s_len != 32) {
        fprintf(stderr, "Error: Invalid public key or signature length\n");
        return -1;
    }

    uint8_t *hashed_msg = malloc(msg_len);
    uint8_t *public_key = malloc(pubkey_len);
    uint8_t *signature_r = malloc(sig_r_len);
    uint8_t *signature_s = malloc(sig_s_len);

    if (!hashed_msg || !public_key || !signature_r || !signature_s) {
        fprintf(stderr, "Memory allocation error\n");
        return -1;
    }

    hex_to_bytes(hashed_msg_hex, hashed_msg, strlen(hashed_msg_hex));
    hex_to_bytes(public_key_hex, public_key, strlen(public_key_hex));
    hex_to_bytes(signature_r_hex, signature_r, strlen(signature_r_hex));
    hex_to_bytes(signature_s_hex, signature_s, strlen(signature_s_hex));

    // Perform ECDSA verification using HACL*
    bool result = false;
    
    if (strcmp(hash_algo, "sha256") == 0) {
        result = Hacl_P256_ecdsa_verif_p256_sha2((uint32_t)msg_len, hashed_msg, public_key, signature_r, signature_s);
    } else if (strcmp(hash_algo, "sha384") == 0) {
        result = Hacl_P256_ecdsa_verif_p256_sha384((uint32_t)msg_len, hashed_msg, public_key, signature_r, signature_s);
    } else if (strcmp(hash_algo, "sha512") == 0) {
        result = Hacl_P256_ecdsa_verif_p256_sha512((uint32_t)msg_len, hashed_msg, public_key, signature_r, signature_s);
    } else {
        fprintf(stderr, "Unsupported hash algorithm\n");
        return -1;
    }

    // Cleanup
    free(hashed_msg);
    free(public_key);
    free(signature_r);
    free(signature_s);
    
    return result ? 1 : 0;
}