#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// #include <openssl/rsa.h>
// #include <openssl/pem.h>
// #include <openssl/evp.h>
// #include <openssl/ec.h>
// #include <openssl/x509.h>
// #include <openssl/bn.h>
#include <getopt.h>
#include <ctype.h>

#define MAX_CERTS 100
#define MAX_LINE_LEN 1024

typedef struct {
    char *tbs;
    char *signature;
    char *public_key;
    char *signoid;
    char *eku_purposes;
} Certificate;

typedef struct {
    char *tbs;
    char *signature;
    char *signoid;
} CRL;

// Define a struct for OID mapping
typedef struct {
    char *oid;
    char *algorithm;
} OIDMap;

// Define an array of OID mappings (simulating Python dictionary)
OIDMap sign_oid_map[] = {
    {"6 9 42 134 72 134 247 13 1 1 11", "sha256WithRSAEncryption"},
    {"6 9 42 134 72 134 247 13 1 1 12", "sha384WithRSAEncryption"},
    {"6 9 42 134 72 134 247 13 1 1 13", "sha512WithRSAEncryption"},
    {"6 9 42 134 72 134 247 13 1 1 14", "sha224WithRSAEncryption"},
    {"6 9 42 134 72 134 247 13 1 1 5", "sha1WithRSAEncryption"},
    {"6 9 42 134 72 134 247 13 1 1 4", "md5WithRSAEncryption"},
    {"6 8 42 134 72 206 61 4 3 2", "ecdsa-with-SHA256"},
    {"6 8 42 134 72 206 61 4 3 3", "ecdsa-with-SHA384"},
    {"6 8 42 134 72 206 61 4 3 4", "ecdsa-with-SHA512"},
    {NULL, NULL} // Sentinel value to mark the end of the array
};

// Function to compare OIDs while ignoring leading/trailing spaces
int compare_oids(const char *oid1, const char *oid2) {
    // Skip leading spaces in both strings
    while (*oid1 && isspace((unsigned char)*oid1)) oid1++;
    while (*oid2 && isspace((unsigned char)*oid2)) oid2++;

    // Compare character by character
    while (*oid1 && *oid2) {
        if (*oid1 != *oid2) return (*oid1 - *oid2);
        oid1++;
        oid2++;
    }

    // Skip trailing spaces in both strings
    while (*oid1 && isspace((unsigned char)*oid1)) oid1++;
    while (*oid2 && isspace((unsigned char)*oid2)) oid2++;

    return (*oid1 - *oid2); // Return difference if strings are not equal
}

// Function to look up OID algorithm safely
char *lookup_sign_oid(const char *oid) {
    if (!oid) return NULL;

    for (int i = 0; sign_oid_map[i].oid != NULL; i++) {
        if (compare_oids(sign_oid_map[i].oid, oid) == 0) {
            return (char *)sign_oid_map[i].algorithm; // Return found algorithm
        }
    }
    return NULL; // Return NULL if no match found
}

char *convert_to_hex(const char *value) {
    if (!value) return NULL;

    // Allocate enough memory for hex output (2 chars per byte + spaces)
    size_t len = strlen(value);
    char *hex_result = (char *)malloc(len * 3); // Worst case: space-separated numbers
    if (!hex_result) {
        fprintf(stderr, "Memory allocation failed\n");
        return NULL;
    }

    hex_result[0] = '\0'; // Initialize empty string

    char *token = strtok(strdup(value), " "); // Duplicate value for safe tokenization
    while (token) {
        int num = atoi(token);
        char buffer[4]; // Max: "FF " (3 chars + null terminator)
        snprintf(buffer, sizeof(buffer), "%02X ", num);
        strcat(hex_result, buffer);
        token = strtok(NULL, " ");
    }

    // Remove trailing space
    size_t hex_len = strlen(hex_result);
    if (hex_len > 0) {
        hex_result[hex_len - 1] = '\0';
    }

    return hex_result;
}

// Function to extract text between markers using strstr(), updating search position
char *extract_text(char **output_ptr, const char *start_marker, const char *end_marker) {
    char *start = strstr(*output_ptr, start_marker);
    if (!start) return NULL;
    start += strlen(start_marker); // Move past the marker

    char *end = strstr(start, end_marker);
    if (!end) return NULL;

    size_t len = end - start;
    char *result = (char *)malloc(len + 1);
    if (!result) return NULL;

    strncpy(result, start, len);
    result[len] = '\0';

    *output_ptr = end + strlen(end_marker); // Move search pointer forward
    return result;
}

void parse_output(const char *output, Certificate *certificates[], int *cert_count, CRL *crls[], int *crl_count) {
    *cert_count = 0;
    *crl_count = 0;
    char *search_position = (char *)output; // Pointer to track progress in output

    while (*cert_count < MAX_CERTS) {
        char *cert_text = extract_text(&search_position, "*******Output Certificate Start*******\n", "*******Output Certificate End*******\n");
        if (!cert_text) break;

        char *lines[5] = {NULL};
        char *token = strtok(cert_text, "\n");
        int i = 0;
        while (token && i < 5) {
            lines[i++] = strdup(token);
            token = strtok(NULL, "\n");
        }

        Certificate *cert = (Certificate *)malloc(sizeof(Certificate));
        cert->tbs = convert_to_hex(strdup(lines[0]));
        cert->signature = convert_to_hex(strdup(lines[1]));
        cert->public_key = convert_to_hex(strdup(lines[2]));
        char *signoid_value = lookup_sign_oid(lines[3]);
        cert->signoid = signoid_value ? strdup(signoid_value) : NULL;
        cert->eku_purposes = (i > 4) ? strdup(lines[4]) : NULL;

        certificates[(*cert_count)++] = cert;
        free(cert_text);
    }

    search_position = (char *)output; // Reset search position for CRLs
    while (*crl_count < MAX_CERTS) {
        char *crl_text = extract_text(&search_position, "*******Output CRL Start*******\n", "*******Output CRL End*******\n");
        if (!crl_text) break;

        char *lines[3] = {NULL};
        char *token = strtok(crl_text, "\n");
        int i = 0;
        while (token && i < 3) {
            lines[i++] = strdup(token);
            token = strtok(NULL, "\n");
        }

        CRL *crl = (CRL *)malloc(sizeof(CRL));
        crl->tbs = convert_to_hex(strdup(lines[0]));
        crl->signature = convert_to_hex(strdup(lines[1]));
        char *signoid_value = lookup_sign_oid(lines[2]);
        crl->signoid = signoid_value ? strdup(signoid_value) : NULL;

        crls[(*crl_count)++] = crl;
        free(crl_text);
    }
}

void free_certificates(Certificate *certificates[], int count) {
    for (int i = 0; i < count; i++) {
        free(certificates[i]->tbs);
        free(certificates[i]->signature);
        free(certificates[i]->public_key);
        free(certificates[i]->signoid);
        free(certificates[i]->eku_purposes);
        free(certificates[i]);
    }
}

void free_crls(CRL *crls[], int count) {
    for (int i = 0; i < count; i++) {
        free(crls[i]->tbs);
        free(crls[i]->signature);
        free(crls[i]->signoid);
        free(crls[i]);
    }
}

// Function to read a file into a string
// char *read_file(const char *filename) {
//     FILE *file = fopen(filename, "rb");
//     if (!file) {
//         fprintf(stderr, "Error: Unable to open file %s\n", filename);
//         return NULL;
//     }
//     fseek(file, 0, SEEK_END);
//     long length = ftell(file);
//     rewind(file);
    
//     char *buffer = (char *)malloc(length + 1);
//     if (!buffer) {
//         fprintf(stderr, "Error: Memory allocation failed\n");
//         fclose(file);
//         return NULL;
//     }
    
//     fread(buffer, 1, length, file);
//     buffer[length] = '\0';
//     fclose(file);
//     return buffer;
// }

// Function to execute external command and return output dynamically
char *run_external_program(const char *command) {
    FILE *fp;
    size_t buffer_size = 4096; // Initial buffer size
    size_t position = 0;
    char chunk[1024];

    // Allocate initial memory
    char *result = (char *)malloc(buffer_size);
    if (!result) {
        fprintf(stderr, "Memory allocation failed\n");
        return NULL;
    }
    result[0] = '\0'; // Initialize empty string

    fp = popen(command, "r");
    if (!fp) {
        fprintf(stderr, "Error executing command: %s\n", command);
        free(result);
        return NULL;
    }

    while (fgets(chunk, sizeof(chunk), fp) != NULL) {
        size_t chunk_len = strlen(chunk);

        // Resize buffer if needed
        if (position + chunk_len + 1 > buffer_size) { // +1 for null terminator
            buffer_size *= 2; // Double the buffer size
            char *new_result = (char *)realloc(result, buffer_size);
            if (!new_result) {
                fprintf(stderr, "Memory reallocation failed\n");
                free(result);
                pclose(fp);
                return NULL;
            }
            result = new_result;
        }

        // Append new chunk to result
        strcpy(result + position, chunk);
        position += chunk_len;
    }

    pclose(fp);
    return result;
}

// Function to verify RSA signature
// int verify_signature_rsa(const unsigned char *tbs, size_t tbs_len, 
//                          const unsigned char *signature, size_t sig_len, 
//                          RSA *public_key, const EVP_MD *md) {
//     EVP_PKEY *pkey = EVP_PKEY_new();
//     EVP_PKEY_assign_RSA(pkey, public_key);
//     EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    
//     if (EVP_DigestVerifyInit(ctx, NULL, md, NULL, pkey) != 1) {
//         fprintf(stderr, "Error: Digest Verify Init failed\n");
//         return 0;
//     }
//     if (EVP_DigestVerifyUpdate(ctx, tbs, tbs_len) != 1) {
//         fprintf(stderr, "Error: Digest Verify Update failed\n");
//         return 0;
//     }
//     int result = EVP_DigestVerifyFinal(ctx, signature, sig_len);
    
//     EVP_MD_CTX_free(ctx);
//     EVP_PKEY_free(pkey);
    
//     return result == 1 ? 1 : 0;
// }

// Function to parse arguments and execute verification
int main(int argc, char *argv[]) {
    char *executable = NULL;
    char *chain_file = NULL;
    char *trust_store = NULL;
    char *purpose = NULL;
    char *crl_file = NULL;

    int option;
    while ((option = getopt(argc, argv, "e:c:t:p:r:")) != -1) {
        switch (option) {
            case 'e':
                executable = optarg;
                break;
            case 'c':
                chain_file = optarg;
                break;
            case 't':
                trust_store = optarg;
                break;
            case 'p':
                purpose = optarg;
                break;
            case 'r':
                crl_file = optarg;
                break;
            default:
                fprintf(stderr, "Usage: %s -e <executable> -c <chain> [-t <trust_store>] [-p <purpose>] [-r <crl>]\n", argv[0]);
                return 1;
        }
    }

    if (!executable || !chain_file) {
        fprintf(stderr, "Error: Missing required arguments\n");
        return 1;
    }

    char command[512];
    
    if (purpose) {
        snprintf(command, sizeof(command), "%s --purpose %s %s", executable, purpose, chain_file);
    } else {
        snprintf(command, sizeof(command), "%s %s", executable, chain_file);
    }

    if (trust_store) snprintf(command + strlen(command), sizeof(command) - strlen(command), " --trust_store %s", trust_store);
    if (crl_file) snprintf(command + strlen(command), sizeof(command) - strlen(command), " --crl %s", crl_file);

    printf("Executing: %s\n", command);
    char *output = run_external_program(command);
    if (output) {
        printf("Output:\n%s\n", output);

        Certificate *certificates[MAX_CERTS];
        CRL *crls[MAX_CERTS];
        int cert_count = 0, crl_count = 0;

        parse_output(output, certificates, &cert_count, crls, &crl_count);

        // Print parsed results
        printf("\nParsed Certificates (%d):\n", cert_count);
        for (int i = 0; i < cert_count; i++) {
            printf("Certificate %d:\n", i + 1);
            printf("  TBS: %s\n", certificates[i]->tbs);
            printf("  Signature: %s\n", certificates[i]->signature);
            printf("  Public Key: %s\n", certificates[i]->public_key);
            printf("  Signoid: %s\n", certificates[i]->signoid);
            if (certificates[i]->eku_purposes)
                printf("  EKU: %s\n", certificates[i]->eku_purposes);
        }

        printf("\nParsed CRLs (%d):\n", crl_count);
        for (int i = 0; i < crl_count; i++) {
            printf("CRL %d:\n", i + 1);
            printf("  TBS: %s\n", crls[i]->tbs);
            printf("  Signature: %s\n", crls[i]->signature);
            printf("  Signoid: %s\n", crls[i]->signoid);
        }

        // Free memory
        free_certificates(certificates, cert_count);
        free_crls(crls, crl_count);

        free(output);
    }

    return 0;
}