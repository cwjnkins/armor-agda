import subprocess
import sys
import re
import argparse
import os
from dataclasses import dataclass, field
from typing import List, Optional

from cryptography.hazmat.primitives.asymmetric.rsa import *
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.backends import default_backend
from hashlib import *
from cryptography.hazmat.primitives.serialization import load_der_public_key

@dataclass
class Certificate:
    tbs: str
    signature: str
    public_key: str
    signoid: str
    eku_purposes: List[str] = field(default_factory=list)

@dataclass
class CRL:
    tbs: str
    signature: str
    signoid: str

def convert_to_hex(value: str) -> str:
    """Converts a space-separated string of integers to uppercase two-digit hexadecimal format."""
    return " ".join(f"{int(num):02X}" for num in value.split())


# Mapping of OID to RSA signature algorithms
RSA_SIGNATURE_ALGOS = {
    "sha256WithRSAEncryption": sha256,
    "sha384WithRSAEncryption": sha384,
    "sha512WithRSAEncryption": sha512,
    "sha224WithRSAEncryption": sha224,
    "sha1WithRSAEncryption": sha1
}

sign_oid_map = {
    "6 9 42 134 72 134 247 13 1 1 11": "sha256WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 12": "sha384WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 13": "sha512WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 14": "sha224WithRSAEncryption",
    "6 9 42 134 72 134 247 13 1 1 5": "sha1WithRSAEncryption",
    '6 8 42 134 72 206 61 4 3 1': 'ecdsa-with-SHA224',
    '6 8 42 134 72 206 61 4 3 2': 'ecdsa-with-SHA256',
    '6 8 42 134 72 206 61 4 3 3': 'ecdsa-with-SHA384',
    '6 8 42 134 72 206 61 4 3 4': 'ecdsa-with-SHA512',
    '6 9 42 134 72 134 247 13 1 1 2': "md2WithRSAEncryption",
    '6 9 42 134 72 134 247 13 1 1 3': "md4WithRSAEncryption",
    '6 9 42 134 72 134 247 13 1 1 4': "md5WithRSAEncryption"
}

# Insecure algorithms list
INSECURE_ALGORITHMS = {

}

### specific to RSA public key, signature algorithm
def verify_signature_with_secure_algorithm(signature, sign_algo, tbs_bytes, public_key, i):
    """Helper function to handle common signature verification logic."""
    try:
        # Get the corresponding hash function for the RSA signature algorithm
        if sign_algo in RSA_SIGNATURE_ALGOS and isinstance (public_key, RSAPublicKey):
            signature_mod = pow(int.from_bytes(signature, byteorder='big'),
                    public_key.public_numbers().e,
                    public_key.public_numbers().n)
            signature_mod_hex = '00' + signature_mod.to_bytes((signature_mod.bit_length() + 7) // 8, byteorder='big').hex()
            hash_func = RSA_SIGNATURE_ALGOS[sign_algo]
            tbs_hash = hash_func(tbs_bytes).hexdigest()
            n_length = public_key.public_numbers().n.bit_length() // 8
            hash_size = hash_func().digest_size * 8  # Size in bits
            # Build the command for morpheous RSA signature verirification
            cmd = ['./morpheous-bin', signature_mod_hex, str(n_length), tbs_hash, str(hash_size)]
            morpheous_res = subprocess.getoutput(' '.join(cmd))
            print(morpheous_res)
            return morpheous_res
        else:
            print(f"Signature algorithm {sign_algo} is not supported - signature verification skipped for certificate {i}.")
            return "true"
    except Exception as e:
        print(f"Error during signature verification for certificate {i}: {e}")
        return "false"

def verifySign(signature, sign_algo, tbs_bytes, public_key, i):
    """Verifies the signature of a certificate using the provided public key and signature algorithm."""
    # Check if the signature algorithm is insecure
    if sign_algo in INSECURE_ALGORITHMS:
        print(f"Signature algorithm {INSECURE_ALGORITHMS[sign_algo]} is insecure in certificate {i}.")
        return "false"
    
    # Handle signature verification based on the algorithm
    return verify_signature_with_secure_algorithm(signature, sign_algo, tbs_bytes, public_key, i)

def verifySignatures(certificates):
    res = "true"

    for i in range(1, len(certificates)):
        cert = certificates[i - 1]
        signature = bytes.fromhex(cert.signature[3:]) if cert.signature.startswith("00 ") else bytes.fromhex(cert.signature)
        sign_algo = cert.signoid
        tbs_bytes = bytes.fromhex(cert.tbs)
        public_key = load_der_public_key(bytes.fromhex(certificates[i].public_key), backend=default_backend())
                
        # Verify signature using the provided function
        verification_result = verifySign(signature, sign_algo, tbs_bytes, public_key, i)
        
        if verification_result == "false":
            print(f"Failed to verify signature of certificate {i}")
            res = "false"
            break    
    return res

def run_external_program(executable, purpose, certs, trusted_certs=None, crls=None):
    try:
        command = f"{executable}"
        
        # Add the purpose if provided
        if purpose:
            command += f" --purpose {purpose}"

        command += f" {certs}"
        
        if trusted_certs:
            command += f" --trust_store {trusted_certs}"
        
        # Add the CRL file if provided
        if crls:
            command += f" --crl {crls}"

        print("Command Executed:", command)
        
        # Run the command as a whole string
        process = subprocess.run(command, 
            shell=True, 
            capture_output=True, 
            text=True)
        
        # Capture the output and error streams
        stdout, stderr = process.stdout, process.stderr
        
        if stderr:
            print(f"{stderr}", file=sys.stderr)
        
        return stdout
    except Exception as e:
        print(f"An error occurred: {e}", file=sys.stderr)
        return None

def parse_output(output):
    certificates = []
    crls = []
    
    cert_blocks = re.findall(r"\*{7}Output Certificate Start\*{7}\n(.*?)\n\*{7}Output Certificate End\*{7}", output, re.DOTALL)
    if cert_blocks:
        for block in cert_blocks:
            lines = [line.strip() for line in block.strip().split("\n")]
            tbs, signature, public_key = map(convert_to_hex, lines[:3])
            signoid = sign_oid_map[lines[3]] if lines[3] in sign_oid_map else None
            eku_purposes = lines[4].rstrip(" @@").split(" @@ ") if len(lines) > 4 and lines[4] else []
            certificates.append(Certificate(
                tbs=tbs,
                signature=signature,
                public_key=public_key,
                signoid=signoid,
                eku_purposes=eku_purposes
            ))
    
    crl_blocks = re.findall(r"\*{7}Output CRL Start\*{7}\n(.*?)\n\*{7}Output CRL End\*{7}", output, re.DOTALL)
    if crl_blocks:
        for block in crl_blocks:
            lines = [line.strip() for line in block.strip().split("\n")]
            crls.append(CRL(
                tbs, signature = map(convert_to_hex, lines[:2]),
                signoid=sign_oid_map[lines[2]] if lines[2] in sign_oid_map else None
            ))
    
    return certificates, crls

def check_file_exists(file_path: str, file_type: str) -> bool:
    """Check if a file exists and is a valid file."""
    if not os.path.isfile(file_path):
        print(f"Error: {file_type} file '{file_path}' does not exist or is not a file.", file=sys.stderr)
        return False
    return True

if __name__ == "__main__":
    # Define command-line argument parsing using argparse
    parser = argparse.ArgumentParser(description='ARMOR command-line arguments')
    parser.add_argument('--executable', type=str, required=True, help='Path to the external executable')
    parser.add_argument('--chain', type=str, required=True, help='Input certificate chain location')
    # parser.add_argument('--trust_store', type=str, default='/etc/ssl/certs/ca-certificates.crt', help='Trust anchor location; default=/etc/ssl/certs/ca-certificates.crt')
    parser.add_argument('--trust_store', type=str, help='Trust anchor location')
    parser.add_argument('--purpose', type=str, help='Optional Expected purpose for end-user certificate: serverAuth, clientAuth, codeSigning, emailProtection, timeStamping, or OCSPSigning')
    parser.add_argument('--crl', type=str, help='Optional CRL file location')

    # Parse the arguments
    args = parser.parse_args()

    # Perform sanity checks
    if not check_file_exists(args.executable, "Executable"):
        sys.exit(1)
    
    if not check_file_exists(args.chain, "Certificate chain"):
        sys.exit(1)
    
    if args.trust_store and not check_file_exists(args.trust_store, "Trust store"):
        sys.exit(1)
    
    if args.crl and not check_file_exists(args.crl, "CRL"):
        sys.exit(1)

    # Run the external program using the provided arguments
    output = run_external_program(args.executable, args.purpose, args.chain, args.trust_store, args.crl)
    
    if output:
        certificates, crls = parse_output(output)

        if len(certificates) > 0:
            print("Parsed Certificates:", certificates)
        if len(crls) > 0:
            print("Parsed CRL:", crls)

        sig_verify_chain = verifySignatures(certificates)
        print("Certificate Chain Signature Verification:", sig_verify_chain)
