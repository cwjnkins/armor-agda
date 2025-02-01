import subprocess
import sys
import re
import argparse
import os
from dataclasses import dataclass, field
from typing import List, Optional

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

def run_external_program(executable, purpose, certs, trusted_certs, crls=None):
    try:
        command = f"{executable}"
        
        # Add the purpose if provided
        if purpose:
            command += f" --purpose {purpose}"
        
        # Add the pem files
        command += f" {certs} {trusted_certs}"
        
        # Add the CRL file if provided
        if crls:
            command += f" {crls}"

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
    crl_data = None
    
    cert_blocks = re.findall(r"\*{7}Output Certificate Start\*{7}\n(.*?)\n\*{7}Output Certificate End\*{7}", output, re.DOTALL)
    if cert_blocks:
        for block in cert_blocks:
            lines = [line.strip() for line in block.strip().split("\n")]
            tbs, signature, public_key, signoid = map(convert_to_hex, lines[:4])
            eku_purposes = lines[4].rstrip(" @@").split(" @@ ") if len(lines) > 4 and lines[4] else []
            certificates.append(Certificate(
                tbs=tbs,
                signature=signature,
                public_key=public_key,
                signoid=signoid,
                eku_purposes=eku_purposes
            ))
    
    crl_match = re.search(r"\*{7}Output CRL Start\*{7}\n(.*?)\n\*{7}Output CRL End\*{7}", output, re.DOTALL)
    if crl_match:
        lines = [line.strip() for line in crl_match.group(1).strip().split("\n")]
        if len(lines) == 3:
            crl_data = CRL(
                tbs=convert_to_hex(lines[0]),
                signature=convert_to_hex(lines[1]),
                signoid=convert_to_hex(lines[2])
            )
    
    return certificates, crl_data

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
    parser.add_argument('--trust_store', type=str, default='/etc/ssl/certs/ca-certificates.crt', help='Trust anchor location; default=/etc/ssl/certs/ca-certificates.crt')
    parser.add_argument('--purpose', type=str, help='Optional Expected purpose for end-user certificate: serverAuth, clientAuth, codeSigning, emailProtection, timeStamping, or OCSPSigning')
    parser.add_argument('--crl', type=str, help='Optional CRL file location')

    # Parse the arguments
    args = parser.parse_args()

    # Perform sanity checks
    if not check_file_exists(args.executable, "Executable"):
        sys.exit(1)
    
    if not check_file_exists(args.chain, "Certificate chain"):
        sys.exit(1)
    
    if not check_file_exists(args.trust_store, "Trust store"):
        sys.exit(1)
    
    if args.crl and not check_file_exists(args.crl, "CRL"):
        sys.exit(1)

    # Run the external program using the provided arguments
    output = run_external_program(args.executable, args.purpose, args.chain, args.trust_store, args.crl)
    
    if output:
        certificates, crl_data = parse_output(output)

        if len(certificates) > 0:
            print("Parsed Certificates:", certificates)
        if crl_data:
            print("Parsed CRL:", crl_data)
