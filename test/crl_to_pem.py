import os
import argparse
import subprocess
import sys

def convert_and_merge(input_directory, merged_pem_file):
    # Ensure the input directory exists
    if not os.path.isdir(input_directory):
        print(f"Error: Directory '{input_directory}' does not exist.")
        sys.exit(1)

    # Get all .crl files in the specified directory
    der_files = [f for f in os.listdir(input_directory) if f.endswith('.crl')]

    if not der_files:
        print("No .crl files found in the directory.")
        sys.exit(1)

    merged_pem_path = os.path.join(input_directory, merged_pem_file)

    # Convert and merge certificates
    with open(merged_pem_path, "wb") as merged_file:
        for der_file in der_files:
            der_path = os.path.join(input_directory, der_file)
            pem_file = der_path.replace(".crl", ".pem")

            # Construct OpenSSL command
            openssl_cmd = ["openssl", "crl", "-inform", "DER", "-in", der_path, "-out", pem_file]
            print(f"Running command: {' '.join(openssl_cmd)}")

            try:
                # Convert DER to PEM using OpenSSL
                subprocess.run(openssl_cmd, check=True)

                # Append PEM content to the merged file
                with open(pem_file, "rb") as pem:
                    merged_file.write(pem.read())

                # Remove the individual PEM file
                os.remove(pem_file)
            except subprocess.CalledProcessError:
                print(f"Failed to convert {der_file} to PEM format.")
                sys.exit(1)

    print(f"All DER certificates have been converted and merged into {merged_pem_path}.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert DER certificates to PEM and merge them into one file.")
    parser.add_argument("folder", type=str, help="Path to the folder containing DER files.")
    parser.add_argument("output_file", type=str, help="Name of the merged PEM file.")

    args = parser.parse_args()
    convert_and_merge(args.folder, args.output_file)
