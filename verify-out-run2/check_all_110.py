import subprocess

lake_cmd = open('verify-out/lake-cmd.txt').read().strip()

with open('verify-out/get_lean_names.py') as f:
    pass

# We have the 110 symbols. Let's write a lean file checking each one with Molt.Name, MoltPetit.Model.Name, Rust.Name, etc.
