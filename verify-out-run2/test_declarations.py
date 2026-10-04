import subprocess
import re

lake_cmd = open('verify-out/lake-cmd.txt').read().strip()
print(f"Lake command: {lake_cmd}")
