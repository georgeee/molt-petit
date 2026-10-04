import re

with open('paper/molt.tex') as f:
    text = f.read()

# Let's split into lines and also track line numbers.
lines = text.splitlines()

# We want to identify sentences. A sentence typically ends with . ? ! followed by space or newline, or \end{...}.
# But simpler: scan paragraph by paragraph or find matches of \code{...}, "machine-checked", "proved", "formalized", "formalised".

# Let's collect all non-code identifiers or identify which \code{...} refer to Lean declarations.
