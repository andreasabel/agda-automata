# Named arguments
s/\\AgdaSymbol{\\{}\([a-zA-Z?]\+\) \\AgdaSymbol{=}/\\AgdaSymbol{\\{}\\AgdaSymbol{\1} \\AgdaSymbol{=}/g

# Equational reasoning
# Only replace the eq-reasoning identifiers in code blocks,
# hence the initial ']' which comes from polytable
s/]\\AgdaFunction{≡⟨⟩}/]\\AgdaFunction{\\qquad≡⟨⟩}/g
s/]\\AgdaFunction{∼⟨}/]\\AgdaFunction{\\qquad∼⟨}/g

# Bound variable f needs extra spacing
s:\\AgdaBound{f}:\\AgdaBound\{\\,f\\,\}:g
s:\\AgdaBound{f′}:\\AgdaBound\{\\,f\\,′\}:g
s:\\AgdaBound{⟦f⟧}:\\AgdaBound\{⟦\\,f\\,⟧\}:g

# Δ′ has too much spacing
# s:Δ′:\\ensuremath\{\\Delta'\}:g
s:Δ′:Δ\\kern-1pt′:g
s:Δ″:Δ\\kern-1pt″:g

# Super- and subscripts.
#s/\\textasciicircum\([^\}]*\)‿\([^\}]*\)/\$\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\_\\AgdaFontStyle\{\\scriptscriptstyle \2\}\$/g

s/\\textasciicircum\([^\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g

#s/‿\([^\}]*\)/\$\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}\$/g

# Σ[ x ∈ X ] into (x : X) ×
#s/\\AgdaRecord{Σ\[} \(.*\) \\AgdaRecord{∈} \(.*\) \\AgdaRecord{]}/\\AgdaSymbol\{(\}\1 \\AgdaSymbol\{:\} \2\\AgdaSymbol\{)\} \\AgdaFunction\{×\}/g


# Bind. Discarded renderings of >>=
#s/>>=/\$\\mathbin\{>\\!\\!\\!>\\mkern-6.7mu=\}\$/g
#s/>>=/\\mathbin\{>\\!\\!\\!>\\mkern-6.7mu=\}/g
#s/>>=/\\ensuremath\{\\mathbin\{\\rangle\\rangle\{=\}\}\}/g
#s/>>=/\\ensuremath\{\\mathbin\{❭❭\{=\}\}\}/g # does not work, since
# ucs does not know these characters:
# ❬ MEDIUM LEFT-POINTING ANGLE BRACKET ORNAMENT
# ❭ MEDIUM RIGHT-POINTING ANGLE BRACKET ORNAMENT

# Bind >>=
s/∞>>=/\\ensuremath\{\\mathbin\{\\infty\\mkern-3mu\{>\}\\mkern-8.5mu\{>\}\\mkern-2mu\{=\}\}\}/g
s/>>=/\\ensuremath\{\\mathbin\{\{>\}\\mkern-8.5mu\{>\}\\mkern-2mu\{=\}\}\}/g

# Kleisli extension =<<
#s/=<</\$\\mathbin\{=\\mkern-6.7mu<\\!\\!\\!<\}\$/g
#s/=<</\\mathbin\{=\\mkern-6.7mu<\\!\\!\\!<\}/g
s/=<</\\ensuremath\{\\mathbin\{\{=\}\\mkern-2mu\{<\}\\mkern-8.5mu\{<\}\}\}/g

# Sequence >>
#s/>>/\$\\mathbin\{>\\!\\!\\!>}\$/g

# Map <$>
#s/<\\$>/\$\\mathop\{<\\!\\!\\!\\$\\!\\!\\!>\}\$/g
#s/<\\$>/\\mathop\{<\\!\\!\\!\\$\\!\\!\\!>\}/g
#s/<\\$>/\{<\}\{\\$\}\{>\}/g
#s/<\\$>/\\ensuremath\{\\langle\\$\\rangle\}/g
s/<\\$>/\\ensuremath\{\{<\}\\$\{>\}\}/g

# Append.
s/++/+\\!+/g

# Comments.
#s/AgdaComment{\-\-/AgdaComment\{\-\\!\-/g

