#! /bin/bash

# Byzantine Fault Tolerant Consensus Verification in Agda, version 0.9.
#
# Copyright (c) 2020 Oracle and/or its affiliates.
# Licensed under the Universal Permissive License v 1.0 as shown at https://oss.oracle.com/licenses/upl/

BASE64ENCDEC_TCB_PAT='src/Armor/Binary/(UInt6\.agda|.*TCB\.agda)'
FOREIGN_TCB_PAT='src/Armor/(Foreign/.*|IO\.agda|Main\.agda)'
GENERIC_GRAMMAR_TCB_PAT='src/Armor/(Grammar/(.*TCB\.agda|.*Base\.agda|Parser/(Completeness\.agda|Core\.agda|Maximal\.agda)))'
X509_GRAMMAR_TCB_PAT='^(?!(.*Semantic.*))(src/Armor/Data/(Base64/.*TCB|PEM/.*TCB|Unicode/.*TCB|(X509/.*TCB)|X690-DER/.*TCB))'
X509_SEMANTIC_TCB_PAT='src/Armor/Data/X509/Semantic/(Cert/R.*\.agda|Cert/Utils\.agda|Chain/(NameMatch|R.*|TCB\.agda))'
STRINGPREP_PAT='src/Armor/Data/X509/Semantic/StringPrep'

EXCLUDE_LINE_PAT='^(?!\h*(--|import|open))'

echo '{-# OPTIONS --sized-types --guardedness #-}' > src/TCB.agda
echo "module TCB where" >> src/TCB.agda
for f in $(git ls-files | grep -P "${BASE64ENCDEC_TCB_PAT}|${FOREIGN_TCB_PAT}|${GENERIC_GRAMMAR_TCB_PAT}|${X509_GRAMMAR_TCB_PAT}|${X509_SEMANTIC_TCB_PAT}|${STRINGPREP_PAT}")
do
    echo "$f" \
      | sed 's/\.agda//' \
      | sed 's/src.//' \
      | sed 's!/!\.!g' \
      | sed 's/^/import /' >> src/TCB.agda
done

# report TCB LoC
echo "Base64 enc/dec TCB: $(git ls-files | grep -P "${BASE64ENCDEC_TCB_PAT}" | xargs cat | grep -P "${EXCLUDE_LINE_PAT}" | wc -l)"
echo "X.509/X690-DER/PEM parser TCB: $(git ls-files | grep -P "${GENERIC_GRAMMAR_TCB_PAT}|${X509_GRAMMAR_TCB_PAT}" | xargs cat | grep -P "${EXCLUDE_LINE_PAT}" | wc -l)"
echo "X.509 semantic TCB: $(git ls-files | grep -P "${X509_SEMANTIC_TCB_PAT}" | xargs cat | grep -P "${EXCLUDE_LINE_PAT}" | wc -l)"
echo "LDAP StringPrep TCB: $(git ls-files | grep -P "${STRINGPREP_PAT}" | xargs cat | grep -P "${EXCLUDE_LINE_PAT}" | wc -l)"
echo "Foreign/IO TCB: $(git ls-files | grep -P "${FOREIGN_TCB_PAT}" | xargs cat | grep -P "${EXCLUDE_LINE_PAT}" | wc -l)"
