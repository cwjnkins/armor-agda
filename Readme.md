
# ARMOR Agda Module


## Directory

- Source (clickable HTML): [html/Everything.html](html/Everything.html)
    
    Use the "View raw" option at the top left
    
    -   [PEM](html/Armor.Data.PEM.html), [X.509](html/Armor.Data.X509.html), and [X.690-DER](html/Armor.Data.X690-DER.html) parsers modules
    -   [Generic soundness and completeness results](html/Armor.Grammar.Parser.Completeness.html)
    -   [Chain builder](html/Armor.Data.X509.Semantic.Chain.Builder.html)
    -   Semantic checks
        -   [Certificate](html/Armor.Data.X509.Semantic.Cert.html)
        -   [Chain](html/Armor.Data.X509.Semantic.Chain.html)

## Prerequisites
- `Agda version 2.6.2.2-442c76b`

## Build and Install

`./compile.sh`

## Cleanup

`./cleanup.sh`

## How to run
`./src/Main <pem/crt input chain> <root CA store>`
 
or

`./src/Main --DER <der input chain> <root CA store>`


