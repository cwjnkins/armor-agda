
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

## How to Install Agda
### Step 1: Stack (`haskell-stack`) Installation
```
    sudo apt install haskell-stack
    stack update
    stack upgrade
```
**Remark:** This step will create ~/.local/bin if it does not exist. If so,
then (on some systems) to ensure that this directory is listed in your $PATH
variable you can log off and log back in again.

### Step 2: Agda Installation
Armor uses Agda v2.6.2.2. To install this from source, choose a directory
listed in your $PATH environment variable (such as `~/.local/bin`) for the
Agda executable. We will refer to this as $AGDAEXECDIR in what follows:
**please replace all occurrences of $AGDAEXECDIR with this, or set this as
an environment variable**

Open a terminal in some working directory and perform the following steps. 
1.  Install dependencies for Agda
        `sudo apt install zlib1g-dev libncurses5-dev`
2.  Checkout Agda source repository
        `git clone --depth 1 --branch v2.6.2.2 https://github.com/agda/agda.git`
        `cd agda`
3.  Build Agda (this will take a while: stack may need to install the
    specific GHC and the Haskell base libraries, and then building Agda itself
    takes a long time).
        `stack install --stack-yaml stack-8.8.4.yaml --local-bin-path $AGDAEXECDIR`

4.  Confirm Agda is installed correctly. The result of `agda --version` should be
        `Agda version 2.6.2.2-442c76b`

## Build ARMOR-agda
`./compile.sh`

## How to run ARMOR-agda
### Option 1: Certificate Chain Validation
`./src/Main [--purpose <expected_purpose>] <pem/crt input chain> <root CA store> `

or

`./src/Main --DER [--purpose <expected_purpose>] <der input chain> <root CA store>`

### Option 2: Parsing a single certificate and enforcing relevant semantic rules
`./src/Main [--purpose <expected_purpose>] <pem/crt input certificate>`

or

`./src/Main --DER [--purpose <expected_purpose>] <der input certificate>`

##### *** List of Supported Purposes ***
`serverAuth`, `clientAuth`, `codeSigning`, `emailProtection`, `timeStamping`, `ocspSigning`

## Cleanup ARMOR-agda
`./cleanup.sh`
