sudo docker pull ubuntu
sudo docker run -ti --rm ubuntu /bin/bash

cd ~/
home=$(pwd)
echo $home

rm -rf /$home/.armor
mkdir /$home/.armor

apt-get -y update
apt-get -y upgrade
apt-get install -y build-essential git nano opam python3 python3-pip python3-cryptography haskell-stack zlib1g-dev libncurses5-dev

wget https://www.python.org/ftp/python/2.7.18/Python-2.7.18.tgz
tar xzf Python-2.7.18.tgz
cd Python-2.7.18
./configure --enable-optimizations
make altinstall
ln -s /usr/local/bin/python2.7 /usr/bin/python2
cd $home
rm Python-2.7.18.tgz
python2 --version
python3 --version

stack update
stack upgrade

echo "PATH=$PATH:/$home/.local/bin" >> /$home/.bashrc
source /$home/.bashrc

git clone --depth 1 --branch v2.7.0.1 https://github.com/agda/agda.git
cd agda
export AGDAEXECDIR=/$home/.local/bin
stack install --stack-yaml stack-9.8.2.yaml --local-bin-path $AGDAEXECDIR
agda --version
cd $home

git clone https://github.com/Morpheus-Repo/Morpheus.git
cd Morpheus/oracle
ocamlc -o /$home/.armor/oracle pkcs1.mli pkcs1.ml oracle.ml
cd $home

opam init
eval $(opam env --switch=default)
opam install ppx_deriving_yojson zarith pprint "menhir>=20161115" sedlex process fix "wasm>=2.0.0" visitors ctypes-foreign ctypes uucp

opam pin add fstar --dev-repo

opam install z3 z3.4.8.5 --no-depexts
ln -s /$home/.opam/default/bin/z3 /usr/bin/z3-4.8.5
z3-4.8.5 --version

opam install karamel

git clone https://github.com/hacl-star/hacl-star.git
cd hacl-star/dist/gcc-compatible/
make
cd $home

git clone https://github.com/cwjnkins/armor-agda.git
cd armor-agda
git checkout crl-revocation
git pull
./compile.sh
cd $home