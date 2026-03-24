mkdir -p fonts
pushd fonts

wget https://github.com/alerque/libertinus/releases/download/v7.051/Libertinus-7.051.zip
unzip Libertinus-7.051.zip
mv Libertinus-7.051 libertinus
rm -rf *.zip

popd
