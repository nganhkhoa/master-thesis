mkdir -p fonts
pushd fonts

wget https://github.com/alerque/libertinus/releases/download/v7.051/Libertinus-7.051.zip
unzip Libertinus-7.051.zip
mv Libertinus-7.051 libertinus

wget https://font.download/dl/font/minion-pro.zip
unzip -d minion-pro minion-pro.zip

wget https://font.download/dl/font/latin-modern-mono.zip
unzip -d lmmono latin-modern-mono.zip

rm -rf *.zip

popd
