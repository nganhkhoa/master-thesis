mkdir -p fonts
pushd fonts

wget https://font.download/dl/font/minion-pro.zip
unzip -d minion-pro minion-pro.zip

wget https://font.download/dl/font/latin-modern-mono.zip
unzip -d lmmono latin-modern-mono.zip

# not needed, but just download as well
wget https://font.download/dl/font/stix-two-text.zip
unzip -d stix-two stix-two-text.zip

wget https://font.download/dl/font/stix-two-math.zip
unzip -d stix-two stix-two-math.zip

rm -rf *.zip

popd
