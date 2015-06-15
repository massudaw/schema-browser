cabal build && GHCRTS='-M2G'  dist/build/layer/layer academia academia postgres queijo aluno +RTS -p
cat layer.prof | .cabal-sandbox/bin/ghc-prof-flamegraph > layer.folded
cat layer.folded | flamegraph.pl > layer.svg
chromium layer.svg
