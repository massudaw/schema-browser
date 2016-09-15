cat threepenny-layer.prof | ghc-prof-flamegraph > layer.folded
cat layer.folded | flamegraph.pl > layer.svg
chromium layer.svg
