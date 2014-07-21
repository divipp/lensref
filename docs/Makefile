
Introduction.pdf: Introduction.pandoc dotplugin
	pandoc -N -f markdown+lhs -t latex --latex-engine=xelatex --filter ./dotplugin $< -o $@

dotplugin: DotPlugin.hs
	ghc --make $< -o $@


