%.cmo : %.ml
	ocamlc -annot $<

all : interp.cmo
clean:; rm -f *.annot *.cmi *.cmo a.out

