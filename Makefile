
all: tutorial.v
	coqc -R '../Kami' 'Kami' -R '../bbv/theories' 'bbv' -R '.' 'tutorial' tutorial.v

clean: tutorial.vo
	rm *.vo *.glob
