all: clean build html
	+make -f Makefile.coq all

clean:
	@find . -type f -name '*.agdai' -delete

build:
	agda ./ROmega/All.agda

html:
	rm -rf ./html/
	agda --html ./Rome.agda

supp: clean
	rm -rf ./Rome-supp-materials/
	mkdir  ./Rome-supp-materials/
	cp -rf ./Rome/ ./Rome-supp-materials/
	cp -rf ./Rome.agda ./Rome-supp-materials/
	cp -rf ./IndexCalculus/ ./Rome-supp-materials/
	cp -rf ./IndexCalculus.agda ./Rome-supp-materials/	
	cp -rf ./Preludes/ ./Rome-supp-materials/	
	cp -rf ./Prelude.agda ./Rome-supp-materials/	
	cp -rf ./Shared/ ./Rome-supp-materials/	
	cp     ./README.md ./Rome-supp-materials/
	rm -rf ./Rome-supp-materials/Rome/Programs/
	rm -rf ./Rome-supp-materials/Rome/Programs/
	rm -rf ./Rome-supp-materials/IndexCalculus/Trash/
	rm -rf ./Rome-supp-materials/Rome/Examples/
	rm Rome-supp-POPL25.zip & zip -r Rome-supp-POPL25.zip ./Rome-supp-materials/;
