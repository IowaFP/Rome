all: clean build html

clean:
	@find . -type f -name '*.agdai' -delete

build:
	agda ./Operational/All.agda

html:
	rm -rf ./html/
	agda --html ./All.agda

supp: clean
	rm -rf ./Rome-supp-materials/
	mkdir  ./Rome-supp-materials/
	mkdir  ./Rome-supp-materials/Rome/

	cp -rf ./Rome/Operational/* ./Rome-supp-materials/Rome/

	rm -rf ./Rome-supp-materials/Rome/Writing/
	rm -rf ./Rome-supp-materials/Rome/Types/Pre/
	rm -rf ./Rome-supp-materials/Rome/Types/Checking.agda
	rm -rf ./Rome-supp-materials/Rome/Types/Presentation.agda
	rm -rf ./Rome-supp-materials/Rome/Types/Semantic/Examples.agda

	rm -rf ./Rome-supp-materials/Rome/Terms/Examples.agda 
	rm -rf ./Rome-supp-materials/Rome/Terms/Examples.agda 
	rm -rf ./Rome-supp-materials/Rome/Terms/Theorems/Completeness.agda
	rm -rf ./Rome-supp-materials/Rome/Terms/Theorems/Soundness.agda

	rm Rome-supp-POPL26.zip & zip -r Rome-supp-POPL26.zip ./Rome-supp-materials/;
