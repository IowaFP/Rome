find . -type f -name '*.agdai' -delete

rm -rf ./Rome-supp-materials/
mkdir  ./Rome-supp-materials/
mkdir  ./Rome-supp-materials/Rome/

cp -rf ./Operational/* ./Rome-supp-materials/Rome/

rm -rf ./Rome-supp-materials/Rome/Writing/
rm -rf ./Rome-supp-materials/Rome/Types/Pre/
rm -rf ./Rome-supp-materials/Rome/Types/Checking.agda
rm -rf ./Rome-supp-materials/Rome/Types/Presentation.agda
rm -rf ./Rome-supp-materials/Rome/Types/Semantic/Examples.agda

rm -rf ./Rome-supp-materials/Rome/Terms/Examples.agda 
rm -rf ./Rome-supp-materials/Rome/Terms/Examples.agda 
rm -rf ./Rome-supp-materials/Rome/Terms/Theorems/Completeness.agda
rm -rf ./Rome-supp-materials/Rome/Terms/Theorems/Soundness.agda

find ./Rome-supp-materials/ -name '*.agda' -exec sed -i -e 's/Rome\.Operational/Rome/g' {} \;

cd ./Rome-supp-materials/
agda --html ./Rome/All.agda 
find . -type f -name '*.agdai' -delete
cd -

rm Rome-supp-POPL26.zip & zip -r Rome-supp-POPL26.zip ./Rome-supp-materials/;
