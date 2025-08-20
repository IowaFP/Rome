find . -type f -name '*.agdai' -delete

rm -rf ./CPP-Rome-supp-materials/
mkdir  ./CPP-Rome-supp-materials/
mkdir  ./CPP-Rome-supp-materials/Rome/

cp -rf ./Operational/* ./CPP-Rome-supp-materials/Rome/

rm -rf ./CPP-Rome-supp-materials/Rome/Writing/
rm -rf ./CPP-Rome-supp-materials/Rome/Types/Pre/
rm -rf ./CPP-Rome-supp-materials/Rome/Types/Checking.agda
rm -rf ./CPP-Rome-supp-materials/Rome/Types/SynAna.agda
rm -rf ./CPP-Rome-supp-materials/Rome/Types/Equivalence/Admissable.agda
rm -rf ./CPP-Rome-supp-materials/Rome/Types/Presentation.agda
rm -rf ./CPP-Rome-supp-materials/Rome/Types/Semantic/Examples.agda

rm -rf ./CPP-Rome-supp-materials/Rome/Terms/
mv ./CPP-Rome-supp-materials/Rome/AllTypes.agda ./CPP-Rome-supp-materials/Rome/All.agda

find ./CPP-Rome-supp-materials/ -name '*.agda' -exec sed -i -e 's/Rome\.Operational/Rome/g' {} \;

cd ./CPP-Rome-supp-materials/
agda ./Rome/All.agda 
find . -type f -name '*.agdai' -delete
cd -

rm Rome-supp-CPP26.zip & zip -r Rome-supp-CPP26.zip ./CPP-Rome-supp-materials/;
