build:

coq_makefile -f _CoqProject -o CoqMakeFile
make -f CoqMakeFile

clean:

make -f CoqMakeFile clean
