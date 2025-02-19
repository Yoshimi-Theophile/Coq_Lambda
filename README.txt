build:

coq_makefile -f _CoqProject -o CoqMakeFile
make -f CoqMakeFile

clean:

make -f CoqMakeFile clean

- substitution
- type substitution
- proof of subst_typed
- change bidir into a predicate
- add shape-annotated planar lambda-terms
- do shape annotated bidir
- some predicate on the principal typing
- sigma satisfies constraints

G <= t => A　｜三 ->
s |= 三 ->
sG |- t : sA
