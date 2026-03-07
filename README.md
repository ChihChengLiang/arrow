# Arrow's impossibility theorem in Lean 4

This is an attempt to implement Arrow's impossibility theorem, [Yu 2012](https://sites.math.rutgers.edu/~zeilberg/EM22/yu2012.pdf) specifically, in Lean to practice the language.

It's completed now, with some small issues to fix.

- remove antisymm from the Preorder. The paper asks a complete, reflexive, and transitive preference. The closest thing in Lean is Preorder with total property.
- `n_ab_pivotal_bc_cb`, and some other lemmas seem to be overly complicated.

In another branch, I also tried [Barbera 1980](http://pareto.uab.es/sbarbera/versions%20noves/SB%20Pivotal%20voters%20ELetters1980.pdf), which defines ideas more formally. (Unfinished)

[Wiedijk 2009](https://repository.ubn.ru.nl/bitstream/handle/2066/75428/75428.pdf?sequence=1) formalizes Arrow's theorem in Mizar language. I haven't dived into this.
