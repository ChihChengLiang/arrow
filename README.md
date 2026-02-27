# (WIP) Arrow's impossibility theorem in Lean 4

This is an attempt to implement Arrow's impossibility theorem, [Yu 2012](https://sites.math.rutgers.edu/~zeilberg/EM22/yu2012.pdf) specifically, in Lean to practice the language.

This is still WIP. I'm stuck at the formula marked with `(*)` in the paper.

I made some wrong turns.

- I made the preference preorder "total." So that weak preference in the paper was temporarily ignored.
- I haven't figured out how to build a preference profile that behave like the second one in the paper.


In another branch, I also tried Barbera 1980, which defines ideas more formally.

[Wiedijk 2009](https://repository.ubn.ru.nl/bitstream/handle/2066/75428/75428.pdf?sequence=1) formalizes Arrow's theorem in Mizar language. I haven't dived into this.
