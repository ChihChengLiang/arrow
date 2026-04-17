# Arrow's Impossibility Theorem in Lean 4

A machine-checked proof of **Arrow's Impossibility Theorem**: no voting system with three or more alternatives can simultaneously satisfy Unanimity, Independence of Irrelevant Alternatives (IIA), and Non-Dictatorship.

The proof follows [Yu 2012](https://sites.math.rutgers.edu/~zeilberg/EM22/yu2012.pdf).

## Try it

**Prerequisites:** [Lean 4](https://leanprover.github.io/) with Lake (bundled in `elan`)

```sh
git clone https://github.com/ChihChengLiang/arrow
cd arrow
lake build
```

The build fetches Mathlib and verifies all proofs. Expect a few minutes on first run.

## Structure

| File | Contents |
|---|---|
| `Arrow/Basic.lean` | All definitions and the full proof |

## Key definitions

| Name | Description |
|---|---|
| `Preorder'` | Total preorder representing one voter's preference ranking |
| `Profile` | Assignment of a `Preorder'` to each voter |
| `SWF` | Social Welfare Function — maps a `Profile` to a society-wide `Preorder'` |
| `Unanimity` | If every voter prefers `a` to `b`, so does society |
| `AIIA` | Society's ranking of `a` vs `b` depends only on voters' rankings of that pair |
| `NonDictatorial` | No single voter's preferences determine society's ranking for every pair |
| `Impossibility` | No `SWF` satisfies all three properties when there are ≥ 3 alternatives |

## Reference

- Ning Neil Yu, "A one-shot proof of Arrow's impossibility theorem," 2012. ([PDF](https://sites.math.rutgers.edu/~zeilberg/EM22/yu2012.pdf))

## License

Apache 2.0 — see [LICENSE](LICENSE).
