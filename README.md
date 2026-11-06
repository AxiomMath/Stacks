[![](logo.svg)](https://axiommath.ai/)

# The Stacks Project in Lean

* [Website](https://stacks.axiommath.ai/)

A Lean 4 formalization of [the Stacks Project](https://stacks.math.columbia.edu/), the open-source reference work on algebraic geometry, built on [Mathlib](https://github.com/leanprover-community/mathlib4). The compiler version is pinned in [lean-toolchain](lean-toolchain).

The project's reported coverage is every Stacks tag with formalizable content; remaining examples, exercises and remarks are contributor tasks. A tag can describe a partial result, so inspect the declaration's statement and tag comment before reusing it. Declarations also carry references to Grothendieck's *Éléments de géométrie algébrique* (EGA) and *Séminaire de géométrie algébrique* (SGA).

**Start here:** [find a tag](#finding-a-tag) · [choose an import](#structure) · [check a result](#checking-a-result) · [contribute](#contributing)

Coverage, human review and proof certification are separate questions. The intended trust boundary is Lean's kernel with only the three standard axioms, without `sorry` or `native_decide`. Those are verification requirements, not a certificate for an arbitrary checkout; see [Checking a result](#checking-a-result).

## Structure

`import Stacks` brings in both tiers; `import StacksCore` restricts imports to the human-reviewed tier. For a focused dependency, import the individual module containing the declaration instead of either umbrella. The tiers describe review provenance, not different proof-checking standards.

* [StacksCore](StacksCore/): human-reviewed formalizations, checked against the Stacks Project and brought to Mathlib standards of naming, generality and style.
* [StacksFrontier](StacksFrontier/): formalizations written by AI agents. This is where coverage grows fastest, and where review is most needed before code moves into StacksCore.

## Finding a tag

A declaration that formalizes all or part of a Stacks tag carries the attribute `@[stacks TAG]`, for example `@[stacks 00DS]`; a tag that Mathlib already covers is registered on the Mathlib declaration with `add_to_stacks TAG`. A tag can be carried by several declarations, and a comment in the attribute records which part of the tag a declaration covers when it covers only part. After `import Stacks`, the command `#stacks_tags` lists every tagged declaration with its tag, and `#stacks_tags!` also prints each statement. The [website](https://stacks.axiommath.ai/) links each tag to its Lean code, its dependencies and the Stacks Project's own statement.

## EGA and SGA references

Declarations are also tagged with the numbered items of Grothendieck's *Éléments de géométrie algébrique* (EGA) and *Séminaire de géométrie algébrique* (SGA) that they prove, with `@[ega "IV 7.8.3"]` or `@[sga "4 IV 4.9.4"]`, or with `add_to_ega` / `add_to_sga` for a Mathlib declaration. A declaration carries a reference exactly when it proves one of the following, and the attribute's comment says which:

* the whole item: no comment;
* a more general statement than the item: `"more general"`;
* some of the item's clauses: the clauses, for example `"(ii)"`;
* a special case of the item: the restriction, for example `"affine case"`.

A declaration that is only related to an item, without proving any of these, is not tagged with it. Numbers follow the original installments: Publ. Math. IHÉS for EGA, and the standard Springer Lecture Notes editions for SGA.

## Checking a result

Use the version in `lean-toolchain` and the dependencies in `lake-manifest.json`. Check the current source of the module you intend to consume, then use a small probe importing that module:

```lean
import StacksCore.Order.DirectedInverseSystem

set_option pp.fullNames true
#check DirectedSystem
```

Run a probe with `lake env lean path/to/Probe.lean` once its dependencies are built. `#check` confirms the imported declaration's type, not its proof dependencies. For a theorem, add `#print axioms Fully.Qualified.theoremName`, replacing the name with the exact theorem being reused, and retain the raw output together with the compiler exit status, source revision and any local modifications.

### Axioms

A proof-dependency receipt meets the standard-axiom requirement only when its axiom set is a subset of `propext`, `Classical.choice` and `Quot.sound`. An empty set is valid; `sorryAx`, custom axioms and native-decision trust axioms are not. A successful compiler exit alone does not establish this: Lean can accept a `sorry` with a warning. An imported compiled file alone does not certify that its current source was checked.

The receipt covers the named declaration, not every tag or module. It also does not establish that the Lean statement matches the cited mathematical result: check its hypotheses, conclusion, intended objects and partial-coverage comment separately. Explicit hypotheses remain assumptions even when the axiom receipt is clean.

The EGA/SGA registration utilities have a bounded native regression test, requiring only the pinned compiler (no Mathlib download or full library build):

```sh
python3 -m unittest discover -s tests -v
```

This checks reference metadata and documentation behavior, not the mathematical library's proof certification.

## Building

```
lake exe cache get
lake build
```

`lake exe cache get` downloads Mathlib's compiled files. The library itself has about 63,000 modules, so a full build takes a long time and a lot of memory; a cache service for the compiled Stacks modules is planned, so that `lake build` will not have to compile them locally.

## Contributing

Contributions are welcome: formalizing the remaining examples, exercises and remarks, reviewing StacksFrontier code and moving it into StacksCore, formalizing directly for StacksCore, or improving existing proofs.

New formalizations and reviews are claimed before they start, so that efforts do not collide:

1. Find a task on the [task board](https://stacks.axiommath.ai/contributing) and check the [open claims](https://github.com/AxiomMath/Stacks/issues?q=is%3Aissue+label%3Aclaim).
2. Open a [claim](https://github.com/AxiomMath/Stacks/issues/new?template=claim.yml) with a blueprint: the exact statement, the Lean statement you intend to prove, the declarations in this library or in Mathlib that you will use or extend, and a proof outline. The task board pre-fills it for you.
3. A maintainer reviews the blueprint. When it is approved, the issue is labelled `blueprint-approved` and assigned to you; that is your claim.
4. Formalize it and open a pull request that closes the issue. The maintainers review every pull request, to either tier.

Improvements to existing proofs and small fixes (typos, broken proofs, documentation) need no claim; open a pull request directly. [CONTRIBUTING.md](CONTRIBUTING.md) has the conventions.

## License

[Apache 2.0](LICENSE). The Stacks Project itself is licensed under the GNU Free Documentation License.
