module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AlgebraSheafSupport

/-!
# The reduction of the algebra hypothesis of Stacks 09ZT to Grothendieck existence for modules

`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f` is the single input behind the `halg`
hypotheses of Stacks 09ZT, 0A42 and 0899
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraization.lean`). It reduces to
**Grothendieck existence for coherent modules with support proper over the base** — the
equivalence asserted by Stacks 088F, carried by
`AlgebraicGeometry.adicThickeningCompletionFunctor` — together with two further residuals. This
file carries the account of that reduction's six steps.

The statements of the residuals, and the refutation of an earlier and false form of one of them,
are in `StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraAlgebraization.lean`. The
properness bridge `AlgebraicGeometry.AlgebraSheafProperSupportBridge` is no longer a residual: it
is a theorem, `AlgebraicGeometry.algebraSheafProperSupportBridge`, proved in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AlgebraSheafSupport.lean`, which
imports the file stating it. So the reduction cannot both discharge the bridge and sit beside the
statements; it sits downstream of the proof instead, and this file is the point of the import
chain at which it became expressible.

## The reduction

Let `A` be Noetherian and `I`-adically complete and `f : X ⟶ Spec A` separated of finite type.
Given the system `(B n)` of finite quasi-coherent algebra sheaves on the adic thickenings `Xₙ`
with the cartesian transitions, the reduction

1. passes to the underlying `𝒪_{Xₙ}`-modules `ℳₙ = underlyingModule (B n)`, which are **coherent**
   because `Xₙ` is locally Noetherian — a closed subscheme of `X`, by
   `AlgebraicGeometry.AdicFiniteAlgebra.isClosedImmersion_adicBaseChange_fst` — and `B n` is
   finite and quasi-coherent
   (`Stacks.RelativeSpec.AlgebraSheaf.isCoherent_underlyingModule_of_isFinite`);
2. transports the transition isomorphisms of the algebra system to the module system;
3. converts properness of the relative spectrum of `B 0` over `S₀` into properness of the support
   of `ℳ₀` over `S₀`, which is clause (3) of the systems of Stacks 088F — this is
   `AlgebraicGeometry.algebraSheafProperSupportBridge`;
4. assembles an `AlgebraicGeometry.AdicCoherentModuleSystem` — this is
   `AlgebraicGeometry.adicAlgebraModuleSystem` — and algebraizes it by Grothendieck existence for
   modules, obtaining a coherent `𝒪_X`-module `𝒩` with support proper over `A` and an isomorphism
   of *systems* between the completion of `𝒩` and the system `(ℳₙ)`;
5. puts the algebra structure on `𝒩`, giving `C`;
6. concludes that `C` is finite — its underlying module is coherent, and
   `Stacks.RelativeSpec.AlgebraSheaf.isFinite_of_isCoherent_underlyingModule` needs nothing
   else — quasi-coherent, and that its relative spectrum is proper over `Spec A`, the converse of
   step 3.

Steps 1, 2, 3, 4, 6 and the assembly are proved. Step 5 is the residual, and step 2 needs the
identification of the module underlying an algebra pullback with the module pullback, which is the
hypothesis `hpullback`.

## Why this file no longer states the reduction

It used to: `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_moduleAlgebraization` ran the
six steps above with `AlgebraicGeometry.AdicAlgebraStructureTransport` as its step-5 binder.
**That binder is false**, and the refutation is
`AlgebraicGeometry.not_adicAlgebraStructureTransport_of_not_algebraTransition` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraStructureProof.lean`;
the module docstring of `FiniteAlgebraAlgebraization` records the defect and the counterexample.
A theorem resting on a false hypothesis is vacuous, so that statement said nothing about Stacks
09ZT and has been retired rather than left standing as a reduction.

The reduction itself is **not** lost, and nothing about it is weakened. Step 5 has a repaired
binder, `AlgebraicGeometry.AdicAlgebraStructureSystemTransport`, which is handed the isomorphism
of systems that step 4 actually produces instead of a family of unrelated isomorphisms of
modules — and the six steps run off it unchanged, as
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport`, concluding the same
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f` from the same two other binders
`h088F` and `hpullback`. Coherence of `𝒩` and properness of its support survive as the two
components of the `Stacks.Algebraization.CoherentModulesProperOver f` that the repaired binder
takes, so the repair strengthens a false hypothesis and loses no content. Both live in
`AdicAlgebraStructureProof.lean`, which imports this file.

## Main results

The reduction has moved; see
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraStructureProof.lean`.
This file remains the place where the account of the reduction's six steps is kept, and the point
in the import chain at which the properness bridge of step 3 is available as a theorem.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/
