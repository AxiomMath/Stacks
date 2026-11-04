module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonGeneral
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-!
# The right adjoint of pushforward commutes with direct sums

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, so that it restricts to `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and
let `a` be a right adjoint of that restriction — the twisted inverse image `f^×` of
[Stacks, Tag 0A9E]. Then `a` commutes with direct sums. This is [Stacks, Tag 0A9R], Lemma
48.13.1 of the source.

## The argument

The source's proof is this. Pick a perfect object `P` of `D(𝒪_X)`. Then `Rf_*P` is perfect on
`Y` ([Stacks, Tag 0B6G], More on Morphisms Lemma 37.61.13 — this is where "perfect proper
morphism of Noetherian schemes" is used, and the only place), hence compact
([Stacks, Tag 09M1], Derived Categories of Schemes Proposition 36.17.1). So for a family `K i`
of objects of `D_QCoh(𝒪_Y)`

  `Hom(P, a(⊕ K i)) = Hom(Rf_*P, ⊕ K i) = ⊕ Hom(Rf_*P, K i) = ⊕ Hom(P, a(K i))`

— adjunction, compactness of `Rf_*P`, adjunction — and the last group is `Hom(P, ⊕ a(K i))` by
compactness of `P`. Since `D_QCoh(𝒪_X)` has a perfect generator ([Stacks, Tag 09IS], Derived
Categories of Schemes Theorem 36.15.3), a map inducing a bijection on maps out of every shift of
that generator is an isomorphism, so `⊕ a(K i) ⟶ a(⊕ K i)` is one.

That argument is entirely formal once "perfect" is replaced by "compact", and in that form it is
already in this repository:
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` of
`StacksFrontier/CategoryTheory/Triangulated/RightAdjointCoproducts.lean` says that a right
adjoint commutes with direct sums as soon as its left adjoint carries a compact weak generator to
a compact object. The same device, read with `L = Lf^*` and `R = Rf_*`, is what
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/CompactPullback.lean` uses for
[Stacks, Tag 08DZ]; here it is read with `L = Rf_*` and `R = a`, which is [Stacks, Tag 0A9R].
All this file supplies is that instantiation together with the structure the device asks of
`D_QCoh` on either side: direct sums
(`Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory`), the
triangulated structure
(`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated`),
exactness and compatibility with the shift of `Rf_*`
(`Stacks.Duality.DerivedPushforward.commShift_quasiCoherentDerivedPushforward` and
`isTriangulated_quasiCoherentDerivedPushforward`), and additivity of `a`
(`CategoryTheory.Adjunction.right_adjoint_additive`).

## Main results

All in the namespace `Stacks.Duality`.

* `preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward` — **[Stacks, Tag 0A9R]**:
  every right adjoint `a` of `Rf_*` commutes with direct sums.
* `preservesCoproducts_twistedInverseImage_of_isCompactObject_pushforward` —
  **[Stacks, Tag 0A9R]** at the source's own right adjoint, `Stacks.Duality.twistedInverseImage`.
* `preservesCoproducts_quasiCoherentDerivedTensorRight_comp_rightAdjoint` — the composite
  `K ↦ a(K ⊗ᴸ_{𝒪_Y} L)` commutes with direct sums, which is the shape in which
  `StacksFrontier/AlgebraicGeometry/Duality/RightAdjointPushforward/PullbackComparisonGeneral.lean`
  consumes 0A9R. It carries no tag: it is the statement above composed with the commutation of
  the derived tensor product with direct sums, which is not 0A9R.

## What is carried, and why

The perfect-proper hypotheses on `f` — proper, perfect, Noetherian source and target — are
*absent* here. They enter the source's proof at exactly one point, to make `Rf_*P` perfect, and
that point is the hypothesis `hpushE` below: `Rf_*E` is compact. The statements are therefore
strictly more general than the source's, with its geometric content isolated in one hypothesis.
Nothing else is assumed.

* **Compactness of `Rf_*E`, the hypothesis `hpushE`.** The source gets it from
  [Stacks, Tag 0B6G] (`Rf_*` of a perfect complex along a perfect proper morphism with
  Noetherian target is perfect) together with [Stacks, Tag 09M1] (an object of `D_QCoh` is
  compact if and only if it is perfect). Both are in this tree: 0B6G at
  `Stacks.AlgebraicGeometry.PerfectProperDirectImage` `.isPerfect_derivedPushforward_of_`
  `isPerfect_of_locallyHasFiniteTorDimension`
  of `StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/ProperDirectImage.lean`, and
  09M1 at `AlgebraicGeometry.isCompactObject_iff_isPerfect_spec` of
  `StacksFrontier/AlgebraicGeometry/Perfect/QuasiCoherentDerived/CompactAndPerfect.lean`. The
  affine case of 09M1 is unconditional. 0B6G is still conditional there, on [Stacks, Tag 02O5]
  and on the Tor-dimension half of [Stacks, Tag 08EV], which is why `hpushE` stays a hypothesis
  here.
* **A compact weak generator of `D_QCoh(𝒪_X)`, [Stacks, Tag 09IS]** — the arguments `E`, `hEc`
  and `hE`. Unproved in this repository, which has the affine counterpart in
  `StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration.lean`; every consumer here carries it
  in this shape, including
  `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactGenerator`.
* **Quasi-coherence of the cohomology of `Rf_*`, [Stacks, Tag 08D5]** — the argument `hpush`,
  without which the restricted functor does not exist.
* **The existence of the right adjoint, [Stacks, Tag 0A9E]** — the argument `adj`, or the
  instance binder `Functor.IsLeftAdjoint` in the `twistedInverseImage` form. This repository
  proves 0A9E conditionally, in
  `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward`; the source's `a` is the one
  supplied by its Lemma 48.3.1.

Note what the conclusion asserts that the hypotheses do not. The hypotheses say that one object
of `D_QCoh(𝒪_X)` is compact, that it generates, and that its image under `Rf_*` is compact; the
conclusion says that `a` preserves every direct sum indexed by a type of `Type u`. No
`PreservesColimitsOfShape` instance for `a` — or for any functor out of `D_QCoh(𝒪_Y)` — is
assumed anywhere, and a right adjoint preserves limits, not colimits, so nothing of the sort is
available from `adj` alone.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/CompactPullback.lean`, the statements
are at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the only
one at which `D_QCoh` is known here to have the direct sums the argument needs; so the index
types and the universe at which compactness is tested are `Type u` rather than a free universe.

## References

* [Stacks Project, Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-! ### The right adjoint commutes with direct sums -/

/-- **[Stacks, Tag 0A9R].** Let `f : X ⟶ Y` be a morphism of schemes along which derived direct
image preserves quasi-coherence of cohomology, and let `a` be a right adjoint of the restriction
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Suppose `D_QCoh(𝒪_X)` has a compact weak generator `E`
whose image `Rf_*E` is compact in `D_QCoh(𝒪_Y)`. Then `a` commutes with direct sums.

In the source `E` is the perfect generator of [Stacks, Tag 09IS] and compactness of `Rf_*E` is
[Stacks, Tag 0B6G] together with [Stacks, Tag 09M1]; those are the only places the source's
hypotheses on `f` — perfect, proper, Noetherian — are used, and they appear here only through
`hpushE`. The formal half of the argument is
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map`, read with `Rf_*` as
the left adjoint and `a` as the right one. -/
@[stacks 0A9R "a commutes with direct sums: for every right adjoint a of the restricted Rf_* \
and every index type in Type u, a preserves coproducts of that shape. The source's hypotheses \
on f — perfect, proper, Noetherian source and target — are not binders here; they enter its \
proof only to make Rf_*E perfect, hence compact, and that is the hypothesis hpushE. Carried: \
hpushE, compactness of Rf_*E, which is Tag 0B6G (Rf_* of a perfect complex along a perfect \
proper morphism is perfect) together with Tag 09M1 (compact iff perfect in D_QCoh) — both in \
this tree, at \
StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/ProperDirectImage.lean and \
StacksFrontier/AlgebraicGeometry/Perfect/QuasiCoherentDerived/CompactAndPerfect.lean; 09M1 is \
unconditional in the affine case, but 0B6G is still conditional there, on Tag 02O5 and on the \
Tor-dimension half of Tag 08EV, which is why hpushE is carried; E, hEc, hE, a compact weak \
generator of D_QCoh(O_X), Tag 09IS, unproved in this repository and carried in this shape by \
every consumer here; hpush, quasi-coherence of the cohomology of Rf_*, Tag 08D5; and adj, the \
existence of the right adjoint, Tag 0A9E, which this repository proves only conditionally in \
Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward. No PreservesColimitsOfShape \
instance for a, or for any functor out of D_QCoh(O_Y), is assumed"]
theorem preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
    (E : quasiCoherentDerivedCategory X) (hEc : IsCompactObject.{u} E)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hpushE : IsCompactObject.{u} ((quasiCoherentDerivedPushforward f hpush).obj E)) :
    ∀ J : Type u, PreservesColimitsOfShape (Discrete J) a := by
  have hsumX := hasCoproducts_quasiCoherentDerivedCategory X
  have hsumY := hasCoproducts_quasiCoherentDerivedCategory Y
  have hadd : a.Additive := adj.right_adjoint_additive
  exact Pretriangulated.preservesCoproducts_of_isCompactObject_map adj E hE hEc hpushE

/-- **[Stacks, Tag 0A9R] at the source's own right adjoint.** When the restricted derived direct
image is a left adjoint, `Stacks.Duality.twistedInverseImage` is the right adjoint `a` of
[Stacks, Tag 0A9E] that Lemma 48.13.1 of the source speaks about, and it commutes with direct
sums under the same hypotheses as
`Stacks.Duality.preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward`. -/
@[stacks 0A9R "the same conclusion at the source's own right adjoint, \
Stacks.Duality.twistedInverseImage, the f^× of Tag 0A9E. Carries everything \
Stacks.Duality.preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward carries — \
hpushE, which is Tag 0B6G with Tag 09M1, neither of them available to this file; E, \
hEc, hE, the compact weak generator of Tag 09IS; hpush, Tag 08D5 — with the existence of the \
right adjoint now the instance binder Functor.IsLeftAdjoint rather than an adjunction argument, \
that binder being Tag 0A9E"]
theorem preservesCoproducts_twistedInverseImage_of_isCompactObject_pushforward
    [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]
    (E : quasiCoherentDerivedCategory X) (hEc : IsCompactObject.{u} E)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hpushE : IsCompactObject.{u} ((quasiCoherentDerivedPushforward f hpush).obj E)) :
    ∀ J : Type u, PreservesColimitsOfShape (Discrete J) (twistedInverseImage f hpush) :=
  preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward f hpush
    (twistedInverseImageAdjunction f hpush) E hEc hE hpushE

/-! ### The shape the comparison map of Equation 48.8.0.1 consumes -/

/-- **The composite `K ↦ a(K ⊗ᴸ_{𝒪_Y} L)` commutes with direct sums.** This is the right-hand
side of the comparison map of [Stacks, Tag 0A9S] read as a functor of `K`, and the form in which
`Stacks.Duality.isIso_compareWithPullbackTensor_of_isIso_generators` — [Stacks, Tag 0A9U] —
consumes [Stacks, Tag 0A9R]: its instance binder

  `∀ J : Type u, PreservesColimitsOfShape (Discrete J) (quasiCoherentDerivedTensorRight Y L ⋙ a)`

is this statement. It is the commutation of `a` with direct sums, which is
`Stacks.Duality.preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward`, composed with
the commutation of the derived tensor product with direct sums, which is a separate fact and the
instance binder `htensor` here — the source's proof of Lemma 48.13.3 cites both.

No `@[stacks]` attribute: the content beyond 0A9R is the tensor side, which 0A9R does not state,
and the `a` side is registered where it is proved. -/
theorem preservesCoproducts_quasiCoherentDerivedTensorRight_comp_rightAdjoint
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) (L : quasiCoherentDerivedCategory Y)
    [htensor : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (quasiCoherentDerivedTensorRight Y L)]
    (E : quasiCoherentDerivedCategory X) (hEc : IsCompactObject.{u} E)
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hpushE : IsCompactObject.{u} ((quasiCoherentDerivedPushforward f hpush).obj E)) :
    ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (quasiCoherentDerivedTensorRight Y L ⋙ a) := by
  have ha := preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward f hpush adj E hEc hE
    hpushE
  intro J
  have := ha J
  infer_instance

end Stacks.Duality

end
