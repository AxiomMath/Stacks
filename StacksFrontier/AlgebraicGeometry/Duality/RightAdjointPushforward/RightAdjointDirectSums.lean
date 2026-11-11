module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonGeneral
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

/-!
# The right adjoint of pushforward commutes with direct sums: the formal reduction

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, so that it restricts to `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and
let `a` be a right adjoint of that restriction. If `D_QCoh(𝒪_X)` has a compact weak generator
`E` whose image `Rf_*E` is compact, then `a` commutes with direct sums. This is the formal half
of the proof of [Stacks, Tag 0A9R], Lemma 48.13.1 of the source.

## The argument

The source's proof is this. Pick a perfect object `P` of `D(𝒪_X)`. Then `Rf_*P` is perfect on
`Y` ([Stacks, Tag 0B6G]), hence compact ([Stacks, Tag 09M1]). So for a family `K i` of objects
of `D_QCoh(𝒪_Y)`

  `Hom(P, a(⊕ K i)) = Hom(Rf_*P, ⊕ K i) = ⊕ Hom(Rf_*P, K i) = ⊕ Hom(P, a(K i))`

and the last group is `Hom(P, ⊕ a(K i))` by compactness of `P`. Since `D_QCoh(𝒪_X)` has a
perfect generator ([Stacks, Tag 09IS]), `⊕ a(K i) ⟶ a(⊕ K i)` is an isomorphism.

Once "perfect" is replaced by "compact" the argument is formal: it is
`CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map` of
`StacksFrontier/CategoryTheory/Triangulated/RightAdjointCoproducts.lean`, read with `L = Rf_*` and
`R = a`. This file supplies that instantiation together with the structure the device asks of
`D_QCoh` on either side: direct sums
(`Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory`), the
triangulated structure, exactness and compatibility with the shift of `Rf_*`, and additivity of
`a` (`CategoryTheory.Adjunction.right_adjoint_additive`).

The statement of [Stacks, Tag 0A9R] itself, for a perfect proper morphism of Noetherian
schemes and with nothing carried, is
`Stacks.Duality.preservesCoproducts_twistedInverseImage_of_perfect_proper` (in
`RightAdjointDirectSumsUnconditional.lean`, beside this file) and
`Stacks.Duality.preservesColimitsOfShape_rightAdjoint_quasiCoherentDerivedPushforward` (in
`RightAdjointDirectSumsPerfectProper.lean`); there [Stacks, Tag 0B6G], [Stacks, Tag 09M1]
and [Stacks, Tag 09IS] are used as proved results.

## Main results

All in the namespace `Stacks.Duality`.

* `preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward` — every right adjoint `a` of
  `Rf_*` commutes with direct sums, given a compact weak generator `E` of `D_QCoh(𝒪_X)` with
  `Rf_*E` compact.
* `preservesCoproducts_twistedInverseImage_of_isCompactObject_pushforward` — the same at
  `Stacks.Duality.twistedInverseImage`.
* `preservesCoproducts_quasiCoherentDerivedTensorRight_comp_rightAdjoint` — the composite
  `K ↦ a(K ⊗ᴸ_{𝒪_Y} L)` commutes with direct sums, given that tensoring with `L` does.

*The model of the derived categories.* The statements are at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which `D_QCoh` has the direct sums the
argument needs; so the index types and the universe at which compactness is tested are `Type u`.

## References

* [Stacks Project, Tag 0A9R](https://stacks.math.columbia.edu/tag/0A9R)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
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

/-- **A right adjoint of `Rf_*` commutes with direct sums once `Rf_*` keeps a compact generator
compact.** Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, and let `a` be a right adjoint of the restriction
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Suppose `D_QCoh(𝒪_X)` has a compact weak generator `E`
whose image `Rf_*E` is compact in `D_QCoh(𝒪_Y)`. Then `a` commutes with direct sums. This is the
formal half of the proof of [Stacks, Tag 0A9R]; the tag itself is
`Stacks.Duality.preservesCoproducts_twistedInverseImage_of_perfect_proper`. -/
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

/-- **The twisted inverse image commutes with direct sums once `Rf_*` keeps a compact generator
compact.** When the restricted derived direct image is a left adjoint,
`Stacks.Duality.twistedInverseImage` commutes with direct sums under the same hypotheses as
`Stacks.Duality.preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward`. -/
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

is this statement. It is the commutation of `a` with direct sums, here
`Stacks.Duality.preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward`, composed with
the commutation of the derived tensor product with direct sums, which is a separate fact and the
instance binder `htensor` here — the source's proof of Lemma 48.13.3 cites both.

No `@[stacks]` attribute: the content beyond 0A9R is the tensor side, which 0A9R does not
state. -/
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
