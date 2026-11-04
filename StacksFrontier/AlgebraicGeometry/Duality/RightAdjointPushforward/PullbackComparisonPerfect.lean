module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonStructureSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

/-!
# Equation 48.8.0.1 is an isomorphism for a perfect complex

Let `f : X ⟶ Y` be a morphism of schemes and let `a` be a right adjoint of the restricted derived
direct image `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `K, L ∈ D_QCoh(𝒪_Y)` the comparison map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)`

of `Stacks.Duality.compareWithPullbackTensor`, which is the two-variable form of Equation 48.8.0.1
of [Stacks, Tag 0A9S], is an isomorphism when `K` is perfect; and so, in particular, is the
displayed map `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)` of that equation. This is [Stacks, Tag 0A9T]; this
file proves the source's argument for it granted the duality data of `K`, and the tag itself is
`Stacks.Duality.isIso_compareWithPullbackTensor_and_compareWithPullback_of_isPerfect` of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointPushforward/PullbackComparisonPerfectDual.lean`.

## The argument

The source argues by Yoneda. Writing `K^∨` for the dual of the perfect complex `K`
([Stacks, Tag 08DQ]), one has for every `M ∈ D_QCoh(𝒪_X)`

  `Hom(Rf_*M, K ⊗ᴸ L) = Hom(K^∨ ⊗ᴸ Rf_*M, L) = Hom(Rf_*(Lf^*K^∨ ⊗ᴸ M), L)`
  `                   = Hom(Lf^*K^∨ ⊗ᴸ M, a(L)) = Hom(M, Lf^*K ⊗ᴸ a(L))`,

the first and last equalities because tensoring with `K^∨` is left adjoint to tensoring with `K`
and likewise after pullback, the second the projection formula for `K^∨`, and the third the
adjunction `Rf_* ⊣ a`. Comparing with `Hom(Rf_*M, K ⊗ᴸ L) = Hom(M, a(K ⊗ᴸ L))` gives the claim.

Read as a chain of adjunctions rather than of Hom-sets, that argument says: the comparison
transformation `a ⋙ (Lf^*K ⊗ᴸ -) ⟶ (K ⊗ᴸ -) ⋙ a` is the *conjugate*, in the sense of
`CategoryTheory.conjugateEquiv`, of the projection-formula transformation
`Rf_* ⋙ (K^∨ ⊗ᴸ -) ⟶ (Lf^*K^∨ ⊗ᴸ -) ⋙ Rf_*` for the two composite adjunctions

  `(Lf^*K^∨ ⊗ᴸ -) ⋙ Rf_* ⊣ a ⋙ (Lf^*K ⊗ᴸ -)` and `Rf_* ⋙ (K^∨ ⊗ᴸ -) ⊣ (K ⊗ᴸ -) ⋙ a`,

and the conjugate of an invertible transformation is invertible. The file assembles this in three
steps:

* `Stacks.Duality.compareWithPullbackTensorTwoSquare_eq_mateEquiv` — the comparison
  transformation is the mate, for the adjunction `Rf_* ⊣ a` on both sides of the square, of the
  inverse projection formula for `K`. This is a restatement of the adjunction characterization
  of the comparison map, so it is a computation with the unit of `Rf_* ⊣ a`.
* `Stacks.Duality.isIso_compareWithPullbackTensorTwoSquare_of_mateEquiv` — iterating the mates
  correspondence yields a conjugate, by `CategoryTheory.iterated_mateEquiv_conjugateEquiv`.
  Hence if the inverse projection formula for `K` is the mate of the projection formula for some
  `K^∨` with respect to adjunctions `(Lf^*K^∨ ⊗ᴸ -) ⊣ (Lf^*K ⊗ᴸ -)` and `(K^∨ ⊗ᴸ -) ⊣ (K ⊗ᴸ -)`,
  the comparison transformation is the conjugate of the invertible projection formula for `K^∨`,
  and is therefore invertible.
* For a perfect `K` that data is the duality of [Stacks, Tag 08DQ]. [Stacks, Tag 0A9T] itself,
  for a quasi-compact quasi-separated `f` with `Y` quasi-compact, is
  `Stacks.Duality.isIso_compareWithPullbackTensor_and_compareWithPullback_of_isPerfect` of
  `PullbackComparisonPerfectDual.lean`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `quasiCoherentDerivedPullbackTensor` — the endofunctor `E ↦ Lf^*K ⊗ᴸ_{𝒪_X} E` of `D_QCoh(𝒪_X)`.
* `projectionFormulaTwoSquare` — the projection-formula map of [Stacks, Tag 0B53] read as a
  2-square `Rf_* ⋙ (K ⊗ᴸ -) ⟶ (Lf^*K ⊗ᴸ -) ⋙ Rf_*` for the square of categories whose two
  horizontal sides are `Rf_*`.
* `projectionFormulaInvTwoSquare` — its inverse, as a 2-square for the transposed square.
* `compareWithPullbackTensorTwoSquare` — the comparison map of [Stacks, Tag 0A9S] read as a
  2-square `a ⋙ (Lf^*K ⊗ᴸ -) ⟶ (K ⊗ᴸ -) ⋙ a`, that is, as a natural transformation in `L`.

## Main results

* `isIso_compareWithPullbackTensorTwoSquare_of_mateEquiv` and
  `isIso_compareWithPullbackTensor_of_mateEquiv` — the comparison map is an isomorphism as soon
  as the inverse projection formula for `K` is the mate of the projection formula for some other
  complex with respect to a pair of tensor adjunctions.

## What is carried, and why

The invertibility of the projection-formula map, which the source cites as [Stacks, Tag 08EU] or
[Stacks, Tag 0B54], is already a hypothesis of `Stacks.Duality.compareWithPullbackTensor`, and is
inherited here in the same shape, as an `IsIso` instance assumption; so is the oplax monoidality
`α` that the projection-formula map is built from. Beyond those, the one input of the source's
proof is the duality of [Stacks, Tag 08DQ] for the perfect complex `K`, in the following form:

* a complex `K^∨` — the dual of `K`;
* the adjunctions `(K^∨ ⊗ᴸ_{𝒪_Y} -) ⊣ (K ⊗ᴸ_{𝒪_Y} -)` on `D_QCoh(𝒪_Y)` and
  `(Lf^*K^∨ ⊗ᴸ_{𝒪_X} -) ⊣ (Lf^*K ⊗ᴸ_{𝒪_X} -)` on `D_QCoh(𝒪_X)`, which hold because `K` is
  perfect, hence dualizable, with dual `K^∨`, and `Lf^*K` is perfect with dual `Lf^*K^∨`;
* the coherence that the projection-formula map for `K^∨` is the mate of the inverse
  projection-formula map for `K`, with respect to those two adjunctions. Spelled out, the mate is
  the composite

    `Rf_*(Lf^*K ⊗ᴸ E) ⟶ K ⊗ᴸ K^∨ ⊗ᴸ Rf_*(Lf^*K ⊗ᴸ E) ⟶ K ⊗ᴸ Rf_*(Lf^*K^∨ ⊗ᴸ Lf^*K ⊗ᴸ E)`
    `                                               ⟶ K ⊗ᴸ Rf_*E`

  of the coevaluation of `K`, the projection formula for `K^∨`, and the evaluation of `Lf^*K`,
  and the coherence is that this composite inverts the projection formula for `K`. That is the
  standard reason the projection formula is invertible for a perfect complex.

This file does not construct that data. In `isIso_compareWithPullbackTensor_of_mateEquiv` the
three items, for the one complex `K`, are the hypotheses `adjX`, `adjY` and `hmate`, and
perfectness is dropped; they are statements about the tensor product and the projection formula
and not about the comparison map, let alone about the right adjoint `a`: neither `a` nor the
comparison map occurs in them. [Stacks, Tag 0A9T] itself is proved in
`PullbackComparisonPerfectDual.lean` through the left dual `Stacks.Duality.perfectDual` of a
perfect complex in the monoidal category `D_QCoh(𝒪_Y)`.

*Which `IsPerfect`.* As in `StacksFrontier/AlgebraicGeometry/Duality/IdentityFourierMukaiKernel.lean`
perfectness is `Stacks.Cohomology.PerfectComplexes.IsPerfect` of [Stacks, Tag 08CM], read on the
ringed space `Y.toRingedSpace` underlying the scheme, and applied to the underlying object of the
derived category of a complex with quasi-coherent cohomology.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointPushforward/PullbackComparison.lean`, no
declaration here carries a `[HasDerivedCategory.{w}]` binder: the quasi-coherent derived tensor
product and derived pullback are available only at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## References

* [Stacks Project, Tag 0A9T](https://stacks.math.columbia.edu/tag/0A9T)
* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Duality.DerivedPushforward
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (α : quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ⟶
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X)

/-! ### The projection formula and the comparison map as 2-squares -/

/-- Tensoring with the derived pullback of `K`: the endofunctor `E ↦ Lf^*K ⊗ᴸ_{𝒪_X} E` of
`D_QCoh(𝒪_X)`. -/
abbrev quasiCoherentDerivedPullbackTensor (K : quasiCoherentDerivedCategory Y) :
    quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory X :=
  (quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K)

/-- **The projection-formula map as a 2-square.** The maps
`K ⊗ᴸ_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗ᴸ_{𝒪_X} E)` of `Stacks.Duality.projectionFormulaMap`, natural in
`E`, read as a 2-square `Rf_* ⋙ (K ⊗ᴸ_{𝒪_Y} -) ⟶ (Lf^*K ⊗ᴸ_{𝒪_X} -) ⋙ Rf_*` for the square of
categories both of whose horizontal sides are `Rf_*`. -/
def projectionFormulaTwoSquare (K : quasiCoherentDerivedCategory Y) :
    TwoSquare (quasiCoherentDerivedPushforward f hpush)
      (quasiCoherentDerivedPullbackTensor f K) ((quasiCoherentDerivedTensor Y).obj K)
      (quasiCoherentDerivedPushforward f hpush) :=
  TwoSquare.mk _ _ _ _
    { app := fun E => projectionFormulaMap f hpush α E K
      naturality := fun _ _ φ => projectionFormulaMap_naturality_right f hpush α φ K }

/-- The 2-square of the projection formula has the projection-formula maps as its components. -/
@[simp]
theorem projectionFormulaTwoSquare_natTrans_app (K : quasiCoherentDerivedCategory Y)
    (E : quasiCoherentDerivedCategory X) :
    (projectionFormulaTwoSquare f hpush α K).natTrans.app E =
      projectionFormulaMap f hpush α E K :=
  rfl

section Comparison

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]

/-- Granted [Stacks, Tag 08EU], the 2-square of the projection formula is invertible, because its
components are. -/
instance isIso_projectionFormulaTwoSquare_natTrans (K : quasiCoherentDerivedCategory Y) :
    IsIso (projectionFormulaTwoSquare f hpush α K).natTrans := by
  have : ∀ E, IsIso ((projectionFormulaTwoSquare f hpush α K).natTrans.app E) := fun E =>
    inferInstanceAs (IsIso (projectionFormulaMap f hpush α E K))
  exact NatIso.isIso_of_isIso_app _

/-- **The inverse projection formula as a 2-square**: the inverse of
`Stacks.Duality.projectionFormulaTwoSquare`, read as a 2-square
`(Lf^*K ⊗ᴸ_{𝒪_X} -) ⋙ Rf_* ⟶ Rf_* ⋙ (K ⊗ᴸ_{𝒪_Y} -)` for the transposed square. -/
def projectionFormulaInvTwoSquare (K : quasiCoherentDerivedCategory Y) :
    TwoSquare (quasiCoherentDerivedPullbackTensor f K)
      (quasiCoherentDerivedPushforward f hpush) (quasiCoherentDerivedPushforward f hpush)
      ((quasiCoherentDerivedTensor Y).obj K) :=
  TwoSquare.mk _ _ _ _ (inv (projectionFormulaTwoSquare f hpush α K).natTrans)

variable {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-- **The comparison map of Equation 48.8.0.1 as a 2-square.** The maps
`Lf^*K ⊗ᴸ_{𝒪_X} a(L) ⟶ a(K ⊗ᴸ_{𝒪_Y} L)` of `Stacks.Duality.compareWithPullbackTensor`, natural in
`L`, read as a 2-square `a ⋙ (Lf^*K ⊗ᴸ_{𝒪_X} -) ⟶ (K ⊗ᴸ_{𝒪_Y} -) ⋙ a` for the square of
categories both of whose horizontal sides are `a`. -/
def compareWithPullbackTensorTwoSquare (K : quasiCoherentDerivedCategory Y) :
    TwoSquare a ((quasiCoherentDerivedTensor Y).obj K)
      (quasiCoherentDerivedPullbackTensor f K) a :=
  TwoSquare.mk _ _ _ _
    { app := fun L => compareWithPullbackTensor f hpush α adj K L
      naturality := fun _ _ g =>
        compareWithPullbackTensor_naturality_right f hpush α adj _ g }

/-- The 2-square of the comparison map has the comparison maps as its components. -/
@[simp]
theorem compareWithPullbackTensorTwoSquare_natTrans_app (K L : quasiCoherentDerivedCategory Y) :
    (compareWithPullbackTensorTwoSquare f hpush α adj K).natTrans.app L =
      compareWithPullbackTensor f hpush α adj K L :=
  rfl

/-- **The comparison map is the mate of the inverse projection formula.** The 2-square of the
comparison map of [Stacks, Tag 0A9S] is the mate of the 2-square of the inverse projection
formula, taken with respect to the adjunction `Rf_* ⊣ a` on both horizontal sides of the square.
This is the adjunction characterization
`Stacks.Duality.homEquiv_symm_compareWithPullbackTensor` of the comparison map, read for all `L`
at once. -/
theorem compareWithPullbackTensorTwoSquare_eq_mateEquiv (K : quasiCoherentDerivedCategory Y) :
    compareWithPullbackTensorTwoSquare f hpush α adj K =
      mateEquiv adj adj (projectionFormulaInvTwoSquare f hpush α K) := by
  ext L
  simp [compareWithPullbackTensorTwoSquare, projectionFormulaInvTwoSquare,
    compareWithPullbackTensor, Adjunction.homEquiv_unit]

/-- **The comparison transformation is invertible as soon as the projection formula is a mate.**
Let `Kd` be a complex, and suppose tensoring with `Kd` is left adjoint to tensoring with `K`, both
on `D_QCoh(𝒪_Y)` and, after derived pullback, on `D_QCoh(𝒪_X)`, in such a way that the projection
formula for `Kd` is the mate of the inverse projection formula for `K`. Then the comparison
transformation `a ⋙ (Lf^*K ⊗ᴸ_{𝒪_X} -) ⟶ (K ⊗ᴸ_{𝒪_Y} -) ⋙ a` of [Stacks, Tag 0A9S] is
invertible.

Indeed by `Stacks.Duality.compareWithPullbackTensorTwoSquare_eq_mateEquiv` it is the mate of the
mate of the projection formula for `Kd`, and an iterated mate is a conjugate
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`); the conjugate of an invertible
transformation is invertible, and the projection formula for `Kd` is invertible. -/
theorem isIso_compareWithPullbackTensorTwoSquare_of_mateEquiv
    {K Kd : quasiCoherentDerivedCategory Y}
    (adjX : quasiCoherentDerivedPullbackTensor f Kd ⊣
      quasiCoherentDerivedPullbackTensor f K)
    (adjY : (quasiCoherentDerivedTensor Y).obj Kd ⊣ (quasiCoherentDerivedTensor Y).obj K)
    (hmate : mateEquiv adjX adjY (projectionFormulaTwoSquare f hpush α Kd) =
      projectionFormulaInvTwoSquare f hpush α K) :
    IsIso (compareWithPullbackTensorTwoSquare f hpush α adj K).natTrans := by
  have key := iterated_mateEquiv_conjugateEquiv adjX adjY adj adj
    (projectionFormulaTwoSquare f hpush α Kd)
  rw [hmate] at key
  have hconj : IsIso (conjugateEquiv (adjX.comp adj) (adj.comp adjY)
      (projectionFormulaTwoSquare f hpush α Kd).natTrans) := inferInstance
  rw [compareWithPullbackTensorTwoSquare_eq_mateEquiv, key]
  exact hconj

/-- **The comparison map is invertible as soon as the projection formula is a mate**, the
componentwise form of `Stacks.Duality.isIso_compareWithPullbackTensorTwoSquare_of_mateEquiv`. -/
theorem isIso_compareWithPullbackTensor_of_mateEquiv
    {K Kd : quasiCoherentDerivedCategory Y}
    (adjX : quasiCoherentDerivedPullbackTensor f Kd ⊣
      quasiCoherentDerivedPullbackTensor f K)
    (adjY : (quasiCoherentDerivedTensor Y).obj Kd ⊣ (quasiCoherentDerivedTensor Y).obj K)
    (hmate : mateEquiv adjX adjY (projectionFormulaTwoSquare f hpush α Kd) =
      projectionFormulaInvTwoSquare f hpush α K)
    (L : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullbackTensor f hpush α adj K L) := by
  have := isIso_compareWithPullbackTensorTwoSquare_of_mateEquiv f hpush α adj adjX adjY hmate
  exact NatIso.isIso_app_of_isIso
    (compareWithPullbackTensorTwoSquare f hpush α adj K).natTrans L

end Comparison

end Stacks.Duality

end
