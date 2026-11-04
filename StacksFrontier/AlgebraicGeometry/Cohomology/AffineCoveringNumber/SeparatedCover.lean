module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoveringNumber.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.SeparatedCover

/-!
# Cohomological vanishing from a finite cover by quasi-compact separated opens

For a quasi-compact quasi-separated scheme covered by finitely many quasi-compact separated
opens, the cohomology of every quasi-coherent module vanishes above a bound determined by the
affine covering numbers of the intersections of the given opens.

## Main definitions

The bound is expressed in terms of
`Stacks.AlgebraicGeometry.AffineCoveringNumber.minimalAffineCoverCardinality`, the affine
covering number; no new definition is introduced here.

## Main results

* `cohomology_isZero_of_degree_ge_affineCoveringNumber`: the vanishing bound attached to a finite
  cover by quasi-compact separated opens, [Stacks, Tag 071L].

## Implementation notes

The maximum over subsets of the indexing set is represented by `Finset.sup`. Cohomology is the
value at the top open of Mathlib's cohomology presheaf of the underlying sheaf of abelian groups,
and vanishing is expressed categorically by `IsZero`. The `HasExt` assumption supplies the chosen
categorical model for sheaf cohomology.

The Mayer--Vietoris induction over the subsets of the indexing set is
`Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_cover`. The affine covering
number of that development is the same infimum as the one of this namespace, so the two agree by
`rfl` and the bound here is the bound proved there.

## References

* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.AffineCoveringNumber

universe w v u

section SeparatedCover

variable {X : Scheme.{u}}

/-- This namespace's affine covering number and `AlgebraicGeometry.minimalAffineCoverCardinality`
are the same infimum, so the Mayer--Vietoris vanishing stated with the latter applies verbatim. -/
private lemma minimalAffineCoverCardinality_eq (U : X.Opens) :
    minimalAffineCoverCardinality U = AlgebraicGeometry.minimalAffineCoverCardinality U := rfl

/-- **[Stacks, Tag 071L].** Let `X` be quasi-compact and quasi-separated and let `U₁, ..., Uₙ` be
a cover of `X` by quasi-compact separated opens. If
`d = max_I (|I| + t(⋂ i ∈ I, Uᵢ) - 1)`, where `t` is the affine covering number, then the
cohomology of every quasi-coherent `𝒪_X`-module vanishes in every degree at least `d`. -/
lemma cohomology_isZero_of_degree_ge_affineCoveringNumber [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    {n d : ℕ} (U : Fin n → X.Opens)
    (hU : ⨆ i, U i = ⊤)
    (hU_compact : ∀ i, IsCompact (U i : Set X))
    (hU_separated : ∀ i, Scheme.IsSeparated (U i : Scheme))
    (hd : d = Finset.univ.sup fun I : Finset (Fin n) ↦
      I.card + minimalAffineCoverCardinality (⨅ i ∈ I, U i) - 1)
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : d ≤ p) :
    IsZero
      ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf p).obj
        (op (⊤ : X.Opens))) := by
  classical
  have hbound : ∀ J : Finset (Fin n), J ⊆ Finset.univ →
      J.card + AlgebraicGeometry.minimalAffineCoverCardinality (⊤ ⊓ J.inf U) - 1 ≤ d := by
    intro J _
    rw [hd, ← minimalAffineCoverCardinality_eq]
    simpa [Finset.inf_eq_iInf] using
      (Finset.le_sup (f := fun I : Finset (Fin n) ↦
        I.card + minimalAffineCoverCardinality (⨅ i ∈ I, U i) - 1) (Finset.mem_univ J))
  have hvan := Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_cover
    (⊤ : X.Opens) (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
    U hU_compact hU_separated F Finset.univ d hbound p hp
  have hcover : (Finset.univ : Finset (Fin n)).sup U = ⊤ := by
    simpa [Finset.sup_eq_iSup] using hU
  rwa [hcover, top_inf_eq] at hvan

end SeparatedCover

end Stacks.AlgebraicGeometry.AffineCoveringNumber
