module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTermsSurjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import StacksCore.Tactic.StacksAttribute

/-! # K-flat resolutions with flat terms, termwise surjective

Every complex of sheaves of modules on a ringed site receives a termwise surjective
quasi-isomorphism from a K-flat complex whose terms are flat (Stacks 06YS). The resolution is the
colimit of the resolution of Tag 077J; its degree-`i` term is the filtered colimit of the
degree-`i` terms of the stages, which are direct sums of extensions by zero of structure sheaves,
and so is flat by Tag 05NG.

## Main results

* `Stacks.SheafOfModules.isIso_ιTruncLE_f`: in degrees below the truncation bound the inclusion
  `τ_{≤ m} K ⟶ K` is an isomorphism, in an arbitrary abelian category.
* `Stacks.SheafOfModules.isFlat_colimit_resolution`: the terms of the colimit of a Tag 077J
  resolution are flat.
* `Stacks.SheafOfModules.exists_kFlatResolution`: all four assertions of Stacks 06YS at once.

## Implementation notes

The sequential colimit of Tag 077J is indexed by `ℕ`, which is `Type 0`, while
`Stacks.SheafOfModules.FlatColimits.isFlat_colimit` wants an index category in the module
universe; `CategoryTheory.ULiftHomULiftCategory.equiv` does the lifting, and
`CategoryTheory.Limits.HasColimit.isoOfEquivalence` transports the colimit back.

The universes are collapsed to `RingedSite.{u, u, u}` because Tag 077J is.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 05NG](https://stacks.math.columbia.edu/tag/05NG)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

/-- In degrees below the truncation bound the inclusion `τ_{≤ m} K ⟶ K` is an isomorphism. -/
lemma isIso_ιTruncLE_f {A : Type*} [Category* A] [Abelian A]
    (K : CochainComplex A ℤ) {m n : ℤ} (h : n < m) : IsIso ((K.ιTruncLE m).f n) := by
  let e := ComplexShape.embeddingUpIntLE m
  have hi : e.f (m - n).natAbs = n := by
    simp only [e, ComplexShape.embeddingUpIntLE_f, Int.natCast_natAbs,
      abs_of_pos (sub_pos.2 h)]
    omega
  have hb : ¬ e.op.BoundaryGE (m - n).natAbs := by
    rw [ComplexShape.Embedding.op_boundaryGE_iff, ComplexShape.boundaryLE_embeddingUpIntLE_iff,
      Int.natAbs_eq_zero]
    omega
  have : IsIso ((K.op.πTruncGE e.op).f n) := by
    show IsIso ((e.op.liftExtend _ _).f n)
    rw [e.op.isIso_liftExtend_f_iff _ _ hi]
    exact K.op.isIso_restrictionToTruncGE' e.op _ hb
  exact inferInstanceAs (IsIso ((K.op.πTruncGE e.op).f n).unop)

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The degree-`i` terms of the colimit of a Tag 077J resolution are flat. -/
theorem isFlat_colimit_resolution
    (G : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ)
    (res : ResolutionByDirectSumsExtensionsByZero X G) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((colimit res.system).X i) := by
  let A := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let ev : CochainComplex A ℤ ⥤ A := HomologicalComplex.eval A (ComplexShape.up ℤ) i
  let stages : ℕ ⥤ A := res.system ⋙ ev
  let eq := ULiftHomULiftCategory.equiv.{u, u} ℕ
  have : IsFiltered (ULiftHom.{u} (ULift.{u} ℕ)) := IsFiltered.of_equivalence eq
  have hstages' : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (colimit (eq.inverse ⋙ stages)) :=
    FlatColimits.isFlat_colimit.{u, u, u, u} (O := X.O) (eq.inverse ⋙ stages) fun n =>
      isFlat_of_isSumOfExtensionByZeroStructureSheaves X
        (res.term_isSum (eq.inverse.obj n) i)
  have eCol : colimit (eq.inverse ⋙ stages) ≅ colimit stages :=
    HasColimit.isoOfEquivalence eq.symm (Iso.refl _)
  have eEval : (colimit res.system).X i ≅ colimit stages := preservesColimitIso ev res.system
  exact (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
      (eCol.trans eEval.symm)) hstages'

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 06YS.** Every complex of sheaves of modules on a ringed site receives a termwise
surjective quasi-isomorphism from a K-flat complex whose terms are flat. -/
theorem exists_kFlatResolution
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p :
      P ⟶ G),
      IsKFlat X.O P ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (P.X i)) ∧
      QuasiIso p ∧ (∀ i : ℤ, Epi (p.f i)) := by
  obtain ⟨res⟩ := exists_resolutionByDirectSumsExtensionsByZero X G
  exact ⟨colimit res.system, res.colimitComparison,
    kFlat_colimit X.O res.system fun m => kFlat_of_boundedAbove_of_flat X.O (res.system.obj m)
      (res.boundedAbove m) fun j => isFlat_of_isSumOfExtensionByZeroStructureSheaves X
        (res.term_isSum m j),
    isFlat_colimit_resolution X G res, res.colimit_quasiIso, epi_colimitComparison_f X res⟩

end Stacks.SheafOfModules

end
