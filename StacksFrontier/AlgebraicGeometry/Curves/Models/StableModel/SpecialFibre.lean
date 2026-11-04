module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.ReductionTypes
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentCartier
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.HigherGenusLocal
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RationalPointSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaModel
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyStructureSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibre.RationalTailExceptional

/-!
# The special fibre of a minimal at-worst-nodal model

Let `X ⟶ Spec R` be a regular proper model of a smooth projective curve `C` over the fraction
field of a discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K`, which is at-worst-nodal of relative
dimension one and contains no exceptional curve of the first kind (a minimal model, as in
[Stacks, Tag 0CDG]). Its special fibre `X_k` is a proper curve over the residue field `k` with
`H⁰(X_k, 𝒪) = k`, at-worst-nodal singularities, the genus of `C`, all multiplicities one, and no
rational tails: a rational tail of the reduced nodal fibre of a regular model would be an
exceptional curve of the first kind.

## Main results

* `Stacks.Models.RegularProperModelSituation.specialFiber_standing`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The special fibre of an at-worst-nodal model has at-worst-nodal singularities.** The
fibre of `X ⟶ Spec R` over the closed point is at-worst-nodal over its residue field by the
fibrewise criterion of [Stacks, Tag 0C59], and it is `X_k` over `k` through the isomorphism of
residue fields `κ(𝔪) ≅ k`. -/
theorem hasAtWorstNodalSingularities_specialFiber_of_isAtWorstNodal
    (hnod : IsAtWorstNodalOfRelativeDimensionOne S.X_to_R) :
    letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber := by
  obtain ⟨-, -, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff S.X_to_R).mpr hnod
  have := isIso_descResidueField_of_surjective (algebraMap S.R S.k) S.surjective_algebraMap
  obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField S.X_to_R
    (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
  have : Nonempty S.specialFiber := S.nonempty_specialFiber
  obtain ⟨-, hdim, hnodal⟩ := h _ ⟨E.inv (Classical.arbitrary _)⟩
  let φ : CommRingCat.of S.k ⟶ CommRingCat.of ((Spec (.of S.R)).residueField
      ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) (IsLocalRing.closedPoint S.k))) :=
    inv ((Spec (.of S.R)).descResidueField
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))))
  have : IsIso φ := IsIso.inv_isIso
  have : LocallyOfFiniteType (S.X_to_R.fiberToSpecResidueField
      ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) (IsLocalRing.closedPoint S.k))) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  refine Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ S.specialFiberToSpec hdim E.inv
    φ ?_ hnodal
  rw [← hE]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, φ, ← Spec.map_comp, IsIso.inv_hom_id,
    Spec.map_id, Category.comp_id]

open Stacks.AlgebraicGeometry in
/-- **`H⁰(X_k, 𝒪) = k` for an at-worst-nodal model.** The family `X ⟶ Spec R` is proper,
at-worst-nodal with geometrically connected fibres, so `f_*𝒪_X = 𝒪` holds after every base change
([Stacks, Tag 0E0L], read through [Stacks, Tag 0GKA] part (a)); over the one-point base `Spec k`
this is the bijectivity of `k ⟶ Γ(X_k, 𝒪)`. -/
theorem isIso_globalSections_specialFiber_of_isAtWorstNodal
    (hnod : IsAtWorstNodalOfRelativeDimensionOne S.X_to_R) :
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) := by
  have := S.geometricallyConnected_X_to_R
  have hc := (NodalFamilyCohomology.isIso_c_and_isIso_c_of_isPullback_of_isAtWorstNodal
    S.X_to_R hnod).2 (IsPullback.of_hasPullback S.X_to_R
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))
  have hb := (ProperFlatFamilyUnit.isIso_c_iff_bijective_appTop S.specialFiberToSpec).1 hc
  have : IsIso S.specialFiberToSpec.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

/-- **The special fibre of a minimal at-worst-nodal model.** In the situation of
[Stacks, Tag 0C61], if `X` contains no exceptional curve of the first kind and `X ⟶ Spec R` is
at-worst-nodal of relative dimension one, then the special fibre `X_k` is proper of dimension one
over `k` with `H⁰(X_k, 𝒪) = k`, has at-worst-nodal singularities and the genus of `C`, has no
rational tail, is reduced, and all its components have multiplicity one. -/
theorem specialFiber_standing (hmin : ¬ S.X.HasExceptionalCurveOfFirstKind)
    (hnod : IsAtWorstNodalOfRelativeDimensionOne S.X_to_R) :
    IsProper S.specialFiberToSpec ∧ topologicalKrullDim S.specialFiber = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) ∧
      (letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩;
        Stacks.Curves.HasAtWorstNodalSingularities S.k S.specialFiber) ∧
      genus S.specialFiberToSpec = genus S.C_to_K ∧
      (letI : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩;
        ∀ C : S.specialFiber.IdealSheafData, ¬ IsRationalTail S.k S.specialFiber C) ∧
      IsReduced S.specialFiber ∧
      ∀ Z, S.specialFiberMultiplicity Z = 1 := by
  have hdim := S.topologicalKrullDim_specialFiber S.nonempty_specialFiber
  have hglob := S.isIso_globalSections_specialFiber_of_isAtWorstNodal hnod
  have hnodal := S.hasAtWorstNodalSingularities_specialFiber_of_isAtWorstNodal hnod
  have hred : IsReduced S.specialFiber := by
    let : S.specialFiber.Over (Spec (.of S.k)) := ⟨S.specialFiberToSpec⟩
    have : LocallyOfFiniteType (S.specialFiber ↘ Spec (.of S.k)) :=
      inferInstanceAs (LocallyOfFiniteType S.specialFiberToSpec)
    exact Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities S.k S.specialFiber hnodal
  have hmult : ∀ Z, S.specialFiberMultiplicity Z = 1 := fun Z =>
    S.specialFiberMultiplicity_eq_one_of_isField Z
      (S.isField_stalk_specialFiberComponentGenericPoint_of_isReduced Z)
  refine ⟨inferInstance, hdim, hglob, hnodal,
    S.genus_specialFiber_eq_of_eulerCharacteristic_eq S.eulerCharacteristic_C_eq_specialFiber,
    S.not_isRationalTail_specialFiber hmin hnodal hmult, hred, hmult⟩

end Stacks.Models.RegularProperModelSituation

end
