module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.AlgebraicGeometry.Curves.Models.Reduction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.NodalContraction.SmoothAt

/-!
# Good reduction of a curve over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K`. A smooth proper model of `C` is a minimal model, and a
regular proper model of `C` with smooth special fibre is smooth over `R`; these are the parts of
[Stacks, Tag 0CDI] that do not involve the uniqueness of minimal models.

## Main results

* `Stacks.Models.isMinimalModel_of_isModel_of_smooth` — a smooth proper model is a minimal model.
* `Stacks.Models.RegularProperModelSituation.smooth_of_smooth_specialFiberToSpec` — a regular
  proper model with smooth special fibre is smooth over `R`.

## References

* [Stacks Project, Tag 0CDI](https://stacks.math.columbia.edu/tag/0CDI)
* [Stacks Project, Tag 0C62](https://stacks.math.columbia.edu/tag/0C62)
* [Stacks Project, Tag 0CA6](https://stacks.math.columbia.edu/tag/0CA6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **A smooth proper model is a minimal model.** -/
public theorem isMinimalModel_of_isModel_of_smooth {C X : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hc : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) [IsProper p] [Smooth p] : IsMinimalModel c p e := by
  classical
  obtain ⟨hflat, hlft, hqc, hce⟩ := hmod
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let S : RegularProperModelSituation.{u} :=
    { R := R, K := K, k := IsLocalRing.ResidueField R, residueEquiv := AlgEquiv.refl,
      C := C, C_to_K := c, X := X, X_to_R := p, flat := hflat,
      locallyOfFiniteType := hlft, quasiCompact := hqc,
      regular := isRegular_of_smooth_over_regular p,
      genericFiberIso := e, genericFiberIso_over_K := hce,
      π := π, uniformizer := hπ, curveProjective := hc }
  have : ConnectedSpace S.specialFiber := S.connectedSpace_specialFiber
  have : IsIntegral S.specialFiber := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth
    (pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))
  have hcomp : irreducibleComponents S.specialFiber = {Set.univ} :=
    irreducibleComponents_eq_singleton
  let eC : Fin 1 ≃ irreducibleComponents S.specialFiber :=
    { toFun := fun _ ↦ ⟨Set.univ, by rw [hcomp]; rfl⟩
      invFun := fun _ ↦ 0
      left_inv := fun i ↦ Subsingleton.elim _ _
      right_inv := fun Z ↦ by
        obtain ⟨Z, hZ⟩ := Z
        rw [hcomp] at hZ
        exact Subtype.ext hZ.symm }
  have hmin : (S.associatedNumericalType 1 eC).IsMinimal := by
    rintro ⟨i, -, hi⟩
    have hsum := (S.associatedNumericalType 1 eC).intersection_mul_multiplicity i
    have hi0 : ∀ j : Fin (S.associatedNumericalType 1 eC).componentCount, j = i := fun j ↦ by
      have h₁ : j.val < 1 := j.2
      have h₂ : i.val < 1 := i.2
      exact Fin.ext (by lia)
    rw [Fintype.sum_eq_single i (fun j hj ↦ absurd (hi0 j) hj)] at hsum
    have hm := (S.associatedNumericalType 1 eC).multiplicity_pos i
    have hw := (S.associatedNumericalType 1 eC).weight_pos i
    rcases mul_eq_zero.mp hsum with h | h
    · rw [h] at hi
      linarith
    · linarith
  exact S.isMinimalModel_of_isMinimal_associatedNumericalType 1 eC hmin

/-- If the base change of `h` along a field-valued point with isomorphic residue field is smooth,
then so is the corresponding scheme-theoretic fibre over its residue field. -/
private theorem smooth_fiberToSpecResidueField_of_smooth_pullback_snd {W Y : Scheme.{u}}
    (h : W ⟶ Y) {F : Type u} [Field F] (f : Spec (.of F) ⟶ Y)
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo f))] (hs : Smooth (pullback.snd h f)) :
    Smooth (h.fiberToSpecResidueField (f (IsLocalRing.closedPoint F))) := by
  obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField h f
  rw [← hE]
  infer_instance

/-- **A regular proper model with smooth special fibre is smooth over `R`.** -/
public theorem RegularProperModelSituation.smooth_of_smooth_specialFiberToSpec
    (S : RegularProperModelSituation.{u}) (h : Smooth S.specialFiberToSpec) :
    Smooth S.X_to_R := by
  have hfib : ∀ t : Spec (.of S.R), Smooth (S.X_to_R.fiberToSpecResidueField t) := by
    intro t
    rcases S.eq_specMap_algebraMap_fraction_or_residue t with rfl | rfl
    · have := isIso_descResidueField_algebraMap_of_isFractionRing S.R S.K
      refine smooth_fiberToSpecResidueField_of_smooth_pullback_snd _ _ ?_
      have hinv : S.genericFiberIso.inv ≫ S.C_to_K =
          pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) := by
        rw [← S.genericFiberIso_over_K, Iso.inv_hom_id_assoc]
      rw [← hinv]
      infer_instance
    · have := isIso_descResidueField_of_surjective (algebraMap S.R S.k) S.surjective_algebraMap
      exact smooth_fiberToSpecResidueField_of_smooth_pullback_snd _ _ h
  exact (InfinitesimalLifting.smooth_iff_forall_smoothAt _).mpr fun x ↦
    smoothAt_of_flat_of_smoothAt_fiber S.X_to_R inferInstance x
      ((InfinitesimalLifting.smooth_iff_forall_smoothAt _).mp (hfib _) _)

end Stacks.Models

end
