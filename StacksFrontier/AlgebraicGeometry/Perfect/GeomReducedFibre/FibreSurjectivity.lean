module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.FibreSpanning
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseAlternatingCechModuleTransport
public import StacksFrontier.RingTheory.Flat.FiniteFreeResidueExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Surjectivity of the degree-zero base-change map at a geometrically reduced fibre

Let `g : Y ⟶ Spec R` be proper and `p` a prime of `R` such that every base change of `g` along
`Spec K ⟶ Spec R`, for a field `K` and a ring map `R → K` with kernel `p`, is a reduced scheme --
for instance, the fibre `Y_p` is geometrically reduced over `κ(p)`. Then for the Čech model `D`
of `𝒪_Y` attached to a finite affine open cover with affine finite intersections, every
degree-zero cocycle of `D ⊗_R κ(p)` comes from a degree-zero cocycle of `D`.

This is the step "it suffices to prove that `(f_*𝒪_X)_s → H⁰(X_s, 𝒪_{X_s})` is surjective" of the
proof of [Stacks, Tag 0G7Y], carried out as the source does: choose a flat local
`R_p → B` with algebraically closed residue field `k` ([Stacks, Tag 03C3]); the global functions
on the reduced proper `k`-scheme `Y_k` are spanned by idempotents ([Stacks, Tag 0BUG]), which
lift to `Y_B` by [Stacks, Tag 0G7X]; the base change of the Čech model to `B` is the Čech model of
`Y_B`, and flatness of `B` and of `k` over `κ(p)` lets the surjectivity descend to `κ(p)`.

## Main results

* `StacksDraft.Perfect.GeomReducedFibre.degreeZeroCyclesSurjective_residueField`: every
  degree-zero cocycle of the Čech model base-changed to `κ(p)` lifts, when the fibre over `p`
  is geometrically reduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

variable {R : Type u} [CommRing R]

/-- The geometric reducedness condition at a prime `p`: every base change of `g` along
`Spec K ⟶ Spec R`, for a field `K` and a ring map `R → K` with kernel `p`, is reduced. -/
def FibreGeometricallyReducedAt {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) (p : Ideal R) : Prop :=
  ∀ ⦃K : Type u⦄ [Field K] (ψ : R →+* K), RingHom.ker ψ = p →
    ∀ ⦃Z : Scheme.{u}⦄ (a : Z ⟶ Y) (b : Z ⟶ Spec (.of K)),
      IsPullback a b g (Spec.map (CommRingCat.ofHom ψ)) → IsReduced Z

/-- The residue field of a local ring at its closed point, in the sense of `Ideal.ResidueField`,
is the residue field of the local ring. -/
def closedPointResidueFieldEquiv (B : Type u) [CommRing B] [IsLocalRing B] :
    IsLocalRing.ResidueField B ≃+* (IsLocalRing.closedPoint B).asIdeal.ResidueField :=
  RingEquiv.ofBijective (algebraMap (B ⧸ IsLocalRing.maximalIdeal B)
    (IsLocalRing.maximalIdeal B).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal B))

/-- A ring map to a field with kernel `p` factors through the residue field `κ(p)`. -/
private theorem exists_residueField_comp_eq {K : Type*} [Field K] (p : Ideal R) [p.IsPrime]
    (ψ : R →+* K) (hker : RingHom.ker ψ = p) :
    ∃ ι : p.ResidueField →+* K, ι.comp (algebraMap R p.ResidueField) = ψ :=
  have hunit : p.primeCompl ≤ (IsUnit.submonoid K).comap ψ := fun _ hr =>
    isUnit_iff_ne_zero.2 fun h => hr (hker ▸ RingHom.mem_ker.2 h)
  ⟨Ideal.ResidueField.lift p ψ hker.ge hunit,
    RingHom.ext (Ideal.ResidueField.lift_algebraMap p ψ hker.ge hunit)⟩

/-- **The degree-zero base-change map of the Čech model is surjective at a geometrically reduced
fibre.** -/
theorem degreeZeroCyclesSurjective_residueField {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R))
    [IsProper g] (p : Ideal R) [p.IsPrime] (hred : FibreGeometricallyReducedAt g p)
    {I : Type u} [Finite I] (U : I → Y.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    DegreeZeroCyclesSurjective (algebraMap R p.ResidueField)
      (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)) := by
  classical
  let Rp := Localization.AtPrime p
  let K := AlgebraicClosure p.ResidueField
  obtain ⟨B, _, _, _, hloc, hflat, -, ⟨eK⟩⟩ :=
    IsLocalRing.exists_flat_residueField_algEquiv Rp K
  let φB : R →+* B := (algebraMap Rp B).comp (algebraMap R Rp)
  have hφB : φB.Flat := RingHom.Flat.comp
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Rp p.primeCompl))
    (RingHom.flat_algebraMap_iff.mpr hflat)
  let T := (IsLocalRing.closedPoint B).asIdeal.ResidueField
  let ψ : R →+* T := (algebraMap B T).comp φB
  have hker : RingHom.ker ψ = p := by
    rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, ← Ideal.comap_comap]
    exact (congrArg (Ideal.comap _) (IsLocalRing.maximalIdeal_comap (algebraMap Rp B))).trans
      Localization.AtPrime.under_maximalIdeal
  have : IsAlgClosed T := IsAlgClosed.of_ringEquiv K T
    ((eK.toRingEquiv.symm).trans (closedPointResidueFieldEquiv B))
  have hsqB := IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom φB))
  let gB := pullback.snd g (Spec.map (CommRingCat.ofHom φB))
  let qB := pullback.fst g (Spec.map (CommRingCat.ofHom φB))
  have : IsProper gB := inferInstance
  have : IsReduced (gB.fiber (IsLocalRing.closedPoint B)) := by
    refine hred ψ hker (Scheme.Hom.fiberι gB (IsLocalRing.closedPoint B) ≫ qB)
      (fiberToSpec gB (IsLocalRing.closedPoint B)) ?_
    have := (isPullback_fiberι_fiberToSpec gB (IsLocalRing.closedPoint B)).paste_horiz hsqB
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp] at this
  let UB : I → (pullback g (Spec.map (CommRingCat.ofHom φB))).Opens := fun i => qB ⁻¹ᵁ U i
  have hUB : (⊤ : (pullback g (Spec.map (CommRingCat.ofHom φB))).Opens) = ⨆ i, UB i :=
    top_eq_iSup_preimage qB U hU
  have hUBaff : ∀ i, IsAffineOpen (UB i) := isAffineOpen_preimage φB hsqB U hUaff
  have hSB : DegreeZeroCyclesSurjective (algebraMap B T)
      (baseAlternatingCechComplex gB UB hUB (Scheme.unitModule _)) :=
    degreeZeroCyclesSurjective_of_mem_span (algebraMap B T)
      (isPullback_fiberι_fiberToSpec gB (IsLocalRing.closedPoint B)) UB hUB hUBaff
      (mem_span_range_appTop_closedFibre gB)
  have hS' : DegreeZeroCyclesSurjective (algebraMap B T)
      (extendScalarsCx φB (baseAlternatingCechComplex g U hU (Scheme.unitModule Y))) :=
    hSB.of_iso ((baseAlternatingCechComplexBaseChangeIso φB hsqB (Scheme.unitModule Y) U hU
      hUaff) ≪≫ baseAlternatingCechComplexMapIso gB UB hUB
        (Scheme.Modules.pullbackUnitIso qB)).symm
  have hψS : DegreeZeroCyclesSurjective ψ
      (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)) :=
    DegreeZeroCyclesSurjective.of_flat_comp φB hφB (algebraMap B T) hS'
  obtain ⟨ι, hι⟩ := exists_residueField_comp_eq p ψ hker
  rw [← hι] at hψS
  exact DegreeZeroCyclesSurjective.of_field_comp _ ι hψS

/-- Under `FibreGeometricallyReducedAt`, the fibre over `p` is geometrically reduced over
`κ(p)`. -/
theorem geometricallyReduced_of_fibreGeometricallyReducedAt {Y Yp : Scheme.{u}}
    {g : Y ⟶ Spec (.of R)} {p : Ideal R} [p.IsPrime] (hred : FibreGeometricallyReducedAt g p)
    {fp : Yp ⟶ Spec (.of p.ResidueField)} {gp : Yp ⟶ Y}
    (hsq : IsPullback gp fp g (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) :
    GeometricallyReduced fp := by
  rw [geometricallyReduced_iff]
  intro K _ y Z fst snd h
  obtain ⟨ι, rfl⟩ := Spec.map_surjective y
  have h' := h.paste_horiz hsq
  rw [← Spec.map_comp] at h'
  refine hred (ι.hom.comp (algebraMap R p.ResidueField)) ?_ (fst ≫ gp) snd ?_
  · rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot ι.hom).1 ι.hom.injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  · exact h'

end StacksDraft.Perfect.GeomReducedFibre

end
