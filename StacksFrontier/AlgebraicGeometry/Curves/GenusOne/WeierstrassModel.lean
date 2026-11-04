module

public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.SectionRing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassProj
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicCharts

/-!
# A scheme whose section ring is a Weierstrass cubic is the plane cubic

Let `X` be a scheme over a field `k`, `L` an ample invertible module, and suppose the section ring
`Γ_*(X, L)` is presented, as a graded `k`-algebra generated in degree one, by a Weierstrass
cubic `C`. If `X ⟶ Spec Γ(X, 𝒪_X)` is universally closed, then `X` is isomorphic over `k` to
the plane cubic of `C`: the canonical morphism `X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ is an
isomorphism (Stacks Tag 0C6J), and `Proj` of the presentation identifies `Proj Γ_*(X, L)` with the
plane cubic.

## Main definitions

* `AlgebraicGeometry.GenusOne.weierstrassModelHom`: the composite
  `X ⟶ Proj Γ_*(X, L) ⟶ projOf C`.

## Main results

* `AlgebraicGeometry.GenusOne.degZeroRingHom_degreeZeroHom`: the comparison of the degree-zero
  part of the section ring with the functions on `X` inverts the inclusion of functions.
* `AlgebraicGeometry.GenusOne.isIso_weierstrassModelHom`: the composite is an isomorphism.
* `AlgebraicGeometry.GenusOne.weierstrassModelHom_projectionOf`: it is a morphism over `k`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace MvPolynomial
open Stacks.GradedSections (powSections sectionRing mul mulMap)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.GradedSectionRingMap (degreeZeroHom)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (baseRingHom)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjMorphism.ToSpecZero (degZeroRingHom unitSec)
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

universe u

namespace AlgebraicGeometry.GenusOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The comparison of the degree-zero part with the functions inverts the inclusion of
functions**: the function `r`, read as a degree-zero element of `Γ_*(X, L)`, is sent back to
`r`. -/
theorem degZeroRingHom_degreeZeroHom (r : Γ(X, ⊤)) :
    degZeroRingHom L ⟨degreeZeroHom L r, ⟨_, rfl⟩⟩ = r := by
  show Stacks.SectionRingChartMap.ratioR L (unitSec L) _
    (DirectSum.of (powSections L) 0 ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm r)) = r
  rw [Stacks.SectionRingChartMap.ratioR_of]
  refine Stacks.SectionRingChartMap.ratio_unique L _ _ _ r ?_
  have h : globalSection X (natTensorPow L 0)
      ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm r) =
      r • globalSection X (natTensorPow L 0) (unitSec L) := by
    have := globalSection_unitScalarEquiv_symm_comp L r (unitSec L)
    rwa [show (Stacks.SectionRingGeometric.unitScalarEquiv X).symm r ≫ unitSec L =
      (Stacks.SectionRingGeometric.unitScalarEquiv X).symm r from Category.comp_id _] at this
  rw [Stacks.SectionRingProjMorphism.ToSpecZero.resTop_top,
    Stacks.SectionRingProjMorphism.ToSpecZero.resTop_top, h]

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- The structure morphism of a scheme over `k`, through `Spec Γ(X, 𝒪_X)`. -/
theorem over_eq_toSpecΓ_comp :
    X ↘ Spec (.of k) = X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (baseRingHom k X)) := by
  rw [show CommRingCat.ofHom (baseRingHom k X) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop from rfl, Spec.map_comp,
    ← Category.assoc, ← Scheme.toSpecΓ_naturality (X ↘ Spec (.of k)), Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

variable (hL : Stacks.Ample.IsAmple X L) (C : WeierstrassCurve k)
  (φ : MvPolynomial (Fin 3) k →ₐ[k] sectionRing L)
  (hker : RingHom.ker φ = Ideal.span {C.toProjective.polynomial})
  (hv : ∀ i, φ (MvPolynomial.X i) ∈ Stacks.AmpleFiniteAvoidance.grading L 1)
  (hsurj : Function.Surjective φ)

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The image of a scalar `c : k` in the section ring `Γ_*(X, L)` lies in degree `0`. -/
theorem algebraMap_mem_grading_zero [Stacks.Ample.IsInvertibleModule X L] (c : k) :
    algebraMap k (sectionRing L) c ∈ Stacks.AmpleFiniteAvoidance.grading L 0 :=
  ⟨_, (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.algebraMap_eq k L c).symm⟩

/-- **The morphism `X ⟶ projOf C`**: the canonical morphism `X ⟶ Proj Γ_*(X, L)` of Stacks Tag
01PZ followed by `Proj` of the Weierstrass presentation. -/
def weierstrassModelHom : X ⟶ projOf C :=
  projHomOfIsAmple L hL ≫ Proj.map (weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L)
    C φ hker (algebraMap_mem_grading_zero L k) hv)
      (Proj.irrelevant_le_map_of_surjective _ (bijective_weierstrassRingHom C φ hker hsurj).2)

/-- **The morphism `X ⟶ projOf C` lies over `k`.** -/
theorem weierstrassModelHom_projectionOf :
    weierstrassModelHom L k hL C φ hker hv hsurj ≫ projectionOf C = X ↘ Spec (.of k) := by
  show (projHomOfIsAmple L hL ≫ (Proj.map (weierstrassGradedHom
      (Stacks.AmpleFiniteAvoidance.grading L) C φ hker (algebraMap_mem_grading_zero L k) hv)
      (Proj.irrelevant_le_map_of_surjective _ (bijective_weierstrassRingHom C φ hker hsurj).2) :
        Proj (Stacks.AmpleFiniteAvoidance.grading L) ⟶ Proj (gradingOf C))) ≫
      Proj.toSpecZero (gradingOf C) ≫ Spec.map (CommRingCat.ofHom (toGradingZeroOf C)) = _
  rw [Category.assoc, Proj.map_toSpecZero_assoc,
    ← Category.assoc, Stacks.SectionRingProjMorphism.ToSpecZero.projHomOfIsAmple_toSpecZero,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp, over_eq_toSpecΓ_comp k]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  show degZeroRingHom L (GradedRingHom.gradedZeroRingHom _ (toGradingZeroOf C c)) =
    baseRingHom k X c
  have h : GradedRingHom.gradedZeroRingHom (weierstrassGradedHom
      (Stacks.AmpleFiniteAvoidance.grading L) C φ hker (algebraMap_mem_grading_zero L k) hv)
        (toGradingZeroOf C c) = ⟨degreeZeroHom L (baseRingHom k X c), ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    show φ (MvPolynomial.C c) = _
    rw [MvPolynomial.algHom_C]
    rfl
  rw [h, degZeroRingHom_degreeZeroHom]

/-- **The morphism `X ⟶ projOf C` is an isomorphism** when `X ⟶ Spec Γ(X, 𝒪_X)` is universally
closed. -/
theorem isIso_weierstrassModelHom (hX : UniversallyClosed X.toSpecΓ) :
    IsIso (weierstrassModelHom L k hL C φ hker hv hsurj) := by
  have := Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple L hL hX
  have := isIso_map_weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C φ hker
    (algebraMap_mem_grading_zero L k) hv hsurj
  exact IsIso.comp_isIso' (f := projHomOfIsAmple L hL) (h := (Proj.map (weierstrassGradedHom
      (Stacks.AmpleFiniteAvoidance.grading L) C φ hker (algebraMap_mem_grading_zero L k) hv)
      (Proj.irrelevant_le_map_of_surjective _ (bijective_weierstrassRingHom C φ hker hsurj).2) :
        Proj (Stacks.AmpleFiniteAvoidance.grading L) ⟶ Proj (gradingOf C))) inferInstance
    inferInstance

section ZeroSection

variable {k}

/-- The point of `Spec (Spec.map β)` at the closed point of a field is the kernel of `β`, so it
lies in `D(r)` exactly when `β r ≠ 0`. -/
theorem SpecMap_closedPoint_mem_basicOpen_iff {R : Type u} [CommRing R] (β : R →+* k) (r : R) :
    Spec.map (CommRingCat.ofHom β) (IsLocalRing.closedPoint k) ∈
        PrimeSpectrum.basicOpen r ↔ β r ≠ 0 := by
  show r ∉ (PrimeSpectrum.comap β (IsLocalRing.closedPoint k)).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, IsLocalRing.closedPoint,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]

/-- **A rational point of the plane cubic outside the chart `D₊(z)` is the point at infinity**:
a section `σ` of the plane cubic of `C` over `k` whose point does not lie in `D₊(z)` is the zero
section `(0 : 1 : 0)`. -/
theorem eq_zeroOf_of_notMem_basicOpenOf (C' : WeierstrassCurve k) (σ : Spec (.of k) ⟶ projOf C')
    (hσ : σ ≫ projectionOf C' = 𝟙 _)
    (hpt : σ (IsLocalRing.closedPoint k) ∉ basicOpenOf C' (coordOf C' 2)) : σ = zeroOf C' := by
  have hrange : Set.range σ ⊆ Set.range (chartY C') := by
    rintro _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    obtain ⟨q, hq⟩ : σ (IsLocalRing.closedPoint k) ∈ Set.range (zeroOf C') := by
      rw [range_zeroOf]
      exact hpt
    rw [← hq, zeroOf_eq_chartY]
    exact ⟨_, rfl⟩
  set τ := IsOpenImmersion.lift (chartY C') σ hrange
  have hτσ : τ ≫ chartY C' = σ := IsOpenImmersion.lift_fac _ _ _
  set β := (Spec.preimage τ).hom
  have hτβ : τ = Spec.map (CommRingCat.ofHom β) := (Spec.map_preimage τ).symm
  -- `β` is a `k`-algebra map
  have halg : ∀ a : k, β (algebraMap k (ChartYRing C') a) = a := by
    have h1 : Spec.map (CommRingCat.ofHom β) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (ChartYRing C'))) = 𝟙 _ := by
      rw [← hτβ, ← chartY_projectionOf, ← Category.assoc, hτσ, hσ]
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at h1
    intro a
    exact congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of k => g.hom a) h1
  -- the coordinates `X` and `Z` vanish
  have hZ : β (chartYZ C') = 0 := by
    by_contra hne
    apply hpt
    rw [← hτσ]
    show τ (IsLocalRing.closedPoint k) ∈ chartY C' ⁻¹ᵁ basicOpenOf C' (coordOf C' 2)
    rw [chartY, specPoint_preimage_basicOpenOf C' _ _ one_pos (coordOf_mem C' 2),
      chartYHom_coordOf_two, hτβ]
    exact (SpecMap_closedPoint_mem_basicOpen_iff β _).mpr hne
  have hX : β (chartYX C') = 0 := by
    have : (RingHom.ker β).IsPrime := RingHom.ker_isPrime β
    exact RingHom.mem_ker.mp (chartYX_mem_of_chartYZ_mem C' _ (RingHom.mem_ker.mpr hZ))
  have hβε : β = chartYEvalZero C' := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
    · show β (AdjoinRoot.of _ (Polynomial.C a)) = chartYEvalZero C' (AdjoinRoot.of _ _)
      rw [← algebraMap_chartYRing, halg, chartYEvalZero_algebraMap]
    · show β (chartYZ C') = chartYEvalZero C' (chartYZ C')
      rw [hZ, chartYEvalZero_chartYZ]
    · show β (chartYX C') = chartYEvalZero C' (chartYX C')
      rw [hX, chartYEvalZero_chartYX]
  rw [← hτσ, hτβ, hβε, zeroOf_eq_chartY]

end ZeroSection

end AlgebraicGeometry.GenusOne

end
