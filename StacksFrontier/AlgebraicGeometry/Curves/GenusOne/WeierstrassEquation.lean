module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveAmple
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.SectionRingData
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.TwistDimensions
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassModel
public import StacksFrontier.AlgebraicGeometry.EllipticCurve.DiscriminantSmoothCubic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# A curve of genus one with a rational point has a Weierstrass equation

Let `k` be a field and `X` a proper scheme over `k`, smooth of relative dimension one, with
`dim_k H⁰(X, 𝒪_X) = 1` and genus one, and let `p` be a `k`-rational point. Then `X` is isomorphic
over `k` to the plane cubic `zy² + a₁xyz + a₃yz² = x³ + a₂x²z + a₄xz² + a₆z³` of a Weierstrass
curve with invertible discriminant, by an isomorphism carrying `p` to the point `(0 : 1 : 0)` at
infinity.

## Main results

* `AlgebraicGeometry.GenusOne.exists_weierstrassCurve_iso`: the statement above.

## The argument

Put `L = 𝒪_X(3p)`, with canonical section `Z` vanishing exactly at `p`, to order three.
Riemann–Roch and Serre vanishing bound the dimensions of the graded pieces of the section ring
`Γ_*(X, L)`, and the order at `p` makes `Γ_*(X, L)` an instance of
`Stacks.GenusOneSectionRing.Data`; the abstract theory then produces elements `X', Y'` of degree
one and orders one and zero, and a Weierstrass curve `C` such that `x, y, z ↦ λX', νY', Z` presents
`Γ_*(X, L)` as `k[x, y, z]/(F)`. The line bundle `L` is ample since its degree is three ([Stacks,
Tag 0B5X]), so the canonical morphism `X ⟶ Proj Γ_*(X, L)` is an isomorphism ([Stacks, Tag 0C6J]),
and `Proj` of the presentation identifies `Proj Γ_*(X, L)` with the plane cubic of `C`. The point
`p` lies off the open `X_Z`, which is the preimage of the chart `z ≠ 0`, so it goes to the point at
infinity. Finally the plane cubic is smooth over `k`, being isomorphic to `X`, so its discriminant
is a unit.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.GradedSections (powSections sectionRing)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors (modulesInvertibleSheaf)
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

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A curve of genus one with a rational point has a Weierstrass equation.** Let `X` be proper
and smooth of relative dimension one over a field `k`, with `dim_k H⁰(X, 𝒪_X) = 1` and genus one,
and let `p` be a section of `X ⟶ Spec k`. Then there are a Weierstrass curve `C` over `k` with
invertible discriminant and an isomorphism of `X` with its plane cubic over `k` carrying `p` to the
point `(0 : 1 : 0)`. -/
theorem exists_weierstrassCurve_iso [IsProper f] [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (hg : genus f = 1)
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ∃ (C : WeierstrassCurve k) (_ : C.IsElliptic) (e : X ≅ projOf C),
      e.hom ≫ projectionOf C = f ∧ p ≫ e.hom = zeroOf C := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have := isIntegral f h0
  have := isCurve f h0
  have := isDiscreteValuationRing_stalk f h0 p hp
  have hx := isClosed_point f p hp
  have := isEffectiveCartierDivisor_pow f h0 p hp 3
  set L := modulesInvertibleSheaf
    (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, hx⟩ : Closeds X) ^ 3) with hLdef
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hdeg : invertibleCurveDegree k f hdim L = (3 : ℕ) :=
    invertibleCurveDegree_vanishingIdeal_point_pow f h0 hdim p hp 3
  -- the abstract data
  have hfin : ∀ m, FiniteDimensional k (gradingK L k m) := fun m =>
    have : FiniteDimensional k (cohomologyOverField k (X ↘ Spec (.of k)) (natTensorPow L m) 0) :=
      finiteDimensional_cohomologyOverField_natTensorPow f L m 0
    finiteDimensional_gradingK L k m
  have : Nontrivial (sectionRing L) := by
    have := nontrivial_globalSections f h0
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have h1 : (1 : Stacks.AmpleFiniteAvoidance.grading L 0) = 0 := Subtype.ext h
    have h2 := congrArg (Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom L) h1
    rw [map_one, map_zero] at h2
    exact one_ne_zero h2
  have hle : ∀ m, 1 ≤ m → 3 * m ≤ Module.finrank k (gradingK L k m) := fun m _ => by
    rw [finrank_gradingK]
    exact mul_le_finrank_cohomologyOverField_zero_natTensorPow f h0 hg hdim L hdeg m
  have hev : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → Module.finrank k (gradingK L k m) ≤ 3 * m := by
    obtain ⟨m₀, hm₀⟩ := exists_forall_finrank_cohomologyOverField_zero_natTensorPow_le f h0 hg
      hdim L hdeg (by norm_num)
    exact ⟨m₀, fun m hm => by rw [finrank_gradingK]; exact hm₀ m hm⟩
  let D := sectionRingData L (point p) k (exists_sub_Γgerm_mem_maximalIdeal f p hp)
    (bijective_globalSectionsHom f h0).2 (pointSection hx 3)
    (mem_nonvanishingOpen_pointSection hx 3 (by norm_num)) (sectionOrd_pointSection hx 3)
    hfin hle hev
  -- the Weierstrass presentation
  obtain ⟨X', hX', -, hX'o⟩ := (Stacks.GenusOneSectionRing.exists_ord_eq_iff D (by norm_num)
    le_rfl 1).mpr ⟨by norm_num, by norm_num⟩
  obtain ⟨Y', hY', -, hY'o⟩ := (Stacks.GenusOneSectionRing.exists_ord_eq_iff D (by norm_num)
    le_rfl 0).mpr ⟨by norm_num, by norm_num⟩
  obtain ⟨C, l, n, -, -, hsurj, hker⟩ :=
    Stacks.GenusOneSectionRing.exists_weierstrassCurve D hX' hX'o hY' hY'o
  set φ := (MvPolynomial.aeval ![l • X', n • Y', D.Z] :
    MvPolynomial (Fin 3) k →ₐ[k] sectionRing L) with hφ
  have hv : ∀ i, φ (MvPolynomial.X i) ∈ Stacks.AmpleFiniteAvoidance.grading L 1 := by
    intro i
    rw [hφ, MvPolynomial.aeval_X]
    fin_cases i
    · exact (gradingK L k 1).smul_mem l hX'
    · exact (gradingK L k 1).smul_mem n hY'
    · exact D.Z_mem
  -- the isomorphism
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L
      ((isAmple_iff_invertibleCurveDegree_pos k f hdim L).mpr (by rw [hdeg]; norm_num))
  have hUC : UniversallyClosed X.toSpecΓ :=
    Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ f
  have := isIso_weierstrassModelHom L k hL C φ hker hv hsurj hUC
  set e := asIso (weierstrassModelHom L k hL C φ hker hv hsurj) with he
  have hover : e.hom ≫ projectionOf C = f := weierstrassModelHom_projectionOf L k hL C φ hker hv
    hsurj
  refine ⟨C, ?_, e, hover, ?_⟩
  · -- the discriminant is a unit
    have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    have hproj : projectionOf C = e.inv ≫ f := by rw [← hover, Iso.inv_hom_id_assoc]
    have : Smooth (projectionOf C) := by rw [hproj]; infer_instance
    exact isElliptic_of_smooth C
  · -- the point goes to infinity
    refine eq_zeroOf_of_notMem_basicOpenOf C _ (by rw [Category.assoc, hover, hp]) ?_
    intro hmem
    have hpre : point p ∈ e.hom ⁻¹ᵁ basicOpenOf C (coordOf C 2) := hmem
    change point p ∈ Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL ⁻¹ᵁ
      (Proj.map _ (Proj.irrelevant_le_map_of_surjective _
        (bijective_weierstrassRingHom C φ hker hsurj).2) ⁻¹ᵁ
          Proj.basicOpen (gradingOf C) (coordOf C 2)) at hpre
    rw [Proj.map_preimage_basicOpen] at hpre
    have hz : (weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C φ hker
        (algebraMap_mem_grading_zero L k) hv) (coordOf C 2) =
        DirectSum.of (powSections L) 1 (pointSection hx 3) := by
      change φ (MvPolynomial.X 2) = _
      rw [hφ, MvPolynomial.aeval_X]
      rfl
    rw [hz, Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL _
      one_pos] at hpre
    exact notMem_nonvanishingOpen_pointSection hx 3 (by norm_num) hpre

end AlgebraicGeometry.GenusOne

end
