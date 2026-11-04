module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.CubeSectionRing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassModelSections
public import StacksFrontier.AlgebraicGeometry.EllipticCurve.DiscriminantSmoothCubic
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationFieldSections

/-!
# The morphism to a plane cubic given by `s x, y, s³` on an elliptic curve over a field

Let `(E, f, 0)` be an elliptic curve over a field `k`: a pointed family, proper and smooth of
relative dimension one, with `dim_k H⁰(E, 𝒪_E) = 1` and genus one. Let `s` be the canonical
section of `O(0)`, and `x ∈ Γ(O(0)^{⊗ 2})`, `y ∈ Γ(O(0)^{⊗ 3})` sections that are not multiples
of `s`. For every Weierstrass curve `C` over `k` whose cubic is satisfied by the three sections
`s x, y, s³` of `O(0)^{⊗ 3}`, the morphism `E ⟶ projOf C` they define is an isomorphism, and the
discriminant of `C` is a unit.

## Main results

* `AlgebraicGeometry.GenusOne.isIso_cubicHomOfSections`: the statement for a curve of genus one
  with a rational point `p`, in terms of `𝒪_X(p)`.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.isIso_cubicHomOfSections`: the statement
  for a pointed family over a field, in terms of `O(0)`.

## The argument

The section ring of `L = 𝒪_X(p)^{⊗ 3}`, with `s³` in degree one, is a genus-one section ring with
`d = 3` (`AlgebraicGeometry.GenusOne.cubeData`), in which `s x` and `y` have orders one and zero.
So `s x, y, s³` generate it, and a Weierstrass polynomial they satisfy generates the relations
(`Stacks.GenusOneSectionRing.aeval_surjective`,
`Stacks.GenusOneSectionRing.mem_span_of_aeval_eq_zero`). The cubic of `C` is satisfied in the
section ring because it is satisfied on every chart. `L` is ample, of degree three, so the morphism
`X ⟶ projOf C` of the presentation is an isomorphism (Stacks Tag 0C6J), and it is the morphism
given by the three sections. Finally `projOf C` is smooth, being isomorphic to `X`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.GradedSections (powSections sectionRing)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors
open Stacks.SectionProduct (globalSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections secOf globalSection_secOf)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection)
open Stacks.ProjectiveFromSections (nvCover)
open Stacks.StalkOrder (stalkOrd)
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

universe u

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

namespace AlgebraicGeometry.GenusOne

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  (h0 : Module.finrank k (structureSheafCohomology (X ↘ Spec (.of k)) 0) = 1)
  (hg : genus (X ↘ Spec (.of k)) = 1) (p : Spec (.of k) ⟶ X) (hp : p ≫ (X ↘ Spec (.of k)) = 𝟙 _)
  [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
    (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)]

/-- The three sections `s x, y, s³` of `𝒪_X(p)^{⊗ 3}`. -/
abbrev cubeSections (x : Γ(natTensorPow (pointDivisorSheaf p hp 1) 2, ⊤))
    (y : Γ(natTensorPow (pointDivisorSheaf p hp 1) 3, ⊤)) :
    Fin 3 → Γ(natTensorPow (pointDivisorSheaf p hp 1) 3, ⊤) :=
  ![mulSections _ (pointSectionOne p hp) x, y,
    ModuliEllipticCurves.PointedFamily.cube _ (pointSectionOne p hp)]

include h0 hg in
/-- **The morphism to a plane cubic given by `s x, y, s³` is an isomorphism**, and the
discriminant of the cubic is a unit, on a curve of genus one with a rational point `p`, for
sections `x, y` of `𝒪_X(2p)`, `𝒪_X(3p)` not divisible by `s`. -/
theorem isIso_cubicHomOfSections {x : Γ(natTensorPow (pointDivisorSheaf p hp 1) 2, ⊤)}
    (hx : ∀ t : Γ(natTensorPow (pointDivisorSheaf p hp 1) 1, ⊤),
      mulSections _ (pointSectionOne p hp) t ≠ x)
    {y : Γ(natTensorPow (pointDivisorSheaf p hp 1) 3, ⊤)}
    (hy : ∀ t : Γ(natTensorPow (pointDivisorSheaf p hp 1) 2, ⊤),
      mulSections _ (pointSectionOne p hp) t ≠ y)
    (C : WeierstrassCurve k) (hrel : SatisfiesCubic C (X ↘ Spec (.of k)) (cubeSections p hp x y))
    (hcov : IsOpenCover (nvCover (cubeSections p hp x y))) :
    IsIso (cubicHomOfSections hrel hcov) ∧ IsUnit C.Δ := by
  have := isIntegral (X ↘ Spec (.of k)) h0
  have := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  have := nontrivial_sectionRing h0 (natTensorPow (pointDivisorSheaf p hp 1) 3)
  set D := cubeData h0 hg p hp with hD
  have hmem : ∀ j, degOneElt _ (cubeSections p hp x y j) ∈
      gradingK (natTensorPow (pointDivisorSheaf p hp 1) 3) k 1 :=
    fun j => ⟨_, rfl⟩
  -- the orders of `s x` and `y`
  have hord : ∀ (n : ℕ) (z : Γ(natTensorPow (pointDivisorSheaf p hp 1) (1 + n), ⊤)),
      (∀ t : Γ(natTensorPow (pointDivisorSheaf p hp 1) n, ⊤),
        mulSections _ (pointSectionOne p hp) t ≠ z) →
      stalkOrd (natTensorPow (pointDivisorSheaf p hp 1) (1 + n)) (point p)
        (((natTensorPow (pointDivisorSheaf p hp 1) (1 + n)).presheaf.Γgerm (point p)).hom z) =
          0 := fun n z hz => by
    have h := ord_ringElt_eq_zero h0 hg p hp z hz
    change ringOrd _ (point p) _ = _ at h
    rw [ringOrd_of] at h
    unfold Stacks.StalkOrder.sectionOrd Stacks.StalkOrder.sectionGerm at h
    rw [globalSection_secOf] at h
    exact h
  have hx0 := hord 1 x hx
  have hy0 := hord 2 y hy
  have hσ1 : stalkOrd (natTensorPow (pointDivisorSheaf p hp 1) 1) (point p)
      (((natTensorPow (pointDivisorSheaf p hp 1) 1).presheaf.Γgerm (point p)).hom
        (pointSectionOne p hp)) = 1 :=
    sectionOrd_pointSection _ 1
  have hXo : D.ord (degOneElt _ (cubeSections p hp x y 0)) = 1 := by
    rw [hD, cubeData_ord]
    have h := stalkOrd_mulSections (x := point p) (pointDivisorSheaf p hp 1)
      (pointSectionOne p hp) x
    rw [hσ1, hx0, add_zero] at h
    exact h
  have hYo : D.ord (degOneElt _ (cubeSections p hp x y 1)) = 0 := by
    rw [hD, cubeData_ord]
    exact hy0
  have hvec : ![degOneElt _ (cubeSections p hp x y 0), degOneElt _ (cubeSections p hp x y 1),
      D.Z] = fun j => degOneElt _ (cubeSections p hp x y j) := by
    funext j
    fin_cases j <;> rfl
  -- the presentation
  have hC := aeval_cubicOf_eq_zero k hrel hcov
  have hsurj := Stacks.GenusOneSectionRing.aeval_surjective D (hmem 0) hXo (hmem 1) hYo
  rw [hvec] at hsurj
  have hker : RingHom.ker (MvPolynomial.aeval (fun j => degOneElt _ (cubeSections p hp x y j)) :
      MvPolynomial (Fin 3) k →ₐ[k] sectionRing (natTensorPow (pointDivisorSheaf p hp 1) 3)) =
        Ideal.span {C.toProjective.polynomial} := by
    apply le_antisymm
    · intro q hq
      refine Stacks.GenusOneSectionRing.mem_span_of_aeval_eq_zero D (hmem 0) hXo (hmem 1) hYo C
        ?_ ?_
      · rw [hvec]; exact hC
      · rw [hvec]; exact RingHom.mem_ker.1 hq
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact RingHom.mem_ker.2 hC
  have hv : ∀ i, (MvPolynomial.aeval (fun j => degOneElt _ (cubeSections p hp x y j)) :
      MvPolynomial (Fin 3) k →ₐ[k] sectionRing (natTensorPow (pointDivisorSheaf p hp 1) 3))
        (MvPolynomial.X i) ∈ Stacks.AmpleFiniteAvoidance.grading _ 1 := fun i => by
    rw [MvPolynomial.aeval_X]
    exact ⟨_, rfl⟩
  -- the isomorphism
  have hL := isAmple_cube h0 p hp
  have hUC : UniversallyClosed X.toSpecΓ :=
    Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ (X ↘ Spec (.of k))
  have hiso := isIso_weierstrassModelHom _ k hL C _ hker hv hsurj hUC
  rw [weierstrassModelHom_eq_cubicHomOfSections k hL hker hv hsurj hrel hcov] at hiso
  refine ⟨hiso, ?_⟩
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have hproj : projectionOf C = inv (cubicHomOfSections hrel hcov) ≫ (X ↘ Spec (.of k)) :=
    (IsIso.eq_inv_comp _).mpr (cubicHomOfSections_projectionOf hrel hcov)
  have : Smooth (projectionOf C) := by rw [hproj]; infer_instance
  exact isUnit_Δ_of_smooth C this

end AlgebraicGeometry.GenusOne

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

variable {k : Type u} [Field k] (F : PointedFamily (Spec (.of k))) [IsProper F.map]
  [SmoothOfRelativeDimension 1 F.map]
  (h0 : Module.finrank k (structureSheafCohomology F.map 0) = 1) (h1 : genus F.map = 1)

include h0 h1 in
/-- **The morphism to a plane cubic given by `s x, y, s³` is an isomorphism**, for an invertible
module `L` equal to `𝒪(0(Spec k))` with `s` its canonical section, and `x, y` sections of
`L^{⊗ 2}`, `L^{⊗ 3}` not divisible by `s`; and the discriminant of the cubic is a unit. -/
theorem isIso_cubicHomOfSections_of_eq
    [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point F.zero}, GenusOne.isClosed_point F.map F.zero F.zero_map⟩ :
        Closeds F.total) ^ 1)]
    (L : F.total.Modules) [Stacks.Ample.IsInvertibleModule F.total L]
    (hL : L = modulesInvertibleSheaf (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point F.zero}, GenusOne.isClosed_point F.map F.zero F.zero_map⟩ :
        Closeds F.total) ^ 1))
    (σ : Γ(natTensorPow L 1, ⊤)) (hσ : HEq σ (globalSection F.total _
      (GenusOne.pointSection (GenusOne.isClosed_point F.map F.zero F.zero_map) 1)))
    {x : Γ(natTensorPow L 2, ⊤)} (hx : x ∉ Set.range (mulSections L (m := 1) σ))
    {y : Γ(natTensorPow L 3, ⊤)} (hy : y ∉ Set.range (mulSections L (m := 2) σ))
    (C : WeierstrassCurve k)
    (hrel : SatisfiesCubic C F.map
      (![mulSections L σ x, y, cube L σ] : Fin 3 → Γ(natTensorPow L 3, ⊤)))
    (hcov : IsOpenCover (nvCover
      (![mulSections L σ x, y, cube L σ] : Fin 3 → Γ(natTensorPow L 3, ⊤)))) :
    IsIso (cubicHomOfSections hrel hcov) ∧ IsUnit C.Δ := by
  subst hL
  obtain rfl := eq_of_heq hσ
  let : F.total.Over (Spec (.of k)) := ⟨F.map⟩
  have : IsProper (F.total ↘ Spec (.of k)) := ‹IsProper F.map›
  have : SmoothOfRelativeDimension 1 (F.total ↘ Spec (.of k)) := ‹_›
  exact GenusOne.isIso_cubicHomOfSections h0 h1 F.zero F.zero_map
    (fun t ht => hx ⟨t, ht⟩) (fun t ht => hy ⟨t, ht⟩) C hrel hcov

include h0 h1 in
/-- **The morphism to a plane cubic given by `s x, y, s³` on an elliptic curve over a field is
an isomorphism, and the discriminant is a unit.** Here `s` is the canonical section of `O(0)`,
`x ∈ Γ(O(0)^{⊗ 2})` and `y ∈ Γ(O(0)^{⊗ 3})` are not multiples of `s`, and `C` is any Weierstrass
curve over `k` whose cubic the three sections `s x, y, s³` of `O(0)^{⊗ 3}` satisfy. -/
theorem isIso_cubicHomOfSections {x : Γ(natTensorPow F.zeroSheaf 2, ⊤)}
    (hx : x ∉ Set.range (mulSections F.zeroSheaf (m := 1) F.zeroSection))
    {y : Γ(natTensorPow F.zeroSheaf 3, ⊤)}
    (hy : y ∉ Set.range (mulSections F.zeroSheaf (m := 2) F.zeroSection))
    (C : WeierstrassCurve k)
    (hrel : SatisfiesCubic C F.map (![mulSections F.zeroSheaf F.zeroSection x, y,
      cube F.zeroSheaf F.zeroSection] : Fin 3 → Γ(natTensorPow F.zeroSheaf 3, ⊤)))
    (hcov : IsOpenCover (nvCover (![mulSections F.zeroSheaf F.zeroSection x, y,
      cube F.zeroSheaf F.zeroSection] : Fin 3 → Γ(natTensorPow F.zeroSheaf 3, ⊤)))) :
    IsIso (cubicHomOfSections hrel hcov) ∧ IsUnit C.Δ := by
  let : F.total.Over (Spec (.of k)) := ⟨F.map⟩
  have : IsProper (F.total ↘ Spec (.of k)) := ‹IsProper F.map›
  have : SmoothOfRelativeDimension 1 (F.total ↘ Spec (.of k)) := ‹_›
  have := GenusOne.isEffectiveCartierDivisor_pow F.map h0 F.zero F.zero_map 1
  exact F.isIso_cubicHomOfSections_of_eq h0 h1 F.zeroSheaf
    (congrArg invertibleSheaf' F.zeroDivisor_eq_pointDivisor) F.zeroSection
    (by
      have key : ∀ (D D' : F.total.IdealSheafData), D = D' →
          HEq (twistOneSection (invertibleSheaf' D) ((canonicalSection' D).val (op ⊤)))
            (twistOneSection (invertibleSheaf' D') ((canonicalSection' D').val (op ⊤))) := by
        rintro D _ rfl
        rfl
      exact (key _ _ F.zeroDivisor_eq_pointDivisor).trans
        (heq_of_eq (GenusOne.globalSection_pointSection _ 1).symm)) hx hy C hrel hcov

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
