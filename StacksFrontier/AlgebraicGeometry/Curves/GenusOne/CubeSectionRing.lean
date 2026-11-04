module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointDivisorData
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseRestrict

/-!
# The section ring of `𝒪_X(p)^{⊗ 3}` on a curve of genus one

Let `X` be proper and smooth of relative dimension one over a field `k`, with
`dim_k H⁰(X, 𝒪_X) = 1` and genus one, let `p` be a `k`-rational point and `s` the canonical
section of `𝒪_X(p)`. The section ring of `𝒪_X(p)^{⊗ 3}`, with `s³` in degree one and the order
at `p`, is an instance of the abstract genus-one section ring `Stacks.GenusOneSectionRing.Data`
with `d = 3`: the `m`-th graded piece is `H⁰(X, 𝒪_X(p)^{⊗ 3m})`, of dimension `3m`.

## Main definitions

* `AlgebraicGeometry.GenusOne.cubeData`: the data.

## Main results

* `AlgebraicGeometry.GenusOne.cubeData_Z`: its distinguished element is `s³`.
* `AlgebraicGeometry.GenusOne.cubeData_ord`: the order of a section of `𝒪_X(p)^{⊗ 3}`, read in
  degree one, is its order in the section ring of `𝒪_X(p)`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors (IsEffectiveCartierDivisor)
open Stacks.SectionProduct (globalSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections secOf globalSection_secOf
  secOf_globalSection mulSections_globalSection)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection)
open Stacks.StalkOrder (stalkOrd sectionOrd)

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

section Order

variable {X : Scheme.{u}} {x : X} [IsDomain (X.presheaf.stalk x)]
  [IsDiscreteValuationRing (X.presheaf.stalk x)]

/-- **The order of a global section is invariant under an isomorphism of invertible modules.** -/
theorem stalkOrd_Γgerm_app_iso {M N : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
    [Stacks.Ample.IsInvertibleModule X N] (e : M ≅ N) (t : Γ(M, ⊤)) :
    stalkOrd N x ((N.presheaf.Γgerm x).hom (e.hom.app ⊤ t)) =
      stalkOrd M x ((M.presheaf.Γgerm x).hom t) := by
  rw [← Stacks.ModuleStalk.mapFun_Γgerm]
  exact Stacks.StalkOrder.stalkOrd_map_of_bijective (Stacks.ModuleStalk.equivOfIso e x).toLinearMap
    (Stacks.ModuleStalk.equivOfIso e x).bijective _

/-- **The order of a section of `L`, read in degree one of `Γ_*(X, L)`**, is its order in `L`. -/
theorem sectionOrd_secOf_twistOneSection (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (t : Γ(L, ⊤)) :
    sectionOrd x L (secOf L (twistOneSection L t)) = stalkOrd L x ((L.presheaf.Γgerm x).hom t) := by
  unfold sectionOrd Stacks.StalkOrder.sectionGerm
  rw [globalSection_secOf]
  exact stalkOrd_Γgerm_app_iso
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).symm t

/-- **The order of a product of global sections of tensor powers is the sum of the orders.** -/
theorem stalkOrd_mulSections (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {n m : ℕ}
    (a : Γ(natTensorPow L n, ⊤)) (b : Γ(natTensorPow L m, ⊤)) :
    stalkOrd (natTensorPow L (n + m)) x
        (((natTensorPow L (n + m)).presheaf.Γgerm x).hom (mulSections L a b)) =
      stalkOrd (natTensorPow L n) x (((natTensorPow L n).presheaf.Γgerm x).hom a) +
        stalkOrd (natTensorPow L m) x (((natTensorPow L m).presheaf.Γgerm x).hom b) := by
  have h := Stacks.StalkOrder.sectionOrd_mul (x := x) L (secOf L a) (secOf L b)
  unfold sectionOrd Stacks.StalkOrder.sectionGerm at h
  rwa [← mulSections_globalSection, globalSection_secOf, globalSection_secOf] at h

end Order

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  (h0 : Module.finrank k (structureSheafCohomology (X ↘ Spec (.of k)) 0) = 1)
  (hg : genus (X ↘ Spec (.of k)) = 1) (p : Spec (.of k) ⟶ X) (hp : p ≫ (X ↘ Spec (.of k)) = 𝟙 _)
  [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
    (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)]

/-- The canonical section `s` of `𝒪_X(p)`, in degree one of its section ring. -/
abbrev pointSectionOne : Γ(natTensorPow (pointDivisorSheaf p hp 1) 1, ⊤) :=
  globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
    (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)] in
/-- `s³` is the global section of the cube of `s` in the section ring. -/
theorem cube_pointSectionOne :
    ModuliEllipticCurves.PointedFamily.cube _ (pointSectionOne p hp) =
      globalSection X _ (mul (mul (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)
        (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1))
        (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)) := by
  rw [ModuliEllipticCurves.PointedFamily.cube, ModuliEllipticCurves.PointedFamily.sq,
    mulSections_globalSection, mulSections_globalSection]

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- **`s³` does not vanish off `p`.** -/
theorem mem_nonvanishingOpen_cube (y : X) (hy : y ≠ point p) :
    y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow (pointDivisorSheaf p hp 1) 3)
      (ModuliEllipticCurves.PointedFamily.cube _ (pointSectionOne p hp)) := by
  rw [cube_pointSectionOne]
  show y ∈ Stacks.AmpleFiniteAvoidance.nvOpen (pointDivisorSheaf p hp 1)
    (mul (mul (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)
      (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1))
      (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1))
  rw [Stacks.SectionRingChartMap.nvOpen_mul, Stacks.SectionRingChartMap.nvOpen_mul]
  have h := mem_nonvanishingOpen_pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1
    one_pos y hy
  exact ⟨⟨h, h⟩, h⟩

include h0 in
/-- **`s³` has order three at `p`.** -/
theorem stalkOrd_cube :
    letI := isIntegral (X ↘ Spec (.of k)) h0
    letI := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
    stalkOrd (natTensorPow (pointDivisorSheaf p hp 1) 3) (point p)
      (((natTensorPow (pointDivisorSheaf p hp 1) 3).presheaf.Γgerm (point p)).hom
        (ModuliEllipticCurves.PointedFamily.cube _ (pointSectionOne p hp))) = 3 := by
  let := isIntegral (X ↘ Spec (.of k)) h0
  let := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  rw [cube_pointSectionOne]
  show sectionOrd (point p) (pointDivisorSheaf p hp 1)
    (mul (mul (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)
      (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1))
      (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)) = 3
  rw [Stacks.StalkOrder.sectionOrd_mul, Stacks.StalkOrder.sectionOrd_mul,
    sectionOrd_pointSection]
  rfl

include h0 hg in
/-- **`dim_k H⁰(X, (𝒪_X(p)^{⊗ 3})^{⊗ m}) = 3m`** for `m ≥ 1`. -/
theorem finrank_gradingK_cube {m : ℕ} (hm : 1 ≤ m) :
    Module.finrank k (gradingK (natTensorPow (pointDivisorSheaf p hp 1) 3) k m) = 3 * m := by
  rw [finrank_gradingK, finrank_cohomologyOverField_eq_of_iso k _
    (Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso _ 3 m) 0,
    finrank_cohomologyOverField_zero_pointDivisor h0 hg p hp 1 one_pos (by omega), one_mul]

include h0 hg in
/-- **The section ring of `𝒪_X(p)^{⊗ 3}` as an abstract genus-one section ring**, with `s³` in
degree one. -/
def cubeData :
    letI := isIntegral (X ↘ Spec (.of k)) h0
    letI := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
    Stacks.GenusOneSectionRing.Data (gradingK (natTensorPow (pointDivisorSheaf p hp 1) 3) k) 3 :=
  letI := isIntegral (X ↘ Spec (.of k)) h0
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  sectionRingData (natTensorPow (pointDivisorSheaf p hp 1) 3) (point p) k
    (exists_sub_Γgerm_mem_maximalIdeal (X ↘ Spec (.of k)) p hp)
    (bijective_globalSectionsHom (X ↘ Spec (.of k)) h0).2
    (secOf _ (twistOneSection _ (ModuliEllipticCurves.PointedFamily.cube _ (pointSectionOne p hp))))
    (fun y hy => by
      rw [globalSection_secOf,
        Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.nonvanishingOpen_twistOneSection]
      exact mem_nonvanishingOpen_cube p hp y hy)
    (by
      rw [sectionOrd_secOf_twistOneSection]
      exact stalkOrd_cube h0 p hp)
    (fun m =>
      have : FiniteDimensional k (cohomologyOverField k (X ↘ Spec (.of k))
          (natTensorPow (natTensorPow (pointDivisorSheaf p hp 1) 3) m) 0) :=
        finiteDimensional_cohomologyOverField_natTensorPow (X ↘ Spec (.of k)) _ m 0
      finiteDimensional_gradingK _ k m)
    (fun m hm => (finrank_gradingK_cube h0 hg p hp hm).ge)
    ⟨1, fun m hm => (finrank_gradingK_cube h0 hg p hp hm).le⟩

include h0 hg in
/-- **The order of a section of `𝒪_X(p)^{⊗ 3}`, read in degree one**, is its order at `p`. -/
theorem cubeData_ord (t : Γ(natTensorPow (pointDivisorSheaf p hp 1) 3, ⊤)) :
    letI := isIntegral (X ↘ Spec (.of k)) h0
    letI := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
    (cubeData h0 hg p hp).ord (DirectSum.of (powSections _) 1 (secOf _ (twistOneSection _ t))) =
      stalkOrd (natTensorPow (pointDivisorSheaf p hp 1) 3) (point p)
        (((natTensorPow (pointDivisorSheaf p hp 1) 3).presheaf.Γgerm (point p)).hom t) := by
  let := isIntegral (X ↘ Spec (.of k)) h0
  let := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  show ringOrd _ (point p) _ = _
  rw [ringOrd_of, sectionOrd_secOf_twistOneSection]

/-- The distinguished element of `cubeData` is the cube `s³` of the section `s` of `𝒪_X(p)`
vanishing at `p`, placed in degree one. -/
theorem cubeData_Z :
    (cubeData h0 hg p hp).Z = DirectSum.of (powSections _) 1 (secOf _ (twistOneSection _
      (ModuliEllipticCurves.PointedFamily.cube _ (pointSectionOne p hp)))) :=
  rfl

include h0 in
/-- **`𝒪_X(p)^{⊗ 3}` is ample**: it has degree three. -/
theorem isAmple_cube :
    Stacks.Ample.IsAmple X (natTensorPow (pointDivisorSheaf p hp 1) 3) := by
  have := isCurve (X ↘ Spec (.of k)) h0
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X ↘ Spec (.of k))).le
  have hdeg1 := invertibleCurveDegree_vanishingIdeal_point_pow (X ↘ Spec (.of k)) h0 hdim p hp 1
  have hdeg3 := invertibleCurveDegree_tensorPower_eq_mul_of_isCurve k (X ↘ Spec (.of k)) hdim
    (pointDivisorSheaf p hp 1) (3 : ℕ)
  rw [invertibleCurveDegree_eq_of_iso k _ hdim (tensorPowerIsoNatTensorPow _ 3), hdeg1] at hdeg3
  exact Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X _
    ((isAmple_iff_invertibleCurveDegree_pos k (X ↘ Spec (.of k)) hdim _).mpr
      (by rw [hdeg3]; norm_num))

end AlgebraicGeometry.GenusOne

end
