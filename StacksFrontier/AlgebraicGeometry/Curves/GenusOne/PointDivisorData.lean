module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.SectionRingData
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.TwistDimensions
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassMonomials

/-!
# The section ring of `𝒪_X(d · p)` on a curve of genus one

Let `X` be proper and smooth of relative dimension one over a field `k`, with
`dim_k H⁰(X, 𝒪_X) = 1` and genus one, and let `p` be a `k`-rational point. For `d ≥ 1` the
section ring of `𝒪_X(d · p)`, with the canonical section `1_{d·p}` in degree one and the order at
`p`, is an instance of the abstract genus-one section ring `Stacks.GenusOneSectionRing.Data`.
Consequently `H⁰(X, 𝒪_X(d · p)^{⊗ m})` has dimension `d m` and the higher cohomology vanishes for
`m ≥ 1`.

## Main definitions

* `AlgebraicGeometry.GenusOne.pointDivisorData`: the data.

## Main results

* `AlgebraicGeometry.GenusOne.finrank_cohomologyOverField_zero_pointDivisor`:
  `dim_k H⁰(X, 𝒪_X(d · p)^{⊗ m}) = d m` for `m ≥ 1`.
* `AlgebraicGeometry.GenusOne.isZero_cohomologyOverField_pointDivisor`: `Hⁱ` vanishes for
  `i ≥ 1` and `m ≥ 1`.
* `AlgebraicGeometry.GenusOne.exists_basis_weierstrassMonomials`: for `d = 1`, if `x` and `y` are
  sections of `𝒪_X(2p)` and `𝒪_X(3p)` not divisible by the canonical section `s`, the six products
  `s⁶, s⁴x, s³y, s²x², sxy, x³` are a basis of `H⁰(X, 𝒪_X(6p))`, and `x³` has a nonzero
  coefficient in `y²`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.GradedSections (powSections sectionRing)
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors (modulesInvertibleSheaf IsEffectiveCartierDivisor)
open Stacks.SectionProduct (globalSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections secOf globalSection_secOf
  secOf_globalSection mulSections_globalSection)

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

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  (h0 : Module.finrank k (structureSheafCohomology (X ↘ Spec (.of k)) 0) = 1)
  (hg : genus (X ↘ Spec (.of k)) = 1) (p : Spec (.of k) ⟶ X) (hp : p ≫ (X ↘ Spec (.of k)) = 𝟙 _)
  (d : ℕ)
  [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
    (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ d)]

/-- The invertible module `𝒪_X(d · p)`. -/
abbrev pointDivisorSheaf : X.Modules :=
  modulesInvertibleSheaf (Scheme.IdealSheafData.vanishingIdeal
    (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ d)

include h0 hg in
/-- **The section ring of `𝒪_X(d · p)` as an abstract genus-one section ring.** -/
def pointDivisorData (hd : 0 < d) :
    letI := isIntegral (X ↘ Spec (.of k)) h0
    letI := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
    Stacks.GenusOneSectionRing.Data (gradingK (pointDivisorSheaf p hp d) k) d :=
  letI := isIntegral (X ↘ Spec (.of k)) h0
  letI := isCurve (X ↘ Spec (.of k)) h0
  letI := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X ↘ Spec (.of k))).le
  have hdeg : invertibleCurveDegree k (X ↘ Spec (.of k)) hdim (pointDivisorSheaf p hp d) = d :=
    invertibleCurveDegree_vanishingIdeal_point_pow (X ↘ Spec (.of k)) h0 hdim p hp d
  sectionRingData (pointDivisorSheaf p hp d) (point p) k
    (exists_sub_Γgerm_mem_maximalIdeal (X ↘ Spec (.of k)) p hp)
    (bijective_globalSectionsHom (X ↘ Spec (.of k)) h0).2
    (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) d)
    (mem_nonvanishingOpen_pointSection _ d hd) (sectionOrd_pointSection _ d)
    (fun m =>
      have : FiniteDimensional k (cohomologyOverField k (X ↘ Spec (.of k))
          (natTensorPow (pointDivisorSheaf p hp d) m) 0) :=
        finiteDimensional_cohomologyOverField_natTensorPow (X ↘ Spec (.of k))
          (pointDivisorSheaf p hp d) m 0
      finiteDimensional_gradingK _ k m)
    (fun m _ => by
      rw [finrank_gradingK]
      exact mul_le_finrank_cohomologyOverField_zero_natTensorPow _ h0 hg hdim _ hdeg m)
    (by
      obtain ⟨m₀, hm₀⟩ := exists_forall_finrank_cohomologyOverField_zero_natTensorPow_le _ h0 hg
        hdim _ hdeg hd
      exact ⟨m₀, fun m hm => by rw [finrank_gradingK]; exact hm₀ m hm⟩)

omit [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
include h0 in
/-- The section ring of an invertible module on `X` is nontrivial, since its degree-zero part is
`Γ(X, 𝒪_X) = k`. -/
theorem nontrivial_sectionRing (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] :
    Nontrivial (sectionRing L) := by
  have := nontrivial_globalSections (X ↘ Spec (.of k)) h0
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h1 : (1 : Stacks.AmpleFiniteAvoidance.grading L 0) = 0 := Subtype.ext h
  have h2 := congrArg (Stacks.SectionRingProjMorphism.ToSpecZero.degZeroRingHom L) h1
  rw [map_one, map_zero] at h2
  exact one_ne_zero h2

include h0 hg in
/-- **`dim_k H⁰(X, 𝒪_X(d · p)^{⊗ m}) = d m`** for `d, m ≥ 1`. -/
theorem finrank_cohomologyOverField_zero_pointDivisor (hd : 0 < d) {m : ℕ} (hm : 1 ≤ m) :
    Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
      (natTensorPow (pointDivisorSheaf p hp d) m) 0) = d * m := by
  have := isIntegral (X ↘ Spec (.of k)) h0
  have := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  have := nontrivial_sectionRing h0 (pointDivisorSheaf p hp d)
  rw [← finrank_gradingK]
  exact Stacks.GenusOneSectionRing.finrank_eq (pointDivisorData h0 hg p hp d hd) hd hm

include h0 hg in
/-- **The higher cohomology of `𝒪_X(d · p)^{⊗ m}` vanishes** for `d, m ≥ 1`: in degree one by
Riemann–Roch and the dimension of `H⁰`, and above degree one because `X` is a curve. -/
theorem isZero_cohomologyOverField_pointDivisor (hd : 0 < d) {m : ℕ} (hm : 1 ≤ m) {i : ℕ}
    (hi : 0 < i) :
    IsZero (cohomologyOverField k (X ↘ Spec (.of k))
      (natTensorPow (pointDivisorSheaf p hp d) m) i) := by
  have := isCurve (X ↘ Spec (.of k)) h0
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X ↘ Spec (.of k))).le
  rcases Nat.lt_or_ge 1 i with h | h
  · exact isZero_cohomologyOverField_of_topologicalKrullDim_le k _ _ (d := 1)
      (by exact_mod_cast hdim) h
  · obtain rfl : i = 1 := le_antisymm h hi
    have hrr := finrank_cohomologyOverField_zero_sub_one_natTensorPow _ h0 hg hdim
      (pointDivisorSheaf p hp d) m
    rw [invertibleCurveDegree_vanishingIdeal_point_pow _ h0 hdim p hp d,
      finrank_cohomologyOverField_zero_pointDivisor h0 hg p hp d hd hm] at hrr
    have h1 : Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
        (natTensorPow (pointDivisorSheaf p hp d) m) 1) = 0 := by
      push_cast at hrr
      have : ((d * m : ℕ) : ℤ) = (m : ℤ) * d := by push_cast; ring
      omega
    have := finiteDimensional_cohomologyOverField_natTensorPow (X ↘ Spec (.of k))
      (pointDivisorSheaf p hp d) m 1
    exact (ModuleCat.isZero_iff_subsingleton).mpr (Module.finrank_zero_iff.mp h1)

section Basis

variable {Y : Scheme.{u}} (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]

/-- A global section of a tensor power, as a homogeneous element of the section ring. -/
abbrev ringElt {n : ℕ} (a : Γ(natTensorPow M n, ⊤)) : sectionRing M :=
  DirectSum.of (powSections M) n (secOf M a)

omit [Stacks.Ample.IsInvertibleModule Y M] in
/-- The homogeneous element of the product `mulSections M a b` of global sections of tensor
powers is the product of the homogeneous elements of `a` and `b` in the section ring. -/
theorem ringElt_mulSections {n m : ℕ} (a : Γ(natTensorPow M n, ⊤)) (b : Γ(natTensorPow M m, ⊤)) :
    ringElt M (mulSections M a b) = ringElt M a * ringElt M b := by
  rw [ringElt, ringElt, ringElt, Stacks.SectionProduct.of_mul_of]
  congr 1
  rw [← secOf_globalSection M (Stacks.GradedSections.mul (secOf M a) (secOf M b)),
    ← mulSections_globalSection, globalSection_secOf, globalSection_secOf]

omit [Stacks.Ample.IsInvertibleModule Y M] in
/-- The homogeneous element of the zero section of `M^{⊗ n}` is zero. -/
theorem ringElt_zero {n : ℕ} : ringElt M (0 : Γ(natTensorPow M n, ⊤)) = 0 := by
  rw [ringElt, show secOf M (0 : Γ(natTensorPow M n, ⊤)) = 0 from
    map_zero (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm, map_zero]

omit [Stacks.Ample.IsInvertibleModule Y M] in
/-- Distinct global sections of `M^{⊗ n}` give distinct elements of the section ring. -/
theorem ringElt_injective {n : ℕ} : Function.Injective (ringElt M (n := n)) := fun _ _ h =>
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y _).symm.injective
    (DirectSum.of_injective (β := powSections M) n h)

end Basis

/-- Homogeneous elements of the section ring lie in the corresponding graded piece. -/
private theorem ringElt_mem_gradingK {Y : Scheme.{u}} {K : Type u} [Field K]
    [Y.Over (Spec (.of K))] (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] {n : ℕ}
    (a : Γ(natTensorPow M n, ⊤)) : ringElt M a ∈ gradingK M K n :=
  ⟨_, rfl⟩

/-- The canonical section of `𝒪_X(p)` is the degree-one generator `Z` of the section ring. -/
private theorem pointDivisorData_Z [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)] :
    letI := isIntegral (X ↘ Spec (.of k)) h0
    letI := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
    (pointDivisorData h0 hg p hp 1 one_pos).Z = ringElt (pointDivisorSheaf p hp 1)
      (globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)) := by
  rw [ringElt, secOf_globalSection]
  rfl

include h0 hg in
/-- **A section of `𝒪_X(p)^{⊗ (1 + n)}` not divisible by the canonical section `s` has order zero
at `p`**: an element of positive order is `s` times an element of degree `n`. -/
theorem ord_ringElt_eq_zero
    [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)]
    {n : ℕ} (a : Γ(natTensorPow (pointDivisorSheaf p hp 1) (1 + n), ⊤))
    (ha : ∀ t : Γ(natTensorPow (pointDivisorSheaf p hp 1) n, ⊤), mulSections _
      (globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)) t ≠ a) :
    (pointDivisorData h0 hg p hp 1 one_pos).ord (ringElt (pointDivisorSheaf p hp 1) a) = 0 := by
  set σ := globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1) with hσ
  have := isIntegral (X ↘ Spec (.of k)) h0
  have := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  have := nontrivial_sectionRing h0 (pointDivisorSheaf p hp 1)
  set D := pointDivisorData h0 hg p hp 1 one_pos with hD
  have hZ : D.Z = ringElt (pointDivisorSheaf p hp 1) σ := pointDivisorData_Z h0 hg p hp
  have hmem := fun {n : ℕ} (a : Γ(natTensorPow (pointDivisorSheaf p hp 1) n, ⊤)) =>
    ringElt_mem_gradingK (K := k) (pointDivisorSheaf p hp 1) a
  have ha0 : ringElt (pointDivisorSheaf p hp 1) a ≠ 0 := by
    intro h
    apply ha 0
    apply ringElt_injective (pointDivisorSheaf p hp 1)
    rw [h, ringElt_mulSections, ringElt_zero, mul_zero]
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp (D.ord_ne_top (hmem a) ha0)
  rcases Nat.eq_zero_or_pos v with h | h
  · rw [← hv, h]; rfl
  · exfalso
    have h1 : ((1 * 1 : ℕ) : ℕ∞) ≤ D.ord (ringElt (pointDivisorSheaf p hp 1) a) := by
      rw [← hv]; exact_mod_cast h
    have hmem' : ringElt (pointDivisorSheaf p hp 1) a ∈
        gradingK (pointDivisorSheaf p hp 1) k (n + 1) := by
      rw [add_comm]; exact hmem a
    obtain ⟨b, ⟨t, rfl⟩, hb⟩ := D.exists_eq_Z_pow_mul hmem' h1
    apply ha (globalSection X _ t)
    apply ringElt_injective (pointDivisorSheaf p hp 1)
    rw [ringElt_mulSections, hb, pow_one D.Z]
    congr 1
    · exact hZ.symm
    · rw [ringElt, secOf_globalSection]

include h0 hg in
/-- **A Weierstrass basis of `H⁰(X, 𝒪_X(6p))`.** For `x ∈ Γ(𝒪_X(2p))` and `y ∈ Γ(𝒪_X(3p))` not
divisible by the canonical section `s` of `𝒪_X(p)`, the six products `s⁶, s⁴x, s³y, s²x², sxy,
x³` are a basis of `Γ(𝒪_X(6p))`, and the coefficient of `x³` in `y²` is nonzero. -/
theorem exists_basis_weierstrassMonomials
    [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)]
    (x : Γ(natTensorPow (pointDivisorSheaf p hp 1) 2, ⊤))
    (hx : ∀ t : Γ(natTensorPow (pointDivisorSheaf p hp 1) 1, ⊤), mulSections _
      (globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)) t ≠ x)
    (y : Γ(natTensorPow (pointDivisorSheaf p hp 1) 3, ⊤))
    (hy : ∀ t : Γ(natTensorPow (pointDivisorSheaf p hp 1) 2, ⊤), mulSections _
      (globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)) t ≠ y) :
    letI := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule k X
      (natTensorPow (pointDivisorSheaf p hp 1) 6)
    ∃ b : Module.Basis (Fin 6) k Γ(natTensorPow (pointDivisorSheaf p hp 1) 6, ⊤),
      (∀ i, b i = ModuliEllipticCurves.PointedFamily.weierstrassMonomials (pointDivisorSheaf p hp 1)
        (globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1)) x y i) ∧
      b.repr (mulSections (pointDivisorSheaf p hp 1) y y) 5 ≠ 0 := by
  set σ := globalSection X _ (pointSection (isClosed_point (X ↘ Spec (.of k)) p hp) 1) with hσ
  have := isIntegral (X ↘ Spec (.of k)) h0
  have := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  have := nontrivial_sectionRing h0 (pointDivisorSheaf p hp 1)
  set D := pointDivisorData h0 hg p hp 1 one_pos with hD
  have hZ : D.Z = ringElt (pointDivisorSheaf p hp 1) σ := pointDivisorData_Z h0 hg p hp
  have hmem := fun {n : ℕ} (a : Γ(natTensorPow (pointDivisorSheaf p hp 1) n, ⊤)) =>
    ringElt_mem_gradingK (K := k) (pointDivisorSheaf p hp 1) a
  have hordσ : D.ord (ringElt (pointDivisorSheaf p hp 1) σ) = 1 := by rw [← hZ]; exact D.ord_Z
  have hxo : D.ord (ringElt (pointDivisorSheaf p hp 1) x) = 0 :=
    ord_ringElt_eq_zero h0 hg p hp (n := 1) x hx
  have hyo : D.ord (ringElt (pointDivisorSheaf p hp 1) y) = 0 :=
    ord_ringElt_eq_zero h0 hg p hp (n := 2) y hy
  have hom : ∀ {n m : ℕ} (a : Γ(natTensorPow (pointDivisorSheaf p hp 1) n, ⊤))
      (b : Γ(natTensorPow (pointDivisorSheaf p hp 1) m, ⊤)),
      D.ord (ringElt (pointDivisorSheaf p hp 1) (mulSections (pointDivisorSheaf p hp 1) a b)) =
        D.ord (ringElt (pointDivisorSheaf p hp 1) a) +
          D.ord (ringElt (pointDivisorSheaf p hp 1) b) :=
    fun a b => by rw [ringElt_mulSections]; exact D.ord_mul (hmem a) (hmem b)
  set w := ModuliEllipticCurves.PointedFamily.weierstrassMonomials
    (pointDivisorSheaf p hp 1) σ x y with hw
  have hords : ∀ i, D.ord (ringElt (pointDivisorSheaf p hp 1) (w i)) =
      ((![6, 4, 3, 2, 1, 0] : Fin 6 → ℕ) i : ℕ∞) := by
    intro i
    fin_cases i <;>
      simp [hw, ModuliEllipticCurves.PointedFamily.weierstrassMonomials,
        ModuliEllipticCurves.PointedFamily.cube, ModuliEllipticCurves.PointedFamily.sq, hom,
        hordσ, hxo, hyo] <;> norm_num
  have hR0 : ∀ i, ringElt (pointDivisorSheaf p hp 1) (w i) ≠ 0 := fun i h => by
    have := hords i
    rw [h, D.ord_zero] at this
    exact ENat.top_ne_natCast _ this
  have hli : LinearIndependent k (fun i => ringElt (pointDivisorSheaf p hp 1) (w i)) :=
    have hinj : Function.Injective (![6, 4, 3, 2, 1, 0] : Fin 6 → ℕ) := by decide
    D.linearIndependent_of_ord _ (fun _ => 6) (fun i => hmem _) hR0 (fun i j _ h =>
      hinj (Nat.cast_inj.mp (((hords i).symm.trans h).trans (hords j))))
  let : Module k Γ(natTensorPow (pointDivisorSheaf p hp 1) 6, ⊤) :=
    Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule k X _
  set Φ := gradingKEquivSections (pointDivisorSheaf p hp 1) k 6 with hΦdef
  have hΦ : ∀ a : Γ(natTensorPow (pointDivisorSheaf p hp 1) 6, ⊤),
      Φ ⟨ringElt (pointDivisorSheaf p hp 1) a, hmem a⟩ = a := fun a => by
    have h1 : (⟨ringElt (pointDivisorSheaf p hp 1) a, hmem a⟩ :
          Stacks.AmpleFiniteAvoidance.grading (pointDivisorSheaf p hp 1) 6) =
        Stacks.ExternalGrading.summandEquiv (powSections (pointDivisorSheaf p hp 1)) 6
          (secOf (pointDivisorSheaf p hp 1) a) := Subtype.ext rfl
    change globalSection X _ ((Stacks.ExternalGrading.summandEquiv
      (powSections (pointDivisorSheaf p hp 1)) 6).symm
      ⟨ringElt (pointDivisorSheaf p hp 1) a, hmem a⟩) = a
    rw [h1, AddEquiv.symm_apply_apply, globalSection_secOf]
  have hΦs : ∀ a : Γ(natTensorPow (pointDivisorSheaf p hp 1) 6, ⊤),
      ((Φ.symm a : gradingK (pointDivisorSheaf p hp 1) k 6) :
        sectionRing (pointDivisorSheaf p hp 1)) = ringElt (pointDivisorSheaf p hp 1) a := fun a =>
    congrArg Subtype.val (Φ.symm_apply_eq.2 (hΦ a).symm)
  have hli' : LinearIndependent k w :=
    .of_comp Φ.symm.toLinearMap (.of_comp (gradingK (pointDivisorSheaf p hp 1) k 6).subtype
      (by convert hli using 2 with i; exact hΦs _))
  have hfr : Module.finrank k Γ(natTensorPow (pointDivisorSheaf p hp 1) 6, ⊤) = 6 := by
    rw [← Φ.finrank_eq, Stacks.GenusOneSectionRing.finrank_eq D le_rfl (by norm_num)]
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 6) k Γ(natTensorPow (pointDivisorSheaf p hp 1) 6, ⊤),
      ∀ i, b i = w i :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli' (by rw [Fintype.card_fin, hfr]),
      fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩
  refine ⟨b, hb, fun h5 => ?_⟩
  have hsum := b.sum_repr (mulSections (pointDivisorSheaf p hp 1) y y)
  have hring : ringElt (pointDivisorSheaf p hp 1) (mulSections (pointDivisorSheaf p hp 1) y y) =
      ∑ i, b.repr (mulSections (pointDivisorSheaf p hp 1) y y) i •
        ringElt (pointDivisorSheaf p hp 1) (w i) := by
    have h1 := congrArg (fun a => ((Φ.symm a : gradingK (pointDivisorSheaf p hp 1) k 6) :
      sectionRing (pointDivisorSheaf p hp 1))) hsum
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hΦs, hb] at h1
    exact h1.symm
  have hle : (1 : ℕ∞) ≤ D.ord (ringElt (pointDivisorSheaf p hp 1)
      (mulSections (pointDivisorSheaf p hp 1) y y)) := by
    rw [hring]
    refine D.le_ord_sum _ _
      (fun i _ => (gradingK (pointDivisorSheaf p hp 1) k 6).smul_mem _ (hmem _)) 1
      fun i _ => ?_
    by_cases hc : b.repr (mulSections (pointDivisorSheaf p hp 1) y y) i = 0
    · rw [hc, zero_smul, D.ord_zero]; exact le_top
    · rw [D.ord_smul (hmem _) hc, hords]
      fin_cases i
      all_goals first | (exfalso; exact hc h5) | exact_mod_cast (by decide : (1 : ℕ) ≤ _)
  rw [hom, hyo, add_zero] at hle
  exact absurd hle (by norm_num)

end AlgebraicGeometry.GenusOne

end
