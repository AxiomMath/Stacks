module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointDivisorData
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroSections

/-!
# The sections of the powers of `O(0)` on an elliptic curve over a field

Let `(E, f, 0)` be a pointed family over a field `k`, proper and smooth of relative dimension
one, with `dim_k H⁰(E, 𝒪_E) = 1` and genus one, and let `O(0)` be the invertible sheaf of its
zero divisor, with canonical section `s`. For `n ≥ 1`:

* the higher cohomology of `O(0)^{⊗ n}` vanishes, and `dim_k H⁰(E, O(0)^{⊗ n}) = n`;
* if `x ∈ Γ(O(0)^{⊗ 2})` and `y ∈ Γ(O(0)^{⊗ 3})` are not multiples of `s`, then the six
  Weierstrass monomials `s⁶, s⁴x, s³y, s²x², sxy, x³` are a basis of `Γ(O(0)^{⊗ 6})`, and `x³`
  has a nonzero coefficient in `y²`.

The `k`-structure on sections is `Stacks.Cech.sectionsModule`, through the structure morphism.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.subsingleton_cohomologyOverField_zeroSheaf`
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.finrank_sections_zeroSheaf`
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.linearIndependent_weierstrassMonomials`
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.span_weierstrassMonomials`
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.coeff_ySq_ne_zero`

## Implementation notes

Over a field the zero divisor is the reduced point `0(Spec k)`, so `O(0)` is the sheaf `𝒪_E(p)`
of `AlgebraicGeometry.GenusOne.pointDivisorSheaf` at `p = 0`, and the statements are those of
`AlgebraicGeometry.GenusOne.finrank_cohomologyOverField_zero_pointDivisor`,
`AlgebraicGeometry.GenusOne.isZero_cohomologyOverField_pointDivisor` and
`AlgebraicGeometry.GenusOne.exists_basis_weierstrassMonomials`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection
  globalSectionsModule)

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

namespace AlgebraicGeometry

/-- **The two `k`-structures on global sections agree**: the one through the structure morphism
`f : X ⟶ Spec k` used by Čech cohomology, and the one of `X` as a scheme over `k`. -/
theorem _root_.Stacks.Cech.sectionsModule_top_eq_globalSectionsModule {k : Type u} [Field k]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : X.Modules) :
    Stacks.Cech.sectionsModule f M ⊤ = @globalSectionsModule k _ X ⟨f⟩ M := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have h1 : toSpecΓ (CommRingCat.of k) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv :=
    rfl
  have h2 : (Stacks.Cech.baseRingHom f ⊤).hom =
      Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X := by
    rw [Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom, h1]
    simp
    rfl
  unfold Stacks.Cech.sectionsModule globalSectionsModule
  rw [h2]

end AlgebraicGeometry

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

variable {k : Type u} [Field k] (F : PointedFamily (Spec (.of k))) [IsProper F.map]
  [SmoothOfRelativeDimension 1 F.map]

omit [SmoothOfRelativeDimension 1 F.map] in
/-- Over a field the zero divisor is the reduced point of the zero section. -/
theorem zeroDivisor_eq_pointDivisor :
    F.zeroDivisor = Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point F.zero}, GenusOne.isClosed_point F.map F.zero F.zero_map⟩ :
        Closeds F.total) ^ 1 := by
  rw [pow_one]
  exact F.zeroDivisor_eq_vanishingIdeal _

variable (h0 : Module.finrank k (structureSheafCohomology F.map 0) = 1) (h1 : genus F.map = 1)

include h0 h1 in
/-- **The higher cohomology of `O(0)^{⊗ n}` vanishes** for `n ≥ 1`. -/
theorem subsingleton_cohomologyOverField_zeroSheaf {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : 0 < i) :
    Subsingleton (cohomologyOverField k F.map (natTensorPow F.zeroSheaf n) i) := by
  let : F.total.Over (Spec (.of k)) := ⟨F.map⟩
  have : IsProper (F.total ↘ Spec (.of k)) := ‹IsProper F.map›
  have : SmoothOfRelativeDimension 1 (F.total ↘ Spec (.of k)) := ‹_›
  have := GenusOne.isEffectiveCartierDivisor_pow F.map h0 F.zero F.zero_map 1
  rw [zeroSheaf, F.zeroDivisor_eq_pointDivisor]
  exact ModuleCat.isZero_iff_subsingleton.mp
    (GenusOne.isZero_cohomologyOverField_pointDivisor h0 h1 F.zero F.zero_map 1 one_pos hn hi)

include h0 h1 in
/-- **`dim_k Γ(E, O(0)^{⊗ n}) = n`** for `n ≥ 1`. -/
theorem finrank_sections_zeroSheaf {n : ℕ} (hn : 1 ≤ n) :
    letI := Stacks.Cech.sectionsModule F.map (natTensorPow F.zeroSheaf n) ⊤
    Module.finrank k Γ(natTensorPow F.zeroSheaf n, ⊤) = n := by
  rw [Stacks.Cech.sectionsModule_top_eq_globalSectionsModule, zeroSheaf,
    F.zeroDivisor_eq_pointDivisor]
  let : F.total.Over (Spec (.of k)) := ⟨F.map⟩
  have : IsProper (F.total ↘ Spec (.of k)) := ‹IsProper F.map›
  have : SmoothOfRelativeDimension 1 (F.total ↘ Spec (.of k)) := ‹_›
  have := GenusOne.isEffectiveCartierDivisor_pow F.map h0 F.zero F.zero_map 1
  let := globalSectionsModule k F.total
    (natTensorPow (GenusOne.pointDivisorSheaf F.zero F.zero_map 1) n)
  have h := (GenusOne.gradingKEquivSections (GenusOne.pointDivisorSheaf F.zero F.zero_map 1) k
    n).finrank_eq.symm.trans ((GenusOne.finrank_gradingK _ k n).trans
      (GenusOne.finrank_cohomologyOverField_zero_pointDivisor h0 h1 F.zero F.zero_map 1 one_pos hn))
  rw [one_mul] at h
  exact h

include h0 h1 in
/-- **The Weierstrass monomials are a basis of `Γ(O(D)^{⊗ 6})`** for a divisor `D` equal to the
zero divisor `0(Spec k)`, with `x³` occurring in `y²`, read through the `k`-structure of the
structure morphism. -/
theorem weierstrassMonomials_basis_of_eq (D : F.total.IdealSheafData)
    (hD : D = Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point F.zero}, GenusOne.isClosed_point F.map F.zero F.zero_map⟩ :
        Closeds F.total) ^ 1)
    (x : Γ(natTensorPow (invertibleSheaf' D) 2, ⊤))
    (hx : x ∉ Set.range (mulSections (invertibleSheaf' D) (m := 1)
      (twistOneSection (invertibleSheaf' D) ((canonicalSection' D).val (op ⊤)))))
    (y : Γ(natTensorPow (invertibleSheaf' D) 3, ⊤))
    (hy : y ∉ Set.range (mulSections (invertibleSheaf' D) (m := 2)
      (twistOneSection (invertibleSheaf' D) ((canonicalSection' D).val (op ⊤))))) :
    letI := Stacks.Cech.sectionsModule F.map (natTensorPow (invertibleSheaf' D) 6) ⊤
    LinearIndependent k (weierstrassMonomials (invertibleSheaf' D)
        (twistOneSection (invertibleSheaf' D) ((canonicalSection' D).val (op ⊤))) x y) ∧
      Submodule.span k (Set.range (weierstrassMonomials (invertibleSheaf' D)
        (twistOneSection (invertibleSheaf' D) ((canonicalSection' D).val (op ⊤))) x y)) = ⊤ ∧
      ∀ c : Fin 6 → k, ySq (invertibleSheaf' D) y = ∑ i, c i • weierstrassMonomials
        (invertibleSheaf' D) (twistOneSection (invertibleSheaf' D)
          ((canonicalSection' D).val (op ⊤))) x y i → c 5 ≠ 0 := by
  subst hD
  rw [Stacks.Cech.sectionsModule_top_eq_globalSectionsModule]
  let : F.total.Over (Spec (.of k)) := ⟨F.map⟩
  have : IsProper (F.total ↘ Spec (.of k)) := ‹IsProper F.map›
  have : SmoothOfRelativeDimension 1 (F.total ↘ Spec (.of k)) := ‹_›
  have := GenusOne.isEffectiveCartierDivisor_pow F.map h0 F.zero F.zero_map 1
  have hσ := GenusOne.globalSection_pointSection
    (GenusOne.isClosed_point (F.total ↘ Spec (.of k)) F.zero F.zero_map) 1
  obtain ⟨b, hb, h5⟩ := GenusOne.exists_basis_weierstrassMonomials h0 h1 F.zero F.zero_map x
    (fun t ht => hx ⟨t, by rw [hσ] at ht; exact ht⟩) y
    (fun t ht => hy ⟨t, by rw [hσ] at ht; exact ht⟩)
  rw [hσ] at hb
  let := globalSectionsModule k F.total
    (natTensorPow (GenusOne.pointDivisorSheaf F.zero F.zero_map 1) 6)
  have hb' : (b : Fin 6 → _) = weierstrassMonomials (invertibleSheaf'
      (Scheme.IdealSheafData.vanishingIdeal (⟨{GenusOne.point F.zero},
        GenusOne.isClosed_point F.map F.zero F.zero_map⟩ : Closeds F.total) ^ 1))
      (twistOneSection _ ((canonicalSection' _).val (op ⊤))) x y := funext hb
  refine ⟨?_, ?_, fun c hc hc5 => h5 ?_⟩
  · rw [← hb']
    exact b.linearIndependent
  · rw [← hb']
    exact b.span_eq
  · have e : mulSections (GenusOne.pointDivisorSheaf F.zero F.zero_map 1) y y =
        ∑ i, c i • b i := by
      rw [hb']
      exact hc
    rw [e, b.repr_sum_self]
    exact hc5

variable {F} {x : Γ(natTensorPow F.zeroSheaf 2, ⊤)}
  (hx : x ∉ Set.range (mulSections F.zeroSheaf (m := 1) F.zeroSection))
  {y : Γ(natTensorPow F.zeroSheaf 3, ⊤)}
  (hy : y ∉ Set.range (mulSections F.zeroSheaf (m := 2) F.zeroSection))

include h0 h1 hx hy in
/-- **The Weierstrass monomials `s⁶, s⁴x, s³y, s²x², sxy, x³` are linearly independent** in
`Γ(E, O(0)^{⊗ 6})`, for `x, y` of degrees two and three not multiples of `s`. -/
theorem linearIndependent_weierstrassMonomials :
    letI := Stacks.Cech.sectionsModule F.map (natTensorPow F.zeroSheaf 6) ⊤
    LinearIndependent k (weierstrassMonomials F.zeroSheaf F.zeroSection x y) :=
  (F.weierstrassMonomials_basis_of_eq h0 h1 F.zeroDivisor F.zeroDivisor_eq_pointDivisor x hx y
    hy).1

include h0 h1 hx hy in
/-- **The Weierstrass monomials span `Γ(E, O(0)^{⊗ 6})`**, for `x, y` of degrees two and three
not multiples of `s`. -/
theorem span_weierstrassMonomials :
    letI := Stacks.Cech.sectionsModule F.map (natTensorPow F.zeroSheaf 6) ⊤
    Submodule.span k (Set.range (weierstrassMonomials F.zeroSheaf F.zeroSection x y)) = ⊤ :=
  (F.weierstrassMonomials_basis_of_eq h0 h1 F.zeroDivisor F.zeroDivisor_eq_pointDivisor x hx y
    hy).2.1

include h0 h1 hx hy in
/-- **`x³` occurs in `y²`**: in any expression of `y²` in the Weierstrass monomials, the
coefficient of `x³` is nonzero. -/
theorem coeff_ySq_ne_zero :
    letI := Stacks.Cech.sectionsModule F.map (natTensorPow F.zeroSheaf 6) ⊤
    ∀ c : Fin 6 → k, ySq F.zeroSheaf y =
      ∑ i, c i • weierstrassMonomials F.zeroSheaf F.zeroSection x y i → c 5 ≠ 0 :=
  (F.weierstrassMonomials_basis_of_eq h0 h1 F.zeroDivisor F.zeroDivisor_eq_pointDivisor x hx y
    hy).2.2

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
