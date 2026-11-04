module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupTwistCohomology

/-!
# The global sections of `𝒪_L(iE)` on the coordinate blowup

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupTwistCohomology`, for
`0 ≤ i ≤ n - 1` every global section of `𝒪_L(iE)` is `b^♯(a)` times the canonical section, for a
unique function `a` on `X`.

A global section is determined by its restriction to `W₀ = b⁻¹(D(y₁ ⋯ y_n))`, which is a Laurent
polynomial in the `y`'s supported on every single chart. A Laurent exponent needing at most the
chart `j`, for every `j`, needs none: for `n ≥ 2` because two distinct charts are available, and
for `n = 1` because then `i = 0` and the total degree in the single `y` is nonnegative. So the
restriction is a polynomial `a`, and it is the restriction of `b^♯(a)` times the canonical
section.

## Main results

* `Stacks.DeRham.CoordinateCech.bijective_smul_canonicalSection`: **the map `a ↦ b^♯(a) · 1_{iE}`
  from the functions on `X` to the global sections of `𝒪_L(iE)` is bijective**, for `i < n`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.DeRham.CoordinateCech

open Stacks.Divisors Stacks.LaurentCoeff Stacks.PartialLaurent
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf
open Stacks.Cohomology.Basis (res res_res res_id)

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- A Laurent polynomial all of whose exponents are nonnegative is a polynomial. -/
theorem exists_polyLaurent_eq (g : ((Fin m ⊕ Fin n) →₀ ℤ) →₀ R)
    (hg : ∀ e ∈ g.support, ∀ v, 0 ≤ e v) :
    ∃ a : Γ(coordinateAmbient R m n, ⊤), polyLaurent R m n a = AddMonoidAlgebra.ofCoeff g := by
  classical
  refine ⟨Stacks.MoreMorphisms.gammaEquiv R m n
    (∑ e ∈ g.support, MvPolynomial.monomial (Finsupp.mapRange Int.toNat (by simp) e) (g e)), ?_⟩
  simp only [polyLaurent, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, map_sum, toLaurent_monomial]
  conv_rhs => rw [← AddMonoidAlgebra.ofCoeff_coeff (AddMonoidAlgebra.ofCoeff g),
    AddMonoidAlgebra.coeff_ofCoeff, ← Finsupp.sum_single g, Finsupp.sum,
    AddMonoidAlgebra.ofCoeff_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [natToInt_toNat m n (hg e he)]
  rfl

/-- **A Laurent polynomial supported on every single chart has nonnegative exponents**, for
`i < n`. -/
theorem nonneg_of_forall_mem_supported {i : ℕ} (hi : i < n) {g : ((Fin m ⊕ Fin n) →₀ ℤ) →₀ R}
    (hg : ∀ j : Fin n, g ∈ Stacks.CechFinsupp.supported (twistOk m n i) (negSet.{u} m n)
      (Set.range (ULift.up ∘ ![j]))) :
    ∀ e ∈ g.support, ∀ v, 0 ≤ e v := by
  intro e he v
  have hok := ((hg ⟨0, by omega⟩) e he).1
  rcases v with s | k
  · exact hok.1 s
  · by_contra hneg
    push Not at hneg
    have hk : ∀ j : Fin n, k = j := fun j => by
      obtain ⟨a, ha⟩ := ((hg j) e he).2
        (show (⟨k⟩ : ULift.{u} (Fin n)) ∈ negSet.{u} m n e from hneg)
      have := congrArg ULift.down ha
      simp only [Function.comp_apply, Matrix.cons_val_fin_one] at this
      exact this.symm
    -- only one chart: then `i = 0` and the single exponent is the total degree
    have hn1 : n = 1 := by
      by_contra h
      have h2 : 1 < n := by omega
      exact absurd ((hk ⟨0, by omega⟩).symm.trans (hk ⟨1, h2⟩)) (by simp [Fin.ext_iff])
    subst hn1
    have hi0 : i = 0 := by omega
    have hdeg := hok.2
    simp only [yDegree, hi0, Fin.sum_univ_one, CharP.cast_eq_zero, neg_zero] at hdeg
    rw [Subsingleton.elim k 0] at hneg
    omega

/-- `b^♯(a)` times the canonical section of `𝒪_L(iE)`, as a global section. -/
abbrev globalTwist (i : ℕ) (a : Γ(coordinateAmbient R m n, ⊤)) :
    (twistSheaf R m n i).val.obj (op ⊤) :=
  Stacks.SheafOfModules.smulSectionMap (𝒪 := (coordinateBlowup R m n).presheaf)
    (h𝒪 := (structureSheafRing (coordinateBlowup R m n).toRingedSpace).property)
    (L := invertibleSheaf' (coordinateExceptional R m n ^ i))
    ((canonicalSection' (coordinateExceptional R m n ^ i)).val (op ⊤))
    ((coordinateBlowupToAmbient R m n).appTop.hom a)

/-- Restricting a global section of `𝒪_L(iE)` to `W₀`. -/
abbrev resTop (i : ℕ) : (twistSheaf R m n i).val.obj (op ⊤) →
    (twistSheaf R m n i).val.obj (op (punctured R m n)) :=
  ((twistSheaf R m n i).val.map (homOfLE (le_top : punctured R m n ≤ ⊤)).op).hom

/-- **`b^♯(a) · 1_{iE}`, restricted to `W₀` and read on `D(y₁ ⋯ y_n)`, is `a`.** -/
theorem puncturedFrac_resTop_globalTwist (hn : 0 < n) (i : ℕ) (a : Γ(coordinateAmbient R m n, ⊤)) :
    puncturedFrac R m n hn i (resTop R m n i (globalTwist R m n i a)) = toFrac R m n a := by
  have h1 : resTop R m n i (globalTwist R m n i a) =
      Stacks.SheafOfModules.smulSectionMap (𝒪 := (coordinateBlowup R m n).presheaf)
        (h𝒪 := (structureSheafRing (coordinateBlowup R m n).toRingedSpace).property)
        (L := invertibleSheaf' (coordinateExceptional R m n ^ i))
        ((canonicalSection' (coordinateExceptional R m n ^ i)).val (op (punctured R m n)))
        (((coordinateBlowupToAmbient R m n).appLE ⊤ (punctured R m n) le_top).hom a) := by
    refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
    rw [PresheafOfModules.sections_property]
    congr 1
  rw [puncturedFrac, h1, ← puncturedEquiv_appLE R m n hn]
  congr 1
  refine (Stacks.SheafOfModules.evalSection_smul_left _ _ _ _ _ _ _).trans ?_
  have he : @id Γ(coordinateBlowup R m n, punctured R m n) (Stacks.SheafOfModules.dualEval
      ((canonicalSection' (coordinateExceptional R m n ^ i)).val (op (punctured R m n)))
      (puncturedBasis R m n hn i).e) = 1 := idealSheafSection_puncturedBasis_e R m n hn i
  exact (congrArg (fun t : Γ(coordinateBlowup R m n, punctured R m n) =>
    ((coordinateBlowupToAmbient R m n).appLE ⊤ (punctured R m n) le_top).hom a * t) he).trans
      (mul_one _)

/-- The one-chart tuple `(j)`. -/
abbrev single (j : Fin n) : Fin (0 + 1) → Fin n := ![j]

/-- The one-chart intersection opens cover the blowup. -/
theorem iSup_tupleOpen_single (hn : 0 < n) :
    (⊤ : (coordinateBlowup R m n).Opens) ≤ ⨆ j : Fin n, (tupleOpen R m n (single n j)).1 := by
  rw [← iSup_chart R m n hn]
  refine iSup_mono fun j => ?_
  show chart R m n j ≤ (coordinateBlowup R m n).basicOpen (tupleRatio R m n (single n j))
  rw [← iInf_chart]
  exact le_iInf fun k => by rw [Fin.fin_one_eq_zero k]; rfl

/-- **A global section of `𝒪_L(iE)` is determined by its restriction to `W₀`.** -/
theorem res_top_injective (hn : 0 < n) (i : ℕ) :
    Function.Injective (res (abSections (divisorSheaf (coordinateExceptional R m n ^ i)))
      (le_top : punctured R m n ≤ ⊤)) := by
  intro μ μ' h
  refine (abSheaf (divisorSheaf (coordinateExceptional R m n ^ i))).eq_of_locally_eq'
    (fun j : Fin n => (tupleOpen R m n (single n j)).1) ⊤
    (fun j : Fin n => homOfLE le_top) (iSup_tupleOpen_single R m n hn) μ μ' fun j => ?_
  refine res_tuple_injective R m n hn i (single n j) ?_
  show res _ _ (res _ _ μ) = res _ _ (res _ _ μ')
  rw [Stacks.Cohomology.Basis.res_res, Stacks.Cohomology.Basis.res_res]
  exact h

/-- The Laurent coefficients of the restriction to `W₀` of a global section `μ` of `𝒪_L(iE)`
are those of `puncturedValue` applied to `resTop μ`. -/
theorem puncturedValueAb_resTop (hn : 0 < n) (i : ℕ)
    (μ : ToType ((abSections (divisorSheaf (coordinateExceptional R m n ^ i))).obj (op ⊤))) :
    puncturedValueAb R m n hn i (res (abSections (divisorSheaf (coordinateExceptional R m n ^ i)))
      (le_top : punctured R m n ≤ ⊤) μ) = (puncturedValue R m n hn i (resTop R m n i μ)).coeff :=
  rfl

/-- `b^♯(a) · 1_{iE}` restricted to `W₀`, as a Laurent polynomial, is `a`. -/
theorem puncturedValueAb_globalTwist (hn : 0 < n) (i : ℕ) (a : Γ(coordinateAmbient R m n, ⊤)) :
    puncturedValueAb R m n hn i (res (abSections (divisorSheaf
      (coordinateExceptional R m n ^ i))) (le_top : punctured R m n ≤ ⊤) (globalTwist R m n i a)) =
        (polyLaurent R m n a).coeff :=
  (puncturedValueAb_resTop R m n hn i (globalTwist R m n i a)).trans
    ((congrArg (fun t => (laurent R m n t).coeff)
      (puncturedFrac_resTop_globalTwist R m n hn i a)).trans
        (congrArg AddMonoidAlgebra.coeff (laurent_toFrac R m n a)))

/-- The restriction of a global section to `W₀`, as a Laurent polynomial, is supported on every
single chart. -/
theorem puncturedValueAb_res_top_mem (hn : 0 < n) (i : ℕ) (j : Fin n)
    (μ : ToType ((abSections (divisorSheaf (coordinateExceptional R m n ^ i))).obj (op ⊤))) :
    puncturedValueAb R m n hn i (res (abSections (divisorSheaf (coordinateExceptional R m n ^ i)))
      (le_top : punctured R m n ≤ ⊤) μ) ∈
        Stacks.CechFinsupp.supported (twistOk m n i) (negSet.{u} m n)
          (Set.range (ULift.up ∘ single n j)) := by
  have h := puncturedValueAb_tuple_mem R m n hn i (single n j)
    (res (abSections (divisorSheaf (coordinateExceptional R m n ^ i)))
      (le_top : (tupleOpen R m n (single n j)).1 ≤ ⊤) μ)
  rw [Stacks.Cohomology.Basis.res_res] at h
  exact h

/-- **The map `a ↦ b^♯(a) · 1_{iE}` from the functions on `X` to the global sections of
`𝒪_L(iE)` is bijective**, for `0 ≤ i ≤ n - 1`. -/
theorem bijective_globalTwist (hn : 0 < n) (i : ℕ) (hi : i < n) :
    Function.Bijective (globalTwist R m n i) := by
  refine ⟨fun a a' haa' =>
      polyLaurent_injective R m n (AddMonoidAlgebra.coeffAddEquiv.injective ?_),
    fun μ => ?_⟩
  · show (polyLaurent R m n a).coeff = (polyLaurent R m n a').coeff
    rw [← puncturedValueAb_globalTwist R m n hn i, ← puncturedValueAb_globalTwist R m n hn i, haa']
  · obtain ⟨a, ha⟩ := exists_polyLaurent_eq R m n _ (nonneg_of_forall_mem_supported R m n hi
      (fun j => puncturedValueAb_res_top_mem R m n hn i j μ))
    refine ⟨a, res_top_injective R m n hn i (puncturedValueAb_injective R m n hn i ?_)⟩
    rw [puncturedValueAb_globalTwist, ha]

end Stacks.DeRham.CoordinateCech

end
