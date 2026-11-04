module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage

/-!
# Forms of a smooth morphism do not vanish off an effective Cartier divisor

Let `f : X ⟶ S` be a smooth morphism with `S` affine and `D ⊂ X` an effective Cartier divisor.
A local section of `Ω^d_{X/S}` that vanishes on the complement of `D` vanishes.

## Main results

* `exteriorPower.projective`: an exterior power of a projective module is projective.
* `Stacks.Divisors.projective_sections_relativeDifferentialForms`: the forms of a smooth morphism
  over a pair of affine opens are a projective module.
* `Stacks.Divisors.isSMulRegular_sections_relativeDifferentialForms`: nonzerodivisors act
  injectively on them.
* `Stacks.Divisors.eq_zero_of_res_compl_support_eq_zero_of_isSMulRegular`: a section of a
  quasi-coherent module on which nonzerodivisors act injectively and which vanishes off an
  effective Cartier divisor vanishes.
* `Stacks.Divisors.eq_zero_of_res_compl_support_eq_zero`: a form of a smooth morphism vanishing
  off an effective Cartier divisor vanishes.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u v

namespace exteriorPower

/-- **An exterior power of a projective module is projective.** -/
theorem projective {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

end exteriorPower

namespace Stacks.Divisors

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]

/-- **The forms of a smooth morphism over a pair of affine opens are a projective module.** For
affine opens `W ⊆ f⁻¹V`, `Γ(Ω^d_{X/S}, W)` is a projective `Γ(X, W)`-module. -/
theorem projective_sections_relativeDifferentialForms (W : X.affineOpens) (V : S.affineOpens)
    (e : W.1 ≤ f ⁻¹ᵁ V.1) (d : ℕ) :
    Module.Projective Γ(X, W.1) Γ(Scheme.Hom.relativeDifferentialForms f (d : ℤ), W.1) := by
  have hsm : (f.appLE V.1 W.1 e).hom.Smooth := HasRingHomProperty.appLE (P := @Smooth) f
    inferInstance V W e
  let := (f.appLE V.1 W.1 e).hom.toAlgebra
  have : Algebra.Smooth Γ(S, V.1) Γ(X, W.1) := hsm
  have : Module.Projective Γ(X, W.1) (CommRingCat.KaehlerDifferential (f.appLE V.1 W.1 e)) :=
    inferInstanceAs (Module.Projective Γ(X, W.1) Ω[Γ(X, W.1)⁄Γ(S, V.1)])
  have := exteriorPower.projective (R := Γ(X, W.1))
    (M := CommRingCat.KaehlerDifferential (f.appLE V.1 W.1 e)) d
  exact Module.Projective.of_equiv
    (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso f W.2 V.2 e d).toLinearEquiv.symm

/-- **Nonzerodivisors act injectively on the forms of a smooth morphism over an affine
open.** -/
theorem isSMulRegular_sections_relativeDifferentialForms (W : X.affineOpens) (V : S.affineOpens)
    (e : W.1 ≤ f ⁻¹ᵁ V.1) (d : ℕ) (g : Γ(X, W.1)) (hg : IsRegular g) :
    IsSMulRegular Γ(Scheme.Hom.relativeDifferentialForms f (d : ℤ), W.1) g :=
  have := projective_sections_relativeDifferentialForms f W V e d
  Module.Flat.isSMulRegular_of_isRegular hg

/-- **A section of a quasi-coherent module vanishing off an effective Cartier divisor vanishes**,
as soon as every nonzerodivisor of every affine open acts injectively on the sections there. -/
theorem eq_zero_of_res_compl_support_eq_zero_of_isSMulRegular {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent]
    (hM : ∀ (W : X.affineOpens) (g : Γ(X, W.1)), IsRegular g → IsSMulRegular Γ(M, W.1) g)
    (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I) {U : X.Opens} (s : Γ(M, U))
    (hs : M.presheaf.map (homOfLE (inf_le_left : U ⊓ I.support.compl ≤ U)).op s = 0) :
    s = 0 := by
  refine (Scheme.Modules.isSheaf M).section_ext (U := op U) (t := 0) fun x hx ↦ ?_
  obtain ⟨W, hxW, hWU, g, hg, hbasic⟩ :=
    exists_affineOpen_basicOpen_eq_inf_compl_support I hI U x hx
  refine ⟨W.1, hWU, hxW, ?_⟩
  rw [map_zero]
  have hle : W.1 ⊓ X.basicOpen g ≤ U ⊓ I.support.compl := by
    rw [inf_eq_right.mpr (X.basicOpen_le g), hbasic]
    exact inf_le_inf_right _ hWU
  have hz : M.presheaf.map (homOfLE (inf_le_left : W.1 ⊓ X.basicOpen g ≤ W.1)).op
      (M.presheaf.map (homOfLE hWU).op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      show homOfLE (inf_le_left : W.1 ⊓ X.basicOpen g ≤ W.1) ≫ homOfLE hWU =
        homOfLE hle ≫ homOfLE (inf_le_left : U ⊓ I.support.compl ≤ U) from rfl,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]
  obtain ⟨k, hk⟩ := Scheme.Modules.exists_pow_smul_res_eq_zero_of_isCompact M g W.1
    W.2.isCompact le_rfl _ hz
  rw [show X.presheaf.map (homOfLE (le_refl W.1)).op g = g by simp] at hk
  exact hM W (g ^ k) (hg.pow k) (hk.trans (smul_zero _).symm)

/-- **A form of a smooth morphism vanishing off an effective Cartier divisor vanishes.** For
`f : X ⟶ S` smooth with `S` affine, `I` an effective Cartier divisor on `X` and `U` an open of
`X`, a section of `Ω^d_{X/S}` over `U` that restricts to zero on `U ∖ V(I)` is zero. -/
theorem eq_zero_of_res_compl_support_eq_zero [IsAffine S] (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (d : ℕ) {U : X.Opens}
    (s : Γ(Scheme.Hom.relativeDifferentialForms f (d : ℤ), U))
    (hs : (Scheme.Hom.relativeDifferentialForms f (d : ℤ)).presheaf.map
      (homOfLE (inf_le_left : U ⊓ I.support.compl ≤ U)).op s = 0) : s = 0 :=
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f d
  eq_zero_of_res_compl_support_eq_zero_of_isSMulRegular _
    (fun W g hg ↦ isSMulRegular_sections_relativeDifferentialForms f W
      ⟨⊤, isAffineOpen_top S⟩ (by simp) d g hg) I hI s hs

end Stacks.Divisors
