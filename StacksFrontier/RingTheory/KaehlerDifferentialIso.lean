module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The map on Kähler differentials induced by a square of ring homomorphisms

Let `ρ : R₁ →+* R₂` and `σ : S₁ →+* S₂` be ring homomorphisms forming a commutative square with
two algebra structures `R₁ → S₁` and `R₂ → S₂`. **This file constructs the induced
`σ`-semilinear map `Ω[S₁/R₁] → Ω[S₂/R₂]` and proves that it, and indeed any `σ`-semilinear map
carrying `d s` to `d (σ s)`, is bijective as soon as `ρ` and `σ` are.**

The square of ring homomorphisms is not a tower, so `KaehlerDifferential.map` does not apply
directly; it is applied to the algebra structures that `ρ` and `σ` themselves define.

## Main definitions

* `Stacks.KaehlerDifferentialSquare.map`: the induced `σ`-semilinear map
  `Ω[S₁/R₁] → Ω[S₂/R₂]`.

## Main results

* `Stacks.KaehlerDifferentialSquare.map_D`: the induced map carries `d s` to `d (σ s)`. Since
  the universal differentials generate, this pins the map down.
* `Stacks.KaehlerDifferentialSquare.bijective_of_map_D`: an additive map semilinear over `σ`
  and carrying `d s` to `d (σ s)` is bijective as soon as `ρ` and `σ` are. This is the algebraic
  core of the statement that the module of relative differentials is unchanged by an isomorphism
  of the square.

## References

* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
-/

@[expose] public section

universe u

noncomputable section

namespace Stacks.KaehlerDifferentialSquare

/-- Induction principle: a predicate on `Ω[S/R]` holding for all `d s` and stable under zero,
addition and scalar multiplication holds everywhere. -/
private theorem induction_on_D {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {P : Ω[S⁄R] → Prop} (ω : Ω[S⁄R]) (hD : ∀ s, P (KaehlerDifferential.D R S s)) (h0 : P 0)
    (hadd : ∀ x z, P x → P z → P (x + z)) (hsmul : ∀ (s : S) x, P x → P (s • x)) : P ω := by
  have mem : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hD s
  | zero => exact h0
  | add x z _ _ ihx ihz => exact hadd x z ihx ihz
  | smul s x _ ih => exact hsmul s x ih

variable {R₁ S₁ R₂ S₂ : Type u} [CommRing R₁] [CommRing S₁] [CommRing R₂] [CommRing S₂]
  [Algebra R₁ S₁] [Algebra R₂ S₂] {ρ : R₁ →+* R₂} {σ : S₁ →+* S₂}
  (hsq : ∀ r : R₁, σ (algebraMap R₁ S₁ r) = algebraMap R₂ S₂ (ρ r))

include hsq

/-- **The map on Kähler differentials induced by a commutative square of ring
homomorphisms**, as a map semilinear over `σ`. -/
@[ega "0 20.5.2"]
def map : Ω[S₁⁄R₁] →ₛₗ[σ] Ω[S₂⁄R₂] := by
  letI : Algebra R₁ R₂ := ρ.toAlgebra
  letI : Algebra S₁ S₂ := σ.toAlgebra
  letI : Algebra R₁ S₂ := ((algebraMap R₂ S₂).comp ρ).toAlgebra
  have : IsScalarTower R₁ S₁ S₂ := IsScalarTower.of_algebraMap_eq fun r => (hsq r).symm
  have : IsScalarTower R₁ R₂ S₂ := IsScalarTower.of_algebraMap_eq' rfl
  exact
    { toFun := KaehlerDifferential.map R₁ R₂ S₁ S₂
      map_add' := map_add _
      map_smul' := fun s x => by
        refine (map_smul (KaehlerDifferential.map R₁ R₂ S₁ S₂) s x).trans ?_
        exact (algebraMap_smul (R := S₁) S₂ s _).symm }

/-- **The induced map carries universal differentials to universal differentials.** -/
@[simp]
theorem map_D (s : S₁) :
    map hsq (KaehlerDifferential.D R₁ S₁ s) = KaehlerDifferential.D R₂ S₂ (σ s) := by
  let : Algebra R₁ R₂ := ρ.toAlgebra
  let : Algebra S₁ S₂ := σ.toAlgebra
  let : Algebra R₁ S₂ := ((algebraMap R₂ S₂).comp ρ).toAlgebra
  have : IsScalarTower R₁ S₁ S₂ := IsScalarTower.of_algebraMap_eq fun r => (hsq r).symm
  have : IsScalarTower R₁ R₂ S₂ := IsScalarTower.of_algebraMap_eq' rfl
  exact KaehlerDifferential.map_D R₁ R₂ S₁ S₂ s

variable (hρ : Function.Bijective ρ) (hσ : Function.Bijective σ)

include hρ hσ

/-- The square formed by the inverses of two bijective sides of a commutative square of ring
homomorphisms again commutes. -/
theorem inverse_square (r : R₂) :
    ((RingEquiv.ofBijective σ hσ).symm : S₂ →+* S₁) (algebraMap R₂ S₂ r) =
      algebraMap R₁ S₁ (((RingEquiv.ofBijective ρ hρ).symm : R₂ →+* R₁) r) := by
  refine (RingEquiv.ofBijective σ hσ).injective ?_
  refine ((RingEquiv.ofBijective σ hσ).apply_symm_apply _).trans (Eq.symm ?_)
  refine (hsq _).trans ?_
  exact congrArg (algebraMap R₂ S₂) ((RingEquiv.ofBijective ρ hρ).apply_symm_apply r)

variable {T : Ω[S₁⁄R₁] → Ω[S₂⁄R₂]} (hadd : ∀ x z : Ω[S₁⁄R₁], T (x + z) = T x + T z)
  (hsmul : ∀ (s : S₁) (ω : Ω[S₁⁄R₁]), T (s • ω) = σ s • T ω)
  (hT : ∀ s : S₁, T (KaehlerDifferential.D R₁ S₁ s) = KaehlerDifferential.D R₂ S₂ (σ s))

include hadd hsmul hT

/-- The map induced by the inverse square undoes `T` on `Ω[S₁/R₁]`. -/
theorem map_inverse_square_comp (ω : Ω[S₁⁄R₁]) :
    map (inverse_square hsq hρ hσ) (T ω) = ω := by
  have hzero : T 0 = 0 := (AddMonoidHom.mk' T hadd).map_zero
  induction ω using induction_on_D with
  | hD s =>
      rw [hT, map_D]
      exact congrArg (KaehlerDifferential.D R₁ S₁)
        ((RingEquiv.ofBijective σ hσ).symm_apply_apply s)
  | h0 => rw [hzero, map_zero]
  | hadd x z ihx ihz => rw [hadd, map_add, ihx, ihz]
  | hsmul s x ih =>
      rw [hsmul, map_smulₛₗ, ih]
      exact congrArg (· • x) ((RingEquiv.ofBijective σ hσ).symm_apply_apply s)

/-- The map induced by the inverse square is undone by `T` on `Ω[S₂/R₂]`. -/
theorem comp_map_inverse_square (ω : Ω[S₂⁄R₂]) :
    T (map (inverse_square hsq hρ hσ) ω) = ω := by
  have hzero : T 0 = 0 := (AddMonoidHom.mk' T hadd).map_zero
  induction ω using induction_on_D with
  | hD s =>
      rw [map_D, hT]
      exact congrArg (KaehlerDifferential.D R₂ S₂)
        ((RingEquiv.ofBijective σ hσ).apply_symm_apply s)
  | h0 => rw [map_zero, hzero]
  | hadd x z ihx ihz => rw [map_add, hadd, ihx, ihz]
  | hsmul s x ih =>
      rw [map_smulₛₗ, hsmul, ih]
      exact congrArg (· • x) ((RingEquiv.ofBijective σ hσ).apply_symm_apply s)

/-- **A map on Kähler differentials along a square of ring isomorphisms is bijective.** Any
additive map `Ω[S₁/R₁] → Ω[S₂/R₂]` semilinear over `σ` and carrying `d s` to `d (σ s)` is
bijective as soon as both sides `ρ` and `σ` of the square are. -/
theorem bijective_of_map_D : Function.Bijective T :=
  Function.bijective_iff_has_inverse.2
    ⟨map (inverse_square hsq hρ hσ), map_inverse_square_comp hsq hρ hσ hadd hsmul hT,
      comp_map_inverse_square hsq hρ hσ hadd hsmul hT⟩

end Stacks.KaehlerDifferentialSquare

end

end
