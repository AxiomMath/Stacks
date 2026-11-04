module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule

/-!
# The product of two sheaves of ideals, and the powers of that product

Let `O` be a sheaf of commutative rings on a site and let `I` and `K` be sheaves of ideals of
`O`. Their product is `Stacks.Sites.idealSmul I K`, the product of `I` with `K` read as a
submodule of the free rank-one sheaf of `O`-modules. The product lies in both factors, the `n`-th
powers multiply into the `n`-th power of the product, and the same holds after multiplying a
submodule of a sheaf of modules.

## Main results

* `Stacks.Sites.idealSmul_le_left`: `I · K ⊆ I`.
* `Stacks.Sites.sectionIdeal_mul_le_sectionIdeal_idealSmul`: on sections over an object, the
  product of the two ideals of sections lies in the ideal of sections of the product.
* `Stacks.Sites.idealSmul_idealPow_idealPow_le_idealPow_idealSmul`: `Kⁿ · Iⁿ ⊆ (I · K)ⁿ`.
* `Stacks.Sites.ringSectionIdeal_idealPow_smul_le_idealSmul`: on sections over an object, the
  ideal of sections of `Kⁿ` times the ideal of sections of `Iⁿ` lies in that of `(I · K)ⁿ`.
* `Stacks.Sites.idealPowSmul_idealPowSmul_le_idealPowSmul_idealSmul`:
  `Kⁿ · (Iⁿ · N) ⊆ (I · K)ⁿ · N` for a submodule `N` of a sheaf of modules.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v₁ u₁ u

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}

/-! ### The product lies in both factors -/

/-- **The product of two sheaves of ideals lies in its left factor.** -/
theorem idealSmul_le_left (I K : IdealSubsheaf O) : idealSmul I K ≤ I := by
  refine Stacks.SheafOfModules.sheafifySubmodule_le (presheafIdealSmul_le I ?_)
  intro X a ha m _
  have key : ∀ c d : O.obj.obj X, c ∈ sectionIdeal I X → c * d ∈ sectionIdeal I X :=
    fun _ d hc ↦ (sectionIdeal I X).mul_mem_right d hc
  exact key a m ha

/-- **On sections, the product of the two ideals of sections lies in the ideal of sections of the
product.** -/
theorem sectionIdeal_mul_le_sectionIdeal_idealSmul (I K : IdealSubsheaf O) (X : Cᵒᵖ) :
    sectionIdeal I X * sectionIdeal K X ≤ sectionIdeal (idealSmul I K) X :=
  Ideal.mul_le.2 fun _ ha _ hb => smul_mem_idealSmul I ha hb

/-! ### Powers of the product -/

/-- **`Kⁿ · Iⁿ ⊆ (I · K)ⁿ`** for sheaves of ideals `I` and `K`. -/
theorem idealSmul_idealPow_idealPow_le_idealPow_idealSmul (I K : IdealSubsheaf O) (n : ℕ) :
    idealSmul (idealPow K n) (idealPow I n) ≤ idealPow (idealSmul I K) n := by
  refine Stacks.SheafOfModules.sheafifySubmodule_le (presheafIdealSmul_le (idealPow K n) ?_)
  intro X a ha z hz
  obtain ⟨S₁, hS₁, ha⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule ha
  obtain ⟨S₂, hS₂, hz⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule hz
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem
    (J.intersection_covering hS₁ hS₂) fun Y f hf => ?_
  have h1 : (ConcreteCategory.hom
        ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).val.map f.op)) (a • z)
      = (ConcreteCategory.hom (O.obj.map f.op)) a * (ConcreteCategory.hom (O.obj.map f.op)) z :=
    map_mul (ConcreteCategory.hom (O.obj.map f.op)) a z
  have h2 : sectionIdeal I (op Y) ^ n * sectionIdeal K (op Y) ^ n
      = sectionIdeal K (op Y) ^ n * sectionIdeal I (op Y) ^ n := mul_comm _ _
  have h3 : sectionIdeal I (op Y) ^ n * sectionIdeal K (op Y) ^ n
      ≤ sectionIdeal (idealSmul I K) (op Y) ^ n := by
    rw [← mul_pow]
    exact Ideal.pow_right_mono (sectionIdeal_mul_le_sectionIdeal_idealSmul I K (op Y)) n
  rw [h1]
  exact h3 (h2.ge (Ideal.mul_mem_mul (ha f hf.1) (hz f hf.2)))

variable {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- The ideal of sections of `Kⁿ` times the ideal of sections of `Iⁿ` lies in the ideal of
sections of `(I · K)ⁿ`. -/
theorem ringSectionIdeal_idealPow_smul_le_idealSmul (I K : IdealSubsheaf O) (n : ℕ) (X : Cᵒᵖ) :
    ringSectionIdeal (idealPow K n) X • ringSectionIdeal (idealPow I n) X ≤
      ringSectionIdeal (idealPow (idealSmul I K) n) X :=
  Submodule.smul_le.2 fun _ ha _ hz =>
    _root_.SheafOfModules.Submodule.le_iff.1
      (idealSmul_idealPow_idealPow_le_idealPow_idealSmul I K n) X
      (smul_mem_idealSmul (idealPow K n) ha hz)

/-- **`Kⁿ · (Iⁿ · N) ⊆ (I · K)ⁿ · N`** for sheaves of ideals `I` and `K` and a submodule `N` of
a sheaf of modules. -/
theorem idealPowSmul_idealPowSmul_le_idealPowSmul_idealSmul (I K : IdealSubsheaf O) (n : ℕ)
    (N : M.Submodule) :
    idealPowSmul K n (idealPowSmul I n N) ≤ idealPowSmul (idealSmul I K) n N := by
  refine (idealSmul_sheafifySubmodule_le (idealPow K n)
    (presheafIdealSmul (idealPow I n) N.toSubmodule)).trans
    (Stacks.SheafOfModules.sheafifySubmodule_le fun X => ?_)
  rw [presheafIdealSmul_obj, presheafIdealSmul_obj, ← Submodule.smul_assoc]
  exact (Submodule.smul_mono_left (ringSectionIdeal_idealPow_smul_le_idealSmul I K n X)).trans
    ((presheafIdealSmul_obj (idealPow (idealSmul I K) n) N.toSubmodule X).ge.trans
      (Stacks.SheafOfModules.le_sheafifySubmodule _ X))

end Stacks.Sites

end
