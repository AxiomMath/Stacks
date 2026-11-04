module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule

/-!
# The product of a power of a sheaf of ideals with the whole structure sheaf

Let `(C, J)` be a site, `O` a sheaf of commutative rings on it and `I ⊆ O` a sheaf of ideals. The
products `I · N` and `Iⁿ · N` of `I` and its powers with a submodule `N` of a sheaf of `O`-modules
are `Stacks.Sites.idealSmul` and `Stacks.Sites.idealPowSmul`. This file computes their value at the
largest submodule of the free rank-one module: the product with the whole of `O` is the sheaf of
ideals itself.

## Main results

* `Stacks.Sites.idealSmul_top`: **`I · O = I`** — the product of a sheaf of ideals with the whole
  free rank-one sheaf of modules is the sheaf of ideals itself.
* `Stacks.Sites.idealPowSmul_top`: **`Iⁿ · O = Iⁿ`**, the same at a power.

## Implementation notes

The sheaf-of-modules API reads the ring of sections as an object of `RingCat`, so the commutative
ring structure it carries is reinstalled as a local instance.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u₁ v₁ u

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {O : Sheaf J CommRingCat.{u}}

/-- The sections of the structure sheaf over an object, read as a sheaf of not necessarily
commutative rings, form a commutative ring. -/
noncomputable local instance commRing_ringSheaf_obj_obj (Y : Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y) :=
  inferInstanceAs (CommRing (O.obj.obj Y))

/-- **`I · 𝒪 = I`.**  The product of a sheaf of ideals with the whole free rank-one sheaf of
modules is the sheaf of ideals itself. -/
theorem idealSmul_top (I : IdealSubsheaf O) : idealSmul I (⊤ : IdealSubsheaf O) = I := by
  refine le_antisymm
    (Stacks.SheafOfModules.sheafifySubmodule_le
      (presheafIdealSmul_le I fun Y a ha m _ => ?_))
    (_root_.SheafOfModules.Submodule.le_iff.2 fun Y a ha => ?_)
  · show a * (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from m) ∈
      sectionIdeal I Y
    rw [mul_comm]
    exact Ideal.mul_mem_left _ _ ha
  · convert smul_mem_idealSmul I ha (Stacks.SheafOfModules.mem_top_obj
      (M := _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y)) using 1
    exact (mul_one (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Y from a)).symm

/-- **`Iⁿ · 𝒪 = Iⁿ`.**  The product of a power of a sheaf of ideals with the whole free rank-one
sheaf of modules is that power. -/
@[simp]
theorem idealPowSmul_top (I : IdealSubsheaf O) (n : ℕ) :
    idealPowSmul I n (⊤ : IdealSubsheaf O) = idealPow I n :=
  idealSmul_top (idealPow I n)

end Stacks.Sites

end
