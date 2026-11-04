module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal

/-!
# The inclusion of a submodule of the unit module along a closed immersion is a monomorphism

`AlgebraicGeometry.Space.submoduleιOfEssImage` is the inclusion into the unit module of a
submodule of the unit module which is the direct image of its own inverse image along a closed
immersion; the inclusion `i_*𝒞_{Z/X} ⟶ 𝒪_X` of the conormal module of a first-order thickening,
`AlgebraicGeometry.Space.firstOrderConormalModuleι`, is an instance of it.  This file proves that
it is a monomorphism.

## Main results

* `AlgebraicGeometry.Space.mono_submoduleιOfEssImage`: the inclusion
  `AlgebraicGeometry.Space.submoduleιOfEssImage` is a monomorphism.
* `Stacks.CategoryTheory.mono_inv_comp`: the inverse of an isomorphism followed by a monomorphism
  is a monomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ u₁

/-- The inverse of an isomorphism followed by a monomorphism is a monomorphism. -/
theorem mono_inv_comp {C : Type u₁} [Category.{v₁} C] {X Y Z : C} (e : X ≅ Y) (m : X ⟶ Z)
    (hm : Mono m) : Mono (e.inv ≫ m) := by
  have := hm
  infer_instance

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}

/-- **A submodule of the unit module which is the direct image of its own inverse image along a
closed immersion is included in the unit module by a monomorphism.** -/
theorem mono_submoduleιOfEssImage {W : AlgebraicSpaces B S hS} (f : W ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h : (modulePushforward B S hS f).essImage N.toSheafOfModules) :
    Mono (submoduleιOfEssImage B S hS f hf N h) := by
  have hdef : submoduleιOfEssImage B S hS f hf N h =
      (submoduleUnitIsoOfEssImage B S hS f hf N h).inv ≫ N.ι := rfl
  have hmono : Mono N.ι :=
    (SheafOfModules.forget _).mono_of_mono_map
      (inferInstanceAs (Mono N.toSubmodule.ι))
  rw [hdef]
  exact Stacks.CategoryTheory.mono_inv_comp
    (submoduleUnitIsoOfEssImage B S hS f hf N h) N.ι hmono

end AlgebraicGeometry.Space

end
