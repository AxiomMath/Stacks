module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.RingTheory.Koszul.PowerLift.HomTorsion
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence

/-!
# Mayer--Vietoris descent for power-torsion morphism groups

Let `X` be a topological space, `O` a sheaf of commutative rings on it, and `a` a global
section of `O`. Multiplication by `a` makes every morphism group of `D(𝒪_X)` a module over the
ring of global sections (`Stacks.Cohomology.SiteModules.linearSheafOfModules`, transported to the
derived category by `CategoryTheory.Localization.linear`), so it makes sense to ask that every
morphism out of a given object be annihilated by a power of `a`; that is
`Stacks.Koszul.PowerLift.HomPowerTorsion`.

This file proves that the property descends along a cover by two opens. If `X = U ∪ V` and, for
every shift, every morphism into `F` out of the extension by zero of the restriction of `E` to
`U`, to `V` and to `U ∩ V` is killed by a power of `a`, then so is every morphism `E⟦n⟧ ⟶ F`.

## Main results

* `Stacks.Koszul.PowerLift.HomPowerTorsion.of_biprod`: the property passes to a binary
  biproduct of two sources.
* `Stacks.ExtensionByZero.homPowerTorsion_of_cover`: the descent along a cover by two opens.

## References

* [Stacks Project, Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe v u

namespace Stacks.Koszul.PowerLift

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- If every morphism from `A` and every morphism from `B` into `E` is killed by a power of `g`,
then so is every morphism from `A ⊞ B` into `E`. -/
public theorem HomPowerTorsion.of_biprod {g : R} {A B E : C} [HasBinaryBiproduct A B]
    (hA : HomPowerTorsion g A E) (hB : HomPowerTorsion g B E) :
    HomPowerTorsion g (A ⊞ B) E := by
  intro φ
  obtain ⟨k, hk⟩ := hA (biprod.inl ≫ φ)
  obtain ⟨m, hm⟩ := hB (biprod.inr ≫ φ)
  refine ⟨k + m, biprod.hom_ext' _ _ ?_ ?_⟩
  · rw [comp_zero, Linear.comp_smul, pow_add, mul_comm, mul_smul, hk, smul_zero]
  · rw [comp_zero, Linear.comp_smul, pow_add, mul_smul, hm, smul_zero]

end Stacks.Koszul.PowerLift

namespace Stacks.ExtensionByZero

open Stacks.Koszul.PowerLift

attribute [local instance] HasDerivedCategory.standard

/-- Let `X` be a topological space covered by two opens `U` and `V`, let `O` be a sheaf of
commutative rings on `X` and let `a` be a global section of `O`. Let `E` and `F` be objects of
`D(𝒪_X)`. If, in every shift, every morphism into `F` out of the extension by zero of the
restriction of `E` to `U`, to `V` and to `U ∩ V` is annihilated by a power of `a`, then so is
every morphism `E⟦n⟧ ⟶ F`. -/
public theorem homPowerTorsion_of_cover {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [∀ Y : (Opens X)ᵒᵖ, IsMulCommutative (O.obj.obj Y)]
    (a : GlobalSectionRing O) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (E F : DerivedCategory (SheafOfModules.{u} O))
    (hU : ∀ n : ℤ, HomPowerTorsion a (((derivedExtensionRestriction O U).obj E)⟦n⟧) F)
    (hV : ∀ n : ℤ, HomPowerTorsion a (((derivedExtensionRestriction O V).obj E)⟦n⟧) F)
    (hUV' : ∀ n : ℤ, HomPowerTorsion a (((derivedExtensionRestriction O (U ⊓ V)).obj E)⟦n⟧) F)
    (n : ℤ) : HomPowerTorsion a (E⟦n⟧) F := by
  obtain ⟨iU, iV, δ, -, -, htri⟩ :=
    distinguished_extensionRestriction_triangle O U V hUV
      (derivedExtensionRestriction O U) (derivedExtensionRestriction O V)
      (derivedExtensionRestriction O (U ⊓ V))
      (derivedExtensionRestrictionFactorsh O U).inv
      (derivedExtensionRestrictionFactorsh O V).inv
      (derivedExtensionRestrictionFactorsh O (U ⊓ V)).inv
  let : PreservesBinaryBiproducts
      (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) n) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  refine HomPowerTorsion.of_distTriang₃ _
    (Triangle.shift_distinguished _ (htri E) n) ?_ ?_
  · exact HomPowerTorsion.of_iso
      ((shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) n).mapBiprod _ _).symm
      (HomPowerTorsion.of_biprod (hU n) (hV n))
  · exact HomPowerTorsion.of_iso
      ((shiftFunctorAdd' (DerivedCategory (SheafOfModules.{u} O)) n 1 (n + 1) rfl).app _)
      (hUV' (n + 1))

end Stacks.ExtensionByZero

end
