module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksCore.Tactic.StacksAttribute

/-!
# The resolution property

A scheme has the resolution property when every finite type quasi-coherent module on it is a
quotient of a finite locally free module.

## Main definitions

* `AlgebraicGeometry.HasResolutionProperty` is the resolution property for schemes.

## Main results

* `AlgebraicGeometry.hasResolutionProperty_iff` characterizes the resolution property by the
  existence of finite locally free epimorphisms onto finite type quasi-coherent modules.

## Implementation notes

A quotient of sheaves of modules is represented by an epimorphism in the category of modules on
the scheme. The property is a typeclass, in keeping with other intrinsic properties of schemes;
the characterizing equivalence allows it to be used propositionally as well.

## References

* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A scheme has the resolution property if every finite type quasi-coherent module on it is a
quotient of a finite locally free module. -/
@[stacks 0F86]
class HasResolutionProperty (X : Scheme.{u}) : Prop where
  /-- Every finite type quasi-coherent module is the target of an epimorphism from a finite
  locally free module. -/
  exists_finiteLocallyFree_quotient
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (E : X.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (f : E ⟶ F), Epi f

/-- A scheme has the resolution property exactly when every finite type quasi-coherent module is
the target of an epimorphism from a finite locally free module. -/
@[simp]
theorem hasResolutionProperty_iff (X : Scheme.{u}) :
    HasResolutionProperty X ↔
      ∀ (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
        ∃ (E : X.Modules)
          (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
          (f : E ⟶ F), Epi f := ⟨fun h F ↦ h.exists_finiteLocallyFree_quotient F, fun h ↦ ⟨h⟩⟩

end AlgebraicGeometry
