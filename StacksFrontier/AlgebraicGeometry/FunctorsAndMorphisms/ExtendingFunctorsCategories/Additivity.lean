module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.Extension
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.ExtendingFunctorsCategories.FiniteModuleRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Additivity of extensions from finite modules

Every filtered-colimit-preserving extension of an additive functor between categories of finite
modules is additive.

## Main results

* `ModuleCat.fgFilteredColimitExtension_additive`: any such extension is additive.

## Implementation notes

The result applies to an arbitrary filtered-colimit-preserving extension together with its
specified identification on the finite modules, not only to the chosen extension; existence of
an extension is supplied separately, and no Noetherian hypothesis is needed once an extension is
given. Additivity is transported to the restriction of the extension along that identification
and then propagated to all modules by
`ModuleCat.additive_of_finiteModuleRestriction`, since every module is the filtered colimit of
its finite submodules.

## References

* [Stacks Project, Tag 0GP9](https://stacks.math.columbia.edu/tag/0GP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable (A : Type u) [CommRing A]
variable (B : Type w) [CommRing B]

/-- **Stacks Project, Tag 0GP9.** Every filtered-colimit-preserving extension of an additive
functor on finite modules is additive. -/
@[stacks 0GP9 "additivity"]
instance fgFilteredColimitExtension_additive
    {F : FGModuleCat.{v} A ⥤ FGModuleCat.{v} B}
    (E : FGFilteredColimitExtension.{u, v, w} A B F) [F.Additive] :
    E.functor.Additive := by
  let : (forget₂ (FGModuleCat.{v} B) (ModuleCat.{v} B)).Additive := ⟨by intros; rfl⟩
  let : (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E.functor).Additive :=
    Functor.additive_of_iso E.iso.symm
  exact additive_of_finiteModuleRestriction A E.functor

end ModuleCat
