module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Derived global sections of sheaves of modules on a ringed space

Global sections of a sheaf of modules on a ringed space `X` form a module over the ring
`Γ(X, 𝒪_X)` of global sections of the structure sheaf, and the resulting functor
`Γ(X, -) : Mod(𝒪_X) ⥤ Mod(Γ(X, 𝒪_X))` is additive, so it has a right derived functor on the
bounded-below derived category. A morphism of ringed spaces `f : X ⟶ Y` induces a ring
homomorphism `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`, and restricting scalars along it puts the derived global
sections over `X` and over `Y` in the same bounded-below derived category.

This file supplies those four objects. It does **not** construct the arrow
`RΓ(Y, G) ⟶ RΓ(X, F)` induced by an `f`-map `f^*G ⟶ F`; see the implementation notes.

## Main definitions

* `Stacks.Cohomology.moduleGlobalSections`: global sections of sheaves of modules, with their
  module structure over the ring of global sections of the structure sheaf.
* `Stacks.Cohomology.globalSectionsRingHom`: the homomorphism on rings of global sections
  induced by a morphism of ringed spaces.
* `Stacks.Cohomology.restrictGlobalScalars`: restriction of scalars along that homomorphism.
* `Stacks.Cohomology.derivedModuleGlobalSections`: the bounded-below right derived functor
  `RΓ(X, -)`.
* `Stacks.Cohomology.derivedModuleGlobalSectionsAlong`: the same functor on `X`, with its values
  regarded as modules over the global sections on `Y` along `f : X ⟶ Y`.

## Main results

* `Stacks.Cohomology.moduleGlobalSections_additive`: global sections of sheaves of modules is an
  additive functor, which is what makes the derived functors below exist.

## Implementation notes

These declarations carry **no** Stacks tag. Stacks 01F9 is the displayed arrow
`RΓ(Y, G) ⟶ RΓ(X, F)` attached to an `f`-map `f^*G ⟶ F`, and that arrow is not constructed here:
what is here is the pair of derived functors between which it runs, together with the change of
rings that puts its two ends in one category. The arrow itself, which is the whole content of
01F9 and therefore its entire covering set, is
`Stacks.Cohomology.derivedModuleGlobalSectionsMap`, and it carries the tag.

The `f`-map is kept in its adjoint form `f^*G ⟶ F`, matching
`pullbackPushforwardAdjunction`, so that a later construction of the arrow can read it off the
adjunction unit.

`HasDerivedCategory.standard` is used as a local instance, since the bounded-below right derived
functor is taken in the standard derived category of the abelian category of sheaves of modules.

## References

* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Global sections of sheaves of modules on a ringed space, with their module structure over
the ring of global sections of the structure sheaf. -/
abbrev moduleGlobalSections (X : RingedSpace.{u}) :
    Modules X ⥤ ModuleCat ((ringCatSheaf X).obj.obj (op ⊤)) :=
  SheafOfModules.evaluation (ringCatSheaf X) (op ⊤)

/-- The homomorphism on rings of global sections induced by a morphism of ringed spaces. -/
noncomputable def globalSectionsRingHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (ringCatSheaf Y).obj.obj (op ⊤) ⟶ (ringCatSheaf X).obj.obj (op ⊤) :=
  RingCat.ofHom (SheafedSpace.Γ.map f.op).hom

/-- Restriction of scalars along the homomorphism of rings of global sections induced by a
morphism of ringed spaces. -/
abbrev restrictGlobalScalars {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ModuleCat ((ringCatSheaf X).obj.obj (op ⊤)) ⥤
      ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤)) :=
  ModuleCat.restrictScalars (globalSectionsRingHom f).hom

/-- Global sections of sheaves of modules is an additive functor: on underlying presheaves of
modules it is evaluation at the top open, which is additive. -/
instance moduleGlobalSections_additive (X : RingedSpace.{u}) :
    (moduleGlobalSections X).Additive := by
  change (SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation (ringCatSheaf X).obj (op ⊤)).Additive
  infer_instance

/-- The bounded-below derived global-sections functor `RΓ(X, -)` on sheaves of modules. -/
noncomputable def derivedModuleGlobalSections (X : RingedSpace.{u})
    [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
    [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
    [EnoughInjectives (Modules X)] :
    DerivedCategory.Plus (Modules X) ⥤
      DerivedCategory.Plus (ModuleCat ((ringCatSheaf X).obj.obj (op ⊤))) :=
  let _ := moduleGlobalSections_additive X
  (moduleGlobalSections X).rightDerivedFunctorPlus

/-- The bounded-below derived global-sections functor on `X`, with its values regarded as
modules over the global sections on `Y` along `f : X ⟶ Y`. -/
noncomputable def derivedModuleGlobalSectionsAlong {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
    [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
    [EnoughInjectives (Modules X)] :
    DerivedCategory.Plus (Modules X) ⥤
      DerivedCategory.Plus (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) :=
  let _ := moduleGlobalSections_additive X
  (moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlus

end

end Stacks.Cohomology

end
