module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
public import StacksFrontier.Topology.Sheaves.OpenImmersion.Restriction
public import StacksFrontier.Topology.Sheaves.RingedSpace.Basic
public import StacksFrontier.Topology.Sheaves.Sheaf.Module
import StacksCore.Tactic.StacksAttribute

/-!
# Locally given objects of the derived category of a ringed space

Let `X` be a ringed space. The glueing problem of Stacks 20.45 starts from a collection of
open subsets of `X`, an object `K_U` of the derived category `D(O_U)` for each member `U` of
the collection, and, for each inclusion `V ⊆ U` of members, an isomorphism
`ρ_{V,U} : (K_U)|_V ≅ K_V`, subject to the cocycle condition
`ρ_{W,U} = ρ_{W,V} ∘ (ρ_{V,U})|_W` for `W ⊆ V ⊆ U`. This file packages that data as the
structure `LocallyGiven`, which is the situation of Stacks 0D67.

Two points require care in a formalisation. First, "restriction" `D(O_U) ⥤ D(O_V)` has to be
the functor induced by ordinary restriction of complexes of sheaves, not an arbitrary functor
between the two categories; this is recorded by the field `restrictionFactors`, which asks for
an isomorphism with the localisation of the complex-level restriction. Second, the composite
`(·)|_V` then `(·)|_W` is not literally `(·)|_W`, so the cocycle condition needs the canonical
comparison between them; that comparison is `openModuleRestrictionComparison`, induced by the
counit of `j_! ⊣ j^*` on the middle open, and the field `restrictionCompFactors` pins
`restrictionComp` down to it.

## Main definitions

* `Stacks.DerivedGlueing.openModuleRestriction`: restriction of sheaves of modules from an
  open `U` to a smaller open `V`, as extension by zero followed by restriction.
* `Stacks.DerivedGlueing.openModuleRestrictionComparison`: the canonical comparison from
  restriction in two steps to direct restriction.
* `Stacks.DerivedGlueing.LocallyGiven`: the locally specified derived objects and their
  transition isomorphisms (Stacks 0D67).

## Implementation notes

Restriction from `U` to `V ⊆ U` is implemented as `j_!` from `U` to `X` followed by `j^*` from
`X` to `V`; for `V ⊆ U` this is canonically ordinary restriction to `V`, and taking this route
means the comparison for a nested pair is literally the counit of the extension-by-zero
adjunction, which is what makes `openModuleRestrictionComparison` available with no choices.
The additivity of the two functors, needed to apply them degreewise to complexes, is
`ExtensionByZeroModules.jStar_additive` and `ExtensionByZeroModules.jShriek_additive`.

The structure sheaf of a ringed space is `CommRingCat`-valued, while extension by zero is
developed for a `RingCat`-valued sheaf of rings, so `underlyingRingSheaf` composes with the
forgetful functor; the derived categories are taken with
`CategoryTheory.HasDerivedCategory.standard`, there being no global instance.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.DerivedGlueing

/-- The structure sheaf of `X`, regarded as a sheaf of (not necessarily commutative) rings. -/
noncomputable abbrev underlyingRingSheaf (X : RingedSpace.{u}) :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
    X.sheaf

/-- The sheaf of rings underlying the restriction of the structure sheaf of `X` to `U`. -/
noncomputable abbrev restrictedRingSheaf (X : RingedSpace.{u}) (U : Opens X) :=
  ExtensionByZeroModules.resRing U (underlyingRingSheaf X)

/-- The unbounded derived category of modules on an open subspace. -/
noncomputable abbrev OpenDerivedCategory (X : RingedSpace.{u}) (U : Opens X) :=
  let C := SheafOfModules.{u} (restrictedRingSheaf X U)
  let _ := HasDerivedCategory.standard C
  DerivedCategory C

/-- Restriction of sheaves of modules from `U` to a smaller open `V`.

We first extend by zero from `U` to `X` and then restrict to `V`. For `V ⊆ U` this is
canonically ordinary restriction to `V`. -/
noncomputable def openModuleRestriction (X : RingedSpace.{u})
    (V U : Opens X) (_ : V ≤ U) :
    CategoryTheory.Functor
      (SheafOfModules.{u} (restrictedRingSheaf X U))
      (SheafOfModules.{u} (restrictedRingSheaf X V)) :=
  ExtensionByZeroModules.jShriek U (underlyingRingSheaf X) ⋙
    ExtensionByZeroModules.jStar V (underlyingRingSheaf X)

/-- Restriction between two opens is additive, being a composite of additive functors. -/
noncomputable instance openModuleRestriction_additive (X : RingedSpace.{u})
    (V U : Opens X) (hVU : V ≤ U) : (openModuleRestriction X V U hVU).Additive := by
  change (ExtensionByZeroModules.jShriek U (underlyingRingSheaf X) ⋙
    ExtensionByZeroModules.jStar V (underlyingRingSheaf X)).Additive
  infer_instance

/-- The comparison from restriction in two steps to direct restriction is induced by the
counit of extension by zero and restriction on the middle open. -/
noncomputable def openModuleRestrictionComparison (X : RingedSpace.{u})
    (W V U : Opens X) (hWV : W ≤ V) (hVU : V ≤ U) :
    openModuleRestriction X V U hVU ⋙ openModuleRestriction X W V hWV ⟶
      openModuleRestriction X W U (hWV.trans hVU) where
  app M := (ExtensionByZeroModules.jStar W (underlyingRingSheaf X)).map
    ((ExtensionByZeroModules.jShriekAdjunction V (underlyingRingSheaf X)).counit.app
      ((ExtensionByZeroModules.jShriek U (underlyingRingSheaf X)).obj M))
  naturality := by
    intro M N f
    simp [openModuleRestriction, Functor.comp_map, ← Functor.map_comp]

/-- A system of locally given derived objects on a ringed space.

The `restrictionComp` field is the canonical identification between direct restriction and
restriction in two steps. With this identification inserted, `cocycle` says exactly
`ρ W U = ρ W V ∘ (ρ V U)|_W`. -/
@[stacks 0D67]
structure LocallyGiven (X : RingedSpace.{u}) where
  /-- The collection of open subsets on which objects are specified. -/
  opens : Set (Opens X)
  /-- Restriction on derived categories for an inclusion of open subsets. -/
  restriction : ∀ (V U : Opens X), V ≤ U →
    OpenDerivedCategory X U ⥤ OpenDerivedCategory X V
  /-- The displayed restriction is induced by ordinary restriction of complexes of sheaves. -/
  restrictionFactors : ∀ (V U : Opens X) (hVU : V ≤ U),
    let CU := SheafOfModules.{u} (restrictedRingSheaf X U)
    let CV := SheafOfModules.{u} (restrictedRingSheaf X V)
    let _ := HasDerivedCategory.standard CU
    let _ := HasDerivedCategory.standard CV
    DerivedCategory.Q ⋙ restriction V U hVU ≅
      (openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q
  /-- The canonical comparison of direct restriction with restriction in two steps. -/
  restrictionComp : ∀ (W V U : Opens X) (hWV : W ≤ V) (hVU : V ≤ U),
    restriction W U (hWV.trans hVU) ≅
      restriction V U hVU ⋙ restriction W V hWV
  /-- The comparison is the one induced by the counit on ordinary complexes; after
  localization it is uniquely determined by this equality. -/
  restrictionCompFactors : ∀ (W V U : Opens X) (hWV : W ≤ V) (hVU : V ≤ U)
      (C : HomologicalComplex
        (SheafOfModules.{u} (restrictedRingSheaf X U))
        (ComplexShape.up ℤ)),
    let CU := SheafOfModules.{u} (restrictedRingSheaf X U)
    let _ := HasDerivedCategory.standard CU
    let CW := SheafOfModules.{u} (restrictedRingSheaf X W)
    let _ := HasDerivedCategory.standard CW
    let FVU := openModuleRestriction X V U hVU
    let FWV := openModuleRestriction X W V hWV
    (restrictionComp W V U hWV hVU).hom.app (DerivedCategory.Q.obj C) ≫
      (restriction W V hWV).map ((restrictionFactors V U hVU).hom.app C) ≫
      (restrictionFactors W V hWV).hom.app
        ((FVU.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (FVU ⋙ FWV))
          (ComplexShape.up ℤ)).hom.app C) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (openModuleRestrictionComparison X W V U hWV hVU)
          (ComplexShape.up ℤ)).app C) =
      (restrictionFactors W U (hWV.trans hVU)).hom.app C
  /-- The object specified on each member of the collection. -/
  obj : ∀ (U : Opens X), U ∈ opens → OpenDerivedCategory X U
  /-- The transition isomorphism associated to an inclusion. -/
  rho : ∀ (V U : Opens X) (hVU : V ≤ U) (hU : U ∈ opens) (hV : V ∈ opens),
    (restriction V U hVU).obj (obj U hU) ≅ obj V hV
  /-- The transition isomorphisms satisfy the cocycle condition. -/
  cocycle : ∀ (W V U : Opens X) (hWV : W ≤ V) (hVU : V ≤ U)
      (hU : U ∈ opens) (hV : V ∈ opens) (hW : W ∈ opens),
    (rho W U (hWV.trans hVU) hU hW).hom =
      (restrictionComp W V U hWV hVU).hom.app (obj U hU) ≫
        (restriction W V hWV).map (rho V U hVU hU hV).hom ≫
          (rho W V hWV hV hW).hom

end Stacks.DerivedGlueing
