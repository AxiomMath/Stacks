module

public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroHom
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroNaturality

/-!
# Classes of morphisms out of the structure sheaf under the degree-zero Künneth map

`AlgebraicGeometry.degreeZeroClassAddEquiv` identifies a morphism `s : 𝒪_X ⟶ E` in `D(𝒪_X)` with
a degree-zero class of `RΓ(X, E)` (Stacks 08JA at source the structure sheaf), in the spelling
`AlgebraicGeometry.degreeZeroSectionsField` of the degree-zero Künneth statement. This file
proves that this identification is natural in `E`, so that every class is the image of the class
`1_X` of the identity of `𝒪_X`, and deduces how the degree-zero Künneth map
`AlgebraicGeometry.degreeZeroKunnethMap` acts on classes: the product of the classes of
`s : 𝒪_X ⟶ A` and `t : 𝒪_Y ⟶ B` is the class of `u ≫ (Lp^*s ⊗ Lq^*t)`, for one morphism
`u : 𝒪_W ⟶ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` on `W = X ×_k Y` that does not depend on `s`, `t`, `A` or `B`.

## Main results

* `AlgebraicGeometry.degreeZeroClassAddEquiv_comp`: the class of `s ≫ g` is the image of the
  class of `s` under `H⁰RΓ(X, g)`.
* `AlgebraicGeometry.degreeZeroClassAddEquiv_eq_map_unit`: the class of `s` is `H⁰RΓ(X, s)(1_X)`.
* `AlgebraicGeometry.degreeZeroKunnethMap_classes`: the degree-zero Künneth map on two classes.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace MonoidalCategory
open scoped TensorProduct

attribute [local instance 100000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)
open Stacks.AlgebraicGeometry.ProperSupportCoherent (homologyZeroForgetIso homologyZeroForgetNatIso)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

section OneScheme

variable (k : Type u) [Field k] (X : Over (Spec (.of k)))

/-- The map `H⁰RΓ(X, E) ⟶ H⁰RΓ(X, E')` over `k` induced by a morphism `g : E ⟶ E'`. -/
abbrev degreeZeroSectionsFieldMap {E E' : DerivedCategory X.left.Modules} (g : E ⟶ E') :
    degreeZeroSectionsField k X.hom E ⟶ degreeZeroSectionsField k X.hom E' :=
  (gammaRestrict k).map
    ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
      ((sectionsOverBase X.hom.toLRSHom.toShHom).map g))

/-- **The class of a morphism out of the structure sheaf is natural in the target.** For
`s : 𝒪_X ⟶ E` and `g : E ⟶ E'`, the class of `s ≫ g` is the image of the class of `s` under the
map `g` induces on `H⁰RΓ(X, -)`. -/
theorem degreeZeroClassAddEquiv_comp {E E' : DerivedCategory X.left.Modules}
    (s : structureSheafObj k X ⟶ E) (g : E ⟶ E') :
    degreeZeroClassAddEquiv k X E' (s ≫ g) =
      (degreeZeroSectionsFieldMap k X g).hom (degreeZeroClassAddEquiv k X E s) := by
  set x := degreeZeroClassAddEquiv k X E s
  have hs : (degreeZeroClassAddEquiv k X E).symm x = s :=
    (degreeZeroClassAddEquiv k X E).symm_apply_apply s
  apply (degreeZeroClassAddEquiv k X E').symm.injective
  rw [AddEquiv.symm_apply_apply]
  change s ≫ g = structureSheafGlobalSectionsEquivScheme k X E'
    ((homologyZeroForgetIso X.hom E').hom
      ((homologyZeroGlobalSectionsOverIso k X E').inv.hom
        ((degreeZeroSectionsFieldMap k X g).hom x)))
  have hnat : (homologyZeroGlobalSectionsOverIso k X E').inv.hom
      ((degreeZeroSectionsFieldMap k X g).hom x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver X.hom).map g)).hom
        ((homologyZeroGlobalSectionsOverIso k X E).inv.hom x) :=
    ConcreteCategory.congr_hom ((homologyZeroGlobalSectionsOverNatIso k X).inv.naturality g) x
  have key : (homologyZeroForgetIso X.hom E').hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver X.hom).map g)).hom
        ((homologyZeroGlobalSectionsOverIso k X E).inv.hom x)) =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.left.sheaf)).map g))
        ((homologyZeroForgetIso X.hom E).hom
          ((homologyZeroGlobalSectionsOverIso k X E).inv.hom x)) :=
    ((CategoryTheory.comp_apply
        ((derivedGlobalSectionsOver X.hom ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ⋙
          forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map g)
        ((homologyZeroForgetNatIso X.hom).hom.app _) _).symm.trans
      (ConcreteCategory.congr_hom ((homologyZeroForgetNatIso X.hom).hom.naturality g) _)).trans
        (CategoryTheory.comp_apply ((homologyZeroForgetNatIso X.hom).hom.app _)
          ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
            (Stacks.SheafOfModules.ringedSite X.left.sheaf) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map g) _)
  have hS := RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality
    (Stacks.SheafOfModules.ringedSite X.left.sheaf) g
    ((homologyZeroForgetIso X.hom E).hom ((homologyZeroGlobalSectionsOverIso k X E).inv.hom x))
  rw [hnat, key]
  exact (hS.trans (congrArg (· ≫ g) hs)).symm

/-- `1_X`, the class of the identity of the structure sheaf. -/
abbrev degreeZeroUnitClass : degreeZeroSectionsField k X.hom (structureSheafObj k X) :=
  degreeZeroClassAddEquiv k X (structureSheafObj k X) (𝟙 _)

/-- **Every class is the image of the class of the identity.** For `s : 𝒪_X ⟶ E` the class of
`s` is `H⁰RΓ(X, s)(1_X)`. -/
theorem degreeZeroClassAddEquiv_eq_map_unit {E : DerivedCategory X.left.Modules}
    (s : structureSheafObj k X ⟶ E) :
    degreeZeroClassAddEquiv k X E s =
      (degreeZeroSectionsFieldMap k X s).hom (degreeZeroUnitClass k X) := by
  simpa only [Category.id_comp] using degreeZeroClassAddEquiv_comp k X (𝟙 _) s

end OneScheme

section TwoSchemes

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- `W = X ×_k Y` as a scheme over `Spec k`, through the first projection. -/
abbrev fibreProductOver : Over (Spec (.of k)) :=
  Over.mk (Limits.pullback.fst X.hom Y.hom ≫ X.hom)

/-- `Lp^*u ⊗ Lq^*v : Lp^*A ⊗^𝐋 Lq^*B ⟶ Lp^*A' ⊗^𝐋 Lq^*B'`, in the form of
`AlgebraicGeometry.degreeZeroKunnethMap_naturality`. -/
abbrev boxDerivedMap {A A' : DerivedCategory X.left.Modules} {B B' : DerivedCategory Y.left.Modules}
    (u : A ⟶ A') (v : B ⟶ B') :
    boxDerived k X.hom Y.hom A B ⟶ boxDerived k X.hom Y.hom A' B' :=
  ((derivedTensorProductFunctor (Limits.pullback X.hom Y.hom).toRingedSpace.sheaf).map
      ((derivedPullback (Limits.pullback.fst X.hom Y.hom).toLRSHom.toShHom).map u)).app
        ((derivedPullback (Limits.pullback.snd X.hom Y.hom).toLRSHom.toShHom).obj B) ≫
    ((derivedTensorProductFunctor (Limits.pullback X.hom Y.hom).toRingedSpace.sheaf).obj
      ((derivedPullback (Limits.pullback.fst X.hom Y.hom).toLRSHom.toShHom).obj A')).map
      ((derivedPullback (Limits.pullback.snd X.hom Y.hom).toLRSHom.toShHom).map v)

/-- **The unit of the degree-zero Künneth map on classes**: the morphism
`𝒪_W ⟶ Lp^*𝒪_X ⊗^𝐋 Lq^*𝒪_Y` whose class is the degree-zero Künneth product `μ(1_X ⊗ 1_Y)`. -/
def degreeZeroKunnethUnit :
    structureSheafObj k (fibreProductOver k X Y) ⟶
      boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y) :=
  (degreeZeroClassAddEquiv k (fibreProductOver k X Y)
      (boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y))).symm
    ((degreeZeroKunnethMap k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y)).hom
      (degreeZeroUnitClass k X ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace] degreeZeroUnitClass k Y))

/-- **The degree-zero Künneth map on classes.** For `s : 𝒪_X ⟶ A` and `t : 𝒪_Y ⟶ B`, the
degree-zero Künneth product of the classes of `s` and `t` is the class of
`u ≫ (Lp^*s ⊗ Lq^*t)`, where `u = AlgebraicGeometry.degreeZeroKunnethUnit k X Y` depends on
neither `s`, `t`, `A` nor `B`. -/
theorem degreeZeroKunnethMap_classes {A : DerivedCategory X.left.Modules}
    {B : DerivedCategory Y.left.Modules} (s : structureSheafObj k X ⟶ A)
    (t : structureSheafObj k Y ⟶ B) :
    (degreeZeroKunnethMap k X.hom Y.hom A B).hom
        (degreeZeroClassAddEquiv k X A s ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace]
          degreeZeroClassAddEquiv k Y B t) =
      degreeZeroClassAddEquiv k (fibreProductOver k X Y) (boxDerived k X.hom Y.hom A B)
        (degreeZeroKunnethUnit k X Y ≫ boxDerivedMap k X Y s t) := by
  rw [degreeZeroClassAddEquiv_eq_map_unit k X s, degreeZeroClassAddEquiv_eq_map_unit k Y t]
  refine (ConcreteCategory.congr_hom (degreeZeroKunnethMap_naturality k X.hom Y.hom s t)
    (degreeZeroUnitClass k X ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace]
      degreeZeroUnitClass k Y)).trans ?_
  have hc := degreeZeroClassAddEquiv_comp k (fibreProductOver k X Y)
    (degreeZeroKunnethUnit k X Y) (boxDerivedMap k X Y s t)
  have hu : degreeZeroClassAddEquiv k (fibreProductOver k X Y)
      (boxDerived k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y))
      (degreeZeroKunnethUnit k X Y) =
    (degreeZeroKunnethMap k X.hom Y.hom (structureSheafObj k X) (structureSheafObj k Y)).hom
      (degreeZeroUnitClass k X ⊗ₜ[baseRing (Spec (.of k)).toRingedSpace] degreeZeroUnitClass k Y) :=
    AddEquiv.apply_symm_apply _ _
  rw [hu] at hc
  exact hc.symm

end TwoSchemes

end AlgebraicGeometry

end
