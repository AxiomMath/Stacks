module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossingNaturality
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for the cohomology sheaves of `Rf_*`, natural in the module

Consider a cartesian square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `g` flat.  [Stacks, Tag 02KH] part (1) says that the base change map
`g^* R^q f_* ℱ ⟶ R^q f'_* (g')^* ℱ` is an isomorphism for `f` quasi-compact and quasi-separated
and `ℱ` quasi-coherent; in this library that is
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_higherBaseChangeMap`, stated in the bounded
below model `CategoryTheory.Functor.rightDerivedPlus` of the higher direct images.

This file restates it in the spelling in which the derived direct image of a module is met
elsewhere in the library — the cohomology sheaves of
`AlgebraicGeometry.schemeDerivedPushforward f` applied to the module placed in degree zero — and
proves that the map is **natural in the module**, which is what transporting an isomorphism of
module maps along a flat base change needs.

## Main definitions

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.homologyDerivedPushforwardBaseChange`: the map
  `g^* H^q(Rf_*(ℱ[0])) ⟶ H^q(Rf'_*((g')^* ℱ[0]))`, for every module `ℱ`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.homologyDerivedPushforwardBaseChangeIso`: the
  same as an isomorphism, for `f` quasi-compact and quasi-separated and `ℱ` quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.homologyDerivedPushforwardBaseChange_naturality`:
  the map is natural in `ℱ`.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_homologyDerivedPushforwardBaseChange`:
  **[Stacks, Tag 02KH] part (1)** in this spelling.

## Implementation notes

The map is the base change map of [Stacks, Tag 02N7], `schemeBaseChange`, read on cohomology
sheaves, conjugated by the canonical crossing
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso` between the
two models of the derived direct image.  It differs from `higherBaseChangeMap` only in how the
derived pullback of a module placed in degree zero is identified with the pullback of the
module: here by the natural isomorphism
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` of an exact functor, so that
naturality in the module is a composite of naturality squares.  Invertibility does not depend on
that identification.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeDerived

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] abelianModules enoughInjectivesModules

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
  (H : IsPullback g' f' f g) [Flat g]

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (homologyFunctorDerivedPushforwardIso
  homologyFunctorDerivedPushforwardIso_hom_naturality
  homologyFunctorDerivedPushforwardIso_inv_naturality)

/-- A functor carries a commuting square to a commuting square.  Stated at generic morphisms, so
that it applies across the two spellings of the modules on a scheme, where `rw` does not. -/
private theorem map_comp_eq_map_comp' {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} {a : A ⟶ B} {b : B ⟶ B'} {c : A ⟶ A'} {d : A' ⟶ B'} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- Five commuting squares paste to a commuting rectangle. -/
private theorem comp_five_naturality {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅)
    (b₁ : B₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃) (b₄ : B₃ ⟶ B₄) (b₅ : B₄ ⟶ B₅)
    (x₀ : A₀ ⟶ B₀) (x₁ : A₁ ⟶ B₁) (x₂ : A₂ ⟶ B₂) (x₃ : A₃ ⟶ B₃) (x₄ : A₄ ⟶ B₄) (x₅ : A₅ ⟶ B₅)
    (h₁ : x₀ ≫ b₁ = a₁ ≫ x₁) (h₂ : x₁ ≫ b₂ = a₂ ≫ x₂) (h₃ : x₂ ≫ b₃ = a₃ ≫ x₃)
    (h₄ : x₃ ≫ b₄ = a₄ ≫ x₄) (h₅ : x₄ ≫ b₅ = a₅ ≫ x₅) :
    x₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ x₅ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]

/-- **The base change map on cohomology sheaves of the derived direct image.**  For a cartesian
square with `g` flat and any `𝒪_X`-module `ℱ`, the morphism
`g^* H^q(Rf_*(ℱ[0])) ⟶ H^q(Rf'_*((g')^* ℱ[0]))`: the degree-`q` cohomology of the base change
map of [Stacks, Tag 02N7] at `ℱ[0]`, read through exactness of `g^*` and of `(g')^*` and through
the crossing of the two models of the derived direct image. -/
def homologyDerivedPushforwardBaseChange (F : X.Modules) (q : ℤ) :
    (Scheme.Modules.pullback g).obj ((DerivedCategory.homologyFunctor S.Modules q).obj
        ((schemeDerivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))) ⟶
      (DerivedCategory.homologyFunctor S'.Modules q).obj
        ((schemeDerivedPushforward f').obj ((DerivedCategory.singleFunctor X'.Modules 0).obj
          ((Scheme.Modules.pullback g').obj F))) :=
  have : Flat g' := MorphismProperty.of_isPullback H.flip inferInstance
  have := preservesFiniteLimits_pullback g
  have := preservesFiniteColimits_modulePullback' g
  have := preservesFiniteLimits_pullback g'
  have := preservesFiniteColimits_modulePullback' g'
  (Scheme.Modules.pullback g).map (homologyFunctorDerivedPushforwardIso f F q).hom ≫
    (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (modulePullback g.toLRSHom.toShHom) q).inv.app
      ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) q).map
      ((schemeBaseChange f f' g g' H.w).app ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) q).map
      ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus.map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (modulePullback g'.toLRSHom.toShHom) 0).inv.app F)) ≫
    (homologyFunctorDerivedPushforwardIso f' ((Scheme.Modules.pullback g').obj F) q).inv

/-- **[Stacks, Tag 02KH] part (1), on cohomology sheaves of the derived direct image.**  For a
cartesian square with `g` flat and `f` quasi-compact and quasi-separated, and a quasi-coherent
`𝒪_X`-module `ℱ`, the base change map `g^* H^q(Rf_*(ℱ[0])) ⟶ H^q(Rf'_*((g')^* ℱ[0]))` is an
isomorphism for every `q`. -/
@[ega "IV 2.3.1" "more general", sga "3 VIB 11.0" "more general"]
instance isIso_homologyDerivedPushforwardBaseChange [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℤ) :
    IsIso (homologyDerivedPushforwardBaseChange H F q) := by
  have : Flat g' := MorphismProperty.of_isPullback H.flip inferInstance
  have := preservesFiniteLimits_pullback g
  have := preservesFiniteColimits_modulePullback' g
  have := preservesFiniteLimits_pullback g'
  have := preservesFiniteColimits_modulePullback' g'
  have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) q).map
      ((schemeBaseChange f f' g g' H.w).app ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
    have := baseChangeIsIso f g f' g' H F
    inferInstance
  dsimp only [homologyDerivedPushforwardBaseChange]
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' h₂
    (IsIso.comp_isIso' ?_ ?_)))
  · exact Functor.map_isIso _ _
  · exact ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (modulePullback g.toLRSHom.toShHom) q).app _).isIso_inv
  · exact ((DerivedCategory.Plus.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) q).mapIso
      ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus.mapIso
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (modulePullback g'.toLRSHom.toShHom) 0).app F).symm)).isIso_hom
  · exact Iso.isIso_inv _

/-- The base change isomorphism `g^* H^q(Rf_*(ℱ[0])) ≅ H^q(Rf'_*((g')^* ℱ[0]))`. -/
def homologyDerivedPushforwardBaseChangeIso [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℤ) :
    (Scheme.Modules.pullback g).obj ((DerivedCategory.homologyFunctor S.Modules q).obj
        ((schemeDerivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))) ≅
      (DerivedCategory.homologyFunctor S'.Modules q).obj
        ((schemeDerivedPushforward f').obj ((DerivedCategory.singleFunctor X'.Modules 0).obj
          ((Scheme.Modules.pullback g').obj F))) :=
  asIso (homologyDerivedPushforwardBaseChange H F q)

/-- **The base change map is natural in the module.** -/
theorem homologyDerivedPushforwardBaseChange_naturality {F G : X.Modules} (φ : F ⟶ G) (q : ℤ) :
    (Scheme.Modules.pullback g).map ((DerivedCategory.homologyFunctor S.Modules q).map
        ((schemeDerivedPushforward f).map ((DerivedCategory.singleFunctor X.Modules 0).map φ))) ≫
      homologyDerivedPushforwardBaseChange H G q =
    homologyDerivedPushforwardBaseChange H F q ≫
      (DerivedCategory.homologyFunctor S'.Modules q).map
        ((schemeDerivedPushforward f').map ((DerivedCategory.singleFunctor X'.Modules 0).map
          ((Scheme.Modules.pullback g').map φ))) := by
  have : Flat g' := MorphismProperty.of_isPullback H.flip inferInstance
  have := preservesFiniteLimits_pullback g
  have := preservesFiniteColimits_modulePullback' g
  have := preservesFiniteLimits_pullback g'
  have := preservesFiniteColimits_modulePullback' g'
  exact comp_five_naturality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (map_comp_eq_map_comp' (Scheme.Modules.pullback g)
      (homologyFunctorDerivedPushforwardIso_hom_naturality f φ q))
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (modulePullback g.toLRSHom.toShHom) q).inv.naturality
      ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor _ 0).map φ)))
    (map_comp_eq_map_comp' (DerivedCategory.Plus.homologyFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) q)
      ((schemeBaseChange f f' g g' H.w).naturality
        ((DerivedCategory.Plus.singleFunctor _ 0).map φ)))
    (map_comp_eq_map_comp' ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) q)
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (modulePullback g'.toLRSHom.toShHom) 0).inv.naturality φ))
    (homologyFunctorDerivedPushforwardIso_inv_naturality f' ((Scheme.Modules.pullback g').map φ) q)

end Stacks.AlgebraicGeometry.FlatBaseChangeDerived

end
