module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorQuasiInverse
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModel
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeTransformation
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction

public import StacksFrontier.CategoryTheory.Sites.PushforwardSquareSheafCompose
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived direct and inverse images of pro-étale sheaves of modules

Let `Λ` be a ring. For a morphism of schemes `f : X ⟶ Y`, direct image of sheaves of
`Λ`-modules on the small pro-étale sites, `f_* = ` restriction along pro-étale base change, has a
total right derived functor `Rf_* : D(X_proét, Λ) ⥤ D(Y_proét, Λ)` on the unbounded derived
categories, and the inverse image `f⁻¹`, being exact, induces `f⁻¹ : D(Y_proét, Λ) ⥤
D(X_proét, Λ)` with no derivation; the two are adjoint. For a commutative square of schemes there
is the canonical base change map `g⁻¹ Rf_* K ⟶ Rf'_* (g')⁻¹ K` (the shape of Cohomology on Sites,
Remark 07A7).

## Main definitions

* `AlgebraicGeometry.ProEtale.proetaleModuleDirectImage`: direct image of pro-étale sheaves of
  `Λ`-modules.
* `AlgebraicGeometry.ProEtale.proetaleModuleDerivedDirectImage`: its total right derived functor
  `Rf_*` on unbounded derived categories.
* `AlgebraicGeometry.ProEtale.proetaleModuleDerivedInverseImage`: the functor `f⁻¹` induced on
  derived categories by the exact inverse image.
* `AlgebraicGeometry.ProEtale.proetaleModuleDerivedAdjunction`: `f⁻¹ ⊣ Rf_*`.
* `AlgebraicGeometry.ProEtale.proetaleModuleDerivedInverseImageCompIso`: `b⁻¹ ⋙ a⁻¹ ≅ (a ≫ b)⁻¹`
  on derived categories.
* `AlgebraicGeometry.ProEtale.proetaleModuleDerivedBaseChange` and
  `AlgebraicGeometry.ProEtale.proetaleModuleDerivedBaseChangeMap`: the base change map of a
  commutative square of schemes.

## Implementation notes

`D(X_proét, Λ)` is the derived category of `Sheaf (Scheme.ProEt.topology X) (ModuleCat Λ)`, at
the standard model `HasDerivedCategory.standard`. The categories of sheaves are Grothendieck
abelian at the universe of the sections, because the small pro-étale site is essentially small
there; this is the input of the K-injective resolutions computing `Rf_*`
(`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`).

The adjunction is `Stacks.DerivedModel.adjunctionOfExact`, transported along
`Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory`.

The base change map only uses that the square commutes, `f' ≫ g = g' ≫ f`, through the
composition isomorphisms of inverse images; it is
`Stacks.CategoryTheory.BaseChange.map`, the mate of the comparison of the two composites.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 09C9](https://stacks.math.columbia.edu/tag/09C9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type v) [CommRing Λ]

/-- Modules over `Λ` with carriers in a universe containing that of `Λ` form a Grothendieck
abelian category. Mathlib's instance is stated only when the two universes agree. -/
instance isGrothendieckAbelian_moduleCatMax :
    IsGrothendieckAbelian.{max v w} (ModuleCat.{max v w} Λ) :=
  letI : AB5 (ModuleCat.{max v w} Λ) :=
    { ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor J
        (forget₂ (ModuleCat.{max v w} Λ) AddCommGrpCat) }
  {}

/-- Sheaves of `Λ`-modules on a small pro-étale site form a Grothendieck abelian category at the
universe of their sections. -/
instance isGrothendieckAbelian_proetaleModuleSheaf (X : Scheme.{u}) :
    IsGrothendieckAbelian.{max (u + 1) v w}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) :=
  have := isGrothendieckAbelian_moduleCatMax.{v, max (u + 1) w} Λ
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

variable {Λ}

/-- Direct image of pro-étale sheaves of `Λ`-modules along a morphism of schemes: restriction
along pro-étale base change. -/
abbrev proetaleModuleDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ) :=
  (Scheme.proetaleBaseChange g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v w} Λ)
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)

/-- Direct image is additive, being a right adjoint. -/
instance additive_proetaleModuleDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleModuleDirectImage.{u, v, w} (Λ := Λ) g).Additive := by
  have := (proetaleModuleInverseImageAdjunction.{u, v, w} Λ g).rightAdjoint_preservesLimits.{0, 0}
  exact Functor.additive_of_preserves_binary_products _

/-- Direct image applied degreewise to unbounded complexes, followed by the localization onto
the derived category of the target. Its right derived functor is `Rf_*`. -/
abbrev proetaleModulePushforwardToDerivedCategory {Z X : Scheme.{u}} (g : Z ⟶ X) :
    HomotopyCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ))
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) :=
  (proetaleModuleDirectImage.{u, v, w} (Λ := Λ) g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Degreewise direct image followed by localization has a pointwise right derived functor with
respect to quasi-isomorphisms. -/
instance hasPointwiseRightDerivedFunctor_proetaleModulePushforwardToDerivedCategory
    {Z X : Scheme.{u}} (g : Z ⟶ X) :
    Functor.HasPointwiseRightDerivedFunctor
      (proetaleModulePushforwardToDerivedCategory.{u, v, w} (Λ := Λ) g)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- **The derived direct image `Rf_*`** of pro-étale sheaves of `Λ`-modules on unbounded derived
categories: the total right derived functor of degreewise direct image. -/
abbrev proetaleModuleDerivedDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) :=
  (proetaleModulePushforwardToDerivedCategory.{u, v, w} (Λ := Λ) g).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The unit of the derived direct image. -/
abbrev proetaleModuleDerivedDirectImageUnit {Z X : Scheme.{u}} (g : Z ⟶ X) :
    proetaleModulePushforwardToDerivedCategory.{u, v, w} (Λ := Λ) g ⟶
      DerivedCategory.Qh ⋙ proetaleModuleDerivedDirectImage.{u, v, w} g :=
  (proetaleModulePushforwardToDerivedCategory.{u, v, w} (Λ := Λ) g).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- `Rf_*`, with its unit, is a right derived functor of degreewise direct image with respect to
quasi-isomorphisms. -/
instance isRightDerivedFunctor_proetaleModuleDerivedDirectImage {Z X : Scheme.{u}}
    (g : Z ⟶ X) :
    (proetaleModuleDerivedDirectImage.{u, v, w} (Λ := Λ) g).IsRightDerivedFunctor
      (proetaleModuleDerivedDirectImageUnit.{u, v, w} g)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  dsimp only [proetaleModuleDerivedDirectImage, proetaleModuleDerivedDirectImageUnit]
  infer_instance

/-- **The inverse image `f⁻¹`** on unbounded derived categories of pro-étale sheaves of
`Λ`-modules, induced by the exact inverse image. -/
abbrev proetaleModuleDerivedInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{max (u + 1) v w} Λ)) :=
  (proetaleModuleInverseImage.{u, v, w} g Λ).mapDerivedCategory

/-- **The derived adjunction `f⁻¹ ⊣ Rf_*`** on unbounded derived categories of pro-étale sheaves
of `Λ`-modules. -/
def proetaleModuleDerivedAdjunction {Z X : Scheme.{u}} (g : Z ⟶ X) :
    proetaleModuleDerivedInverseImage.{u, v, w} (Λ := Λ) g ⊣
      proetaleModuleDerivedDirectImage.{u, v, w} g :=
  Stacks.DerivedFunctor.derivedAdjunction (proetaleModuleInverseImageAdjunction.{u, v, w} Λ g)
    (proetaleModuleDerivedDirectImage.{u, v, w} g)
    (proetaleModuleDerivedDirectImageUnit.{u, v, w} g)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- Inverse image along `b` followed by inverse image along `a` is inverse image along `a ≫ b`,
on derived categories. -/
def proetaleModuleDerivedInverseImageCompIso {Y Z X : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ X) :
    proetaleModuleDerivedInverseImage.{u, v, w} (Λ := Λ) b ⋙
        proetaleModuleDerivedInverseImage.{u, v, w} a ≅
      proetaleModuleDerivedInverseImage.{u, v, w} (a ≫ b) :=
  Functor.mapDerivedCategoryCompIso (proetaleModuleInverseImageCompIso.{u, v, w} Λ a b)

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : f' ≫ g = g' ≫ f)

/-- The comparison `g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite direct images around a
commutative square of schemes: both are direct image along the common composite `X' ⟶ Y`. -/
def proetaleModuleDirectImageSquare :
    proetaleModuleDirectImage.{u, v, w} (Λ := Λ) g' ⋙ proetaleModuleDirectImage.{u, v, w} f ≅
      proetaleModuleDirectImage.{u, v, w} (Λ := Λ) f' ⋙ proetaleModuleDirectImage.{u, v, w} g :=
  Functor.sheafPushforwardSquare (Scheme.ProEt.topology X') (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology Y') (Scheme.ProEt.topology Y)
    (Scheme.proetaleBaseChangeCompIso g' f ≪≫
      eqToIso (congrArg Scheme.proetaleBaseChange w.symm) ≪≫
      (Scheme.proetaleBaseChangeCompIso f' g).symm) (ModuleCat.{max (u + 1) v w} Λ)

/-- The underived base change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of pro-étale sheaves of
`Λ`-modules: the mate, under the inverse-image/direct-image adjunctions for the horizontal
morphisms `g'` and `g`, of the identification `g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite
direct images around the square. -/
@[sga "4 Vbis 3.2.2" "special case"]
def proetaleModuleBaseChange :
    proetaleModuleDirectImage.{u, v, w} (Λ := Λ) f ⋙ proetaleModuleInverseImage.{u, v, w} g Λ ⟶
      proetaleModuleInverseImage.{u, v, w} g' Λ ⋙ proetaleModuleDirectImage.{u, v, w} f' :=
  ((mateEquiv (proetaleModuleInverseImageAdjunction.{u, v, w} Λ g')
    (proetaleModuleInverseImageAdjunction.{u, v, w} Λ g)).symm
      (TwoSquare.mk _ _ _ _ (proetaleModuleDirectImageSquare f g f' g' w).hom)).natTrans

/-- **The base change map** `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of a commutative square of schemes, on
unbounded derived categories of pro-étale sheaves of `Λ`-modules (Cohomology on Sites, Remark
07A7): the descent, along the universal property of `Rf_* ⋙ g⁻¹` as a right derived functor of
degreewise `f_* ⋙ g⁻¹`, of the degreewise base change comparison followed by the unit of
`Rf'_*` (`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap`). -/
def proetaleModuleDerivedBaseChange :
    proetaleModuleDerivedDirectImage.{u, v, w} (Λ := Λ) f ⋙
        proetaleModuleDerivedInverseImage.{u, v, w} g ⟶
      proetaleModuleDerivedInverseImage.{u, v, w} g' ⋙
        proetaleModuleDerivedDirectImage.{u, v, w} f' :=
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
    (proetaleModuleInverseImage.{u, v, w} g' Λ) (proetaleModuleInverseImage.{u, v, w} g Λ)
    (proetaleModuleDirectImage.{u, v, w} (Λ := Λ) f)
    (proetaleModuleDirectImage.{u, v, w} (Λ := Λ) f')
    (proetaleModuleDerivedDirectImage.{u, v, w} f) (proetaleModuleDerivedDirectImage.{u, v, w} f')
    (proetaleModuleDerivedDirectImageUnit.{u, v, w} f)
    (proetaleModuleDerivedDirectImageUnit.{u, v, w} f')
    (proetaleModuleBaseChange f g f' g' w)

/-- The base change map at an object. -/
def proetaleModuleDerivedBaseChangeMap
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))) :
    (proetaleModuleDerivedInverseImage.{u, v, w} g).obj
        ((proetaleModuleDerivedDirectImage.{u, v, w} f).obj K) ⟶
      (proetaleModuleDerivedDirectImage.{u, v, w} f').obj
        ((proetaleModuleDerivedInverseImage.{u, v, w} g').obj K) :=
  (proetaleModuleDerivedBaseChange f g f' g' w).app K

end BaseChange

end AlgebraicGeometry.ProEtale
