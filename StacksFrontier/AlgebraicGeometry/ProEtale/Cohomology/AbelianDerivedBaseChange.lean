module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SuccUniverseCoefficients
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AbelianSheafification
public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedExactness

public import StacksFrontier.CategoryTheory.Sites.PushforwardSquareSheafCompose

/-!
# Derived direct and inverse images of pro-étale abelian sheaves, and their base change map

For a morphism of schemes `f : X ⟶ Y` and abelian sheaves on the small pro-étale sites: direct
image (restriction along pro-étale base change), its total right derived functor `Rf_*` on
unbounded derived categories, the exact inverse image, and for a commutative square of schemes
the base change map `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹`, built exactly as for sheaves of `Λ`-modules
(`AlgebraicGeometry.ProEtale.proetaleModuleDerivedBaseChange`).

## Main definitions

* `AlgebraicGeometry.ProEtale.proetaleAbelianDirectImage`,
  `AlgebraicGeometry.ProEtale.proetaleAbelianInverseImage` and their adjunction.
* `AlgebraicGeometry.ProEtale.proetaleAbelianDerivedDirectImage`: `Rf_*`.
* `AlgebraicGeometry.ProEtale.proetaleAbelianBaseChange`: the underived base change map, the
  horizontal mate of the comparison of composite direct images.
* `AlgebraicGeometry.ProEtale.proetaleAbelianDerivedBaseChange`: the derived base change map.

## Implementation notes

Standard model: the derived direct image is formed at `HasDerivedCategory.standard`, as for
sheaves of modules (`AlgebraicGeometry.ProEtale.proetaleModuleDerivedDirectImage`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasSheafify_proetale_addCommGrpCat_succ
  isGrothendieckAbelian_proetale_ab_succ

/-- Direct image of pro-étale abelian sheaves along a morphism of schemes
(`AlgebraicGeometry.ProEtale.Abelian.proetaleDirectImage`). -/
abbrev proetaleAbelianDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  Abelian.proetaleDirectImage.{u, 0} g

/-- Inverse image of pro-étale abelian sheaves along a morphism of schemes
(`AlgebraicGeometry.ProEtale.Abelian.proetaleInverseImage`). -/
abbrev proetaleAbelianInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  Abelian.proetaleInverseImage.{u, 0} g

/-- Inverse image is left adjoint to direct image. -/
abbrev proetaleAbelianInverseImageAdjunction {Z X : Scheme.{u}} (g : Z ⟶ X) :
    proetaleAbelianInverseImage g ⊣ proetaleAbelianDirectImage g :=
  Abelian.proetaleInverseImageDirectImageAdj.{u, 0} g

/-- Direct image of pro-étale abelian sheaves is an additive functor. -/
instance additive_proetaleAbelianDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleAbelianDirectImage g).Additive :=
  (proetaleAbelianInverseImageAdjunction g).right_adjoint_additive

/-- Inverse image of pro-étale abelian sheaves is an additive functor. -/
instance additive_proetaleAbelianInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleAbelianInverseImage g).Additive :=
  (proetaleAbelianInverseImageAdjunction g).left_adjoint_additive

/-- Direct image of complexes followed by localization; its right derived functor is `Rf_*`. -/
abbrev proetaleAbelianPushforwardToDerivedCategory {Z X : Scheme.{u}} (g : Z ⟶ X) :
    HomotopyCategory (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  (proetaleAbelianDirectImage g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `proetaleAbelianPushforwardToDerivedCategory g` has a pointwise right derived functor with
respect to quasi-isomorphisms. -/
instance hasPointwiseRightDerivedFunctor_proetaleAbelianPushforwardToDerivedCategory
    {Z X : Scheme.{u}} (g : Z ⟶ X) :
    (proetaleAbelianPushforwardToDerivedCategory g).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- **The derived direct image `Rf_*`** of pro-étale abelian sheaves on unbounded derived
categories. -/
abbrev proetaleAbelianDerivedDirectImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  (proetaleAbelianPushforwardToDerivedCategory g).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The unit of `Rf_*`. -/
abbrev proetaleAbelianDerivedDirectImageUnit {Z X : Scheme.{u}} (g : Z ⟶ X) :
    proetaleAbelianPushforwardToDerivedCategory g ⟶
      DerivedCategory.Qh ⋙ proetaleAbelianDerivedDirectImage g :=
  (proetaleAbelianPushforwardToDerivedCategory g).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The inverse image on unbounded derived categories. -/
abbrev proetaleAbelianDerivedInverseImage {Z X : Scheme.{u}} (g : Z ⟶ X) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) :=
  (proetaleAbelianInverseImage g).mapDerivedCategory

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : f' ≫ g = g' ≫ f)

/-- The comparison `g'_* ⋙ f_* ≅ f'_* ⋙ g_*` of the two composite direct images. -/
def proetaleAbelianDirectImageSquare :
    proetaleAbelianDirectImage g' ⋙ proetaleAbelianDirectImage f ≅
      proetaleAbelianDirectImage f' ⋙ proetaleAbelianDirectImage g :=
  Functor.sheafPushforwardSquare (Scheme.ProEt.topology X') (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology Y') (Scheme.ProEt.topology Y)
    (Scheme.proetaleBaseChangeCompIso g' f ≪≫
      eqToIso (congrArg Scheme.proetaleBaseChange w.symm) ≪≫
      (Scheme.proetaleBaseChangeCompIso f' g).symm) AddCommGrpCat.{u + 1}

/-- The underived base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of pro-étale abelian sheaves: the
horizontal mate of the comparison of the composite direct images. -/
def proetaleAbelianBaseChange :
    proetaleAbelianDirectImage f ⋙ proetaleAbelianInverseImage g ⟶
      proetaleAbelianInverseImage g' ⋙ proetaleAbelianDirectImage f' :=
  ((mateEquiv (proetaleAbelianInverseImageAdjunction g')
    (proetaleAbelianInverseImageAdjunction g)).symm
      (TwoSquare.mk _ _ _ _ (proetaleAbelianDirectImageSquare f g f' g' w).hom)).natTrans

/-- **The base change map** `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` of pro-étale abelian sheaves. -/
def proetaleAbelianDerivedBaseChange :
    proetaleAbelianDerivedDirectImage f ⋙ proetaleAbelianDerivedInverseImage g ⟶
      proetaleAbelianDerivedInverseImage g' ⋙ proetaleAbelianDerivedDirectImage f' :=
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
    (proetaleAbelianInverseImage g') (proetaleAbelianInverseImage g)
    (proetaleAbelianDirectImage f) (proetaleAbelianDirectImage f')
    (proetaleAbelianDerivedDirectImage f) (proetaleAbelianDerivedDirectImage f')
    (proetaleAbelianDerivedDirectImageUnit f) (proetaleAbelianDerivedDirectImageUnit f')
    (proetaleAbelianBaseChange f g f' g' w)

end BaseChange

end AlgebraicGeometry.ProEtale
