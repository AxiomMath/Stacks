module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian

/-!
# Derived direct and inverse image on abelian sheaves of the small étale site

Let `f : X ⟶ Y` be a morphism of schemes. Direct image `f_*` and inverse image `f⁻¹` on
abelian sheaves for the small étale topology are adjoint, and `f⁻¹` is exact. This file builds
the two functors they induce on the **unbounded** derived categories: the inverse image is
exact, so it is simply applied degreewise, while the direct image has to be derived, and the
derived functor exists because abelian sheaves on the small étale site form a Grothendieck
abelian category, where every unbounded complex has a K-injective resolution. The two derived
functors are again adjoint.

Boundedness is nowhere assumed: the right derived functor is a left Kan extension along the
localization `K(X_étale) ⥤ D(X_étale)` of the whole homotopy category, not the restriction of
such a Kan extension to bounded below complexes.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianPushforwardToDerivedCategory` — direct image on the
  homotopy category of complexes, landing in the derived category of the target.
* `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImage` — the unbounded derived direct image
  `Rf_*`, and `etaleAbelianDerivedDirectImageUnit` its derived-functor unit.
* `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImage` — the inverse image on unbounded
  derived categories, applied degreewise.
* `Stacks.EtaleCohomology.etaleAbelianDerivedAdjunction` — the adjunction `f⁻¹ ⊣ Rf_*` on unbounded
  derived categories.
* `Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso` — the composition isomorphism
  `f_* ⋙ g_* ≅ (f ≫ g)_*` for abelian coefficients.

## Main results

* `Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale` and
  `Stacks.EtaleCohomology.enoughInjectives_sheaf_smallEtale` — abelian sheaves on the
  small étale site form a Grothendieck abelian category and have enough injectives.
* `Stacks.EtaleCohomology.additive_etaleAbelianDirectImage` — direct image is additive.
* `Stacks.EtaleCohomology.etaleAbelianPushforwardToDerivedCategory_hasPointwiseRightDerivedFunctor`
  — the derived direct image exists on the unbounded derived category.
* `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImage_isLeftAdjoint` — the derived inverse
  image is a left adjoint.

## Implementation notes

Coefficients are `AddCommGrpCat.{max (u + 1) v}` for a scheme universe `u` and an arbitrary `v`;
`Ab.{u + 1}` is the case `v = 0`. The small étale site of a scheme in `Scheme.{u}` has its objects
in `Type (u + 1)`, so with this cutoff the coefficient category has the colimits computing the left
Kan extension along base change.

The existence of the unbounded derived direct image and the derived adjunction are instances of
`Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective` and
`Stacks.DerivedFunctor.derivedAdjunction`, applied with the K-injective resolutions of Tag 079P.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- Abelian sheaves on the small étale site of a scheme form a Grothendieck abelian category. -/
public instance isGrothendieckAbelian_sheaf_smallEtale (X : Scheme.{u}) :
    IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`. -/
public theorem isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_smallEtale.{u, u + 1} X

/-- Abelian sheaves on the small étale site of a scheme have enough injectives, being a
Grothendieck abelian category. -/
public instance enoughInjectives_sheaf_smallEtale (X : Scheme.{u}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  inferInstance

/-- Abelian sheaves on the small étale site of a scheme have enough injectives when the
coefficients lie in the universe of the objects of the site. -/
public instance enoughInjectives_sheaf_smallEtale_objectUniverse (X : Scheme.{u}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  enoughInjectives_sheaf_smallEtale.{u, u + 1} X

/-- Direct image on abelian sheaves of the small étale sites is additive. -/
public instance additive_etaleAbelianDirectImage (f : X ⟶ Y) :
    (etaleAbelianDirectImage.{u, v} f).Additive where
  map_add := by intros; rfl

/-- The composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` for direct image of abelian sheaves on
small étale sites. -/
public def etaleAbelianDirectImageCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianDirectImage.{u, v} g ≅
      etaleAbelianDirectImage.{u, v} (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm _ _ _ _

/-- Direct image applied degreewise to unbounded complexes, followed by the localization onto
the derived category of the target. Its right derived functor is `Rf_*`. -/
public abbrev etaleAbelianPushforwardToDerivedCategory (f : X ⟶ Y) :
    HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Direct image on unbounded complexes admits a pointwise right derived functor along the
quasi-isomorphisms. -/
public instance etaleAbelianPushforwardToDerivedCategory_hasPointwiseRightDerivedFunctor
    (f : X ⟶ Y) :
    (etaleAbelianPushforwardToDerivedCategory.{u, v} f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- The unbounded derived direct image `Rf_* : D(X_étale) ⥤ D(Y_étale)` on abelian sheaves of
the small étale sites: the left Kan extension of degreewise direct image along the
localization of the full homotopy category of complexes. -/
public abbrev etaleAbelianDerivedDirectImage (f : X ⟶ Y) :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (etaleAbelianPushforwardToDerivedCategory.{u, v} f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ))

/-- The derived-functor unit comparing degreewise direct image with the unbounded derived
direct image. It is an isomorphism exactly at the K-injective complexes. -/
public abbrev etaleAbelianDerivedDirectImageUnit (f : X ⟶ Y) :
    etaleAbelianPushforwardToDerivedCategory.{u, v} f ⟶
      DerivedCategory.Qh ⋙ etaleAbelianDerivedDirectImage.{u, v} f :=
  (etaleAbelianPushforwardToDerivedCategory.{u, v} f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ))

/-- The inverse image `f⁻¹ : D(Y_étale) ⥤ D(X_étale)` on unbounded derived categories of abelian
sheaves of the small étale sites, applied degreewise. -/
public abbrev etaleAbelianDerivedInverseImage (f : X ⟶ Y) :
    DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (etaleAbelianInverseImage.{u, v} f).mapDerivedCategory

/-- **The derived inverse image is left adjoint to the derived direct image.** -/
public def etaleAbelianDerivedAdjunction (f : X ⟶ Y) :
    etaleAbelianDerivedInverseImage.{u, v} f ⊣ etaleAbelianDerivedDirectImage.{u, v} f :=
  Stacks.DerivedFunctor.derivedAdjunction (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianDerivedDirectImage.{u, v} f) (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- The inverse image on unbounded derived categories of abelian étale sheaves is a left
adjoint, its right adjoint being the derived direct image. -/
public instance etaleAbelianDerivedInverseImage_isLeftAdjoint (f : X ⟶ Y) :
    (etaleAbelianDerivedInverseImage.{u, v} f).IsLeftAdjoint :=
  (etaleAbelianDerivedAdjunction.{u, v} f).isLeftAdjoint

end Stacks.EtaleCohomology

end
