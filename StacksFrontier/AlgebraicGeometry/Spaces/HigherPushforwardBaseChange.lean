module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianInverseImageExact
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianPushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardBaseChange

/-!
# Étale base change for higher direct images of abelian sheaves

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  Stacks 03LR has two conclusions: part (1), for a sheaf of sets `F` on
`X_étale`, direct image commutes with restriction, `f'_{small,*}(F|_{X'}) = (f_{small,*}F)|_{Y'}`;
and part (2), for `F` an abelian sheaf, the same holds for the higher direct images,
`R^i f'_{small,*}(F|_{X'}) = (R^i f_{small,*}F)|_{Y'}`.  Part (1) is
`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso`.  This file proves part (1) for
abelian sheaves, and part (2) under the hypothesis `h03F3` that restriction along `i` carries
injective abelian sheaves to injective abelian sheaves (the injective-preservation half of
Stacks 03F3).  Part (1) for abelian sheaves is deduced from part (1) for sheaves of sets for any
four morphisms of topoi `a, b, c, d` together with a natural isomorphism
`a⁻¹ ⋙ b_* ≅ c_* ⋙ d⁻¹`, and the base change of higher right derived functors is proved as a
general statement of homological algebra.

## Main definitions

* `StacksTag03LR.commGrpBaseChangeIso`: the base-change isomorphism on commutative group
  objects of a topos.
* `StacksTag03LR.abelianBaseChangeIso`: part (1) for abelian sheaves, for any four morphisms of
  topoi together with a natural isomorphism `a⁻¹ ⋙ b_* ≅ c_* ⋙ d⁻¹`.
* `StacksTag03LR.rightDerivedBaseChangeIso` and
  `StacksTag03LR.rightDerivedPlusBaseChangeIso`: base change for higher right derived functors
  across a square of additive functors, in the injective-resolution convention
  `CategoryTheory.Functor.rightDerived` and in the derived-category convention
  `CategoryTheory.Functor.rightDerivedPlus` respectively.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardBaseChangeIso`: part (1) for abelian
  sheaves on the small étale sites of the cartesian square.
* `AlgebraicGeometry.Space.smallEtaleHigherPushforwardBaseChangeIso` and
  `AlgebraicGeometry.Space.smallEtaleHigherPushforwardPlusBaseChangeIso`: Stacks 03LR part (2),
  in the two conventions for `R^n`, under the hypothesis `h03F3`.

## Main results

* `StacksTag03LR.abelianInverseImage_additive`: the inverse image of abelian sheaves along a
  morphism of topoi is additive.

## Implementation notes

These isomorphisms are built from the equality of site functors and are not identified with the
canonical base-change comparison maps; Stacks 03LR part (2) for the canonical comparison is
`AlgebraicGeometry.Space.isIso_smallEtaleAbelianHigherBaseChangeMap`.

Two monoidal structures on `Sheaf J (Type w)` are in scope: the cartesian one, with which
`CategoryTheory.Sites.AbelianSheaf` builds its commutative group objects, and the one inherited
from presheaves by `CategoryTheory.ObjectProperty.fullMonoidalSubcategory`.  Instance search
reaches the latter first, over which `CategoryTheory.Functor.Braided.ofChosenFiniteProducts`
produces no braided structure; the local instance priorities below make search go through the
cartesian structure.

## References

* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory

attribute [local instance 5000]
  CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instCartesianMonoidalCategorySheafType_stacksFrontier

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instBraidedCategorySheafType_stacksFrontier

attribute [local instance] HasDerivedCategory.standard

namespace StacksTag03LR

/-! ### Base change for the direct image of abelian sheaves -/

section Topoi

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ w

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄}
  (a : MorphismOfTopoi (Sheaf J₂ (Type w)) (Sheaf J₁ (Type w)))
  (b : MorphismOfTopoi (Sheaf J₂ (Type w)) (Sheaf J₄ (Type w)))
  (c : MorphismOfTopoi (Sheaf J₁ (Type w)) (Sheaf J₃ (Type w)))
  (d : MorphismOfTopoi (Sheaf J₄ (Type w)) (Sheaf J₃ (Type w)))

/-- The inverse image of abelian sheaves along a morphism of topoi is additive. -/
theorem abelianInverseImage_additive [HasSheafify J₁ AddCommGrpCat.{w}]
    [HasSheafify J₂ AddCommGrpCat.{w}] :
    (CategoryTheory.Sites.abelianInverseImage a).Additive :=
  leftExactFunctor_le_additiveFunctor _ _ (CategoryTheory.Sites.abelianInverseImage a)
    (by rw [leftExactFunctor_iff]; infer_instance)

/-- **Base change on commutative group objects.**  An isomorphism
`a⁻¹ ⋙ b_* ≅ c_* ⋙ d⁻¹` of functors between the topoi of four morphisms of topoi `a, b, c, d`
induces the corresponding isomorphism of functors on commutative group objects.  Nothing here
assumes the four morphisms form a commutative, let alone cartesian, square: the natural
isomorphism is the only link between them. -/
noncomputable def commGrpBaseChangeIso
    (α : a.inverseImage ⋙ b.pushforward ≅ c.pushforward ⋙ d.inverseImage) :
    Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₂ a ⋙
      Stacks.Topos.AbelianInverseImage.commGrpPushforward J₂ b ≅
      Stacks.Topos.AbelianInverseImage.commGrpPushforward J₁ c ⋙
        Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₄ d := by
  letI : PreservesLimitsOfSize.{0, 0} b.pushforward := b.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits b.pushforward := inferInstance
  letI : b.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesLimitsOfSize.{0, 0} c.pushforward := c.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits c.pushforward := inferInstance
  letI : c.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits a.inverseImage := a.preservesFiniteLimits
  letI : a.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits d.inverseImage := d.preservesFiniteLimits
  letI : d.inverseImage.Braided := .ofChosenFiniteProducts _
  exact Functor.mapCommGrpCompIso.symm ≪≫ Functor.mapCommGrpNatIso α ≪≫
    Functor.mapCommGrpCompIso

/-- **Stacks 03LR, part (1), for abelian sheaves, along any square of morphisms of topoi.**  If
the direct image of `b` composed with the inverse image of `a` is the inverse image of `d`
composed with the direct image of `c` on sheaves of sets, then the same holds on abelian
sheaves. -/
noncomputable def abelianBaseChangeIso
    (α : a.inverseImage ⋙ b.pushforward ≅ c.pushforward ⋙ d.inverseImage) :
    CategoryTheory.Sites.abelianInverseImage a ⋙
      Stacks.Topos.AbelianPushforward.abelianPushforward J₂ b ≅
      Stacks.Topos.AbelianPushforward.abelianPushforward J₁ c ⋙
        CategoryTheory.Sites.abelianInverseImage d :=
  let E₁ : CommGrp (Sheaf J₁ (Type w)) ≌ Sheaf J₁ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₁).symm
  let E₂ : CommGrp (Sheaf J₂ (Type w)) ≌ Sheaf J₂ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₂).symm
  let E₃ : CommGrp (Sheaf J₃ (Type w)) ≌ Sheaf J₃ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₃).symm
  let E₄ : CommGrp (Sheaf J₄ (Type w)) ≌ Sheaf J₄ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₄).symm
  Equivalence.conjugateCompIso E₁ E₂ E₄ (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₂ a)
      (Stacks.Topos.AbelianInverseImage.commGrpPushforward J₂ b) ≪≫
    Functor.isoWhiskerLeft E₁.inverse
      (Functor.isoWhiskerRight (commGrpBaseChangeIso a b c d α) E₄.functor) ≪≫
    (Equivalence.conjugateCompIso E₁ E₃ E₄
      (Stacks.Topos.AbelianInverseImage.commGrpPushforward J₁ c)
      (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₄ d)).symm

end Topoi

/-! ### Base change for higher right derived functors -/

section Derived

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {A' : Type u₂} [Category.{v₂} A'] [Abelian A']
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']

/-- **Base change for higher right derived functors, injective-resolution convention.**  Let

```
A --R--> A'
|F       |F'
D --R'-> D'
```

be a square of additive functors between abelian categories with injective resolutions, with
`R` and `R'` exact and `R` moreover carrying injective objects to injective objects, and let
`α : R ⋙ F' ≅ F ⋙ R'`.  Then `R ⋙ R^n F' ≅ R^n F ⋙ R'` for every `n`, naturally. -/
noncomputable def rightDerivedBaseChangeIso [HasInjectiveResolutions A]
    [HasInjectiveResolutions A'] (R : A ⥤ A') [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [R.PreservesInjectiveObjects] (F : A ⥤ D) [F.Additive]
    (F' : A' ⥤ D') [F'.Additive] (R' : D ⥤ D') [R'.Additive] [PreservesFiniteLimits R']
    [PreservesFiniteColimits R'] (α : R ⋙ F' ≅ F ⋙ R') (n : ℕ) :
    R ⋙ F'.rightDerived n ≅ F.rightDerived n ⋙ R' :=
  letI : R'.PreservesHomology := Functor.preservesHomologyOfExact R'
  (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso R F' n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso α n ≪≫ Functor.rightDerivedCompIso F R' n

/-- **Base change for higher right derived functors, derived-category convention.**  The same
statement as `StacksTag03LR.rightDerivedBaseChangeIso` for
`CategoryTheory.Functor.rightDerivedPlus`, the convention of Stacks 05U4 in which the higher
direct images of Stacks 0A4K are stated. -/
noncomputable def rightDerivedPlusBaseChangeIso [HasInjectiveResolutions A]
    [HasInjectiveResolutions A'] [EnoughInjectives A] [EnoughInjectives A']
    [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory D] [HasDerivedCategory D']
    (R : A ⥤ A') [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [R.PreservesInjectiveObjects] (F : A ⥤ D) [F.Additive] (F' : A' ⥤ D') [F'.Additive]
    (R' : D ⥤ D') [R'.Additive] [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (α : R ⋙ F' ≅ F ⋙ R') (n : ℕ) :
    R ⋙ F'.rightDerivedPlus (n : ℤ) ≅ F.rightDerivedPlus (n : ℤ) ⋙ R' :=
  Functor.isoWhiskerLeft R
      (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard F' n) ≪≫
    rightDerivedBaseChangeIso R F F' R' α n ≪≫
    Functor.isoWhiskerRight
      (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard F n).symm R'

end Derived

end StacksTag03LR

/-! ### The cartesian square of algebraic spaces -/

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **Stacks 03LR, part (1), for abelian sheaves.**  For a cartesian square of algebraic spaces
whose bottom arrow `g` is étale, direct image of *abelian* sheaves on the small étale sites
commutes with restriction: `f'_{small,*}(F|_{X'}) = (f_{small,*}F)|_{Y'}`, naturally in the
abelian sheaf `F`. -/
noncomputable def smallEtaleAbelianPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    CategoryTheory.Sites.abelianInverseImage (smallToposMorphism B S hS i) ⋙
        Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X'.obj)
          (smallToposMorphism B S hS f') ≅
      Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
          (smallToposMorphism B S hS f) ⋙
        CategoryTheory.Sites.abelianInverseImage (smallToposMorphism B S hS g) :=
  StacksTag03LR.abelianBaseChangeIso _ _ _ _
    (smallEtalePushforwardBaseChangeIso B S hS i f' f g sq hg)

/-- **Stacks 03LR, part (2)**, in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, with the injective-preservation half of Stacks 03F3
carried as the explicit hypothesis `h03F3`.

For a cartesian square of algebraic spaces whose bottom arrow `g` is étale, the higher direct
images of abelian sheaves on the small étale sites commute with restriction:
`R^n f'_{small,*}(F|_{X'}) = (R^n f_{small,*}F)|_{Y'}` for every `n`, naturally in the abelian
sheaf `F` — *given* that restriction along `i` carries injective abelian sheaves to injective
abelian sheaves. -/
noncomputable def smallEtaleHigherPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (h03F3 : (CategoryTheory.Sites.abelianInverseImage
      (smallToposMorphism B S hS i)).PreservesInjectiveObjects) (n : ℕ) :
    CategoryTheory.Sites.abelianInverseImage (smallToposMorphism B S hS i) ⋙
        (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X'.obj)
          (smallToposMorphism B S hS f')).rightDerived n ≅
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
          (smallToposMorphism B S hS f)).rightDerived n ⋙
        CategoryTheory.Sites.abelianInverseImage (smallToposMorphism B S hS g) :=
  haveI := h03F3
  haveI := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS i)
  haveI := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS g)
  StacksTag03LR.rightDerivedBaseChangeIso _ _ _ _
    (smallEtaleAbelianPushforwardBaseChangeIso B S hS i f' f g sq hg) n

/-- **Stacks 03LR, part (2)**, in the derived-category convention
`CategoryTheory.Functor.rightDerivedPlus` used by Stacks 0A4K in
`StacksFrontier.AlgebraicGeometry.Spaces.AbelianPushforwardExact`, with the same explicit
hypothesis `h03F3` as `AlgebraicGeometry.Space.smallEtaleHigherPushforwardBaseChangeIso`. -/
noncomputable def smallEtaleHigherPushforwardPlusBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (h03F3 : (CategoryTheory.Sites.abelianInverseImage
      (smallToposMorphism B S hS i)).PreservesInjectiveObjects) (n : ℕ) :
    CategoryTheory.Sites.abelianInverseImage (smallToposMorphism B S hS i) ⋙
        (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X'.obj)
          (smallToposMorphism B S hS f')).rightDerivedPlus (n : ℤ) ≅
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
          (smallToposMorphism B S hS f)).rightDerivedPlus (n : ℤ) ⋙
        CategoryTheory.Sites.abelianInverseImage (smallToposMorphism B S hS g) :=
  haveI := h03F3
  haveI := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS i)
  haveI := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS g)
  StacksTag03LR.rightDerivedPlusBaseChangeIso _ _ _ _
    (smallEtaleAbelianPushforwardBaseChangeIso B S hS i f' f g sq hg) n

end AlgebraicGeometry.Space

end
