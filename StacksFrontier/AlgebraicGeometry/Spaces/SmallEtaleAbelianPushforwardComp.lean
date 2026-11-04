module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# The direct image of abelian sheaves across a commutative square

Let

```
W --i'--> Y
|f'       |f
Z --i---> X
```

be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`.
Composing direct images along the two sides gives two functors from the abelian sheaves on the
small étale site of `W` to those on the small étale site of `X`, and this file identifies them:
`i'_* ⋙ f_* ≅ f'_* ⋙ i_*`.

The content is the compatibility of the small étale direct image with composition, which is
Stacks 03G2, part (3), `AlgebraicGeometry.Space.smallToposMorphism_comp`, at sheaves of sets;
the passage to abelian coefficients is the pseudofunctoriality of
`CategoryTheory.Functor.mapCommGrp`, exactly as in
`StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange` for base change.

## Main definitions

* `Stacks.Topos.AbelianPushforward.commGrpPushforwardSquareIso` and
  `Stacks.Topos.AbelianPushforward.abelianPushforwardSquareIso` transport an isomorphism
  `p_* ⋙ q_* ≅ r_* ⋙ s_*` of direct images of sheaves of sets along four morphisms of topoi to
  commutative group objects and to abelian sheaves. No square is assumed to commute: the
  isomorphism is the only link between the four morphisms.
* `AlgebraicGeometry.Space.smallEtalePushforwardCommSquareIso` is the isomorphism
  `i'_* ⋙ f_* ≅ f'_* ⋙ i_*` of direct images of sheaves of sets on the small étale sites of a
  commutative square of algebraic spaces.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardCommSquareIso` is the same isomorphism
  for abelian sheaves.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardCompIso` and
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardSiteCommSquareIso` are the composition
  isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` and its commutative-square form for the direct image of
  abelian sheaves `AlgebraicGeometry.Space.smallEtaleAbelianPushforward`. They go through the
  comparison equivalences of Stacks 03G1 at abelian coefficients,
  `AlgebraicGeometry.Space.smallEtaleAbelianSheafComparisonEquiv`, where the statement is
  Stacks 03G2, part (2).

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory

attribute [local instance 5000]
  CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instCartesianMonoidalCategorySheafType_stacksFrontier

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instBraidedCategorySheafType_stacksFrontier

namespace Stacks.Topos.AbelianPushforward

open Stacks.Topos.AbelianInverseImage

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ w

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄}
  (p : MorphismOfTopoi (Sheaf J₁ (Type w)) (Sheaf J₂ (Type w)))
  (q : MorphismOfTopoi (Sheaf J₂ (Type w)) (Sheaf J₃ (Type w)))
  (r : MorphismOfTopoi (Sheaf J₁ (Type w)) (Sheaf J₄ (Type w)))
  (s : MorphismOfTopoi (Sheaf J₄ (Type w)) (Sheaf J₃ (Type w)))

/-- **A square of direct images on commutative group objects.** An isomorphism
`p_* ⋙ q_* ≅ r_* ⋙ s_*` of functors between the topoi of four morphisms of topoi induces the
corresponding isomorphism of functors on commutative group objects.

All four functors on group objects are `CategoryTheory.Functor.mapCommGrp` of a
finite-product-preserving functor of topoi, so this is the pseudofunctoriality of `mapCommGrp`:
`CategoryTheory.Functor.mapCommGrpCompIso` twice and
`CategoryTheory.Functor.mapCommGrpNatIso` once. -/
def commGrpPushforwardSquareIso
    (α : p.pushforward ⋙ q.pushforward ≅ r.pushforward ⋙ s.pushforward) :
    commGrpPushforward J₁ p ⋙ commGrpPushforward J₂ q ≅
      commGrpPushforward J₁ r ⋙ commGrpPushforward J₄ s := by
  letI : PreservesLimitsOfSize.{0, 0} p.pushforward := p.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits p.pushforward := inferInstance
  letI : p.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesLimitsOfSize.{0, 0} q.pushforward := q.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits q.pushforward := inferInstance
  letI : q.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesLimitsOfSize.{0, 0} r.pushforward := r.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits r.pushforward := inferInstance
  letI : r.pushforward.Braided := .ofChosenFiniteProducts _
  letI : PreservesLimitsOfSize.{0, 0} s.pushforward := s.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits s.pushforward := inferInstance
  letI : s.pushforward.Braided := .ofChosenFiniteProducts _
  exact Functor.mapCommGrpCompIso.symm ≪≫ Functor.mapCommGrpNatIso α ≪≫
    Functor.mapCommGrpCompIso

/-- **A square of direct images of abelian sheaves.** If the composite of the direct images of
`p` and `q` agrees with that of `r` and `s` on sheaves of sets, then it does so on abelian
sheaves.

Each of the four functors on abelian sheaves is the conjugate, by the identification
`CategoryTheory.Sites.AbelianSheaf.equivalence` of abelian sheaves with commutative
group objects, of the corresponding functor on group objects, where the statement is
`Stacks.Topos.AbelianPushforward.commGrpPushforwardSquareIso`;
`CategoryTheory.Equivalence.conjugateCompIso` collapses the composites of conjugates to the
conjugates of the composites. -/
def abelianPushforwardSquareIso
    (α : p.pushforward ⋙ q.pushforward ≅ r.pushforward ⋙ s.pushforward) :
    abelianPushforward J₁ p ⋙ abelianPushforward J₂ q ≅
      abelianPushforward J₁ r ⋙ abelianPushforward J₄ s :=
  let E₁ : CommGrp (Sheaf J₁ (Type w)) ≌ Sheaf J₁ AddCommGrpCat.{w} :=
    (Sites.AbelianSheaf.equivalence J₁).symm
  let E₂ : CommGrp (Sheaf J₂ (Type w)) ≌ Sheaf J₂ AddCommGrpCat.{w} :=
    (Sites.AbelianSheaf.equivalence J₂).symm
  let E₃ : CommGrp (Sheaf J₃ (Type w)) ≌ Sheaf J₃ AddCommGrpCat.{w} :=
    (Sites.AbelianSheaf.equivalence J₃).symm
  let E₄ : CommGrp (Sheaf J₄ (Type w)) ≌ Sheaf J₄ AddCommGrpCat.{w} :=
    (Sites.AbelianSheaf.equivalence J₄).symm
  Equivalence.conjugateCompIso E₁ E₂ E₃ (commGrpPushforward J₁ p) (commGrpPushforward J₂ q) ≪≫
    Functor.isoWhiskerLeft E₁.inverse
      (Functor.isoWhiskerRight (commGrpPushforwardSquareIso p q r s α) E₃.functor) ≪≫
    (Equivalence.conjugateCompIso E₁ E₄ E₃ (commGrpPushforward J₁ r)
      (commGrpPushforward J₄ s)).symm

end Stacks.Topos.AbelianPushforward

/-! ### The commutative square of algebraic spaces -/

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W Y Z X : AlgebraicSpaces B S hS}

/-- **The small étale direct image of sheaves of sets across a commutative square.** For a
commutative square `i' ≫ f = f' ≫ i` of algebraic spaces over `S`, the composites
`i'_* ⋙ f_*` and `f'_* ⋙ i_*` of the direct images of Stacks 03G2, part (3) agree.

This is the compatibility of the direct image with composition, Stacks 03G2, part (3), applied
to the two factorizations of the diagonal of the square. -/
def smallEtalePushforwardCommSquareIso (i' : W ⟶ Y) (f' : W ⟶ Z) (f : Y ⟶ X) (i : Z ⟶ X)
    (h : i' ≫ f = f' ≫ i) :
    (smallToposMorphism B S hS i').pushforward ⋙ (smallToposMorphism B S hS f).pushforward ≅
      (smallToposMorphism B S hS f').pushforward ⋙ (smallToposMorphism B S hS i).pushforward :=
  smallToposMorphism_comp B S hS i' f ≪≫ eqToIso (by rw [h]) ≪≫
    (smallToposMorphism_comp B S hS f' i).symm

/-- **The small étale direct image of abelian sheaves across a commutative square.** For a
commutative square `i' ≫ f = f' ≫ i` of algebraic spaces over `S`, the composites
`i'_* ⋙ f_*` and `f'_* ⋙ i_*` of the direct images of abelian sheaves on the small étale sites
agree.

It is `Stacks.Topos.AbelianPushforward.abelianPushforwardSquareIso` applied to the statement for
sheaves of sets, `AlgebraicGeometry.Space.smallEtalePushforwardCommSquareIso`. -/
def smallEtaleAbelianPushforwardCommSquareIso (i' : W ⟶ Y) (f' : W ⟶ Z) (f : Y ⟶ X) (i : Z ⟶ X)
    (h : i' ≫ f = f' ≫ i) :
    Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS W.obj)
          (smallToposMorphism B S hS i') ⋙
        Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS Y.obj)
          (smallToposMorphism B S hS f) ≅
      Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS W.obj)
          (smallToposMorphism B S hS f') ⋙
        Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS Z.obj)
          (smallToposMorphism B S hS i) :=
  Stacks.Topos.AbelianPushforward.abelianPushforwardSquareIso _ _ _ _
    (smallEtalePushforwardCommSquareIso B S hS i' f' f i h)

/-! ### The site-level direct image of abelian sheaves -/

/-- The comparison equivalence of Stacks 03G1 at abelian coefficients: abelian sheaves on the
spaces-étale site of an algebraic space are abelian sheaves on its small étale site, by
restriction along the inclusion of the small étale site as a dense subsite. -/
def smallEtaleAbelianSheafComparisonEquiv (X : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1} ≌
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  ((comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).asEquivalence

/-- **Stacks 03G2, part (2), for the direct image of abelian sheaves on the spaces-étale
sites.** Restriction along base change of étale algebraic spaces is compatible with
composition. -/
def spacesBaseChangeAbelianPushforwardComp (f : W ⟶ Y) (g : Y ⟶ X) :
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS W) ⋙
      (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ≅
      (spacesBaseChange B S hS (f ≫ g)).functor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SpacesEtale.topology B S hS X)
        (SpacesEtale.topology B S hS W) :=
  Functor.sheafPushforwardContinuousComp' (spacesBaseChange_comp B S hS f g)
    AddCommGrpCat.{u + 1} (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS W)

/-- The small étale direct image of abelian sheaves is the conjugate, by the comparison
equivalences of Stacks 03G1, of the spaces-étale one. This is
`AlgebraicGeometry.Space.smallBaseChangePushforwardComparison` with the comparison on the source
side cancelled. -/
def smallEtaleAbelianPushforwardConjIso (f : W ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallEtaleAbelianPushforward.{u + 1} B S hS f hf ≅
      (smallEtaleAbelianSheafComparisonEquiv B S hS W).inverse ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS W) ⋙
        (smallEtaleAbelianSheafComparisonEquiv B S hS Y).functor :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleAbelianSheafComparisonEquiv B S hS W).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleAbelianSheafComparisonEquiv B S hS W).inverse
      (smallBaseChangePushforwardComparison B S hS f hf AddCommGrpCat.{u + 1})

/-- **The small étale direct image of abelian sheaves is compatible with composition.** For
morphisms `f : W ⟶ Y` and `g : Y ⟶ X` of algebraic spaces over `S` with representable
underlying morphisms, `f_* ⋙ g_* ≅ (f ≫ g)_*` on abelian sheaves of the small étale sites.

Both sides are conjugates of the spaces-étale direct images by the comparison equivalences of
Stacks 03G1, where the statement is Stacks 03G2, part (2); the two copies of the middle
equivalence cancel by `CategoryTheory.Equivalence.conjugateCompIso`. -/
def smallEtaleAbelianPushforwardCompIso (f : W ⟶ Y) (g : Y ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    smallEtaleAbelianPushforward.{u + 1} B S hS f hf ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS g hg ≅
      smallEtaleAbelianPushforward.{u + 1} B S hS (f ≫ g) hfg :=
  Functor.isoWhiskerRight (smallEtaleAbelianPushforwardConjIso B S hS f hf) _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleAbelianPushforwardConjIso B S hS g hg) ≪≫
    Equivalence.conjugateCompIso (smallEtaleAbelianSheafComparisonEquiv B S hS W)
      (smallEtaleAbelianSheafComparisonEquiv B S hS Y)
      (smallEtaleAbelianSheafComparisonEquiv B S hS X) _ _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleAbelianSheafComparisonEquiv B S hS W).inverse
      (Functor.isoWhiskerRight (spacesBaseChangeAbelianPushforwardComp B S hS f g) _) ≪≫
    (smallEtaleAbelianPushforwardConjIso B S hS (f ≫ g) hfg).symm

/-- **The small étale direct image of abelian sheaves is compatible with composition**, stated
for a morphism `d` together with a factorization `f ≫ g = d`. This is
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardCompIso` in the form that composes two
factorizations of one morphism. -/
def smallEtaleAbelianPushforwardCompIsoOfEq (f : W ⟶ Y) (g : Y ⟶ X) (d : W ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hd : yoneda.relativelyRepresentable d.hom) (he : f ≫ g = d) :
    smallEtaleAbelianPushforward.{u + 1} B S hS f hf ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS g hg ≅
      smallEtaleAbelianPushforward.{u + 1} B S hS d hd := by
  subst he
  exact smallEtaleAbelianPushforwardCompIso B S hS f g hf hg hd

/-- **The small étale direct image of abelian sheaves across a commutative square, at the site
level.** For a commutative square whose two diagonals are both the morphism `d` — that is,
`i' ≫ f = d = f' ≫ i` — and whose sides have representable underlying morphisms,
`i'_* ⋙ f_* ≅ f'_* ⋙ i_*` on abelian sheaves of the small étale sites.

This is the version of `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardCommSquareIso` for
the direct image `AlgebraicGeometry.Space.smallEtaleAbelianPushforward`. -/
def smallEtaleAbelianPushforwardSiteCommSquareIso {V : AlgebraicSpaces B S hS} (i' : V ⟶ W)
    (f' : V ⟶ Y) (f : W ⟶ X) (i : Y ⟶ X) (d : V ⟶ X)
    (hi' : yoneda.relativelyRepresentable i'.hom)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hf' : yoneda.relativelyRepresentable f'.hom)
    (hi : yoneda.relativelyRepresentable i.hom)
    (hd : yoneda.relativelyRepresentable d.hom)
    (h₁ : i' ≫ f = d) (h₂ : f' ≫ i = d) :
    smallEtaleAbelianPushforward.{u + 1} B S hS i' hi' ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS f hf ≅
      smallEtaleAbelianPushforward.{u + 1} B S hS f' hf' ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS i hi :=
  smallEtaleAbelianPushforwardCompIsoOfEq B S hS i' f d hi' hf hd h₁ ≪≫
    (smallEtaleAbelianPushforwardCompIsoOfEq B S hS f' i d hf' hi hd h₂).symm

end AlgebraicGeometry.Space

end
