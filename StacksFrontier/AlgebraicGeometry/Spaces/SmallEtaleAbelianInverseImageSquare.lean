module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocalHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianRestrictionInverseImage

/-!
# The inverse-image square at abelian coefficients, and Stacks 0A4P's sheaf identity on `Z`

Stacks 03LR has a parenthetical assertion alongside its two parts — "Also
`(f')^{-1}_{small}(G|_{Y'}) = (f_{small}^{-1}G)|_{X'}` because of commutativity of the diagram
and (03LQ)" — which for sheaves of sets is
`AlgebraicGeometry.Space.smallEtaleInverseImageSquareIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePushforwardBaseChange.lean`.  This file proves
it for abelian sheaves, and uses it to move the Stacks 0A4P comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupportEtaleLocalHigher.lean` across the two
closed immersions.  That delivers the first conclusion of Stacks 0A4P in the source's own
reading — the sheaf identity on `Z` rather than on the ambient small étale site — both without
the source's hypothesis that `f⁻¹Z ⟶ Z` is an isomorphism, as an identity of abelian sheaves on
`f⁻¹Z`, and with it, as an identity of abelian sheaves on `Z`.

## Main definitions

* `StacksTag03LR.commGrpInverseImageSquareIso` and
  `StacksTag03LR.abelianInverseImageSquareIso`: an isomorphism `a⁻¹ ⋙ b⁻¹ ≅ c⁻¹ ⋙ d⁻¹` of
  functors between the topoi of four morphisms of topoi `a, b, c, d` induces the corresponding
  isomorphism on commutative group objects, and hence on abelian sheaves.  No square is assumed
  to commute, let alone to be cartesian: the natural isomorphism is the only link between the
  four morphisms.  This is the inverse-image/inverse-image analogue of
  `StacksTag03LR.commGrpBaseChangeIso` and `StacksTag03LR.abelianBaseChangeIso`.
* `AlgebraicGeometry.Space.smallEtaleInverseImageSquareIsoOfComm` and
  `AlgebraicGeometry.Space.smallEtaleAbelianInverseImageSquareIsoOfComm`: the square
  identification from commutativity alone, for sheaves of sets and for abelian sheaves.
* `AlgebraicGeometry.Space.smallEtaleAbelianInverseImageSquareIso`: **Stacks 03LR's
  inverse-image footnote, at abelian coefficients.**
* `StacksTag03LR.abelianInverseImageCompIso` and
  `AlgebraicGeometry.Space.smallToposMorphism_comp_abelianInverseImage`: the inverse image of
  abelian sheaves is compatible with composition, in general and for the morphisms of small
  étale topoi, the latter being **Stacks 03G2, part (3) at abelian coefficients.**

## Main results

* `AlgebraicGeometry.Space.closedHigherSectionsWithSupportOnSubspaceIso`: **Stacks 0A4P in every
  degree, read on the subspaces.**  For an étale `f : X ⟶ Y`, a subspace `iY : Z ⟶ Y` and its
  inverse image `iX : W ⟶ X` presented by the cartesian square with `k : W ⟶ Z`,
  `k⁻¹(H^q_Z(F)|_Z) = H^q_{f⁻¹Z}(f⁻¹F)|_{f⁻¹Z}` as abelian sheaves on `W = f⁻¹Z`, naturally in
  `F` and in every degree.  Nothing is assumed about `k`.
* `AlgebraicGeometry.Space.closedHigherSectionsWithSupportOnZIso`: **Stacks 0A4P in every
  degree, on `Z` itself**, with the source's hypothesis that `k` is an isomorphism:
  `H^q_Z(F)|_Z = H^q_{f⁻¹Z}(f⁻¹F)|_{f⁻¹Z}` as abelian sheaves on `Z`, the right-hand side read
  on `Z` through `k`.  This is the reading the source states.

## Implementation notes

The general isomorphism is the pseudofunctoriality of `CategoryTheory.Functor.mapCommGrp`, as
for the direct-image version in
`StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardBaseChange.lean`:
`CategoryTheory.Functor.mapCommGrpCompIso` twice and
`CategoryTheory.Functor.mapCommGrpNatIso` once, then
`CategoryTheory.Equivalence.conjugateCompIso` to collapse the composites of conjugates by
`CategoryTheory.Sites.AbelianSheaf.equivalence` into the conjugates of the composites.  All four
functors are inverse images, so all four are left exact by the definition of a morphism of
topoi and no adjoint has to be produced; the direct-image version needs the right adjoints'
preservation of limits for two of its four.

The `OfComm` variants exist because the proof of the footnote uses only commutativity of the
square — it is the composition isomorphism of Stacks 03G2, part (3) applied twice around
`i ≫ f = f' ≫ g` — and because that is what the consumer here can supply: the cartesian square
of Stacks 0A4P is an `CategoryTheory.IsPullback` of the *underlying presheaf morphisms*, not of
morphisms of `AlgebraicGeometry.Space.AlgebraicSpaces`, so its `w` field gives commutativity in
the full subcategory by `CategoryTheory.ObjectProperty.hom_ext` but not a pullback square there.
The `IsPullback` form is kept as the faithful reading of the footnote and is the one that
carries the attribute.

What `closedHigherSectionsWithSupportOnSubspaceIso` adds to the ambient-site statement is one
whiskering by inverse image along the closed immersion `iX`, after which abelian Stacks 03LQ
(`AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImageIso`) turns restriction along
postcomposition into the topos-theoretic inverse image and the abelian footnote exchanges the
two routes around the square.  The source's hypothesis that `k` is an isomorphism is *not*
assumed, exactly as in the two ambient-site statements; under it the left-hand side is the
source's `H^q_Z(F)` read on `Z`, so this is the source's identity with its hypothesis removed.

`closedHigherSectionsWithSupportOnZIso` then puts the source's hypothesis back in and cancels
`k`.  It needs *no unit law* for `AlgebraicGeometry.Space.smallToposMorphism`: two applications
of `smallToposMorphism_comp_abelianInverseImage` suffice, one at `inv k ≫ k = 𝟙 Z`, turning the
composite `k⁻¹ ⋙ (inv k)⁻¹` into the inverse image along `𝟙 Z`, and one at `𝟙 Z ≫ iY = iY`,
absorbing that into the inverse image along `iY`.  So the inverse image along an identity is
never compared with the identity functor, and `smallToposMorphism (𝟙 X) ≅ MorphismOfTopoi.id`
— which the library does not have — is not needed.  Both statements are kept: the one on
`f⁻¹Z` assumes nothing about `k` and is strictly stronger, the one on `Z` is the source's
reading.

## References

* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
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

/-! ### The inverse-image square on group objects and on abelian sheaves -/

namespace StacksTag03LR

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ w

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄}
  (a : MorphismOfTopoi (Sheaf J₂ (Type w)) (Sheaf J₁ (Type w)))
  (b : MorphismOfTopoi (Sheaf J₄ (Type w)) (Sheaf J₂ (Type w)))
  (c : MorphismOfTopoi (Sheaf J₃ (Type w)) (Sheaf J₁ (Type w)))
  (d : MorphismOfTopoi (Sheaf J₄ (Type w)) (Sheaf J₃ (Type w)))

/-- **The inverse-image square on commutative group objects.**  An isomorphism
`a⁻¹ ⋙ b⁻¹ ≅ c⁻¹ ⋙ d⁻¹` of functors between the topoi of four morphisms of topoi `a, b, c, d`
induces the corresponding isomorphism of functors on commutative group objects.  Nothing here
assumes the four morphisms form a commutative, let alone cartesian, square: the natural
isomorphism is the only link between them.

All four functors on group objects are `CategoryTheory.Functor.mapCommGrp` of the inverse image
of a morphism of topoi, which is left exact by definition, so this is the pseudofunctoriality of
`mapCommGrp`: `CategoryTheory.Functor.mapCommGrpCompIso` twice and
`CategoryTheory.Functor.mapCommGrpNatIso` once. -/
def commGrpInverseImageSquareIso
    (α : a.inverseImage ⋙ b.inverseImage ≅ c.inverseImage ⋙ d.inverseImage) :
    Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₂ a ⋙
      Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₄ b ≅
      Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₃ c ⋙
        Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₄ d := by
  letI : PreservesFiniteLimits a.inverseImage := a.preservesFiniteLimits
  letI : a.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits b.inverseImage := b.preservesFiniteLimits
  letI : b.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits c.inverseImage := c.preservesFiniteLimits
  letI : c.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits d.inverseImage := d.preservesFiniteLimits
  letI : d.inverseImage.Braided := .ofChosenFiniteProducts _
  exact Functor.mapCommGrpCompIso.symm ≪≫ Functor.mapCommGrpNatIso α ≪≫
    Functor.mapCommGrpCompIso

/-- **The inverse-image square on abelian sheaves.**  If the inverse image of `b` composed with
the inverse image of `a` is the inverse image of `d` composed with the inverse image of `c` on
sheaves of sets, then the same holds on abelian sheaves.

Each of the four functors on abelian sheaves is the conjugate, by the identification
`CategoryTheory.Sites.AbelianSheaf.equivalence` of abelian sheaves with commutative group
objects, of the corresponding functor on group objects, where the statement is
`StacksTag03LR.commGrpInverseImageSquareIso`; `CategoryTheory.Equivalence.conjugateCompIso`
collapses the composites of conjugates to the conjugates of the composites. -/
def abelianInverseImageSquareIso
    (α : a.inverseImage ⋙ b.inverseImage ≅ c.inverseImage ⋙ d.inverseImage) :
    CategoryTheory.Sites.abelianInverseImage a ⋙
      CategoryTheory.Sites.abelianInverseImage b ≅
      CategoryTheory.Sites.abelianInverseImage c ⋙
        CategoryTheory.Sites.abelianInverseImage d :=
  let E₁ : CommGrp (Sheaf J₁ (Type w)) ≌ Sheaf J₁ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₁).symm
  let E₂ : CommGrp (Sheaf J₂ (Type w)) ≌ Sheaf J₂ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₂).symm
  let E₃ : CommGrp (Sheaf J₃ (Type w)) ≌ Sheaf J₃ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₃).symm
  let E₄ : CommGrp (Sheaf J₄ (Type w)) ≌ Sheaf J₄ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₄).symm
  Equivalence.conjugateCompIso E₁ E₂ E₄
      (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₂ a)
      (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₄ b) ≪≫
    Functor.isoWhiskerLeft E₁.inverse
      (Functor.isoWhiskerRight (commGrpInverseImageSquareIso a b c d α) E₄.functor) ≪≫
    (Equivalence.conjugateCompIso E₁ E₃ E₄
      (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₃ c)
      (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₄ d)).symm

section Comp

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  (a : MorphismOfTopoi (Sheaf J₂ (Type w)) (Sheaf J₁ (Type w)))
  (b : MorphismOfTopoi (Sheaf J₃ (Type w)) (Sheaf J₂ (Type w)))
  (e : MorphismOfTopoi (Sheaf J₃ (Type w)) (Sheaf J₁ (Type w)))

/-- **The inverse image of abelian sheaves is compatible with composition.**  If the inverse
image of `e` is the inverse image of `a` followed by that of `b` on sheaves of sets, then the
same holds on abelian sheaves.

As for `StacksTag03LR.abelianInverseImageSquareIso`, the composite is not assumed to *be* a
composite of morphisms of topoi: the natural isomorphism `α` is the only link, which is what
lets the consumers feed it the composition isomorphism of Stacks 03G2, part (3) rather than a
definitional equality.  The proof is `CategoryTheory.Functor.mapCommGrpNatIso` followed by
`CategoryTheory.Functor.mapCommGrpCompIso`, and then
`CategoryTheory.Equivalence.conjugateCompIso` to split the conjugate of the composite into the
composite of the conjugates. -/
def abelianInverseImageCompIso
    (α : e.inverseImage ≅ a.inverseImage ⋙ b.inverseImage) :
    CategoryTheory.Sites.abelianInverseImage e ≅
      CategoryTheory.Sites.abelianInverseImage a ⋙
        CategoryTheory.Sites.abelianInverseImage b := by
  letI : PreservesFiniteLimits a.inverseImage := a.preservesFiniteLimits
  letI : a.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits b.inverseImage := b.preservesFiniteLimits
  letI : b.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits e.inverseImage := e.preservesFiniteLimits
  letI : e.inverseImage.Braided := .ofChosenFiniteProducts _
  let E₁ : CommGrp (Sheaf J₁ (Type w)) ≌ Sheaf J₁ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₁).symm
  let E₂ : CommGrp (Sheaf J₂ (Type w)) ≌ Sheaf J₂ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₂).symm
  let E₃ : CommGrp (Sheaf J₃ (Type w)) ≌ Sheaf J₃ AddCommGrpCat.{w} :=
    (CategoryTheory.Sites.AbelianSheaf.equivalence J₃).symm
  exact Functor.isoWhiskerLeft E₁.inverse
      (Functor.isoWhiskerRight
        (Functor.mapCommGrpNatIso α ≪≫ Functor.mapCommGrpCompIso) E₃.functor) ≪≫
    (Equivalence.conjugateCompIso E₁ E₂ E₃
      (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₂ a)
      (Stacks.Topos.AbelianInverseImage.commGrpInverseImage J₃ b)).symm

end Comp

end StacksTag03LR

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The abelian inverse image is compatible with composition -/

section Composition

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 03G2, part (3), inverse-image composition, at abelian coefficients:**
`(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` for the inverse image of *abelian* sheaves along the morphisms of small
étale topoi.

It is `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage`, the same statement for
sheaves of sets, carried over by `StacksTag03LR.abelianInverseImageCompIso`. -/
@[stacks 03G2 "part (3), inverse-image composition at abelian coefficients"]
def smallToposMorphism_comp_abelianInverseImage (f : X ⟶ Y) (g : Y ⟶ Z) :
    Sites.abelianInverseImage (smallToposMorphism B S hS (f ≫ g)) ≅
      Sites.abelianInverseImage (smallToposMorphism B S hS g) ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS f) :=
  StacksTag03LR.abelianInverseImageCompIso _ _ _
    (smallToposMorphism_comp_inverseImage B S hS f g)

end Composition

/-! ### Stacks 03LR's inverse-image footnote at abelian coefficients -/

section Square

variable {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y)

/-- The inverse-image identification around a *commutative* square of algebraic spaces, for
sheaves of sets.

This is `AlgebraicGeometry.Space.smallEtaleInverseImageSquareIso` with its hypothesis weakened
from cartesian to commutative, which is all its proof uses: the two routes around the square
are compared by the inverse-image composition isomorphism of Stacks 03G2, part (3) applied at
`f' ≫ g` and at `i ≫ f`, which the hypothesis identifies. -/
def smallEtaleInverseImageSquareIsoOfComm (hw : i ≫ f = f' ≫ g) :
    (smallToposMorphism B S hS g).inverseImage ⋙
        (smallToposMorphism B S hS f').inverseImage ≅
      (smallToposMorphism B S hS f).inverseImage ⋙
        (smallToposMorphism B S hS i).inverseImage :=
  (smallToposMorphism_comp_inverseImage B S hS f' g).symm ≪≫
    eqToIso ((congrArg
      (fun h : X' ⟶ Y => (smallToposMorphism B S hS h).inverseImage) hw).symm) ≪≫
    smallToposMorphism_comp_inverseImage B S hS i f

/-- The inverse-image identification around a commutative square of algebraic spaces, for
*abelian* sheaves.

It is `AlgebraicGeometry.Space.smallEtaleInverseImageSquareIsoOfComm` carried to abelian
coefficients by `StacksTag03LR.abelianInverseImageSquareIso`. -/
def smallEtaleAbelianInverseImageSquareIsoOfComm (hw : i ≫ f = f' ≫ g) :
    Sites.abelianInverseImage (smallToposMorphism B S hS g) ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS f') ≅
      Sites.abelianInverseImage (smallToposMorphism B S hS f) ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS i) :=
  StacksTag03LR.abelianInverseImageSquareIso _ _ _ _
    (smallEtaleInverseImageSquareIsoOfComm B S hS i f' f g hw)

/-- **Stacks 03LR's inverse-image footnote, at abelian coefficients.**  For a cartesian square
of algebraic spaces, the inverse image of *abelian* sheaves on the small étale sites may be
taken around the square either way:
`(f')_{small}^{-1}(G|_{Y'}) = (f_{small}^{-1}G)|_{X'}`, naturally in the abelian sheaf `G`.

As at `Type` coefficients the hypothesis is only that the square commute, which is
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImageSquareIsoOfComm`; the identity is pure
functoriality.

Like `AlgebraicGeometry.Space.smallEtaleInverseImageSquareIso`, which is the same statement for
sheaves of sets, this is the datum of which the inverse of
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardBaseChangeIso` is *expected* to be the
adjunction mate; that identification is not proved here either. -/
@[stacks 03LR "the inverse-image footnote, at abelian coefficients"]
def smallEtaleAbelianInverseImageSquareIso (sq : IsPullback i f' f g) :
    Sites.abelianInverseImage (smallToposMorphism B S hS g) ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS f') ≅
      Sites.abelianInverseImage (smallToposMorphism B S hS f) ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS i) :=
  smallEtaleAbelianInverseImageSquareIsoOfComm B S hS i f' f g sq.w

end Square

/-! ### Stacks 0A4P read on the subspaces -/

section OnSubspace

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0A4P, in every degree, read on the subspaces.**  Let `f : X ⟶ Y` be an étale
morphism of algebraic spaces over `S`, let `iY : Z ⟶ Y` be a subspace and let `iX : W ⟶ X` be
its inverse image, presented by the cartesian square `hk` with `k : W ⟶ Z`.  Then, in every
degree `q` and naturally in the abelian sheaf `F` on `Y_étale`,

`k⁻¹(H^q_Z(F)|_Z) = H^q_{f⁻¹Z}(f⁻¹F)|_{f⁻¹Z}`

as abelian sheaves on `W = f⁻¹Z`.  This is the form of the conclusion the source states — the
sheaf identity read on the subspace rather than on the ambient small étale site — with the
source's hypothesis that `k` is an isomorphism *removed*: under that hypothesis `k⁻¹` is an
equivalence and the left-hand side is the source's `H^q_Z(F)` read on `Z`.

The ambient-site statement is
`AlgebraicGeometry.Space.closedHigherSectionsWithSupportEtaleRestrictionIso`.  What is added is
one whiskering by inverse image along `iX`, after which
`AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImageIso` — Stacks 03LQ at abelian
coefficients — turns restriction along postcomposition with `f` into the inverse image of the
morphism of small étale topoi, and
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImageSquareIsoOfComm` exchanges the two routes
around the square.  Only commutativity of `hk` is used, through
`CategoryTheory.ObjectProperty.hom_ext`. -/
@[stacks 0A4P "every degree q, read on the subspaces: k⁻¹(H^q_Z(F)|_Z) = H^q_{f⁻¹Z}(f⁻¹F)|_{f⁻¹Z}"]
def closedHigherSectionsWithSupportOnSubspaceIso {W Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y) (iX : W ⟶ X) (k : W ⟶ Z)
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) (q : ℕ) :
    (closedSectionsWithSupport.{u + 1} B S hS iY).rightDerived q ⋙
        (Sites.abelianInverseImage (smallToposMorphism B S hS iY) ⋙
          Sites.abelianInverseImage (smallToposMorphism B S hS k)) ≅
      etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        ((closedSectionsWithSupport.{u + 1} B S hS iX).rightDerived q ⋙
          Sites.abelianInverseImage (smallToposMorphism B S hS iX)) :=
  let Pq := (closedSectionsWithSupport.{u + 1} B S hS iY).rightDerived q
  let Qq := (closedSectionsWithSupport.{u + 1} B S hS iX).rightDerived q
  let Rf := etaleAbelianRestriction.{u + 1} B S hS f hf
  let LX := Sites.abelianInverseImage (smallToposMorphism B S hS iX)
  let e₀ : Sites.abelianInverseImage (smallToposMorphism B S hS iY) ⋙
      Sites.abelianInverseImage (smallToposMorphism B S hS k) ≅ Rf ⋙ LX :=
    (smallEtaleAbelianInverseImageSquareIsoOfComm B S hS k iX iY f
        (by apply ObjectProperty.hom_ext; exact hk.w)).symm ≪≫
      Functor.isoWhiskerRight (smallToposMorphism_abelianInverseImageIso B S hS f hf) LX
  Functor.isoWhiskerLeft Pq e₀ ≪≫ (Functor.associator Pq Rf LX).symm ≪≫
    Functor.isoWhiskerRight
      (closedHigherSectionsWithSupportEtaleRestrictionIso B S hS f hf iY iX k hk q) LX ≪≫
    Functor.associator Rf Qq LX

/-- **Stacks 0A4P, in every degree, on `Z` itself**, with the source's hypothesis that
`k : f⁻¹Z ⟶ Z` is an isomorphism.  Let `f : X ⟶ Y` be an étale morphism of algebraic spaces
over `S`, let `iY : Z ⟶ Y` be a subspace and let `iX : W ⟶ X` be its inverse image, presented
by the cartesian square `hk` with `k : W ⟶ Z` an isomorphism.  Then, in every degree `q` and
naturally in the abelian sheaf `F` on `Y_étale`,

`H^q_Z(F)|_Z = H^q_{f⁻¹Z}(f⁻¹F)|_{f⁻¹Z}`

as abelian sheaves on `Z`, the right-hand side read on `Z` through `k` — that is, pulled back
along `inv k : Z ⟶ f⁻¹Z`.  This is the reading of the conclusion that the source states.

It is `AlgebraicGeometry.Space.closedHigherSectionsWithSupportOnSubspaceIso`, which states the
same identity on `f⁻¹Z` and assumes nothing about `k`, with
`AlgebraicGeometry.Space.smallToposMorphism_comp_abelianInverseImage` used twice to cancel
`k⁻¹` against `(inv k)⁻¹`: once at `inv k ≫ k = 𝟙 Z`, which turns the composite into the
inverse image along `𝟙 Z`, and once at `𝟙 Z ≫ iY = iY`, which absorbs that into the inverse
image along `iY`.  No unit law for `AlgebraicGeometry.Space.smallToposMorphism` is needed: the
composition isomorphism at the second of those two identities does the cancelling without the
inverse image along `𝟙 Z` ever being identified with the identity functor.

Every intermediate isomorphism is named with its type written out and every reassociation is an
explicit `CategoryTheory.Functor.associator`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionInverseImage.lean`: although
`CategoryTheory.Functor.assoc` is an equality, leaving a functor composition to definitional
unfolding here hands the unifier the small étale inverse image to whnf and the elaboration runs
out of heartbeats. -/
@[stacks 0A4P "every degree q, on Z itself, with the source's hypothesis that k is an iso"]
def closedHigherSectionsWithSupportOnZIso {W Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y) (iX : W ⟶ X) (k : W ⟶ Z) [IsIso k]
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) (q : ℕ) :
    (closedSectionsWithSupport.{u + 1} B S hS iY).rightDerived q ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS iY) ≅
      etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        ((closedSectionsWithSupport.{u + 1} B S hS iX).rightDerived q ⋙
          (Sites.abelianInverseImage (smallToposMorphism B S hS iX) ⋙
            Sites.abelianInverseImage (smallToposMorphism B S hS (inv k)))) :=
  let Pq := (closedSectionsWithSupport.{u + 1} B S hS iY).rightDerived q
  let Qq := (closedSectionsWithSupport.{u + 1} B S hS iX).rightDerived q
  let Rf := etaleAbelianRestriction.{u + 1} B S hS f hf
  let LY := Sites.abelianInverseImage (smallToposMorphism B S hS iY)
  let LX := Sites.abelianInverseImage (smallToposMorphism B S hS iX)
  let LK := Sites.abelianInverseImage (smallToposMorphism B S hS k)
  let LKi := Sites.abelianInverseImage (smallToposMorphism B S hS (inv k))
  let TZ := Sites.abelianInverseImage (smallToposMorphism B S hS (𝟙 Z))
  let c₁ : LK ⋙ LKi ≅ TZ :=
    (smallToposMorphism_comp_abelianInverseImage B S hS (inv k) k).symm ≪≫
      eqToIso (congrArg
        (fun h : Z ⟶ Z => Sites.abelianInverseImage (smallToposMorphism B S hS h))
        (IsIso.inv_hom_id k))
  let c₂ : LY ⋙ TZ ≅ LY :=
    (smallToposMorphism_comp_abelianInverseImage B S hS (𝟙 Z) iY).symm ≪≫
      eqToIso (congrArg
        (fun h : Z ⟶ Y => Sites.abelianInverseImage (smallToposMorphism B S hS h))
        (Category.id_comp iY))
  let a₁ : Pq ⋙ LY ≅ Pq ⋙ (LY ⋙ TZ) := Functor.isoWhiskerLeft Pq c₂.symm
  let a₂ : Pq ⋙ (LY ⋙ TZ) ≅ Pq ⋙ (LY ⋙ (LK ⋙ LKi)) :=
    Functor.isoWhiskerLeft Pq (Functor.isoWhiskerLeft LY c₁.symm)
  let a₃ : Pq ⋙ (LY ⋙ (LK ⋙ LKi)) ≅ Pq ⋙ ((LY ⋙ LK) ⋙ LKi) :=
    Functor.isoWhiskerLeft Pq (Functor.associator LY LK LKi).symm
  let a₄ : Pq ⋙ ((LY ⋙ LK) ⋙ LKi) ≅ (Pq ⋙ (LY ⋙ LK)) ⋙ LKi :=
    (Functor.associator Pq (LY ⋙ LK) LKi).symm
  let a₅ : (Pq ⋙ (LY ⋙ LK)) ⋙ LKi ≅ (Rf ⋙ (Qq ⋙ LX)) ⋙ LKi :=
    Functor.isoWhiskerRight
      (closedHigherSectionsWithSupportOnSubspaceIso B S hS f hf iY iX k hk q) LKi
  let a₆ : (Rf ⋙ (Qq ⋙ LX)) ⋙ LKi ≅ Rf ⋙ ((Qq ⋙ LX) ⋙ LKi) :=
    Functor.associator Rf (Qq ⋙ LX) LKi
  let a₇ : Rf ⋙ ((Qq ⋙ LX) ⋙ LKi) ≅ Rf ⋙ (Qq ⋙ (LX ⋙ LKi)) :=
    Functor.isoWhiskerLeft Rf (Functor.associator Qq LX LKi)
  a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅ ≪≫ a₆ ≪≫ a₇

end OnSubspace

end AlgebraicGeometry.Space

end
