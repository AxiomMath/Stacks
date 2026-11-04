module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange
public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of an extension by zero along an étale morphism of algebraic spaces

Let `j : U ⟶ X` and `j_V : V ⟶ X` be étale morphisms of algebraic spaces over a scheme `S`
contained in a big fppf site `B`, let `W = V ×_X U` and let `j_W : W ⟶ V` and `p : W ⟶ U` be the
two projections.  Writing `(-)|_•` for restriction of modules along an étale morphism and `•_!`
for its left adjoint, extension by zero, the canonical base-change map

`j_{W!}(E|_W) ⟶ (j_!E)|_V`

is an isomorphism, both for a sheaf of `𝒪_U`-modules and for an object `E` of the unbounded
derived category `D(𝒪_U)`; that is, `(j_!E)|_V = j_{W!}(E|_W)`.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryComp` identifies the derived functor of a composite
  of exact functors with the composite of their derived functors.
* `AlgebraicGeometry.Space.etaleModulePullbackAdjunction`: restriction of modules along an étale
  morphism of algebraic spaces is left adjoint to the direct image.
* `AlgebraicGeometry.Space.restrictExtensionByZeroMap` is the base-change map
  `j_{W!}(-|_W) ⟶ (j_!-)|_V` of sheaves of modules, and
  `AlgebraicGeometry.Space.derivedRestrictExtensionByZeroMap` is its derived form.

## Main results

* `AlgebraicGeometry.Space.restrictExtensionByZeroMap_eq` unfolds the base-change map of sheaves
  of modules into the conjugate of the cartesian comparison of direct images.
* `AlgebraicGeometry.Space.isIso_restrictExtensionByZeroMap`: the base-change map of sheaves of
  modules is an isomorphism.
* `AlgebraicGeometry.Space.isIso_derivedRestrictExtensionByZeroMap`: the base-change map on
  unbounded derived categories of modules is an isomorphism.

## Implementation notes

Restriction is `AlgebraicGeometry.Space.etaleModulePullback`, the inverse image of modules along
an étale morphism in the reading of Stacks 03LV in which it is plain restriction of sections
along postcomposition of étale charts; `AlgebraicGeometry.Space.etaleModulePullbackAdjunction`
transports the adjunction of Stacks 03LU to that reading.  Extension by zero is not constructed
here but enters as data: a functor together with an adjunction exhibiting it as a left adjoint of
restriction.  An adjoint and its adjunction determine the functor up to a unique compatible
isomorphism, so this pins `j_!` and `j_{W!}`; étaleness of `j` and of `j_V` remains a hypothesis,
since the source asserts the formula for étale morphisms.

The base-change map is *defined*, not existentially quantified.  Restriction along an étale
morphism is both a left and a right adjoint, so each of the two functors in the statement is a
left adjoint: `j_{W!}(-|_W)` of `p_*((-)|_W)` and `(j_!-)|_V` of `j^*(j_{V*}-)`.  The map is the
conjugate, under those two adjunctions, of the cartesian comparison
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` of direct images of Stacks 03LX
around the square.  Explicitly, it is the unit of `j_{W!}(-|_W) ⊣ p_*((-)|_W)`, followed by that
comparison, followed by the counit of `(j_!-)|_V ⊣ j^*(j_{V*}-)`.  The conjugation bijection
`CategoryTheory.conjugateEquiv` both preserves and reflects isomorphisms — unlike the mate
bijection for a general square — and that is what makes the comparison an isomorphism with no
further input.  The direction `j_{W!}(E|_W) ⟶ (j_!E)|_V` is the one in which a canonical map
exists.

The cartesian square is the hypothesis `CategoryTheory.IsPullback`;
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` supplies it for the fibre product
`W = V ×_X U` of Stacks 02X2, and `AlgebraicGeometry.Space.isEtale_of_isPullback` of Stacks 03FU
provides the étaleness of the two projections.  The caveat inherited from Stacks 03LX applies:
that comparison of direct images has the right endpoints but is not known to be the adjunction
mate of the identification of the two composite inverse images around the square, so the map
constructed here is not compared with the mate of the latter.

The module universe is the universe `u` of the structure rings, which is the only one at which
`AlgebraicGeometry.Space.modulePushforward` and the exactness of restriction exist.

On derived categories, restriction is exact and so induces a functor on unbounded derived
categories; exactness of the extension by zero is a hypothesis, for the same reason that the
functor itself is.  Mathlib's `CategoryTheory.Functor.mapDerivedCategory` is functorial in
neither natural transformations nor composition, and two general constructions fill that gap.
Functoriality in natural transformations is `CategoryTheory.NatTrans.mapDerivedCategory`,
imported from `StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory`.
Functoriality in composition is `CategoryTheory.Functor.mapDerivedCategoryComp`
below.  Both are lifts through the localization `DerivedCategory.Q`, so the derived base-change
map is determined by the map of modules.

## References

* [Stacks Project, Tag 08HA](https://stacks.math.columbia.edu/tag/08HA)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- The composite of the derived functors of two exact functors lifts, through the localization
`DerivedCategory.Q`, the functor induced by the composite on cochain complexes. -/
noncomputable instance Functor.liftingMapDerivedCategoryComp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ))
      DerivedCategory.Q⟩

/-- The derived functor of a composite of exact functors is the composite of their derived
functors. -/
noncomputable def Functor.mapDerivedCategoryComp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F ⋙ G).mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory) (Iso.refl _)

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of modules along an étale morphism `f : X ⟶ Y` of algebraic spaces is left
adjoint to the direct image: it is the adjunction of Stacks 03LU, read through the
identification of Stacks 03LV of the pullback of modules with étale restriction. -/
noncomputable def etaleModulePullbackAdjunction {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    etaleModulePullback.{u, u} B S hS f hf ⊣ modulePushforward B S hS f :=
  (modulePullbackAdjunction B S hS f).ofNatIsoLeft
    (modulePullbackIsoEtaleModulePullback B S hS f hf)

section BaseChange

variable {U X V W : AlgebraicSpaces B S hS} {j : U ⟶ X} {jV : V ⟶ X} {jW : W ⟶ V} {p : W ⟶ U}
  (sq : IsPullback jW p jV j) (hj : IsEtale B S hS j.hom) (hjV : IsEtale B S hS jV.hom)
  {jShriek : Modules.{u, u} B S hS U.1 U.2 ⥤ Modules.{u, u} B S hS X.1 X.2}
  (adj : jShriek ⊣ etaleModulePullback.{u, u} B S hS j hj)
  {jWShriek : Modules.{u, u} B S hS W.1 W.2 ⥤ Modules.{u, u} B S hS V.1 V.2}
  (adjW : jWShriek ⊣ etaleModulePullback.{u, u} B S hS jW
    (isEtale_of_isPullback B S hS p jW j jV sq.flip hj))

/-- `(j_!-)|_V`, extension by zero along `j` followed by restriction to `V`, is left adjoint to
`j^*(j_{V*}-)`, the direct image along `j_V` followed by restriction to `U`. -/
noncomputable def shriekRestrictAdjunction :
    jShriek ⋙ etaleModulePullback.{u, u} B S hS jV hjV ⊣
      modulePushforward B S hS jV ⋙ etaleModulePullback.{u, u} B S hS j hj :=
  adj.comp (etaleModulePullbackAdjunction B S hS jV hjV)

/-- `j_{W!}((-)|_W)`, restriction to `W` followed by extension by zero along `j_W`, is left
adjoint to `p_*((-)|_W)`, restriction to `W` followed by the direct image along `p`. -/
noncomputable def restrictShriekAdjunction :
    etaleModulePullback.{u, u} B S hS p
          (isEtale_of_isPullback B S hS jW p jV j sq hjV) ⋙ jWShriek ⊣
      etaleModulePullback.{u, u} B S hS jW
          (isEtale_of_isPullback B S hS p jW j jV sq.flip hj) ⋙ modulePushforward B S hS p :=
  (etaleModulePullbackAdjunction B S hS p
    (isEtale_of_isPullback B S hS jW p jV j sq hjV)).comp adjW

/-- The canonical base-change map `j_{W!}(F|_W) ⟶ (j_!F)|_V` of sheaves of modules attached to a
cartesian square `W = V ×_X U` of algebraic spaces with `j : U ⟶ X` and `j_V : V ⟶ X` étale.

It is the conjugate, under `AlgebraicGeometry.Space.restrictShriekAdjunction` and
`AlgebraicGeometry.Space.shriekRestrictAdjunction`, of the cartesian comparison of direct images
of Stacks 03LX around the square. -/
noncomputable def restrictExtensionByZeroMap :
    etaleModulePullback.{u, u} B S hS p
          (isEtale_of_isPullback B S hS jW p jV j sq hjV) ⋙ jWShriek ⟶
      jShriek ⋙ etaleModulePullback.{u, u} B S hS jV hjV :=
  (conjugateEquiv (shriekRestrictAdjunction B S hS hj hjV adj)
      (restrictShriekAdjunction B S hS sq hj hjV adjW)).symm
    (modulePushforwardEtaleBaseChangeIso B S hS jW p jV j sq hj).inv

/-- The base-change map of sheaves of modules is the conjugate of the cartesian comparison of
direct images of Stacks 03LX, stated as an equation.  The elaborator does not unfold the
definition on its own, and this is what to rewrite with when it has to be unfolded. -/
theorem restrictExtensionByZeroMap_eq :
    restrictExtensionByZeroMap B S hS sq hj hjV adj adjW =
      (conjugateEquiv (shriekRestrictAdjunction B S hS hj hjV adj)
          (restrictShriekAdjunction B S hS sq hj hjV adjW)).symm
        (modulePushforwardEtaleBaseChangeIso B S hS jW p jV j sq hj).inv :=
  rfl

/-- **Stacks 08HA**, on sheaves of modules.  Let `j : U ⟶ X` and `j_V : V ⟶ X` be étale
morphisms of algebraic spaces, let `W = V ×_X U` with projections `j_W : W ⟶ V` and `p : W ⟶ U`,
and let `F` be a sheaf of `𝒪_U`-modules.  Then the canonical map
`j_{W!}(F|_W) ⟶ (j_!F)|_V` is an isomorphism, that is, `(j_!F)|_V = j_{W!}(F|_W)`. -/
@[stacks 08HA "on modules"]
theorem isIso_restrictExtensionByZeroMap :
    IsIso (restrictExtensionByZeroMap B S hS sq hj hjV adj adjW) :=
  conjugateEquiv_symm_iso _ _ _

section Derived

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable [HasSheafify (smallEtaleRingedSite B S hS U.1 U.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS U.1 U.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS V.1 V.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS V.1 V.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [jShriek.Additive] [PreservesFiniteLimits jShriek] [PreservesFiniteColimits jShriek]
  [jWShriek.Additive] [PreservesFiniteLimits jWShriek] [PreservesFiniteColimits jWShriek]

/-- The canonical base-change map `j_{W!}(E|_W) ⟶ (j_!E)|_V` on unbounded derived categories of
modules: the map of sheaves of modules, lifted through the localizations defining the derived
categories and read through the identification of the derived functor of a composite with the
composite of the derived functors. -/
noncomputable def derivedRestrictExtensionByZeroMap :
    (etaleModulePullback.{u, u} B S hS p
            (isEtale_of_isPullback B S hS jW p jV j sq hjV)).mapDerivedCategory ⋙
          jWShriek.mapDerivedCategory ⟶
      jShriek.mapDerivedCategory ⋙
        (etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory :=
  (Functor.mapDerivedCategoryComp _ jWShriek).inv ≫
    NatTrans.mapDerivedCategory (restrictExtensionByZeroMap B S hS sq hj hjV adj adjW) ≫
      (Functor.mapDerivedCategoryComp jShriek _).hom

/-- **Stacks 08HA.**  Let `j : U ⟶ X` and `j_V : V ⟶ X` be étale morphisms of algebraic spaces,
let `W = V ×_X U` with projections `j_W : W ⟶ V` and `p : W ⟶ U`, and let `E` be an object of
the unbounded derived category of `𝒪_U`-modules.  Then the canonical map
`j_{W!}(E|_W) ⟶ (j_!E)|_V` is an isomorphism, that is, `(j_!E)|_V = j_{W!}(E|_W)`. -/
@[stacks 08HA]
theorem isIso_derivedRestrictExtensionByZeroMap :
    IsIso (derivedRestrictExtensionByZeroMap B S hS sq hj hjV adj adjW) := by
  have := isIso_restrictExtensionByZeroMap B S hS sq hj hjV adj adjW
  unfold derivedRestrictExtensionByZeroMap
  infer_instance

end Derived

end BaseChange

end AlgebraicGeometry.Space

end
