module

public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects
import all StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjects

/-!
# Formal smoothness on objects along a class of test objects

The lifting conditions of formal smoothness for a transformation of presheaves on the big fppf
site of a scheme `S` (Stacks 049S) and of formal smoothness on objects for a 1-morphism of
categories fibred in groupoids (Stacks 06D0) quantify over all affine first-order thickenings
`U ⟶ U'`. This file restricts both quantifiers to the thickenings whose *larger* member `U'`
satisfies a prescribed predicate `P` on objects of the site, and proves the implication of
Stacks 06D3 — formal smoothness of a 1-morphism representable by algebraic spaces implies formal
smoothness on objects — for each such restriction.

The point of the restriction is that some consumers only ever test the condition on special
thickenings. The predeformation categories of Stacks 07WJ only see thickenings of spectra of
Artinian local rings, so the condition of Stacks 07XS follows from the restricted condition at
the predicate "the underlying scheme is the spectrum of an Artinian local ring".

## Main definitions

* `AlgebraicGeometry.BigFppfOver.IsSpecArtinianLocal`: the objects of the site whose underlying
  scheme is the spectrum of an Artinian local ring.
* `AlgebraicGeometry.Space.FormallySmoothAlong`: existence of infinitesimal lifts along the
  affine square-zero closed immersions whose target satisfies `P`.
* `AlgebraicGeometry.Stack.IsFormallySmoothOnObjectsAlong`: formal smoothness on objects along
  the affine first-order thickenings whose target satisfies `P`.
* `AlgebraicGeometry.BigFppfOver.IsRelativelyFormallySmoothAlong`: every algebraic space
  representing a base change of the 1-morphism along a scheme-valued point of the target has
  structural morphism formally smooth along `P`.

## Main results

* `BigFppfOver.isFormallySmoothOnObjectsAlong_of_isRelativelyFormallySmoothAlong`: the
  implication of Stacks 06D3, along `P`.

## Implementation notes

The proof is that of
`AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth`: the
formal smoothness hypothesis is applied exactly once, to the thickening `U ⟶ U'` of the lifting
problem itself, read in the site of `S`, so the restriction to targets satisfying `P` passes
through unchanged; the private helper of that proof is used directly, through `import all`. That
declaration and the definitions it relates are the case `P = ⊤` and are left as they are.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06D3](https://stacks.math.columbia.edu/tag/06D3)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe u v w

namespace BigFppfOver

/-- An object of the big fppf site of `S` whose underlying scheme is the spectrum of an Artinian
local ring. These are the test objects of the predeformation categories of Stacks 07WJ. -/
def IsSpecArtinianLocal (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) : Prop :=
  ∃ R : CommRingCat.{u}, IsLocalRing R ∧ IsArtinianRing R ∧
    Nonempty ((BigFppfOver.toScheme B S hS).obj T ≅ Spec R)

end BigFppfOver

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Formal smoothness along a class of test objects.** Every commutative affine square against
a square-zero closed immersion `T ⟶ T'` whose target `T'` satisfies `P` admits a lift. With
`P = ⊤` this is `AlgebraicGeometry.Space.FormallySmooth`. -/
abbrev FormallySmoothAlong (P : BigFppfOver B S hS → Prop)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop :=
  ∀ (T T' : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj T') → P T' → ∀ (i : T ⟶ T'),
      IsSquareZeroClosedImmersion B S hS i → ∀ (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map i.op y → ∃ z : F.obj (op T'), IsLift a i x y z

end Space

namespace Stack

open Stacks.Thickenings

/-- **Formal smoothness on objects along a class of test objects**: the first-order lifting
condition of Stacks 06D0, `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`, asked only for the
affine first-order thickenings `U ⟶ U'` whose target `U'` satisfies `P`, with the comparison
square required to commute. -/
def IsFormallySmoothOnObjectsAlong
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (P : BigFppfOver B S hS → Prop)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)) (p : 𝒳 ⟶ 𝒴) : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let F := CatFiberedInGroupoids.homFunctor p
  let hF := CatFiberedInGroupoids.homFunctor_comp_p p
  let pU := fun U => Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF U
  let compare := fun (U U' : BigFppfOver B S hS)
      (i : U ⟶ U') (x' : 𝒳.val.p.Fiber U') =>
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p) i
      (Functor.IsPreFibered.pullbackMap ((pU U').obj x').2 i)
      (F.map (Functor.IsPreFibered.pullbackMap x'.2 i))
      (by infer_instance)
      (@Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ _ _ _ _ _ _ _
        (CatFiberedInGroupoids.isStronglyCartesian_map p i
          (Functor.IsPreFibered.pullbackMap x'.2 i)))
  ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj U') → P U' →
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) →
    ∀ (x : 𝒳.val.p.Fiber U) (y' : 𝒴.val.p.Fiber U')
      (γ : (pU U).obj x ≅ Functor.pullbackFiber 𝒴.val.p y' i),
      ∃ (x' : 𝒳.val.p.Fiber U')
        (β : Functor.pullbackFiber 𝒳.val.p x' i ≅ x)
        (γ' : (pU U').obj x' ≅ y'),
        ((compare U U' i x').hom ≫
          (pU U).map β.hom) ≫ γ.hom =
          Functor.pullbackFiberHom (p := 𝒴.val.p) γ'.hom i

end Stack

namespace BigFppfOver

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.TwoFibreProductOver.fst CategoryTheory.TwoFibreProductOver.snd
  twoFibreProduct twoFibreProductSnd
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.Fiber.mapOfComp CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.instCategoryObj

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.isoMk

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is formally smooth along `P`* when every algebraic space
representing its base change along a scheme-valued point of the target has structural morphism
formally smooth along `P`, read as a morphism of algebraic spaces over `S`. With `P = ⊤` this is
`AlgebraicGeometry.BigFppfOver.IsRelativelyFormallySmooth`. -/
abbrev IsRelativelyFormallySmoothAlong
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (P : BigFppfOver B S hS → Prop)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor p))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.FormallySmoothAlong P
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- **Stacks 06D3, that (2) implies (1), along a class of test objects.** A 1-morphism of
categories fibred in groupoids over the big fppf site of `S` which is representable by algebraic
spaces and formally smooth along `P` is formally smooth on objects along `P`.

The proof is that of
`AlgebraicGeometry.BigFppfOver.isFormallySmoothOnObjects_of_isRelativelyFormallySmooth`: the
formal smoothness of the representing algebraic space is used once, at the thickening of the
lifting problem itself, whose target is the one `P` is asked of. -/
theorem isFormallySmoothOnObjectsAlong_of_isRelativelyFormallySmoothAlong
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (P : BigFppfOver B S hS → Prop)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hform : IsRelativelyFormallySmoothAlong B S hS P p) :
    Stack.IsFormallySmoothOnObjectsAlong B S hS P 𝒳 𝒴 p :=
  isFormallySmoothOnObjectsOn_of_formallySmoothOn B S hS P p hp hform

end BigFppfOver

end AlgebraicGeometry

end
