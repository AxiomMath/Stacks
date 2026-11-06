module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveGeometricTwoArrows
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres

/-!
# An étale stabilizer-preserving morphism which is an equivalence on geometric points
(Stacks 0DUD)

Let `f : 𝒳 ⟶ 𝒴` be an étale 1-morphism of algebraic stacks over a scheme `S` of a big fppf
site. **Stacks 0DUD** says that `f` is an isomorphism as soon as it induces an isomorphism
between automorphism groups at every point of `|𝒳|` (**Stacks 0DTW**) and, for every
algebraically closed field `k`, the functor
`Mor(Spec k, 𝒳) ⟶ Mor(Spec k, 𝒴)` is an equivalence.

## Main results

* `AlgebraicGeometry.Stack.exists_isHomLift_map_eq_of_fiberMap_full`: condition (3) of
  **Stacks 0CPN** follows from fullness of the geometric fibre functors.
* `AlgebraicGeometry.Stack.isSurjective_of_fiberMap_essSurj`: the last sentence of the source's
  proof — the hypothesis on geometric points makes `f` surjective.
* `AlgebraicGeometry.Stack.isRelativelyEtale_of_isEtale`: an étale 1-morphism representable by
  algebraic spaces is étale in the sense of **Stacks 04XB**.
* `AlgebraicGeometry.Stack.isEquivalence_of_isEtale_of_universallyInjective_of_isSurjective`:
  **Stacks 05W5** for 1-morphisms of algebraic stacks representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isEquivalence_of_isEtale_of_inducesIsomorphismAt`: **Stacks 0DUD**.

## Implementation notes

The proof follows the source step by step. "By Lemma 0CPN we see that `f` is universally
injective": the input to the relevant implication of **Stacks 0CPN** — its condition (3), that a
2-arrow between the images of two geometric points of `𝒳` lifts — is exactly fullness of the
geometric fibre functor, which the hypothesis supplies;
`AlgebraicGeometry.Stack.exists_isHomLift_map_eq_of_fiberMap_full` extracts it, and
`AlgebraicGeometry.Stack.isSurjective_relativeDiagonal_of_liftsTwoArrowsAtGeometricPoints` and
`AlgebraicGeometry.Stack.universallyInjective_iff_isSurjective_relativeDiagonal` turn it into
universal injectivity.

"Combining Lemmas 0DU7 and 0DU9 we see that `f` is representable by algebraic spaces": étaleness
gives unramifiedness by **Stacks 0CIW**, so the implication (2) `⟹` (1) of **Stacks 0DU9**
(`AlgebraicGeometry.Stack.inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt`)
makes `f` stabilizer preserving, and **Stacks 0DU7**
(`AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isStabilizerPreserving`)
makes it representable by algebraic spaces.

"Hence `f` is an open immersion by Morphisms of Spaces, Lemma 05W5. To finish we remark that the
condition in the lemma also guarantees that `f` is surjective": surjectivity is
`AlgebraicGeometry.Stack.isSurjective_of_fiberMap_essSurj`, using that every point of `|𝒴|` is
represented over an algebraically closed field. The two steps are combined into **Stacks 05W5**
for representable 1-morphisms: each algebraic space representing a base change of `f` along a
scheme-valued point of `𝒴` is étale (**Stacks 0CIF** and **Stacks 0CG3**), universally injective
(**Stacks 0CI1**) and surjective (**Stacks 04XI**) over that point, hence isomorphic to it by
**Stacks 05W5** for algebraic spaces
(`AlgebraicGeometry.Space.isIso_of_isEtale_of_universallyInjective_of_isSurjective`); so `f` is
fully faithful (**Stacks 05UK**) and every object of `𝒴` lifts.

The groupoid `Mor(Spec k, 𝒳)` is the fibre of `𝒳` over a site object whose underlying scheme is
`Spec k`, and the functor is `CategoryTheory.Functor.fiberMap`, as in the reading of
**Stacks 0DTM** by `AlgebraicGeometry.Stack.exists_fiber_lift_of_universallyInjective`.

Being an isomorphism is `CategoryTheory.Functor.IsEquivalence` of the underlying functor. This
is not weaker than being an isomorphism over the site, because
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over` upgrades an equivalence between
categories fibred in groupoids over the site to a quasi-inverse strictly over it.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CI1](https://stacks.math.columbia.edu/tag/0CI1)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIW](https://stacks.math.columbia.edu/tag/0CIW)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0DTM](https://stacks.math.columbia.edu/tag/0DTM)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
* [Stacks Project, Tag 0DU7](https://stacks.math.columbia.edu/tag/0DU7)
* [Stacks Project, Tag 0DU9](https://stacks.math.columbia.edu/tag/0DU9)
* [Stacks Project, Tag 0DUD](https://stacks.math.columbia.edu/tag/0DUD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section GeometricFibres

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The functor `Mor(Spec k, 𝒳) ⟶ Mor(Spec k, 𝒴)` induced by a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` on the groupoids of objects over a site object: the functor between
the fibres of the two structure functors. -/
abbrev geometricFibreFunctor (f : 𝒳 ⟶ 𝒴) (V : BigFppfOver B S hS) :
    𝒳.val.val.p.Fiber V ⥤ 𝒴.val.val.p.Fiber V :=
  Functor.fiberMap 𝒳.val.val.p 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) V

/-- **The hypothesis on geometric points gives condition (3) of Stacks 0CPN.** Let `f : 𝒳 ⟶ 𝒴`
be a 1-morphism of algebraic stacks over `S` whose functor on the groupoid of objects over the
spectrum of an algebraically closed field is full. Then every 2-arrow between the images under
`f` of two objects of `𝒳` over such a spectrum is the image of a 2-arrow between the objects
themselves.

A 2-arrow lying over an identity between two objects over `V` is precisely a morphism of the
fibre `𝒳_V`, so this is fullness of `AlgebraicGeometry.Stack.geometricFibreFunctor` read
through the definition of the fibre category. -/
theorem exists_isHomLift_map_eq_of_fiberMap_full (f : 𝒳 ⟶ 𝒴)
    (hfull : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
        (geometricFibreFunctor B S hS f V).Full)
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (x₁ x₂ : 𝒳.val.val.obj) (h₁ : 𝒳.val.val.p.obj x₁ = V) (h₂ : 𝒳.val.val.p.obj x₂ = V)
    (β : (CatFiberedInGroupoids.homFunctor f.hom).obj x₁ ⟶
      (CatFiberedInGroupoids.homFunctor f.hom).obj x₂)
    (hβ : 𝒴.val.val.p.IsHomLift (𝟙 V) β) :
    ∃ α : x₁ ⟶ x₂, 𝒳.val.val.p.IsHomLift (𝟙 V) α ∧
      (CatFiberedInGroupoids.homFunctor f.hom).map α = β := by
  have hF : (geometricFibreFunctor B S hS f V).Full := hfull k V hV
  let a₁ : 𝒳.val.val.p.Fiber V := ⟨x₁, h₁⟩
  let a₂ : 𝒳.val.val.p.Fiber V := ⟨x₂, h₂⟩
  obtain ⟨α, hα⟩ := Functor.map_surjective (geometricFibreFunctor B S hS f V)
    (show (geometricFibreFunctor B S hS f V).obj a₁ ⟶ (geometricFibreFunctor B S hS f V).obj a₂
      from ⟨β, hβ⟩)
  exact ⟨α.1, α.2, congrArg Subtype.val hα⟩

/-- **The last sentence of the proof of Stacks 0DUD.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` whose functor on the groupoid of objects over the spectrum of an
algebraically closed field is essentially surjective. Then `f` is surjective.

Every point of `|𝒴|` is represented over an algebraically closed field
(`AlgebraicGeometry.Stack.exists_isAlgClosed_fieldValuedPoint`), and such a representative is an
object of the fibre of `𝒴` over its field spectrum; essential surjectivity produces an object of
the fibre of `𝒳` whose image is isomorphic to it in that fibre, and the isomorphism is a common
refinement of the two field-valued points. -/
@[ega "I 6.3.10" "Sufficiency"]
theorem isSurjective_of_fiberMap_essSurj (f : 𝒳 ⟶ 𝒴)
    (hessSurj : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
        (geometricFibreFunctor B S hS f V).EssSurj) :
    IsSurjective B S hS f := by
  intro y
  obtain ⟨p, hp, hpy⟩ := exists_isAlgClosed_fieldValuedPoint B S hS 𝒴.val.val
    𝒴.val.isFiberedInGroupoids y
  have : IsAlgClosed p.carrier := hp
  have : (geometricFibreFunctor B S hS f p.base).EssSurj :=
    hessSurj p.carrier p.base p.isSpec
  let a := (geometricFibreFunctor B S hS f p.base).objPreimage
    (⟨p.obj, p.over⟩ : 𝒴.val.val.p.Fiber p.base)
  let e := (geometricFibreFunctor B S hS f p.base).objObjPreimageIso
    (⟨p.obj, p.over⟩ : 𝒴.val.val.p.Fiber p.base)
  refine ⟨pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids
    { carrier := p.carrier
      field := p.field
      base := p.base
      isSpec := p.isSpec
      obj := a.1
      «over» := a.2 }, ?_⟩
  refine Eq.trans ?_ hpy
  exact (class_eq_class_iff_hasCommonExtension B S hS 𝒴.val.val
    𝒴.val.isFiberedInGroupoids _ _).2 ⟨_, ⟨𝟙 _⟩, ⟨e.hom.1⟩⟩

end GeometricFibres

section RepresentableEtale

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **An étale 1-morphism representable by algebraic spaces is étale in the sense of
Stacks 04XB.** For `f` representable by algebraic spaces, the universal étale-smooth diagram
test of **Stacks 0CIL** is passed on a diagram of **Stacks 0CIF** built from a presentation of
the target, and the third assertion of Stacks 0CIF identifies the existential test with the
relative property of **Stacks 03YK**; étaleness is étale-smooth local on the source-and-target
by **Stacks 0CG3**. -/
theorem isRelativelyEtale_of_isEtale (f : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (he : IsEtale B S hS f) :
    IsRelativelyEtale B S hS f.hom := by
  have hrel : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.etaleMorphisms B S hS)
      f.hom hrep := by
    refine hasRelativeProperty_of_hasPropertyOnSomeEtaleSmoothDiagram.{u, u, w} B S hS _
      (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) f hrep ?_
    refine hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram
      B S hS _ f ?_ he.2
    obtain ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp', -⟩ :=
      hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
        (⊤ : MorphismProperty (AlgebraicSpaces B S hS)) f hrep
        (fun _ _ _ _ _ _ => trivial)
    exact ⟨U', V', hU', hV', a', b', h', η', hsu', hbsm', hcomp'⟩
  exact ⟨hrep, hrel⟩

/-- **Stacks 05W5 for 1-morphisms of algebraic stacks representable by algebraic spaces.** A
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is representable by algebraic
spaces, étale, universally injective and surjective is an isomorphism.

Each of the three properties is read on the algebraic spaces representing the base changes of
`f` along scheme-valued points of `𝒴`: étaleness by
`AlgebraicGeometry.Stack.isRelativelyEtale_of_isEtale`, universal injectivity by
**Stacks 0CI1** and surjectivity by **Stacks 04XI**. So each such base change is an isomorphism
by **Stacks 05W5** for algebraic spaces. Hence `f` is fully faithful (**Stacks 05UK**), and an
object `y` of `𝒴` over `U` is the image of an object of `𝒳`: the base change of `f` along the
point `y` has a section over `U`, and that section names an object of `𝒳` whose image is
isomorphic to `y`. -/
theorem isEquivalence_of_isEtale_of_universallyInjective_of_isSurjective (f : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (he : IsEtale B S hS f)
    (hui : UniversallyInjective B S hS f) (hsurj : IsSurjective B S hS f) :
    (CatFiberedInGroupoids.homFunctor f.hom).IsEquivalence := by
  have het := (isRelativelyEtale_of_isEtale B S hS f hrep he).2
  have hui' := (representable_universallyInjective_iff B S hS f hrep).2 hui
  have hsu' : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      f.hom hrep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hrep).1 hsurj
  have hiso : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
      (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
          (CatFiberedInGroupoids.homFunctor f.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      IsIso (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
    fun U y hy F hF hrepr =>
      Space.isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
        (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) _
        (het U y hy F hF hrepr) (hui' U y hy F hF hrepr) (hsu' U y hy F hF hrepr)
  obtain ⟨hfull, hfaith⟩ := full_and_faithful_homFunctor_of_mono_representingMaps B S hS f.hom
    hrep fun U y hy F hF hrepr => have := hiso U y hy F hF hrepr; IsIso.mono_of_iso _
  have hess : (CatFiberedInGroupoids.homFunctor f.hom).EssSurj := by
    refine ⟨fun y₀ => ?_⟩
    let U : BigFppfOver B S hS := 𝒴.val.val.p.obj y₀
    let yf : 𝒴.val.val.p.Fiber U := ⟨y₀, rfl⟩
    have hyv := fibrePoint_comp B S hS 𝒴.val U yf
    obtain ⟨G, hG, ⟨e⟩⟩ := hrep U (fibrePoint B S hS 𝒴.val U yf) hyv
    let a : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
    obtain ⟨s⟩ := nonempty_section_of_isIso_algebraicSpaceMap B S hS U G hG
      (hiso U _ hyv G hG ⟨e⟩) a
    obtain ⟨x, i, -⟩ := exists_vertical_iso_of_section_baseChange B S hS f U _ G e a s
    let L := Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U yf
      ((Over.iteratedSliceBackward U).obj a)
    have : 𝒴.val.val.p.IsStronglyCartesian ((Over.iteratedSliceBackward U).obj a).hom L.φ :=
      L.isStronglyCartesian
    have : IsIso ((Over.iteratedSliceBackward U).obj a).hom := by
      have : IsIso ((Over.forget _).map ((Over.iteratedSliceBackward U).obj a).hom) :=
        inferInstanceAs (IsIso (𝟙 U.left))
      exact isIso_of_reflects_iso _ (Over.forget _)
    have hφ : IsIso L.φ := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.val.val.p
      ((Over.iteratedSliceBackward U).obj a).hom L.φ
    exact ⟨x, ⟨i.symm ≪≫ @asIso _ _ _ _ L.φ hφ⟩⟩
  exact { }

end RepresentableEtale

section Main

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0DUD.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Assume `f`
is étale, that `f` induces an isomorphism between the automorphism groups at `x` and at `f(x)`
for every `x ∈ |𝒳|` (**Stacks 0DTW**), and that for every algebraically closed field `k` the
functor `Mor(Spec k, 𝒳) ⟶ Mor(Spec k, 𝒴)` is an equivalence. Then `f` is an isomorphism.

The proof is the source's. Fullness of the functors on geometric points is condition (3) of
**Stacks 0CPN**, so `f` is universally injective. Étale implies unramified (**Stacks 0CIW**), so
**Stacks 0DU9** makes `f` stabilizer preserving and **Stacks 0DU7** makes it representable by
algebraic spaces. Essential surjectivity on geometric points makes `f` surjective, and
**Stacks 05W5**, in the form
`AlgebraicGeometry.Stack.isEquivalence_of_isEtale_of_universallyInjective_of_isSurjective`,
concludes. -/
@[stacks 0DUD]
theorem isEquivalence_of_isEtale_of_inducesIsomorphismAt (f : 𝒳 ⟶ 𝒴)
    (he : IsEtale B S hS f)
    (hauto : ∀ x : AlgebraicStacks.points B S hS 𝒳, InducesIsomorphismAt B S hS f x)
    (hfibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) →
        (geometricFibreFunctor B S hS f V).IsEquivalence) :
    (CatFiberedInGroupoids.homFunctor f.hom).IsEquivalence := by
  have hΔ : IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS f) :=
    isSurjective_relativeDiagonal_of_liftsTwoArrowsAtGeometricPoints B S hS f
      fun k _ _ V hV =>
        exists_isHomLift_map_eq_of_fiberMap_full B S hS f
          (fun k' _ _ V' hV' => have := hfibre k' V' hV'; inferInstance) k V hV
  have hui : UniversallyInjective B S hS f :=
    universallyInjective_of_isSurjective_relativeDiagonal B S hS f hΔ
  have hsurj : IsSurjective B S hS f :=
    isSurjective_of_fiberMap_essSurj B S hS f
      (fun k _ _ V hV => have := hfibre k V hV; inferInstance)
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_isStabilizerPreserving B S hS f
      (inertiaPullbackComparison_isEquivalenceOver_of_inducesIsomorphismAt B S hS f
        (isUnramified_of_isEtale B S hS he) hauto)
  exact isEquivalence_of_isEtale_of_universallyInjective_of_isSurjective B S hS f hrep he hui
    hsurj

end Main

end AlgebraicGeometry.Stack

end
