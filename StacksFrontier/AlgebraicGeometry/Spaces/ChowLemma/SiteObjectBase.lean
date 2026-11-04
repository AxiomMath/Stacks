module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence

/-!
# Chow's lemma relative to a base object of the site (Stacks 089J)

`AlgebraicGeometry.Space.hasChowSchemeCover_of_isSeparated_isFiniteType` is Stacks 089J read over
the base scheme of the site: an algebraic space over `Spec A` whose *structure* morphism is
separated and of finite type is covered properly and surjectively by a scheme of the site which is
H-quasi-projective over `Spec A`. This file transports that statement along the equivalence of
Stacks 04SG, so that it applies to an algebraic space over an arbitrary base scheme `S` of the
site equipped with a morphism to the representable presheaf of an object `T` of the big fppf site
of `S` whose underlying scheme is `Spec A`.

## Main results

* `AlgebraicGeometry.Space.exists_chowSchemeCover_over_base`: **Stacks 089J over a base object of
  the site.** An algebraic space `X` over `S` with a separated morphism of finite type
  `g : X ⟶ h_T`, where `T = (Spec A ⟶ S)` is an object of the big fppf site of `S`, is the target
  of a proper surjective morphism `p : h_{X'} ⟶ X` from a scheme `X'` of the site over `T`, with
  `p` compatible with the two morphisms to `h_T` and with `X' ⟶ T` H-quasi-projective on
  underlying schemes.
* `AlgebraicGeometry.Space.exists_chowSchemeCover_over_spec`: the same statement with the base
  object presented as `AlgebraicGeometry.siteObject` of a morphism `Spec A ⟶ S`.

## Implementation notes

Write `Λ_h` for the lower-shriek extension `CategoryTheory.OverShriek.relocalizePresheafFunctor h`
of Stacks 03I5 part (2) along `h : (Spec A) ⟶ S`, which is the structure morphism of the base
object `T = Over.mk h`.

The equivalence `AlgebraicGeometry.spacesOverSmallerBaseEquivalence` of Stacks 04SG identifies
algebraic spaces over `Spec A` with algebraic spaces over `S` equipped with a morphism to `h_T`.
Its counit therefore produces, from the pair `(X, g)`, an algebraic space `F` over `Spec A`
together with an isomorphism `θ : Λ_h F ≅ X` *over* `h_T`, that is one satisfying
`θ ≫ g = CategoryTheory.OverShriek.relocalizeToYoneda h F`. That single identity is all this file
uses of the equivalence; everything else is the invariance of the relevant conditions under an
isomorphism of arrows and under the extension, which
`StacksFrontier/AlgebraicGeometry/Spaces/ProperSmallerBase.lean` supplies.

Separatedness and finite type of `g` travel to the structure morphism
`AlgebraicGeometry.Space.toYonedaId` of `F` over `Spec A` in two steps: along `θ`, by
`AlgebraicGeometry.Space.isSeparated_of_arrowIso` and
`AlgebraicGeometry.Space.isFiniteType_of_arrowIso`; then down to `Spec A`, by
`AlgebraicGeometry.Space.isSeparated_of_relocalizeMap` and
`AlgebraicGeometry.Space.isFiniteType_relocalize_iff`, the structural morphism of `Λ_h` being the
extension of the structure morphism of `F` up to the isomorphism
`AlgebraicGeometry.relocalizeToYoneda_eq_map_toYonedaId`.

Chow's lemma over `Spec A` then yields `p_A : h_{X'_A} ⟶ F`. Its extension, read through the
identification of `Λ_h h_{X'_A}` with the representable presheaf of `X'_A` viewed over `S`, is
`AlgebraicGeometry.relocalizeChart`, whose source is the object `X' = (Over.map h).obj X'_A` of
the big fppf site of `S`; properness survives by
`AlgebraicGeometry.Space.isProper_relocalize_iff` and surjectivity by
`AlgebraicGeometry.Space.isSurjective_relocalize`. The morphism `ψ : X' ⟶ T` is
`AlgebraicGeometry.relocalizeOverHom`, which is `X'_A.hom` on underlying schemes — so the
H-quasi-projectivity clause of `AlgebraicGeometry.Space.HasChowSchemeCover` is literally the one
asked for here — and the commutation `p ≫ g = h_ψ` is
`AlgebraicGeometry.relocalizeChart_comp_relocalizeToYoneda`.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pair `(X, g)` comes from an algebraic space over the smaller base.** For an algebraic
space `X` over `S` with a morphism `g` to the representable presheaf of the object `Over.mk h` of
the big fppf site of `S`, there is an algebraic space `F` over the source of `h` whose
lower-shriek extension is isomorphic to `X` *over* that representable presheaf.

This is the counit of the equivalence of Stacks 04SG, read through the identification
`AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso` of its forward functor with the
lower-shriek extension and the identification `AlgebraicGeometry.Space.relocalizeToYoneda_eq` of
the structural morphism of that functor with the extension's own. -/
theorem exists_relocalize_arrowIso_of_isAlgebraicSpace
    (W : Scheme.{u}) (hW : B.Contains W) (h : B.obj hW ⟶ B.obj hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj (Over.mk h)) :
    ∃ (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B W hW F)
      (θ : (OverShriek.relocalizePresheafFunctor h).obj F ⟶ X),
      IsIso θ ∧ θ ≫ g = OverShriek.relocalizeToYoneda h F := by
  let Z : SpacesOverSmallerBase B W S hW hS h := ⟨Over.mk g, hX⟩
  let Fo : AlgebraicSpaces B W hW :=
    (spacesOverSmallerBaseEquivalence B W S hW hS h).inverse.obj Z
  let cOver : ((spacesOverSmallerBaseFunctor B W S hW hS h).obj Fo).1 ≅
      (Over.mk g : Over (yoneda.obj (Over.mk h))) :=
    (ObjectProperty.ι _).mapIso
      ((spacesOverSmallerBaseEquivalence B W S hW hS h).counitIso.app Z)
  let cPre : ((spacesOverSmallerBaseFunctor B W S hW hS h).obj Fo).1.left ≅ X :=
    (Over.forget (yoneda.obj (Over.mk h))).mapIso cOver
  have hw : cPre.hom ≫ g = ((spacesOverSmallerBaseFunctor B W S hW hS h).obj Fo).1.hom :=
    Over.w cOver.hom
  refine ⟨Fo.1, Fo.2,
    (spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app Fo ≫ cPre.hom,
    inferInstance, ?_⟩
  rw [Category.assoc, hw, relocalizeToYoneda_eq B W S hW hS h Fo]

/-- Properness and surjectivity are preserved by composing with isomorphisms on both sides. -/
private theorem isProper_isSurjective_comp_isIso_comp
    {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ⟶ X') (q : X' ⟶ Y) (ι : Y ⟶ Y')
    [IsIso e] [IsIso ι] (hp : IsProper B S hS q) (hs : IsSurjective B S hS q) :
    IsProper B S hS ((e ≫ q) ≫ ι) ∧ IsSurjective B S hS ((e ≫ q) ≫ ι) :=
  ⟨(isProper_comp_isIso_iff B S hS _ ι).2 ((isProper_isIso_comp_iff B S hS e q).2 hp),
    isSurjective_comp B S hS
      (isSurjective_comp B S hS (bijective_pointsMap_of_isIso B S hS e).2 hs)
      (bijective_pointsMap_of_isIso B S hS ι).2⟩

/-- **Chow's lemma for algebraic spaces over a base object of the site, [Stacks, Tag 089J].**

Let `h : Spec A ⟶ S` present an object `T = Over.mk h` of the big fppf site of `S`, and let `X` be
an algebraic space over `S` equipped with a separated morphism of finite type `g : X ⟶ h_T`. Then
there are an object `X'` of the big fppf site of `S`, a morphism `ψ : X' ⟶ T`, and a proper
surjective morphism `p : h_{X'} ⟶ X` with `p ≫ g = h_ψ`, such that `ψ` is H-quasi-projective on
underlying schemes.

This is Stacks 089J over `Spec A`, transported along the equivalence of Stacks 04SG: the pair
`(X, g)` is the lower-shriek extension of an algebraic space `F` over `Spec A` whose structure
morphism inherits separatedness and finite type, and the Chow scheme cover of `F` extends to one
of `X`. -/
theorem exists_chowSchemeCover_over_base
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (h : B.obj hA ⟶ B.obj hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj (Over.mk h))
    (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g) :
    ∃ (X' : BigFppfOver B S hS) (ψ : X' ⟶ Over.mk h) (p : yoneda.obj X' ⟶ X),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ g = yoneda.map ψ ∧
        IsHQuasiProjective ((BigFppfOver.toScheme B S hS).map ψ) := by
  obtain ⟨F, hF, θ, hθiso, hθ⟩ :=
    exists_relocalize_arrowIso_of_isAlgebraicSpace B S hS (Spec A) hA h hX g
  have _ := hθiso
  -- The structural morphism of the extension is separated and of finite type over `S`.
  have hsep₁ : IsSeparated B S hS (OverShriek.relocalizeToYoneda h F) := by
    rw [← hθ]
    exact isSeparated_of_arrowIso B S hS g (θ ≫ g) (inv θ) (𝟙 _) (by simp) hsep
  have hft₁ : IsFiniteType B S hS (OverShriek.relocalizeToYoneda h F) := by
    rw [← hθ]
    exact isFiniteType_of_arrowIso B S hS g (θ ≫ g) (inv θ) (𝟙 _) (by simp) hft
  -- Hence the structure morphism of `F` is separated and of finite type over `Spec A`.
  have _ := isIso_relocalizeToYoneda_yonedaId B (Spec A) S hA hS h
  have hkey := relocalizeToYoneda_eq_map_toYonedaId B (Spec A) S hA hS h F
  have hsep₂ : IsSeparated B (Spec A) hA (toYonedaId B (Spec A) hA F) := by
    refine isSeparated_of_relocalizeMap B (Spec A) S hA hS h _ ?_
    refine isSeparated_of_arrowIso B S hS (OverShriek.relocalizeToYoneda h F) _ (𝟙 _)
      (inv (OverShriek.relocalizeToYoneda h (yoneda.obj (Over.mk (𝟙 (B.obj hA)))))) ?_ hsep₁
    rw [← hkey]
    simp
  have hft₂ : IsFiniteType B (Spec A) hA (toYonedaId B (Spec A) hA F) := by
    refine (isFiniteType_relocalize_iff B (Spec A) hA S hS h (toYonedaId B (Spec A) hA F)).1 ?_
    refine isFiniteType_of_arrowIso B S hS (OverShriek.relocalizeToYoneda h F) _ (𝟙 _)
      (inv (OverShriek.relocalizeToYoneda h (yoneda.obj (Over.mk (𝟙 (B.obj hA)))))) ?_ hft₁
    rw [← hkey]
    simp
  -- Chow's lemma over `Spec A`.
  obtain ⟨XA, pA, hpAproper, hpAsurj, hqp⟩ :=
    hasChowSchemeCover_of_isSeparated_isFiniteType B A hA F hF
      (toYonedaId B (Spec A) hA F) hsep₂ hft₂
  -- Relocalize the cover to `S`.
  have hΛp : IsProper B S hS ((OverShriek.relocalizePresheafFunctor h).map pA) :=
    (isProper_relocalize_iff B (Spec A) hA S hS h
      (isAlgebraicSpace_yoneda B (Spec A) hA XA) hF pA).2 hpAproper
  have hΛs : IsSurjective B S hS ((OverShriek.relocalizePresheafFunctor h).map pA) :=
    isSurjective_relocalize B (Spec A) hA S hS h pA hpAsurj
  obtain ⟨hcp, hcs⟩ := isProper_isSurjective_comp_isIso_comp B S hS
    (relocalizedYonedaIso B (B.obj hA) (B.obj hS) h XA).inv
    ((OverShriek.relocalizePresheafFunctor h).map pA) θ hΛp hΛs
  exact ⟨(Over.map h).obj XA, relocalizeOverHom B (Spec A) S hA hS h XA,
    relocalizeChart B (Spec A) S hA hS h pA ≫ θ, hcp, hcs,
    by rw [Category.assoc, hθ, relocalizeChart_comp_relocalizeToYoneda], hqp⟩

/-- **Chow's lemma for algebraic spaces over an affine base object of the site,
[Stacks, Tag 089J].** The form of
`AlgebraicGeometry.Space.exists_chowSchemeCover_over_base` in which the base object of the big
fppf site of `S` is presented as `AlgebraicGeometry.siteObject` of a morphism `Spec A ⟶ S`. -/
theorem exists_chowSchemeCover_over_spec
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj (siteObject B S hS hA a))
    (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g) :
    ∃ (X' : BigFppfOver B S hS) (ψ : X' ⟶ siteObject B S hS hA a)
      (p : yoneda.obj X' ⟶ X),
      IsProper B S hS p ∧ IsSurjective B S hS p ∧ p ≫ g = yoneda.map ψ ∧
        IsHQuasiProjective ((BigFppfOver.toScheme B S hS).map ψ) :=
  exists_chowSchemeCover_over_base B S hS A hA (ObjectProperty.homMk a) hX g hsep hft

end AlgebraicGeometry.Space

end
