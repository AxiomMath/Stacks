module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.NormalizationFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSiteChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Tag 07U4: the four properties of the normalization of an algebraic space

Let `X` be an algebraic space over `S` satisfying the equivalent conditions of Tag 0BB1. Tag 0BB2
names its normalization `ν_X : X^ν ⟶ X`; in this development that is
`AlgebraicGeometry.Space.normalization`, with source
`AlgebraicGeometry.Space.normalizationPresheaf`, both defined from `X`, the proof that it is an
algebraic space and the proof of condition (2) of Tag 0BB1, and from nothing else. This file
states the four numbered parts of **Tag 07U4** for that morphism, at exactly the hypotheses the
tag carries:

1. `X^ν` is normal and `ν_X` is integral;
2. if `X` is a scheme every quasi-compact open of which has finitely many irreducible components,
   then `ν_X` is the normalization of `X` in the sense of Tag 035E;
3. a morphism `f : X ⟶ Y` of algebraic spaces both satisfying the conditions of Tag 0BB1 and
   carrying codimension-zero points to codimension-zero points has a unique lift
   `f^ν : X^ν ⟶ Y^ν` with `ν_Y ∘ f^ν = f ∘ ν_X`;
4. if `f : X ⟶ Y` is étale or smooth and `Y` satisfies the conditions of Tag 0BB1, then the
   hypotheses of part (3) hold and `f^ν` induces an isomorphism `X^ν ⟶ X ×_Y Y^ν`.

No normalization datum is an input of any statement here: the normalization is the constructed
one, which exists by `AlgebraicGeometry.Space.nonempty_normalizationData`.

## Main results

* `AlgebraicGeometry.Space.isNormal_and_isIntegralHom_normalization`: part (1).
* `AlgebraicGeometry.Space.exists_iso_yoneda_normalizationScheme_normalization`: part (2).
* `AlgebraicGeometry.Space.existsUnique_comp_normalization_eq`: part (3).
* `AlgebraicGeometry.Space.isIso_pullbackLift_normalization_of_isEtale_or_isSmooth`: part (4).

## Implementation notes

The proofs specialize the statements proved for an arbitrary normalization datum —
`AlgebraicGeometry.Space.NormalizationData.isNormal_and_isIntegralHom`,
`AlgebraicGeometry.Space.NormalizationData.exists_iso_yoneda_normalizationScheme`,
`AlgebraicGeometry.Space.NormalizationData.existsUnique_normalizationLift` and
`AlgebraicGeometry.Space.NormalizationData.isIso_pullbackLift_of_isSmooth` — to the datum
`AlgebraicGeometry.Space.normalizationData`, whose morphism is the normalization Tag 0BB2
names. For part (2) the condition of
Tag 0BB1 on the represented algebraic space is derived from the scheme hypothesis by
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_yoneda`; for part (4) the étale
case is reduced to the smooth case by Tag 04XX (`AlgebraicGeometry.Space.isSmooth_of_isEtale`),
and the condition of Tag 0BB1 on `X`, which the normalization of `X` needs in order to be
defined, is the first conclusion.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB2](https://stacks.math.columbia.edu/tag/0BB2)
* [Stacks Project, Tag 035E](https://stacks.math.columbia.edu/tag/035E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_NormalizationProperties
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 07U4, part (1).** Let `F` be an algebraic space over `S` satisfying the equivalent
conditions of Tag 0BB1. Then its normalization `F^ν` is a normal algebraic space and the
normalization morphism `ν_F : F^ν ⟶ F` is integral. -/
@[stacks 07U4 "part (1)"]
theorem isNormal_and_isIntegralHom_normalization {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) :
    Space.IsNormal B S hS (normalizationPresheaf B S hS hF hfin) ∧
      Space.IsIntegralHom B S hS (normalization B S hS hF hfin) :=
  (normalizationData B S hS hF hfin).isNormal_and_isIntegralHom hF

/-- **Stacks 07U4, part (2).** Let `X` be an object of the big fppf site of `S` every
quasi-compact open of whose underlying scheme has finitely many irreducible components, so that
the algebraic space `X` represents satisfies the conditions of Tag 0BB1. Then the normalization
`X^ν` of that algebraic space is represented by an object `Xν` of the site whose underlying
scheme is the normalization scheme of the underlying scheme of `X`, and under that
identification `ν_X` is the normalization morphism of Tag 035E. -/
@[stacks 07U4 "part (2)"]
theorem exists_iso_yoneda_normalizationScheme_normalization (X : BigFppfOver B S hS)
    (hX : ∀ V : ((BigFppfOver.toScheme B S hS).obj X).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj X)) →
        (irreducibleComponents V).Finite) :
    ∃ (Xν : BigFppfOver B S hS) (p : Xν ⟶ X)
      (e : ((BigFppfOver.toScheme B S hS).obj Xν) ≅
        Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj X) hX)
      (φ : normalizationPresheaf B S hS (isAlgebraicSpace_yoneda B S hS X)
        (hasLocallyFiniteIrreducibleComponents_yoneda B S hS X hX) ≅ yoneda.obj Xν),
      (BigFppfOver.toScheme B S hS).map p =
          e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj X) hX ∧
        φ.hom ≫ yoneda.map p = normalization B S hS (isAlgebraicSpace_yoneda B S hS X)
          (hasLocallyFiniteIrreducibleComponents_yoneda B S hS X hX) :=
  NormalizationData.exists_iso_yoneda_normalizationScheme
    (normalizationData B S hS (isAlgebraicSpace_yoneda B S hS X)
      (hasLocallyFiniteIrreducibleComponents_yoneda B S hS X hX)) hX

/-- **Stacks 07U4, part (3).** Let `f : F ⟶ G` be a morphism of algebraic spaces over `S` both
satisfying the equivalent conditions of Tag 0BB1, such that every point of codimension zero of
`F` maps to a point of codimension zero of `G`. Then there is a unique morphism
`f^ν : F^ν ⟶ G^ν` with `ν_G ∘ f^ν = f ∘ ν_F`. -/
@[stacks 07U4 "part (3)"]
theorem existsUnique_comp_normalization_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hFfin : HasLocallyFiniteIrreducibleComponents B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hGfin : HasLocallyFiniteIrreducibleComponents B S hS G)
    (f : F ⟶ G)
    (hgeneric : ∀ x : points B S hS F, localRingDimension B S hS x = 0 →
      localRingDimension B S hS (pointsMap B S hS F f x) = 0) :
    ∃! g : normalizationPresheaf B S hS hF hFfin ⟶ normalizationPresheaf B S hS hG hGfin,
      g ≫ normalization B S hS hG hGfin = normalization B S hS hF hFfin ≫ f :=
  (normalizationData B S hS hF hFfin).existsUnique_normalizationLift
    (normalizationData B S hS hG hGfin) hF hG f hgeneric

/-- **Stacks 07U4, part (4).** Let `f : F ⟶ G` be an étale or a smooth morphism of algebraic
spaces over `S` with `G` satisfying the equivalent conditions of Tag 0BB1. Then the hypotheses of
part (3) hold — `F` satisfies the conditions of Tag 0BB1 too, and `f` carries points of
codimension zero to points of codimension zero — and the morphism `f^ν : F^ν ⟶ G^ν` of part (3)
induces an isomorphism `F^ν ⟶ F ×_G G^ν`.

The third conjunct is the existence and uniqueness of `f^ν`, part (3) at the hypotheses just
established, and the fourth is the isomorphism `(f^ν, ν_F) : F^ν ⟶ F ×_G G^ν`.

The condition of Tag 0BB1 on `F` is stated as an existential because the normalization `F^ν`
is only defined given it; by proof irrelevance the witness does not matter. The isomorphism is
asserted for every `g` with `ν_G ∘ g = f ∘ ν_F`, and by the third conjunct there is exactly one
such `g`, namely `f^ν`. -/
@[stacks 07U4 "part (4)"]
theorem isIso_pullbackLift_normalization_of_isEtale_or_isSmooth
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hGfin : HasLocallyFiniteIrreducibleComponents B S hS G) {f : F ⟶ G}
    (hf : IsEtale B S hS f ∨ IsSmooth B S hS f) :
    ∃ hFfin : HasLocallyFiniteIrreducibleComponents B S hS F,
      (∀ x : points B S hS F, localRingDimension B S hS x = 0 →
        localRingDimension B S hS (pointsMap B S hS F f x) = 0) ∧
      (∃! g : normalizationPresheaf B S hS hF hFfin ⟶ normalizationPresheaf B S hS hG hGfin,
        g ≫ normalization B S hS hG hGfin = normalization B S hS hF hFfin ≫ f) ∧
      ∀ (g : normalizationPresheaf B S hS hF hFfin ⟶ normalizationPresheaf B S hS hG hGfin)
        (hg : g ≫ normalization B S hS hG hGfin = normalization B S hS hF hFfin ≫ f),
        IsIso (pullback.lift g (normalization B S hS hF hFfin) hg) := by
  have hsm : IsSmooth B S hS f := hf.elim (isSmooth_of_isEtale B S hS hG) id
  have hFfin : HasLocallyFiniteIrreducibleComponents B S hS F :=
    hasLocallyFiniteIrreducibleComponents_of_isFlat_of_isLocallyOfFiniteType B S hS hF hG f
      (isFlat_of_isSmooth B S hS f hsm) (isLocallyOfFiniteType_of_isSmooth B S hS hsm) hGfin
  obtain ⟨-, hgen, hiso⟩ := NormalizationData.isIso_pullbackLift_of_isSmooth
    (normalizationData B S hS hF hFfin) (normalizationData B S hS hG hGfin) hF hG hsm hGfin
  exact ⟨hFfin, hgen, existsUnique_comp_normalization_eq B S hS hF hFfin hG hGfin f hgen, hiso⟩

end AlgebraicGeometry.Space

end
