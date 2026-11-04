module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContraction
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# Existence of a contraction of an exceptional curve of the first kind

`AlgebraicGeometry.IsContractionOfExceptionalCurve D b` says that `b : X ⟶ Z` is the blowup of a
Noetherian scheme `Z` in a closed point whose local ring is regular of dimension two, and that
`D` is the exceptional ideal of that blowup. Before this file the only morphism known to satisfy
it was the blowup itself contracting its own exceptional ideal
(`AlgebraicGeometry.isContractionOfExceptionalCurve_blowUpToBase`), so no morphism given
independently of a blowup had ever been exhibited as a contraction.

This file supplies the missing construction. Given a morphism `f : X ⟶ Y` to a Noetherian
scheme and a closed point `y` of `Y` whose local ring is regular of dimension two, the inverse
image `ℐ_y · 𝒪_X` of the vanishing ideal of `y` is an effective Cartier divisor exactly when `f`
is an object of the category of which the blowup of `Y` at `y` is the final object, so the
universal property of blowing up — [Stacks, Tag 0806],
`Stacks.Blowup.exists_hom_blowUp_of_isEffectiveCartierDivisor` — produces the classifying
morphism `g : X ⟶ Bl_y Y` over `Y`. Once `g` is an isomorphism, `f` *is* a contraction of
`ℐ_y · 𝒪_X`, and a contraction of an exceptional curve of the first kind therefore exists as
soon as that curve is cut out by `ℐ_y · 𝒪_X`.

## Main results

* `AlgebraicGeometry.isContractionOfExceptionalCurve_of_isIso_blowUpClassifying` — a morphism to
  a Noetherian scheme whose inverse image of a regular closed point of dimension two is an
  effective Cartier divisor, and whose classifying morphism to the blowup at that point is an
  isomorphism, is a contraction of that inverse image.
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying` — the
  existence statement for an exceptional curve of the first kind cut out by such an inverse
  image.

## What 0C2L still asks for

[Stacks, Tag 0C2L] is the unconditional existence statement: on a Noetherian `X` carrying an
exceptional curve of the first kind `E`, a proper `f : X ⟶ Y` to a Noetherian `Y` which carries
`E` to a single point `y` and is quasi-finite at every point off `E` has a Stein factorization
whose first factor is a contraction of `E`. Neither result below carries the tag, because both
take as a hypothesis the step of that proof which this development cannot yet perform. The
binder is `hclassify` — that every morphism over `f` to the blowup is an isomorphism, which is
the source's final step: the induced map on exceptional curves is non-constant and hence
quasi-finite, so the classifying morphism is birational and quasi-finite over a base that is
regular, hence normal, *at the points of its exceptional curve* — the hypothesis of item (4) of
[Stacks, Tag 0BFP], not of [Stacks, Tag 0AB1], which wants a globally normal target.

Regularity of `𝒪_{Y, y}` and the identification of the scheme-theoretic fibre `X_y` with `E` are
hypotheses `hreg`, `hdim` and `hfibre` for the same reason: in the source both come from
[Stacks, Tag 0C2K], whose regularity and dimension clauses are available here only on an
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`. That bundle is constructed in
`StacksFrontier/AlgebraicGeometry/Surfaces/FormalNeighborhoodFromMonomialValueLaw.lean`, which
builds it and reduces the whole tag to one equation. What genuinely blocks `hreg` and `hdim` is
the other half: nothing relates
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing`, a ring on the *source*, to the
completed local ring of the *base*, which is the transport [Stacks, Tag 0C2K] needs in order to
say anything about `𝒪_{Y, y}`.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A morphism whose classifying morphism to a blowup is an isomorphism is a contraction.**
Let `f : X ⟶ Y` be a morphism to a Noetherian scheme and let `y` be a closed point of `Y` whose
local ring is regular of dimension two. Suppose the inverse image along `f` of the vanishing
ideal `ℐ_y` of `y` is an effective Cartier divisor on `X`, so that the universal property of
blowing up provides a morphism `g : X ⟶ Bl_y Y` with `g ≫ Bl_y Y ⟶ Y` equal to `f`. If every
such `g` is an isomorphism then `f` is a contraction of `ℐ_y · 𝒪_X`.

The hypothesis `hclassify` is the one step of [Stacks, Tag 0C2L] this development cannot yet
perform; it is equivalent to the existential form, because the classifying morphism is unique
by the uniqueness half of [Stacks, Tag 0806]. -/
public theorem isContractionOfExceptionalCurve_of_isIso_blowUpClassifying
    {X Y : Scheme.{u}} [IsNoetherian Y] (y : Y) (hy : IsClosed ({y} : Set Y))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) (f : X ⟶ Y)
    (hcartier : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f))
    (hclassify : ∀ g : X ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      g ≫ AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f → IsIso g) :
    IsContractionOfExceptionalCurve
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f) f := by
  obtain ⟨g, hg⟩ := Stacks.Blowup.exists_hom_blowUp_of_isEffectiveCartierDivisor
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) f hcartier
  have : IsIso g := hclassify g hg
  exact ⟨inferInstance, y, hy, hreg, hdim, rfl, asIso g, hg⟩

/-- **A contraction of an exceptional curve of the first kind exists** as soon as the curve is
the scheme-theoretic inverse image of a regular closed point of dimension two under a morphism
whose classifying morphism to the blowup at that point is an isomorphism.

This is the conclusion of [Stacks, Tag 0C2L] with three of that proof's steps as hypotheses:
`hfibre`, that the scheme-theoretic fibre over `y` is `E`; `hreg` together with `hdim`, that
`𝒪_{Y, y}` is regular of dimension two; and `hclassify`, that the classifying morphism of the
blowup at `y` is an isomorphism. The properness of `f` and its quasi-finiteness off `E`, which
the source uses to obtain exactly those three, are not needed once they are granted, so they do
not appear. -/
public theorem exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying
    {X Y : Scheme.{u}} [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) (f : X ⟶ Y)
    (hfibre : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f)
    (hclassify : ∀ g : X ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      g ≫ AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f → IsIso g) :
    ∃ (Z : Scheme.{u}) (b : X ⟶ Z), IsContractionOfExceptionalCurve D b := by
  subst hfibre
  exact ⟨Y, f, isContractionOfExceptionalCurve_of_isIso_blowUpClassifying y hy hreg hdim f
    hE.isEffectiveCartierDivisor hclassify⟩

end AlgebraicGeometry

end
