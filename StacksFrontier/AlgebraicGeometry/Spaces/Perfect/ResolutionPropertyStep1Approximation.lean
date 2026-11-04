module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection

/-!
# An affine morphism to a Noetherian algebraic space, by absolute Noetherian approximation

The first half of Step 1 of the proof of Stacks 0GV6 reads: "we may view `X` as an algebraic
space over `Spec ℤ` … thus we may apply Limits of Spaces, Proposition 70.8.1.  It follows that
we can find an affine morphism `X ⟶ X₀` with `X₀` of finite presentation over `ℤ`".  The
proposition cited is absolute Noetherian approximation, Stacks 07SU, and "of finite presentation
over `ℤ`" is used only through its consequence that `X₀` is Noetherian, Stacks 04ZL.

This file assembles exactly that sentence over the terminal scheme, out of three results all of
which are already proved:

* **Stacks 07SU** in the strengthened form the library proves it,
  `AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas` of
  `StacksFrontier/AlgebraicGeometry/Spaces/AbsoluteNoetherianApproximation/Main.lean`, which
  produces an approximation *together with the chapter's standing convention of Section 70.2*
  (tag 07SD, `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`) on its inverse system;
* **Stacks 07SF, part (1)** under that convention,
  `AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits`, by which the
  projection from the limit to a stage is affine;
* **Stacks 04ZL** for a stage of an approximation,
  `AlgebraicGeometry.Space.NoetherianApproximation.isNoetherian_obj`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_conventionalNoetherianApproximation_π`: the projection
  from a space to a stage of a Noetherian approximation of it whose system satisfies the
  chapter's convention is affine.
* `AlgebraicGeometry.Space.exists_isAffineHom_isNoetherian_of_isQuasiCompactSpace`: **the
  approximation sentence of Step 1 of Stacks 0GV6** — a quasi-compact, quasi-separated algebraic
  space over `Spec ℤ` admits an affine morphism to a Noetherian algebraic space over `Spec ℤ`.
* `AlgebraicGeometry.Space.exists_isAffineHom_isNoetherian_algebraicSpaces`: the same, phrased
  in the category `AlgebraicGeometry.Space.AlgebraicSpaces` of algebraic spaces, which is where
  the stratification predicate of Stacks 0GV6 lives.

## Implementation notes

**Why the *conventional* approximation and not the bare Stacks 07SU.**  The library's Stacks 07SU,
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`, forgets the
convention and places (correctly, as its own documentation explains) *no* bound on the size of
the index set — with the bound `#I < B.cutoff.ord.cof` the statement would be false.  But that
bound is exactly what the size-based form of Stacks 07SF, part (1)
(`AlgebraicGeometry.Space.isAffineHom_limitπ`, and
`AlgebraicGeometry.Space.isAffineHom_noetherianApproximation_π` built on it) needs in order to
conclude that the projection `X ⟶ X_i` is affine.  So the bare Stacks 07SU does *not* give the
affine morphism of Step 1.  The convention does, and the library's proof of Stacks 07SU
establishes it for every system it builds; this file therefore re-enters that proof one step
earlier, at `hasConventionalNoetherianApproximation_of_etaleAtlas`, rather than consuming its
conclusion.  Nothing is assumed: the surjective étale atlas by an affine object of the site that
`hasConventionalNoetherianApproximation_of_etaleAtlas` asks for is produced from
quasi-compactness by
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`.

**The base is the terminal scheme, and that is not a weakening of the input.**  Stacks 07SU is a
statement about algebraic spaces over `Spec ℤ`, and the library proves it there; `Spec ℤ` is the
terminal scheme `⊤_ Scheme`, whose containment in the site is `B.contains_terminal`.  What is
*not* done here is the base crossing of the source's first sentence, "we may view `X` as an
algebraic space over `Spec ℤ`": see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyStep1.lean` for why that
crossing is a wall for the conclusion of Stacks 0GV6 and precisely which transport results it
is missing.

**No hypothesis is carried.**  Every statement below has only the hypotheses of the source's own
sentence: `X` an algebraic space over the terminal scheme, quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 07SF, part (1), on a Noetherian approximation satisfying the chapter's
convention.**  If the inverse system of a Noetherian approximation `A` of `X` satisfies the
standing convention of Section 70.2 (tag 07SD), then every projection `X ⟶ A.diagram.obj j` is
affine.

This is `AlgebraicGeometry.Space.isAffineHom_limitπ_of_siteContainsBaseChangeLimits` read on the
approximation's own limiting cone: that result is about the projections of the canonical limit
cone of the system, and the two cones are carried onto one another by the canonical isomorphism
of limit cone points, affineness being stable under composition with an isomorphism.  Unlike
`AlgebraicGeometry.Space.isAffineHom_noetherianApproximation_π` it asks nothing about the size
of the index set. -/
theorem isAffineHom_conventionalNoetherianApproximation_π
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X)
    (hconv : letI := A.preorder; letI := A.nonempty; letI := A.isDirected
      SiteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A.diagram)
    (j : letI := A.preorder; (A.I)ᵒᵖ) :
    letI := A.preorder
    IsAffineHom B (⊤_ Scheme.{u}) hZ (A.π.app j) := by
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  let : IsCofiltered (A.I)ᵒᵖ := A.isCofiltered_op
  have hlim : IsAffineHom B (⊤_ Scheme.{u}) hZ (limit.π A.diagram j) :=
    isAffineHom_limitπ_of_siteContainsBaseChangeLimits B (⊤_ Scheme.{u}) hZ A.diagram hconv
      (fun g => A.isAffineHom_map g) j
  have heq : A.π.app j =
      (A.isLimit.conePointUniqueUpToIso (limit.isLimit A.diagram)).hom ≫
        limit.π A.diagram j :=
    (IsLimit.conePointUniqueUpToIso_hom_comp A.isLimit (limit.isLimit A.diagram) j).symm
  rw [heq]
  exact isAffineHom_iso_comp _ hlim

/-- **The approximation sentence of Step 1 of the proof of Stacks 0GV6.**  A quasi-compact,
quasi-separated algebraic space `X` over `Spec ℤ` admits an affine morphism `X ⟶ X₀` to a
Noetherian algebraic space `X₀` over `Spec ℤ`.

This is the source's "we can find an affine morphism `X ⟶ X₀` with `X₀` of finite presentation
over `ℤ`", with "of finite presentation over `ℤ`" replaced by the consequence of it the source
uses, namely that `X₀` is Noetherian in the sense of Stacks 03EA.  The space `X₀` is a stage of
the Noetherian approximation of Stacks 07SU; the projection to it is affine by Stacks 07SF, part
(1) under the chapter's convention, and the stage is Noetherian by Stacks 04ZL.  No hypothesis
beyond the two of the source's sentence is used. -/
theorem exists_isAffineHom_isNoetherian_of_isQuasiCompactSpace
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X) :
    ∃ (X₀ : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ X₀) (a : X ⟶ X₀),
      IsNoetherian B (⊤_ Scheme.{u}) hZ hZ X₀ ∧ IsAffineHom B (⊤_ Scheme.{u}) hZ a := by
  obtain ⟨U, u, -, hus, hue⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (⊤_ Scheme.{u}) hZ X hX).mp
      hqc
  obtain ⟨A, hconv⟩ :=
    hasConventionalNoetherianApproximation_of_etaleAtlas hX hqc hqs U u hus hue
  let := A.preorder
  let := A.nonempty
  obtain ⟨i⟩ : Nonempty A.I := A.nonempty
  exact ⟨A.diagram.obj (op i), A.isAlgebraicSpace _, A.π.app (op i),
    A.isNoetherian_obj B hZ (op i),
    isAffineHom_conventionalNoetherianApproximation_π B hZ A hconv (op i)⟩

/-- **The approximation sentence of Step 1 of the proof of Stacks 0GV6, in the category of
algebraic spaces.**  A quasi-compact, quasi-separated algebraic space `X` over `Spec ℤ` admits
an affine morphism to a Noetherian one, as a morphism of
`AlgebraicGeometry.Space.AlgebraicSpaces`.

This is `AlgebraicGeometry.Space.exists_isAffineHom_isNoetherian_of_isQuasiCompactSpace`
repackaged: the stratification predicate of Stacks 0GV6,
`AlgebraicGeometry.Space.IsResolutionBlowupStratified`, is stated for objects and morphisms of
that category. -/
theorem exists_isAffineHom_isNoetherian_algebraicSpaces
    (X : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ X.1)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ X.1) :
    ∃ (X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ) (a : X ⟶ X₀),
      IsNoetherian B (⊤_ Scheme.{u}) hZ hZ X₀.1 ∧
        IsAffineHom B (⊤_ Scheme.{u}) hZ a.hom := by
  obtain ⟨X₀, hX₀, a, hN, ha⟩ :=
    exists_isAffineHom_isNoetherian_of_isQuasiCompactSpace B hZ X.2 hqc hqs
  exact ⟨⟨X₀, hX₀⟩, ObjectProperty.homMk a, hN, ha⟩

end AlgebraicGeometry.Space

end
