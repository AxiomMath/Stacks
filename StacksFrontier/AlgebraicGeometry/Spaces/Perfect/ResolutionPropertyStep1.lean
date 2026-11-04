module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyBlowupStratificationNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyStep1Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyStep1Pullback

/-!
# Step 1 of Stacks 0GV6, over `Spec ℤ`

Stacks 0GV6 asserts that a quasi-compact, quasi-separated algebraic space `X` over a scheme `S`
carries a chain of closed subspaces `X ⊇ Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t = ∅` with each `Z_i → X` of finite
presentation, with `Z₀ ⊆ X` a thickening, and with, for every `i < t`, a
`(Z_i ∖ Z_{i+1})`-admissible blowing up `Z'_i → Z_i` such that `Z'_i` has the resolution
property.  Its proof has two steps.  Step 2, the Noetherian case, is
`AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isNoetherian`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/`.  Step 1 reduces the general case to it in three
moves:

1. view `X` as an algebraic space over `Spec ℤ`;
2. find, by absolute Noetherian approximation (Stacks 07SU), an affine morphism `X ⟶ X₀` with
   `X₀` of finite presentation over `ℤ`, hence Noetherian (Stacks 04ZL);
3. prove the lemma for `X₀` by Step 2 and pull the stratification and the blowup centres back
   to `X`, using that the resolution property goes up along affine morphisms (Stacks 0GUU) and
   that the strict transform of an affine morphism is affine.

**Moves 2 and 3 are proved here, and move 1 is not.**  The main result,
`AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isQuasiCompactSpace_overIntegers`,
is Stacks 0GV6 for a quasi-compact quasi-separated algebraic space **over the terminal scheme
`Spec ℤ`**, with no Noetherian hypothesis, given Stacks 0GV5.  Nothing here carries a tag, and
nothing here claims Stacks 0GV6 for a general base; see "What move 1 still needs" below for
exactly which transport results the base crossing is missing.

## Main results

* `AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isQuasiCompactSpace_overIntegers`:
  **Step 1 over `Spec ℤ`** — a quasi-compact, quasi-separated algebraic space over the terminal
  scheme is stratified in the sense of
  `AlgebraicGeometry.Space.IsResolutionBlowupStratified`, given Stacks 0GV5 and with no
  Noetherian hypothesis.
* `AlgebraicGeometry.Space.exists_closedFiltration_admissibleBlowups_`
  `resolutionProperty_overIntegers`: the same, unpacked into the words of Stacks 0GV6.

## The one hypothesis carried, and why

**Stacks 0GV5 is an explicit hypothesis `h0GV5`.**  It is carried verbatim from Step 2, whose
statement it is a hypothesis of: for a quasi-compact, quasi-separated algebraic space with
finitely many irreducible components it produces a quasi-compact dense open `U` and a
`U`-admissible blowing up with the resolution property.  Stacks 0GV5 is **not proved in this
library**; it is being proved on a separate branch, and the hypothesis is written in exactly the
shape of that statement — universally quantified over the algebraic space it is applied to,
because Step 2's induction applies it to every stratum — so that these results compose with it
unedited once it lands.  It is the *only* hypothesis beyond the tag's own, and in particular
there is no `IsNoetherian` hypothesis here: that is precisely what Step 1 removes.

## What move 1 still needs

The source's move 1 is one sentence citing two definitions ("Spaces, Definition 65.16.2 and
Properties of Spaces, Definition 66.3.1"), but in this framework every predicate is relative to
the triple `(B, S, hS)`, and absolute Noetherian approximation is available only over the
terminal scheme: `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace` and
`AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas` are both stated
for the base `⊤_ Scheme`.  So move 1 means transporting the *whole conclusion* of Stacks 0GV6
back across `AlgebraicGeometry.Space.viewOverIntegers` (Stacks 03BS, the lower-shriek extension
`Λ` of Stacks 03I5 part (2)) from the base `⊤_ Scheme` to the base `S`.  Note the direction: the
hypotheses of the tag travel *forward* along `Λ` and are available, while its conclusion has to
be *reflected*.

What the library already has for that transport:

* the equivalence itself, Stacks 04SG:
  `AlgebraicGeometry.spacesOverSmallerBaseEquivalence` in
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseEquivalence.lean`, with
  `AlgebraicGeometry.isAlgebraicSpace_viewOver_iff` there as its object-level form;
* `AlgebraicGeometry.Space.isQuasiCompactSpace_relocalize_iff` in
  `StacksFrontier/AlgebraicGeometry/Spaces/ProperSmallerBase.lean` (both directions);
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_viewOverIntegers` in
  `StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/SeparatedDescent.lean` (forward
  only);
* `AlgebraicGeometry.Space.isClosedSubspace_relocalizeSubfunctor` and
  `AlgebraicGeometry.Space.range_pointsMap_relocalizeSubfunctor_ι` in
  `StacksFrontier/AlgebraicGeometry/Spaces/RelocalizeProperSupport.lean` (forward only), and
  `AlgebraicGeometry.Space.exists_closedSubspaces_viewOverIntegers` in
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspacesViewOverIntegers.lean` (forward only);
* the bijection on points, `AlgebraicGeometry.Space.pointsRelocalize_bijective` in
  `StacksFrontier/AlgebraicGeometry/Spaces/PointsSmallerBase.lean` and the homeomorphism
  `AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph` in
  `StacksFrontier/AlgebraicGeometry/Spaces/PointsSmallerBaseInverse.lean`.

What it does not have, and what move 1 therefore still needs, is the *reflecting* direction for
the five ingredients of the conclusion: `AlgebraicGeometry.Space.IsClosedSubspace`,
`AlgebraicGeometry.Space.IsFinitePresentation` of the inclusion of a closed subspace,
`AlgebraicGeometry.Space.OpenSubspaces`, `AlgebraicGeometry.Space.IsAdmissibleBlowup` and
`AlgebraicGeometry.Space.HasResolutionProperty`.  For the last three the library has **no**
statement relating them to `Λ` or to `viewOverIntegers` in either direction; the same is true of
`AlgebraicGeometry.Space.IsThickening` and of `AlgebraicGeometry.Space.IsNoetherian`.  Two of
those are not plumbing: reflecting `IsAdmissibleBlowup` means knowing that the equivalence of
Stacks 04SG carries effective Cartier divisors and the terminal object of the category `𝒞` of
Stacks 085U across the two bases, and reflecting `HasResolutionProperty` means comparing
finite-locally-free quotients of modules on the small étale sites of the two views.  That is why
Step 1 is proved here over `Spec ℤ` and not for a general base.

## Implementation notes

**The base is literally `(B, ⊤_ Scheme, B.contains_terminal)`.**  Step 2 and the stratification
predicate read the containment of the terminal scheme off `B.contains_terminal`, so the
statements below take that same proof as their base containment, which makes them instances of
the general-base statements at `S = ⊤_ Scheme` with nothing special assumed about the site.

**The two general-base ingredients.**  Step 2 and the pullback are both stated over an arbitrary
base: `AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isNoetherian` and
`AlgebraicGeometry.Space.IsResolutionBlowupStratified.pullback_of_isAffineHom`.  Only the
approximation, `AlgebraicGeometry.Space.exists_isAffineHom_isNoetherian_algebraicSpaces`, is
particular to `Spec ℤ`, which is where the base crossing enters.

**The module universe is fixed at `{u, u}`**, as in
`AlgebraicGeometry.Space.IsResolutionBlowupStratified` and in every resolution-property
result of this tree.

## References

* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u})

/-- **Step 1 of the proof of Stacks 0GV6, over `Spec ℤ`.**  A quasi-compact, quasi-separated
algebraic space `X` over the terminal scheme carries the chain of Stacks 0GV6, given the
conclusion of Stacks 0GV5.  **There is no Noetherian hypothesis**: removing it is what Step 1
does.

The proof is the source's.  Absolute Noetherian approximation gives an affine morphism
`X ⟶ X₀` with `X₀` Noetherian
(`AlgebraicGeometry.Space.exists_isAffineHom_isNoetherian_algebraicSpaces`, Stacks 07SU with
Stacks 07SF part (1) and Stacks 04ZL); Step 2
(`AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isNoetherian`) stratifies `X₀`;
and the stratification pulls back along the affine morphism
(`AlgebraicGeometry.Space.IsResolutionBlowupStratified.pullback_of_isAffineHom`, which is the
source's "details omitted", using Stacks 0GUU and Stacks 0864 part (1)).

`h0GV5` is the conclusion of Stacks 0GV5, which this library does not prove, carried verbatim
from Step 2 in exactly that statement's shape; it is the only hypothesis beyond the tag's own.
What is *not* done is the source's first move, viewing a space over an arbitrary base `S` as a
space over `Spec ℤ`, so Stacks 0GV6 for a general base does not follow from this; see the module
documentation for the five transport results that move needs and does not have. -/
theorem isResolutionBlowupStratified_top_of_isQuasiCompactSpace_overIntegers
    (h0GV5 : ∀ X : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal,
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal X.1 →
      IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal X.1 →
      (irreducibleComponents (points B (⊤_ Scheme.{u}) B.contains_terminal X.1)).Finite →
      ∃ U : OpenSubspaces B (⊤_ Scheme.{u}) B.contains_terminal X.1,
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal U.1.toFunctor ∧
        Dense (subspacePointSet B (⊤_ Scheme.{u}) B.contains_terminal X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal) (b : X' ⟶ X),
            IsAdmissibleBlowup B (⊤_ Scheme.{u}) B.contains_terminal U b ∧
            HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) B.contains_terminal X'.1 X'.2)
    (X : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal X.1)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal
      B.contains_terminal X.1) :
    IsResolutionBlowupStratified B (⊤_ Scheme.{u}) B.contains_terminal X ⊤ := by
  obtain ⟨X₀, a, hX₀N, ha⟩ :=
    exists_isAffineHom_isNoetherian_algebraicSpaces B B.contains_terminal X hqc hqs
  exact IsResolutionBlowupStratified.pullback_of_isAffineHom B (⊤_ Scheme.{u})
    B.contains_terminal B.contains_terminal a ha hX₀N.1 hX₀N.2.1
    (isResolutionBlowupStratified_top_of_isNoetherian B (⊤_ Scheme.{u}) B.contains_terminal
      h0GV5 X₀ hX₀N)

/-- **The chain of Stacks 0GV6 over `Spec ℤ`, in the words of the source.**  For a
quasi-compact, quasi-separated algebraic space `X` over the terminal scheme — and given the
conclusion of Stacks 0GV5 — there are closed subspaces `Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t` of `X`, each of
finite presentation over `X`, with `Z₀ ⊆ X` a thickening in the sense of Stacks 05ZK part (1),
with `Z_t` the empty algebraic space, and with a `(Z_i ∖ Z_{i+1})`-admissible blowing up of
`Z_i` whose source has the resolution property for every `i < t`.

This is the conclusion of Stacks 0GV6 for the base `Spec ℤ`, with no Noetherian hypothesis.
`h0GV5` is the unproved Stacks 0GV5 in exactly its own shape and is the only hypothesis beyond
the tag's own; the base being `Spec ℤ` is the source's first move, which is not carried out in
this library.  See the module documentation. -/
theorem exists_closedFiltration_admissibleBlowups_resolutionProperty_overIntegers
    (h0GV5 : ∀ X : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal,
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal X.1 →
      IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal X.1 →
      (irreducibleComponents (points B (⊤_ Scheme.{u}) B.contains_terminal X.1)).Finite →
      ∃ U : OpenSubspaces B (⊤_ Scheme.{u}) B.contains_terminal X.1,
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal U.1.toFunctor ∧
        Dense (subspacePointSet B (⊤_ Scheme.{u}) B.contains_terminal X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal) (b : X' ⟶ X),
            IsAdmissibleBlowup B (⊤_ Scheme.{u}) B.contains_terminal U b ∧
            HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) B.contains_terminal X'.1 X'.2)
    (X : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
    (hqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal X.1)
    (hqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal
      B.contains_terminal X.1) :
    ∃ (t : ℕ) (Z : ℕ → Subfunctor X.1)
      (hZ : ∀ i, IsClosedSubspace B (⊤_ Scheme.{u}) B.contains_terminal (Z i)),
      (∀ i, IsFinitePresentation B (⊤_ Scheme.{u}) B.contains_terminal (Z i).ι) ∧
      (∀ i, Z (i + 1) ≤ Z i) ∧
      IsThickening B (⊤_ Scheme.{u}) B.contains_terminal X (Z 0) ∧
      IsEmpty (points B (⊤_ Scheme.{u}) B.contains_terminal (Z t).toFunctor) ∧
      ∀ i < t, ∃ (U : OpenSubspaces B (⊤_ Scheme.{u}) B.contains_terminal (Z i).toFunctor)
          (Y : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
          (f : Y ⟶ (⟨(Z i).toFunctor, (hZ i).1⟩ :
            AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)),
        Set.range (pointsMap B (⊤_ Scheme.{u}) B.contains_terminal U.1.toFunctor
            (U.1.ι ≫ (Z i).ι)) =
            subspacePointSet B (⊤_ Scheme.{u}) B.contains_terminal X.1 (Z i) \
              subspacePointSet B (⊤_ Scheme.{u}) B.contains_terminal X.1 (Z (i + 1)) ∧
          IsAdmissibleBlowup B (⊤_ Scheme.{u}) B.contains_terminal U f ∧
          HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) B.contains_terminal Y.1 Y.2 :=
  exists_thickening_filtration_of_isResolutionBlowupStratified_top
    (isResolutionBlowupStratified_top_of_isQuasiCompactSpace_overIntegers B h0GV5 X hqc hqs)

end AlgebraicGeometry.Space

end
