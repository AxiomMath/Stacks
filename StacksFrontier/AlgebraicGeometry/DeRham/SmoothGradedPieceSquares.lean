module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceCut
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# Section 0FMK: the squares against the differentials, reduced to two

`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplex` builds [Stacks, Section 0FMK] at the level
of complexes,

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`

for `f : X ⟶ Y` smooth over a base `S`, from two hypotheses: the comparison `e₀` in the degree of
the cut, and the hypothesis `he` that the degreewise comparisons commute with the differentials.
`e₀` is now discharged — it is
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXAtCut`. **This file discharges the bookkeeping
half of `he`**, leaving the mathematics as two concrete squares:

* the square in the degree of the cut, between `e₀` and the comparison one degree up;
* the squares above the cut, between consecutive values of
  `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`.

`he` quantifies over a degree named by a variable and an equation, as `CochainComplex.isoOfGE`
asks for it, and over the comparison
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXFromCut`, which is defined by cases on the
offset from the cut. `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXFromCut_comm_of_squares`
performs that case split and substitutes the degree equations away, so the two squares are stated
in the degrees their proofs will be about — `k` and `k + 1` at the cut, `k + 1 + j` and
`k + 1 + (j + 1)` above it — with no transport of a degree.

## Main results

* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXFromCut_zero` and
  `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXFromCut_succ`: the comparison from the cut, in
  the degree of the cut and above it, is the isomorphism it was built from.
* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXFromCut_comm_of_squares`: **the hypothesis
  `he`, from the two squares.**
* `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares`: **Section 0FMK granted only
  the two squares** — `e₀` supplied.

## Implementation notes

The two reduction lemmas hold by `rfl`, and that is the whole point of stating them. The case
split of `gradedPieceXIsoGradedTargetXFromCut` substitutes the degree away inside a tactic block,
so in each branch the comparison is the given isomorphism only up to the `Eq.mpr` that
substitution leaves. Checking that away is free — 594 and 655 heartbeats here — in a goal whose
only content is the two isomorphisms. It is **not** free in the square: discharging the same
`Eq.mpr` by `exact` against a goal that also carries the two differentials and the comparison one
degree up does not finish in ten minutes of elaboration. So the reduction is isolated in these
two statements, and the squares are reached from them by `congrArg`, never by `exact` into the
large goal and never by `rw` on it.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

/-! The derived-category and abelian structures, pinned rather than restated exactly as in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceFiltered`: resolving them at the
concrete inverse-image ringed space exceeds the default instance-synthesis budget. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **In the degree of the cut the comparison from the cut is the comparison at the cut.** The
degree equation is substituted away rather than transported along, so this holds by `rfl`.

Costs 593 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoGradedTargetXFromCut_zero [Smooth f] (k : ℕ)
    (e₀ : (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X (k : ℤ) ≅
      (gradedTargetComplex f g k).X (k : ℤ))
    (hp : (k : ℤ) + ((0 : ℕ) : ℤ) = ((k : ℕ) : ℤ)) :
    gradedPieceXIsoGradedTargetXFromCut f g k e₀ 0 ((k : ℕ) : ℤ) hp = e₀ := rfl

/-- **Above the cut the comparison from the cut is
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`**, in the degree `k + 1 + j` that the
decomposition `n = k + 1 + m` with `m : ℕ` names. Holds by `rfl`, for the same reason as in the
degree of the cut.

Costs 655 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoGradedTargetXFromCut_succ [Smooth f] (k : ℕ)
    (e₀ : (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X (k : ℤ) ≅
      (gradedTargetComplex f g k).X (k : ℤ)) (j : ℕ)
    (hp : (k : ℤ) + ((j + 1 : ℕ) : ℤ) = ((k + 1 + j : ℕ) : ℤ)) :
    gradedPieceXIsoGradedTargetXFromCut f g k e₀ (j + 1) ((k + 1 + j : ℕ) : ℤ) hp =
      gradedPieceXIsoGradedTargetX f g k j := rfl

/-- **The hypothesis `he` of `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplex`, from two
squares**: the one in the degree of the cut, and the ones above it.

`he` is stated with the degree named by a variable and an equation, which is what
`CochainComplex.isoOfGE` asks for; this performs the case split on the offset from the cut and
substitutes both equations away, leaving in each branch exactly the square its proof will be
about. Nothing mathematical happens here — the two squares are the hypotheses — and in particular
nothing is assumed of `e₀` beyond its being an isomorphism in the degree of the cut.

Costs 10,389 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoGradedTargetXFromCut_comm_of_squares [Smooth f] (k : ℕ)
    (e₀ : (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X (k : ℤ) ≅
      (gradedTargetComplex f g k).X (k : ℤ))
    (hcut : e₀.hom ≫ (gradedTargetComplex f g k).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) =
      (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d
          ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k 0).hom)
    (hup : ∀ j : ℕ, (gradedPieceXIsoGradedTargetX f g k j).hom ≫
        (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) =
      (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d
          ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom) :
    ∀ (m : ℕ) (p q : ℤ) (hp : (k : ℤ) + (m : ℤ) = p)
        (hq : (k : ℤ) + ((m + 1 : ℕ) : ℤ) = q),
      (gradedPieceXIsoGradedTargetXFromCut f g k e₀ m p hp).hom ≫
          (gradedTargetComplex f g k).d p q =
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d p q ≫
          (gradedPieceXIsoGradedTargetXFromCut f g k e₀ (m + 1) q hq).hom := by
  intro m p q hp hq
  have transport : ∀ (p q : ℤ)
      (e₁ e₁' : (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ)
        (deRhamSmoothFiltration f g)).X p ≅ (gradedTargetComplex f g k).X p)
      (e₂ e₂' : (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ)
        (deRhamSmoothFiltration f g)).X q ≅ (gradedTargetComplex f g k).X q),
      e₁ = e₁' → e₂ = e₂' →
      e₁'.hom ≫ (gradedTargetComplex f g k).d p q =
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d p q ≫
          e₂'.hom →
      e₁.hom ≫ (gradedTargetComplex f g k).d p q =
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d p q ≫
          e₂.hom := by
    rintro p q e₁ e₁' e₂ e₂' rfl rfl h
    exact h
  obtain rfl : ((k + 1 + m : ℕ) : ℤ) = q := by push_cast at hq; omega
  cases m with
  | zero =>
      obtain rfl : ((k : ℕ) : ℤ) = p := by push_cast at hp; omega
      exact transport _ _ _ _ _ _ (gradedPieceXIsoGradedTargetXFromCut_zero f g k e₀ hp)
        (gradedPieceXIsoGradedTargetXFromCut_succ f g k e₀ 0 hq) hcut
  | succ j =>
      obtain rfl : ((k + 1 + j : ℕ) : ℤ) = p := by push_cast at hp; omega
      exact transport _ _ _ _ _ _ (gradedPieceXIsoGradedTargetXFromCut_succ f g k e₀ j hp)
        (gradedPieceXIsoGradedTargetXFromCut_succ f g k e₀ (j + 1) hq) (hup j)

/-- **Stacks Project, Section 0FMK, at the level of complexes, granted only the squares against
the differentials.** For `f : X ⟶ Y` smooth over a base `S` and a cut `k`,

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`.

This is `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplex` with its comparison in the degree
of the cut supplied — `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXAtCut`, which assumes
nothing beyond smoothness of `f`. **What is still owed is exactly the two squares**, and they are
the Leibniz rule `AlgebraicGeometry.SheafOfModules.summand_d` read on the graded piece: the
differential of the `k`-th graded piece is `(-1)^k(1 ⊗ d_{X/Y})`, the term `dω ∧ η` of `d(ω ∧ η)`
lying in the next step of the filtration when `ω` is a pulled-back `k`-form, and the sign being
the one `Stacks.DeRhamSmooth.gradedTargetComplex_d` carries.

Costs 1,275 heartbeats against the default budget of 200,000. -/
def gradedPieceIsoGradedTargetComplexOfSquares [Smooth f] (k : ℕ)
    (hcut : (gradedPieceXIsoGradedTargetXAtCut f g k).hom ≫
        (gradedTargetComplex f g k).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) =
      (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d
          ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k 0).hom)
    (hup : ∀ j : ℕ, (gradedPieceXIsoGradedTargetX f g k j).hom ≫
        (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) =
      (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d
          ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom) :
    gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g) ≅
      gradedTargetComplex f g k :=
  gradedPieceIsoGradedTargetComplex f g k (gradedPieceXIsoGradedTargetXAtCut f g k)
    (gradedPieceXIsoGradedTargetXFromCut_comm_of_squares f g k
      (gradedPieceXIsoGradedTargetXAtCut f g k) hcut hup)

end Stacks.DeRhamSmooth

end
