module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreClassesFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses

/-!
# Invariance and commutation of Chern classes, reduced to the projective bundles

In Situation 0EDT let `X/B` be good. The Chern classes `c_n(ℰ) ∩ -` of a finite locally free
module of rank `r` are the coefficients of the inverse of the Segre series of its projective
bundle. Two consequences of this description are recorded here.

* If the projective bundles of `ℰ` and `ℰ'` (of the same rank) are identified over `X` by an
  isomorphism carrying `𝒪(1)` to `𝒪(1)`, then `c_n(ℰ) = c_n(ℰ')`.
* If the Segre operations of `ℰ` commute with those of `ℱ`, then so do their Chern classes:
  `c_i(ℰ) ∘ c_j(ℱ) = c_j(ℱ) ∘ c_i(ℰ)` (the conclusion of Stacks 0ES1), since the Chern classes are
  polynomials in the Segre operations.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.commute_chernSeq_of_commute`: the Chern sequences of two
  pairwise commuting Segre sequences commute.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_commute_of_segreCap_commute`: commutation of
  Chern classes from commutation of Segre operations.
* `AlgebraicGeometry.Space.PrivateChern.chernCap_eq_of_isPullback_projectiveBundle`: equality
  of Chern classes from an identification of the projective bundles.

## References

* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ES1](https://stacks.math.columbia.edu/tag/0ES1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

section Algebra

variable {R : Type*} [Ring R]

/-- An element commuting with every term of a Segre sequence commutes with every term of its
inverse sequence. -/
theorem commute_segreInverseSeq_of_commute {x : R} {t : ℕ → R} (h : ∀ a, Commute x (t a)) :
    ∀ n, Commute x (segreInverseSeq t n)
  | 0 => by rw [segreInverseSeq_zero]; exact Commute.one_right x
  | n + 1 => by
    rw [segreInverseSeq_succ]
    refine (Commute.sum_right _ _ _ fun j _ => ?_).neg_right
    exact (h _).mul_right (commute_segreInverseSeq_of_commute h j)
termination_by n => n
decreasing_by exact j.2

/-- An element commuting with every term of a Segre sequence commutes with every term of its
Chern sequence. -/
theorem commute_chernSeq_of_commute {x : R} {t : ℕ → R} (h : ∀ a, Commute x (t a)) (n : ℕ) :
    Commute x (chernSeq t n) :=
  ((Commute.neg_one_right x).pow_right n).mul_right (commute_segreInverseSeq_of_commute h n)

/-- **The Chern sequences of two pairwise commuting Segre sequences commute.** -/
theorem commute_chernSeq_chernSeq_of_commute {t t' : ℕ → R} (h : ∀ a b, Commute (t a) (t' b))
    (i j : ℕ) : Commute (chernSeq t i) (chernSeq t' j) :=
  (commute_chernSeq_of_commute (fun a => (commute_chernSeq_of_commute (fun b => h a b) j).symm)
    i).symm

end Algebra

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- **Commutation of Chern classes from commutation of Segre operations.** If every Segre
operation of `ℰ` commutes with every Segre operation of `ℱ`, then
`c_i(ℰ) ∘ c_j(ℱ) = c_j(ℱ) ∘ c_i(ℰ)`. -/
theorem chernCap_commute_of_segreCap_commute.{v}
    (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r s : ℕ)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E r) (hF : IsFiniteLocallyFreeOfRank D sX hX F s)
    (h : ∀ a b, Commute (segreCapOfModule.{u, v} E r hE a) (segreCapOfModule.{u, v} F s hF b))
    (i j : ℕ) : Commute (chernCap.{u, v} E r hE i) (chernCap.{u, v} F s hF j) :=
  commute_chernSeq_chernSeq_of_commute h i j

/-- **Equality of Chern classes from an identification of the projective bundles.** Let `ℰ`, `ℰ'`
have rank `d + 1`. If `f' : 𝐏(ℰ') ⟶ 𝐏(ℰ)` is an isomorphism over `X` (a cartesian square over the
identity) with `f'^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(ℰ')}(1)`, then `c_n(ℰ') = c_n(ℰ)`. -/
theorem chernCap_eq_of_isPullback_projectiveBundle
    (E E' : Modules.{u, u} D.site D.base D.base_mem X hX.1) (d : ℕ)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E (d + 1))
    (hE' : IsFiniteLocallyFreeOfRank D sX hX E' (d + 1))
    {f' : (projectiveBundleDatum E' d hE').space ⟶ (projectiveBundleDatum E d hE).space}
    (sq : IsPullback f' (projectiveBundleDatum E' d hE').proj (projectiveBundleDatum E d hE).proj
      (𝟙 X))
    (e : pullbackLine D (projectiveBundleDatum E' d hE').toBase
      (projectiveBundleDatum E' d hE').isGood (projectiveBundleDatum E d hE).toBase
      (projectiveBundleDatum E d hE).isGood f' (projectiveBundleDatum E d hE).twist ≅
        (projectiveBundleDatum E' d hE').twist) (n : ℕ) :
    chernCap.{u, u + 1} E' (d + 1) hE' n = chernCap.{u, u + 1} E (d + 1) hE n :=
  ProjectiveBundleDatum.chernCap_eq_of_isPullback_id _ _ sq e n

end AlgebraicGeometry.Space.PrivateChern

end
