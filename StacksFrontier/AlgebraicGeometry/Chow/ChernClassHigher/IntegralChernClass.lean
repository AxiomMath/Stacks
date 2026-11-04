module

public import Mathlib.Algebra.DirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleExistence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a finite locally free module, capped with the fundamental cycle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, integral and of delta-dimension `n`, let `ℰ` be a finite locally
free `O_X`-module of rank `r` and let `(π : P ⟶ X, O_P(1))` be the projective bundle of `ℰ`.
[Stacks, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0) *defines* the Chern classes of `ℰ`
on `X` as follows:

1. by the projective space bundle formula, Stacks 02TX, there are classes
   `c_i ∈ A_{n-i}(X)`, `i = 0, …, r`, with `c_0 = [X]` and

     `∑_{i=0}^{r} (-1)^i c₁(O_P(1))^i ∩ π^*c_{r-i} = 0`   (formula 02U1);

2. one writes `c_i(ℰ) ∩ [X] = c_i`;
3. the *total* Chern class is the sum `c(ℰ) ∩ [X] = ∑_{i=0}^{r} c_i(ℰ) ∩ [X]` in the graded group
   `A_*(X) = ⊕_k A_k(X)`.

The displayed equation is `Stacks.Chow.ProjectiveBundleChernRelation`, and clause (1) is
`Stacks.Chow.IsChernCapFamily` read at the fundamental class `[X] ∈ A_n(X)`. The projective bundle
enters through a flat morphism `π : P ⟶ X` of relative dimension `r - 1`, an operator
`Stacks.Chow.ChernCapOperator` on `P` standing for `c₁(O_P(1)) ∩ -`, and the two halves of
Stacks 02TX as the hypotheses `Stacks.Chow.ProjectiveBundleRelationSurjective` and
`Stacks.Chow.ProjectiveBundleRelationInjective`. Neither the integrality of `X` nor `n = dim_δ(X)`
is assumed.

## Main definitions

* `Stacks.Chow.IsChernClassFundamentalFamily` — **clause (1)**: that a family `(c_j)_{j ≤ r}` of
  Chow classes on `X` has `c_0 = [X]` and satisfies the relation 02U1.
* `Stacks.Chow.ChernClassFundamentalFamily` — such a family, as a datum.
* `Stacks.Chow.chernClassCapFundamental` — **part (2)**, the class `c_i(ℰ) ∩ [X] ∈ A_{n-i}(X)`.
* `Stacks.Chow.totalChernClassCapFundamental` — **part (3)**, the total Chern class
  `c(ℰ) ∩ [X] ∈ ⊕_k A_k(X)`.

## Main results

* `Stacks.Chow.exists_isChernClassFundamentalFamily`,
  `Stacks.Chow.nonempty_chernClassFundamentalFamily` — **clause (1), existence**, granted the
  surjectivity of the map of Stacks 02TX.
* `Stacks.Chow.chernClassCapFundamental_zero` — **the normalisation `c_0(ℰ) ∩ [X] = [X]`**.
* `Stacks.Chow.chernClassFundamentalFamily_unique`,
  `Stacks.Chow.totalChernClassCapFundamental_unique` — **clause (1), uniqueness**, granted the
  injectivity of the map of Stacks 02TX: the datum, and hence every class read off it, is
  determined.

## References

* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02U1](https://stacks.math.columbia.edu/tag/02U1)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)

/-! ### The Chern classes of Stacks 02U0 -/

/-- **Stacks 02U0, clause (1).** That a family `(c_j)_{0 ≤ j ≤ r}` of Chow classes on `X`, with
`c_j` of degree `n - j`, is the family of Chern classes of a rank-`r` module capped with the
fundamental cycle of `X`: its zeroth member is `[X]`, and it satisfies the projective-bundle
relation 02U1.

This is `Stacks.Chow.IsChernCapFamily`, the characterization of Stacks 02U6, read at the
fundamental class `[X] ∈ A_n(X)`. -/
def IsChernClassFundamentalFamily (n : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (n - (j : ℤ))) : Prop :=
  IsChernCapFamily C sX sP π hsP r hπ hfac twist n
    (QuotientAddGroup.mk' (rationalEquivalences C sX n)
      (cycleAssociatedToClosedSubscheme C sX (𝟙 X) n)) c

/-- **Stacks 02U0, clause (1), existence.** Granted the surjectivity of the projective space
bundle map of Stacks 02TX there is a family of Chern classes capped with the fundamental
cycle. -/
theorem exists_isChernClassFundamentalFamily
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (n : ℤ) :
    ∃ c : ∀ j : Fin (r + 1), chowGroup C sX (n - (j : ℤ)),
      IsChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n c :=
  exists_isChernCapFamily C sX sP π hsP r hπ hfac twist hsurj n _

/-- **Stacks 02U0, clause (1), uniqueness.** Granted the injectivity of the projective space
bundle map of Stacks 02TX there is at most one such family. -/
theorem eq_of_isChernClassFundamentalFamily
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist) (n : ℤ)
    {c d : ∀ j : Fin (r + 1), chowGroup C sX (n - (j : ℤ))}
    (hc : IsChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n c)
    (hd : IsChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n d) : c = d :=
  eq_of_isChernCapFamily C sX sP π hsP r hπ hfac twist hinj n _ hc hd

/-- The family of Chern classes capped with the fundamental cycle, as a datum: a family together
with the proof that it satisfies clause (1) of Stacks 02U0. -/
abbrev ChernClassFundamentalFamily (n : ℤ) :=
  { c : ∀ j : Fin (r + 1), chowGroup C sX (n - (j : ℤ)) //
    IsChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n c }

/-- Granted the surjectivity of the projective space bundle map of Stacks 02TX the datum
exists. -/
theorem nonempty_chernClassFundamentalFamily
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (n : ℤ) :
    Nonempty (ChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n) :=
  let ⟨c, hc⟩ := exists_isChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist hsurj n
  ⟨⟨c, hc⟩⟩

/-- **Stacks 02U0, part (2).** The `i`-th Chern class of a finite locally free module of rank `r`,
capped with the fundamental cycle of `X`: `c_i(ℰ) ∩ [X] ∈ A_{n-i}(X)`, the `i`-th member of the
family of clause (1). -/
def chernClassCapFundamental (n : ℤ)
    (D : ChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n) (i : Fin (r + 1)) :
    chowGroup C sX (n - (i : ℤ)) :=
  D.1 i

/-- **Stacks 02U0, the normalisation `c_0(ℰ) ∩ [X] = [X]`.** The zeroth Chern class capped with
the fundamental cycle is the fundamental class itself. -/
theorem chernClassCapFundamental_zero (n : ℤ)
    (D : ChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n) :
    chowGroupCast C sX
        (show n - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = n from by simp)
        (chernClassCapFundamental C sX sP π hsP r hπ hfac twist n D ⟨0, Nat.zero_lt_succ r⟩) =
      QuotientAddGroup.mk' (rationalEquivalences C sX n)
        (cycleAssociatedToClosedSubscheme C sX (𝟙 X) n) :=
  D.2.1

/-- **Stacks 02U0, part (3).** The total Chern class of a finite locally free module of rank `r`,
capped with the fundamental cycle:

  `c(ℰ) ∩ [X] = c_0(ℰ) ∩ [X] + c_1(ℰ) ∩ [X] + … + c_r(ℰ) ∩ [X]`,

an element of the graded Chow group `A_*(X) = ⊕_k A_k(X)`. -/
def totalChernClassCapFundamental (n : ℤ)
    (D : ChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n) :
    ⨁ k : ℤ, chowGroup C sX k :=
  ∑ i : Fin (r + 1), DirectSum.of (fun k : ℤ => chowGroup C sX k) (n - (i : ℤ))
    (chernClassCapFundamental C sX sP π hsP r hπ hfac twist n D i)

/-- Granted the injectivity of the projective space bundle map of Stacks 02TX, the datum is
unique. -/
theorem chernClassFundamentalFamily_unique
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist) (n : ℤ)
    (D D' : ChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n) : D = D' :=
  Subtype.ext
    (eq_of_isChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist hinj n D.2 D'.2)

/-- The total Chern class capped with the fundamental cycle is determined by the two clauses of
Stacks 02U0, granted the injectivity of the map of Stacks 02TX. -/
theorem totalChernClassCapFundamental_unique
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist) (n : ℤ)
    (D D' : ChernClassFundamentalFamily C sX sP π hsP r hπ hfac twist n) :
    totalChernClassCapFundamental C sX sP π hsP r hπ hfac twist n D =
      totalChernClassCapFundamental C sX sP π hsP r hπ hfac twist n D' := by
  rw [chernClassFundamentalFamily_unique C sX sP π hsP r hπ hfac twist hinj n D D']

end Stacks.Chow

end
