module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIso
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence

/-!
# Flat pullback along a vector bundle projection of positive rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℰ` be a finite locally free sheaf of rank `r ≥ 1` on `X` and let
`p : E = Spec(Sym^*(ℰ)) ⟶ X` be the associated vector bundle. Then

  `p^* : CH_k(X) ⟶ CH_{k+r}(E)`

is an isomorphism for every `k`.

Write `π : P = P(ℰ ⊕ 𝒪_X) ⟶ X` for the projective space bundle of `ℰ ⊕ 𝒪_X`, in which `E` is the
complement of the divisor at infinity `D = P(ℰ)`, with closed immersion `i : D ⟶ P` and open
immersion `j : E ⟶ P`. The localization sequence

  `CH_{k+r}(D) --i_*--> CH_{k+r}(P) --j^*--> CH_{k+r}(E) ⟶ 0`

and the projective space bundle formula identify the cokernel of `i_*` with the summand
`CH_k(X)` of `CH_{k+r}(P) = ⨁_{i=0}^{r} CH_{k+i}(X)`. The bundles `P` and `D`, the first Chern
class operators of `𝒪_P(1)` and `𝒪_D(1)` and the projective space bundle formula enter as
parameters, and the compatibility of `i_*` with the two decompositions as the hypothesis
`Stacks.Chow.PushforwardShiftsSummands`.

## Main definitions

* `Stacks.Chow.completionTerm`: the `i`-th summand `c₁(𝒪_P(1))^i ∩ π^*(-)` of the relation for
  `P`, read at the level `n` and transported to a single degree `d`.
* `Stacks.Chow.infinityTerm`: the `j`-th summand `c₁(𝒪_D(1))^j ∩ π_D^*(-)` of the relation for
  `D`, transported to the same degree `d`.
* `Stacks.Chow.completionPullbackTerm`: the zeroth summand for `P`, with its source written in the
  base degree `k`.
* `Stacks.Chow.extendByZero`, `Stacks.Chow.baseFamily`: a family for `D` extended by zero in the
  summand `i = 0`, and a family concentrated in that summand.

## Main results

* `Stacks.Chow.bijective_sum_completionTerm`: the sum of the `r + 1` summands for `P` is a
  bijection from the family of Chow groups of `X`.
* `Stacks.Chow.pushforward_sum_infinityTerm`: pushing a family for `D` forward along `i` gives the
  family for `P` extended by zero in the summand `i = 0`.
* `Stacks.Chow.bijective_chowGroupOpensRestrict_comp_completionPullbackTerm`: the composite
  `j^* ∘ π^*` of the zeroth summand for `P` with the restriction to the complement of `D` is
  bijective.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Reindexing the summands -/

/-- The degree that the `j`-th summand of the relation for a rank-`r` bundle reads is the degree
that the `(j+1)`-st summand for a rank-`r + 1` bundle reads. -/
theorem sub_natCast_succ_sub_succ (r : ℕ) (n : ℤ) (j : Fin r) :
    n - ((r - j.val : ℕ) : ℤ) = n - ((r + 1 - (j.succ : Fin (r + 1)).val : ℕ) : ℤ) := by
  rw [Fin.val_succ]
  omega

/-- The degree that the zeroth summand of the relation for a rank-`r + 1` bundle reads. -/
theorem sub_natCast_zero_eq (r : ℕ) (n : ℤ) :
    n - ((r + 1 - (0 : Fin (r + 1)).val : ℕ) : ℤ) = n - ((r + 1 : ℕ) : ℤ) := by
  simp

/-! ### The zeroth summand is the flat pullback -/

/-- Capping zero times with a first Chern class is the identity, up to the transport of the
degree `k + 0` to `k`. -/
theorem iteratedChernCapOnChow_replicate_zero (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (O : ChernCapOperator C q) (k : ℤ)
    (x : chowGroup C q (k + (((List.replicate 0 O).length : ℕ) : ℤ))) :
    iteratedChernCapOnChow C q (List.replicate 0 O) k x =
      chowGroupCast C q
        (show k + (((List.replicate 0 O).length : ℕ) : ℤ) = k from by simp) x := by
  have key : ∀ (m : ℤ) (hm : m = k) (y : chowGroup C q m),
      chowGroupDegreeCast C q hm (AddMonoidHom.id (chowGroup C q k)) y =
        chowGroupCast C q hm y := by
    rintro m rfl y
    rfl
  exact key _ (by simp) x

/-- The zeroth summand of the projective bundle relation is the flat pullback composed with a
single transport of degrees. -/
theorem projectiveBundleChernTerm_zero (C : ChowSituation.{u}) {X P : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP) (ρ : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π (ρ - 1))
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (ρ - 1) hπ k)
    (twist : ChernCapOperator C sP) (k : ℤ) (h0 : 0 ≤ ρ)
    (α : chowGroup C sX (k - ((ρ - 0 : ℕ) : ℤ))) :
    projectiveBundleChernTerm C sX sP π hsP ρ hπ hfac twist k 0 h0 α =
      chowGroupCast C sP
        (show k - ((ρ - 0 : ℕ) : ℤ) + ((ρ - 1 : ℕ) : ℤ) =
            k + ((ρ - 1 : ℕ) : ℤ) - (ρ : ℤ) from by omega)
        (projectiveBundlePullback C sX sP π hsP ρ hπ hfac (k - ((ρ - 0 : ℕ) : ℤ)) α) := by
  rw [show projectiveBundleChernTerm C sX sP π hsP ρ hπ hfac twist k 0 h0 α =
      iteratedChernCapOnChow C sP (List.replicate 0 twist)
        (k + ((ρ - 1 : ℕ) : ℤ) - (ρ : ℤ))
        (chowGroupCast C sP
          (show k - ((ρ - 0 : ℕ) : ℤ) + ((ρ - 1 : ℕ) : ℤ) =
              k + ((ρ - 1 : ℕ) : ℤ) - (ρ : ℤ) + ((List.replicate 0 twist).length : ℤ) from by
            simp only [List.length_replicate]
            omega)
          (projectiveBundlePullback C sX sP π hsP ρ hπ hfac (k - ((ρ - 0 : ℕ) : ℤ)) α)) from rfl,
    iteratedChernCapOnChow_replicate_zero, chowGroupCast_chowGroupCast]

section Summands

variable (C : ChowSituation.{u}) {X P D : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
  (πD : D ⟶ X) [LocallyOfFiniteType πD] [Flat πD] (hsD : πD ≫ sX = sD)
  (r : ℕ)
  (hπ : AlgebraicGeometry.RelativeDimension π (r + 1 - 1))
  (hfac : ∀ k : ℤ,
    FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r + 1 - 1) hπ k)
  (twist : ChernCapOperator C sP)
  (hπD : AlgebraicGeometry.RelativeDimension πD (r - 1))
  (hfacD : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sD sX πD hsD (r - 1) hπD k)
  (twistD : ChernCapOperator C sD)

/-- The `i`-th summand `c₁(𝒪_P(1))^i ∩ π^*(-)` of the projective bundle relation for
`P = P(ℰ ⊕ 𝒪_X)`, a bundle of rank `r + 1`, read at the level `n` and transported to the
degree `d`. -/
def completionTerm (n d : ℤ)
    (hd : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d) (i : Fin (r + 1)) :
    chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ)) →+ chowGroup C sP d :=
  (chowGroupCast C sP hd).toAddMonoidHom.comp
    (projectiveBundleChernTerm C sX sP π hsP (r + 1) hπ hfac twist n i.val i.isLt.le)

/-- The `j`-th summand `c₁(𝒪_D(1))^j ∩ π_D^*(-)` of the projective bundle relation for the
divisor at infinity `D = P(ℰ)`, a bundle of rank `r`, read at the level `n` and transported to the
degree `d`. -/
def infinityTerm (n d : ℤ) (hd : n + ((r - 1 : ℕ) : ℤ) - (r : ℤ) = d) (j : Fin r) :
    chowGroup C sX (n - ((r - j.val : ℕ) : ℤ)) →+ chowGroup C sD d :=
  (chowGroupCast C sD hd).toAddMonoidHom.comp
    (projectiveBundleChernTerm C sX sD πD hsD r hπD hfacD twistD n j.val j.isLt.le)

/-- The zeroth summand for `P`, which is `π^*` up to the degree transports, with its source
written in the base degree `k`. -/
def completionPullbackTerm (n d k : ℤ)
    (hd : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d)
    (hk : k = n - ((r + 1 - (0 : Fin (r + 1)).val : ℕ) : ℤ)) :
    chowGroup C sX k →+ chowGroup C sP d :=
  (completionTerm C sX sP π hsP r hπ hfac twist n d hd 0).comp
    (chowGroupCast C sX hk).toAddMonoidHom

/-- A family of Chow classes indexed by the summands for `D`, extended by zero in the summand
`i = 0` to a family indexed by the summands for `P`. -/
def extendByZero (n : ℤ) (γ : ∀ j : Fin r, chowGroup C sX (n - ((r - j.val : ℕ) : ℤ)))
    (i : Fin (r + 1)) : chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ)) :=
  Fin.cases 0 (fun j ↦ chowGroupCast C sX (sub_natCast_succ_sub_succ r n j) (γ j)) i

/-- The family of Chow classes concentrated in the summand `i = 0`. -/
def baseFamily (n : ℤ) (α : chowGroup C sX (n - ((r + 1 - (0 : Fin (r + 1)).val : ℕ) : ℤ)))
    (i : Fin (r + 1)) : chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ)) :=
  Fin.cases α 0 i

/-- A family of Chow classes indexed by the summands for `P`, with the summand `i = 0` replaced by
zero. -/
def tailFamily (n : ℤ)
    (β : ∀ i : Fin (r + 1), chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ)))
    (i : Fin (r + 1)) : chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ)) :=
  Fin.cases 0 (fun j ↦ β j.succ) i

/-- Every family of Chow classes indexed by the summands for `P` is the sum of its zeroth entry
and its tail. -/
theorem baseFamily_add_tailFamily (n : ℤ)
    (β : ∀ i : Fin (r + 1), chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ)))
    (i : Fin (r + 1)) :
    β i = baseFamily C sX r n (β 0) i + tailFamily C sX r n β i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [baseFamily, tailFamily, Fin.cases_zero, add_zero]
  · simp only [baseFamily, tailFamily, Fin.cases_succ, Pi.zero_apply, zero_add]

/-! ### The normalized projective space bundle maps -/

/-- The sum of the normalized summands for `P` is the projective space bundle map followed by the
degree transport. -/
theorem sum_completionTerm (n d : ℤ)
    (hd : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d)
    (β : ∀ i : Fin (r + 1), chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ))) :
    ∑ i : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hd i (β i) =
      chowGroupCast C sP hd (∑ i : Fin (r + 1),
        projectiveBundleChernTerm C sX sP π hsP (r + 1) hπ hfac twist n i.val i.isLt.le
          (β i)) := by
  rw [map_sum]
  rfl

/-- The sum of the normalized summands for `D` is the projective space bundle map for `D` followed
by the degree transport. -/
theorem sum_infinityTerm (n d : ℤ) (hd : n + ((r - 1 : ℕ) : ℤ) - (r : ℤ) = d)
    (γ : ∀ j : Fin r, chowGroup C sX (n - ((r - j.val : ℕ) : ℤ))) :
    ∑ j : Fin r, infinityTerm C sX sD πD hsD r hπD hfacD twistD n d hd j (γ j) =
      chowGroupCast C sD hd (∑ j : Fin r,
        projectiveBundleChernTerm C sX sD πD hsD r hπD hfacD twistD n j.val j.isLt.le
          (γ j)) := by
  rw [map_sum]
  rfl

/-- Granted both halves of the projective space bundle formula for `P`, the sum of the `r + 1`
normalized summands is a bijection

  `⨁_{i=0}^{r} A_{k+i}(X) ⟶ A_{k+r}(P)`. -/
theorem bijective_sum_completionTerm
    (hinjP : ProjectiveBundleRelationInjective C sX sP π hsP (r + 1) hπ hfac twist)
    (hsurjP : ProjectiveBundleRelationSurjective C sX sP π hsP (r + 1) hπ hfac twist)
    (n d : ℤ) (hd : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d) :
    Function.Bijective
      fun β : (∀ i : Fin (r + 1), chowGroup C sX (n - ((r + 1 - i.val : ℕ) : ℤ))) ↦
        ∑ i : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hd i (β i) := by
  convert (chowGroupCast C sP hd).bijective.comp ⟨hinjP n, hsurjP n⟩ using 1
  exact funext fun β ↦ sum_completionTerm C sX sP π hsP r hπ hfac twist n d hd β

/-- Granted the surjectivity half of the projective space bundle formula for `D`, every class on
`D` is a sum of normalized summands. -/
theorem surjective_sum_infinityTerm
    (hsurjD : ProjectiveBundleRelationSurjective C sX sD πD hsD r hπD hfacD twistD)
    (n d : ℤ) (hd : n + ((r - 1 : ℕ) : ℤ) - (r : ℤ) = d) :
    Function.Surjective
      fun γ : (∀ j : Fin r, chowGroup C sX (n - ((r - j.val : ℕ) : ℤ))) ↦
        ∑ j : Fin r, infinityTerm C sX sD πD hsD r hπD hfacD twistD n d hd j (γ j) := by
  convert (chowGroupCast C sD hd).surjective.comp (hsurjD n) using 1
  exact funext fun γ ↦ sum_infinityTerm C sX sD πD hsD r hπD hfacD twistD n d hd γ

/-- The family concentrated in the summand `i = 0` is sent by the projective space bundle map to
the zeroth summand alone. -/
theorem sum_completionTerm_baseFamily (n d : ℤ)
    (hd : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d)
    (α : chowGroup C sX (n - ((r + 1 - (0 : Fin (r + 1)).val : ℕ) : ℤ))) :
    ∑ i : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hd i
        (baseFamily C sX r n α i) =
      completionTerm C sX sP π hsP r hπ hfac twist n d hd 0 α := by
  rw [Fin.sum_univ_succ]
  simp only [baseFamily, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, map_zero,
    Finset.sum_const_zero, add_zero]

end Summands

/-! ### The image of the pushforward from the divisor at infinity -/

section Pushforward

variable (C : ChowSituation.{u}) {X P D : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
  (πD : D ⟶ X) [LocallyOfFiniteType πD] [Flat πD] (hsD : πD ≫ sX = sD)
  (r : ℕ)
  (hπ : AlgebraicGeometry.RelativeDimension π (r + 1 - 1))
  (hfac : ∀ k : ℤ,
    FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r + 1 - 1) hπ k)
  (twist : ChernCapOperator C sP)
  (hπD : AlgebraicGeometry.RelativeDimension πD (r - 1))
  (hfacD : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sD sX πD hsD (r - 1) hπD k)
  (twistD : ChernCapOperator C sD)
  (i : D ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sD)
  (n d : ℤ) (hdP : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d)
  (hdD : n + ((r - 1 : ℕ) : ℤ) - (r : ℤ) = d)

/-- The compatibility of the pushforward along the closed immersion of the divisor at infinity
with the two projective-bundle decompositions:

  `i_*(c₁(𝒪_D(1))^j ∩ π_D^* α) = c₁(𝒪_P(1))^{j+1} ∩ π^* α`. -/
def PushforwardShiftsSummands : Prop :=
  ∀ (j : Fin r) (α : chowGroup C sX (n - ((r - j.val : ℕ) : ℤ))),
    chowPushforwardOfIsClosedImmersion C sD sP i hi d
        (infinityTerm C sX sD πD hsD r hπD hfacD twistD n d hdD j α) =
      completionTerm C sX sP π hsP r hπ hfac twist n d hdP j.succ
        (chowGroupCast C sX (sub_natCast_succ_sub_succ r n j) α)

/-- Pushing a family of Chow classes
for the divisor at infinity forward along `i` gives the projective space bundle map of `P` applied
to that family extended by zero in the summand `i = 0`. -/
theorem pushforward_sum_infinityTerm
    (hpush : PushforwardShiftsSummands C sX sP sD π hsP πD hsD r hπ hfac twist hπD hfacD twistD
      i hi n d hdP hdD)
    (γ : ∀ j : Fin r, chowGroup C sX (n - ((r - j.val : ℕ) : ℤ))) :
    chowPushforwardOfIsClosedImmersion C sD sP i hi d
        (∑ j : Fin r, infinityTerm C sX sD πD hsD r hπD hfacD twistD n d hdD j (γ j)) =
      ∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l
        (extendByZero C sX r n γ l) := by
  rw [map_sum, Fin.sum_univ_succ]
  simp only [extendByZero, Fin.cases_zero, Fin.cases_succ, map_zero, zero_add]
  exact Finset.sum_congr rfl fun j _ ↦ hpush j (γ j)

end Pushforward

/-! ### Flat pullback along a vector bundle of positive rank -/

section Main

variable (C : ChowSituation.{u}) {X P D : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
  (πD : D ⟶ X) [LocallyOfFiniteType πD] [Flat πD] (hsD : πD ≫ sX = sD)
  (r : ℕ)
  (hπ : AlgebraicGeometry.RelativeDimension π (r + 1 - 1))
  (hfac : ∀ k : ℤ,
    FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r + 1 - 1) hπ k)
  (twist : ChernCapOperator C sP)
  (hπD : AlgebraicGeometry.RelativeDimension πD (r - 1))
  (hfacD : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sD sX πD hsD (r - 1) hπD k)
  (twistD : ChernCapOperator C sD)
  (i : D ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sD) (V : P.Opens)

/-- Let `π : P ⟶ X` carry the projective space bundle formula in rank `r + 1`, let `i : D ⟶ P` be
a closed immersion whose image is the complement of the open `V ⊆ P`, let `π_D : D ⟶ X` carry the
surjectivity half of the projective space bundle formula in rank `r`, and let the pushforward
along `i` shift the summands. Then the composite

  `A_k(X) --π^*--> A_{k+r}(P) --j^*--> A_{k+r}(V)`

of the zeroth summand for `P` with the restriction to `V` is bijective. -/
theorem bijective_chowGroupOpensRestrict_comp_completionPullbackTerm
    (hcomplement : Set.range i.base = (Set.range V.ι.base)ᶜ)
    (hinjP : ProjectiveBundleRelationInjective C sX sP π hsP (r + 1) hπ hfac twist)
    (hsurjP : ProjectiveBundleRelationSurjective C sX sP π hsP (r + 1) hπ hfac twist)
    (hsurjD : ProjectiveBundleRelationSurjective C sX sD πD hsD r hπD hfacD twistD)
    (n d k : ℤ) (hdP : n + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d)
    (hdD : n + ((r - 1 : ℕ) : ℤ) - (r : ℤ) = d)
    (hk : k = n - ((r + 1 - (0 : Fin (r + 1)).val : ℕ) : ℤ))
    (hpush : PushforwardShiftsSummands C sX sP sD π hsP πD hsD r hπ hfac twist hπD hfacD twistD
      i hi n d hdP hdD) :
    Function.Bijective ((chowGroupOpensRestrictOfIsOpenImmersion C sP V d).comp
      (completionPullbackTerm C sX sP π hsP r hπ hfac twist n d k hdP hk)) := by
  have hexact := exact_chowPushforward_chowGroupOpensRestrict C sP sD i hi V hcomplement d
  have hbijP := bijective_sum_completionTerm C sX sP π hsP r hπ hfac twist hinjP hsurjP n d hdP
  have hsurD := surjective_sum_infinityTerm C sX sD πD hsD r hπD hfacD twistD hsurjD n d hdD
  have hval : ∀ α : chowGroup C sX k,
      ((chowGroupOpensRestrictOfIsOpenImmersion C sP V d).comp
          (completionPullbackTerm C sX sP π hsP r hπ hfac twist n d k hdP hk)) α =
        chowGroupOpensRestrictOfIsOpenImmersion C sP V d
          (∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l
            (baseFamily C sX r n (chowGroupCast C sX hk α) l)) := fun α ↦ by
    rw [sum_completionTerm_baseFamily C sX sP π hsP r hπ hfac twist n d hdP]
    rfl
  have hker : ∀ β : (∀ l : Fin (r + 1), chowGroup C sX (n - ((r + 1 - l.val : ℕ) : ℤ))),
      chowGroupOpensRestrictOfIsOpenImmersion C sP V d
          (∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l (β l)) = 0 ↔
        ∃ γ : (∀ j : Fin r, chowGroup C sX (n - ((r - j.val : ℕ) : ℤ))),
          ∀ l : Fin (r + 1), β l = extendByZero C sX r n γ l := by
    intro β
    refine ⟨fun hzero ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
    · obtain ⟨δ, hδ⟩ := (hexact _).mp hzero
      obtain ⟨γ, hγ⟩ := hsurD δ
      have hγ' : ∑ j : Fin r,
          infinityTerm C sX sD πD hsD r hπD hfacD twistD n d hdD j (γ j) = δ := hγ
      have hfam : extendByZero C sX r n γ = β := by
        refine hbijP.1 ?_
        change ∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l
              (extendByZero C sX r n γ l) =
            ∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l (β l)
        rw [← pushforward_sum_infinityTerm C sX sP sD π hsP πD hsD r hπ hfac twist hπD hfacD
          twistD i hi n d hdP hdD hpush γ, hγ', hδ]
      exact ⟨γ, fun l ↦ (congrFun hfam l).symm⟩
    · refine (hexact _).mpr ⟨∑ j : Fin r,
        infinityTerm C sX sD πD hsD r hπD hfacD twistD n d hdD j (γ j), ?_⟩
      rw [pushforward_sum_infinityTerm C sX sP sD π hsP πD hsD r hπ hfac twist hπD hfacD twistD
        i hi n d hdP hdD hpush γ]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [hγ l]
  refine ⟨fun α α' hαα' ↦ ?_, fun q ↦ ?_⟩
  · rw [← sub_eq_zero] at hαα' ⊢
    have hsub : ((chowGroupOpensRestrictOfIsOpenImmersion C sP V d).comp
        (completionPullbackTerm C sX sP π hsP r hπ hfac twist n d k hdP hk)) (α - α') = 0 := by
      rw [map_sub, hαα']
    rw [hval (α - α')] at hsub
    obtain ⟨γ, hγ⟩ := (hker _).mp hsub
    have h0 := hγ 0
    simp only [baseFamily, extendByZero, Fin.cases_zero] at h0
    exact (chowGroupCast C sX hk).injective (h0.trans (map_zero _).symm)
  · obtain ⟨δ, hδ⟩ := surjective_chowGroupOpensRestrictOfIsOpenImmersion C sP V d q
    obtain ⟨β, hβ⟩ := hbijP.2 δ
    have hβ' : ∑ l : Fin (r + 1),
        completionTerm C sX sP π hsP r hπ hfac twist n d hdP l (β l) = δ := hβ
    have htail : chowGroupOpensRestrictOfIsOpenImmersion C sP V d
        (∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l
          (tailFamily C sX r n β l)) = 0 := by
      refine (hker _).mpr
        ⟨fun j ↦ (chowGroupCast C sX (sub_natCast_succ_sub_succ r n j)).symm (β j.succ),
          fun l ↦ ?_⟩
      refine Fin.cases ?_ (fun j ↦ ?_) l
      · simp only [tailFamily, extendByZero, Fin.cases_zero]
      · simp only [tailFamily, extendByZero, Fin.cases_succ, AddEquiv.apply_symm_apply]
    have hsplit : ∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l
          (β l) =
        (∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l
            (baseFamily C sX r n (β 0) l)) +
          ∑ l : Fin (r + 1), completionTerm C sX sP π hsP r hπ hfac twist n d hdP l
            (tailFamily C sX r n β l) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [baseFamily_add_tailFamily C sX r n β l, map_add]
    refine ⟨(chowGroupCast C sX hk).symm (β 0), ?_⟩
    rw [hval, AddEquiv.apply_symm_apply, ← hδ, ← hβ', hsplit, map_add, htail, add_zero]

end Main

end Stacks.Chow

end
