module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.ShortExactSequence
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactFlatScheme

/-!
# The Whitney product form, discharged from the componentwise Stacks 02UI

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. `Stacks.Chow.ChernCapData.totalChernClassSeriesOf`
of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataConstruction` builds a
`Stacks.Chow.TotalChernClassSeries` out of the Chern cap products of Stacks 0B7G, carrying
`Stacks.Chow.ChernCapData.WhitneyProductForm` — Stacks 02UI in the product form
`c(ℰ₂) = c(ℰ₁) c(ℰ₃)` — and nothing else, and
`Stacks.Chow.ChernCapData.nonempty_totalChernClassSeries_iff_whitneyProductForm` shows that
hypothesis is exactly the obstruction.

This file performs the passage from the repository's own Stacks 02UI,
`Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact`, to that product form, and discharges it.

## The passage

`Stacks.Chow.chowCohomologySeries` is a family of bivariant classes, and a bivariant class for
`𝟙 X` is determined by the identity cap rule it induces
(`Stacks.Chow.BivariantClass.eq_of_toIdentityCapRule_eq`). So the product form is an identity of
cap operations on each test scheme `g : T ⟶ X`, and the three steps that turn it into the
componentwise relation are:

* the rule induced by a Cauchy product coefficient is the sum over the antidiagonal of the rules
  induced by the degreewise products, by `Stacks.Chow.BivariantClass.toIdentityCapRule_add` and
  `_zero`;
* the rule induced by one degreewise product of Stacks 0B7E is the composite of the two rules,
  which is `Stacks.Chow.chowCohomologyMul_toIdentityCapRule`;
* the rule induced by the degree-`j` coefficient of the Chern class series of a module of rank `r`
  is cap with `c_j` of the module's pullback, extended by zero above the rank — that is
  `Stacks.Chow.chernCapFamilyOnChow` — by Stacks 0B7H,
  `Stacks.Chow.isChernClassBivariant_chernClassSeriesOfRank`.

After those three the identity to be proved on each `g : T ⟶ X` is the componentwise Whitney
relation for the sequence `g^*(0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0)` on `T`, up to the reflection of the
summation index. That sequence has to be short exact, and `g` is an arbitrary morphism, not a
flat one; it is short exact by Stacks 0G6R at the scheme level,
`AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree`, whose
hypothesis is flatness of the *quotient* and is met because the quotient is finite locally free.

## Main results

* `Stacks.Chow.ChernCapData.toIdentityCapRule_ch_apply` — the cap operation of the degree-`m`
  coefficient of the constructed total Chern class of a module of rank `r` is
  `Stacks.Chow.chernCapFamilyOnChow` at index `m`, in *every* degree `m`, including above the
  rank where both sides vanish.
* `Stacks.Chow.ChernCapData.toIdentityCapRule_chowSeriesTerm` — one term of the Cauchy product
  induces one summand of the convolution. This is the whole of the passage between the two forms.
* `Stacks.Chow.ChernCapData.ch_eq_chowSeriesMul_of_shortExact` — **the product form at globally
  constant ranks**, carrying only `hbase` and `hsplit`, the two inputs that
  `Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact` itself carries. Nothing about pullback is
  carried.
* `Stacks.Chow.ChernCapData.whitneyProductForm_of_forall_exists_rank` —
  `Stacks.Chow.ChernCapData.WhitneyProductForm` in full, on a nonempty `X` whose finite locally
  free modules have global ranks.
* `Stacks.Chow.ChernCapData.totalChernClassSeriesOfWhitney` — **the datum of Stacks 0FEL with the
  Whitney formula discharged.**

## Implementation notes

**What is still carried, and why none of it is about pullback.** Three things: `hbase`, the
componentwise relation when the sub-module has rank at most one; `hsplit`,
`Stacks.Chow.HasChernSplitting`; and, for the step from constant ranks to
`Stacks.Chow.ChernCapData.WhitneyProductForm` as stated, a point of `X` together with `hrank`,
the existence of a global rank for every finite locally free module. The first two are exactly
what the repository's Stacks 02UI carries and are not touched here.

**Why the rank hypothesis is not a weakening of convenience.**
`Stacks.Chow.ChernCapData.ch` is the Chern class series at a module's *global* rank and the unit
series on a module that has none, so `Stacks.Chow.ChernCapData.WhitneyProductForm` — which
quantifies over modules that are finite locally free without a constant rank — asserts in that
case that `c(ℰ₂) = 1 · c(ℰ₃)`, i.e. `c(ℰ₂) = c(ℰ₃)`. That is not what the componentwise relation
says and it is not implied by it: on `X = X₁ ⊔ X₂` a sub-module whose rank is `1` on `X₁` and `0`
on `X₂` has no global rank while the middle term can have one, and the relation then relates a
series read at the middle term's rank to the unit series. Splitting a module into its rank loci
is what `Stacks.Chow.chernClassArbitraryRank` of Stacks 0ESW is for, and identifying that
assembly with `Stacks.Chow.chernClass` on a module of globally constant rank is what would
discharge `hrank`; it is not proved in this repository.

**The point of `X`.** Rank additivity along the sequence,
`AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`, is read on a stalk and so needs a
point. It is not a new restriction: `Stacks.Chow.ChernCapData.rank_eq` already fails on `X = ∅`,
over which every module is finite locally free of every rank.

**The index reflection.** `Stacks.Chow.chowSeriesMul` sums over `Finset.antidiagonal m` with the
first coordinate the index of the sub-module, while `Stacks.Chow.convolve` sums over
`Finset.range (m + 1)` with the index of the *quotient* as the summation variable.
`Finset.sum_range_reflect` makes the translation.

**Nothing is added to an existing structure.** The results are theorems about the existing
`Stacks.Chow.ChernCapData` and `Stacks.Chow.TotalChernClassSeries`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange`: both occur as hypotheses of
tagged theorems, and a new field would strengthen those hypotheses and so weaken every one of
them.

## References

* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX]

/-! ### Transport lemmas for the induced identity cap rule -/

/-- Transport along an equality of degrees does not change the class. -/
private theorem gradedDegreeCast_heq_self (H : ℤ → Type*) [∀ k, AddCommGroup (H k)] {k l : ℤ}
    (h : k = l) (x : H k) : gradedDegreeCast H h x ≍ x := by
  subst h; rfl

/-- The composite of the two transports a product of bivariant classes introduces is one
transport. The equalities are variables and are substituted away, so no `Eq.rec` on a concrete
degree is ever elaborated. -/
private theorem gradedDegreeCast_chowGroupDegreeEquiv {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] {k l n : ℤ} (h : k = l) (h' : l = n) (x : chowGroup C q k) :
    gradedDegreeCast (chowGroup C q) h' (chowGroupDegreeEquiv C q h x) =
      gradedDegreeCast (chowGroup C q) (h.trans h') x :=
  eq_of_heq (((gradedDegreeCast_heq_self _ h' _).trans (chowGroupDegreeEquiv_heq C q h x)).trans
    (gradedDegreeCast_heq_self (chowGroup C q) (h.trans h') x).symm)

variable (C G sX)

/-- The rule a finite sum of bivariant classes induces is the sum of the rules they induce. -/
theorem BivariantClass.toIdentityCapRule_sum {p : ℤ} {ι : Type*} (t : Finset ι)
    (c : ι → chowCohomologyComponent C G sX p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX p (∑ i ∈ t, c i) g k α =
      ∑ i ∈ t, BivariantClass.toIdentityCapRule C G sX p (c i) g k α := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        BivariantClass.toIdentityCapRule_add C G sX p _ _ g k α, ih]

/-- The rule a class transported between components of equal degree induces is the rule of the
class, with the degrees of the values transported to match. -/
theorem BivariantClass.toIdentityCapRule_chowCohomologyDegreeCast {p p' : ℤ} (h : p = p')
    (c : chowCohomologyComponent C G sX p) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX p' (chowCohomologyDegreeCast h c) g k α =
      gradedDegreeCast (chowGroup C (g ≫ sX)) (by rw [h])
        (BivariantClass.toIdentityCapRule C G sX p c g k α) := by
  subst h; rfl

variable {C G sX}

/-! ### The cap operation of the constructed total Chern class -/

namespace ChernCapData

variable (D : ChernCapData C G sX) (hiso : G.IsNaturalUnderInverseIso)
  (R : ChowCohomologySeriesRing C G sX)

/-- **The cap operation of the degree-`m` coefficient of the constructed total Chern class.** On
a module `E` of rank `r` the rule induced by `D.ch E m` is cap with `c_m(g^*E)`, extended by zero
above the rank — that is `Stacks.Chow.chernCapFamilyOnChow` at index `m` — for *every* `m`.

Below the rank this is Stacks 0B7H for the Chern class series,
`Stacks.Chow.isChernClassBivariant_chernClassSeriesOfRank`, read through
`Stacks.Chow.BivariantClass.toIdentityCapRule_apply`. Above the rank both sides vanish, the
series by `Stacks.Chow.chernClassSeriesOfRank_apply_of_gt` and the family by
`Stacks.Chow.chernCapFamilyOnChow_of_gt`; that the two conventions agree is what lets the
Whitney relation be read at every index at once. -/
theorem toIdentityCapRule_ch_apply (E : X.Modules) (r : ℕ)
    [inst : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    [instP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) r]
    (k : ℤ) (m : ℕ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX (m : ℤ) (D.ch hiso R E m) g k α =
      chernCapFamilyOnChow C D.cap (g ≫ sX) ((Scheme.Modules.pullback g).obj E) r k m α := by
  by_cases hm : m < r + 1
  · rw [chernCapFamilyOnChow_of_le C D.cap (g ≫ sX) _ r k (Nat.lt_succ_iff.mp hm),
      BivariantClass.toIdentityCapRule_apply]
    exact D.ch_isChernClass hiso R E r
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r) ⟨m, hm⟩ g k α
  · have h0 : D.ch hiso R E m = 0 := by
      rw [D.ch_eq_seriesOfRank hiso R E r, D.seriesOfRank_eq hiso E r]
      exact chernClassSeriesOfRank_apply_of_gt C sX E r G (D.cap r) _ _ _ hiso m (by omega)
    rw [chernCapFamilyOnChow_of_gt C D.cap (g ≫ sX) _ r k (by omega), AddMonoidHom.zero_apply,
      h0, BivariantClass.toIdentityCapRule_zero]

/-! ### One term of the Cauchy product -/

/-- **One term of the Cauchy product, as a term of the convolution.** For `j ≤ m` the rule
induced by the degree-`(m - j, j)` term of the Cauchy product of the two total Chern classes is
the `j`-th summand of the convolution of the two Chern cap families.

This is the whole of the passage from the product form to the componentwise form: the degreewise
product of Stacks 0B7E induces the composite of the two rules
(`Stacks.Chow.chowCohomologyMul_toIdentityCapRule`), each of which is cap with a Chern class by
`Stacks.Chow.ChernCapData.toIdentityCapRule_ch_apply`, and the two transports of the degree that
the product and the composite introduce compose into the single one the convolution carries. -/
theorem toIdentityCapRule_chowSeriesTerm
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (E₁ E₃ : X.Modules) (r₁ r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₃ r₂]
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E₁) r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E₃) r₂]
    (k : ℤ) (m j : ℕ) (hj : j ≤ m) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX (m : ℤ)
        (chowSeriesTerm R.gradedMul (D.ch hiso R E₁) (D.ch hiso R E₃) m (m - j, j)) g k α =
      convolveTerm (chernCapFamilyOnChow C D.cap (g ≫ sX)
          ((Scheme.Modules.pullback g).obj E₁) r₁)
        (chernCapFamilyOnChow C D.cap (g ≫ sX) ((Scheme.Modules.pullback g).obj E₃) r₂)
        k m j α := by
  have hgp : ∀ (i j' n : ℕ) (h : i + j' = n)
      (x : chowCohomologyComponent C G sX (i : ℤ))
      (y : chowCohomologyComponent C G sX (j' : ℤ)),
      chowCohomologyGradedProductRule (sX := sX) hiso i j' n h x y =
        chowCohomologyDegreeCast (show (i : ℤ) + (j' : ℤ) = (n : ℤ) by omega)
          (chowCohomologyRingMul C G sX hiso x y) := fun _ _ _ _ _ _ => rfl
  rw [chowSeriesTerm_of_add R.gradedMul _ _ (show m - j + j = m from Nat.sub_add_cancel hj), hmul,
    hgp, BivariantClass.toIdentityCapRule_chowCohomologyDegreeCast,
    chowCohomologyMul_toIdentityCapRule, IdentityCapRule.comp_apply,
    gradedDegreeCast_chowGroupDegreeEquiv, convolveTerm_of_le _ _ k hj, capTo_def,
    D.toIdentityCapRule_ch_apply hiso R E₃ r₂ g k j α,
    D.toIdentityCapRule_ch_apply hiso R E₁ r₁ g (k - (j : ℤ)) (m - j) _]

/-! ### The Whitney product form at constant ranks -/

/-- **The Whitney sum formula of Stacks 02UI in the product form Stacks 0FEL asks for, at
globally constant ranks.** For a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` of finite locally
free modules of constant ranks `r₁`, `r₁ + r₂` and `r₂`, the total Chern class built in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataConstruction` satisfies
`c(ℰ₂) = c(ℰ₁) c(ℰ₃)` for the Cauchy product.

Carried, and only these: `hbase`, the componentwise relation when the sub-module has rank at
most one, and `hsplit`, `Stacks.Chow.HasChernSplitting` — the two inputs that the repository's
own Stacks 02UI, `Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact`, carries. Nothing about
pullback is carried: a bivariant class is determined by its cap operation on every test scheme
`g : T ⟶ X`, and the sequence pulled back to `T` is short exact by Stacks 0G6R at the scheme
level, `AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree` — `g`
is not flat, and does not need to be, because the quotient of the sequence is finite locally
free hence flat. -/
theorem ch_eq_chowSeriesMul_of_shortExact
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hbase : ∀ r₁ ≤ 1, WhitneyChernRelation C D.cap r₁) (hsplit : HasChernSplitting C D.cap)
    (s : ShortComplex X.Modules) (hs : s.ShortExact) (r₁ r₂ : ℕ)
    [i₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} s.X₁ r₁]
    [i₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} s.X₂ (r₁ + r₂)]
    [i₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} s.X₃ r₂] :
    D.ch hiso R s.X₂ = chowSeriesMul R.gradedMul (D.ch hiso R s.X₁) (D.ch hiso R s.X₃) := by
  have hflf₃ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      s.X₃ := by
    let hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
        X.ringCatSheaf.property) s.X₃ r₂ := i₃
    exact
      InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
        X.sheaf.obj X.ringCatSheaf.property s.X₃ r₂
  funext m
  refine BivariantClass.eq_of_toIdentityCapRule_eq C G sX (m : ℤ) ?_
  intro T g _ k α
  let p₁ := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g s.X₁ r₁
  let p₂ := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g s.X₂ (r₁ + r₂)
  let p₃ := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g s.X₃ r₂
  let q₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (s.map (Scheme.Modules.pullback g)).X₁ r₁ := p₁
  let q₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (s.map (Scheme.Modules.pullback g)).X₂ (r₁ + r₂) := p₂
  let q₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (s.map (Scheme.Modules.pullback g)).X₃ r₂ := p₃
  -- Stacks 0G6R: the sequence stays short exact on the test scheme, `g` not being flat.
  have hse : (s.map (Scheme.Modules.pullback g)).ShortExact :=
    AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree g s hs hflf₃
  have hw := whitneyChernRelation_of_hasChernSplitting C D.cap hbase hsplit r₁ (g ≫ sX)
    (s.map (Scheme.Modules.pullback g)) hse r₂
  have hcap : chernCapFamilyOnChow C D.cap (g ≫ sX) ((Scheme.Modules.pullback g).obj s.X₂)
        (r₁ + r₂) k m α =
      ∑ j ∈ Finset.range (m + 1), convolveTerm
        (chernCapFamilyOnChow C D.cap (g ≫ sX) ((Scheme.Modules.pullback g).obj s.X₁) r₁)
        (chernCapFamilyOnChow C D.cap (g ≫ sX) ((Scheme.Modules.pullback g).obj s.X₃) r₂)
        k m j α :=
    (DFunLike.congr_fun (congrFun (congrFun hw k) m) α).trans (convolve_apply _ _ k m α)
  rw [D.toIdentityCapRule_ch_apply hiso R s.X₂ (r₁ + r₂) g k m α,
    chowSeriesMul, BivariantClass.toIdentityCapRule_sum C G sX _ _ g k α,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine hcap.trans ((Finset.sum_range_reflect _ (m + 1)).symm.trans ?_)
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hterm := D.toIdentityCapRule_chowSeriesTerm hiso R hmul s.X₁ s.X₃ r₁ r₂ g k m (m - i)
    (by omega) α
  rw [Nat.sub_sub_self him] at hterm
  exact hterm.symm

/-! ### The Whitney product form in full, and the datum of Stacks 0FEL -/

/-- **`Stacks.Chow.ChernCapData.WhitneyProductForm` in full, on a nonempty scheme whose finite
locally free modules have global ranks.**

`Stacks.Chow.ChernCapData.WhitneyProductForm` quantifies over modules that are finite locally
free without a constant rank, and on such a module `Stacks.Chow.ChernCapData.ch` is the unit
series by definition; so the hypothesis `hrank` is not removable by any argument about Chern
classes — it is the statement that that case does not occur. Granted it, the ranks of the three
terms are additive by `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`, which is what
puts the middle term's rank in the form `r₁ + r₂` that the componentwise relation asks for, and
the constant-rank form above applies.

Carried: `hbase` and `hsplit`, the two inputs of the repository's Stacks 02UI; `x`, a point of
`X`, which rank additivity needs and which `Stacks.Chow.ChernCapData.rank_eq` already needs — on
`X = ∅` every module is finite locally free of every rank, so that field fails there; and
`hrank`. Splitting a module into its rank loci is what `Stacks.Chow.chernClassArbitraryRank` of
Stacks 0ESW is for, and identifying that assembly with `Stacks.Chow.chernClass` on a module of
globally constant rank is what would discharge `hrank`; it is not proved in this repository. -/
theorem whitneyProductForm_of_forall_exists_rank
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hbase : ∀ r₁ ≤ 1, WhitneyChernRelation C D.cap r₁) (hsplit : HasChernSplitting C D.cap)
    (x : X)
    (hrank : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    D.WhitneyProductForm hiso R := by
  intro E₁ E₂ E₃ f g w h₁ h₂ h₃ hm he hex
  obtain ⟨r₁, hr₁⟩ := hrank E₁ h₁
  obtain ⟨r₂, hr₂⟩ := hrank E₂ h₂
  obtain ⟨r₃, hr₃⟩ := hrank E₃ h₃
  let := hr₁
  let := hr₂
  let := hr₃
  have hS : (ShortComplex.mk f g w).ShortExact := ShortComplex.ShortExact.mk' hex hm he
  have hsum : r₂ = r₁ + r₃ :=
    AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact (ShortComplex.mk f g w) hS r₁ r₂ r₃ x
  subst hsum
  exact D.ch_eq_chowSeriesMul_of_shortExact hiso R hmul hbase hsplit (ShortComplex.mk f g w) hS
    r₁ r₃

/-- **The datum of Stacks 0FEL, with the Whitney sum formula discharged.** A term of
`Stacks.Chow.TotalChernClassSeries` whose cap products are the given ones and whose total Chern
class is the series of bivariant Chern classes of Stacks 0B7H, carrying no hypothesis about
pullback at all.

`Stacks.Chow.ChernCapData.totalChernClassSeriesOf` carries
`Stacks.Chow.ChernCapData.WhitneyProductForm`, which
`Stacks.Chow.ChernCapData.nonempty_totalChernClassSeries_iff_whitneyProductForm` shows is exactly
the obstruction; this discharges it from `hbase`, `hsplit`, a point of `X` and `hrank`. See
`Stacks.Chow.ChernCapData.whitneyProductForm_of_forall_exists_rank` for what each of those is and
why none of them is about pullback: that part is now Stacks 0G6R at the scheme level,
`AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree`. -/
def totalChernClassSeriesOfWhitney
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hbase : ∀ r₁ ≤ 1, WhitneyChernRelation C D.cap r₁) (hsplit : HasChernSplitting C D.cap)
    (x : X)
    (hrank : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    TotalChernClassSeries C G sX R :=
  D.totalChernClassSeriesOf hiso R hmul
    (D.whitneyProductForm_of_forall_exists_rank hiso R hmul hbase hsplit x hrank)

/-- The cap products of `Stacks.Chow.ChernCapData.totalChernClassSeriesOfWhitney` are those of
`D`. -/
@[simp] theorem totalChernClassSeriesOfWhitney_cap
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hbase : ∀ r₁ ≤ 1, WhitneyChernRelation C D.cap r₁) (hsplit : HasChernSplitting C D.cap)
    (x : X)
    (hrank : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    (D.totalChernClassSeriesOfWhitney hiso R hmul hbase hsplit x hrank).cap = D.cap := rfl

/-- The total Chern class of `Stacks.Chow.ChernCapData.totalChernClassSeriesOfWhitney` is the
series `Stacks.Chow.ChernCapData.ch` of bivariant Chern classes of `D`. -/
@[simp] theorem totalChernClassSeriesOfWhitney_ch
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hbase : ∀ r₁ ≤ 1, WhitneyChernRelation C D.cap r₁) (hsplit : HasChernSplitting C D.cap)
    (x : X)
    (hrank : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    (D.totalChernClassSeriesOfWhitney hiso R hmul hbase hsplit x hrank).ch = D.ch hiso R := rfl

end ChernCapData

end Stacks.Chow

end
