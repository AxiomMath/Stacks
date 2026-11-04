module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassSeriesOfModule
public import StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction

/-!
# The total Chern class datum of Stacks 0FEL, built from the Chern cap products

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be a scheme locally of finite type over `S`. `Stacks.Chow.TotalChernClassSeries` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` is the datum out of which the Chern class
map `c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` of Stacks 0FEL is built. It is a *parameter* of every
theorem there and of every module downstream of it, and nothing in this repository supplies one.
This file supplies five of its six fields from the Chern classes of Stacks 0B7H that this
repository constructs, and isolates exactly what is left.

## What is built

* `Stacks.Chow.ChowCohomologySeriesRing.one_apply_zero` — **the degree-`0` part of the unit
  series is forced.** For any series ring whose degreewise product is the product of Stacks 0B7E,
  `R.one 0` is the identity class `1 ∈ A^0(X)` of `Stacks.Chow.chowCohomologyUnit`. The
  implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` record `R.one 0`
  as *unconstrained*, "the only condition on the unit series being `one_apply_succ`"; it is not.
  The unit law of the Cauchy product pins its degree-`0` coefficient as a left unit for the
  degreewise product, the product of Stacks 0B7E has `1 ∈ A^0(X)` as a right unit, and a left
  unit and a right unit of one operation agree.
* `Stacks.Chow.ChernCapData` — the Chern cap products of Stacks 0B7G together with the
  properties of them that the Chern classes of Stacks 0B7H are built against: the three
  naturality clauses of Stacks 0B76 for the induced identity cap rules, the normalisation
  `c_0 = 1` of Stacks 02U0, and well-definedness of the rank. Every field is a property of the
  genuine cap products; see the implementation notes.
* `Stacks.Chow.ChernCapData.ch` — the total Chern class of an **arbitrary** module: the series
  `Stacks.Chow.chernClassSeriesOfRank` of bivariant Chern classes of Stacks 0B7H at the module's
  rank when it has one, and the unit series when it has none.
* `Stacks.Chow.ChernCapData.ch_isChernClass`, `Stacks.Chow.ChernCapData.ch_apply_zero`,
  `Stacks.Chow.ChernCapData.ch_eq_one_of_not_isFiniteLocallyFree` — three of the six fields of
  `Stacks.Chow.TotalChernClassSeries`, discharged.
* `Stacks.Chow.ChernCapData.totalChernClassSeriesOf` — **the construction**: a term of
  `Stacks.Chow.TotalChernClassSeries`, carrying
  `Stacks.Chow.ChernCapData.WhitneyProductForm` and nothing else. This is the first term of that
  structure built anywhere in this repository; every theorem of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` and of the modules downstream of it takes
  one as a parameter, and until now nothing supplied one.
* `Stacks.Chow.ChernCapData.nonempty_totalChernClassSeries_iff_whitneyProductForm` — **the
  obstruction, exactly**: such a datum exists if and only if the Whitney sum formula of Stacks
  02UI holds for the constructed total Chern class in the product form.

## What is still missing, exactly

The one carried hypothesis is `Stacks.Chow.ChernCapData.WhitneyProductForm`, Stacks 02UI in the
source's product form `c(ℰ₂) = c(ℰ₁) c(ℰ₃)`. It is not a convenience that could be weakened away:
it *is* the field `ch_shortExact`, and that field is what makes the Chern class map of Stacks 0FEL
well defined on `K_0(Vect(X))` at all.

What would discharge it, and what stands in the way, is now precise. The repository's own Stacks
02UI is `Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact`, the relation read componentwise on
Chow groups between cap products; and — the point — it is stated about a
`Stacks.Chow.HigherChernCapRule` exactly like the field `cap` here, under the source's own two
inputs `hbase` (the relation at rank at most one) and `hsplit`
(`Stacks.Chow.HasChernSplitting`, the projective space bundle of `ℰ₁` with Stacks 02TX and
Stacks 02U8). The implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` say the step from there to the product form
needs the bivariant Chern classes of Stacks 0B7H, the degreewise product of Stacks 0FE0, and the
compatibility of the cap operation of a composite with the two cap operations, and that the last
two are unavailable. Two of those three are no longer missing: the degreewise product is
`Stacks.Chow.chowCohomologyGradedProductRule`, and the cap compatibility is
`Stacks.Chow.chowCohomologyMul_toIdentityCapRule`, which says the identity cap rule a product of
bivariant classes induces is the composite of the two rules. What is genuinely absent is the
pullback of a short exact sequence of finite locally free modules to an arbitrary test scheme:
a bivariant class is determined by its cap operation on every `g : T ⟶ X`
(`Stacks.Chow.BivariantClass.eq_of_toIdentityCapRule_eq`), so the componentwise relation has to be
applied to the pulled-back sequence on each `T`, and this repository proves short-exactness is
preserved only along a **flat** morphism of schemes
(`Stacks.WeilCohomology.shortExact_map_pullback`). The statement that does hold in general —
Stacks 0G6R, flatness of the quotient suffices — is present only at the ringed-topos level, as
`Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules`, with no bridge to
`AlgebraicGeometry.Scheme.Modules.pullback`.

A second, independent edge: `Stacks.Chow.ChernCapData.ch` is the Chern class series at a module's
*global* rank, so on a module with no global rank it is the unit series, and `WhitneyProductForm`
then asserts something about that. Non-constant rank is what the rank-locus assembly of Stacks
0ESW, `Stacks.Chow.chernClassArbitraryRank`, is for; identifying that assembly with
`Stacks.Chow.chernClass` on a module of globally constant rank is not proved here, so the
construction above is the globally-constant-rank reading.

## References

* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX]

/-! ### The degree-zero part of the unit series is forced -/

/-- **The degree-`0` coefficient of the unit series is the identity class.** For a series ring
of Stacks 0FEL whose degreewise product is the product of Stacks 0B7E, the degree-`0` coefficient
of its unit series is the identity class `1 ∈ A^0(X)`.

The implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` record `R.one 0`
as unconstrained, the only condition on the unit series being `one_apply_succ`. That is not so
once the degreewise product is known:
`Stacks.Chow.ChowCohomologySeriesRing.gradedMul_one_apply_zero` extracts from the unit law of the
Cauchy product that `R.one 0` is a left unit for the degreewise product,
`Stacks.Chow.chowCohomologyGradedProductRule_mul_one` says the identity class is a right unit for
it, and a left unit and a right unit of one operation are equal. -/
theorem ChowCohomologySeriesRing.one_apply_zero (R : ChowCohomologySeriesRing C G sX)
    (hiso : G.IsNaturalUnderInverseIso)
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso) :
    R.one 0 = chowCohomologyUnit C G sX hiso := by
  have h1 := R.gradedMul_one_apply_zero 0 (chowCohomologyUnit C G sX hiso)
  rw [hmul] at h1
  exact (chowCohomologyGradedProductRule_mul_one (sX := sX) hiso 0 (R.one 0)).symm.trans h1

/-! ### The Chern cap products and the properties the Chern classes are read against -/

/-- **The Chern cap products of Stacks 0B7G on `X`, with the properties of them that the
bivariant Chern classes of Stacks 0B7H are built against.**

`Stacks.Chow.HigherChernCapRule` is `chernClassCapOnChow` of Stacks 0B7G, and nothing in this
repository inhabits it: it is built in the source from the cap product on cycles of Stacks 02U5
and its invariance under rational equivalence, Stacks 02U7, and while Stacks 02U5 is constructed
here as `Stacks.Chow.chernClassCap`, that lands on cycles rather than on Chow groups and the
descent of Stacks 02U7 is not performed. So the cap products themselves are the field `cap`, which
is no loss: they are already the field `Stacks.Chow.TotalChernClassSeries.cap`.

The remaining fields are properties of those cap products, each of which the source has.

* `proper`, `flat`, `gysin` are the three naturality clauses of Stacks 0B76 for the identity cap
  rules `α ↦ c_j(g^*ℰ) ∩ α` the cap products induce. They are exactly the hypotheses
  `Stacks.Chow.chernClass` of Stacks 0FE1 carries, quantified over every module on `X` and every
  rank, and they are what makes the Chern class a bivariant class at all.
* `cap_zero` is the normalisation `c_0 = 1` of Stacks 02U0: capping with the degree-`0` Chern
  class is the identity, up to the transport of the degree `k = k - 0`. The implementation notes
  of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` single this out as the content the
  field `ch_apply_zero` needs and that a bare cap rule does not carry.
* `rank_eq` is well-definedness of the rank: a module that is finite locally free of rank `r` and
  of rank `r'` has `r = r'`. It is needed because the total Chern class has to be defined on every
  module at once while the Chern classes of Stacks 0B7H are indexed by a rank, and it is the only
  field that is not a statement about `cap`. It holds whenever `X` is nonempty; the sole
  counterexample is `X = ∅`, over which every module has every rank. -/
structure ChernCapData (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] where
  /-- The Chern cap products of Stacks 0B7G, in every rank. -/
  cap : ∀ r : ℕ, HigherChernCapRule C r
  /-- **Stacks 0B76 (1)** for the induced identity cap rules. -/
  proper : ∀ (r : ℕ) (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (i : Fin (r + 1)),
    IdentityCapRule.ProperNaturality C sX (i : ℤ)
      (chernIdentityCapRuleOfRank C sX F r (cap r) i)
  /-- **Stacks 0B76 (2)** for the induced identity cap rules. -/
  flat : ∀ (r : ℕ) (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (i : Fin (r + 1)),
    IdentityCapRule.FlatNaturality C sX (i : ℤ)
      (chernIdentityCapRuleOfRank C sX F r (cap r) i)
  /-- **Stacks 0B76 (3)** for the induced identity cap rules. -/
  gysin : ∀ (r : ℕ) (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (i : Fin (r + 1)),
    IdentityCapRule.GysinNaturality C sX (i : ℤ)
      (chernIdentityCapRuleOfRank C sX F r (cap r) i) G
  /-- **The normalisation `c_0 = 1` of Stacks 02U0.** Capping with the degree-`0` Chern class is
  the identity, up to the transport of the degree. -/
  cap_zero : ∀ (r : ℕ) {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (k : ℤ)
    (α : chowGroup C q k),
    cap r q F k ⟨0, Nat.zero_lt_succ r⟩ α = chowGroupDegreeEquiv C q (sub_zero k).symm α
  /-- **The rank is well defined.** This holds for every nonempty `X`. -/
  rank_eq : ∀ (E : X.Modules) (r r' : ℕ),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r' → r = r'

namespace ChernCapData

variable (D : ChernCapData C G sX) (hiso : G.IsNaturalUnderInverseIso)
  (R : ChowCohomologySeriesRing C G sX)

/-- The Chern class series of a module that is finite locally free of a given rank, with the
naturality hypotheses supplied from the datum. The rank witness is an explicit argument rather
than an instance, so that the total Chern class below can be defined by a case split on whether
one exists. -/
def seriesOfRank (E : X.Modules) (r : ℕ)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    chowCohomologySeries C G sX :=
  letI := hr
  chernClassSeriesOfRank C sX E r G (D.cap r) (fun i => D.proper r E i) (fun i => D.flat r E i)
    (fun i => D.gysin r E i) hiso

/-- The Chern class series of the datum is the Chern class series of Stacks 0FE1. -/
theorem seriesOfRank_eq (E : X.Modules) (r : ℕ)
    [inst : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    D.seriesOfRank hiso E r inst =
      chernClassSeriesOfRank C sX E r G (D.cap r) (fun i => D.proper r E i)
        (fun i => D.flat r E i) (fun i => D.gysin r E i) hiso :=
  rfl

/-- The Chern class series at a rank depends only on the rank, which is what makes the total
Chern class below well defined. The two sides differ only in which proof of finite local freeness
of that rank is used, and that is a proof of a proposition. -/
theorem seriesOfRank_congr (E : X.Modules) (s r : ℕ) (hsr : s = r)
    (hs : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E s)
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    D.seriesOfRank hiso E s hs = D.seriesOfRank hiso E r hr := by
  subst hsr
  rfl

attribute [local instance] Classical.propDecidable

/-- **The total Chern class of an arbitrary module.** The series
`c(ℰ) = 1 + c_1(ℰ) + c_2(ℰ) + ⋯` of bivariant Chern classes of Stacks 0B7H at the rank of `ℰ`
when `ℰ` has a rank, and the unit series otherwise.

The second case is the normalisation `AlgebraicGeometry.VectorBundleKZero.classOf` uses, and is
not a mathematical assumption: a module with no global rank is not in the image of the generators
of `K_0(Vect(X))` that the Chern class map is defined on. -/
def ch (E : X.Modules) : chowCohomologySeries C G sX :=
  if h : ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r then
    D.seriesOfRank hiso E h.choose h.choose_spec
  else R.one

/-- On a module of rank `r` the total Chern class is the Chern class series at that rank. -/
theorem ch_eq_seriesOfRank (E : X.Modules) (r : ℕ)
    [inst : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    D.ch hiso R E = D.seriesOfRank hiso E r inst := by
  have hex : ∃ s : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E s := ⟨r, inst⟩
  have h1 : D.ch hiso R E = D.seriesOfRank hiso E hex.choose hex.choose_spec := dif_pos hex
  rw [h1]
  exact D.seriesOfRank_congr hiso E hex.choose r
    (D.rank_eq E hex.choose r hex.choose_spec inst) hex.choose_spec inst

/-- A module with no global rank gets the unit series. -/
theorem ch_eq_one_of_forall_not (E : X.Modules)
    (h : ∀ r : ℕ, ¬ AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    D.ch hiso R E = R.one :=
  dif_neg (fun hex => h hex.choose hex.choose_spec)

/-! ### Three fields of the total Chern class datum -/

/-- **The field `ch_isChernClass`, discharged.** The degree-`j` component of the total Chern class
of a module of rank `r` satisfies the characterization of Stacks 0B7H for `j ≤ r`, so it *is* the
`j`-th bivariant Chern class; by `Stacks.Chow.eq_of_isChernClassBivariant` that determines it. -/
theorem ch_isChernClass (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hrank : PullbackPreservesRank E r) (j : Fin (r + 1)) :
    IsChernClassBivariant C sX E r G (D.cap r) hrank j (D.ch hiso R E (j : ℕ)) := by
  rw [D.ch_eq_seriesOfRank hiso R E r, D.seriesOfRank_eq hiso E r]
  exact isChernClassBivariant_chernClassSeriesOfRank C sX E r G (D.cap r)
    (fun i => D.proper r E i) (fun i => D.flat r E i) (fun i => D.gysin r E i) hiso j

/-- **The normalisation `c_0 = 1` as a characterization of the identity class.** The identity
class `1 ∈ A^0(X)` satisfies the characterization of Stacks 0B7H in degree `0`, for any module of
any rank. This is exactly the content of the field
`Stacks.Chow.ChernCapData.cap_zero`, Stacks 02U0, read as a statement about bivariant classes. -/
theorem isChernClassBivariant_chowCohomologyUnit (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hrank : PullbackPreservesRank E r) :
    IsChernClassBivariant C sX E r G (D.cap r) hrank ⟨0, Nat.zero_lt_succ r⟩
      (chowCohomologyUnit C G sX hiso) := by
  intro T g _ k α
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) r := hrank g
  rw [D.cap_zero r (g ≫ sX) ((Scheme.Modules.pullback g).obj E) k α]
  exact chowCohomologyUnit_toIdentityCapRule C G sX hiso g k α

/-- **The field `ch_apply_zero`, discharged.** The constant term of the total Chern class of a
module of rank `r` is the degree-`0` coefficient of the unit series. Both are the identity class
`1 ∈ A^0(X)`: on the left by the normalisation `c_0 = 1` of Stacks 02U0 together with the
uniqueness in Stacks 0B7H, on the right by
`Stacks.Chow.ChowCohomologySeriesRing.one_apply_zero`. -/
theorem ch_apply_zero_of_rank
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso) (E : X.Modules)
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    D.ch hiso R E 0 = R.one 0 := by
  rw [R.one_apply_zero hiso hmul]
  have hrank : PullbackPreservesRank E r := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank E r
  exact eq_of_isChernClassBivariant C sX E r G (D.cap r) hrank ⟨0, Nat.zero_lt_succ r⟩
    (D.ch_isChernClass hiso R E r hrank ⟨0, Nat.zero_lt_succ r⟩)
    (D.isChernClassBivariant_chowCohomologyUnit hiso E r hrank)

/-- **The field `ch_apply_zero`, discharged in general.** On a module with no global rank the
total Chern class is the unit series by definition. -/
theorem ch_apply_zero (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (E : X.Modules) : D.ch hiso R E 0 = R.one 0 := by
  by_cases h : ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r
  · obtain ⟨r, hr⟩ := h
    let := hr
    exact D.ch_apply_zero_of_rank hiso R hmul E r
  · rw [D.ch_eq_one_of_forall_not hiso R E (not_exists.mp h)]

/-- **The field `ch_eq_one_of_not_isFiniteLocallyFree`, discharged.** A module that is not finite
locally free has no global rank, since a module of a fixed finite rank is finite locally free, so
it gets the unit series by definition. -/
theorem ch_eq_one_of_not_isFiniteLocallyFree (E : X.Modules)
    (hE : ¬ Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    D.ch hiso R E = R.one := by
  refine D.ch_eq_one_of_forall_not hiso R E fun r inst => hE ?_
  have hL : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
        X.ringCatSheaf.property) E r := inst
  exact
    Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      X.sheaf.obj X.ringCatSheaf.property E r

/-! ### The datum of Stacks 0FEL, and the one field that is left -/

/-- **The Whitney sum formula of Stacks 02UI in the product form Stacks 0FEL asks for**, read at
the total Chern class built above: a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ₂ ⟶ ℰ₃ ⟶ 0` of finite
locally free modules gives `c(ℰ₂) = c(ℰ₁) c(ℰ₃)` for the Cauchy product.

This is the one field of `Stacks.Chow.TotalChernClassSeries` that is not discharged above. The
repository's own Stacks 02UI, `Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact`, is the relation
read componentwise on Chow groups between cap products, and is stated about a
`Stacks.Chow.HigherChernCapRule` exactly like the field `cap` here; what stands between it and
this product form is the identification of the cap operation of a product of bivariant classes
with the composite of the two cap operations — available as
`Stacks.Chow.chowCohomologyMul_toIdentityCapRule` — together with the pullback of a short exact
sequence of finite locally free modules to each test scheme, which this repository has only for a
flat morphism of schemes (`Stacks.WeilCohomology.shortExact_map_pullback`) and not for the
arbitrary test scheme `g : T ⟶ X` that a bivariant class quantifies over. -/
def WhitneyProductForm : Prop :=
  ∀ {E₁ E₂ E₃ : X.Modules} (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (w : f ≫ g = 0),
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₁ →
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₂ →
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E₃ →
          Mono f → Epi g → (CategoryTheory.ShortComplex.mk f g w).Exact →
            D.ch hiso R E₂ = chowSeriesMul R.gradedMul (D.ch hiso R E₁) (D.ch hiso R E₃)

/-- **The datum of Stacks 0FEL, constructed.** A term of
`Stacks.Chow.TotalChernClassSeries` whose cap products are the given ones and whose total Chern
class is the series of bivariant Chern classes of Stacks 0B7H, carrying the Whitney sum formula
of Stacks 02UI and nothing else.

This is the first term of that structure built anywhere in this repository: every theorem of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` and of the modules downstream of it takes
one as a parameter, and until now nothing supplied one. Of its six fields, `cap` is the datum of
`Stacks.Chow.ChernCapData` — which is no loss, since it is the same field — `ch` is
`Stacks.Chow.ChernCapData.ch`, and `ch_apply_zero`, `ch_isChernClass` and
`ch_eq_one_of_not_isFiniteLocallyFree` are the three theorems above. Only
`Stacks.Chow.ChernCapData.WhitneyProductForm` is carried. -/
def totalChernClassSeriesOf
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hw : D.WhitneyProductForm hiso R) : TotalChernClassSeries C G sX R where
  cap := D.cap
  ch := D.ch hiso R
  ch_apply_zero := D.ch_apply_zero hiso R hmul
  ch_isChernClass := fun E r inst hrank j =>
    letI := inst
    D.ch_isChernClass hiso R E r hrank j
  ch_eq_one_of_not_isFiniteLocallyFree := D.ch_eq_one_of_not_isFiniteLocallyFree hiso R
  ch_shortExact := hw

@[simp] theorem totalChernClassSeriesOf_cap
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hw : D.WhitneyProductForm hiso R) :
    (D.totalChernClassSeriesOf hiso R hmul hw).cap = D.cap := rfl

@[simp] theorem totalChernClassSeriesOf_ch
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso)
    (hw : D.WhitneyProductForm hiso R) :
    (D.totalChernClassSeriesOf hiso R hmul hw).ch = D.ch hiso R := rfl

/-- Any datum of Stacks 0FEL whose total Chern class is the constructed one satisfies the Whitney
sum formula for it: that is its field `ch_shortExact`. -/
theorem whitneyProductForm_of_ch_eq (T : TotalChernClassSeries C G sX R)
    (hch : T.ch = D.ch hiso R) : D.WhitneyProductForm hiso R :=
  fun f g w h₁ h₂ h₃ hm he hex => hch ▸ T.ch_shortExact f g w h₁ h₂ h₃ hm he hex

/-- **The obstruction, exactly.** A `Stacks.Chow.TotalChernClassSeries` whose cap products are
the given ones and whose total Chern class is the series of bivariant Chern classes of Stacks
0B7H exists **if and only if** the Whitney sum formula of Stacks 02UI holds for that series in
the product form.

Everything else the structure asks for is discharged above, from the Chern classes of Stacks 0B7H
that this repository constructs; and the Whitney formula cannot be weakened away, because it *is*
the field `ch_shortExact`, which is what makes the Chern class map of Stacks 0FEL well defined on
`K_0(Vect(X))` in the first place. -/
theorem nonempty_totalChernClassSeries_iff_whitneyProductForm
    (hmul : R.gradedMul = chowCohomologyGradedProductRule (sX := sX) hiso) :
    (∃ T : TotalChernClassSeries C G sX R, T.cap = D.cap ∧ T.ch = D.ch hiso R) ↔
      D.WhitneyProductForm hiso R :=
  ⟨fun ⟨T, _, hch⟩ => D.whitneyProductForm_of_ch_eq hiso R T hch,
    fun hw => ⟨D.totalChernClassSeriesOf hiso R hmul hw, rfl, rfl⟩⟩

end ChernCapData

end Stacks.Chow

end
