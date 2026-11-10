module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesUnwinding
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceLocalRing
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesLocallyFreeOutside
public import StacksFrontier.AlgebraicGeometry.Algebraization.ImmediateSpecializationHeightTwo
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkDepthSpecialization
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesCohomologicalDimensionOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthThree
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary

/-!
# Unwinding the `(2, 3)`-inequalities: the criterion at the dimension-one points

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`, and let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. Assume
`A` is local with `𝔞 = 𝔪` and that `cd(A, I) = 1`. Stacks 0EJA asserts that `(ℱ_n)` satisfies
the `(2, 3)`-inequalities if and only if

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2`

for every `y ∈ U ∩ Y` with `dim({y}‾) = 1` and every prime `𝔭 ⊆ 𝒪_{X,y}^∧` with
`𝔭 ∉ V(I𝒪_{X,y}^∧)`. **As published, with only those hypotheses, the statement is false**: the
"if" direction fails for a non-catenary `A/I` (see "The published statement is false" below).
This file proves the corrected statement, with `A/I` catenary added, and its special case for
`A` with a dualizing complex, the standing hypothesis of the neighbouring lemmas of the source.

## Main results

* `Stacks.Algebraization.satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim` — the
  corrected equivalence, both directions in one statement: `A/I` catenary, and the completed
  local rings at the points of `U ∩ Y` of dimension one universally catenary with
  Cohen--Macaulay formal fibres.
* `satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim_of_isDualizingComplex`
  — the same equivalence for `A` with a dualizing complex, which supplies all three of those
  properties.
* `Stacks.Algebraization.isUniversallyCatenary_and_isPRing_completedLocalRing` — a dualizing
  complex on `A` makes the completed local rings of `U` universally catenary with
  Cohen--Macaulay formal fibres.

## The published statement is false

Stacks 0EJA is published with hypotheses (1) `A` local with `𝔞 = 𝔪` and (2) `cd(A, I) = 1`
only, and under those its "if" direction is false. Necessity holds as stated, and is
`Stacks.Algebraization.two_lt_depth_add_dim_of_satisfiesDepthInequalities`.

*The counterexample.* Let `K` be a field with `K ≅ K(u₁, u₂, u₃)`, let `R = K[x₁, …, x₆]`, and
let `B` be the semilocalization of `R` at `𝔪₁ = (x₁, …, x₆)` and `𝔫 = (x₁, x₂, x₃ - 1)`. Glue
the two closed points of `Spec B` along an isomorphism `κ(𝔫) = K(x₄, x₅, x₆) ≅ K = κ(𝔪₁)`: the
subring `A ⊆ B` of elements with matching residues is a Noetherian local domain, `B` is finite
over it, and `Spec A` is `Spec B` with its two closed points identified. Put
`A'' = A/((x₄, x₅) ∩ (x₁) ∩ A)`, `I = x₁A''`, `𝔞` the maximal ideal and `ℱ_n = 𝒪_U/Iⁿ𝒪_U`.
Then `cd(A'', I) = 1`. The point `y` of `Y` given by `𝔓 = (x₁, x₄, x₅)` has `dim({y}‾) = 3`
but `δ^Y_Z(y) = 2`, through the system `{𝔪} ⊂ V(x₁, x₃ - 1) ⊂ V(x₁) ⊃ V(𝔓)`. At the prime
`𝔭 = (x₄, x₅)` of `𝒪_{X,y}^∧` the quotient is a discrete valuation ring and the localization is
a field, so `depth + δ = 0 + 2` and clause (2) of the `(2, 3)`-inequalities fails. At the points
of dimension one the completed stalks are `R_𝔔/(x₁)`, where the condition is vacuous, or have
`𝒪^∧/(x₄, x₅)` regular of dimension three, where `depth + dim = 3 > 2`. So the right-hand side
holds and the left-hand side fails. Here `A''/I` is not catenary: `(x₁) ⊂ (x₁, x₃ - 1) ⊂ 𝔪` is
a saturated chain of length two, and through `𝔪₁` there is one of length five. The completed
stalks are quotients of regular local rings.

The Lean proof that the published statement is false is
`Stacks.NonCatenaryExample.not_stacks0EJA`, in
`StacksFrontier/AlgebraicGeometry/Algebraization/NonCatenaryCounterexample/Final.lean`. It has no
hypotheses. It negates the published statement, quantified over all algebraization situations
with `A` local, `𝔞 = 𝔪` and `cd(A, I) = 1` and over all objects of `Coh(U, I𝒪_U)`, with the
right-hand side exactly that of the corrected theorem below. It is witnessed by the ring `A''`
above over `K = ℚ(t₀, t₁, …)`, with `(ℱ_n)` the completion of `𝒪_U`; the construction and the
two local computations are in the modules under
`StacksFrontier/AlgebraicGeometry/Algebraization/NonCatenaryCounterexample/`. In that example
`A''/I` is not catenary, which is what the corrected theorem adds. The non-catenarity is the
argument given in the previous paragraph and is not itself a Lean statement.

*Where the published proof breaks.* It quotes Stacks 0EIY (5), `δ^Y_Z(y) = dim({y}‾)`, which
is stated for a *catenary* Noetherian local ring and fails at the point `y` above. Part of it
survives without catenarity:
`Stacks.Algebraization.two_le_distanceFunction_closedPoint_of_two_le_coheight` gives
`dim({y}‾) ≥ 2 → δ^Y_Z(y) ≥ 2` in any Noetherian local ring, so `δ^Y_Z(y) = 1 ↔ dim({y}‾) = 1`.
The case that breaks is `δ^Y_Z(y) = 2`. The proof transports the depth-plus-dimension sum from
`y` along an *immediate* specialization `y ⤳ y'` with `dim({y'}‾) = 1`, and in the
counterexample `y` has no such specialization.

*The correction.* The hypothesis added to repair this is `Ring.IsCatenary (A/I)`: the ring on
which `δ^Y_Z` is computed, at the strength Stacks 0EIY (5) asks for. The transport also uses the
second display of Stacks 0EHW for the completed local ring `𝒪_{X,y'}^∧`. The source proves
that display for a ring with a dualizing complex, and its proof uses that only to get
universal catenarity and Cohen--Macaulay formal fibres. So the corrected statement also asks
for those two properties of `𝒪_{X,y'}^∧` at the points `y'` of `U ∩ Y` of dimension one. They
are the form the source itself uses for this same translation in Stacks 0EHI and Stacks 0BJV.
A dualizing complex on `A` supplies all three: the first by
`Ring.IsUniversallyCatenary.of_surjective`, the others by
`isUniversallyCatenary_and_isPRing_completedLocalRing`. That is the content of
`satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim_of_isDualizingComplex`, and a
dualizing complex is clause (2) of the neighbouring Stacks 0DXU, 0EJ9 and 0EJB.

*What the conditions on the completed stalks are used for.* This paragraph and the next record a
mathematical analysis. Nothing in them is formalized in this file, and none of it is used by the
declarations below. Write `B = 𝒪_{X,y'}^∧`, `M = ℱ_{y'}^∧` and `C` for the `I`-adic completion
of the localization of `B` at the prime of `y`. Let `𝔭` be a prime of `C` with `dim C/𝔭 = 1` and
`I C ⊄ 𝔭`, and let `𝔭' = 𝔭 ∩ B`. A vanishing depth at `(y, 𝔭)` forces `𝔭' ∈ Ass(M)` and
`𝔭 ∈ Ass(C/𝔭'C)`, by flat local base change. So the `δ^Y_Z(y) = 2` step consumes exactly the
bound `dim B/𝔭' ≤ 2` for such `𝔭'`. Put `D = B/𝔭'`. The bound can fail in only two ways: `D` is
not catenary off `V(I)`, or the generic `I`-adic formal fibre of a localization of `D` is not
Cohen--Macaulay, through an embedded associated prime of coheight one. What the argument uses is
associatedness, not a dimension count. A prime of coheight one lying over `(0)` in the
completion of a two-dimensional local domain is not contradictory by itself: take
`k[x, y]_{(x, y)}` and `𝔭 = (y - g(x))` with `g` a transcendental power series. So no dimension
count can replace the Cohen--Macaulay fibre condition.

*Invariance under `I`-adic completion.* Every ingredient of Stacks 0EJA depends only on the
system `(A/Iⁿ)ₙ`. Let `A'` be the `I`-adic completion of `A`. It is local with maximal ideal
`𝔪A'`. The map `A → A'` is faithfully flat, so `cd(A, I) = cd(A', IA')`. The schemes `Y`, `Z`
and `U ∩ Y` and the function `δ^Y_Z` depend only on `A/I`. The category `Coh(U, I𝒪_U)` depends
only on the schemes `Spec(A/Iⁿ) ∖ {𝔪}`. The completed stalks and the formal stalks `ℱ_y^∧` are
the same for `A` and for `A'`. So Stacks 0EJA holds for `A` exactly when it holds for `A'`, and
a counterexample exists exactly when one exists with `A` `I`-adically complete.

*Open.* It is not known whether `Ring.IsCatenary (A/I)` alone suffices, that is, whether the two
conditions on the completed stalks can be dropped from
`satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim`. There is neither a proof nor a
counterexample. The completed stalks are `I`-adic completions, not `𝔪_y`-adic ones, so the fact
that complete Noetherian local rings are universally catenary with Cohen--Macaulay formal fibres
does not supply the two conditions. The bound `dim B/𝔭' ≤ 2` that the `δ^Y_Z(y) = 2` step consumes
is also not a consequence of `B` being `I`-adically complete with `B/IB` catenary. Take a field `K`
with `K ≅ K(x₃)`, let `B₀` be the semilocalization of `K[x₁, x₂, x₃]` at `𝔪₁ = (x₁, x₂, x₃)` and
`𝔫 = (x₁, x₂ - 1)`, let `f = x₁(x₁ + x₂ - 1)`, and glue the two closed points of the `f`-adic
completion `B₀'` along an isomorphism `κ(𝔫) = K(x₃) ≅ K = κ(𝔪₁)`. Here `B₀'` is regular, since `B₀`
is excellent. Its spectrum is connected, because `V(f)` is: the component `V(x₁)` passes through
both closed points. So `B₀'` is a domain. The glued ring `D` is then an `f`-adically complete local
domain of dimension three, and `D/fD` has dimension two and is catenary. The prime `𝔮` of
`(x₁ + x₂ - 1)` contains `f`, has height one and coheight one, and every minimal prime of the
completion of `D_𝔮` has coheight one. So the bound fails for `B = M = D` and `𝔭' = 0`. In this
example `D/fD` is not universally catenary: the image of `V(x₁)` is a two-dimensional local domain
whose completion is not equidimensional, with branches of dimensions two and one. Dropping the
conditions on the completed stalks means excluding this failure when `D/ID` is a quotient of the
localization of a catenary local ring at a prime of coheight one.

## Implementation notes

`dim({y}‾)` is the height of the point in the specialization order of the scheme `X`, which is
the coheight of the corresponding prime in the inclusion order of `Spec(A)`; the translation is
`Stacks.Algebraization.height_spec_eq_coheight`.

Depth, the dimension of the quotient and the distance are compared in `EInt`, as in the
definition of the `(2, 3)`-inequalities.

## References

* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EKW](https://stacks.math.columbia.edu/tag/0EKW), cohomological
  dimension one.
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY), the distance function.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), depth plus dimension
  under completion.
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80), universal catenarity.
* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY), the formal fibres.
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR), the classes of rings
  with a dualizing complex.
* [Stacks Project, Tag 0EHI](https://stacks.math.columbia.edu/tag/0EHI) and
  [Stacks Project, Tag 0BJV](https://stacks.math.columbia.edu/tag/0BJV), the same translation
  between finiteness and the depth-plus-dimension bound, made under "universally catenary with
  Cohen--Macaulay formal fibres", and
  [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW), its weakening to
  `(S_n)` formal fibres in a bounded range of degrees.
* [Stacks Project, Tag 0EJ9](https://stacks.math.columbia.edu/tag/0EJ9) and
  [Stacks Project, Tag 0EJB](https://stacks.math.columbia.edu/tag/0EJB), the neighbouring
  lemmas, which assume a dualizing complex outright.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentPushforwardCriterion
open Stacks.AdicCompletionDimension

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Extended-integer arithmetic -/

/-- Translation by an integer is an order isomorphism of the extended integers. -/
private theorem lt_add_coe_iff_lt (s n : ℤ) (x : EInt) :
    ((s + n : ℤ) : EInt) < x + ((n : ℤ) : EInt) ↔ ((s : ℤ) : EInt) < x := by
  rw [Stacks.Chow.coe_add_coe_eq_coe_add, ← Stacks.Chow.eintAddRight_apply n x,
    ← Stacks.Chow.eintAddRight_apply n ((s : ℤ) : EInt)]
  exact (Stacks.Chow.eintAddRight n).lt_iff_lt

/-- The image of an extended natural number in the extended integers is nonnegative. -/
private theorem zero_le_enatToEInt (n : ℕ∞) : ((0 : ℤ) : EInt) ≤ enatToEInt n := by
  cases n using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    change ((0 : ℤ) : EInt) ≤ ((k : ℤ) : EInt)
    exact WithBotTop.coe_le_coe.mpr (by positivity)

/-- A lower bound `k ≤ n` in `ℕ∞` persists in the extended integers. -/
private theorem coe_le_enatToEInt {n : ℕ∞} {k : ℕ} (h : (k : ℕ∞) ≤ n) :
    ((k : ℤ) : EInt) ≤ enatToEInt n := by
  cases n using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    have hm : k ≤ m := by exact_mod_cast h
    change ((k : ℤ) : EInt) ≤ ((m : ℤ) : EInt)
    exact WithBotTop.coe_le_coe.mpr (by exact_mod_cast hm)

/-- Every integer is below `⊤` in the extended integers. -/
private theorem coe_lt_top_eint (n : ℤ) : ((n : ℤ) : EInt) < ⊤ :=
  lt_top_iff_ne_top.mpr (WithBotTop.coe_ne_top _)

/-- Adding `⊤` to an extended integer other than `⊥` gives `⊤`. -/
private theorem add_top_eq_top_of_ne_bot {x : EInt} (hx : x ≠ ⊥) : x + ⊤ = ⊤ := by
  cases x using WithBot.recBotCoe with
  | bot => exact absurd rfl hx
  | coe m =>
    change ((m + ⊤ : WithTop ℤ) : EInt) = ((⊤ : WithTop ℤ) : EInt)
    rw [WithTop.add_top]

/-- Lower bounds by integers add up in the extended integers. -/
private theorem coe_add_le_add {x y : EInt} {a b : ℤ} (hx : ((a : ℤ) : EInt) ≤ x)
    (hy : ((b : ℤ) : EInt) ≤ y) : ((a + b : ℤ) : EInt) ≤ x + y := by
  rw [Stacks.Chow.coe_add_coe_eq_coe_add]
  exact add_le_add hx hy

/-- The depth `d`, the dimension `c` of the quotient and the distance `e ≥ 1` satisfy
`d + c + e > 3` as soon as `c ≥ 1`, the pointwise bound `d + c > 2` holds when `e = 1` and the
bound `d + c > 1` holds when `e = 2`. -/
private theorem three_lt_add_add_of_cases {dep dist : ℕ∞} {c : EInt}
    (hcbot : c ≠ ⊥) (hc : ((1 : ℤ) : EInt) ≤ c) (hdist : 1 ≤ dist)
    (h1 : dist = 1 → ((2 : ℤ) : EInt) < enatToEInt dep + c)
    (h2 : dist = 2 → ((1 : ℤ) : EInt) < enatToEInt dep + c) :
    ((3 : ℤ) : EInt) < enatToEInt dep + c + enatToEInt dist := by
  have hsumne : enatToEInt dep + c ≠ ⊥ :=
    WithBot.add_ne_bot.mpr ⟨enatToEInt_ne_bot' dep, hcbot⟩
  cases dist using ENat.recTopCoe with
  | top =>
    rw [show enatToEInt (⊤ : ℕ∞) = ⊤ from rfl, add_top_eq_top_of_ne_bot hsumne]
    exact coe_lt_top_eint 3
  | coe n =>
    have hn1 : 1 ≤ n := by exact_mod_cast hdist
    match n, hn1 with
    | 1, _ =>
      rw [show enatToEInt ((1 : ℕ) : ℕ∞) = ((1 : ℤ) : EInt) from rfl]
      exact (lt_add_coe_iff_lt 2 1 _).mpr (h1 rfl)
    | 2, _ =>
      rw [show enatToEInt ((2 : ℕ) : ℕ∞) = ((2 : ℤ) : EInt) from rfl]
      exact (lt_add_coe_iff_lt 1 2 _).mpr (h2 rfl)
    | (k + 3), _ =>
      have hd : ((0 : ℤ) : EInt) ≤ enatToEInt dep := zero_le_enatToEInt dep
      have he : ((3 : ℤ) : EInt) ≤ enatToEInt ((k + 3 : ℕ) : ℕ∞) :=
        coe_le_enatToEInt (by exact_mod_cast Nat.le_add_left 3 k)
      exact lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr (by norm_num))
        (coe_add_le_add (coe_add_le_add hd hc) he)

/-- If the dimension term is at least two the bound `d + c > 1` is automatic. -/
private theorem one_lt_add_of_two_le {dep : ℕ∞} {c : EInt} (hc : ((2 : ℤ) : EInt) ≤ c) :
    ((1 : ℤ) : EInt) < enatToEInt dep + c := by
  exact lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr (by norm_num))
    (coe_add_le_add (zero_le_enatToEInt dep) hc)

/-! ### The distance is the dimension of the closure -/

/-- The dimension of `(A/I)/(𝔮/I)` equals the dimension of `A/𝔮`. -/
private theorem ringKrullDim_quotientQuotient (S : AlgebraizationSituation.{u})
    (q : Ideal S.A) (hIle : S.I ≤ q) :
    ringKrullDim ((S.A ⧸ S.I) ⧸ q.map (Ideal.Quotient.mk S.I)) =
      ringKrullDim (S.A ⧸ q) :=
  ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIle)

/-- The height of a point of an affine scheme, in the specialization order, is the coheight of
the corresponding prime in the inclusion order. -/
private theorem height_spec_eq_coheight (R : CommRingCat.{u}) (x : Spec R) :
    Order.height x = Order.coheight (α := PrimeSpectrum R) x :=
  (Order.height_orderIso (AlgebraicGeometry.specOrderIsoPrimeSpectrum R) x).symm

/-- In a local algebraization situation with `𝔞 = 𝔪` and `A/I` catenary the distance
`δ^Y_Z(z)` is the dimension of the closure of the point of `X` under `z`. -/
private theorem distanceToZ_eq_height (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (hmax : S.a = maximalIdeal S.A) (hcat : Ring.IsCatenary (S.A ⧸ S.I)) (z : S.Y) :
    (S.distanceToZ z : ℕ∞) = Order.height (S.Yι.base z) := by
  have hIle : S.I ≤ z.asIdeal.comap (Ideal.Quotient.mk S.I) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_quotient_self]
    exact bot_le
  have hmapq : (z.asIdeal.comap (Ideal.Quotient.mk S.I)).map (Ideal.Quotient.mk S.I) =
      z.asIdeal := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  have h := ringKrullDim_quotientQuotient S (z.asIdeal.comap (Ideal.Quotient.mk S.I)) hIle
  rw [hmapq] at h
  have hdimY : ringKrullDim ((S.A ⧸ S.I) ⧸ (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal) =
      ringKrullDim (S.A ⧸ (S.Yι.base z : PrimeSpectrum S.A).asIdeal) := h
  have h2 : ((Order.coheight (α := PrimeSpectrum (S.A ⧸ S.I)) z : ℕ∞) : WithBot ℕ∞) =
      ((Order.coheight (α := PrimeSpectrum S.A) (S.Yι.base z) : ℕ∞) : WithBot ℕ∞) := by
    rw [coheight_eq_ringKrullDim_quotient (R := S.A ⧸ S.I) z,
      coheight_eq_ringKrullDim_quotient (R := S.A) (S.Yι.base z)]
    exact hdimY
  rw [height_spec_eq_coheight (.of S.A) (S.Yι.base z), ← WithBot.coe_injective h2]
  exact distanceToZEqCoheight_of_isCatenary_quotient S hmax hcat z

/-! ### The pointwise depth bound at the points of `U ∩ Y` of dimension one -/

/-- The maximal ideal of the completed local ring is the extension of the maximal ideal. -/
private theorem maximalIdeal_completedLocalRing (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z) :
    letI := isLocalRing_adicCompletion_of_le_maximalIdeal _
      (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
    completedLocalIdeal (idealOnOpen S) y ≤
      maximalIdeal (completedLocalRing (idealOnOpen S) y) := by
  let _ := isLocalRing_adicCompletion_of_le_maximalIdeal _
    (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
  have hle := stalk_idealOnOpen_le_maximalIdeal S y z hyz
  have hmax : maximalIdeal (completedLocalRing (idealOnOpen S) y) =
      (maximalIdeal (S.U.toScheme.presheaf.stalk y)).map
        (algebraMap (S.U.toScheme.presheaf.stalk y) (completedLocalRing (idealOnOpen S) y)) :=
    (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le
      (IdealSheafData.stalk (idealOnOpen S) y) (maximalIdeal _) hle
      (Ideal.fg_of_isNoetherianRing _))).symm
  rw [hmax]
  exact Ideal.map_mono hle

/-- From `a + b = 2` in the Krull-dimension order the extended-integer sum is at most `2`. -/
private theorem two_le_of_add_eq_two {a : ℕ∞} {b : WithBot ℕ∞}
    (h0 : ((a : ℕ∞) : WithBot ℕ∞) + b = ((0 : ℕ∞) : WithBot ℕ∞) + 1 + 1) :
    enatToEInt a + krullDimToEInt b ≤ ((2 : ℤ) : EInt) := by
  have hrhs : ((0 : ℕ∞) : WithBot ℕ∞) + 1 + 1 = (((2 : ℕ∞)) : WithBot ℕ∞) := rfl
  rw [hrhs] at h0
  cases b using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe m =>
    rw [← WithBot.coe_add] at h0
    have h' : a + m = (2 : ℕ∞) := WithBot.coe_injective h0
    cases a using ENat.recTopCoe with
    | top => exact absurd h' (by simp)
    | coe k =>
      cases m using ENat.recTopCoe with
      | top => exact absurd h' (by simp)
      | coe j =>
        have hkj : k + j = 2 := by exact_mod_cast h'
        have e1 : enatToEInt ((k : ℕ) : ℕ∞) = ((k : ℤ) : EInt) := rfl
        have e2 : krullDimToEInt ((((j : ℕ) : ℕ∞)) : WithBot ℕ∞) = ((j : ℤ) : EInt) := rfl
        rw [e1, e2, ← Stacks.Chow.coe_add_coe_eq_coe_add]
        exact WithBotTop.coe_le_coe.mpr (by omega)

/-- The local ring of `U` at a point has a dualizing complex when `A` does: it is a localization
of `A`. -/
public theorem dualizingComplex_pointStalk (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (y' : S.U.toScheme) :
    ∃ K : DerivedCategory (ModuleCat.{u} (S.U.toScheme.presheaf.stalk y')),
      Dualizing.IsDualizingComplex K := by
  obtain ⟨K, hK⟩ := hdual
  have _ : IsNoetherianRing (Localization.AtPrime (underlyingPrime S y').asIdeal) :=
    IsLocalization.isNoetherianRing (underlyingPrime S y').asIdeal.primeCompl _ inferInstance
  let e : Localization.AtPrime (underlyingPrime S y').asIdeal ≃+*
      S.U.toScheme.presheaf.stalk y' := (pointStalkRingEquiv S y').symm
  let _ : Algebra (Localization.AtPrime (underlyingPrime S y').asIdeal)
      (S.U.toScheme.presheaf.stalk y') := e.toRingHom.toAlgebra
  let M₀ : Submonoid (S.U.toScheme.presheaf.stalk y') :=
    IsUnit.submonoid (S.U.toScheme.presheaf.stalk y')
  let M : Submonoid (Localization.AtPrime (underlyingPrime S y').asIdeal) :=
    M₀.map e.symm.toRingHom
  have hloc : IsLocalization M (S.U.toScheme.presheaf.stalk y') :=
    IsLocalization.isLocalization_of_base_ringEquiv M₀ (S.U.toScheme.presheaf.stalk y') e.symm
  have _ : IsNoetherianRing (S.U.toScheme.presheaf.stalk y') :=
    IsLocalization.isNoetherianRing M (S.U.toScheme.presheaf.stalk y') inferInstance
  exact ⟨_, Dualizing.isDualizingComplex_localization M _
    (Dualizing.isDualizingComplex_localization (underlyingPrime S y').asIdeal.primeCompl K hK)⟩

/-- **The completed local ring of `U` at a point is universally catenary with Cohen--Macaulay
formal fibres when `A` has a dualizing complex.** -/
public theorem isUniversallyCatenary_and_isPRing_completedLocalRing
    (S : AlgebraizationSituation.{u})
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (y' : S.U.toScheme) :
    Ring.IsUniversallyCatenary (completedLocalRing (idealOnOpen S) y') ∧
      IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u}
        (completedLocalRing (idealOnOpen S) y') := by
  obtain ⟨L, hL⟩ := Dualizing.exists_isDualizingComplex_adicCompletion
    (IdealSheafData.stalk (idealOnOpen S) y') (dualizingComplex_pointStalk S hdual y')
  exact ⟨Dualizing.isUniversallyCatenary_of_isDualizingComplex_univ hL,
    Stacks.AdicCompletionFibre.isPRing_cohenMacaulayRingMapProperty_univ hL⟩

/-- Under the hypotheses of `satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim` and its
pointwise bound, at a point `y` of `U ∩ Y` whose closure has dimension two, the formal stalk has
positive depth at a prime `𝔭` outside `V(I𝒪_{X,y}^∧)` with `dim(𝒪_{X,y}^∧/𝔭) = 1`. -/
private theorem one_le_completedStalkDepth_of_height_two
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (ha : S.a = maximalIdeal S.A)
    (hcatStalk : ∀ (y' : S.U.toScheme) (z' : S.Y), S.U.ι.base y' = S.Yι.base z' →
      Order.height (S.U.ι.base y') = 1 →
      Ring.IsUniversallyCatenary (completedLocalRing (idealOnOpen S) y'))
    (hCMStalk : ∀ (y' : S.U.toScheme) (z' : S.Y), S.U.ι.base y' = S.Yι.base z' →
      Order.height (S.U.ι.base y') = 1 →
      IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u}
        (completedLocalRing (idealOnOpen S) y'))
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hH : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      Order.height (S.U.ι.base y) = 1 →
      ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
        ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
        ((2 : ℤ) : EInt) <
          enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
            krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)))
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (hheight : Order.height (S.U.ι.base y) = 2)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal)
    (hdim1 : ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) = 1) :
    1 ≤ completedStalkDepth (idealOnOpen S) F y p := by
  obtain ⟨y', z', q, hspec, hy'z', hheight', hqy, hqI, hqdim⟩ :=
    exists_specializes_height_one S ha y z hyz hheight
  have hJmax' : IdealSheafData.stalk (idealOnOpen S) y' ≤
      maximalIdeal (S.U.toScheme.presheaf.stalk y') :=
    stalk_idealOnOpen_le_maximalIdeal S y' z' hy'z'
  have hp' : ¬ completedLocalIdeal (idealOnOpen S) y' ≤
      (PrimeSpectrum.comap (completedLocalRingSpecializes (idealOnOpen S) hspec) p).asIdeal :=
    fun hle => hp (by
      rw [← map_completedLocalIdeal_completedLocalRingSpecializes (idealOnOpen S) hspec]
      exact Ideal.map_le_of_le_comap hle)
  have htrans := completedStalkDepth_add_ringKrullDim_succ_eq_of_specializes
    (idealOnOpen S) F hspec q hqy hqI hJmax' (hcatStalk y' z' hy'z' hheight')
    (hCMStalk y' z' hy'z' hheight') hqdim p
  have hHy' := hH y' z' hy'z' hheight'
    (PrimeSpectrum.comap (completedLocalRingSpecializes (idealOnOpen S) hspec) p) hp'
  rw [hdim1] at htrans
  refine Order.one_le_iff_ne_zero.mpr fun hzero => ?_
  rw [hzero] at htrans
  exact (two_le_of_add_eq_two htrans.symm).not_gt hHy'

/-- In Situation 0EHC let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. Assume `A` is local with `𝔞 = 𝔪`,
that `cd(A, I) = 1`, and that `A/I` is catenary. Assume also that, at every point `y'` of `U ∩ Y`
with `dim({y'}‾) = 1`, the completed local ring `𝒪_{X,y'}^∧` is universally catenary and has
Cohen--Macaulay formal fibres. Then `(ℱ_n)` satisfies the `(2, 3)`-inequalities if and only if
`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2` for every `y ∈ U ∩ Y` with `dim({y}‾) = 1` and every
prime `𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`.

Without the catenarity of `A/I` and the hypotheses on the completed stalks the statement is false:
see `Stacks.NonCatenaryExample.not_stacks0EJA`. -/
@[stacks 0EJA "corrected form: the published statement, at hypotheses (1) and (2) alone, is \
false, by Stacks.NonCatenaryExample.not_stacks0EJA, an example in which A/I is not catenary; \
this is the equivalence with A/I catenary and the completed local rings of U at the points of \
U ∩ Y of dimension one universally catenary with Cohen-Macaulay formal fibres"]
public theorem satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (ha : S.a = maximalIdeal S.A)
    (hcat : Ring.IsCatenary (S.A ⧸ S.I))
    (hcatStalk : ∀ (y' : S.U.toScheme) (z' : S.Y), S.U.ι.base y' = S.Yι.base z' →
      Order.height (S.U.ι.base y') = 1 →
      Ring.IsUniversallyCatenary (completedLocalRing (idealOnOpen S) y'))
    (hCMStalk : ∀ (y' : S.U.toScheme) (z' : S.Y), S.U.ι.base y' = S.Yι.base z' →
      Order.height (S.U.ι.base y') = 1 →
      IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u}
        (completedLocalRing (idealOnOpen S) y'))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    SatisfiesDepthInequalities S F 2 3 ↔
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        Order.height (S.U.ι.base y) = 1 →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          ((2 : ℤ) : EInt) <
            enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
              krullDimToEInt
                (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) := by
  constructor
  · intro h y z hyz hd p hp
    exact two_lt_depth_add_dim_of_satisfiesDepthInequalities S ha hcd F h y z hyz hd p hp
  · intro hH
    refine (satisfiesDepthInequalities_two_three_iff S F hcd).2 fun y z hyz p hp => ?_
    let _ := isLocalRing_adicCompletion_of_le_maximalIdeal _
      (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
    have hJm := maximalIdeal_completedLocalRing S y z hyz
    have hpne : p.asIdeal ≠ maximalIdeal (completedLocalRing (idealOnOpen S) y) := fun h =>
      hp (h ▸ hJm)
    have hdimpos : 1 ≤ ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) :=
      one_le_ringKrullDim_quotient_of_ne_maximalIdeal p.asIdeal hpne
    have hdimbot : ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le (by simp) hdimpos)
    have hdistpos : 1 ≤ S.distanceToZ z := S.one_le_distanceToZ y z hyz
    have hdh : (S.distanceToZ z : ℕ∞) = Order.height (S.U.ι.base y) := by
      rw [hyz]; exact distanceToZ_eq_height S ha hcat z
    change ((3 : ℤ) : EInt) <
      enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
          krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
        enatToEInt (S.distanceToZ z)
    refine three_lt_add_add_of_cases (krullDimToEInt_ne_bot' hdimbot)
      (one_le_krullDimToEInt' hdimpos) hdistpos (fun hone => ?_) (fun htwo => ?_)
    · exact hH y z hyz (by rw [← hdh, hone]) p hp
    · by_cases hdone :
          ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) = 1
      · have hdep : 1 ≤ completedStalkDepth (idealOnOpen S) F y p :=
          one_le_completedStalkDepth_of_height_two S ha hcatStalk hCMStalk F hH y z hyz
            (by rw [← hdh, htwo]) p hp hdone
        have hd1 : ((1 : ℤ) : EInt) ≤
            enatToEInt (completedStalkDepth (idealOnOpen S) F y p) :=
          coe_le_enatToEInt (k := 1) (by exact_mod_cast hdep)
        have hc1 : krullDimToEInt
            (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) =
              ((1 : ℤ) : EInt) := (krullDimToEInt_eq_one_iff' hdimbot).2 hdone
        rw [hc1]
        exact lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr (by norm_num))
          (coe_add_le_add hd1 le_rfl)
      · exact one_lt_add_of_two_le (two_le_of_one_le_of_ne_one' (krullDimToEInt_ne_bot' hdimbot)
          (one_le_krullDimToEInt' hdimpos)
          (fun hcc => hdone ((krullDimToEInt_eq_one_iff' hdimbot).1 hcc)))

/-- In Situation 0EHC let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. Assume `A` is local with `𝔞 = 𝔪`,
that `A` has a dualizing complex, and that `cd(A, I) = 1`. Then `(ℱ_n)` satisfies the
`(2, 3)`-inequalities if and only if `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2` for every
`y ∈ U ∩ Y` with `dim({y}‾) = 1` and every prime `𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`. -/
@[stacks 0EJA "corrected form: the published statement, at hypotheses (1) and (2) alone, is \
false, by Stacks.NonCatenaryExample.not_stacks0EJA, an example in which A/I is not catenary; \
this is the equivalence for A with a dualizing complex, the standing hypothesis of the \
neighbouring 0EJ9 and 0EJB"]
public theorem satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim_of_isDualizingComplex
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (ha : S.a = maximalIdeal S.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    SatisfiesDepthInequalities S F 2 3 ↔
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        Order.height (S.U.ι.base y) = 1 →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          ((2 : ℤ) : EInt) <
            enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
              krullDimToEInt
                (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) := by
  obtain ⟨K, hK⟩ := hdual
  have hcatQ : Ring.IsUniversallyCatenary (S.A ⧸ S.I) :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective
      (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK)
  exact satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim S ha
    (hcatQ (S.A ⧸ S.I))
    (fun y' _ _ _ => (isUniversallyCatenary_and_isPRing_completedLocalRing S ⟨K, hK⟩ y').1)
    (fun y' _ _ _ => (isUniversallyCatenary_and_isPRing_completedLocalRing S ⟨K, hK⟩ y').2)
    hcd F

end Stacks.Algebraization

end
