module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor

/-!
# The principal divisor of a rational function

Let `X` be a locally Noetherian integral algebraic space and let `f ∈ R(X)^*`. The *principal
divisor associated to `f`* is

`div(f) = div_X(f) = ∑_Z ord_Z(f) [Z]`,

the sum running over the prime divisors `Z ⊆ X`, with `ord_Z(f)` the order of vanishing of `f`
along `Z`. This is **Stacks 0ENP** as an element of `Div(X)`, and, in Situation 0EDT with `X/B`
good and `dim_δ(X) = n`, **Stacks 0EQ1** as an element of `Z_{n-1}(X)` — the two readings agree
because a prime divisor of such an `X` has δ-dimension `n - 1`, which is Stacks 0EPZ.

That the formal sum makes sense is **Stacks 0ENN**: the prime divisors with `ord_Z(f) ≠ 0` are
locally finite in `|X|`. It is proved here, not assumed. The source's argument is that `f` is a
unit section over some nonempty open `U ⊆ X`, so every prime divisor contributing to the sum has
its generic point in the closed set `|X| ∖ U`, where codimension one forces it to be an
irreducible component; the components of a closed set are locally finite by Stacks 0EE5. That
argument is already in the library in exactly the generality needed, as
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`, which is that
Stacks 0EE5 step and is also the second and third sentences of the proof of Stacks 0EPS; and
what is added here is the other half: at a generic point lying in `U` the order of vanishing
really is zero, because the order of vanishing of a unit is zero.

## Main definitions

* `AlgebraicGeometry.Space.principalDivisorCoefficients`: the coefficients `ord_Z(f)` of
  `div(f)`, indexed by the prime divisors of `X`.
* `AlgebraicGeometry.Space.principalWeilDivisor`: **Stacks 0ENP**, the principal divisor
  `div(f) = ∑_Z ord_Z(f) [Z]` as an element of `Div(X)`.
* `AlgebraicGeometry.Space.principalWeilDivisorOfRegularLocus`: the same, with local finiteness
  supplied from a nonempty open subset of `|X|` over which `f` is a unit.
* `AlgebraicGeometry.Space.principalDivisorCycle`: **Stacks 0EQ1**, the principal divisor
  `div(f)` as an element of `Z_{n-1}(X)`.
* `AlgebraicGeometry.Space.principalDivisorCycleOfRegularLocus`: the same, with local finiteness
  supplied from a nonempty open subset of `|X|` over which `f` is a unit.
* `AlgebraicGeometry.Space.principalDivisorCycleSet`: the set of principal divisors in
  `Z_k(X)`, that is the set of `k`-cycles whose coefficient family is `div(f)` for some
  `f ∈ R(X)^*`.
* `AlgebraicGeometry.Space.principalDivisorsOfIntegralClosedSubspaces`: the set of principal
  divisors on each integral closed subspace of a good algebraic space, which is an inhabitant of
  the `principalDivisors` field of `AlgebraicGeometry.Space.ChowTarget`; see the implementation
  notes.

## Main results

* `Ring.ordTotalFracInt_eq_zero_of_eq_algebraMap` and
  `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_zero_of_eq_algebraMap`: the order of vanishing of
  the image of a unit of the ring is zero.
* `AlgebraicGeometry.Space.principalDivisorCoefficients_eq_zero_of_isUnit`: `ord_Z(f) = 0` when
  `f` is a unit of `𝒪^h_{X,ξ}` at the generic point `ξ` of `Z`. This is the step the source
  makes when it restricts to the open subspace over which `f` is invertible.
* `AlgebraicGeometry.Space.locallyFinite_principalDivisorCoefficients_ne_zero`: **Stacks 0ENN**,
  the second of its two sets — the prime divisors with `ord_Z(f) ≠ 0` are locally finite.
* `AlgebraicGeometry.Space.principalDivisorCycleCoefficients_mem_cyclesOfDimension`: the
  coefficient family of `div(f)` is an `(n-1)`-cycle.
* `AlgebraicGeometry.Space.principalDivisorCycle_mem_principalDivisorCycleSet`: `div(f)` is one
  of the principal divisors.
* `AlgebraicGeometry.Space.principalWeilDivisor_mul` and
  `AlgebraicGeometry.Space.principalWeilDivisorOfRegularLocus_mul`: **Stacks 0ENQ**,
  `div(fg) = div(f) + div(g)` in `Div(X)`.

## Implementation notes

### The coefficient family is the one already in the library

`AlgebraicGeometry.Space.principalDivisorCycleCoefficients` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor` is already the coefficient
family of `div(f)` indexed by the integral closed subspaces of `X`, built with a real body out
of the embeddings `emb`; it was introduced there to state Stacks 0EPT. What it lacked, and what
this file supplies, is local finiteness and the δ-dimension clause, hence the bundled cycle. So
the cycle below is that family, and the identity of Stacks 0EPT already proved applies to it
verbatim.

### `div(f)` inhabits the `principalDivisors` field of a Chow group parameter

`AlgebraicGeometry.Space.ChowTarget` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection` asks, for each integral
closed subspace `W ⊆ Y`, for a `Set (CycleGroup D (W.subspace.ι ≫ sY) k)` of principal divisors
on `W`.  `AlgebraicGeometry.Space.principalDivisorsOfIntegralClosedSubspaces` is such a family,
built
from `AlgebraicGeometry.Space.principalDivisorCycleSet` at each `W`. That field is now
inhabited by the honest principal divisors rather than by an arbitrary set, and
`AlgebraicGeometry.Space.principalDivisorCycle_mem_principalDivisorCycleSet` says `div(f)` lies
in it. Nothing about `ChowTarget` is changed.

### What is carried

The embeddings `R(X) → Q(𝒪^h_{X,ξ})` of Stacks 0ENK are the parameter `emb`, exactly as they
are in Stacks 0EPT and in `AlgebraicGeometry.Space.principalDivisorCycleCoefficients`, so that
the results here do not fix a choice. The repository does construct them: Stacks 0ENK is
`AlgebraicGeometry.Space.genericFractionEmbedding`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorFunctionFieldEmbedding.lean:288`),
whose `emb` field supplies the parameter at every prime divisor of a decent, locally
Noetherian, integral algebraic space, with the independence of the chart proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorFunctionFieldChartIndependence.lean`.
Regularity of `f` — that `f ∈ R(X)^*` rather than `f ∈ R(X)` — is the hypothesis `hf` that
`emb W f` is a unit at every prime divisor, which is where the source uses it, and is the shape
already used by `AlgebraicGeometry.Space.principalDivisorCycleCoefficients`.

That `f` is a *unit section* over a nonempty open is carried as the pair of a nonempty open set
`U ⊆ |X|` and the hypothesis `hreg`: at the generic point of a prime divisor meeting `U`, the
image of `f` is the image of a unit of `𝒪^h_{X,ξ}`. This is the source's own sentence "there
exists a nonempty open `U ⊆ X` such that `f` corresponds to a section of `Γ(U, 𝒪_X^*)`", read at
each of those generic points through the embedding of Stacks 0ENK — the only form in which this
repository can speak of the image of `f` in a local ring at all. The conclusion `ord_Z(f) = 0`
is then *proved*, from `Ring.ord_of_isUnit`, not assumed; and local finiteness is proved from it
through `AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`, the Stacks
0EE5 step. Nothing about the conclusion of Stacks 0ENN or Stacks 0ENP is assumed.

The dimension-function hypotheses `d` and `hd` of the cycle reading are the assertion of
Stacks 0EDN that Situation 0EDT invokes, carried exactly as
`AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace` and
`AlgebraicGeometry.Space.divisorCycleOfSection` carry them. Nontriviality, Noetherianness and
the dimension bound on the henselian local rings are instance arguments, as they are for
`AlgebraicGeometry.Space.PrimeDivisor.ord` itself.

### Stacks 0ENN's first set

Stacks 0ENN asserts local finiteness of two families: the prime divisors at whose generic point
`f` fails to be regular, and the prime divisors with `ord_Z(f) ≠ 0`. Only the second is stated
here; the first is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.PrimeDivisorPoleLocus`, as
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_isDefinedAt`, which reads `f ∉ 𝒪_{X,ξ}`
as failure of `AlgebraicGeometry.Space.RationalMap.IsDefinedAt` at the generic point and
supplies the nonempty open from the dense open domain of a representative of `f`. Both halves
rest on the same general statement,
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`, which covers any
family of prime divisors whose generic points avoid a nonempty open.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0ENQ](https://stacks.math.columbia.edu/tag/0ENQ)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-! ### The order of vanishing of the image of a unit -/

namespace Ring

/-- **The order of vanishing of the image of a unit is zero.** If a unit `x` of a total ring of
fractions of a Noetherian ring `R` of Krull dimension at most one is the image of a unit `r` of
`R`, then its order of vanishing vanishes: the order of vanishing at `r` is the length of
`R ⧸ (r)`, and `(r)` is the whole of `R`. -/
theorem ordTotalFracInt_eq_zero_of_eq_algebraMap (R : Type*) [CommRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Nontrivial R] {K : Type*} [CommRing K] [Algebra R K]
    [IsFractionRing R K] {x : K} (hx : IsUnit x) {r : R} (hr : IsUnit r)
    (hxr : x = algebraMap R K r) :
    ordTotalFracInt R x hx = 0 := by
  have hr' : r ∈ nonZeroDivisors R := hr.mem_nonZeroDivisors
  rw [ordTotalFracInt_congr R hx (IsLocalization.map_units K ⟨r, hr'⟩) hxr,
    ordTotalFracInt_algebraMap R r hr', ord_of_isUnit hr]
  rfl

end Ring

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The principal divisor as a Weil divisor -/

section WeilForm

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (hdec : IsDecentSpace B S hS X)
variable [∀ W : PrimeDivisor B S hS X,
  Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

/-- The order of vanishing along a prime divisor `Z` of the image of a unit of `𝒪^h_{X,ξ}` is
zero. This is the pointwise content of the source's reduction to a nonempty open subspace over
which the rational function is invertible. -/
theorem PrimeDivisor.ord_eq_zero_of_eq_algebraMap (Z : PrimeDivisor B S hS X)
    {x : Z.genericTotalFractionRing B S hS hX hdec} (hx : IsUnit x)
    {r : ↥(Z.genericHenselianLocalRing B S hS hX hdec)} (hr : IsUnit r)
    (hxr : x = algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec) r) :
    Z.ord B S hS hX hdec x hx = 0 :=
  Ring.ordTotalFracInt_eq_zero_of_eq_algebraMap _ hx hr hxr

/-- **Stacks 0ENP, the coefficients.** The coefficients `ord_Z(f)` of the principal divisor
`div(f) = ∑_Z ord_Z(f) [Z]` of a rational function `f` on `X`, indexed by the prime divisors of
`X`: the coefficient at `Z` is the order of vanishing along `Z` of the image of `f` in the total
ring of fractions of `𝒪^h_{X,ξ}`.

The embeddings `R(X) → Q(𝒪^h_{X,ξ})` of Stacks 0ENK are the parameter `emb`, as in Stacks 0EPT;
regularity of `f` is the hypothesis `hf` that each image is a unit. -/
@[stacks 0ENP "the coefficients ord_Z(f) of div(f); the embeddings R(X) → Q(O^h_{X,ξ}) of
  Stacks 0ENK are the parameter emb, as they are for Stacks 0EPT"]
def principalDivisorCoefficients
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f)) :
    PrimeDivisor B S hS X → ℤ :=
  fun W => W.ord B S hS hX hdec (emb W f) (hf W)

/-- The coefficient of `div(f)` at a prime divisor is the order of vanishing there. -/
@[simp]
theorem principalDivisorCoefficients_apply
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f)) (W : PrimeDivisor B S hS X) :
    principalDivisorCoefficients B S hS hX hdec emb f hf W =
      W.ord B S hS hX hdec (emb W f) (hf W) :=
  rfl

/-- **The coefficient of `div(f)` vanishes where `f` is invertible.** If the image of `f` at the
generic point of a prime divisor `Z` is the image of a unit of `𝒪^h_{X,ξ}`, then `ord_Z(f) = 0`.

This is proved, from `Ring.ord_of_isUnit`, and is the half of the source's argument for
Stacks 0ENN that is not already in the library. -/
theorem principalDivisorCoefficients_eq_zero_of_isUnit
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f)) (W : PrimeDivisor B S hS X)
    {r : ↥(W.genericHenselianLocalRing B S hS hX hdec)} (hr : IsUnit r)
    (hfr : emb W f = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r) :
    principalDivisorCoefficients B S hS hX hdec emb f hf W = 0 :=
  PrimeDivisor.ord_eq_zero_of_eq_algebraMap B S hS hX hdec W (hf W) hr hfr

/-- A prime divisor carrying a nonzero coefficient of `div(f)` has its generic point outside any
open set over which `f` is invertible: inside such an open set the coefficient vanishes, by
`AlgebraicGeometry.Space.principalDivisorCoefficients_eq_zero_of_isUnit`. -/
theorem genericPoint_notMem_of_principalDivisorCoefficients_ne_zero
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (U : Set (points B S hS X))
    (hreg : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W f = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r)
    (W : PrimeDivisor B S hS X)
    (hW : principalDivisorCoefficients B S hS hX hdec emb f hf W ≠ 0) :
    W.genericPoint B S hS X ∈ Uᶜ := by
  intro hmem
  obtain ⟨r, hr, hfr⟩ := hreg W hmem
  exact hW (principalDivisorCoefficients_eq_zero_of_isUnit B S hS hX hdec emb f hf W hr hfr)

include hX in
/-- **Stacks 0ENN, the second set.** The prime divisors of `X` along which a rational function
`f` has nonzero order of vanishing are locally finite in `|X|`, given a nonempty open subset of
`|X|` over which `f` is invertible.

This is the source's argument. Such a prime divisor has its generic point outside the open set,
by `AlgebraicGeometry.Space.genericPoint_notMem_of_principalDivisorCoefficients_ne_zero`, so its
point set is an irreducible component of the closed complement — codimension one leaves no room
for a larger irreducible closed subset of that complement — and the irreducible components of a
closed set are locally finite by Stacks 0EE5. Both steps are
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`, already in the
library in exactly this generality; it is also the Stacks 0EE5 step in the proof of Stacks
0EPS. -/
@[stacks 0ENN "the second set: the prime divisors with ord_Z(f) ≠ 0 are locally finite. The
  first set, the prime divisors at whose generic point f is not regular, is
  locallyFinite_primeDivisor_not_isDefinedAt"]
theorem locallyFinite_principalDivisorCoefficients_ne_zero
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X))
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hreg : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W f = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r) :
    LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb f hf W = 0 then ∅
      else W.support B S hS X := by
  have h := locallyFinite_primeDivisor_of_genericPoint_notMem B S hS hX hN hirr
    (fun W => principalDivisorCoefficients B S hS hX hdec emb f hf W ≠ 0) U hUopen hUne
    (genericPoint_notMem_of_principalDivisorCoefficients_ne_zero B S hS hX hdec emb f hf U hreg)
  refine h.subset fun W p hp => ?_
  rw [Set.mem_ite_empty_left] at hp
  rw [Set.mem_ite_empty_right]
  exact hp

/-- **Stacks 0ENP.** The *principal divisor associated to `f ∈ R(X)^*`*, that is
`div(f) = ∑_Z ord_Z(f) [Z]`, as an element of `Div(X)`.

That the sum makes sense is Stacks 0ENN, the argument `hfin`, which
`AlgebraicGeometry.Space.locallyFinite_principalDivisorCoefficients_ne_zero` proves and
`AlgebraicGeometry.Space.principalWeilDivisorOfRegularLocus` discharges from a nonempty open
subset of `|X|` over which `f` is invertible. -/
@[stacks 0ENP "div(f) = ∑ ord_Z(f) [Z] as an element of Div(X); local finiteness is Stacks 0ENN,
  the argument hfin, discharged by locallyFinite_principalDivisorCoefficients_ne_zero in
  principalWeilDivisorOfRegularLocus; the embeddings of Stacks 0ENK are the parameter emb"]
def principalWeilDivisor
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb f hf W = 0 then ∅
      else W.support B S hS X) :
    WeilDivisor B S hS X :=
  ⟨principalDivisorCoefficients B S hS hX hdec emb f hf, hfin⟩

/-- The coefficient of `div(f)` at a prime divisor `Z` is `ord_Z(f)`. -/
@[simp]
theorem coe_principalWeilDivisor
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (hfin : LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb f hf W = 0 then ∅
      else W.support B S hS X) (W : PrimeDivisor B S hS X) :
    (principalWeilDivisor B S hS hX hdec emb f hf hfin : PrimeDivisor B S hS X → ℤ) W =
      W.ord B S hS hX hdec (emb W f) (hf W) :=
  rfl

include hX in
/-- **Stacks 0ENP.** The principal divisor `div(f) = ∑_Z ord_Z(f) [Z]` of a rational function
`f ∈ R(X)^*` as an element of `Div(X)`, with the local finiteness of Stacks 0ENN supplied from a
nonempty open subset of `|X|` over which `f` is invertible. -/
@[stacks 0ENP "div(f) in Div(X), with local finiteness (Stacks 0ENN) discharged here: it is
  proved from a nonempty open U over which f is invertible, the datum (U, hUopen, hUne, hreg)
  that is the first sentence of the source's own proof of Stacks 0ENN"]
def principalWeilDivisorOfRegularLocus
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X))
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hreg : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W f = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r) :
    WeilDivisor B S hS X :=
  principalWeilDivisor B S hS hX hdec emb f hf
    (locallyFinite_principalDivisorCoefficients_ne_zero B S hS hX hdec hN hirr emb f hf U
      hUopen hUne hreg)

/-! ### Additivity of the principal divisor -/

/-- **Stacks 0ENQ, the coefficients.** The coefficients of `div(fg)` are the sum of the
coefficients of `div(f)` and of `div(g)`: at each prime divisor this is the additivity
`ord_Z(fg) = ord_Z(f) + ord_Z(g)` of the order of vanishing, the image of `fg` under the
embedding of Stacks 0ENK being the product of the images of `f` and `g`. -/
theorem principalDivisorCoefficients_mul
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f g : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (hg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W g))
    (hfg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W (f * g))) :
    principalDivisorCoefficients B S hS hX hdec emb (f * g) hfg =
      principalDivisorCoefficients B S hS hX hdec emb f hf +
        principalDivisorCoefficients B S hS hX hdec emb g hg := by
  funext W
  have hord : W.ord B S hS hX hdec (emb W (f * g)) (hfg W) =
      W.ord B S hS hX hdec (emb W f * emb W g) ((hf W).mul (hg W)) :=
    Ring.ordTotalFracInt_congr _ (hfg W) ((hf W).mul (hg W)) (map_mul (emb W) f g)
  simp only [principalDivisorCoefficients_apply, Pi.add_apply, hord]
  exact PrimeDivisor.ord_mul B S hS hX hdec W (emb W f) (emb W g) (hf W) (hg W)

/-- **Stacks 0ENN for a product.** The prime divisors with `ord_Z(fg) ≠ 0` are locally finite as
soon as those for `f` and those for `g` are: the coefficient family of `div(fg)` is the sum of
the other two, and `Div(X)` is a subgroup of the coefficient families. -/
theorem locallyFinite_principalDivisorCoefficients_mul
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f g : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (hg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W g))
    (hfg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W (f * g)))
    (hfinf : LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb f hf W = 0 then ∅
      else W.support B S hS X)
    (hfing : LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb g hg W = 0 then ∅
      else W.support B S hS X) :
    LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb (f * g) hfg W = 0 then ∅
      else W.support B S hS X := by
  have hmem : principalDivisorCoefficients B S hS hX hdec emb (f * g) hfg ∈
      WeilDivisor B S hS X := by
    rw [principalDivisorCoefficients_mul B S hS hX hdec emb f g hf hg hfg]
    exact add_mem hfinf hfing
  exact hmem

/-- **Stacks 0ENQ.** The principal divisor of a product of rational functions is the sum of
their principal divisors, `div(fg) = div(f) + div(g)` in `Div(X)`.

Local finiteness for `fg` is not assumed: it is deduced from local finiteness for `f` and for
`g`, which is what makes `div(f)` and `div(g)` elements of `Div(X)` in the first place. -/
@[stacks 0ENQ "div(fg) = div(f) + div(g) in Div(X)"]
theorem principalWeilDivisor_mul
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f g : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (hg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W g))
    (hfg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W (f * g)))
    (hfinf : LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb f hf W = 0 then ∅
      else W.support B S hS X)
    (hfing : LocallyFinite fun W : PrimeDivisor B S hS X =>
      if principalDivisorCoefficients B S hS hX hdec emb g hg W = 0 then ∅
      else W.support B S hS X) :
    principalWeilDivisor B S hS hX hdec emb (f * g) hfg
        (locallyFinite_principalDivisorCoefficients_mul B S hS hX hdec emb f g hf hg hfg hfinf
          hfing) =
      principalWeilDivisor B S hS hX hdec emb f hf hfinf +
        principalWeilDivisor B S hS hX hdec emb g hg hfing :=
  Subtype.ext (principalDivisorCoefficients_mul B S hS hX hdec emb f g hf hg hfg)

section RegularLocus

omit [∀ W : PrimeDivisor B S hS X, Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
  [∀ W : PrimeDivisor B S hS X, IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
  [∀ W : PrimeDivisor B S hS X, Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]

/-- Where `f` and `g` are both the image of a unit of `𝒪^h_{X,ξ}`, so is `fg`, the image of a
product being the product of the images. -/
theorem exists_isUnit_emb_mul_eq_algebraMap
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f g : rationalFunctions B S hS hX) (U : Set (points B S hS X))
    (hregf : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W f = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r)
    (hregg : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W g = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r) :
    ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W (f * g) = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r := by
  intro W hW
  obtain ⟨r, hr, hfr⟩ := hregf W hW
  obtain ⟨s, hs, hgs⟩ := hregg W hW
  exact ⟨r * s, hr.mul hs, by rw [map_mul, hfr, hgs, map_mul]⟩

/-- A nonempty open subset of `|X|` over which `f` is invertible and one over which `g` is
invertible meet, `|X|` being irreducible, so a common such open subset exists. -/
theorem exists_isOpen_nonempty_and_regular_of_regular
    (hirr : IrreducibleSpace (points B S hS X))
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f g : rationalFunctions B S hS hX)
    (U V : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hregf : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W f = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r)
    (hregg : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ V →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W g = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r) :
    ∃ W : Set (points B S hS X), IsOpen W ∧ W.Nonempty ∧
      (∀ P : PrimeDivisor B S hS X, P.genericPoint B S hS X ∈ W →
        ∃ r : ↥(P.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
          emb P f = algebraMap _ (P.genericTotalFractionRing B S hS hX hdec) r) ∧
      ∀ P : PrimeDivisor B S hS X, P.genericPoint B S hS X ∈ W →
        ∃ r : ↥(P.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
          emb P g = algebraMap _ (P.genericTotalFractionRing B S hS hX hdec) r := by
  have hpre : IsPreirreducible (Set.univ : Set (points B S hS X)) :=
    hirr.toPreirreducibleSpace.isPreirreducible_univ
  have hne := hpre U V hUopen hVopen (by simpa using hUne) (by simpa using hVne)
  exact ⟨U ∩ V, hUopen.inter hVopen, by simpa using hne,
    fun P hP => hregf P hP.1, fun P hP => hregg P hP.2⟩

end RegularLocus

include hX in
/-- **Stacks 0ENQ.** The principal divisor of a product of rational functions is the sum of
their principal divisors, `div(fg) = div(f) + div(g)` in `Div(X)`, with the local finiteness of
Stacks 0ENN proved for all three divisors from a nonempty open subset of `|X|` over which both
`f` and `g` are invertible. -/
@[stacks 0ENQ "div(fg) = div(f) + div(g) in Div(X), local finiteness proved throughout"]
theorem principalWeilDivisorOfRegularLocus_mul
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X))
    (emb : ∀ W : PrimeDivisor B S hS X, rationalFunctions B S hS hX →+*
      W.genericTotalFractionRing B S hS hX hdec)
    (f g : rationalFunctions B S hS hX)
    (hf : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W f))
    (hg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W g))
    (hfg : ∀ W : PrimeDivisor B S hS X, IsUnit (emb W (f * g)))
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hregf : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W f = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r)
    (hregg : ∀ W : PrimeDivisor B S hS X, W.genericPoint B S hS X ∈ U →
      ∃ r : ↥(W.genericHenselianLocalRing B S hS hX hdec), IsUnit r ∧
        emb W g = algebraMap _ (W.genericTotalFractionRing B S hS hX hdec) r) :
    principalWeilDivisorOfRegularLocus B S hS hX hdec hN hirr emb (f * g) hfg U hUopen hUne
        (exists_isUnit_emb_mul_eq_algebraMap B S hS hX hdec emb f g U hregf hregg) =
      principalWeilDivisorOfRegularLocus B S hS hX hdec hN hirr emb f hf U hUopen hUne hregf +
        principalWeilDivisorOfRegularLocus B S hS hX hdec hN hirr emb g hg U hUopen hUne hregg :=
  Subtype.ext (principalDivisorCoefficients_mul B S hS hX hdec emb f g hf hg hfg)

end WeilForm

/-! ### The principal divisor as a cycle -/

section CycleForm

variable (D : BaseSpaceDimensionSituation.{u})
variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
variable (sX : X ⟶ D.space) (hX : D.IsGood sX)
variable (hdec : IsDecentSpace D.site D.base D.base_mem X)
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
  rationalFunctions D.site D.base D.base_mem hX.1 →+*
    W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)
variable (f : rationalFunctions D.site D.base D.base_mem hX.1)
variable (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (emb W f))

/-- The coefficient of `div(f)` at the integral closed subspace underlying a prime divisor `W` is
`ord_W(f)`; in particular it does not depend on which prime divisor with that subspace is
used. -/
@[simp]
theorem principalDivisorCycleCoefficients_toIntegralClosedSubspace
    (W : PrimeDivisor D.site D.base D.base_mem X) :
    principalDivisorCycleCoefficients D sX hX hdec emb f hf
        (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf W := by
  have hcod := W.codimension_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
  have heq : IntegralClosedSubspace.toPrimeDivisor D.site D.base D.base_mem hX.1
      (W.toIntegralClosedSubspace D.site D.base D.base_mem) hcod = W :=
    IntegralClosedSubspace.toPrimeDivisor_eq D.site D.base D.base_mem hX.1 _ hcod W rfl
  have h1 : principalDivisorCycleCoefficients D sX hX hdec emb f hf
      (W.toIntegralClosedSubspace D.site D.base D.base_mem) =
      principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf
        (IntegralClosedSubspace.toPrimeDivisor D.site D.base D.base_mem hX.1
          (W.toIntegralClosedSubspace D.site D.base D.base_mem) hcod) := dite_eq_left hcod
  rw [h1]
  exact congrArg _ heq

/-- The coefficient of `div(f)` at an integral closed subspace which is not a prime divisor
vanishes, the source's sum being over prime divisors only. -/
theorem principalDivisorCycleCoefficients_of_codimension_ne_one
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) ≠ 1) :
    principalDivisorCycleCoefficients D sX hX hdec emb f hf Z = 0 :=
  dite_eq_right h

/-- An integral closed subspace with a nonzero `div(f)`-coefficient has codimension one. -/
private theorem codimension_eq_one_of_principalDivisorCycleCoefficients_ne_zero
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : principalDivisorCycleCoefficients D sX hX hdec emb f hf Z ≠ 0) :
    codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 :=
  of_not_not fun hc =>
    h (principalDivisorCycleCoefficients_of_codimension_ne_one D sX hX hdec emb f hf hc)

/-- The prime divisors with `ord_Z(f) ≠ 0` and the integral closed subspaces with a nonzero
`div(f)`-coefficient have the same point sets, so local finiteness of the family indexed by
prime divisors — Stacks 0ENN — gives local finiteness of the family indexed by integral closed
subspaces. -/
theorem locallyFinite_principalDivisorCycleCoefficients_ne_zero
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf W = 0 then ∅
      else W.support D.site D.base D.base_mem X) :
    LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if principalDivisorCycleCoefficients D sX hX hdec emb f hf Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  intro x
  obtain ⟨V, hV, hVfin⟩ := hfin x
  refine ⟨V, hV, Set.Finite.subset
    (hVfin.image (PrimeDivisor.toIntegralClosedSubspace D.site D.base D.base_mem)) ?_⟩
  rintro Z ⟨p, hpZ, hpV⟩
  rw [Set.mem_ite_empty_left] at hpZ
  obtain ⟨hne, hpZ'⟩ := hpZ
  have hcod := codimension_eq_one_of_principalDivisorCycleCoefficients_ne_zero D sX hX hdec emb
    f hf hne
  have hWZ : (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod).toIntegralClosedSubspace
      D.site D.base D.base_mem = Z :=
    IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
      hX.1 Z hcod
  have hWne : principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf
      (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod) ≠ 0 := by
    rw [← principalDivisorCycleCoefficients_toIntegralClosedSubspace D sX hX hdec emb f hf,
      hWZ]
    exact hne
  refine ⟨Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod, ⟨p, ?_, hpV⟩, hWZ⟩
  rw [Set.mem_ite_empty_left]
  exact ⟨hWne, hpZ'⟩

/-- **Stacks 0EQ1, well-definedness.** The coefficients of `div(f)` form an `(n-1)`-cycle on a
good integral algebraic space `X/B` of δ-dimension `n`: their support is locally finite by
Stacks 0ENN, and an integral closed subspace carrying a nonzero coefficient is a prime divisor,
hence has δ-dimension `n - 1` by Stacks 0EPZ. -/
theorem principalDivisorCycleCoefficients_mem_cyclesOfDimension
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    principalDivisorCycleCoefficients D sX hX hdec emb f hf ∈
      cyclesOfDimension D sX (n - 1) := by
  refine ⟨locallyFinite_principalDivisorCycleCoefficients_ne_zero D sX hX hdec emb f hf hfin,
    fun Z hZ => ?_⟩
  exact ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint d hd hn Z).out 2 3).mp
    (codimension_eq_one_of_principalDivisorCycleCoefficients_ne_zero D sX hX hdec emb f hf hZ)

/-- **Stacks 0EQ1.** The *principal divisor associated to `f ∈ R(X)^*`*, that is
`div(f) = ∑_Z ord_Z(f) [Z]`, as an element of `Z_{n-1}(X)` for `X/B` good and integral with
`dim_δ(X) = n`.

This is the principal divisor of Stacks 0ENP read as a cycle: the formal sum is the same, and it
is an `(n-1)`-cycle because a prime divisor of such an `X` has δ-dimension `n - 1` by
Stacks 0EPZ. Local finiteness is Stacks 0ENN, the argument `hfin`, which
`AlgebraicGeometry.Space.principalDivisorCycleOfRegularLocus` discharges. -/
@[stacks 0EQ1 "div(f) = ∑ ord_Z(f) [Z] as an element of Z_{n-1}(X); the δ-dimension of a prime
  divisor is n-1 by Stacks 0EPZ, whose dimension-function hypotheses d and hd are Stacks 0EDN,
  carried; local finiteness is Stacks 0ENN, the argument hfin, discharged by
  locallyFinite_principalDivisorCoefficients_ne_zero in principalDivisorCycleOfRegularLocus"]
def principalDivisorCycle
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    CycleGroup D sX (n - 1) :=
  ⟨principalDivisorCycleCoefficients D sX hX hdec emb f hf,
    principalDivisorCycleCoefficients_mem_cyclesOfDimension D sX hX hdec emb f hf hfin hint d
      hd hn⟩

/-- The coefficient family of `div(f)` as a cycle is the one already in the library. -/
@[simp]
theorem principalDivisorCycle_coe
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    (principalDivisorCycle D sX hX hdec emb f hf hfin hint d hd hn).1 =
      principalDivisorCycleCoefficients D sX hX hdec emb f hf :=
  rfl

/-- **Stacks 0EQ1.** The principal divisor `div(f) = ∑_Z ord_Z(f) [Z]` of a rational function
`f ∈ R(X)^*` as an element of `Z_{n-1}(X)`, with the local finiteness of Stacks 0ENN proved from
a nonempty open subset of `|X|` over which `f` is invertible. -/
@[stacks 0EQ1 "div(f) in Z_{n-1}(X), with local finiteness (Stacks 0ENN) proved from a nonempty
  open U over which f is invertible, the datum (U, hUopen, hUne, hreg) of the first sentence of
  the source's own proof of that lemma; the dimension-function hypotheses d and hd are
  Stacks 0EDN, carried"]
def principalDivisorCycleOfRegularLocus
    (hN : HasEtaleLocalProperty D.site D.base D.base_mem X
      (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (U : Set (points D.site D.base D.base_mem X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hreg : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      W.genericPoint D.site D.base D.base_mem X ∈ U →
        ∃ r : ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec), IsUnit r ∧
          emb W f =
            algebraMap _ (W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec) r)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    CycleGroup D sX (n - 1) :=
  principalDivisorCycle D sX hX hdec emb f hf
    (locallyFinite_principalDivisorCoefficients_ne_zero D.site D.base D.base_mem hX.1 hdec hN
      hint.2.2 emb f hf U hUopen hUne hreg) hint d hd hn

end CycleForm

/-! ### The principal divisors inside the group of cycles -/

section PrincipalSet

variable (D : BaseSpaceDimensionSituation.{u})
variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
variable (sX : X ⟶ D.space) (hX : D.IsGood sX)
variable (hdec : IsDecentSpace D.site D.base D.base_mem X)
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]

/-- The *principal divisors* in `Z_k(X)`: the `k`-cycles whose coefficient family is the
principal divisor `div(f)` of some rational function `f` with `f ∈ R(X)^*`.

This is the set of cycles that Stacks 0EQ6 part (1) consumes on `X`, and the inhabitant of the
`principalDivisors` field of `AlgebraicGeometry.Space.ChowTarget`; the embeddings of
Stacks 0ENK remain existentially quantified parameters, this repository not constructing
them. -/
def principalDivisorCycleSet (k : ℤ) : Set (CycleGroup D sX k) :=
  {c | ∃ (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
        rationalFunctions D.site D.base D.base_mem hX.1 →+*
          W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)
      (f : rationalFunctions D.site D.base D.base_mem hX.1)
      (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (emb W f)),
    (c : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) =
      principalDivisorCycleCoefficients D sX hX hdec emb f hf}

/-- `div(f)` is one of the principal divisors of `Z_{n-1}(X)`. -/
theorem principalDivisorCycle_mem_principalDivisorCycleSet
    (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      rationalFunctions D.site D.base D.base_mem hX.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hX.1 hdec)
    (f : rationalFunctions D.site D.base D.base_mem hX.1)
    (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem X, IsUnit (emb W f))
    (hfin : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if principalDivisorCoefficients D.site D.base D.base_mem hX.1 hdec emb f hf W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    principalDivisorCycle D sX hX hdec emb f hf hfin hint d hd hn ∈
      principalDivisorCycleSet D sX hX hdec (n - 1) :=
  ⟨emb, f, hf, rfl⟩

end PrincipalSet

/-- The principal divisors on each integral closed subspace of a good algebraic space `Y/B`,
as a family of the exact shape that the `principalDivisors` field of
`AlgebraicGeometry.Space.ChowTarget` asks for.

The field's docstring records that the repository lacked the principal divisors `div(f)`,
`f ∈ R(W)^*`, which part (1) of Stacks 0EQ6 consumes; this is them, each
`AlgebraicGeometry.Space.principalDivisorCycleSet` on the subspace. Goodness and decency of each
subspace over the base, and the ring-theoretic hypotheses on the henselian local rings at the
generic points of its prime divisors, are the explicit hypotheses `hgood`, `hdecW`, `hnontriv`,
`hnoeth` and `hdim`: a closed subspace of a good algebraic space is good, but that is not proved
in this repository. -/
def principalDivisorsOfIntegralClosedSubspaces (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space) (k : ℤ)
    (hgood : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      D.IsGood (W.subspace.ι ≫ sY))
    (hdecW : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      IsDecentSpace D.site D.base D.base_mem W.subspace.toFunctor)
    (hnontriv : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
      Nontrivial ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (hgood W).1 (hdecW W)))
    (hnoeth : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
      IsNoetherianRing
        ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (hgood W).1 (hdecW W)))
    (hdim : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
      Ring.KrullDimLE 1
        ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (hgood W).1 (hdecW W))) :
    ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      Set (CycleGroup D (W.subspace.ι ≫ sY) k) :=
  fun W =>
    letI := hnontriv W
    letI := hnoeth W
    letI := hdim W
    principalDivisorCycleSet D (W.subspace.ι ≫ sY) (hgood W) (hdecW W) k

end AlgebraicGeometry.Space

end
