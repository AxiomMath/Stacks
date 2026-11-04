module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper
public import StacksCore.Tactic.StacksAttribute

/-!
# Push and pull along a finite locally free morphism

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
schemes locally of finite type over `S` and let `f : X ⟶ Y` be finite locally free of degree `d`.
Stacks 02RH asserts two things: that `f` is proper and flat of relative dimension `0`, so that
proper pushforward and flat pullback are both defined along it, and that

  `f_* f^* α = d α`   for every `α ∈ Z_k(Y)`.

The first assertion is already available: a finite locally free morphism is finite, flat and
locally of finite presentation (Stacks 02KB), a finite morphism is proper, and a morphism locally
of finite type is locally quasi-finite exactly when it has relative dimension zero (Stacks 0397).
Those three consequences are
`Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank`,
`Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank` and
`Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank`, and they are recorded
against this tag below.

The second assertion is reduced here to a single statement about one fibre, which is the whole
of its mathematical content; see the implementation notes.

## Main definitions

* `Stacks.Chow.FibreDegreeIsRank` — the assertion that along `f` the flat pullback
  multiplicities on a fibre, weighted by the residue degrees of its points, sum to `d`.

## Main results

* `Stacks.Chow.relativeDimension_eq_of_relativeDimension_zero` — along a morphism of relative
  dimension zero the relative dimension over the base is unchanged.
* `Stacks.Chow.properPushforward_flatPullback_apply` — the coefficient of `f_* f^* α` at a point
  `y` of `Y` is the coefficient of `α` at `y` times the weighted degree of the fibre over `y`.
* `Stacks.Chow.properPushforward_flatPullback` — the identity `f_* f^* α = d α`, granted
  `Stacks.Chow.FibreDegreeIsRank`.

## Implementation notes

### Relative dimension is unchanged along `f`

Proper pushforward weights the coefficient at a point `x` of `X` by the residue degree of `x`
only when the relative dimension over `S` at `x` agrees with the relative dimension at `f x`,
and by zero otherwise. For `f` of relative dimension zero that proviso never bites: relative
dimension grows along `f` by the transcendence degree of the residue field extension, and that
degree is at most the relative dimension of `f`, hence zero. So the case distinction inside
`Stacks.Chow.properPushforward_apply` disappears, and the composite `f_* f^*` becomes a plain
sum over the fibre.

### What the reduction leaves

After that, the coefficient of `f_* f^* α` at `y` is the coefficient of `α` at `y` times

  `∑_{x ∈ f^{-1}(y)} mult_x(f^{-1}(Z)) · [κ(x) : κ(y)]`,

where `Z` is the integral closed subscheme with generic point `y` and `mult_x` is the flat
pullback multiplicity `Stacks.Chow.flatPullbackWeight`. The identity of the tag is therefore
equivalent to that sum being `d` for every `y` of relative dimension `k`, which is
`Stacks.Chow.FibreDegreeIsRank`.

That sum is the degree of the fibre of `f` over `y`, read off from its local pieces: the fibre is
`Spec` of a finite `κ(y)`-algebra of dimension `f.finrank y`, that algebra is Artinian, hence the
product of its localizations `A_x` at the points `x` of the fibre, and
`dim_{κ(y)} A_x = length(A_x) · [κ(x) : κ(y)]`, where `A_x` is the stalk
`𝒪_{X, x} / 𝔪_y 𝒪_{X, x}` whose length is the multiplicity by Stacks 02RB
(`Stacks.Chow.flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal`).

That chain is carried out in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength`, which proves for a finite
flat morphism locally of finite type that the fibre sum of the local lengths, weighted by the
separable and inseparable degrees of the residue field extensions separately, is `f.finrank y`.
Its two weights multiply to `[κ(x) : κ(y)]`, and `f.finrank y` is `d` for a morphism finite
locally free of degree `d` by
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq`, so that statement and the
sum here differ only by those two rewritings. The statement is `private`, however, as is every
lemma of the chain that proves it, so it cannot be named from outside that module; the sum is
therefore carried as a hypothesis here.

The source argues differently, through the cycle of a coherent module: `[Z] = [𝒪_Z]_k`
(Stacks 02QY), `f^* [𝒪_Z]_k = [f^* 𝒪_Z]_k` (Stacks 02RE) and `f_* [F]_k = [f_* F]_k`
(Stacks 02R6), after which `f_* f^* 𝒪_Z` is finite locally free of rank `d` on `Z`. The first
three inputs are all available — Stacks 02RE, part (2), cycle identity is
`Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf` and part (1) is
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le`, alongside the two dimension
bounds of that tag and the two parts of Stacks 02R6 — but the last step is not: no declaration
identifies the cycle of a finite locally free module of rank `d` with `d` times the fundamental
cycle of its ambient subscheme. So that route is not open either.

### No `@[stacks 02RH "push-pull formula"]`

The identity of the tag is unconditional. `Stacks.Chow.properPushforward_flatPullback` carries
`Stacks.Chow.FibreDegreeIsRank` as a hypothesis, so it is not the tagged statement and bears no
attribute. What is missing is a declaration, under any name, proving
`Stacks.Chow.FibreDegreeIsRank C sX sY f d k` for a morphism `f` finite locally free of rank
`d`; no such declaration is reachable, for the reason given above. The first assertion of the
tag is recorded below, so the tag is covered in part.

## References

* [Stacks Project, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Stacks 02RH, the first assertion -/

add_to_stacks 02RH "properness" Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank
add_to_stacks 02RH "flatness" Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank
add_to_stacks 02RH "relative dimension zero"
  Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank

/-! ### Relative dimension along a morphism of relative dimension zero -/

/-- Along a morphism of relative dimension zero the relative dimension over the base is
unchanged: it grows by the transcendence degree of the residue field extension, which is at most
the relative dimension of the morphism. -/
theorem relativeDimension_eq_of_relativeDimension_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f 0) (x : X) :
    relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (f.base x) := by
  have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x
  rw [hbase] at hstep
  have htrdeg := toNat_residueTrdeg_le_of_relativeDimension f 0 hf x
  omega

/-! ### The composite of flat pullback and proper pushforward -/

/-- The coefficient of `f_* f^* α` at a point `y` of `Y`, for `f` flat and proper of relative
dimension zero: the coefficient of `α` at `y`, times the sum over the fibre of `f` above `y` of
the flat pullback multiplicities weighted by the residue degrees.

The case distinction in the coefficient formula for proper pushforward is vacuous here, because
relative dimension is unchanged along a morphism of relative dimension zero. -/
theorem properPushforward_flatPullback_apply (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f 0) (k : ℤ) (α : CycleGroup C sY k) (y : Y) :
    (properPushforward C sX sY f hbase (k + ((0 : ℕ) : ℤ))
          (flatPullback C sX sY f hbase 0 hf k α)).1 y =
      α.1 y * ∑ᶠ x ∈ f.base ⁻¹' {y},
        flatPullbackWeight C sX f (k + ((0 : ℕ) : ℤ)) x * (f.residueDegree x : ℤ) := by
  rw [properPushforward_apply, mul_finsum_mem]
  refine finsum_mem_congr rfl fun x hx ↦ ?_
  have hxy : f.base x = y := hx
  rw [flatPullback_apply,
    ite_eq_left (relativeDimension_eq_of_relativeDimension_zero C sX sY f hbase hf x), hxy]
  ring

/-! ### The degree of a fibre -/

/-- The assertion that along `f` the flat pullback multiplicities on the fibre above a point of
relative dimension `k`, weighted by the residue degrees of the points of that fibre, sum to `d`.

This is the degree of the fibre of `f` over that point, read off from its local pieces; for `f`
finite locally free of degree `d` it is `d`, and that is the whole content of the identity of
Stacks 02RH. It is carried as a hypothesis because the statement proving it is not reachable
from here; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFree`. -/
def FibreDegreeIsRank (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (d : ℕ)
    (k : ℤ) : Prop :=
  ∀ y : Y, relativeDimension C.dimensionFunction sY y = k →
    (∑ᶠ x ∈ f.base ⁻¹' {y},
      flatPullbackWeight C sX f (k + ((0 : ℕ) : ℤ)) x * (f.residueDegree x : ℤ)) = (d : ℤ)

/-- **Stacks 02RH, the second assertion, granted the degree of each fibre.** For `f : X ⟶ Y`
flat and proper of relative dimension zero whose fibres have weighted degree `d`,

  `f_* f^* α = d α`   in `Z_k(Y)`.

The statement transports the left hand side along the equality `k + 0 = k` of delta-dimensions,
which is the degree that pullback and pushforward along `f` produce; that equality is taken as a
hypothesis so that the statement typechecks, exactly as in
`Stacks.Chow.flatPullback_gysinRule_extendCycleGroup`.

The hypothesis `Stacks.Chow.FibreDegreeIsRank` is only used at the points carrying a nonzero
coefficient of `α`, which have relative dimension `k`; elsewhere both sides vanish. -/
theorem properPushforward_flatPullback (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [Flat f] [IsProper f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f 0) (d : ℕ) (k : ℤ)
    (hdeg : FibreDegreeIsRank C sX sY f d k)
    (hcast : k + ((0 : ℕ) : ℤ) = k) (α : CycleGroup C sY k) :
    (hcast ▸ properPushforward C sX sY f hbase (k + ((0 : ℕ) : ℤ))
          (flatPullback C sX sY f hbase 0 hf k α) : CycleGroup C sY k) = (d : ℤ) • α := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hsmul : ((d : ℤ) • α : CycleGroup C sY k).1 y = (d : ℤ) * α.1 y := rfl
  rw [val_cycleGroup_cast C sY hcast,
    properPushforward_flatPullback_apply C sX sY f hbase hf k α y, hsmul]
  by_cases hy : α.1 y = 0
  · rw [hy, zero_mul, mul_zero]
  · rw [hdeg y ((mem_cyclesOfDimension_iff_forall_point C sY k α.1).1 α.2 y hy), mul_comm]

end Stacks.Chow

end
