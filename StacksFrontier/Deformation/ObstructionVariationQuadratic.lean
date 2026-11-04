module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The obstruction-variation map of a dévissage is quadratic, not additive

Let `A' → A` be a surjection with nilpotent kernel `I`, let `P'` be a flat `A'`-algebra, let
`P = P' ⊗_{A'} A` and let `M` be an `A`-flat finite `P`-module. The dévissage that would carry
the square-zero case of Stacks 0DZ2 to the nilpotent case — route 4 of the implementation notes
of `StacksFrontier.Deformation.FlatAlgebraLiftLocalization`, and the route recorded as missing in
`StacksFrontier.Deformation.FlatModuleLiftLocalization` — writes `A_j = A'/Iʲ`, `P_j = P' ⊗ A_j`,
`K_j = Iʲ/Iʲ⁺¹`, and asks for a map

  `∂ : Ext¹_P(M, M ⊗ K_j P) → Ext²_P(M, M ⊗ K_{j+1} P)`

along the `Ext¹`-torsor of `P_{j+1}`-lifts of `M_j`, satisfying

  (a) `ω(e · M_{j+1}) = ω(M_{j+1}) + ∂(e)`, and
  (b) `∂` additive and `P`-linear, so that `im ∂` is a `P`-submodule.

**(a) and (b) are jointly contradictory at `j = 1`, which is the step the dévissage starts at.**
This file proves that. The reason is a cup-square term: a lift is a differential `d_{j+1}` on a
free `P'`-resolution reduced mod `Iʲ⁺¹`, the torsor acts by `d_{j+1} + ε` with `ε` of
`K_j`-coefficients, and lifting one step further gives

  `(d_{j+2} + ε̃)² = d_{j+2}² + (d_{j+2} ε̃ + ε̃ d_{j+2}) + ε̃²`,

whose last term has coefficients in `I²ʲ`. Read in `K_{j+1} = Iʲ⁺¹/Iʲ⁺²` it vanishes exactly
when `2j ≥ j + 2`, that is for `j ≥ 2`; at `j = 1` it is the Yoneda square of `e` transported
along the multiplication `K_1 ⊗ K_1 → K_2`, and it is not additive in `e`. So the honest law is

  `ω(e · M_{j+1}) = ω(M_{j+1}) + δ(e) + e ∪ e`

with `δ` the Bockstein of `0 → K_{j+1} → Iʲ/Iʲ⁺² → K_j → 0`; `∂ = δ + (· ∪ ·)` is a quadratic
map, and the image of a quadratic map is not a submodule.

## Main results

* `Module.Flat.exists_eq_smul_of_smul_eq_zero`: for a flat module, an element killed by `b` lies
  in `a • M` as soon as the annihilator of `b` in the ring is contained in `(a)`. This is the
  equational criterion for flatness, specialized.
* `Deformation.ObstructionVariation.mul_self_mem_of_hasSecondOrderFlatLift`: **the quadratic
  law, in elementary form.** If a first-order deformation whose structure matrix is `E` extends
  to a flat lift over the second-order thickening, then `E * E ≡ 0` modulo `t`. The obstruction
  to extending a first-order deformation is the *matrix square*.
* `Deformation.ObstructionVariation.liftsFirstOrder_e`,
  `Deformation.ObstructionVariation.liftsFirstOrder_f` and
  `Deformation.ObstructionVariation.not_liftsFirstOrder_add`: two first-order deformations of
  one module that each extend to second order, whose sum does not. The set of unobstructed
  classes is therefore **not** a subgroup of `Ext¹`.
* `Deformation.ObstructionVariation.not_exists_additive_obstructionVariation`: consequently
  there is no `∂` satisfying (a) and (b). Any `ω` vanishing exactly on the unobstructed classes
  fails to be a translate of an additive map.
* `Deformation.ObstructionVariation.not_exists_additive_obstructionVariation_of_param`: the same
  statement for an abstract group of first-order deformations, with the identification of that
  group with `M₂(ZMod 2)` carried as a hypothesis. That hypothesis is the one step of the
  reduction this file does not formalize, so this is the form in which the refutation applies
  to `Ext¹_P(M, M ⊗ K_1)` itself.

## Implementation notes

**What the counterexample is.** `A' = ZMod 8`, `A = ZMod 2`, `I = (2)` with `I³ = 0`;
`P' = A'[x]/(x²)`, realized as `TrivSqZeroExt A' A'` with `x = inr 1`; `P = P' ⊗_{A'} A` is
`(ZMod 2)[x]/(x²)` and `M = (ZMod 2)²` with `x` acting as zero. All of Stacks 0DZ2's hypotheses
on this data hold: `A' → A` is surjective with nilpotent kernel, `P'` is free hence flat over
`A'`, `P` is Noetherian, and `M` is finite over `P` and flat (indeed free) over the field `A`.
Over `P` one has `Ext^•_P(M, M) = M₂(ZMod 2) ⊗ (ZMod 2)[ε]` with `ε` in degree one, so
`Ext¹_P(M, M ⊗ K_1) = Ext²_P(M, M ⊗ K_2) = M₂(ZMod 2)` and the cup-square `Ext¹ → Ext²` is
`E ↦ E * E`. The first-order lifts of `M` over `P_2 = (ZMod 4)[x]/(x²)` are the free
`ZMod 4`-modules of rank two with `x` acting by `2E`, `E ∈ M₂(ZMod 2)`, and the torsor action of
`Ext¹` is `E ↦ E + e`. Matrix squaring is not additive, and over `ZMod 2` the set
`{E : E * E = 0}` is not even closed under addition: `!![0,1;0,0]` and `!![0,0;1,0]` square to
zero and their sum `!![0,1;1,0]` squares to `1`.

**What is proved here and what is not.** `HasSecondOrderFlatLift` is stated in elementary
module-theoretic terms — a flat module over the big ring, a family whose reductions are
independent and spanning modulo `t`, and the structure constants of the action of `x` modulo
`t²` — and not as `Deformation.HasFlatModuleLift` applied to the first-order lift `M₂^{(E)}`.
The two agree: a family independent and spanning modulo the nilpotent `t` generates, so the
reduction of such an `N` modulo `t²` is the free `A'/(t²)`-module on `m` with `x` acting by
`t E`, which is `M₂^{(E)}`, and conversely. The step **not** formalized here is the
identification of the parametrization `E` with the `Ext¹`-torsor action, i.e. that the class of
`M₂^{(E)} ` minus the class of `M₂^{(E')}` in `Ext¹_P(M, M ⊗ K_1)` is `E - E'`. That
identification is what makes the index group of
`not_exists_additive_obstructionVariation` *be* `Ext¹`; it is the defining property of the
torsor action (two lifts differ by the cocycle given by the difference of their `x`-actions
divided by `t`), and no `Ext` API in this repository presents it, which is precisely the gap
recorded in `StacksFrontier.Deformation.FlatModuleLiftLocalization`. It is carried as an explicit
hypothesis by
`Deformation.ObstructionVariation.not_exists_additive_obstructionVariation_of_param`, so what
the refutation assumes is visible in a statement rather than only in this note. Nothing else is
assumed: the refutation of additivity is carried entirely by the three lemmas about
`HasSecondOrderFlatLift`.

The other unformalized link is bookkeeping with no mathematical content, and is spelled out
here so that it is not mistaken for a gap in the argument. `HasSecondOrderFlatLift A' P' t x E`
is equivalent to `Deformation.HasFlatModuleLift (algebraMap A' P') (P' → P'/t²P') (M₂^{(E)})`,
where `M₂^{(E)}` is the free `A'/(t²)`-module on `ι` with `x` acting by `t E`. Left to right:
reduce the module and its generators modulo `t²`, where independence and spanning modulo the
nilpotent `t` make the generators an `A'/(t²)`-basis. Right to left: lift the basis of
`M₂^{(E)}` through `N → N/t²N`; spanning modulo `t` is inherited from spanning modulo `t²`,
independence modulo `t` from freeness of `M₂^{(E)}`, `x • N ⊆ t • N` from `x` acting as zero on
`M = N/tN`, and the structure constants from the chosen isomorphism. Carrying that out in Lean
means building `P'/t²P'` and `M₂^{(E)}` and transporting four conditions across a tensor-product
identification; it would not change the conclusion, and it is not done here.

**Why this does not merely say that `∂` is hard to construct.** `∂` *exists* — set
`∂(e) = ω(e · M_{j+1}) - ω(M_{j+1})`, which satisfies (a) by fiat. What the counterexample
refutes is (b), and with it the use the dévissage makes of `∂`: route 4 forms the quotient
`Ext²/im ∂` and applies Stacks 05EC to it, and `im ∂` is not a submodule, so that quotient does
not exist. A multiplicative set cannot be made to act invertibly on a subset that is not closed
under addition either. The repair the route would need is a local-global principle for the
solvability of the *quadratic* equation `δ(e) + e ∪ e = -ω` over `P`, which is not Stacks 05EC
and is false for general quadratic equations.

**Where the route survives.** For `j ≥ 2` the cup-square term dies, as the degree count above
shows, so `∂ = δ` is the Bockstein there and (b) does hold. Only the first step of the
dévissage, from `P = P_1` to `P_2`, is quadratic — and that is the step at which the induction
of route 4 starts, so the route is blocked rather than merely delayed.

**Refiltering the kernel does not avoid it in this example.** The dévissage is free to replace
the powers `Iʲ` by any chain `I = J_0 ⊇ J_1 ⊇ … ⊇ J_m = 0` with square-zero steps. The square
term at the stage that lifts from `A'/J_k` to `A'/J_{k+1}` is read in `J_k/J_{k+1}` and comes
from the correction group `Ext¹(M, M ⊗ J_{k-1}/J_k)`, so it dies at every stage exactly when
`J_{k-1}² ⊆ J_{k+1}` throughout. For `A' = ZMod 8` and `I = (2)` the only ideals are
`(1) ⊋ (2) ⊋ (4) ⊋ 0`, so the only chain with square-zero steps is `(2) ⊋ (4) ⊋ 0` — the chain
`(2) ⊋ 0` has a step of kernel `(2)` with `(2)² = (4) ≠ 0` — and there `J_0² = (4) ⊄ J_2 = 0`.
Padding with repeats does not help: a repeated step has correction group zero, so at the stage
that must reach `0` there is nothing to correct with. Hence the quadratic term is a property of
this `A'` and not of the choice of filtration.

This is not a general theorem about nilpotent ideals: for `A' = k[u,v]/(u², uv, v³)` and
`I = (u,v)` the chain `(u,v) ⊋ (u,v²) ⊋ (v²) ⊋ 0` does satisfy `J_{k-1}² ⊆ J_{k+1}` at every
stage, so there a refiltering *would* linearize all the steps. That is why a counterexample has
to name a ring: Stacks 0DZ2 and Stacks 0DZ7 quantify over all `A'`, so one `A'` at which no
filtration linearizes the dévissage is enough to block the route, and `ZMod 8` — nilpotency
index three, the smallest index beyond the square-zero case — is such an `A'`.

**What the right object is.** The variation is quadratic because the lifting problem is a
Maurer–Cartan problem, not a sequence of linear ones. A lift of `M` to `P'` is a differential
on a bounded-above free `P'`-resolution lifting `d`, that is a solution of `(d + ε)² = 0` for
`ε` in the filtered differential graded algebra `End(F̃) ⊗ I`; written out, `d ε + ε d + ε² = 0`.
The obstruction theory of such an equation is the obstruction theory of a differential graded
Lie algebra: at each filtration step the correction is governed by the *linear* term
`d ε + ε d`, whose cohomological shadow is the Bockstein `δ`, together with the *bracket* `ε²`,
whose shadow is the Yoneda square. The right form of the induction step is therefore the
solvability of the quadratic equation `δ(e) + e ∪ e = -ω(M_{j+1})` in `Ext²`, and the right
question for Stacks 0DZ7, 0DZB and 0DZ3 is whether that solvability descends from `Q` and from
the localizations `P_g` — a local-global principle for a quadratic equation over `P`, with no
analogue in Stacks 05EC. It cannot be a formal consequence of flatness plus power torsion:
`c² = -1` is solvable over `ℂ` and not over `ℝ`, so any such principle has to use the specific
geometry of `P → Q` (flat, and an isomorphism modulo `J'`). That is a different theorem from
anything in this repository, and it is the honest statement of what those three tags still
lack. This paragraph is a suggestion about where to look, not a verified route.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public noncomputable section

open Finset TrivSqZeroExt

universe u v w

/-- **An element of a flat module killed by `b` lies in `a • M`, provided the annihilator of `b`
in the ring lies in `(a)`.** This is the equational criterion for flatness (Stacks 00HK) applied
to the one-term relation `b • v = 0`: it factors as `v = ∑ aⱼ • yⱼ` with every `aⱼ` killed by
`b`, hence divisible by `a`. -/
theorem Module.Flat.exists_eq_smul_of_smul_eq_zero {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] {a b : R}
    (hab : ∀ c : R, b * c = 0 → ∃ d : R, c = a * d) {m : M} (hm : b • m = 0) :
    ∃ w : M, m = a • w := by
  obtain ⟨k, A, y, hx, hf⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (ι := Fin 1) (f := fun _ => b)
      (x := fun _ => m) (by simpa using hm)
  choose d hd using fun j => hab (A 0 j) (by simpa using hf j)
  refine ⟨∑ j, d j • y j, ?_⟩
  have h1 : m = ∑ j, A 0 j • y j := hx 0
  rw [h1, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hd j, mul_smul]

namespace Deformation.ObstructionVariation

/-! ### First-order deformations and their second-order obstruction -/

/-- **A first-order deformation with structure matrix `E` that extends to second order.**

Here `t : A'` cuts out the thickening (`t` plays the role of a generator of `I = ker(A' → A)`,
with `t³ = 0`) and `x : P'` with `x² = 0` is the coordinate of `P' = A'[x]/(x²)`. The data is a
`P'`-module `N`, flat over `A'`, together with a family `m : ι → N` which is independent and
spanning modulo `t` — so that `N/tN` is the free `A'/(t)`-module on `m`, with `x` acting as zero
because `x • N ⊆ t • N` — and whose structure constants for the action of `x` are `t` times `E`,
modulo `t²`.

Reducing such an `N` modulo `t²` gives the first-order lift of `M = (A'/t)^ι` whose `x`-action
is `t E`; so this predicate says exactly that the first-order deformation `E` of `M` is
unobstructed, i.e. extends to an `A'`-flat `P'`-module. -/
def HasSecondOrderFlatLift (A' : Type u) (P' : Type u) [CommRing A'] [CommRing P']
    [Algebra A' P'] (t : A') (x : P') {ι : Type w} [Fintype ι] (E : Matrix ι ι A') : Prop :=
  ∃ (N : Type v) (_ : AddCommGroup N) (_ : Module A' N) (_ : Module P' N)
      (_ : IsScalarTower A' P' N), Module.Flat A' N ∧ ∃ m : ι → N,
    (∀ (c : ι → A') (w : N), ∑ l, c l • m l = t • w → ∀ l, ∃ d : A', c l = t * d) ∧
    (∀ n : N, ∃ (c : ι → A') (w : N), n = (∑ l, c l • m l) + t • w) ∧
    (∀ n : N, ∃ w : N, x • n = t • w) ∧
    (∀ i, ∃ n : N, x • m i = t • (∑ j, E j i • m j) + (t ^ 2) • n)

/-- **The obstruction to extending a first-order deformation is the matrix square.**

If the first-order deformation with structure matrix `E` extends to an `A'`-flat `P'`-module,
then `E * E ≡ 0` modulo `t`. This is the elementary form of the cup-square term in the
obstruction-variation law: `ω(E) = E * E` up to the Bockstein, and squaring is quadratic.

The proof is the curvature computation. Writing `S i = ∑ⱼ Eⱼᵢ • mⱼ`, the hypothesis is
`x • mᵢ = t • S i + t² • nᵢ`; applying `x` once more and using `x² = 0`, `t³ = 0` and
`x • N ⊆ t • N` leaves `t² • (∑ₗ (E * E)ₗᵢ • mₗ) = 0`, flatness moves that into `t • N`, and
independence modulo `t` reads off the coefficients. -/
theorem mul_self_mem_of_hasSecondOrderFlatLift {A' P' : Type u} [CommRing A'] [CommRing P']
    [Algebra A' P'] {ι : Type w} [Fintype ι] {t : A'} (ht : t ^ 3 = 0)
    (hann : ∀ c : A', t ^ 2 * c = 0 → ∃ d : A', c = t * d) {x : P'} (hx : x ^ 2 = 0)
    {E : Matrix ι ι A'} (h : HasSecondOrderFlatLift.{u, v} A' P' t x E) :
    ∀ l i, ∃ d : A', (E * E) l i = t * d := by
  obtain ⟨N, _, _, _, _, hflat, m, hindep, -, hxt, hE⟩ := h
  choose n hn using hE
  have hsum : ∀ i, ∑ j, E j i • (∑ l, E l j • m l) = ∑ l, (E * E) l i • m l := by
    intro i
    simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  have hlin : ∀ c : ι → A', x • (∑ j, c j • m j)
      = t • (∑ j, c j • (∑ l, E l j • m l)) + (t ^ 2) • (∑ j, c j • n j) := by
    intro c
    rw [Finset.smul_sum]
    have h : ∀ j ∈ Finset.univ, x • (c j • m j)
        = t • (c j • (∑ l, E l j • m l)) + (t ^ 2) • (c j • n j) := fun j _ => by
      rw [smul_comm x (c j) (m j), hn j, smul_add, smul_comm (c j) t, smul_comm (c j) (t ^ 2)]
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  have hzero : ∀ i, (t ^ 2) • (∑ l, (E * E) l i • m l) = 0 := by
    intro i
    have h0 : x • (x • m i) = 0 := by rw [smul_smul, ← pow_two, hx, zero_smul]
    have h1 : x • (x • m i) = t • (x • (∑ j, E j i • m j)) + (t ^ 2) • (x • n i) := by
      rw [hn i, smul_add, smul_comm x t, smul_comm x (t ^ 2)]
    obtain ⟨w, hw⟩ := hxt (n i)
    rw [h1, hlin (fun j => E j i), hw, smul_add, smul_smul, smul_smul, smul_smul] at h0
    have e1 : t * t = t ^ 2 := by ring
    have e2 : t * t ^ 2 = 0 := by rw [← pow_succ']; exact ht
    have e3 : t ^ 2 * t = 0 := by rw [← pow_succ]; exact ht
    rw [e1, e2, e3, zero_smul, zero_smul, add_zero, add_zero, hsum i] at h0
    exact h0
  intro l i
  obtain ⟨w, hw⟩ := Module.Flat.exists_eq_smul_of_smul_eq_zero hann (hzero i)
  exact hindep (fun l => (E * E) l i) w hw l


/-! ### The counterexample: `A' = ZMod 8`, `P' = A'[x]/(x²)`, `M = (ZMod 2)²` -/

/-- The base `A' = ZMod 8` of the counterexample. The thickening is cut out by `t = 2`, whose
cube vanishes: `ker(ZMod 8 → ZMod 2)` is nilpotent of index three, the smallest index at which
Stacks 0DZ2 is not the square-zero case. -/
abbrev Base : Type := ZMod 8

/-- The algebra `P' = A'[x]/(x²)` of the counterexample, realized as the trivial square-zero
extension of `Base` by itself, with `x = inr 1`. It is free of rank two, hence flat, over
`Base`, and its reduction modulo `2` is `(ZMod 2)[x]/(x²)`. -/
abbrev Coordinate : Type := TrivSqZeroExt Base Base

/-- The reduction `A' → A`, that is `ZMod 8 → ZMod 2`. -/
def reduce : Base →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- `t = 2` is nilpotent of index three in `Base = ZMod 8`. -/
theorem base_t_cube : (2 : Base) ^ 3 = 0 := by decide

/-- The annihilator of `t² = 4` in `Base = ZMod 8` is `(2)`: this is the input flatness needs in
`Deformation.ObstructionVariation.mul_self_mem_of_hasSecondOrderFlatLift`. -/
theorem base_ann : ∀ c : Base, (2 : Base) ^ 2 * c = 0 → ∃ d : Base, c = 2 * d := by decide

/-- The coordinate `x = inr 1` of `Coordinate = Base[x]/(x²)` squares to zero. -/
theorem coordinate_x_sq : (inr (1 : Base) : Coordinate) ^ 2 = 0 := by
  rw [pow_two, inr_mul_inr]

/-- The square-zero endomorphism `(a, b) ↦ (0, s * a)` of `Base²` through which the coordinate
`x` will act. For `s = 2` it is `t` times the matrix `!![0,0;1,0]`, the structure matrix of a
nonzero first-order deformation of `M = (ZMod 2)²`; for `s = 0` it is zero, the trivial
deformation. -/
def act (s : Base) : (Base × Base) →ₗ[Base] (Base × Base) where
  toFun v := (0, s * v.1)
  map_add' u v := by simp [mul_add]
  map_smul' a v := by
    refine Prod.ext (by simp) ?_
    simp [mul_left_comm]

/-- The endomorphism `act s` sends `(a, b)` to `(0, s * a)`. -/
@[simp]
theorem act_apply (s : Base) (v : Base × Base) : act s v = (0, s * v.1) := rfl

/-- The endomorphism `act s` squares to zero, so it is an action of the coordinate `x`. -/
theorem act_comp_act (s : Base) : (act s) * (act s) = 0 := by
  refine LinearMap.ext fun v => Prod.ext (by simp) ?_
  show s * (0, s * v.1).1 = (0 : Base × Base).2
  simp

/-- The `Base`-algebra map `Coordinate → End_{Base}(Base²)` sending the coordinate `x` to
`act s`. It is the `P'`-module structure of the first-order deformation with structure matrix
`s` times `!![0,0;1,0]`. -/
def coordHom (s : Base) : Coordinate →ₐ[Base] Module.End Base (Base × Base) :=
  TrivSqZeroExt.lift (Algebra.ofId Base _)
    (LinearMap.toSpanSingleton Base (Module.End Base (Base × Base)) (act s))
    (fun b b' => by
      simp only [LinearMap.toSpanSingleton_apply, smul_mul_smul_comm, act_comp_act, smul_zero])
    (fun r b => by
      simp only [LinearMap.toSpanSingleton_apply, smul_smul, Algebra.ofId_apply,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_mul])
    (fun r b => by
      simp only [LinearMap.toSpanSingleton_apply, Algebra.ofId_apply, op_smul_eq_smul,
        smul_smul, Algebra.algebraMap_eq_smul_one, mul_smul_one, smul_eq_mul])

/-- The map `coordHom s` sends the coordinate `x = inr 1` to `act s`. -/
@[simp]
theorem coordHom_inr_one (s : Base) : coordHom s (inr (1 : Base)) = act s := by
  rw [coordHom, TrivSqZeroExt.lift_apply_inr, LinearMap.toSpanSingleton_apply, one_smul]

/-- The `Coordinate`-module structure on `Base²` in which the coordinate `x` acts by
`act s`. -/
@[instance_reducible] def twistedModule (s : Base) : Module Coordinate (Base × Base) :=
  Module.compHom (Base × Base) (coordHom s).toRingHom

/-- **A first-order deformation of `M = (ZMod 2)²` that extends to second order.**

Only the reduction of the structure matrix modulo `t = 2` matters, since changing `E` by a
multiple of `t` changes the structure constants by a multiple of `t²`; so the invariant of a
first-order deformation lives in `M₂(ZMod 2) = Ext¹_P(M, M ⊗ K_1)`. -/
def LiftsFirstOrder (e : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Prop :=
  ∃ E : Matrix (Fin 2) (Fin 2) Base, E.map reduce = e ∧
    HasSecondOrderFlatLift.{0, 0} Base Coordinate 2 (inr 1) E

/-- **The realization.** The `Coordinate`-module `Base²` on which `x` acts by `act s` is a flat
lift realizing the structure matrix `E`, provided the generators `m` are independent and
spanning modulo `t = 2` and `act s` has matrix `t E` on them modulo `t²`. Every hypothesis is
stated without reference to the twisted module structure. -/
theorem hasSecondOrderFlatLift_of_act (s : Base) (m : Fin 2 → Base × Base)
    (E : Matrix (Fin 2) (Fin 2) Base)
    (hindep : ∀ (c : Fin 2 → Base) (w : Base × Base),
      ∑ l, c l • m l = (2 : Base) • w → ∀ l, ∃ d : Base, c l = 2 * d)
    (hspan : ∀ v : Base × Base, ∃ (c : Fin 2 → Base) (w : Base × Base),
      v = (∑ l, c l • m l) + (2 : Base) • w)
    (hxt : ∀ v : Base × Base, ∃ w : Base × Base, act s v = (2 : Base) • w)
    (hE : ∀ i, ∃ n : Base × Base,
      act s (m i) = (2 : Base) • (∑ j, E j i • m j) + ((2 : Base) ^ 2) • n) :
    HasSecondOrderFlatLift.{0, 0} Base Coordinate 2 (inr 1) E := by
  let inst : Module Coordinate (Base × Base) := twistedModule s
  have hsmul : ∀ (p : Coordinate) (v : Base × Base), p • v = coordHom s p v := fun _ _ => rfl
  have htower : IsScalarTower Base Coordinate (Base × Base) := by
    refine ⟨fun a p v => ?_⟩
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]
  let := htower
  have hx : ∀ v : Base × Base, (inr (1 : Base) : Coordinate) • v = act s v := fun v => by
    rw [hsmul, coordHom_inr_one]
  exact ⟨Base × Base, inferInstance, inferInstance, inst, htower, inferInstance, m, hindep,
    hspan, fun v => by rw [hx]; exact hxt v, fun i => by rw [hx]; exact hE i⟩

/-- The standard generators of `Base²`, in either order, are independent modulo `t = 2`. -/
private theorem prod_indep (m : Fin 2 → Base × Base)
    (hm : ∀ (c : Fin 2 → Base), ∑ l, c l • m l = (c 0, c 1) ∨ ∑ l, c l • m l = (c 1, c 0))
    (c : Fin 2 → Base) (w : Base × Base) (hw : ∑ l, c l • m l = (2 : Base) • w) :
    ∀ l, ∃ d : Base, c l = 2 * d := by
  rcases hm c with h | h <;> rw [h] at hw <;>
      obtain ⟨h0, h1⟩ := Prod.mk.injEq .. ▸ (hw.trans (Prod.smul_mk ..)) <;> intro l <;>
    fin_cases l
  · exact ⟨w.1, by simpa [smul_eq_mul] using h0⟩
  · exact ⟨w.2, by simpa [smul_eq_mul] using h1⟩
  · exact ⟨w.2, by simpa [smul_eq_mul] using h1⟩
  · exact ⟨w.1, by simpa [smul_eq_mul] using h0⟩

/-- **The trivial first-order deformation extends to second order**: the module `Base²` with `x`
acting as zero is flat over `Base` and lifts `M`. -/
theorem liftsFirstOrder_zero : LiftsFirstOrder 0 := by
  refine ⟨0, by simp, hasSecondOrderFlatLift_of_act 0
    ![((1 : Base), (0 : Base)), ((0 : Base), (1 : Base))] 0
    (prod_indep _ fun c => Or.inl ?_) ?_ ?_ ?_⟩
  · rw [Fin.sum_univ_two]; simp
  · exact fun v => ⟨![v.1, v.2], 0, by rw [Fin.sum_univ_two]; simp⟩
  · exact fun v => ⟨0, by simp⟩
  · exact fun i => ⟨0, by simp⟩

/-- **The first-order deformation `!![0,0;1,0]` extends to second order**: it is realized by
`Base²` with `x` acting by `act 2`, on the generators `(1,0)` and `(0,1)`. -/
theorem liftsFirstOrder_f : LiftsFirstOrder !![0, 0; 1, 0] := by
  refine ⟨!![0, 0; 1, 0], ?_, hasSecondOrderFlatLift_of_act 2
    ![((1 : Base), (0 : Base)), ((0 : Base), (1 : Base))] !![0, 0; 1, 0]
    (prod_indep _ fun c => Or.inl ?_) ?_ ?_ ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [Fin.sum_univ_two]; simp
  · exact fun v => ⟨![v.1, v.2], 0, by rw [Fin.sum_univ_two]; simp⟩
  · exact fun v => ⟨(0, v.1), by simp⟩
  · refine fun i => ⟨0, ?_⟩
    fin_cases i <;> rw [Fin.sum_univ_two] <;> simp

/-- **The first-order deformation `!![0,1;0,0]` extends to second order**: the same module, on
the same two generators listed in the other order. -/
theorem liftsFirstOrder_e : LiftsFirstOrder !![0, 1; 0, 0] := by
  refine ⟨!![0, 1; 0, 0], ?_, hasSecondOrderFlatLift_of_act 2
    ![((0 : Base), (1 : Base)), ((1 : Base), (0 : Base))] !![0, 1; 0, 0]
    (prod_indep _ fun c => Or.inr ?_) ?_ ?_ ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [Fin.sum_univ_two]; simp
  · exact fun v => ⟨![v.2, v.1], 0, by rw [Fin.sum_univ_two]; simp⟩
  · exact fun v => ⟨(0, v.1), by simp⟩
  · refine fun i => ⟨0, ?_⟩
    fin_cases i <;> rw [Fin.sum_univ_two] <;> simp

/-- **The sum of those two first-order deformations does not extend to second order.** Its
structure matrix squares to `1`, and by
`Deformation.ObstructionVariation.mul_self_mem_of_hasSecondOrderFlatLift` the obstruction is the
matrix square. So the unobstructed classes are not closed under addition. -/
theorem not_liftsFirstOrder_add :
    ¬ LiftsFirstOrder (!![0, 1; 0, 0] + !![0, 0; 1, 0]) := by
  rintro ⟨E, hE, hlift⟩
  have hsq := mul_self_mem_of_hasSecondOrderFlatLift base_t_cube base_ann coordinate_x_sq hlift
  have hmap : (E * E).map reduce = 0 := by
    ext l i
    obtain ⟨d, hd⟩ := hsq l i
    rw [Matrix.map_apply, hd, map_mul, show reduce 2 = 0 from by decide, zero_mul,
      Matrix.zero_apply]
  rw [Matrix.map_mul, hE] at hmap
  have key : ∀ G : Matrix (Fin 2) (Fin 2) (ZMod 2),
      G = !![0, 1; 0, 0] + !![0, 0; 1, 0] → (G * G) 0 0 = 1 := by
    rintro G rfl
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 := key _ rfl
  rw [hmap, Matrix.zero_apply] at h11
  exact absurd h11 (by decide)

/-- **There is no additive obstruction-variation map.**

Let `ω` assign to a first-order deformation `e` of `M` its obstruction class, so that `ω e = 0`
exactly when `e` is unobstructed, and suppose the variation law `ω(e · M₂) = ω(M₂) + ∂ e` of
clause (a) holds with `∂` additive, as clause (b) asks — here read at the base point `e = 0`,
the trivial first-order deformation, so that `ω 0` is `ω(M₂)`. Then the unobstructed classes are
the kernel of `∂`, hence a subgroup of `Ext¹`; but `!![0,1;0,0]` and `!![0,0;1,0]` are
unobstructed and their sum is not.

So clauses (a) and (b) of the dévissage's requirement on `∂` are jointly contradictory, already
at the first step of the filtration of the kernel. -/
theorem not_exists_additive_obstructionVariation {H : Type u} [AddCommGroup H]
    (ω : Matrix (Fin 2) (Fin 2) (ZMod 2) → H) (hω : ∀ e, ω e = 0 ↔ LiftsFirstOrder e)
    (variation : Matrix (Fin 2) (Fin 2) (ZMod 2) →+ H)
    (hvar : ∀ e, ω e = ω 0 + variation e) : False := by
  have h0 : ω 0 = 0 := (hω 0).2 liftsFirstOrder_zero
  have hzero : ∀ e, LiftsFirstOrder e → variation e = 0 := fun e he => by
    have h := hvar e
    rw [h0, zero_add, (hω e).2 he] at h
    exact h.symm
  refine not_liftsFirstOrder_add ((hω _).1 ?_)
  rw [hvar, h0, zero_add, map_add, hzero _ liftsFirstOrder_e,
    hzero _ liftsFirstOrder_f, add_zero]

/-- **The same refutation with the torsor identification made an explicit hypothesis.**

The one step this file does not formalize is that the parametrization of first-order lifts by
their structure matrix *is* the `Ext¹`-torsor action, i.e. that the difference class of the
lifts with matrices `E` and `E'` is `E - E'`. Here that step enters as the hypothesis `param`:
an additive identification of the group `G` acting on the lifts — `Ext¹_P(M, M ⊗ K_1)` in the
intended reading — with `M₂(ZMod 2)`. Under it, no additive `∂` on `G` can satisfy the variation
law, so clauses (a) and (b) of the dévissage's requirement are contradictory for the actual
`Ext¹` and not only for the matrix parametrization.

`Deformation.ObstructionVariation.not_exists_additive_obstructionVariation` is the case
`G = M₂(ZMod 2)`, `param = AddEquiv.refl`. -/
theorem not_exists_additive_obstructionVariation_of_param {G : Type v} {H : Type u}
    [AddCommGroup G] [AddCommGroup H] (param : G ≃+ Matrix (Fin 2) (Fin 2) (ZMod 2))
    (ω : G → H) (hω : ∀ e, ω e = 0 ↔ LiftsFirstOrder (param e))
    (variation : G →+ H) (hvar : ∀ e, ω e = ω 0 + variation e) : False := by
  refine not_exists_additive_obstructionVariation (fun e => ω (param.symm e)) (fun e => ?_)
    (variation.comp param.symm.toAddMonoidHom) (fun e => ?_)
  · rw [hω, param.apply_symm_apply]
  · rw [hvar (param.symm e), show (0 : G) = param.symm 0 from (map_zero param.symm).symm]
    rfl

end Deformation.ObstructionVariation

end
