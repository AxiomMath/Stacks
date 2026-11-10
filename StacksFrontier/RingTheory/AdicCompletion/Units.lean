module

public import StacksCore.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Units and the Jacobson radical of an adic completion

Let `R` be a ring, let `I ⊆ R` be an ideal and let `R^∧ = lim R/Iⁿ` be the `I`-adic completion of
`R`. This file proves that units of `R^∧` are detected on the first quotient `R/I`, and the three
consequences of that fact recorded in Stacks 05GI.

The mechanism is that a unit lifts along a nilpotent thickening: if `ab ≡ 1` modulo an ideal `J`
and `Jⁿ ⊆ K`, then `ab - 1` is nilpotent modulo `K`, so `ab`, and hence `a`, is a unit modulo `K`.
Applied to a representative `a` of the `(n+1)`-st component of `x ∈ R^∧`, whose image in `R/I` is
the image of `x`, this makes every component of `x` a unit. The inverses of the components are
again compatible with the transition maps `R/Iⁿ → R/Iᵐ`, a homomorphism carrying the inverse of a
unit to the inverse of its image, so they assemble to an element of `lim R/Iⁿ = R^∧` inverse
to `x`.

Given that, the ideal `IR^∧` lies in the kernel of `R^∧ → R/I`, so an element of `1 + IR^∧` has
image `1` in `R/I` and is a unit; an ideal all of whose `1 + ·` translates consist of units is
contained in the Jacobson radical (Stacks 0AME, `Ideal.le_ringJacobson_iff_isUnit_one_add`), which
gives the last two containments; and an element of `1 + I` maps into `1 + IR^∧`.

## Main results

* `Stacks.AdicCompletion.UnitsJacobson.solution` : Stacks 05GI, as stated in
  `AdicCompletion.isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot`.

## Implementation notes

The only mathematical content is part (1), proved here as
`Stacks.AdicCompletion.UnitsJacobson.isUnit_of_isUnit_evalOneₐ`; parts (2), (3) and (4) are
formal consequences of it together with the containment `IR^∧ ≤ Ker(R^∧ → R/I)`, exactly as in
the source.

Stacks 0AMG is used in the form `isUnit_quotient_mk_of_pow_le`: if `Jⁿ ≤ K`, then a unit modulo
`J` is a unit modulo `K`. This generalises `Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk`, both of
whose restrictions bite here: the ideal `K` that occurs is `Iⁿ • ⊤` rather than `Iⁿ`, and `n = 0`
cannot be excluded, the `0`-th component of `x` being one of those to be inverted.

The components of `x : R^∧` are indexed so that the `n`-th lives in `R ⧸ (Iⁿ • ⊤)` rather than
`R ⧸ Iⁿ`; the two ideals are equal but not definitionally so, which is why the bridge to
`AdicCompletion.evalOneₐ` is isolated as `evalOneₐ_eq_mk`. Working with the `(n+1)`-st component
rather than the `n`-th lets one representative serve both the first component (used to see the
unit) and the `n`-th (the one wanted), with no case distinction at `n = 0`.

## References

* [Stacks Project, Tag 05GI](https://stacks.math.columbia.edu/tag/05GI)
* [Stacks Project, Tag 0AMG](https://stacks.math.columbia.edu/tag/0AMG)
* [Stacks Project, Tag 0AME](https://stacks.math.columbia.edu/tag/0AME)
-/

namespace Stacks.AdicCompletion.UnitsJacobson

open _root_.AdicCompletion

/-- A monoid homomorphism carries the inverse of a unit to the inverse of its image. -/
private theorem map_ringInverse {A B F : Type*} [MonoidWithZero A] [MonoidWithZero B]
    [FunLike F A B] [MonoidHomClass F A B] (f : F) {a : A} (ha : IsUnit a) :
    f (Ring.inverse a) = Ring.inverse (f a) := by
  rw [eq_comm, ← mul_one (Ring.inverse (f a)), Ring.inverse_mul_eq_iff_eq_mul _ _ _ (ha.map f),
    ← map_mul, Ring.mul_inverse_cancel _ ha, map_one]

/-- **Stacks 0AMG**, in quotient form: if some power of `J` is contained in `K`, then an element
that is a unit modulo `J` is a unit modulo `K`. -/
private theorem isUnit_quotient_mk_of_pow_le {A : Type*} [CommRing A] {J K : Ideal A} {n : ℕ}
    (hJK : J ^ n ≤ K) {a : A} (ha : IsUnit (Ideal.Quotient.mk J a)) :
    IsUnit (Ideal.Quotient.mk K a) := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ha
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hmem : a * b - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hb, sub_self]
  have hnil : IsNilpotent (Ideal.Quotient.mk K (a * b - 1)) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hJK (Ideal.pow_mem_pow hmem n)⟩
  refine isUnit_of_mul_isUnit_left (y := Ideal.Quotient.mk K b) ?_
  simpa using hnil.isUnit_add_one

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- A representative of the `n`-th component of `x : R^∧` represents every earlier component. -/
private theorem val_eq_mk_of_le {x : AdicCompletion I R} {a : R} {m n : ℕ} (hmn : m ≤ n)
    (ha : x.val n = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a) :
    x.val m = Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) a := by
  rw [← x.property hmn, ha]
  exact transitionMap_ideal_mk I hmn a

/-- The image of `x : R^∧` in `R ⧸ I` is computed by any representative of its first component. -/
private theorem evalOneₐ_eq_mk {x : AdicCompletion I R} {a : R}
    (ha : x.val 1 = Ideal.Quotient.mk (I ^ 1 • ⊤ : Ideal R) a) :
    evalOneₐ I x = Ideal.Quotient.mk I a := by
  rw [← factorₐ_evalₐ_one, ← factor_eval_eq_evalₐ I x (by simp),
    show eval I R 1 x = Ideal.Quotient.mk (I ^ 1 • ⊤ : Ideal R) a from ha]
  rfl

/-- An element of `R^∧` all of whose components are units is a unit: the inverses of the
components are again compatible with the transition maps. -/
private theorem isUnit_of_forall_isUnit_val {x : AdicCompletion I R}
    (h : ∀ n, IsUnit (x.val n)) : IsUnit x := by
  refine IsUnit.of_mul_eq_one ⟨fun n ↦ Ring.inverse (x.val n), fun {m n} hmn ↦ ?_⟩ ?_
  · change transitionMapₐ I hmn (Ring.inverse (x.val n)) = Ring.inverse (x.val m)
    rw [map_ringInverse _ (h n), show transitionMapₐ I hmn (x.val n) = x.val m from x.property hmn]
  · exact AdicCompletion.ext fun n ↦ Ring.mul_inverse_cancel _ (h n)

/-- **Stacks 05GI (1)**, componentwise: if the image of `x : R^∧` in `R ⧸ I` is a unit, then so is
each component of `x`. -/
private theorem isUnit_val_of_isUnit_evalOneₐ {x : AdicCompletion I R}
    (hx : IsUnit (evalOneₐ I x)) (n : ℕ) : IsUnit (x.val n) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
  have h1 : IsUnit (Ideal.Quotient.mk I a) := by
    rwa [evalOneₐ_eq_mk I (val_eq_mk_of_le I (by omega) ha.symm)] at hx
  rw [val_eq_mk_of_le I n.le_succ ha.symm]
  exact isUnit_quotient_mk_of_pow_le (n := n) (by simp) h1

/-- **Stacks 05GI (1)**: an element of `R^∧` whose image in `R ⧸ I` is a unit is a unit. -/
private theorem isUnit_of_isUnit_evalOneₐ {x : AdicCompletion I R}
    (hx : IsUnit (evalOneₐ I x)) : IsUnit x :=
  isUnit_of_forall_isUnit_val I (isUnit_val_of_isUnit_evalOneₐ I hx)

/-- The ideal `IR^∧` is contained in the kernel of `R^∧ → R ⧸ I`. -/
private theorem map_le_ker_evalOneₐ :
    I.map (algebraMap R (AdicCompletion I R)) ≤ RingHom.ker (evalOneₐ I).toRingHom := by
  rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, evalOneₐ_comp_algebraMap_eq_mk, Ideal.mk_ker]

/-- **Stacks 05GI (4)**: the kernel of `R^∧ → R ⧸ I` is contained in the Jacobson radical
of `R^∧`. -/
private theorem ker_evalOneₐ_le_ringJacobson :
    RingHom.ker (evalOneₐ I).toRingHom ≤ Ring.jacobson (AdicCompletion I R) :=
  (Ideal.le_ringJacobson_iff_isUnit_one_add _).2 fun z hz ↦
    isUnit_of_isUnit_evalOneₐ I <| by
      have hz0 : evalOneₐ I z = 0 := RingHom.mem_ker.1 hz
      simp [hz0]

/-- **Stacks 05GI**, all four parts: units of `R^∧` are detected in `R ⧸ I`, the images of
`1 + I` and the elements of `1 + IR^∧` are units, and `IR^∧` and `Ker(R^∧ → R ⧸ I)` lie in the
Jacobson radical of `R^∧`. -/
public theorem solution {R : Type*} [CommRing R] (I : Ideal R) :
    (∀ x : AdicCompletion I R, IsUnit (evalOneₐ I x) → IsUnit x) ∧
      (∀ a ∈ I, IsUnit (algebraMap R (AdicCompletion I R) (1 + a))) ∧
      (∀ x ∈ I.map (algebraMap R (AdicCompletion I R)), IsUnit (1 + x)) ∧
      I.map (algebraMap R (AdicCompletion I R)) ≤ (⊥ : Ideal (AdicCompletion I R)).jacobson ∧
      RingHom.ker (evalOneₐ I).toRingHom ≤ (⊥ : Ideal (AdicCompletion I R)).jacobson := by
  have hjac : I.map (algebraMap R (AdicCompletion I R)) ≤ Ring.jacobson (AdicCompletion I R) :=
    (map_le_ker_evalOneₐ I).trans (ker_evalOneₐ_le_ringJacobson I)
  have h3 : ∀ z ∈ I.map (algebraMap R (AdicCompletion I R)), IsUnit (1 + z) :=
    (Ideal.le_ringJacobson_iff_isUnit_one_add _).1 hjac
  rw [Ideal.jacobson_bot]
  exact ⟨fun _ hx ↦ isUnit_of_isUnit_evalOneₐ I hx,
    fun a ha ↦ by simpa using h3 _ (Ideal.mem_map_of_mem _ ha), h3, hjac,
    ker_evalOneₐ_le_ringJacobson I⟩

end Stacks.AdicCompletion.UnitsJacobson

/-!
# Units and the Jacobson radical of an adic completion

Let `R` be a ring, let `I ⊆ R` be an ideal, and let `R^∧ = lim R/Iⁿ` be the `I`-adic completion
of `R`, a ring with a canonical map `R → R^∧` and canonical surjections `R^∧ → R/Iⁿ`. This file
records that units of `R^∧` may be detected on the very first quotient `R/I`.

The reason is that a unit lifts along a nilpotent thickening: if `x ∈ R^∧` has unit image
`x₁ ∈ R/I`, then its image `xₙ ∈ R/Iⁿ` is a unit for every `n`, because `I/Iⁿ` is a nilpotent
ideal of `R/Iⁿ` (Stacks 0AMG). The inverses `xₙ⁻¹` are compatible with the transition maps
`R/Iⁿ → R/Iᵐ`, being inverses of compatible elements, so they assemble to an element
`y = (xₙ⁻¹) ∈ lim R/Iⁿ = R^∧` with `xy = 1`.

Three consequences follow at once. An element of `1 + I` has unit image `1` in `R/I`, so its
image in `R^∧` is invertible; an element of `1 + IR^∧` has image `1` in `R/I` as well, hence is
invertible in `R^∧`; and since an ideal all of whose `1 + ·` translates consist of units lies in
the Jacobson radical (Stacks 0AME, `Ideal.mem_jacobson_bot`), both the ideal `IR^∧` generated by
the image of `I` and the whole kernel of `R^∧ → R/I` are contained in the Jacobson radical of
`R^∧`.

## Main results

* `AdicCompletion.isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot`: for every
  ring `R` and every ideal `I` of `R`, the four assertions of Stacks 05GI about the `I`-adic
  completion `AdicCompletion I R`: an element with unit image in `R ⧸ I` is a unit; the image of
  `1 + I` consists of units; `1 + IR^∧` consists of units; and `IR^∧` and `Ker(R^∧ → R ⧸ I)` are
  both contained in the Jacobson radical of `R^∧`.

## Implementation notes

The canonical map `R^∧ → R/I` of the source is Mathlib's `AdicCompletion.evalOneₐ I`, the algebra
map `AdicCompletion I R →ₐ[R] R ⧸ I` obtained from the first projection out of the limit; the
canonical map `R → R^∧` is `algebraMap R (AdicCompletion I R)`, which is `AdicCompletion.of I R`
on underlying sets. The source's ideal `IR^∧` is `I.map (algebraMap R (AdicCompletion I R))`,
Mathlib's spelling for the ideal generated by the image of `I`; by `Ideal.smul_top_eq_map` it is
the same submodule as `I • (⊤ : Submodule R (AdicCompletion I R))`, the shape used in Stacks 0318
and 05GG.

The coset `1 + I` has no name in Mathlib, so parts (2) and (3) are phrased by quantifying over the
ideal: `∀ a ∈ I, IsUnit (algebraMap R (AdicCompletion I R) (1 + a))` and
`∀ x ∈ IR^∧, IsUnit (1 + x)`. The Jacobson radical of a ring is `(⊥ : Ideal _).jacobson`, as in
`IsAdicComplete.le_jacobson_bot`.

Part (4) is genuinely two containments, not one: without a finiteness hypothesis on `I` all that is
available is `IR^∧ ≤ Ker(R^∧ → R/I)`, the two being equal when `I` is finitely generated
(`AdicCompletion.ker_evalOneₐ_eq_map`, which needs `I.FG`). Both are stated, as in the source. No
finiteness of `I`, Noetherian hypothesis on `R`, or completeness of `R` is assumed anywhere; in
particular this is not `IsAdicComplete.le_jacobson_bot`, which is the statement for a ring already
`I`-adically complete, whereas here the completeness that makes the argument work is that of
`R^∧`'s own construction as a limit.

Faithfulness. (1) No hypothesis is dead: beyond the data `R` and `I`, which occur in all four
conclusions, the lemma has none, and that generality is the point — the source assumes nothing
about `I` or `R`. (2) The scalars and base are the source's: `I` is an ideal of `R`, the completion
is taken for that `I`, `R/I` is `R ⧸ I`, and the Jacobson radical is computed in `R^∧` and not in
`R`. (3) Each canonical map the source names is pinned, not merely asserted to exist: the map to
`R/I` is `AdicCompletion.evalOneₐ I` and the map from `R` is
`algebraMap R (AdicCompletion I R)`, so that (1) is about the actual first projection, (2) about
the actual completion map, and (4) about the actual kernel. (4) The instantiation is not
degenerate: for `R = ℤ` and `I = (p)` the completion is the ring `ℤ_p` of `p`-adic integers and
`R/I = 𝔽_p`, where (1) says an element of `ℤ_p` with nonzero residue is invertible and (4) says
`pℤ_p = Ker(ℤ_p → 𝔽_p)` is the Jacobson radical, a nonzero proper ideal. (Both `I = ⊥`, where
`R^∧ = R` and (1) is a tautology, and `I = ⊤`, where `R^∧ = 0`, are excluded by that witness.)

## References

* [StackProject 05GI](https://stacks.math.columbia.edu/tag/05GI)
* [StackProject 0AMG](https://stacks.math.columbia.edu/tag/0AMG) for lifting units along a
  nilpotent ideal
* [StackProject 0AME](https://stacks.math.columbia.edu/tag/0AME) for the characterisation of the
  Jacobson radical used in part (4)

## Tags

adic completion, unit, Jacobson radical
-/

@[expose] public section

namespace AdicCompletion

/-- **Stacks 05GI.** Let `R` be a ring, let `I ⊆ R` be an ideal, and let `R^∧ = lim R/Iⁿ`.
Then (1) any element of `R^∧` which maps to a unit of `R/I` is a unit, (2) any element of `1 + I`
maps to an invertible element of `R^∧`, (3) any element of `1 + IR^∧` is invertible in `R^∧`, and
(4) the ideals `IR^∧` and `Ker(R^∧ → R/I)` are contained in the Jacobson radical of `R^∧`. -/
@[stacks 05GI "All four parts, for an arbitrary ideal of an arbitrary commutative ring."]
public theorem isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot
    {R : Type*} [CommRing R] (I : Ideal R) :
    (∀ x : AdicCompletion I R, IsUnit (evalOneₐ I x) → IsUnit x) ∧
      (∀ a ∈ I, IsUnit (algebraMap R (AdicCompletion I R) (1 + a))) ∧
      (∀ x ∈ I.map (algebraMap R (AdicCompletion I R)), IsUnit (1 + x)) ∧
      I.map (algebraMap R (AdicCompletion I R)) ≤ (⊥ : Ideal (AdicCompletion I R)).jacobson ∧
      RingHom.ker (evalOneₐ I).toRingHom ≤ (⊥ : Ideal (AdicCompletion I R)).jacobson :=
        by apply Stacks.AdicCompletion.UnitsJacobson.solution

end AdicCompletion

end
