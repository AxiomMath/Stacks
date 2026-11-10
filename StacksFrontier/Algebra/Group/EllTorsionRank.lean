module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# The `ℓ`-torsion of a short exact sequence of abelian groups

Fix a natural number `ℓ`. The `ℓ`-torsion `A[ℓ]` of an abelian group `A` is
`AddSubgroup.torsionBy A (ℓ : ℤ)`, and it carries a `ZMod ℓ`-module structure, Mathlib's
`AddSubgroup.torsionBy.zmodModule`; for `ℓ` prime this makes it a vector space over the field
`ZMod ℓ` and `Module.rank (ZMod ℓ) A[ℓ]` is the quantity written `dim_{F_ℓ} A[ℓ]`.

This file records how that dimension behaves along a short exact sequence

`0 ⟶ A ⟶ P ⟶ Q ⟶ 0`

of abelian groups whose left-hand term is `ℓ`-divisible: the sequence of `ℓ`-torsion subgroups
`0 ⟶ A[ℓ] ⟶ P[ℓ] ⟶ Q[ℓ] ⟶ 0` is again short exact, so the dimension is additive,
`dim P[ℓ] = dim A[ℓ] + dim Q[ℓ]`.

Divisibility of `A` is what makes the right-hand map surjective, and it enters as the
hypothesis `∀ a : A, ∃ b : A, (ℓ : ℤ) • b = a` rather than through `DivisibleBy`, matching
`Stacks.Thickenings.surjOn_zsmul_of_exact`. Injectivity of `A ⟶ P` is what makes the sequence
exact in the middle: without it a torsion class of `P` in the image of `A` need not come from a
torsion class of `A`.

Everything is phrased with `Module.rank`, a cardinal, so that no finiteness hypothesis is
needed anywhere; `Module.finrank_eq_rank` converts to `Module.finrank` wherever the torsion is
known to be finite-dimensional.

Because the Picard group of a scheme over `k` lives one universe above `k`, the additivity
statement is given in a form that does not add two cardinals from different universes: the
contribution of `A` appears as the dimension of the *image* of `A[ℓ]` in `P[ℓ]`, a subspace of
`P[ℓ]` and so in the universe of `P`. The two cases the induction of [Stacks, Tag 0C20]
needs — a trivial `A[ℓ]`, and an `A[ℓ]` with exactly `ℓ` elements — are then read off from that.

## Main definitions

* `Stacks.EllTorsion.toZModLinearMap` — an additive map between `ZMod ℓ`-modules, as a
  `ZMod ℓ`-linear map.
* `Stacks.EllTorsion.restrict` — the restriction of an additive map to `ℓ`-torsion.

## Main results

* `Stacks.EllTorsion.injective_restrict`, `Stacks.EllTorsion.exact_restrict`,
  `Stacks.EllTorsion.surjective_restrict` — the `ℓ`-torsion of a short exact sequence with
  `ℓ`-divisible left-hand term is short exact.
* `Stacks.EllTorsion.rank_torsionBy_eq_rank_range_add` — `dim P[ℓ]` is the dimension of the
  image of `A[ℓ]` plus `dim Q[ℓ]`.
* `Stacks.EllTorsion.rank_torsionBy_eq_of_subsingleton` — if `A[ℓ] = 0` then
  `dim P[ℓ] = dim Q[ℓ]`.
* `Stacks.EllTorsion.rank_torsionBy_eq_of_eq_zero` — if `A ⟶ P` is zero then
  `dim P[ℓ] = dim Q[ℓ]`.
* `Stacks.EllTorsion.rank_torsionBy_eq_one_add_of_card` — if `A[ℓ]` has `ℓ` elements then
  `dim P[ℓ] = 1 + dim Q[ℓ]`.

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
-/

@[expose] public section

universe v u

namespace Stacks.EllTorsion

variable {ℓ : ℕ}

/-! ### Additive maps between `ZMod ℓ`-modules -/

section Linear

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (ZMod ℓ) M] [Module (ZMod ℓ) N] [NeZero ℓ]

/-- **An additive map between `ZMod ℓ`-modules commutes with the `ZMod ℓ`-action.** Every
scalar is the image of a natural number, and an additive map commutes with the `ℕ`-action. -/
theorem map_zmod_smul (f : M →+ N) (c : ZMod ℓ) (x : M) : f (c • x) = c • f x := by
  rw [show c = ((c.val : ℕ) : ZMod ℓ) from (ZMod.natCast_rightInverse c).symm,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

/-- An additive map between `ZMod ℓ`-modules, as a `ZMod ℓ`-linear map. -/
def toZModLinearMap (f : M →+ N) : M →ₗ[ZMod ℓ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zmod_smul f

/-- The underlying function of `toZModLinearMap f` is `f`. -/
@[simp]
theorem coe_toZModLinearMap (f : M →+ N) : (toZModLinearMap (ℓ := ℓ) f : M → N) = f := rfl

end Linear

/-! ### The `ℓ`-torsion of a short exact sequence -/

section Restrict

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- **The restriction of an additive map to `ℓ`-torsion.** A map of abelian groups carries
`M[ℓ]` into `N[ℓ]` because it commutes with multiplication by `ℓ`. -/
def restrict (ℓ : ℕ) (f : M →+ N) :
    AddSubgroup.torsionBy M (ℓ : ℤ) →+ AddSubgroup.torsionBy N (ℓ : ℤ) where
  toFun x := ⟨f (x : M), by
    change (ℓ : ℤ) • f (x : M) = 0
    rw [← map_zsmul, show (ℓ : ℤ) • (x : M) = 0 from x.2, map_zero]⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The restriction `restrict ℓ f` sends an `ℓ`-torsion element `x` to `f x`. -/
@[simp]
theorem restrict_coe (f : M →+ N) (x : AddSubgroup.torsionBy M (ℓ : ℤ)) :
    ((restrict ℓ f x : AddSubgroup.torsionBy N (ℓ : ℤ)) : N) = f (x : M) := rfl

/-- An injective map of abelian groups is injective on `ℓ`-torsion. -/
theorem injective_restrict (f : M →+ N) (hf : Function.Injective f) :
    Function.Injective (restrict ℓ f) := fun _ _ hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))

end Restrict

variable {A : Type v} {P Q : Type u} [AddCommGroup A] [AddCommGroup P] [AddCommGroup Q]

/-- **The `ℓ`-torsion of an exact sequence is exact in the middle**, provided the left-hand map
is injective: a torsion class of `P` killed by `ψ` is `φ a` for some `a`, and that `a` is itself
torsion because `φ (ℓ • a) = ℓ • φ a = 0`. -/
theorem exact_restrict {φ : A →+ P} {ψ : P →+ Q} (hφ : Function.Injective φ)
    (hex : Function.Exact φ ψ) :
    Function.Exact (restrict ℓ φ) (restrict ℓ ψ) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (hex (x : P)).1 (congrArg Subtype.val hx)
    have hat : (ℓ : ℤ) • a = 0 := by
      refine hφ ?_
      rw [map_zsmul, ha, map_zero]
      exact x.2
    exact ⟨⟨a, hat⟩, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact Subtype.ext ((hex (φ (a : A))).2 ⟨(a : A), rfl⟩)

/-- A torsion class of `Q` lifts to `p : P` with `ℓ • p` in the image of `φ`. -/
private theorem exists_lift_zsmul_mem_range {φ : A →+ P} {ψ : P →+ Q} (hex : Function.Exact φ ψ)
    (hψ : Function.Surjective ψ) (c : AddSubgroup.torsionBy Q (ℓ : ℤ)) :
    ∃ p : P, ψ p = c ∧ ∃ a : A, φ a = (ℓ : ℤ) • p := by
  obtain ⟨p, hp⟩ := hψ (c : Q)
  refine ⟨p, hp, (hex _).1 ?_⟩
  rw [map_zsmul, hp]
  exact c.2

/-- **The `ℓ`-torsion of a surjection with `ℓ`-divisible kernel is surjective.** Lift a torsion
class `c` of `Q` to `p : P`; then `ℓ • p` lies in the kernel, so it is `φ a` with `a = ℓ • b` by
divisibility, and `p - φ b` is a torsion class of `P` lifting `c`. -/
theorem surjective_restrict {φ : A →+ P} {ψ : P →+ Q} (hex : Function.Exact φ ψ)
    (hψ : Function.Surjective ψ) (hdiv : ∀ a : A, ∃ b : A, (ℓ : ℤ) • b = a) :
    Function.Surjective (restrict ℓ ψ) := by
  intro c
  obtain ⟨p, hp, a, ha⟩ := exists_lift_zsmul_mem_range hex hψ c
  obtain ⟨b, hb⟩ := hdiv a
  refine ⟨⟨p - φ b, ?_⟩, Subtype.ext ?_⟩
  · change (ℓ : ℤ) • (p - φ b) = 0
    rw [smul_sub, ← map_zsmul, hb, ha, sub_self]
  · change ψ (p - φ b) = (c : Q)
    rw [map_sub, hp, (hex (φ b)).2 ⟨b, rfl⟩, sub_zero]

/-! ### The dimension of the `ℓ`-torsion along a short exact sequence -/

section Rank

variable (ℓ) [Fact ℓ.Prime] {φ : A →+ P} {ψ : P →+ Q}

/-- **The dimension of `P[ℓ]` is the dimension of the image of `A[ℓ]` plus the dimension of
`Q[ℓ]`**, for a short exact sequence `0 ⟶ A ⟶ P ⟶ Q ⟶ 0` of abelian groups whose left-hand
term is `ℓ`-divisible.

This is the computation that drives the induction of [Stacks, Tag 0C20]: each step of the
factorization of [Stacks, Tag 0C1L] contributes a short exact sequence
`0 ⟶ k^* ⟶ Pic(X_i) ⟶ Pic(X_{i+1}) ⟶ 0` or `0 ⟶ (k,+) ⟶ Pic(X_i) ⟶ Pic(X_{i+1}) ⟶ 0`
whose left-hand term is `ℓ`-divisible, so the dimension of the `ℓ`-torsion of `Pic(X_i)`
exceeds that of `Pic(X_{i+1})` by the dimension of the `ℓ`-torsion of `k^*` resp. `(k,+)`.

The contribution of `A` is written as the dimension of the image of `A[ℓ]` rather than as the
dimension of `A[ℓ]` itself so that both summands are cardinals in the universe of `P`; `A` is
allowed to live in another universe because `k` lies one universe below the Picard group of a
scheme over `k`. -/
theorem rank_torsionBy_eq_rank_range_add (hφ : Function.Injective φ) (hex : Function.Exact φ ψ)
    (hψ : Function.Surjective ψ) (hdiv : ∀ a : A, ∃ b : A, (ℓ : ℤ) • b = a) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) =
      Module.rank (ZMod ℓ) (toZModLinearMap (ℓ := ℓ) (restrict ℓ φ)).range +
        Module.rank (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  set F := toZModLinearMap (ℓ := ℓ) (restrict ℓ φ) with hF
  set G := toZModLinearMap (ℓ := ℓ) (restrict ℓ ψ) with hG
  have hran : Module.rank (ZMod ℓ) (G.range : Submodule (ZMod ℓ) _) =
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := by
    rw [LinearMap.range_eq_top.mpr (show Function.Surjective G from
      by simpa only [hG, coe_toZModLinearMap] using surjective_restrict hex hψ hdiv)]
    exact (Submodule.topEquiv (R := ZMod ℓ) (M := AddSubgroup.torsionBy Q (ℓ : ℤ))).rank_eq
  have hker : (G.ker : Submodule (ZMod ℓ) _) = F.range :=
    (show Function.Exact F G from
      by simpa only [hF, hG, coe_toZModLinearMap] using exact_restrict hφ hex).linearMap_ker_eq
  rw [← LinearMap.rank_range_add_rank_ker G, hran, hker, add_comm]

/-- **A short exact sequence with `ℓ`-divisible left-hand term whose `ℓ`-torsion is trivial does
not change the dimension of the `ℓ`-torsion.** This is case (3) of the induction of
[Stacks, Tag 0C20], the squishing of a tangent vector, where the left-hand term is `(k,+)` and
`ℓ` is invertible in `k`. -/
theorem rank_torsionBy_eq_of_subsingleton [Subsingleton (AddSubgroup.torsionBy A (ℓ : ℤ))]
    (hφ : Function.Injective φ) (hex : Function.Exact φ ψ) (hψ : Function.Surjective ψ)
    (hdiv : ∀ a : A, ∃ b : A, (ℓ : ℤ) • b = a) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) =
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hbot : (toZModLinearMap (ℓ := ℓ) (restrict ℓ φ)).range = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro x ⟨a, rfl⟩
    rw [Submodule.mem_bot, show a = 0 from Subsingleton.elim _ _, map_zero]
  rw [rank_torsionBy_eq_rank_range_add ℓ hφ hex hψ hdiv, hbot]
  simp

/-- **An exact sequence whose left-hand map is zero does not change the dimension of the
`ℓ`-torsion.** The right-hand map is then injective, and it is surjective on `ℓ`-torsion with no
divisibility hypothesis: a lift of a torsion class of `Q` is already a torsion class of `P`,
because `ℓ` times it lies in the image of `A`, which is zero.

This is case (1) of the induction of [Stacks, Tag 0C20], the glueing of two points on different
connected components, where the glueing homomorphism `k^* ⟶ Pic(X)` vanishes. -/
theorem rank_torsionBy_eq_of_eq_zero (hφ : ∀ a : A, φ a = 0) (hex : Function.Exact φ ψ)
    (hψ : Function.Surjective ψ) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) =
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hinj : Function.Injective (restrict ℓ ψ) := by
    intro x y hxy
    refine Subtype.ext ?_
    have hzero : ψ ((x : P) - (y : P)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val hxy
    obtain ⟨a, ha⟩ := (hex _).1 hzero
    rw [hφ a] at ha
    exact sub_eq_zero.mp ha.symm
  have hsurj : Function.Surjective (restrict ℓ ψ) := by
    intro c
    obtain ⟨p, hp, a, ha⟩ := exists_lift_zsmul_mem_range hex hψ c
    exact ⟨⟨p, ha.symm.trans (hφ a)⟩, Subtype.ext hp⟩
  exact (LinearEquiv.ofBijective (toZModLinearMap (ℓ := ℓ) (restrict ℓ ψ))
    ⟨hinj, hsurj⟩).rank_eq

/-- **A short exact sequence with `ℓ`-divisible left-hand term whose `ℓ`-torsion has exactly `ℓ`
elements raises the dimension of the `ℓ`-torsion by one.** This is case (2) of the induction of
[Stacks, Tag 0C20], the glueing of two points on the same connected component, where the
left-hand term is `k^*` and its `ℓ`-torsion is the group of `ℓ`-th roots of unity. -/
theorem rank_torsionBy_eq_one_add_of_card
    (hcard : Nat.card (AddSubgroup.torsionBy A (ℓ : ℤ)) = ℓ)
    (hφ : Function.Injective φ) (hex : Function.Exact φ ψ) (hψ : Function.Surjective ψ)
    (hdiv : ∀ a : A, ∃ b : A, (ℓ : ℤ) • b = a) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) =
      1 + Module.rank (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy A (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy P (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy Q (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  have hp := (Fact.out : ℓ.Prime)
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  set F := toZModLinearMap (ℓ := ℓ) (restrict ℓ φ) with hF
  have hFinj : Function.Injective F := by
    simpa only [hF, coe_toZModLinearMap] using injective_restrict φ hφ
  have hrange : Nat.card (F.range : Submodule (ZMod ℓ) _) = ℓ :=
    (Nat.card_congr (LinearEquiv.ofInjective F hFinj).toEquiv).symm.trans hcard
  have hfinite : Finite (F.range : Submodule (ZMod ℓ) _) :=
    Nat.finite_of_card_ne_zero (hrange.symm ▸ hp.ne_zero)
  let : Fintype (F.range : Submodule (ZMod ℓ) _) := Fintype.ofFinite _
  have hpow := Module.card_eq_pow_finrank (K := ZMod ℓ)
    (V := (F.range : Submodule (ZMod ℓ) _))
  rw [← Nat.card_eq_fintype_card, hrange, ZMod.card] at hpow
  have hfr : Module.finrank (ZMod ℓ) (F.range : Submodule (ZMod ℓ) _) = 1 := by
    refine Nat.pow_right_injective hp.two_le ?_
    change ℓ ^ Module.finrank (ZMod ℓ) (F.range : Submodule (ZMod ℓ) _) = ℓ ^ 1
    rw [pow_one]
    exact hpow.symm
  have : Module.Finite (ZMod ℓ) (F.range : Submodule (ZMod ℓ) _) := Module.Finite.of_finite
  rw [rank_torsionBy_eq_rank_range_add ℓ hφ hex hψ hdiv, ← hF, ← Module.finrank_eq_rank, hfr,
    Nat.cast_one]

end Rank

end Stacks.EllTorsion
