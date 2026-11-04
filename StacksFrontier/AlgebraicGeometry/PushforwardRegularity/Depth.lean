module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.Basic
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# Depth of the stalk of a flat pushforward

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `F` be a
quasi-coherent `𝒪_X`-module flat over `S`. If the stalk `(f_* F)_s` is finite over `𝒪_{S,s}`,
then

`min(2, depth 𝒪_{S,s}) ≤ depth (f_* F)_s`.

This is [Stacks, Tag 0EY0] part (6), and it is pure bookkeeping on top of parts (4) and (5),
which are `AlgebraicGeometry.isSMulRegular_stalk_pushforward` and
`AlgebraicGeometry.isWeaklyRegular_stalk_pushforward`: a regular sequence in `𝔪_s` of length one
or two on `𝒪_{S,s}` is carried to a weakly regular sequence of the same length on `(f_* F)_s`,
and the depth of a finite module is the supremum of the lengths of the weakly regular sequences
in the ideal, [Stacks, Tag 0AUI]. The three cases `depth 𝒪_{S,s} ≥ 2`, `= 1` and `= 0` are
treated separately because only the first two produce a sequence to transport.

## Main results

* `AlgebraicGeometry.min_depth_le_depth_stalk_pushforward`: [Stacks, Tag 0EY0] part (6).

Part (4) of the same tag, a nonzerodivisor on `𝒪_{S,s}` remaining a nonzerodivisor on
`(f_* F)_s`, is already proved as
`Stacks.AlgebraicGeometry.PushforwardRegularity.isSMulRegular_stalk_pushforward`; it is the
first ingredient of the bound below, and the tag is attached to it here rather than restated.

## Implementation notes

The pushforward is Mathlib's `Scheme.Modules.pushforward` and the module structure on the
abelian-group stalk is `AlgebraicGeometry.Scheme.Modules.moduleStalk`.

The source states part (6) for a finite stalk over a Noetherian local ring. Noetherianity is not
assumed here: it enters the source only through the depth formula for finite modules, which
[Stacks, Tag 0AUI] gives over any commutative ring. Finiteness of the stalk is kept, as it is
what that formula needs. Dropping a hypothesis the conclusion does not need is a strengthening.

The extraction of a regular sequence of a prescribed length from a lower bound on the depth is
`exists_isRegular_length_ge`, which unfolds `Module.depth`; the matching upper bound
`le_depth_of_isWeaklyRegular` is the easy half of [Stacks, Tag 0AUI]. The latter already exists
in `StacksFrontier.RingTheory.Depth.Criteria`, but is `private` there, so it is re-derived in one
line from the public `Module.depth_eq_iSup_isWeaklyRegular_length`.

## References

* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0AUI](https://stacks.math.columbia.edu/tag/0AUI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Pointwise

universe u

namespace Stacks.AlgebraicGeometry.PushforwardRegularity

add_to_stacks 0EY0 "pushforward_nonzerodivisor"
  Stacks.AlgebraicGeometry.PushforwardRegularity.isSMulRegular_stalk_pushforward

/-- A lower bound on the `I`-depth of `M` produces an `M`-regular sequence in `I` at least that
long, as soon as `I • M ≠ M` so that the depth is the supremum of their lengths. -/
private theorem exists_isRegular_length_ge {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (hI : I • (⊤ : Submodule R M) ≠ ⊤)
    (n : ℕ) (hn0 : 0 < n) (hn : (n : ℕ∞) ≤ Module.depth R I M) :
    ∃ rs : List R, n ≤ rs.length ∧ (∀ r ∈ rs, r ∈ I) ∧
      RingTheory.Sequence.IsRegular M rs := by
  rw [Module.depth, ite_eq_right hI] at hn
  obtain ⟨rs, hrs⟩ := lt_iSup_iff.mp
    (lt_of_lt_of_le
      (show ((n - 1 : ℕ) : ℕ∞) < (n : ℕ∞) by rw [Nat.cast_lt]; omega) hn)
  obtain ⟨⟨hmem, hreg⟩, hlen⟩ := lt_iSup_iff.mp hrs
  rw [Nat.cast_lt] at hlen
  exact ⟨rs, by omega, hmem, hreg⟩

/-- A weakly `M`-regular sequence inside `I` is at most as long as the `I`-depth of a finite
module `M`: the easy half of [Stacks, Tag 0AUI]. -/
private theorem le_depth_of_isWeaklyRegular {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (I : Ideal R) (rs : List R)
    (hmem : ∀ x ∈ rs, x ∈ I) (hreg : RingTheory.Sequence.IsWeaklyRegular M rs) :
    (rs.length : ℕ∞) ≤ Module.depth R I M :=
  Module.depth_eq_iSup_isWeaklyRegular_length R I M ▸
    le_biSup (fun rs : List R => (rs.length : ℕ∞)) ⟨hmem, hreg⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- **[Stacks, Tag 0EY0] part (6).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module flat over `S`. If the stalk
`(f_* F)_s` is finite over `𝒪_{S,s}`, then

`min(2, depth 𝒪_{S,s}) ≤ depth (f_* F)_s`.

The source assumes `𝒪_{S,s}` Noetherian; that hypothesis is used there only through the
description of the depth of a finite module as the supremum of the lengths of the weakly regular
sequences in the maximal ideal, which holds over any commutative ring, so it is omitted. -/
@[stacks 0EY0 "flat_pushforward_depth"]
public theorem min_depth_le_depth_stalk_pushforward [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : S)
    (hfinite : Module.Finite (S.presheaf.stalk s) (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s)) :
    min (2 : ℕ∞) (Module.depth (S.presheaf.stalk s)
        (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) ≤
      Module.depth (S.presheaf.stalk s) (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward f).obj F).val.presheaf s) := by
  classical
  set R := S.presheaf.stalk s with hR
  set I := IsLocalRing.maximalIdeal R with hI'
  set M := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pushforward f).obj F).val.presheaf s with hM
  have : Module.Finite R M := hfinite
  set d := Module.depth R I R with hd
  have hI : I • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  -- A depth bound of `n` on the base gives a weakly regular sequence of length `n` in `I`.
  have key : ∀ n : ℕ, 0 < n → (n : ℕ∞) ≤ d → ∃ rs : List R, rs.length = n ∧
      (∀ x ∈ rs, x ∈ I) ∧ RingTheory.Sequence.IsWeaklyRegular R rs := by
    intro n hn hnd
    obtain ⟨rs, hlen, hmem, hreg⟩ := exists_isRegular_length_ge I R hI n hn hnd
    refine ⟨rs.take n, by simp [hlen], fun x hx => hmem x (List.mem_of_mem_take hx), ?_⟩
    have := hreg.toIsWeaklyRegular
    rw [← rs.take_append_drop n, RingTheory.Sequence.isWeaklyRegular_append_iff] at this
    exact this.1
  by_cases hd2 : (2 : ℕ∞) ≤ d
  -- Depth at least two on the base: transport a regular pair by part (5).
  · obtain ⟨rs, hlen, hmem, hreg⟩ := key 2 (by norm_num) hd2
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    rw [min_eq_left hd2]
    exact le_depth_of_isWeaklyRegular I [a, b] hmem
      (isWeaklyRegular_stalk_pushforward f F s hflat a b hreg)
  · by_cases hd1 : (1 : ℕ∞) ≤ d
    -- Depth exactly one on the base: transport a single nonzerodivisor by part (4).
    · obtain ⟨rs, hlen, hmem, hreg⟩ := key 1 (by norm_num) hd1
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
      calc min (2 : ℕ∞) d ≤ d := min_le_right _ _
        _ ≤ 1 := ENat.lt_natCast_add_one_iff.mp (lt_of_not_ge hd2)
        _ ≤ Module.depth R I M := le_depth_of_isWeaklyRegular I [a] hmem
              ((RingTheory.Sequence.isWeaklyRegular_singleton_iff M a).mpr
                (isSMulRegular_stalk_pushforward f F hflat s a
                  ((RingTheory.Sequence.isWeaklyRegular_singleton_iff R a).mp hreg)))
    -- Depth zero on the base: the bound is vacuous.
    · calc min (2 : ℕ∞) d ≤ d := min_le_right _ _
        _ ≤ 0 := ENat.lt_natCast_add_one_iff.mp (lt_of_not_ge hd1)
        _ ≤ Module.depth R I M := bot_le

end Stacks.AlgebraicGeometry.PushforwardRegularity

end
