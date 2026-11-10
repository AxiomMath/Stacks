module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicQuotientMap

/-!
# The kernel of `Q₁ ↠ P'/(Y)` is `(z)`

Eleventh layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`. Layer ten
built the surjection `qOneToQuotOmega : Q₁ ↠ P'/(Y)` killing the Artin–Schreier root; this layer
computes its kernel, which is the injectivity half of `hquot`'s second step:

**`ker (Q₁ → P'/(Y)) = (z)`.**

The argument is the one the shape of `Q₁` suggests. `Q₁ = P'[z]/(z² + z − Y)` with `z² + z − Y`
monic of degree two, so every element is `a + b·z` with `a, b ∈ P'`
(`exists_add_mul_zRoot`, by division with remainder against a monic polynomial). The map sends
`a + b·z` to `a mod Y`, so the kernel is `(Y)·1 + P'·z`; and `Y = z·(z + 1)` — the relation of
`Q₁` again — puts `(Y)` inside `(z)`. Both inclusions are then immediate.

## What remained for `hquot`, and where it is

Only the localization step `Q'/(z) ≅ Q₁/(z)`, which holds because `z + 1 ↦ 1` modulo `z`, so
inverting it does nothing. That is layer twelve,
`StacksFrontier.Deformation.Examples.Linear.NodalCubicQuotientHquot`: `qOneToQuotOmega (z + 1) = 1`
is a unit, so `IsLocalization.lift` extends the map of layer ten to `Q' ↠ P'/(Y)`, and the kernel
computation here plus surjectivity give bijectivity of `P'/(Y) → Q'/(Y·Q')` after
`map_span_omegaP` of layer nine rewrites `Y·Q'` as `z·Q'`. Layer twelve does not form `Q'/(z)` as
a ring: extending the map past the localization and computing its kernel is enough, and is less.

## Main results

* `Deformation.Examples.ArtinSchreier.qPoly_degree`: `z² + z − Y` has degree two (its natural
  degree is then `Polynomial.natDegree_eq_of_degree_eq_some qPoly_degree`), which is what makes
  division with remainder leave `a + b·z`.
* `Deformation.Examples.ArtinSchreier.exists_add_mul_zRoot`: **every element of `Q₁` is
  `a + b·z`** with `a, b ∈ P'`.
* `Deformation.Examples.ArtinSchreier.ker_qOneToQuotOmega`: **the kernel is `(z)`**.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-- The tail of `z² + z − Y` has degree at most one. -/
theorem qPoly_tail_degree_le :
    (X - C omegaP : Polynomial PBase).degree ≤ 1 :=
  le_trans (Polynomial.degree_sub_le _ _)
    (max_le Polynomial.degree_X_le (le_trans Polynomial.degree_C_le (by norm_num)))

/-- `z² + z − Y` has degree two. -/
theorem qPoly_degree : qPoly.degree = 2 := by
  have hlt : (X - C omegaP : Polynomial PBase).degree <
      (X ^ 2 : Polynomial PBase).degree := by
    rw [Polynomial.degree_X_pow]
    exact lt_of_le_of_lt qPoly_tail_degree_le (by norm_num)
  have h : qPoly.degree = (X ^ 2 : Polynomial PBase).degree :=
    Polynomial.degree_add_eq_left_of_degree_lt hlt
  rw [h, Polynomial.degree_X_pow]
  simp

/-- **Every element of `Q₁` is `a + b·z`** with `a, b ∈ P'`: divide with remainder against the
monic `z² + z − Y`, whose degree is two, so the remainder is linear. -/
theorem exists_add_mul_zRoot (u : QOne) :
    ∃ a b : PBase,
      u = algebraMap PBase QOne a + algebraMap PBase QOne b * zRoot := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hmk : AdjoinRoot.mk qPoly f = AdjoinRoot.mk qPoly (f %ₘ qPoly) := by
    refine (AdjoinRoot.mk_eq_mk.2 ?_).symm
    refine ⟨-(f /ₘ qPoly), ?_⟩
    have h := Polynomial.modByMonic_add_div f qPoly
    linear_combination h
  have hdeg : (f %ₘ qPoly).degree ≤ 1 := by
    have h := Polynomial.degree_modByMonic_lt f qPoly_monic
    rw [qPoly_degree] at h
    rcases eq_or_ne (f %ₘ qPoly) 0 with h0 | h0
    · rw [h0]
      simp
    · have hnd := Polynomial.degree_eq_natDegree h0
      rw [hnd] at h
      have hn : (f %ₘ qPoly).natDegree < 2 := by exact_mod_cast h
      rw [hnd]
      exact_mod_cast Nat.lt_succ_iff.mp hn
  obtain ⟨a, b, hr⟩ : ∃ a b : PBase, f %ₘ qPoly = C b * X + C a :=
    ⟨(f %ₘ qPoly).coeff 0, (f %ₘ qPoly).coeff 1,
      Polynomial.eq_X_add_C_of_degree_le_one hdeg⟩
  refine ⟨a, b, ?_⟩
  change AdjoinRoot.mk qPoly f = _
  rw [hmk, hr, map_add, map_mul]
  rw [add_comm]
  rfl

/-- **The kernel of `Q₁ ↠ P'/(Y)` is `(z)`.** Writing an element as `a + b·z`, its image is
`a mod Y`; so the kernel is `(Y)·1 + P'·z`, and `Y = z·(z + 1)` puts `(Y)` inside `(z)`. -/
theorem ker_qOneToQuotOmega :
    RingHom.ker qOneToQuotOmega = Ideal.span {zRoot} := by
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨a, b, rfl⟩ := exists_add_mul_zRoot u
    rw [RingHom.mem_ker, map_add, map_mul, qOneToQuotOmega_root, mul_zero, add_zero,
      qOneToQuotOmega_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    refine Ideal.mem_span_singleton.2 ⟨(zRoot + 1) * algebraMap PBase QOne c +
      algebraMap PBase QOne b, ?_⟩
    rw [map_mul, qRelationMul]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact qOneToQuotOmega_root

end Deformation.Examples.ArtinSchreier

end
