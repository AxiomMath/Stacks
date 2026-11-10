module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.Deformation.Examples.Linear.ArtinSchreierLocalGlobal
public import StacksFrontier.Deformation.Examples.Linear.MaurerCartanWindowSolvable

/-!
# The Artin–Schreier class realized as a module-lifting obstruction

`StacksFrontier.Deformation.Examples.Linear.ArtinSchreierLocalGlobal` exhibits a quadratic equation
with the window's own `z ↦ z + 1` symmetry that fails local-to-global on a pair of exactly the
shape Stacks 0DZ2 supplies. What is needed is a *realization*: the same failure as the
obstruction to lifting an honest module. This file supplies the two pieces of that realization
that are mathematics rather than bookkeeping.

## The instance

Let `k = 𝔽₂`, `A = k`, `A' = k[t]/t³` — so `I = (t)` is nilpotent with `I³ = 0` and `I² ≠ 0`,
which is where the square-zero form of Stacks 0DZ2 stops applying. Let `S` be a
`k`-algebra, `w ∈ S`, and put

`P = S[x]/(x²)`,  `P' = S[t, x]/(t³, x² − t·x − t²·w)`,  `M = P/(x) = S`.

`P'` is free over `S[t]/t³` on `{1, x}`, hence flat over `A'`, and `P' ⊗_{A'} A = P`. The lifting
problem for `M` is then **exactly** the Artin–Schreier equation for `w`:

* `Deformation.Examples.ArtinSchreier.twisted_lift_iff`: an element `ξ = t·a + t²·b` of `S[t]/t³`
  satisfies the relation `ξ² = t·ξ + t²·w` of `P'` if and only if `a·a = a + w`.

That is the whole classification. An `A'`-flat `P'`-module lift `M'` of `M` is free of rank one
over `S[t]/t³` — lift the generator, use Nakayama for the nilpotent `t` and the fact that a
surjection of `A'`-flat modules which is an isomorphism modulo `I` is an isomorphism — so the
action of `x` on it is multiplication by some `ξ ∈ S[t]/t³` with `ξ ≡ 0` modulo `t`, i.e.
`ξ = t·a + t²·b`, subject to the relation of `P'`. (That module-theoretic step is the bookkeeping
half and is not formalized here; the coefficient comparison above is.)

So, over the base `S`, **`M` has an `A'`-flat `P'`-module lift if and only if `w` lies in the
Artin–Schreier image `{a² − a : a ∈ S}`.**

## The three legs, for the nodal base

Take `S = R = {f ∈ 𝔽₂[s] : f(0) = f(1)}`, the nodal ring of
`StacksFrontier.Deformation.Examples.Linear.ArtinSchreierLocalGlobal`, and `w = ω = s² + s`. Let
`𝔫 ⊆ R` be the node and `J' = ω·P'`, which is principal and has `V(J') = V(𝔫)` because `ω`
vanishes exactly at the node.

* **`M` does not lift over `P'`**: `not_isASSol_nodal`.
* **`M_g` lifts over `(P')_g` for every `g ∈ J'`**: `exists_isASSol_of_isUnit` gives the lift over
  `(P')_ω`, and every `g ∈ J' = ωP'` has `D(g) ⊆ D(ω)`, so `(P')_ω → (P')_g` is flat and
  `Deformation.HasFlatModuleLift.baseChange` — the forward implication of Stacks 0DZ2, which
  carries the source's nilpotence — transports the lift. One verification, not infinitely many.
* **`N = M ⊗_P Q` lifts over `Q'`**, for the `Q'` leg built here out of an *étale* cover rather
  than a completion. Put

  `Q₀ = R[z]/(z² + z − ω)`,  `Q = (Q₀)_{z + 1}`,  and `Q' = Q[t, x]/(t³, x² − t·x − t²·ω)`.

  Then `ω = z² + z = z·(z + 1)` in `Q₀` (`isASSol_root`), so `ω` is in the Artin–Schreier image of
  `Q₀` and of `Q`, and the lift exists by the classification. `Q₀` is free of rank two over `R`
  (`asPoly_monic`, `freeNodalQ₀`), hence flat, and `Q` is flat over `R` as a localization of it.

  The quotient condition `P'/J' = Q'/J'Q'` holds: in `Q`, `ω = z(z + 1)` with `z + 1` a unit, so
  `ωQ = zQ`, and `Q₀/(z) = R/(ω)` — the surjection `Q₀ ↠ R/(ω)` killing `z` is
  `quotByRoot`, with `quotByRoot_root` and `quotByRoot_comp_algebraMap` — while inverting `z + 1`
  does nothing modulo `z`, since `z + 1 ↦ 1` there. So `R/ωR ≅ Q/ωQ` canonically, and tensoring
  up gives `P'/J' ≅ Q'/J'Q'`.

A Zariski localization cannot play the `Q'` leg, as
`StacksFrontier.Deformation.Examples.Linear.ArtinSchreierLocalGlobal` records; the étale cover above
does, and unlike the completion it is a free rank-two algebra followed by one localization.

## What is checked here and what is not

Checked: the coefficient classification `twisted_lift_iff`; the flatness half of the
module-theoretic step, `eq_bot_of_flat_quotient_of_isNilpotent`; the `Q'` leg's algebra — `asPoly`
monic, `Q₀` free hence flat over `R`, the Artin–Schreier root in `Q₀`, and the surjection
`Q₀ ↠ R/(ω)` killing the root; and the assembled three-leg statement
`artinSchreier_three_legs`.

Not checked here, and **both done elsewhere**: the assembly of Nakayama with
`eq_bot_of_flat_quotient_of_isNilpotent` into the statement that *every* lift of `M` is an `ξ` as
above is `Deformation.Examples.ArtinSchreier.not_flat_lift_of_reduction` in
`StacksFrontier.Deformation.Examples.Linear.NodalCubicNoLift`, and the instantiation of
`Deformation.FlatModuleLiftBaseChangeStatement` with its six rings, twelve algebra instances and
seven scalar towers is
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement` in
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation`. The first of the two is not
bookkeeping — it is the module-theoretic half of the obstruction — and the quotient presentation
it needs is also what the local liftability hypothesis needs (see
`StacksFrontier.Deformation.Examples.Linear.NodalCubicLocalLift`). So this file is one input to a
Lean proof of `¬ Deformation.FlatModuleLiftBaseChangeStatement.{0}`.

Two choices make that instantiation tractable. First, present the base as a quotient rather than a
subring: `R` is the nodal cubic `𝔽₂[Y, Z]/(Z² + Y·Z + Y³)` with `ω = Y`, which makes
`IsNoetherianRing` immediate, keeps
`ω ∈ AS(R_ω)` immediate — `α = Z/Y` works because `Z² + Y·Z = Y³` *is* the relation — and still
gives `ω ∉ AS(R)` from the ring map `R → 𝔽₂[s]`, `Y ↦ s² + s`, `Z ↦ s³ + s²`, whose image lies in
the subring `nodal` of `ArtinSchreierLocalGlobal` while `s` and `s + 1` do not.
Second, take `A' = R[t]/t³` and hence `A = R`: then `P'` is free over `A'` on `{1, x}` with no
further argument, and the module-theoretic step is exactly the lemma proved here, since a lift is
then a cyclic `A'`-module.

## Main results

* `Deformation.Examples.ArtinSchreier.eq_bot_of_flat_quotient_of_isNilpotent`: **a flat quotient
  by a nilpotent ideal is the whole ring** — the flatness half of the module-theoretic step.
* `Deformation.Examples.ArtinSchreier.twisted_lift_iff`: **the lifting problem of the twisted
  family is the Artin–Schreier equation.**
* `Deformation.Examples.ArtinSchreier.isASSol_root`: `ω` is an Artin–Schreier value in
  `Q₀ = R[z]/(z² + z − ω)`, by the root itself.
* `Deformation.Examples.ArtinSchreier.freeNodalQ₀`: `Q₀` is free over the nodal ring, hence flat.
* `Deformation.Examples.ArtinSchreier.quotByRoot`: the surjection `Q₀ ↠ R/(ω)` killing the root,
  which is the quotient condition's content.
* `Deformation.Examples.ArtinSchreier.artinSchreier_three_legs`: **the three legs together** — no
  solution over the nodal ring, a solution after inverting any element of the node, and a solution
  over `Q₀`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### A flat cyclic quotient by a nilpotent ideal is trivial -/

/-- **A flat quotient by a nilpotent ideal is the whole ring.** If `A ⧸ J` is flat over `A` and
`J` is nilpotent then `J = ⊥`.

Flatness of `A ⧸ J` says exactly that `J` is a *pure* ideal, and a pure ideal is idempotent
(`Ideal.isIdempotentElem_of_pure`), so `J = J ^ k` for every `k ≥ 1`; a power of `J` vanishes, so
`J = ⊥`.

This is the module-theoretic half of the classification of lifts in the twisted family. A lift of
`M = P/(x)` is generated over `A' = S[t]/t³` by one element — Nakayama for the nilpotent `t`,
`Submodule.eq_top_of_sup_ideal_smul_top_eq_top` — so it is `A' ⧸ J` for an ideal `J` contained in
the nilpotent `ker(A' → S) = (t)`, and `A'`-flatness of the lift forces `J = ⊥` by this lemma.
The lift is therefore free of rank one over `A'`, the action of `x` on it is multiplication by an
element of `(t)`, and `twisted_lift_iff` analyses the relation that element must satisfy. -/
theorem eq_bot_of_flat_quotient_of_isNilpotent {A : Type u} [CommRing A] (J : Ideal A)
    (hnil : IsNilpotent J) (hflat : Module.Flat A (A ⧸ J)) : J = ⊥ := by
  have : J.Pure := hflat
  have hidem : J * J = J := Ideal.isIdempotentElem_of_pure J
  have hpow : ∀ k : ℕ, J = J ^ (k + 1) := by
    intro k
    induction k with
    | zero => rw [pow_one]
    | succ k ih => rw [pow_succ, ← ih, hidem]
  obtain ⟨n, hn⟩ := hnil
  rcases n with _ | m
  · rw [pow_zero, Ideal.one_eq_top, Submodule.zero_eq_bot] at hn
    exact eq_bot_mono le_top hn
  · exact (hpow m).trans hn

/-! ### The lifting problem of the twisted family is Artin–Schreier -/

/-- **The classification.** For a commutative ring `S` and `w ∈ S`, an element
`ξ = t·a + t²·b` of `S[t]/t³` satisfies the defining relation `ξ² = t·ξ + t²·w` of
`P' = S[t, x]/(t³, x² − t·x − t²·w)` if and only if `a·a = a + w`.

The left side is the equation an `A'`-flat `P'`-module lift of `M = P/(x)` must solve: such a lift
is free of rank one over `S[t]/t³`, so the action of `x` is multiplication by an element of the
kernel of `S[t]/t³ → S`, and the relation of `P'` is the displayed one. The right side is the
Artin–Schreier equation for `w`. Both sides of the comparison use only that `1`, `t`, `t²` are an
`S`-basis of `S[t]/t³` (`cst_add_tau_eq_zero_iff`) and that `t³ = 0` (`tau_cube`). -/
theorem twisted_lift_iff {S : Type u} [CommRing S] (a b w : S) :
    (tau S * cst S a + tau S * tau S * cst S b) * (tau S * cst S a + tau S * tau S * cst S b) =
        tau S * (tau S * cst S a + tau S * tau S * cst S b) + tau S * tau S * cst S w ↔
      a * a = a + w := by
  have hcube : tau S * tau S * tau S = 0 := tau_cube (R := S)
  constructor
  · intro h
    have hzero : cst S 0 + tau S * cst S 0 + tau S * tau S * cst S (a * a - a - w) = 0 := by
      rw [map_zero, map_sub, map_sub, map_mul]
      linear_combination h +
        (cst S b - 2 * cst S a * cst S b - tau S * cst S b * cst S b) * hcube
    linear_combination ((cst_add_tau_eq_zero_iff (R := S)).1 hzero).2.2
  · intro h
    have hcst : cst S a * cst S a = cst S a + cst S w := by
      rw [← map_mul, ← map_add, h]
    linear_combination (tau S * tau S) * hcst +
      (2 * cst S a * cst S b - cst S b + tau S * cst S b * cst S b) * hcube

/-! ### The `Q'` leg: an étale cover splitting the Artin–Schreier class -/

/-- The Artin–Schreier polynomial `z² + z − ω` over the nodal ring. Its root generates the étale
`ℤ/2`-cover on which the class of `ω` dies. -/
def asPoly : Polynomial nodal := X ^ 2 + (X - C omega)

/-- `z² + z − ω` is monic: it is `X²` plus something of degree at most one. -/
theorem asPoly_monic : asPoly.Monic := by
  refine (Polynomial.monic_X_pow (R := nodal) 2).add_of_left ?_
  rw [Polynomial.degree_X_pow]
  have hle : (X - C omega : Polynomial nodal).degree ≤ 1 := by
    refine le_trans (Polynomial.degree_sub_le _ _) (max_le Polynomial.degree_X_le ?_)
    exact le_trans Polynomial.degree_C_le (by norm_num)
  exact lt_of_le_of_lt hle (by norm_num)

/-- `Q₀ = R[z]/(z² + z − ω)`, the étale `ℤ/2`-cover of the nodal ring on which the
Artin–Schreier class of `ω` becomes trivial. -/
abbrev NodalQ₀ : Type := AdjoinRoot asPoly

/-- `Q₀` is free over the nodal ring, of rank two: `z² + z − ω` is monic of degree two. Hence it
is flat, which is what the `Q'` leg of Stacks 0DZ2 needs of it. -/
theorem freeNodalQ₀ : Module.Free nodal NodalQ₀ :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' asPoly_monic).basis

/-- `Q₀` is flat over the nodal ring. -/
theorem flatNodalQ₀ : Module.Flat nodal NodalQ₀ :=
  have := freeNodalQ₀
  Module.Flat.of_free

/-- **The Artin–Schreier class of `ω` dies on the étale cover `Q₀`**, witnessed by the root
itself: `z·z + z = ω` in `Q₀ = R[z]/(z² + z − ω)`, by the defining relation. Consequently `ω` is
an Artin–Schreier value in every `Q₀`-algebra, in particular in the localization `Q = (Q₀)_{z+1}`
that the quotient condition of Stacks 0DZ2 requires. -/
theorem isASSol_root :
    IsASSol (algebraMap nodal NodalQ₀ omega) (AdjoinRoot.root asPoly) := by
  have h0 : AdjoinRoot.mk asPoly (X ^ 2 + (X - C omega)) = 0 := by
    rw [show (X ^ 2 + (X - C omega) : Polynomial nodal) = asPoly from rfl]
    exact AdjoinRoot.mk_self
  have hC : AdjoinRoot.mk asPoly (C omega) = algebraMap nodal NodalQ₀ omega := rfl
  rw [map_add, map_sub, map_pow, AdjoinRoot.mk_X, hC] at h0
  unfold IsASSol
  linear_combination h0

/-- **The quotient condition's content: `Q₀/(z) = R/(ω)`.** The `R`-algebra map `Q₀ → R/(ω)`
sending the root to `0`, which exists because `z² + z − ω` evaluated at `0` is `−ω`. Together with
`ω = z·(z + 1)` in `Q₀` and invertibility of `z + 1` in `Q = (Q₀)_{z+1}`, this is the identity
`R/ωR ≅ Q/ωQ` that Stacks 0DZ2 asks of the pair `(J', Q')` for `J' = ω·P'`. -/
def quotByRoot : NodalQ₀ →+* (nodal ⧸ Ideal.span {omega}) :=
  AdjoinRoot.lift (algebraMap nodal (nodal ⧸ Ideal.span {omega})) 0 (by
    have hmem : (Ideal.Quotient.mk (Ideal.span {omega})) omega = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [asPoly]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Ideal.Quotient.algebraMap_eq]
    rw [hmem]
    ring)

/-- The map `Q₀ → R/(ω)` kills the root. -/
theorem quotByRoot_root : quotByRoot (AdjoinRoot.root asPoly) = 0 :=
  AdjoinRoot.lift_root _

/-- The map `Q₀ → R/(ω)` restricts to the quotient map on the nodal ring, so `R/(ω)` really is a
quotient of `Q₀` *as an `R`-algebra*. -/
theorem quotByRoot_comp_algebraMap (a : nodal) :
    quotByRoot (algebraMap nodal NodalQ₀ a) = Ideal.Quotient.mk (Ideal.span {omega}) a := by
  have h : quotByRoot (AdjoinRoot.of asPoly a) =
      algebraMap nodal (nodal ⧸ Ideal.span {omega}) a := AdjoinRoot.lift_of _
  simpa [Ideal.Quotient.algebraMap_eq] using h

/-- `ω = z·(z + 1)` in `Q₀`, which is why inverting `z + 1` makes `ωQ = zQ`. -/
theorem omega_eq_root_mul :
    algebraMap nodal NodalQ₀ omega =
      AdjoinRoot.root asPoly * (AdjoinRoot.root asPoly + 1) := by
  have h := isASSol_root
  unfold IsASSol at h
  linear_combination -h

/-! ### The three legs -/

/-- **The three legs of the realization, together.** For the nodal ring `R` and `ω = s² + s`:

1. the Artin–Schreier equation for `ω` has **no** solution over `R`, so by `twisted_lift_iff` the
   module `M = P/(x)` has no `A'`-flat `P'`-module lift;
2. it has a solution over every `R`-algebra in which some element of the node ideal becomes a
   unit — in particular over `R_ω`, which by flatness of `(P')_ω → (P')_g` and the forward
   implication of Stacks 0DZ2 gives local liftability at every `g ∈ J' = ω·P'`;
3. it has a solution over the étale cover `Q₀ = R[z]/(z² + z − ω)`, hence over the localization
   `Q = (Q₀)_{z+1}` which is flat over `R` with `R/ωR ≅ Q/ωQ`, so `N = M ⊗_P Q` lifts over `Q'`.

Those are the three hypotheses and the negated conclusion of Stacks 0DZ2 at the source's
hypotheses, with `I = (t)` nilpotent of index three and not square-zero. -/
theorem artinSchreier_three_legs :
    (¬ ∃ b : nodal, IsASSol omega b) ∧
      (∃ b : Localization.Away omega,
        IsASSol (algebraMap nodal (Localization.Away omega) omega) b) ∧
      (∃ b : NodalQ₀, IsASSol (algebraMap nodal NodalQ₀ omega) b) := by
  refine ⟨not_isASSol_nodal, ?_, ⟨AdjoinRoot.root asPoly, isASSol_root⟩⟩
  refine exists_isASSol_of_isUnit (algebraMap nodal (Localization.Away omega)) omega_mem ?_ ?_
  · simp only [eval_add, eval_pow, eval_X]
    decide
  · exact IsLocalization.Away.algebraMap_isUnit omega

end Deformation.Examples.ArtinSchreier

end
