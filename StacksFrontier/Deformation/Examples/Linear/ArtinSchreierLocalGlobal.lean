module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# A symmetric quadratic correction equation with no global solution

The nilpotent form of Stacks 0DZ2 reduces — see the structural discussion in
`StacksFrontier.Deformation.Examples.Linear.MaurerCartanWindowObstructed` — to one local-to-global
question for the quadric `ω + β(z) + z ∪ z = 0` cut out of a finite module over the affine
`Spec P'`, given a point over `(P')_g` for every `g ∈ J'` and a point over `Q'`. The abstract
principle is false (`Deformation.Examples.QuadraticCorrection.not_quadraticLocalGlobal`), but its
mechanism is two **disjoint branches** of an idempotent carrying the two local solutions, and the
structured window has no such branches: its solution set is symmetric under `a ↦ 1 − a`
(`Deformation.Examples.MaurerCartanWindow.window_sol_one_sub`), so no existence-only local datum
is pinned to one branch. The natural hope is that this symmetry, plus local points on a `J'`-cover
and a point over `Q'`, forces a global point.

**It does not.** This file exhibits a quadratic equation which *has* that symmetry and still fails
local-to-global, on a pair `(J, Q)` of exactly the shape Stacks 0DZ2 provides. The equation is
Artin–Schreier,

`z² + z = ω`,

in characteristic two. It is invariant under `z ↦ z + 1` — the symmetry of the window, since
`(z + 1)² + (z + 1) = z² + z` when `2 = 0` — and its solvability over a ring `S` of characteristic
two is the vanishing of a class in `S/{b² + b}`, which for affine `S` is `H¹_ét(Spec S, ℤ/2)`. So
the failure is an `H¹`, not a branch: exactly the glueing-type obstruction that the point-supported
candidates could not produce.

## The ring and the class

Let `Amb = 𝔽₂[s]` and let `R ⊆ Amb` be the subring of polynomials with `f(0) = f(1)`
(`Deformation.Examples.ArtinSchreier.nodal`). `Spec R` is the affine line with the two points
`s = 0` and `s = 1` glued — an irreducible curve with one node, whose complement of the node is
`Spec R ∖ {𝔫} = 𝔸¹ ∖ {0, 1}`, irreducible and therefore **connected**, while the node's own
punctured neighbourhood has **two** branches. That is the configuration that makes
`Ȟ¹({Spec R ∖ V(𝔫), Spec R^∧_𝔫}, ℤ/2) = 𝔽₂ ≠ 0`: the two pieces are connected and their overlap
is not.

Take `ω = s² + s`, which lies in `R` because it vanishes at both `0` and `1`.

* **No solution over `R`** (`not_isASSol_nodal`). Over the domain `Amb`, `b² + b = s² + s` forces
  `(b + s)(b + s + 1) = 0`, so `b = s` or `b = s + 1`; neither lies in `R`, since `s` takes the
  values `0` and `1` at `0` and `1` and `s + 1` takes `1` and `0`.
* **A solution after inverting any `g ∈ 𝔫`** (`exists_isASSol_of_isUnit`). The point is the
  identity `(s·g)·(s·g) + (s·g)·g = g·g·ω` in `R` — all three of `s·g`, `g` and `g²ω` lie in `R`
  once `g(1) = 0` — so `b = (s·g)/g` solves the equation wherever `g` is invertible. Since
  `D(g) ⊆ Spec R ∖ V(𝔫)` for `g ∈ 𝔫` and `s` is a regular function there, this is just the
  statement that the class dies on the complement of the node.
* **A solution over the `𝔫`-adic completion `Q = R^∧_𝔫`**, which is the `Q'` side of the Stacks
  0DZ2 hypothesis: `R → Q` is flat and `R/𝔫 = Q/𝔫Q`. This is not formalized here, and it is the
  one step that needs no cleverness: `z² + z − ω` is **étale** (its derivative is `1`), `ω ∈ 𝔫`,
  and `z = 0` solves it modulo `𝔫`, so Hensel's lemma in the complete local ring `Q` produces a
  solution. Concretely `Q ≅ {(f, g) ∈ 𝔽₂[[u]] × 𝔽₂[[v]] : f(0) = g(0)}` with `s ↦ (u, 1 + v)`,
  and `b = (u, v)` solves `b² + b = ω` because `u² + u` and `(1 + v)² + (1 + v) = v² + v` are the
  two branch expansions of `ω`. A Zariski localization cannot do this: for `h ∉ 𝔫` a solution over
  `R_h` would force `s ∈ R_h`, i.e. `s·hᵏ ∈ R`, which at `s = 1` reads `1 = 0`. The completion is
  needed precisely because it disconnects the punctured node, which no open subset of an
  irreducible curve does.

## What this decides

The symmetry `z ↦ z + 1` does **not** force a global point. So the positive route to the nilpotent
form of Stacks 0DZ2 cannot be closed by the structure identified so far: local points on the
`J'`-cover, a point over `Q'`, and the `a ↦ 1 − a` symmetry are all present here and there is still
no global point. What a counterexample to Stacks 0DZ2 itself additionally needs is to realize this
`H¹` class as the obstruction quadric of a module-lifting instance — which, by the `n = 2`
computation in characteristic two, means a base `R₂` of dimension two with `q, r, p ∈ R₂`,
`p² = q·r`, such that `R₂/(q, r)` is this nodal ring and the constraint `q·C + r·B = p` forces
`B·C ≡ ω` modulo `{b² + b}`. That realization is not carried out here.

## Main definitions

* `Deformation.Examples.ArtinSchreier.nodal`: the subring `{f ∈ 𝔽₂[s] : f(0) = f(1)}`, the
  coordinate ring of the affine line with `0` and `1` glued.
* `Deformation.Examples.ArtinSchreier.IsASSol`: the Artin–Schreier equation `b² + b = ω`.

## Main results

* `Deformation.Examples.ArtinSchreier.isASSol_add_one`: **the equation is symmetric under
  `z ↦ z + 1`** in characteristic two — the same symmetry as the window's `a ↦ 1 − a`.
* `Deformation.Examples.ArtinSchreier.not_isASSol_nodal`: **no solution over the nodal ring.**
* `Deformation.Examples.ArtinSchreier.exists_isASSol_of_isUnit`: **a solution over any algebra in
  which some `g` of the node ideal becomes a unit** — in particular over `R_g` for every
  `g ∈ 𝔫`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public section

open Polynomial

namespace Deformation.Examples.ArtinSchreier

/-- The ambient ring `𝔽₂[s]`. -/
abbrev Amb : Type := Polynomial (ZMod 2)

/-- **The nodal ring.** The subring `{f ∈ 𝔽₂[s] : f(0) = f(1)}` of `𝔽₂[s]`: the coordinate ring
of the affine line with the two rational points `0` and `1` glued, an irreducible affine curve
with a single node. -/
noncomputable def nodal : Subring Amb :=
  (Polynomial.evalRingHom (0 : ZMod 2)).eqLocus (Polynomial.evalRingHom (1 : ZMod 2))

/-- A polynomial `f ∈ 𝔽₂[s]` lies in the nodal ring if and only if `f(0) = f(1)`. -/
theorem mem_nodal {f : Amb} : f ∈ nodal ↔ f.eval 0 = f.eval 1 := by
  rw [nodal, RingHom.mem_eqLocus]
  simp

/-- `ω = s² + s` lies in the nodal ring: it vanishes at `0` and at `1`. -/
theorem omega_mem : (X ^ 2 + X : Amb) ∈ nodal := by
  rw [mem_nodal]
  simp only [eval_add, eval_pow, eval_X]
  decide

/-- `ω = s² + s`, as an element of the nodal ring. -/
noncomputable def omega : nodal := ⟨X ^ 2 + X, omega_mem⟩

/-- The Artin–Schreier equation `b² + b = ω`. -/
def IsASSol {S : Type*} [CommRing S] (w b : S) : Prop := b * b + b = w

/-- **The Artin–Schreier equation is symmetric under `z ↦ z + 1`** in characteristic two: this is
the same symmetry that the Maurer–Cartan window of the nilpotent dévissage of Stacks 0DZ2 has
under `a ↦ 1 - a`, so the hope that that symmetry forces a global solution has to survive this
equation — and it does not. -/
theorem isASSol_add_one {S : Type*} [CommRing S] (h2 : (2 : S) = 0) {w b : S}
    (h : IsASSol w b) : IsASSol w (b + 1) := by
  unfold IsASSol at h ⊢
  linear_combination h + (b + 1) * h2

/-! ### No solution over the nodal ring -/

/-- Over the domain `𝔽₂[s]` the only solutions of `b² + b = s² + s` are `b = s` and `b = s + 1`. -/
theorem eq_or_eq_of_isASSol_amb {b : Amb} (h : IsASSol (X ^ 2 + X : Amb) b) :
    b = X ∨ b = X + 1 := by
  have h2 := CharTwo.two_eq_zero (R := Amb)
  have hfac : (b + X) * (b + X + 1) = 0 := by
    unfold IsASSol at h
    linear_combination h + (b * X + X ^ 2 + X) * h2
  rcases mul_eq_zero.mp hfac with hb | hb
  · exact Or.inl (by linear_combination hb - X * h2)
  · exact Or.inr (by linear_combination hb - (X + 1) * h2)

/-- **The Artin–Schreier class of `ω = s² + s` is nonzero over the nodal ring.** The two solutions
over `𝔽₂[s]` are `s` and `s + 1`, and neither takes the same value at `0` and at `1`: `s` takes
`0` and `1`, and `s + 1` takes `1` and `0`. So the equation has no solution in the subring where
those two values agree.

Geometrically this is the nontrivial `ℤ/2`-torsor on the nodal curve obtained by gluing the two
sheets of the trivial double cover of `𝔸¹` straight at `s = 0` and crosswise at `s = 1`. -/
theorem not_isASSol_nodal : ¬ ∃ b : nodal, IsASSol omega b := by
  rintro ⟨⟨b, hb⟩, h⟩
  have hamb : IsASSol (X ^ 2 + X : Amb) b := by
    have hval := congrArg (Subring.subtype nodal) h
    simpa [IsASSol, omega] using hval
  rw [mem_nodal] at hb
  rcases eq_or_eq_of_isASSol_amb hamb with rfl | rfl
  · simp only [eval_X] at hb
    exact absurd hb (by decide)
  · simp only [eval_add, eval_X, eval_one] at hb
    exact absurd hb (by decide)

/-! ### A solution after inverting an element of the node ideal -/

/-- If `g` lies in the nodal ring and vanishes at `1` — so, being in the nodal ring, at `0` too,
i.e. `g` lies in the maximal ideal `𝔫` of the node — then `s·g` lies in the nodal ring. -/
theorem mul_X_mem {g : Amb} (hg1 : g.eval 1 = 0) : X * g ∈ nodal := by
  rw [mem_nodal]
  simp [hg1]

/-- The identity that solves the equation after inverting `g`, stated in the ambient ring:
`(s·g)² + (s·g)·g = g²·(s² + s)`. -/
theorem key_identity (g : Amb) :
    (X * g) * (X * g) + (X * g) * g = g * g * (X ^ 2 + X) := by ring

/-- **The Artin–Schreier class of `ω` dies after inverting any element of the node ideal.** Let
`φ : R → S` be a ring homomorphism out of the nodal ring and let `g ∈ 𝔫` — an element of the
nodal ring vanishing at `1` — whose image is a unit in `S`. Then `b = φ(s·g)·φ(g)⁻¹` solves
`b² + b = φ(ω)`.

Applied to `φ : R → R_g` this says the class dies on `D(g)`, for every `g ∈ 𝔫`. Together with
`not_isASSol_nodal` and the solution over the `𝔫`-adic completion, it is the local-to-global
failure: exactly the hypotheses Stacks 0DZ2 supplies, for a quadratic equation carrying the
window's own symmetry. -/
theorem exists_isASSol_of_isUnit {S : Type*} [CommRing S] (φ : nodal →+* S)
    {g : Amb} (hg : g ∈ nodal) (hg1 : g.eval 1 = 0)
    (hu : IsUnit (φ ⟨g, hg⟩)) :
    ∃ b : S, IsASSol (φ omega) b := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hXg : X * g ∈ nodal := mul_X_mem hg1
  have hnodal : (⟨X * g, hXg⟩ : nodal) * ⟨X * g, hXg⟩ + ⟨X * g, hXg⟩ * ⟨g, hg⟩ =
      (⟨g, hg⟩ : nodal) * ⟨g, hg⟩ * omega :=
    Subtype.ext (key_identity g)
  have hkey : φ ⟨X * g, hXg⟩ * φ ⟨X * g, hXg⟩ + φ ⟨X * g, hXg⟩ * φ ⟨g, hg⟩ =
      φ ⟨g, hg⟩ * φ ⟨g, hg⟩ * φ omega := by
    rw [← map_mul, ← map_mul, ← map_add, hnodal, map_mul, map_mul]
  refine ⟨φ ⟨X * g, hXg⟩ * v, ?_⟩
  unfold IsASSol
  linear_combination (v * v) * hkey +
    (φ omega * (φ (⟨g, hg⟩ : nodal) * v + 1) - φ (⟨X * g, hXg⟩ : nodal) * v) * hv

end Deformation.Examples.ArtinSchreier

end
