module

public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic

/-!
# Dehomogenizations at two trivializations differ by a graded unit, and the chart does not see it

A quotient pair has no canonical trivialization: over an open where two degree-one sections `s`
and `s'` both generate, the two dehomogenizations of
`StacksDraft.AlgebraicGeometry.F3.ProjF1Dehomogenization.Basic` differ by the unit ratio `u` of
the two bases, degree by degree — `ψ'(a) = uⁿ · ψ(a)` for `a` homogeneous of degree `n`. The
glueing step of Tag 01O4's classifying morphism needs that this difference is invisible: the two
charts of `Proj` must agree on the overlap.

This file proves that at the ring level, which is where the content is. The homomorphism out of
the degree-zero part of the localization at a positive-degree element — the ring homomorphism
whose `Spec` *is* the chart morphism, by
`Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom` — is
**unchanged** by such a rescaling: the fraction `p / tᵏ` with `p` of degree `k · d` goes to
`ψ(p) · ψ(t)⁻ᵏ = u^{kd} φ(p) · (u^d φ(t))⁻ᵏ = φ(p) · φ(t)⁻ᵏ`, and the two powers of `u`
cancel exactly.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.awayHomOfIsUnit`: for a ring homomorphism
  `φ : A →+* P` inverting a positive-degree homogeneous `t`, the induced homomorphism
  `(A_t)₀ →+* P`, `p / tᵏ ↦ φ(p) · φ(t)⁻ᵏ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.awayHomOfIsUnit_mk`: its value on a
  fraction, with the inverse supplied by the caller.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.projAwayHom_eq_awayHomOfIsUnit`: the
  homomorphism on sections of Mathlib's chart morphism
  `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` is an instance of it. This is what makes
  the next result a statement about the chart and not only about an auxiliary gadget.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.awayHomOfIsUnit_eq_of_gradedUnitScaling`:
  **the cocycle identity.** Two ring homomorphisms differing by a graded unit induce the *same*
  homomorphism out of `(A_t)₀`.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize_pow_mul`: two trivializations of
  one quotient pair whose coefficients differ by the powers of a unit have dehomogenizations in
  exactly the relation the cocycle identity consumes.

## Implementation notes

**Why this is stated for an arbitrary commutative ring and not for `Γ(X, X_{f t})`.** The two
chart morphisms attached to `φ` and `ψ` have *different* sources on the nose,
`X_{φ t}` and `X_{ψ t}`, which are equal as opens — `ψ t = u^d · φ t` and `u^d` is a unit — but
not syntactically. Stating the cocycle identity for homomorphisms into one fixed ring keeps the
whole argument free of that transport; the transport is the one step still owed before the
morphisms themselves can be glued, and it is recorded below rather than hidden.

**The inverse is supplied by the caller.** `awayHomOfIsUnit_mk` takes `v` with `φ t * v = 1`
rather than producing `IsUnit.unit⁻¹`, following
`Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one`: in the cocycle proof the
inverse of `ψ t` is met as `(u⁻¹)^d * v`, never as a chosen unit.

## What is not done here

No project tag is attached. The cocycle identity is the ring-level half of the glueing; what
remains is the passage from "the two charts induce the same homomorphism out of `(A_t)₀`" to
"the two morphisms into `Proj` agree on the overlap", which needs the identification of
`X_{ψ t}` with `X_{φ t}` and then
`Stacks.ProjGlobalSectionsAppTop.eq_toBasicOpenOfGlobalSections`. With that in hand,
`AlgebraicGeometry.Scheme.Cover.glueMorphisms` finishes the glueing, and the remaining residue
of the label `01O4 "represents_f1"` is the bijectivity of the assembled map. See the
accompanying report.

## References

* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjF1Dehomogenization

universe w u

/-! ### The homomorphism out of the degree-zero localization -/

section Algebraic

variable {σ : Type*} {R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {P : Type w} [CommRing P]

/-- **The homomorphism `(A_t)₀ →+* P` induced by a ring homomorphism inverting `t`.** It sends
the degree-zero fraction `p / tᵏ` to `φ(p) · φ(t)⁻ᵏ`. -/
public def awayHomOfIsUnit (φ : R →+* P) {t : R} (hu : IsUnit (φ t)) : Away 𝒜 t →+* P :=
  (Localization.awayLift φ t hu).comp (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- **The value on a fraction**, with an inverse of `φ t` supplied by the caller. -/
public theorem awayHomOfIsUnit_mk (φ : R →+* P) {t : R} (hu : IsUnit (φ t)) {d : ℕ}
    (hd : t ∈ 𝒜 d) (k : ℕ) (p : R) (hp : p ∈ 𝒜 (k • d)) {v : P} (hv : φ t * v = 1) :
    awayHomOfIsUnit 𝒜 φ hu (Away.mk 𝒜 hd k p hp) = φ p * v ^ k := by
  rw [awayHomOfIsUnit, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  exact Localization.awayLift_mk φ t p v hv k

/-- **Mathlib's chart morphism acts on sections by `awayHomOfIsUnit`.** The homomorphism
`Stacks.ProjGlobalSectionsAppTop.projAwayHom`, which is `AlgebraicGeometry.Proj`'s chart morphism
read on global sections, is the one induced by restriction of `f` to the nonvanishing locus of
`f t`. -/
public theorem projAwayHom_eq_awayHomOfIsUnit {X : Scheme.{u}} (f : R →+* Γ(X, ⊤)) {t : R} :
    Stacks.ProjGlobalSectionsAppTop.projAwayHom 𝒜 f =
      awayHomOfIsUnit 𝒜
        ((Stacks.ProjGlobalSectionsAppTop.resTop (X.basicOpen (f t))).comp f)
        (Stacks.ProjGlobalSectionsAppTop.isUnit_resTop_basicOpen (f t)) := by
  rw [Stacks.ProjGlobalSectionsAppTop.projAwayHom,
    Stacks.ProjGlobalSectionsAppTop.resLift_awayLocMap]
  rfl

/-- **The cocycle identity.** Two ring homomorphisms out of a graded ring that differ by the
powers of a unit — `ψ(a) = uⁿ · φ(a)` for `a` homogeneous of degree `n` — induce the *same*
homomorphism out of the degree-zero part of the localization at a positive-degree homogeneous
element.

This is the reason a classifying morphism to `Proj` does not depend on the trivialization chosen
to dehomogenize with: the numerator of a degree-zero fraction `p / tᵏ` carries `u ^ (k · d)` and
the denominator carries `(u ^ d) ^ k`, and these cancel. -/
public theorem awayHomOfIsUnit_eq_of_gradedUnitScaling {φ ψ : R →+* P} (u : Pˣ)
    (hscale : ∀ (n : ℕ) (a : R), a ∈ 𝒜 n → ψ a = (u : P) ^ n * φ a)
    {t : R} {d : ℕ} (hd : t ∈ 𝒜 d) (hφ : IsUnit (φ t)) (hψ : IsUnit (ψ t)) :
    awayHomOfIsUnit 𝒜 ψ hψ = awayHomOfIsUnit 𝒜 φ hφ := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hφ
  have hcancel : ∀ (m : ℕ) (x y : P),
      (u : P) ^ m * x * ((↑u⁻¹ : P) ^ m * y) = x * y := fun m x y => by
    have h : (u : P) ^ m * (↑u⁻¹ : P) ^ m = 1 := by rw [← mul_pow, u.mul_inv, one_pow]
    linear_combination (x * y) * h
  have hvψ : ψ t * ((↑u⁻¹ : P) ^ d * v) = 1 := by
    rw [hscale d t hd, hcancel, hv]
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hd fun k p hp => ?_
  rw [awayHomOfIsUnit_mk 𝒜 ψ hψ hd k p hp hvψ, awayHomOfIsUnit_mk 𝒜 φ hφ hd k p hp hv,
    hscale (k • d) p hp]
  have hpow : ((↑u⁻¹ : P) ^ d * v) ^ k = (↑u⁻¹ : P) ^ (k * d) * v ^ k := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm d k]
  rw [smul_eq_mul, hpow, hcancel]

end Algebraic

/-! ### Two trivializations of one quotient pair -/

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f) (U : S.Opens) {B : Type w} [CommRing B]
  (Θ Θ' : GradedSectionAlgebraHom (TA T P.L).tensor (op (f ⁻¹ᵁ U)) B)

/-- **Two trivializations differing by the powers of a unit dehomogenize to graded multiples.**
This is exactly the hypothesis `awayHomOfIsUnit_eq_of_gradedUnitScaling` consumes, so the two
charts of `Proj` built from the two trivializations of one pair induce the same homomorphism out
of the `Away` ring.

The hypothesis is the relation between the coefficient maps of two trivializing sections of the
same invertible sheaf: if `s' = u · s` then the coefficient against `s' ^ n` is `uⁿ` times the
coefficient against `s ^ n`. -/
public theorem dehomogenize_pow_mul (u : B)
    (h : ∀ (n : ℕ) (x : A.sectionPieces U n),
      Θ'.toFun (n : ℤ) ((P.ψ (n : ℤ)).val.app (op U) x) =
        u ^ n * Θ.toFun (n : ℤ) ((P.ψ (n : ℤ)).val.app (op U) x))
    (n : ℕ) (a : A.sectionRing U) (ha : a ∈ A.grading U n) :
    dehomogenize A TA P U Θ' a = u ^ n * dehomogenize A TA P U Θ a := by
  obtain ⟨x, rfl⟩ := ha
  rw [dehomogenize_of, dehomogenize_of]
  exact h n x

end Stacks.AlgebraicGeometry.ProjF1Dehomogenization

end
