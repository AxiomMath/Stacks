module

import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.LinearAlgebra.Matrix.CommSemiring

public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Henselian.TFAE.Conditions
import all StacksFrontier.RingTheory.Henselian.TFAE.Conditions
public import StacksFrontier.RingTheory.Henselian.TFAE.Decompositions
import all StacksFrontier.RingTheory.Henselian.TFAE.Decompositions
public import StacksFrontier.RingTheory.Henselian.TFAE.MonicFactorization
import all StacksFrontier.RingTheory.Henselian.TFAE.MonicFactorization

@[expose] public section

/-!
# Characterisations of henselian local rings

Let `(R, 𝔪, κ)` be a local ring. This file proves Lemma 04GG: the thirteen conditions

1. `R` is henselian;
2. root lifting for arbitrary (not necessarily monic) polynomials;
3. lifting a coprime factorisation of `f̄` for monic `f`;
4. the same with `deg g = deg g₀`;
5. lifting a coprime factorisation of `f̄` for arbitrary `f`;
6. the same with `deg g = deg g₀`, for `g₀ ≠ 0`;
7. existence of a retraction of an étale `R`-algebra along a prime over `𝔪` with residue field `κ`;
8. unique existence of such a retraction pinned by `τ⁻¹(𝔪) = q`;
9. every finite `R`-algebra is a product of local rings;
10. every finite `R`-algebra is a *finite* product of local rings;
11. every finite type `R`-algebra splits as `A × B` with `A` finite and `B` nowhere quasi-finite
    over `𝔪`;
12. the same with every irreducible component of `Spec(κ ⊗_R B)` of dimension `≥ 1`;
13. every quasi-finite `R`-algebra splits as `A × B` with `A` finite and `κ ⊗_R B = 0`

are equivalent.

## Main results

* `HenselianLocalRing.TFAE_factorization_etale_quasiFinite`: the thirteen conditions, as one
  `List.TFAE`.

## Implementation notes

The thirteen conditions are named `Item1`, …, `Item13` as private reducible abbreviations, so that
each implication of the source's proof is a separate private lemma whose statement can be read
without unfolding the `List.TFAE`.

The implications proved are the source's, with four economies.

*7 ⇒ 1 in place of 7 ⇒ 8 and 8 ⇒ 2.* The source proves the "really unimportant" 7 ⇒ 8 only in
order to place (7) in the equivalence class, and then 8 ⇒ 2. The retraction produced by (7) already
suffices for that argument, which uses existence and not uniqueness, so 7 ⇒ 1 does both at once;
and (2) is reached from (1) by an elementary change of variables (see the docstring of
`item1_imp_item2`), the non-monic case of root lifting being the monic case for the reversal of a
rescaling.

*10 ⇒ 9 and 9 ⇒ 1 in place of 9 ⇒ 10 and 10 ⇒ 1.* Here 10 ⇒ 9 is a restriction, and 9 ⇒ 1
contains the source's argument for 9 ⇒ 10 as its first step: a module-finite `R`-algebra which is a
product of local rings has finitely many factors, because the idempotents cutting them out have
nonzero reductions in the finite `κ`-algebra `S/𝔪S` and orthogonal nonzero idempotents are
linearly independent (`finite_of_ringEquiv_pi_local`).

*12 ⇒ 13 in place of the source's 11 ⇔ 12.* The source closes the pair (11), (12) by reading the
definition of quasi-finiteness at a prime in both directions; only 11 ⇒ 12 needs that reading,
while the return edge is cheaper through (13), where quasi-finiteness makes the fibre a finite,
hence artinian, `κ`-algebra whose components all have dimension zero.

*(8), (10) and (11) from (1) directly.* The source reaches (10) and (11) from (8) by an étale base
change (Lemma 00UK) followed by descent along the retraction; both are instead deduced from (1),
since the henselian decomposition of a finite type algebra is available as
  `exists_algEquiv_prod_of_henselianLocalRing` and its
module-finite case as `exists_algEquiv_pi_isLocalRing`, and 1 ⇒ 8 likewise from
`henselian_etale_retraction` and `henselian_etale_retraction_unique`.

*The common last step of 3 ⇒ 1, 9 ⇒ 1 and 13 ⇒ 1.* Each of the three produces a factor `A` of a
flat `R`-algebra in which the image `y` of `T` is a root of `f` congruent to a lift `b` of `a₀`
modulo `𝔪 A`, and each ends in `exists_isRoot_of_sub_mem`: a nontrivial finite free `R`-algebra all
of whose elements are scalars modulo `𝔪 A` has bijective structure map (surjectivity by Nakayama,
injectivity because a scalar killing a basis element is zero), so the preimage of `y` is the root.
What differs is how the three see that `y ≡ b`, which by `sub_mem_of_isUnit_aeval` amounts to
`h(y)` being invertible, for `h` the lift of `f̄/(T - a₀)`: in 3 ⇒ 1 the factorisation supplied by
(3) makes the two images generate the unit ideal, so `A` is a summand cut out by an idempotent and
`h(y)` is a unit on it; in 13 ⇒ 1 the algebra is `(R[T]/(f))_h`, where `h` is invertible by
construction; in 9 ⇒ 1 the factor is local, and `h(y)` is a unit because its residue `h̄(a₀)` is
nonzero.

*The block (3), (4), (5), (6)* is entered at (6) and left at (3), as in the source. Leaving it at
(4) instead would be cheap — a factorisation `f = gh` with `ḡ = T - a₀` and `deg g = deg g₀ = 1`
has unit leading coefficient, and writing `g = C c₁ * T + C c₀` the element `-c₁⁻¹c₀` is the
root — but the missing edge 3 ⇒ 4 is not degree bookkeeping on a lift produced by (3): that lift
can have inflated degree, and over
`R = k[ε]/(ε²)` with `f = T` the coprime factorisation `f̄ = T · 1` lifts as
`T = (T + εT²)(1 - εT)`, whose first factor has degree `2` and reduction of degree `1`. So 3 ⇒ 4
carries the content of 3 ⇒ 1, and the block is left at (3).

The resulting nineteen implications form a single strongly connected digraph on the thirteen
items: `1 → 8 → 7 → 1`, `1 → 2 → 1`, `1 → 10 → 9 → 1`, `1 → 11 → 13 → 1`, `11 → 12 → 13`,
`1 → 6 → 5 → 3 → 1` and `6 → 4 → 3`.

## Organisation

The proof is in four files. `StacksFrontier.RingTheory.Henselian.TFAE.Conditions` states the thirteen
conditions and proves the easy implications and the cycle `1 → 8 → 7 → 1`;
`StacksFrontier.RingTheory.Henselian.TFAE.Decompositions` proves `1 → 2 → 1`, `1 → 10 → 9 → 1`,
`1 → 11 → 13 → 1`, `11 → 12 → 13` and 3 ⇒ 1;
`StacksFrontier.RingTheory.Henselian.TFAE.MonicFactorization` lifts monic coprime factorisations
through the retraction of (8). This file proves the quasi-finiteness of `R[T]/(f)` for `f` with
monic reduction, deduces 1 ⇒ 6 through the finite factor of `R[T]/(f)` supplied by (11), and
assembles the nineteen implications into the `List.TFAE`.

## References

* [StacksProject 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

universe u

@[expose] public section

namespace Stacks.Henselian.Characterizations

open Polynomial IsLocalRing TensorProduct

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-! ### Quasi-finiteness of `R[T]/(f)` for `f` with monic reduction -/

/-- `K ⊗_R (R[T]/(f))` is finite over a field `K` as soon as `f` does not die in `K[T]`: the
tensor product is the quotient of `K[T]` by the ideal generated by the image of `f`. -/
private theorem finite_tensor_quot_span {R₀ : Type*} [CommRing R₀] (K : Type*) [Field K]
    [Algebra R₀ K] (f : R₀[X]) (hf : f.map (algebraMap R₀ K) ≠ 0) :
    Module.Finite K (K ⊗[R₀] (R₀[X] ⧸ (Ideal.span {f} : Ideal R₀[X]))) := by
  classical
  have h1 : Module.Finite K (K[X] ⧸ (Ideal.span {f.map (algebraMap R₀ K)} : Ideal K[X])) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hf).basis
  set e2 : K[X] ≃ₐ[K] K ⊗[R₀] R₀[X] := polyEquivTensor' R₀ K with he2
  have hmap : ((Ideal.span {f} : Ideal R₀[X]).map
      (Algebra.TensorProduct.includeRight (R := R₀) (A := K) (B := R₀[X]))).map
      (e2.symm : (K ⊗[R₀] R₀[X]) →+* K[X])
      = (Ideal.span {f.map (algebraMap R₀ K)} : Ideal K[X]) := by
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    congr 1
    simp [he2]
  let e3 : ((K ⊗[R₀] R₀[X]) ⧸ (Ideal.span {f} : Ideal R₀[X]).map
      (Algebra.TensorProduct.includeRight (R := R₀) (A := K) (B := R₀[X])))
      ≃ₐ[K] K[X] ⧸ (Ideal.span {f.map (algebraMap R₀ K)} : Ideal K[X]) :=
    Ideal.quotientEquivAlg _ _ e2.symm hmap.symm
  let e1 : K ⊗[R₀] (R₀[X] ⧸ (Ideal.span {f} : Ideal R₀[X]))
      ≃ₐ[K] (K ⊗[R₀] R₀[X]) ⧸ (Ideal.span {f} : Ideal R₀[X]).map
        (Algebra.TensorProduct.includeRight (R := R₀) (A := K) (B := R₀[X])) :=
    Algebra.TensorProduct.tensorQuotientEquiv K R₀[X] K _
  exact Module.Finite.of_surjective (e1.trans e3).symm.toLinearMap
    (e1.trans e3).symm.surjective

/-- If the reduction of `f` to the residue field is monic, the coefficient of `f` in the degree of
that reduction is a unit. -/
private theorem isUnit_coeff_natDegree_of_map_monic {R₀ : Type*} [CommRing R₀] [IsLocalRing R₀]
    {f : R₀[X]} (hf : (f.map (residue R₀)).Monic) :
    IsUnit (f.coeff (f.map (residue R₀)).natDegree) := by
  rw [← residue_ne_zero_iff_isUnit, ← Polynomial.coeff_map, hf.coeff_natDegree]
  exact one_ne_zero

/-- If the reduction of `f` to the residue field of a local ring is monic then `R[T]/(f)` is
quasi-finite: the leading coefficient of `f̄` lifts to a unit, so `f` survives in every fibre. -/
private theorem quasiFinite_adjoinRoot_of_map_monic {R₀ : Type*} [CommRing R₀] [IsLocalRing R₀]
    (f : R₀[X]) (hf : (f.map (residue R₀)).Monic) :
    Algebra.QuasiFinite R₀ (AdjoinRoot f) := by
  classical
  set d := (f.map (residue R₀)).natDegree with hd
  have hunit : IsUnit (f.coeff d) := isUnit_coeff_natDegree_of_map_monic hf
  refine ⟨fun P hP => ?_⟩
  have hne : f.map (algebraMap R₀ P.ResidueField) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun p : (P.ResidueField)[X] => Polynomial.coeff p d) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
    exact (hunit.map (algebraMap R₀ P.ResidueField)).ne_zero h1
  exact finite_tensor_quot_span P.ResidueField f hne


/-- **The finite factor of `R[T]/(f)` and the idempotent that cuts it out.** Let `f ∈ R[T]` have
monic reduction. Then there are a module-finite `R`-algebra `A`, a surjection
`π : R[T]/(f) → A`, and polynomials `G`, `v` with `v̄ = 1` and `G ≡ v` modulo `f`, such that `G`
annihilates the kernel of `π`: `π(p) = 0` implies `f ∣ pG`.

Concretely `G` lifts the idempotent `e ∈ R[T]/(f)` with `A = e·(R[T]/(f))`, and `v̄ = 1` records
that `1 - e` lies in `𝔪·R[T]/(f)`, that is, that the complementary factor `B` has vanishing fibre
over the closed point.

This is item (11) applied to the finite type algebra `R[T]/(f)` — available from (1) as
`item1_imp_item11` — together with the observation that the fibre `κ ⊗_R R[T]/(f) = κ[T]/(f̄)` is
finite over `κ`, since `f̄ ≠ 0`. So no prime of `B` over `𝔪` can fail to be isolated in the fibre,
whence `B` has no prime over `𝔪` at all and `𝔪B = B`. -/
private lemma exists_module_finite_of_map_monic (h1 : Item1 R) (f : R[X])
    (hf : (f.map (residue R)).Monic) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (π : AdjoinRoot f →ₐ[R] A) (G v : R[X]), Function.Surjective π ∧
      v.map (residue R) = 1 ∧ f ∣ G - v ∧
      ∀ p : R[X], π (AdjoinRoot.mk f p) = 0 → f ∣ p * G := by
  classical
  obtain ⟨A, B, hcA, hcB, haA, haB, e, hAfin, hBsub⟩ :=
    item11_imp_item13 R (item1_imp_item11 R h1) (AdjoinRoot f) inferInstance
      (quasiFinite_adjoinRoot_of_map_monic f hf)
  set π : AdjoinRoot f →ₐ[R] A := (AlgHom.fst R A B).comp (e : AdjoinRoot f →ₐ[R] A × B) with hπ
  have hπsurj : Function.Surjective π := Prod.fst_surjective.comp e.surjective
  -- the complementary factor has no point over the closed point, so `𝔪B = B`
  have hBsub' : Subsingleton ((R ⧸ maximalIdeal R) ⊗[R] B) := hBsub
  have hBtop : Ideal.map (algebraMap R B) (maximalIdeal R) = ⊤ :=
    Ideal.Quotient.subsingleton_iff.mp
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := R) (B := B)
        (I := maximalIdeal R)).symm.surjective.subsingleton)
  -- hence `(0, 1) ∈ 𝔪(A × B)`
  have hprod : ((0 : A), (1 : B)) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R) := by
    let J : Ideal B :=
      { carrier := {b : B | ((0 : A), b) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R)}
        add_mem' := by
          intro x y hx hy
          have hx' : ((0 : A), x) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R) := hx
          have hy' : ((0 : A), y) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R) := hy
          show ((0 : A), x + y) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R)
          rw [show ((0 : A), x + y) = ((0 : A), x) + ((0 : A), y) from by ext <;> simp]
          exact add_mem hx' hy'
        zero_mem' := by
          show ((0 : A), (0 : B)) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R)
          rw [show ((0 : A), (0 : B)) = 0 from rfl]
          exact zero_mem _
        smul_mem' := by
          intro c x hx
          have hx' : ((0 : A), x) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R) := hx
          show ((0 : A), c • x) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R)
          rw [show ((0 : A), c • x) = ((0 : A), c) * ((0 : A), x) from by
            ext <;> simp [smul_eq_mul]]
          exact Ideal.mul_mem_left _ _ hx' }
    have hle : Ideal.map (algebraMap R B) (maximalIdeal R) ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      show ((0 : A), algebraMap R B r) ∈ Ideal.map (algebraMap R (A × B)) (maximalIdeal R)
      rw [show ((0 : A), algebraMap R B r)
          = ((0 : A), (1 : B)) * algebraMap R (A × B) r from by ext <;> simp]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr)
    exact hle (hBtop.ge Submodule.mem_top)
  -- the idempotent `ε` cutting out `A` is congruent to `1` modulo `𝔪`
  set ε : AdjoinRoot f := e.symm ((1 : A), (0 : B)) with hε
  have hsplit : (e.symm : (A × B) →+* AdjoinRoot f) ((0 : A), (1 : B)) = 1 - ε := by
    rw [hε, eq_sub_iff_add_eq,
      show ((e.symm : (A × B) →+* AdjoinRoot f)) ((0 : A), (1 : B)) + e.symm ((1 : A), (0 : B))
        = e.symm (((0 : A), (1 : B)) + ((1 : A), (0 : B))) from (map_add e.symm _ _).symm,
      show ((0 : A), (1 : B)) + ((1 : A), (0 : B)) = 1 from by ext <;> simp]
    exact map_one e.symm
  have hcomp : ((e.symm : (A × B) →+* AdjoinRoot f).comp (algebraMap R (A × B)))
      = algebraMap R (AdjoinRoot f) := by
    ext r; exact e.symm.commutes r
  have hmem : (1 : AdjoinRoot f) - ε
      ∈ Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) := by
    have h := Ideal.mem_map_of_mem (e.symm : (A × B) →+* AdjoinRoot f) hprod
    rw [Ideal.map_map, hcomp] at h
    rw [← hsplit]
    exact h
  -- lift the idempotent to a polynomial congruent to `1` modulo `𝔪`
  have hmapC : Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R)
      = Ideal.map (AdjoinRoot.mk f) (Ideal.map (Polynomial.C : R →+* R[X]) (maximalIdeal R)) := by
    rw [Ideal.map_map, AdjoinRoot.algebraMap_eq]
    rfl
  obtain ⟨G₀, hG₀⟩ := AdjoinRoot.mk_surjective (g := f) ε
  rw [hmapC] at hmem
  obtain ⟨w, hw, hwmk⟩ :=
    (Ideal.mem_map_iff_of_surjective (AdjoinRoot.mk f) AdjoinRoot.mk_surjective).mp hmem
  obtain ⟨q, hq⟩ : f ∣ (1 - G₀ - w) := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_sub, hwmk, hG₀, map_one]
    ring
  have hGv : AdjoinRoot.mk f (G₀ + q * f) = ε := by
    rw [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, hG₀]
  refine ⟨A, hcA, haA, hAfin, π, G₀ + q * f, G₀ + q * f, hπsurj, ?_, by simp, ?_⟩
  · have hkerle : Ideal.map (Polynomial.C : R →+* R[X]) (maximalIdeal R)
        ≤ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, Polynomial.coe_mapRingHom, Polynomial.map_C]
      rw [show residue R r = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
    have hw0 : w.map (residue R) = 0 := hkerle hw
    have hveq : (1 : R[X]) - (G₀ + q * f) = w := by linear_combination hq
    have h2 := congrArg (fun p : R[X] => p.map (residue R)) hveq
    simp only [Polynomial.map_sub, Polynomial.map_one, hw0] at h2
    linear_combination -h2
  · intro p hp
    have hp' : (e (AdjoinRoot.mk f p)).1 = 0 := hp
    rw [← AdjoinRoot.mk_eq_zero, map_mul, hGv]
    apply e.injective
    rw [map_mul, map_zero, hε, e.apply_symm_apply]
    ext
    · simpa using hp'
    · simp

/-- **Weierstrass-type preparation over a henselian local ring.** Let `f ∈ R[T]` be a polynomial
whose reduction `f̄ ∈ κ[T]` is monic, of degree `n` say. Then `f = gw` with `g` monic of degree
`n`, `ḡ = f̄` and `w̄ = 1`.

The hypothesis says that the coefficient `a_n` of `f` is a unit and that `a_i ∈ 𝔪` for `i > n`,
which is the form "the coefficients of `f` generate the unit ideal" takes over a local ring; the
conclusion splits off the part of `Spec R[T]/(f)` which is finite over `R`, the complementary
factor `w` being invertible modulo `𝔪` and so having empty fibre over the closed point.

This is the one step of 04GG that the monic items do not reach. It is not degree bookkeeping on a
lift: over `R = k[ε]/(ε²)` the polynomial `f = εT³ + εT² + T` has `f̄ = T`, and its preparation
`f = T · (εT² + εT + 1)` cannot be assembled from linear factors, `εT² + εT + 1` having none —
so the excess degree `deg f - deg f̄` cannot be peeled off one root at a time by item (2). Nor can
`f` be made monic by a substitution: for `κ = 𝔽₂` and `f` of degree `3` with `f̄ = T(T + 1)` the
binary form `XY(X + Y)` attached to `f̄` vanishes at every point of `P¹(𝔽₂)`, so every
`GL₂(R)`-substitute of `f` again has both outer coefficients in `𝔪`.

The proof splits the source's argument into an existence half and a uniqueness half.

*Existence.* `exists_module_finite_of_map_monic` provides the finite factor `A` of `S = R[T]/(f)`
carrying the closed fibre. In `A` the image `y` of `T` satisfies `f(y) = 0`, whose degree-`n`
coefficient is a unit and whose higher ones lie in `𝔪`; so `y^n` lies in the span of
`1, …, y^{n-1}` modulo `𝔪A`, hence so does every power of `y`, hence — `π` being surjective — every
element of `A`. Nakayama's Lemma 00DV then makes `1, …, y^{n-1}` an `R`-module generating set, and
expanding `y^n` in it gives a *monic* `g` of degree `n` with `g(y) = 0`.

*Uniqueness.* The remainder `r = f mod g` has degree `< n` and vanishes at `y`, so `f ∣ rG` for the
idempotent lift `G`; since `G ≡ v` modulo `f` with `v̄ = 1`, also `f ∣ rv`, and
`eq_zero_of_mul_eq_mul_of_degree_lt` forces `r = 0`. So `f = g · (f /ₘ g)`, and comparing degrees
and leading coefficients in `κ[T]` — where `f̄` and `ḡ` are both monic of degree `n` — gives
`(f /ₘ g)‾ = 1` and `ḡ = f̄`.

The source instead deduces the rank of `A` from the flatness of `S` over `R` (its Lemma 046Z) and
runs the characteristic polynomial of `T : A → A` through Cayley–Hamilton. Neither is needed: what
the rank is for is to know that a polynomial of degree `< n` killing `y` vanishes, and that is
`eq_zero_of_mul_eq_mul_of_degree_lt`, an elementary Nakayama argument on the coefficients which
needs no flatness — nor, therefore, that `S` be quasi-finite. -/
private theorem exists_monic_mul_map_eq_one (h1 : Item1 R) (f : R[X])
    (hf : (f.map (residue R)).Monic) :
    ∃ g w : R[X], f = g * w ∧ g.Monic ∧ g.map (residue R) = f.map (residue R) ∧
      w.map (residue R) = 1 := by
  classical
  obtain ⟨n, hn⟩ : ∃ k : ℕ, (f.map (residue R)).natDegree = k := ⟨_, rfl⟩
  have hfu : IsUnit (f.coeff n) := hn ▸ isUnit_coeff_natDegree_of_map_monic hf
  have hfm : ∀ i, n < i → f.coeff i ∈ maximalIdeal R := by
    intro i hi
    have h0 : (f.map (residue R)).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.coeff_map] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  obtain ⟨A, hcA, haA, hfinA, π, G, v, hπ, hv, hGv, hker⟩ :=
    exists_module_finite_of_map_monic R h1 f hf
  let _ := hcA
  let _ := haA
  let _ := hfinA
  set y : A := π (AdjoinRoot.root f) with hy
  have hσ : ∀ p : R[X], aeval y p = π (AdjoinRoot.mk f p) := fun p => by
    rw [hy, Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq]
  have hfy : aeval y f = 0 := by rw [hσ, AdjoinRoot.mk_self, map_zero]
  -- the powers below `n` generate `A` modulo `𝔪A`, hence generate `A`
  set V : Submodule R A := Submodule.span R (Set.range fun i : Fin n => y ^ (i : ℕ)) with hV
  set W : Submodule R A := V ⊔ (maximalIdeal R) • (⊤ : Submodule R A) with hW
  have hpowV : ∀ i : ℕ, i < n → y ^ i ∈ V := fun i hi => by
    rw [hV]; exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hyn : y ^ n ∈ W := by
    have hsum : ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i • y ^ i = 0 := by
      rwa [← Polynomial.aeval_eq_sum_range]
    have hmemn : n ∈ Finset.range (f.natDegree + 1) := by
      have hle := Polynomial.natDegree_map_le (f := residue R) (p := f)
      simp only [Finset.mem_range]
      omega
    rw [← Finset.sum_erase_add _ (fun i => f.coeff i • y ^ i) hmemn] at hsum
    have hrest : ∑ i ∈ (Finset.range (f.natDegree + 1)).erase n, f.coeff i • y ^ i ∈ W := by
      refine Submodule.sum_mem _ fun i hi => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h2 | h2
      · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (hpowV i h2))
      · exact Submodule.mem_sup_right (Submodule.smul_mem_smul (hfm i h2) Submodule.mem_top)
    have hcoef : f.coeff n • y ^ n ∈ W := by
      rw [eq_neg_of_add_eq_zero_right hsum]
      exact neg_mem hrest
    have hfin := Submodule.smul_mem W (↑hfu.unit⁻¹ : R) hcoef
    rwa [smul_smul, hfu.val_inv_mul, one_smul] at hfin
  have hyW : ∀ x ∈ W, y * x ∈ W := by
    intro x hx
    rw [hW, Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [mul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [hV] at ha
      refine Submodule.span_induction (p := fun z _ => y * z ∈ W) ?_ ?_ ?_ ?_ ha
      · rintro z ⟨i, rfl⟩
        have hstep : y * y ^ (i : ℕ) = y ^ ((i : ℕ) + 1) := by ring
        rcases lt_or_ge ((i : ℕ) + 1) n with h2 | h2
        · rw [hstep]; exact Submodule.mem_sup_left (hpowV _ h2)
        · have h3 : (i : ℕ) + 1 = n := by have := i.isLt; omega
          rw [hstep, h3]; exact hyn
      · simp
      · intro z z' _ _ h1 h2
        rw [mul_add]; exact Submodule.add_mem _ h1 h2
      · intro c z _ h1
        rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h1
    · refine Submodule.mem_sup_right ?_
      rw [Ideal.smul_top_eq_map] at hb ⊢
      exact Ideal.mul_mem_left _ _ hb
  have hpowW : ∀ k : ℕ, y ^ k ∈ W := by
    intro k
    induction k with
    | zero =>
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · rw [h0] at hyn; simpa using hyn
        · simpa using le_sup_left (a := V) (hpowV 0 h0)
    | succ k ih =>
        have hstep : y ^ (k + 1) = y * y ^ k := by ring
        rw [hstep]
        exact hyW _ ih
  have hAW : ∀ x : A, x ∈ W := by
    intro x
    obtain ⟨z, rfl⟩ := hπ x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [← hσ]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
    | monomial k c =>
        rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (hpowW k)
  have hVtop : V = ⊤ := by
    refine eq_top_of_sup_smul_top R V fun x => ?_
    rw [← hW]
    exact hAW x
  obtain ⟨c, hc⟩ : ∃ c : Fin n → R, ∑ i, c i • y ^ (i : ℕ) = y ^ n := by
    have hmem : y ^ n ∈ V := by rw [hVtop]; exact Submodule.mem_top
    rw [hV, Submodule.mem_span_range_iff_exists_fun] at hmem
    exact hmem
  -- the monic polynomial of degree `n` killing `y`
  set p : R[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ) with hpdef
  have hpcoeff : ∀ k, n ≤ k → p.coeff k = 0 := by
    intro k hk
    rw [hpdef, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : (i : ℕ) < n := i.isLt
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (by omega), mul_zero]
  set g : R[X] := X ^ n - p with hgdef
  have hgnat : g.natDegree ≤ n :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by
      rw [hgdef, Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right (by omega),
        hpcoeff k (by omega), sub_zero]
  have hgcoeff : g.coeff n = 1 := by
    rw [hgdef, Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_left rfl, hpcoeff _ le_rfl,
      sub_zero]
  have hgmonic : g.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hgnat hgcoeff
  have hgnat' : g.natDegree = n :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hgnat (by rw [hgcoeff]; exact one_ne_zero)
  have hgdeg : g.degree = (n : ℕ) := by
    rw [Polynomial.degree_eq_natDegree hgmonic.ne_zero, hgnat']
  have hgy : aeval y g = 0 := by
    have hterm : ∀ i : Fin n, (aeval y) (C (c i) * X ^ (i : ℕ)) = c i • y ^ (i : ℕ) := by
      intro i; simp [Algebra.smul_def]
    rw [hgdef, map_sub, map_pow, Polynomial.aeval_X, hpdef, map_sum]
    simp only [hterm]
    rw [hc, sub_self]
  -- the remainder of `f` by `g` vanishes at `y`, hence vanishes
  have hrdeg : (f %ₘ g).degree < (n : ℕ) := by
    rw [← hgdeg]; exact Polynomial.degree_modByMonic_lt f hgmonic
  have hry : aeval y (f %ₘ g) = 0 := by
    have h2 := congrArg (aeval y) (Polynomial.modByMonic_add_div f g)
    rwa [map_add, map_mul, hgy, zero_mul, add_zero, hfy] at h2
  have hr0 : f %ₘ g = 0 := by
    have hdvd : f ∣ (f %ₘ g) * v := by
      rw [show (f %ₘ g) * v = (f %ₘ g) * G - (f %ₘ g) * (G - v) by ring]
      exact dvd_sub (hker _ (by rwa [← hσ])) (Dvd.dvd.mul_left hGv _)
    obtain ⟨q, hq⟩ := hdvd
    exact eq_zero_of_mul_eq_mul_of_degree_lt R hfu hfm hv hrdeg hq.symm
  have hfgh : f = g * (f /ₘ g) := by
    have h1 := Polynomial.modByMonic_add_div f g
    rw [hr0, zero_add] at h1
    exact h1.symm
  -- the two reductions
  have hmapmul : f.map (residue R) = g.map (residue R) * (f /ₘ g).map (residue R) := by
    rw [← Polynomial.map_mul, ← hfgh]
  have hgmap : (g.map (residue R)).Monic := hgmonic.map _
  have hwne : (f /ₘ g).map (residue R) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmapmul
    exact hf.ne_zero hmapmul
  have hwdeg : ((f /ₘ g).map (residue R)).natDegree = 0 := by
    have h1 : (f.map (residue R)).natDegree
        = (g.map (residue R)).natDegree + ((f /ₘ g).map (residue R)).natDegree := by
      rw [hmapmul, Polynomial.natDegree_mul hgmap.ne_zero hwne]
    rw [hn, hgmonic.natDegree_map, hgnat'] at h1
    omega
  have hwmap : (f /ₘ g).map (residue R) = 1 := by
    have hlc : ((f /ₘ g).map (residue R)).leadingCoeff = 1 := by
      have h2 : (f.map (residue R)).leadingCoeff
          = (g.map (residue R)).leadingCoeff * ((f /ₘ g).map (residue R)).leadingCoeff := by
        rw [hmapmul, Polynomial.leadingCoeff_mul]
      rw [hf.leadingCoeff, hgmap.leadingCoeff, one_mul] at h2
      exact h2.symm
    have h3 := Polynomial.eq_C_of_natDegree_eq_zero hwdeg
    rw [Polynomial.leadingCoeff, hwdeg] at hlc
    rw [h3, hlc, Polynomial.C_1]
  exact ⟨g, f /ₘ g, hfgh, hgmonic, by rw [hmapmul, hwmap, mul_one], hwmap⟩

/-- 1 ⇒ 6. Assume (1). By `item6_of_monic` it suffices to lift a coprime factorisation
`f̄ = g₀h₀` with `g₀` monic. If `h₀ = 0` then `g₀` is a monic unit, hence `1`, and `f = 1 · f` will
do. Otherwise rescale by a unit `u ∈ R` lifting the leading coefficient `c` of `h₀`, so that
`c⁻¹f̄ = g₀ · (h₀c⁻¹)` is a factorisation into monic polynomials; then

* `exists_monic_mul_map_eq_one` prepares `C u⁻¹ f = P · w` with `P` monic, `P̄ = c⁻¹f̄`, `w̄ = 1`,
  and
* `exists_monic_mul_map_eq_of_isCoprime` splits the monic `P` as `P = g · h₁` along the coprime
  monic factorisation `P̄ = g₀ · (h₀c⁻¹)`.

Then `f = g · (C u · h₁ · w)`, the second factor reducing to `c · (h₀c⁻¹) · 1 = h₀`, and
`deg g = deg g₀` because `g` is monic with `ḡ = g₀`. -/
@[ega "IV 18.5.13" "partial"]
private theorem item1_imp_item6 : Item1 R → Item6 R := by
  intro h1
  have h8 : Item8 R := item1_imp_item8 R h1
  refine item6_of_monic R ?_
  intro f g₀ h₀ hg₀ hfac hcop
  rcases eq_or_ne h₀ 0 with rfl | hh₀
  · rw [mul_zero] at hfac
    obtain ⟨c, -, hgc⟩ := Polynomial.isUnit_iff.mp (isCoprime_zero_right.mp hcop)
    have hg₀' : (C c).Monic := by rw [hgc]; exact hg₀
    have hg1 : g₀ = 1 := by
      rw [← hgc, (Polynomial.leadingCoeff_C c).symm.trans hg₀'.leadingCoeff, map_one]
    exact ⟨1, f, (one_mul f).symm, by rw [Polynomial.map_one, hg1], by rw [hfac],
      by simp [hg1]⟩
  · set c := h₀.leadingCoeff with hcdef
    have hc0 : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hh₀
    obtain ⟨u, hu⟩ : ∃ u : R, residue R u = c := Ideal.Quotient.mk_surjective c
    have hunit : IsUnit u := by rw [← residue_ne_zero_iff_isUnit, hu]; exact hc0
    have hvu : (↑hunit.unit⁻¹ : R) * u = 1 := hunit.val_inv_mul
    have hvres : residue R (↑hunit.unit⁻¹ : R) = c⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← hu, ← map_mul, hvu, map_one])
    have hcc : C c * C c⁻¹ = (1 : (ResidueField R)[X]) := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hc0, Polynomial.C_1]
    have hh₀m : (h₀ * C c⁻¹).Monic := Polynomial.monic_mul_leadingCoeff_inv hh₀
    have hcop' : IsCoprime g₀ (h₀ * C c⁻¹) := by
      obtain ⟨x, y, hxy⟩ := hcop
      refine ⟨x, y * C c, ?_⟩
      rw [show x * g₀ + y * C c * (h₀ * C c⁻¹) = x * g₀ + y * h₀ * (C c * C c⁻¹) by ring, hcc,
        mul_one]
      exact hxy
    have hf₁ : (C (↑hunit.unit⁻¹ : R) * f).map (residue R) = g₀ * (h₀ * C c⁻¹) := by
      rw [Polynomial.map_mul, Polynomial.map_C, hvres, hfac]
      ring
    obtain ⟨P, w, hPw, hPm, hPred, hwred⟩ :=
      exists_monic_mul_map_eq_one R h1 (C (↑hunit.unit⁻¹ : R) * f)
        (by rw [hf₁]; exact hg₀.mul hh₀m)
    obtain ⟨g, h₁, hgm, hPgh, hgred, hh₁red⟩ :=
      exists_monic_mul_map_eq_of_isCoprime R h8 P hPm g₀ (h₀ * C c⁻¹) hg₀ hh₀m
        (by rw [hPred, hf₁]) hcop'
    refine ⟨g, C u * (h₁ * w), ?_, hgred, ?_, ?_⟩
    · calc f = C u * (C (↑hunit.unit⁻¹ : R) * f) := by
            rw [← mul_assoc, ← Polynomial.C_mul, mul_comm u (↑hunit.unit⁻¹ : R), hvu,
              Polynomial.C_1, one_mul]
        _ = C u * (P * w) := by rw [hPw]
        _ = C u * ((g * h₁) * w) := by rw [hPgh]
        _ = g * (C u * (h₁ * w)) := by ring
    · calc (C u * (h₁ * w)).map (residue R) = C c * ((h₀ * C c⁻¹) * 1) := by
            rw [Polynomial.map_mul, Polynomial.map_C, hu, Polynomial.map_mul, hh₁red, hwred]
        _ = h₀ := by
            rw [mul_one, show C c * (h₀ * C c⁻¹) = h₀ * (C c * C c⁻¹) by ring, hcc, mul_one]
    · rw [← hgm.degree_map (residue R), hgred]
/-! ### The equivalence of the thirteen conditions -/

public theorem solution :
    List.TFAE
      [HenselianLocalRing R,
       ∀ f : R[X], ∀ a₀ : ResidueField R, aeval a₀ f = 0 → aeval a₀ (derivative f) ≠ 0 →
         ∃ a : R, f.IsRoot a ∧ residue R a = a₀,
       ∀ f : R[X], f.Monic → ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀,
       ∀ f : R[X], f.Monic → ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
           g.degree = g₀.degree,
       ∀ f : R[X], ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀,
       ∀ f : R[X], ∀ g₀ h₀ : (ResidueField R)[X], g₀ ≠ 0 → f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
           g.degree = g₀.degree,
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.Etale R S →
         ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
         Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
           (q.over_def _)) → Nonempty (S →ₐ[R] R),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.Etale R S →
         ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
         Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
           (q.over_def _)) → ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap (τ : S →+* R) = q,
       ∀ (S : Type u) [CommRing S] [Algebra R S], Module.Finite R S →
         ∃ (ι : Type u) (A : ι → Type u) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsLocalRing (A i)),
           Nonempty (S ≃+* ∀ i, A i),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Module.Finite R S →
         ∃ (ι : Type u) (_ : Finite ι) (A : ι → Type u) (_ : ∀ i, CommRing (A i))
           (_ : ∀ i, IsLocalRing (A i)), Nonempty (S ≃+* ∀ i, A i),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
         ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
           (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
           ∀ q : Ideal B, ∀ [q.IsPrime], q.LiesOver (maximalIdeal R) →
             ¬ Algebra.QuasiFiniteAt R q,
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
         ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
           (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
           ∀ p ∈ minimalPrimes (ResidueField R ⊗[R] B),
             1 ≤ ringKrullDim ((ResidueField R ⊗[R] B) ⧸ p),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
         Algebra.QuasiFinite R S →
         ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
           (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
           Subsingleton (ResidueField R ⊗[R] B)] := by
  tfae_have 1 → 8 := item1_imp_item8 R
  tfae_have 8 → 7 := item8_imp_item7 R
  tfae_have 7 → 1 := item7_imp_item1 R
  tfae_have 1 → 2 := item1_imp_item2 R
  tfae_have 2 → 1 := item2_imp_item1 R
  tfae_have 1 → 10 := item1_imp_item10 R
  tfae_have 10 → 9 := item10_imp_item9 R
  tfae_have 9 → 1 := item9_imp_item1 R
  tfae_have 1 → 11 := item1_imp_item11 R
  tfae_have 11 → 12 := item11_imp_item12 R
  tfae_have 12 → 13 := item12_imp_item13 R
  tfae_have 11 → 13 := item11_imp_item13 R
  tfae_have 13 → 1 := item13_imp_item1 R
  tfae_have 1 → 6 := item1_imp_item6 R
  tfae_have 6 → 5 := item6_imp_item5 R
  tfae_have 5 → 3 := item5_imp_item3 R
  tfae_have 3 → 1 := item3_imp_item1 R
  tfae_have 6 → 4 := item6_imp_item4 R
  tfae_have 4 → 3 := item4_imp_item3 R
  tfae_finish

end Stacks.Henselian.Characterizations

/-! ### The statement of Tag 04GG -/

open Polynomial IsLocalRing TensorProduct in
/-- **Characterisations of henselian local rings** (Stacks 04GG). For a local ring `(R, 𝔪, κ)`
the following are equivalent: (1) `R` is henselian; (2) every `f ∈ R[T]` and every root `a₀ ∈ κ`
of `f̄` with `f̄'(a₀) ≠ 0` come from a root `a ∈ R` of `f` with `ā = a₀`; (3) every coprime
factorisation `f̄ = g₀h₀` of the reduction of a monic `f ∈ R[T]` lifts to `f = gh` in `R[T]`;
(4) the same with `deg g = deg g₀`; (5), (6) the same two statements for arbitrary `f ∈ R[T]`,
(6) under the source's tacit `g₀ ≠ 0`;
(7) every étale `R`-algebra `S` with a prime `q` over `𝔪` such that `κ = κ(q)` admits a
retraction `S → R`; (8) it admits a unique retraction `τ` with `τ⁻¹(𝔪) = q`; (9) every finite
`R`-algebra is a product of local rings; (10) a finite product of local rings; (11) every finite
type `R`-algebra is `A × B` with `A` finite over `R` and `B` quasi-finite over `R` at no prime
over `𝔪`; (12) the same with each irreducible component of `Spec(κ ⊗_R B)` of dimension `≥ 1`;
(13) every quasi-finite `R`-algebra is `A × B` with `A` finite over `R` and `κ ⊗_R B = 0`. -/
@[stacks 04GG "The thirteen items are the entries, in the source's order, of one `List.TFAE`.
`f̄` is `Polynomial.map (IsLocalRing.residue R) f`, `gcd(g₀, h₀) = 1` is `IsCoprime`, degrees are
`Polynomial.degree` and item (6) carries the source's tacit `g₀ ≠ 0`, without which it holds only
for fields. A retraction is an element of `S →ₐ[R] R`, `κ = κ(q)` is bijectivity of
the canonical `Ideal.ResidueField.mapₐ`. A product of local rings is a `RingEquiv` onto a
`Pi` type; the two-factor decompositions of (11)–(13) are `AlgEquiv`s. The source's quasi-finite
of Definition 00PM is `Algebra.FiniteType` together with Mathlib's weaker `Algebra.QuasiFinite`.
See the module docstring.",
  sga "4 VIII 4.1" "(i)–(iv)",
  ega "IV 18.5.13" "a'') existence half",
  ega "IV 18.5.9" "(ii)", ega "IV 18.5.11" "a), a'), b)"]
public theorem HenselianLocalRing.TFAE_factorization_etale_quasiFinite
    (R : Type u) [CommRing R] [IsLocalRing R] :
    List.TFAE
      [HenselianLocalRing R,
       ∀ f : R[X], ∀ a₀ : ResidueField R, aeval a₀ f = 0 → aeval a₀ (derivative f) ≠ 0 →
         ∃ a : R, f.IsRoot a ∧ residue R a = a₀,
       ∀ f : R[X], f.Monic → ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀,
       ∀ f : R[X], f.Monic → ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
           g.degree = g₀.degree,
       ∀ f : R[X], ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀,
       ∀ f : R[X], ∀ g₀ h₀ : (ResidueField R)[X], g₀ ≠ 0 → f.map (residue R) = g₀ * h₀ →
         IsCoprime g₀ h₀ →
         ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
           g.degree = g₀.degree,
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.Etale R S →
         ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
         Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
           (q.over_def _)) → Nonempty (S →ₐ[R] R),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.Etale R S →
         ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
         Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
           (q.over_def _)) → ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap (τ : S →+* R) = q,
       ∀ (S : Type u) [CommRing S] [Algebra R S], Module.Finite R S →
         ∃ (ι : Type u) (A : ι → Type u) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsLocalRing (A i)),
           Nonempty (S ≃+* ∀ i, A i),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Module.Finite R S →
         ∃ (ι : Type u) (_ : Finite ι) (A : ι → Type u) (_ : ∀ i, CommRing (A i))
           (_ : ∀ i, IsLocalRing (A i)), Nonempty (S ≃+* ∀ i, A i),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
         ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
           (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
           ∀ q : Ideal B, ∀ [q.IsPrime], q.LiesOver (maximalIdeal R) →
             ¬ Algebra.QuasiFiniteAt R q,
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
         ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
           (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
           ∀ p ∈ minimalPrimes (ResidueField R ⊗[R] B),
             1 ≤ ringKrullDim ((ResidueField R ⊗[R] B) ⧸ p),
       ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
         Algebra.QuasiFinite R S →
         ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
           (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
           Subsingleton (ResidueField R ⊗[R] B)] :=
  Stacks.Henselian.Characterizations.solution R
