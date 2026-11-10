module

public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Strict henselianity from roots of standard étale polynomials

Two algebraic steps of the proof of Stacks 04KL, recovering a morphism of algebraic spaces from a
morphism of their small étale ringed topoi.

The first is a criterion for strict henselianity: a local ring `R` is strictly henselian as soon
as every monic `f ∈ R[X]` has a root `a` with `(g f')(a)` a unit, for every `g` such that the
image of `g f'` in `κ[X]/(f̄)` is not nilpotent, where `κ` is the residue field.  These are the
pairs `(f, g)` for which `R[X]_{g f'}/(f)` is a standard étale `R`-algebra with nonzero fibre over
the closed point, so the criterion says that a local ring all of whose standard étale algebras
with nonzero closed fibre have a section is strictly henselian.

The second makes the condition "the image of `e` in `K[X]/(f)` is not nilpotent" uniform in the
field `K`: for a monic `f ∈ A[X]` and `e ∈ A[X]` there are finitely many elements of `A` such
that, for every homomorphism `ψ : A → K` to a field, the image of `e` in `K[X]/(ψ f)` is not
nilpotent exactly when `ψ` does not kill all of them.  They are the non-leading coefficients of
the characteristic polynomial of multiplication by `e` on the free `A`-module `A[X]/(f)`.

The third is the fibrewise criterion for the image of `Spec` of a standard étale algebra
`A[X]_g/(f)`: a prime `p` of `A` is in the image as soon as `g` is not nilpotent in
`κ(p)[X]/(f)`.  A prime of `κ(p)[X]/(f)` avoiding `g` gives a homomorphism from `A[X]_g/(f)` to
a field restricting to `A → κ(p)`, whose kernel lies over `p`.

## Main results

* `strictlyHenselianLocalRing_of_exists_root`: the criterion for strict henselianity.
* `AdjoinRoot.exists_coeffs_not_isNilpotent_iff`: the uniform description of non-nilpotence.
* `StandardEtalePair.exists_comap_eq_of_not_isNilpotent`: a prime `p` of `A` lies under a prime
  of the standard étale algebra `A[X]_g/(f)` as soon as `g` is not nilpotent in `κ(p)[X]/(f)`;
  `StandardEtalePair.comap_surjective_of_not_isNilpotent` is the consequence for the map of
  spectra.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04GL](https://stacks.math.columbia.edu/tag/04GL)
-/

@[expose] public section

open Polynomial IsLocalRing

universe u

/-- If `p(0) = 0` and the image of `q` in `K[X]/(p)` is nilpotent, then `q(0) = 0`: evaluation
at `0` factors through `K[X]/(p)`. -/
theorem AdjoinRoot.eval_zero_eq_zero_of_isNilpotent {K : Type u} [Field K] {p q : K[X]}
    (hp : p.eval 0 = 0) (hq : IsNilpotent (AdjoinRoot.mk p q)) : q.eval 0 = 0 := by
  obtain ⟨n, hn⟩ := hq
  rw [← map_pow, AdjoinRoot.mk_eq_zero] at hn
  obtain ⟨r, hr⟩ := hn
  have h : (q.eval 0) ^ n = 0 := by rw [← eval_pow, hr, eval_mul, hp, zero_mul]
  exact (pow_eq_zero_iff' |>.mp h).1

/-- **A local ring is henselian and has a separably closed residue field as soon as standard
étale algebras with nonzero closed fibre have roots.** Let `R` be a local ring with residue
field `κ` such that, for all `f g ∈ R[X]` with `f` monic and the image of `g f'` in `κ[X]/(f̄)`
not nilpotent, `f` has a root `a ∈ R` with `(g f')(a)` a unit.  Then `R` is strictly henselian.

Henselian: for `p` monic with `p(a₀) ∈ 𝔪` and `p'(a₀)` a unit, write
`F(X) = p(X + a₀) = F(0) + X H(X)`.  Then `F̄(0) = 0` and `H̄(0) = F̄'(0)` is nonzero, so `H̄ F̄'`
does not vanish at `0` and is not nilpotent modulo `F̄`; a root `a` of `F` with `H(a)` a unit
lies in `𝔪`, and `a + a₀` is the required root of `p`.  Separably closed: a monic separable
irreducible polynomial over `κ` lifts to a monic `f ∈ R[X]`; with `g = 1` the image of `f̄'` in
`κ[X]/(f̄)` is a unit of a nonzero ring, and a root of `f` reduces to a root of `f̄`. -/
theorem strictlyHenselianLocalRing_of_exists_root {R : Type u} [CommRing R] [IsLocalRing R]
    (h : ∀ f g : R[X], f.Monic →
      ¬ IsNilpotent (AdjoinRoot.mk (f.map (residue R))
        ((g * derivative f).map (residue R))) →
      ∃ a : R, f.eval a = 0 ∧ IsUnit ((g * derivative f).eval a)) :
    StrictlyHenselianLocalRing R := by
  have hen : HenselianLocalRing R := by
    refine ⟨fun p hp a₀ h₁ h₂ ↦ ?_⟩
    set F : R[X] := p.comp (X + C a₀) with hF
    obtain ⟨H, hH⟩ : X ∣ F - C (F.coeff 0) := X_dvd_sub_C
    have hFeq : F = C (F.coeff 0) + X * H := by rw [← hH]; ring
    have hF0 : F.eval 0 = p.eval a₀ := by simp [hF]
    have hF'0 : (derivative F).eval 0 = (derivative p).eval a₀ := by
      simp [hF, derivative_comp]
    have hH0 : H.eval 0 = (derivative p).eval a₀ := by
      rw [← hF'0]
      conv_rhs => rw [hFeq]
      simp
    have hFa : ∀ a, F.eval a = F.eval 0 + a * H.eval a := by
      intro a
      conv_lhs => rw [hFeq]
      simp [coeff_zero_eq_eval_zero]
    obtain ⟨a, ha, hu⟩ := h F H (hp.comp_X_add_C a₀) (by
      intro hnil
      have hz := AdjoinRoot.eval_zero_eq_zero_of_isNilpotent (by
        rw [eval_zero_map, hF0, residue_eq_zero_iff]
        exact h₁) hnil
      rw [eval_zero_map, residue_eq_zero_iff, eval_mul, hH0, hF'0] at hz
      exact (mem_maximalIdeal _).mp hz (h₂.mul h₂))
    have hHa : IsUnit (H.eval a) := isUnit_of_mul_isUnit_left (by rwa [eval_mul] at hu)
    have hamem : a ∈ maximalIdeal R := by
      refine (Ideal.mul_unit_mem_iff_mem _ hHa).mp ?_
      have h0 : a * H.eval a = -F.eval 0 := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm, ← hFa, ha]
      rw [h0, hF0]; exact neg_mem h₁
    refine ⟨a + a₀, ?_, by rwa [add_sub_cancel_right]⟩
    have : F.eval a = p.eval (a + a₀) := by simp [hF]
    rw [IsRoot.def, ← this, ha]
  refine { toHenselianLocalRing := hen, toIsSepClosed := ?_ }
  refine IsSepClosed.of_exists_root _ fun p hpm hirr hsep ↦ ?_
  obtain ⟨f, hfmap, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective residue_surjective p) hpm
  have hdeg : p.degree ≠ 0 := (degree_pos_of_irreducible hirr).ne'
  have : Nontrivial (AdjoinRoot p) := AdjoinRoot.nontrivial p hdeg
  obtain ⟨a, ha, -⟩ := h f 1 hfm (by
    rw [one_mul, ← derivative_map, hfmap]
    obtain ⟨u, v, huv⟩ := hsep
    refine IsUnit.not_isNilpotent (IsUnit.of_mul_eq_one (AdjoinRoot.mk p v) ?_)
    rw [← map_mul, ← map_one (AdjoinRoot.mk p), AdjoinRoot.mk_eq_mk]
    exact ⟨-u, by linear_combination huv⟩)
  refine ⟨residue R a, ?_⟩
  rw [← hfmap, eval_map_apply, ha, map_zero]

namespace AdjoinRoot

/-- A square matrix over a field is nilpotent exactly when its characteristic polynomial is
`X ^ n`. -/
@[sga "3 XIV 2.13" "special case"]
theorem _root_.Matrix.isNilpotent_iff_charpoly_eq_X_pow {K : Type u} [Field K] {n : Type*}
    [Fintype n] [DecidableEq n] (M : Matrix n n K) :
    IsNilpotent M ↔ M.charpoly = X ^ Fintype.card n := by
  refine ⟨fun hM ↦ ?_, fun hM ↦ ⟨Fintype.card n, ?_⟩⟩
  · exact sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM).eq_zero
  · have := Matrix.aeval_self_charpoly M
    rwa [hM, map_pow, aeval_X] at this

/-- A monic polynomial of degree `n` over a field is `X ^ n` exactly when its coefficients below
degree `n` vanish. -/
theorem _root_.Polynomial.Monic.eq_X_pow_iff_coeff_eq_zero {K : Type u} [Field K] {n : ℕ}
    {P : K[X]} (hP : P.Monic) (hdeg : P.natDegree = n) :
    P = X ^ n ↔ ∀ i : Fin n, P.coeff i = 0 := by
  refine ⟨fun h i ↦ by rw [h, coeff_X_pow, ite_eq_right i.isLt.ne], fun h ↦ ?_⟩
  ext i
  rcases lt_trichotomy i n with hi | rfl | hi
  · rw [coeff_X_pow, ite_eq_right hi.ne]; exact h ⟨i, hi⟩
  · rw [coeff_X_pow_self, ← hdeg]; exact hP.coeff_natDegree
  · rw [coeff_X_pow, ite_eq_right hi.ne', coeff_eq_zero_of_natDegree_lt (hdeg ▸ hi)]

/-- The entries of the matrix of multiplication by `mk f e` in the power basis of `A[X]/(f)`: the
`(i, j)` entry is the `i`-th coefficient of `e X ^ j` reduced modulo `f`. -/
theorem leftMulMatrix_powerBasis'_apply {A : Type u} [CommRing A] {f : A[X]} (hf : f.Monic)
    (e : A[X]) (i j : Fin (powerBasis' hf).dim) :
    Algebra.leftMulMatrix (powerBasis' hf).basis (mk f e) i j =
      ((e * X ^ (j : ℕ)) %ₘ f).coeff i := by
  refine (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).trans ?_
  have hj : (powerBasis' hf).basis j = mk f (X ^ (j : ℕ)) := by
    rw [PowerBasis.coe_basis, powerBasis'_gen, map_pow, mk_X]
  rw [hj, ← map_mul]
  exact (powerBasisAux'_repr_apply_to_fun hf _ i).trans (by rw [modByMonicHom_mk])

/-- **The non-nilpotence of `e` modulo a monic `f` is cut out, uniformly in the field, by finitely
many elements.** For a monic `f ∈ A[X]` and `e ∈ A[X]` there are `c₀, …, c_{n-1} ∈ A` such that,
for every homomorphism `ψ : A → K` to a field, the image of `e` in `K[X]/(ψ f)` is not nilpotent
exactly when some `ψ cᵢ` is nonzero.

The `cᵢ` are the coefficients below the top degree of the characteristic polynomial of the matrix
of multiplication by `e` in the power basis of `A[X]/(f)`.  After `ψ` that matrix is the matrix of
multiplication by the image of `e` in the power basis of `K[X]/(ψ f)`, and over a field a matrix
is nilpotent exactly when its characteristic polynomial is a power of `X`. -/
theorem exists_coeffs_not_isNilpotent_iff {A : Type u} [CommRing A] (f e : A[X])
    (hf : f.Monic) :
    ∃ (n : ℕ) (c : Fin n → A), ∀ (K : Type u) [Field K] (ψ : A →+* K),
      ¬ IsNilpotent (AdjoinRoot.mk (f.map ψ) (e.map ψ)) ↔ ∃ i, ψ (c i) ≠ 0 := by
  set M := Algebra.leftMulMatrix (powerBasis' hf).basis (mk f e)
  refine ⟨f.natDegree, fun i ↦ M.charpoly.coeff i, fun K _ ψ ↦ ?_⟩
  have hfψ : (f.map ψ).Monic := hf.map ψ
  have hdeg : (f.map ψ).natDegree = f.natDegree := hf.natDegree_map ψ
  set b := (powerBasis' hfψ).basis.reindex
    (finCongr (show (powerBasis' hfψ).dim = (powerBasis' hf).dim from hdeg))
  have hM : Algebra.leftMulMatrix b (mk (f.map ψ) (e.map ψ)) = M.map ψ := by
    ext i j
    refine (Algebra.leftMulMatrix_eq_repr_mul b _ i j).trans (Eq.trans ?_
      (congrArg ψ (leftMulMatrix_powerBasis'_apply hf e i j)).symm)
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
    refine ((Algebra.leftMulMatrix_eq_repr_mul _ _ _ _).symm.trans
      (leftMulMatrix_powerBasis'_apply hfψ _ _ _)).trans ?_
    rw [← coeff_map, map_modByMonic ψ hf, Polynomial.map_mul, Polynomial.map_pow, map_X]
    rfl
  rw [← not_forall_not, not_iff_not]
  simp only [not_not]
  rw [← IsNilpotent.map_iff (Algebra.leftMulMatrix_injective b), hM,
    Matrix.isNilpotent_iff_charpoly_eq_X_pow, Fintype.card_fin,
    (M.map ψ).charpoly_monic.eq_X_pow_iff_coeff_eq_zero
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])]
  simp only [Matrix.charpoly_map, coeff_map]
  rfl

end AdjoinRoot

namespace StandardEtalePair

/-- **A prime lies under a prime of a standard étale algebra when the localized polynomial is
not nilpotent in its fibre.** Let `P = (f, g)` be a standard étale pair over `A` and `p` a prime
of `A` such that the image of `g` in `κ(p)[X]/(f)` is not nilpotent.  Then some prime of
`A[X]_g/(f)` lies over `p`.

A prime `m` of `B = κ(p)[X]/(f)` avoiding the image of `g` gives the homomorphism
`A[X]_g/(f) → κ(m)` sending `X` to the image of the root of `f`, and its kernel lies over the
kernel `p` of `A → κ(p) → κ(m)`. -/
theorem exists_comap_eq_of_not_isNilpotent {A : Type u} [CommRing A] (P : StandardEtalePair A)
    (p : Ideal A) [p.IsPrime]
    (h : ¬ IsNilpotent (AdjoinRoot.mk (P.f.map (algebraMap A p.ResidueField))
      (P.g.map (algebraMap A p.ResidueField)))) :
    ∃ q : Ideal P.Ring, q.IsPrime ∧ q.comap (algebraMap A P.Ring) = p := by
  set K := p.ResidueField
  set fK := P.f.map (algebraMap A K)
  set B := AdjoinRoot fK
  obtain ⟨m, hm, hgm⟩ :
      ∃ m : Ideal B, m.IsPrime ∧ AdjoinRoot.mk fK (P.g.map (algebraMap A K)) ∉ m := by
    by_contra! H
    exact h (nilpotent_iff_mem_prime.mpr H)
  set T := m.ResidueField
  set φ : A →+* T := (algebraMap B T).comp ((algebraMap K B).comp (algebraMap A K))
  let : Algebra A T := φ.toAlgebra
  set x : T := algebraMap B T (AdjoinRoot.root fK)
  have key : ∀ r : A[X],
      aeval x r = algebraMap B T (AdjoinRoot.mk fK (r.map (algebraMap A K))) := by
    intro r
    rw [aeval_def, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map, Polynomial.hom_eval₂]
    rfl
  have hx : P.HasMap x := by
    refine ⟨?_, ?_⟩
    · rw [key, AdjoinRoot.mk_self, map_zero]
    · rw [key]
      refine isUnit_iff_ne_zero.mpr ?_
      rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
  refine ⟨RingHom.ker (P.lift x hx), RingHom.ker_isPrime _, ?_⟩
  have hcomp : (P.lift x hx : P.Ring →+* T).comp (algebraMap A P.Ring) =
      ((algebraMap B T).comp (algebraMap K B)).comp (algebraMap A K) :=
    (P.lift x hx).comp_algebraMap
  change Ideal.comap _ (RingHom.ker (P.lift x hx : P.Ring →+* T)) = p
  rw [RingHom.comap_ker, hcomp, RingHom.ker_comp_of_injective _ (RingHom.injective _),
    Ideal.ker_algebraMap_residueField]

/-- The map `Spec A[X]_g/(f) → Spec A` of a standard étale pair is surjective as soon as `g` is
not nilpotent in `κ(p)[X]/(f)` for every prime `p` of `A`
(`StandardEtalePair.exists_comap_eq_of_not_isNilpotent`). -/
theorem comap_surjective_of_not_isNilpotent {A : Type u} [CommRing A] (P : StandardEtalePair A)
    (h : ∀ (p : Ideal A) [p.IsPrime],
      ¬ IsNilpotent (AdjoinRoot.mk (P.f.map (algebraMap A p.ResidueField))
        (P.g.map (algebraMap A p.ResidueField)))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A P.Ring)) := by
  intro p
  obtain ⟨q, hq, hqp⟩ := P.exists_comap_eq_of_not_isNilpotent p.asIdeal (h p.asIdeal)
  exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩

end StandardEtalePair

