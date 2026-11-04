module

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
public import StacksFrontier.Algebra.Homology.FiniteFreeComplex

@[expose] public section

/-!
# An exact complex of finite free modules over an Artinian local ring splits

Let `R` be an Artinian local ring and let
`0 → R^{n_{e+1}} →[φ e] R^{n_e} → ⋯ → R^{n_1} →[φ 0] R^{n_0}`
be a complex of finite free `R`-modules which is exact at `R^{n_{e+1}}, …, R^{n_1}`. This file
proves that the complex is isomorphic to a direct sum of trivial complexes, in the normal form of
the statement: there are multiplicities `c j`, with `c (e+2) = 0`, and `R`-linear bijections
`R^{n_i} ≅ R^{c_i} × R^{c_{i+1}}` in the degrees `i ≤ e + 1` carrying each differential to
`(x, y) ↦ (0, x)`.

The source's proof is a single reduction: an Artinian local ring has depth `0`, so Lemma 00MY —
the same statement over a Noetherian local ring whose maximal ideal is an associated prime —
applies. Two things are added here.

First, depth `0`. Over an Artinian ring every prime ideal is maximal, and over a Noetherian
nonzero ring the set of associated primes of `R` is nonempty; over an Artinian local ring the
maximal ideal is therefore the only candidate, and so is an associated prime.

Second, the normal form. Lemma 00MY delivers the splitting as a degreewise change of basis after
which every differential is a *partial permutation matrix* (`IsPartialPerm`): entries `0` and `1`,
at most one `1` in each row and in each column. Reading a direct sum decomposition off such a
family is `exists_normalForm`, whose content is the degreewise splitting of the basis,
`bijective_sumElim_pivot`. Write `M i` for the differential out of degree `i + 1`, and call a
basis index of degree `i` *free* when its row of `M i` vanishes. Then the basis of degree `i`
consists, bijectively, of the free indices of degree `i` together with, for each free index `s` of
degree `i + 1`, the unique index `pivot s` with `M i (pivot s) s = 1`: injectivity is the
uniqueness of the `1` in a row of `M i`, and surjectivity says that an index `r` whose row does
not vanish is such a `pivot s` — the complex condition makes the `s` with `M i r s = 1` free
(`row_eq_zero_of_eq_one`) and the uniqueness of the `1` in the column `s` gives `pivot s = r`.
That there is a pivot for every free index at all is exactness
(`exists_eq_one_of_row_eq_zero`): a free `s` in degree `i + 1` lies in the kernel of `M i`, hence
in the image of `M (i + 1)`, which is impossible unless the column `s` of `M i` carries a `1`. So
in each degree the basis splits into the free indices, whose number is the multiplicity `c i`, and
the pivots of the free indices one degree up; that splitting is the required isomorphism.

## Main results

* `Stacks.Artinian.FreeComplexSplitting.solution`: the statement of tag 00MU.

## Implementation notes

The indexing convention of the statement (degree `i` names the *target* of `φ i`) leaves the ranks
`n j` for `j > e + 1` unconstrained, whereas Lemma 00MY is stated for a complex of a bounded
length. The bridge is the rank function `N i = if i ≤ e + 1 then n i else 0` together with the
degreewise map `ρ i : Fin (N i) → Fin (n i)`, `a ↦ a`, which is a bijection exactly in the degrees
`i ≤ e + 1` and has empty source above them; precomposition with `ρ` transports the differentials
into the bounded-length complex and, in the relevant degrees, transports the resulting splitting
back.

Exactness of the transported complex is recorded in *every* degree, not only in the degrees where
it is hypothesised: above the length of the complex the module in question is zero, so all its
submodules agree. This is what lets `exists_normalForm`, which knows nothing of a length, quantify
over all degrees.

## References

* [StackProject 00MU](https://stacks.math.columbia.edu/tag/00MU)
-/

namespace Stacks.Artinian.FreeComplexSplitting

section Helpers

open LinearMap

variable {R : Type*} [CommRing R]

/-- Over an Artinian local ring the maximal ideal is an associated prime of the ring, i.e. the
ring has depth `0`: the associated primes of a nonzero Noetherian ring are nonempty, and over an
Artinian ring a prime ideal is maximal, hence here equal to the maximal ideal. -/
private theorem maximalIdeal_mem_associatedPrimes [IsArtinianRing R] [IsLocalRing R] :
    IsLocalRing.maximalIdeal R ∈ associatedPrimes R R := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R R
  exact IsLocalRing.eq_maximalIdeal ((IsArtinianRing.isPrime_iff_isMaximal p).1 hp.1) ▸ hp

/-- **Exactness transports along a commuting ladder of bijective maps.** If `a`, `b`, `c` are
bijective with `f' ∘ b = a ∘ f` and `g' ∘ c = b ∘ g`, then `ker f = range g` gives
`ker f' = range g'`. -/
private theorem ker_eq_range_of_ladder {M₀ M₁ M₂ N₀ N₁ N₂ : Type*}
    [AddCommMonoid M₀] [Module R M₀] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₀] [Module R N₀]
    [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]
    {f : M₁ →ₗ[R] M₀} {g : M₂ →ₗ[R] M₁} {f' : N₁ →ₗ[R] N₀} {g' : N₂ →ₗ[R] N₁}
    {a : M₀ →ₗ[R] N₀} {b : M₁ →ₗ[R] N₁} {c : M₂ →ₗ[R] N₂}
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hc : Function.Bijective c)
    (h1 : f' ∘ₗ b = a ∘ₗ f) (h2 : g' ∘ₗ c = b ∘ₗ g) (h : ker f = range g) :
    ker f' = range g' :=
  LinearMap.exact_iff.1 (Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.ofBijective c hc) (e₂ := LinearEquiv.ofBijective b hb)
    (e₃ := LinearEquiv.ofBijective a ha) h2 h1 (LinearMap.exact_iff.2 h))

/-- Exactness is automatic at a module of rank `0`. -/
private theorem ker_eq_range_of_rank_eq_zero {a b k : ℕ} (hk : k = 0)
    (f : (Fin k → R) →ₗ[R] (Fin a → R)) (g : (Fin b → R) →ₗ[R] (Fin k → R)) : ker f = range g := by
  subst hk
  exact Subsingleton.elim _ _

/-! ### Partial permutation matrices

Throughout, `A` is thought of as the differential out of degree `1` and `B` as the differential
out of degree `2`, and a row index `r` of `A` with `A r = 0` is called *free*. -/

/-- A free row of `A` contributes nothing to `A *ᵥ v`. -/
private theorem mulVec_apply_of_row_eq_zero {a b : ℕ} {A : Matrix (Fin a) (Fin b) R} {r : Fin a}
    (hr : A r = 0) (v : Fin b → R) : A.mulVec v r = 0 := by
  simp [Matrix.mulVec, dotProduct, hr]

/-- Off the column of its `1`, a row of a partial permutation matrix vanishes. -/
private theorem eq_zero_of_ne_of_eq_one {a b : ℕ} {A : Matrix (Fin a) (Fin b) R} {r : Fin a}
    {s j : Fin b} (hA : IsPartialPerm A) (hrs : A r s = 1) (hj : j ≠ s) : A r j = 0 :=
  (hA.1 r j).resolve_right fun h1 => hj (hA.2.1 r j s h1 hrs)

/-- A row of a partial permutation matrix carrying a `1` in the column `s` reads off the
coordinate `s`: `(A *ᵥ v) r = v s`. -/
private theorem mulVec_apply_of_eq_one {a b : ℕ} {A : Matrix (Fin a) (Fin b) R}
    (hA : IsPartialPerm A) {r : Fin a} {s : Fin b} (hrs : A r s = 1) (v : Fin b → R) :
    A.mulVec v r = v s := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single s]
  · rw [hrs, one_mul]
  · intro j _ hj
    rw [eq_zero_of_ne_of_eq_one hA hrs hj, zero_mul]
  · simp

/-- **The complex condition on partial permutations.** If `A * B = 0` and the column `s` of the
partial permutation `A` carries a `1`, then the row `s` of `B` vanishes: a basis vector which is
the target of an identity block of `A` is not the source of one of `B`. -/
private theorem row_eq_zero_of_eq_one {a b c : ℕ} {A : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin c) R} (hA : IsPartialPerm A) (hAB : A * B = 0)
    {r : Fin a} {s : Fin b} (hrs : A r s = 1) : B s = 0 := by
  funext t
  have h := mulVec_apply_of_eq_one hA hrs fun j => B j t
  refine h.symm.trans ?_
  change (A * B) r t = 0
  rw [hAB]
  rfl

/-- **Exactness on partial permutations.** If `ker A = range B` and the row `s` of the partial
permutation `A`'s source is free, i.e. `B s = 0`, then the column `s` of `A` carries a `1`:
otherwise the basis vector `s` would lie in `ker A` but not in `range B`. -/
private theorem exists_eq_one_of_row_eq_zero {a b c : ℕ} [Nontrivial R]
    {A : Matrix (Fin a) (Fin b) R} {B : Matrix (Fin b) (Fin c) R} (hA : IsPartialPerm A)
    (hex : ker A.toLin' = range B.toLin') {s : Fin b} (hs : B s = 0) : ∃ r, A r s = 1 := by
  by_contra hcon
  have hmem : Pi.single s (1 : R) ∈ ker A.toLin' := by
    simp only [mem_ker, Matrix.toLin'_apply]
    funext r
    rw [Matrix.mulVec_single]
    simp [(hA.1 r s).resolve_right fun h => hcon ⟨r, h⟩]
  obtain ⟨w, hw⟩ := hex ▸ hmem
  rw [Matrix.toLin'_apply] at hw
  have hs1 := congrFun hw s
  rw [mulVec_apply_of_row_eq_zero hs] at hs1
  simp at hs1

/-- **The degreewise splitting of the basis.** For a partial permutation `A` with `A * B = 0` and
a choice `pivot s` of a `1` in the column of each free row `s` of `B`, the row indices of `A` are
exactly its own free rows together with the pivots of the free rows of `B`. This is the direct sum
decomposition of one degree of the complex: the free rows of `A` are the summands staying in this
degree, the pivots are the lower ends of the identity blocks coming from the degree above. -/
private theorem bijective_sumElim_pivot {a b c : ℕ} [Nontrivial R] {A : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin c) R} (hA : IsPartialPerm A) (hAB : A * B = 0)
    (pivot : {s : Fin b // B s = 0} → Fin a) (hpivot : ∀ s, A (pivot s) s.1 = 1) :
    Function.Bijective (Sum.elim (fun r : {r : Fin a // A r = 0} => r.1) pivot) := by
  constructor
  · rintro (k | k) (k' | k') hkk <;> simp only [Sum.elim_inl, Sum.elim_inr] at hkk
    · exact congrArg Sum.inl (Subtype.ext hkk)
    · exact absurd (hkk ▸ hpivot k') (by rw [congrFun k.2 k'.1]; exact zero_ne_one)
    · exact absurd (hkk ▸ hpivot k) (by rw [congrFun k'.2 k.1]; exact zero_ne_one)
    · exact congrArg Sum.inr (Subtype.ext (hA.2.1 _ _ _ (hkk ▸ hpivot k) (hpivot k')))
  · intro r
    by_cases h : A r = 0
    · exact ⟨Sum.inl ⟨r, h⟩, rfl⟩
    · obtain ⟨s, hs⟩ : ∃ s, A r s = 1 := by
        obtain ⟨s, hs⟩ := Function.ne_iff.1 h
        exact ⟨s, (hA.1 r s).resolve_left hs⟩
      exact ⟨Sum.inr ⟨s, row_eq_zero_of_eq_one hA hAB hs⟩,
        hA.2.2 _ _ _ (hpivot ⟨s, row_eq_zero_of_eq_one hA hAB hs⟩) hs⟩

/-- **Reading the direct sum of trivial complexes off a family of partial permutation matrices.**
Let `M i : Matrix (Fin (m i)) (Fin (m (i+1))) R` be a complex (`hcx`) of partial permutation
matrices (`hpp`) which is exact at every degree (`hex`). Then there are multiplicities `c` and
`R`-linear isomorphisms `R^{m i} ≅ R^{c i} × R^{c (i+1)}` carrying every differential to
`(x, y) ↦ (0, x)`; the multiplicity `c i` is the number of free rows of `M i`. -/
private theorem exists_normalForm [Nontrivial R] {m : ℕ → ℕ}
    (M : ∀ i, Matrix (Fin (m i)) (Fin (m (i + 1))) R) (hpp : ∀ i, IsPartialPerm (M i))
    (hcx : ∀ i, M i * M (i + 1) = 0)
    (hex : ∀ i, ker (M i).toLin' = range (M (i + 1)).toLin') :
    ∃ (c : ℕ → ℕ) (g : ∀ i, (Fin (m i) → R) ≃ₗ[R] ((Fin (c i) → R) × (Fin (c (i + 1)) → R))),
      (∀ i, m i = 0 → c i = 0) ∧
      ∀ i, (g i).toLinearMap ∘ₗ (M i).toLin'
          = LinearMap.inr R _ _ ∘ₗ LinearMap.fst R _ _ ∘ₗ (g (i + 1)).toLinearMap := by
  classical
  choose pivot hpivot using fun (i : ℕ) (s : {s : Fin (m (i + 1)) // M (i + 1) s = 0}) =>
    exists_eq_one_of_row_eq_zero (hpp i) (hex i) s.2
  set c : ℕ → ℕ := fun i => Nat.card {r : Fin (m i) // M i r = 0} with hc
  set eZ : ∀ i, {r : Fin (m i) // M i r = 0} ≃ Fin (c i) := fun i => Finite.equivFin _
  set ι : ∀ i, Fin (c i) ⊕ Fin (c (i + 1)) ≃ Fin (m i) := fun i =>
    (Equiv.sumCongr (eZ i).symm (eZ (i + 1)).symm).trans
      (Equiv.ofBijective _ (bijective_sumElim_pivot (hpp i) (hcx i) (pivot i) (hpivot i)))
  have hιl : ∀ i k, M i (ι i (Sum.inl k)) = 0 := fun i k => ((eZ i).symm k).2
  have hιr : ∀ i k, M i (ι i (Sum.inr k)) (ι (i + 1) (Sum.inl k)) = 1 := fun i k => hpivot i _
  refine ⟨c, fun i => (LinearEquiv.funCongrLeft R R (ι i)) ≪≫ₗ
      LinearEquiv.sumArrowLequivProdArrow _ _ R R, ?_, ?_⟩
  · intro i hi
    have : IsEmpty (Fin (m i)) := by rw [hi]; infer_instance
    simp [hc]
  · intro i
    refine LinearMap.ext fun v => Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact mulVec_apply_of_row_eq_zero (hιl i k) v
    · exact mulVec_apply_of_eq_one (hpp i) (hιr i k) v

/-- **Lemma 00MY as a family of partial permutation matrices in the original bases.** The change
of basis `ψ` of Lemma 00MY conjugates the differentials of an exact complex `C` over an Artinian
local ring into a family `M` of partial permutation matrices, again a complex, and exact in every
degree — beyond the length of `C` because there the module is zero. -/
private theorem exists_isPartialPerm_family [IsArtinianRing R] [IsLocalRing R]
    (C : BoundedFreeComplex R) (hC : C.Exact) :
    ∃ (M : ∀ i, Matrix (Fin (C.n i)) (Fin (C.n (i + 1))) R)
      (ψ : ∀ i, (Fin (C.n i) → R) →ₗ[R] (Fin (C.n i) → R)),
      (∀ i, IsPartialPerm (M i)) ∧ (∀ i, M i * M (i + 1) = 0) ∧
      (∀ i, ker (M i).toLin' = range (M (i + 1)).toLin') ∧
      (∀ i, Function.Bijective (ψ i)) ∧
      (∀ i, (M i).toLin' ∘ₗ ψ (i + 1) = ψ i ∘ₗ (C.φ i).toLin') := by
  obtain ⟨D, iso, -, -, hDtriv⟩ :=
    exists_trivial_iso_of_exact maximalIdeal_mem_associatedPrimes C hC
  have hbij : ∀ i, Function.Bijective (Matrix.toLin' ((iso.P i)⁻¹)) := fun i =>
    (Matrix.toLinearEquiv' _ (Matrix.invertibleOfIsUnitDet _
      (Matrix.isUnit_nonsing_inv_det _ (iso.unit i)))).bijective
  have hM : ∀ i, BoundedFreeComplex.transportφ C D iso.hn i
      = (iso.P i)⁻¹ * (C.φ i * iso.P (i + 1)) := fun i => by
    rw [← iso.comm i, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (iso.unit i), Matrix.one_mul]
  have hkey : ∀ i, BoundedFreeComplex.transportφ C D iso.hn i * (iso.P (i + 1))⁻¹
      = (iso.P i)⁻¹ * C.φ i := fun i => by
    rw [hM i, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (iso.unit (i + 1)),
      Matrix.mul_one]
  have hkeyLin : ∀ i, (BoundedFreeComplex.transportφ C D iso.hn i).toLin'
        ∘ₗ Matrix.toLin' ((iso.P (i + 1))⁻¹)
      = Matrix.toLin' ((iso.P i)⁻¹) ∘ₗ (C.φ i).toLin' := fun i => by
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hkey i]
  refine ⟨BoundedFreeComplex.transportφ C D iso.hn, fun i => Matrix.toLin' ((iso.P i)⁻¹),
    fun i => BoundedFreeComplex.isPartialPerm_submatrix (D.φ i) (finCongr (iso.hn i))
      (finCongr (iso.hn (i + 1))) (hDtriv i), fun i => ?_, fun i => ?_, hbij, hkeyLin⟩
  · calc BoundedFreeComplex.transportφ C D iso.hn i
          * BoundedFreeComplex.transportφ C D iso.hn (i + 1)
        = BoundedFreeComplex.transportφ C D iso.hn i * (iso.P (i + 1))⁻¹
            * (C.φ (i + 1) * iso.P (i + 2)) := by rw [hM (i + 1), Matrix.mul_assoc]
      _ = (iso.P i)⁻¹ * (C.φ i * C.φ (i + 1) * iso.P (i + 2)) := by
            rw [hkey i]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [C.isComplex i]; simp
  · by_cases hi : i ≤ C.e
    · exact ker_eq_range_of_ladder (hbij i) (hbij (i + 1)) (hbij (i + 2)) (hkeyLin i)
        (hkeyLin (i + 1)) (hC i hi)
    · exact ker_eq_range_of_rank_eq_zero (C.length (i + 1) (by omega)) _ _

/-- **Truncation of the ranks.** The family `φ` is transported, by precomposition with the
inclusions `Fin (N i) → Fin (n i)`, into a family of matrices `A` over ranks `N` vanishing above
degree `e + 1`; the transport `Θ` is bijective in the degrees `i ≤ e + 1`, intertwines `φ` with
`A` in the degrees `i ≤ e`, and `A` is a complex. -/
private theorem exists_truncation (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    ∃ (N : ℕ → ℕ) (Θ : ∀ i, (Fin (n i) → R) →ₗ[R] (Fin (N i) → R))
      (A : ∀ i, Matrix (Fin (N i)) (Fin (N (i + 1))) R),
      (∀ i, e + 1 < i → N i = 0) ∧ (∀ i ≤ e + 1, Function.Bijective (Θ i)) ∧
      (∀ i ≤ e, (A i).toLin' ∘ₗ Θ (i + 1) = Θ i ∘ₗ φ i) ∧ (∀ i, A i * A (i + 1) = 0) := by
  classical
  obtain ⟨N, hNeq, hNzero, hNle⟩ : ∃ N : ℕ → ℕ, (∀ i ≤ e + 1, N i = n i) ∧
      (∀ i, e + 1 < i → N i = 0) ∧ (∀ i, N i ≤ n i) :=
    ⟨fun i => if i ≤ e + 1 then n i else 0, fun i hi => by simp [hi],
      fun i hi => by simp [Nat.not_le_of_lt hi], fun i => by dsimp only; split <;> simp⟩
  have hρbij : ∀ i ≤ e + 1, Function.Bijective (Fin.castLE (hNle i)) := fun i hi =>
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨Fin.castLE_injective _, by simp [hNeq i hi]⟩
  -- the degreewise transport into the truncated ranks
  obtain ⟨Θ, hΘapp, hΘbij⟩ : ∃ Θ : ∀ i, (Fin (n i) → R) →ₗ[R] (Fin (N i) → R),
      (∀ i (v : Fin (n i) → R) (r : Fin (N i)), Θ i v r = v (Fin.castLE (hNle i) r)) ∧
      (∀ i ≤ e + 1, Function.Bijective (Θ i)) :=
    ⟨fun i => LinearMap.funLeft R R (Fin.castLE (hNle i)), fun _ _ _ => rfl,
      fun i hi => ⟨LinearMap.funLeft_injective_of_surjective R R _ (hρbij i hi).2,
        LinearMap.funLeft_surjective_of_injective R R _ (hρbij i hi).1⟩⟩
  -- the truncated complex, as a family of matrices
  obtain ⟨A, hAsq, hAcx⟩ : ∃ A : ∀ i, Matrix (Fin (N i)) (Fin (N (i + 1))) R,
      (∀ i ≤ e, (A i).toLin' ∘ₗ Θ (i + 1) = Θ i ∘ₗ φ i) ∧ (∀ i, A i * A (i + 1) = 0) := by
    refine ⟨fun i => (LinearMap.toMatrix' (φ i)).submatrix (Fin.castLE (hNle i))
        (Fin.castLE (hNle (i + 1))), fun i _ => LinearMap.ext fun v => funext fun r => ?_, ?_⟩
    · have hB : φ i v = (LinearMap.toMatrix' (φ i)).mulVec v := by
        rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
      simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hΘapp, hB, Matrix.mulVec,
        Matrix.submatrix_apply, dotProduct]
      exact Fintype.sum_bijective _ (hρbij (i + 1) (by omega)) _ _ fun _ => rfl
    · intro i
      dsimp only
      rcases lt_or_ge i e with h | h
      · rw [← Matrix.submatrix_mul _ _ _ _ _ (hρbij (i + 1) (by omega)),
          ← LinearMap.toMatrix'_comp, hφ i h]
        simp
      · have hz : N (i + 1 + 1) = 0 := hNzero _ (by omega)
        ext r s
        exact absurd s.2 (by omega)
  exact ⟨N, Θ, A, hNzero, hΘbij, hAsq, hAcx⟩

/-- **Lemma 00MY in the indexing of tag 00MU.** A complex of finite free modules over an Artinian
local ring which is exact at `R^{n_{e+1}}, …, R^{n_1}` is, after a degreewise change of basis, a
complex of partial permutation matrices: there are ranks `m` vanishing in degree `e + 2`, a family
of matrices `M` which is a complex, is exact at every degree and is a partial permutation in every
degree, and `R`-linear maps `θ i : R^{n_i} → R^{m_i}` intertwining `φ` with `M`, bijective in the
degrees `i ≤ e + 1`. -/
private theorem exists_partialPerm_model [IsArtinianRing R] [IsLocalRing R] (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (htop : Function.Injective (φ e))
    (hexφ : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∃ (m : ℕ → ℕ) (M : ∀ i, Matrix (Fin (m i)) (Fin (m (i + 1))) R)
      (θ : ∀ i, (Fin (n i) → R) →ₗ[R] (Fin (m i) → R)),
      (∀ i, IsPartialPerm (M i)) ∧ (∀ i, M i * M (i + 1) = 0) ∧
      (∀ i, ker (M i).toLin' = range (M (i + 1)).toLin') ∧
      m (e + 2) = 0 ∧ (∀ i ≤ e + 1, Function.Bijective (θ i)) ∧
      (∀ i ≤ e, θ i ∘ₗ φ i = (M i).toLin' ∘ₗ θ (i + 1)) := by
  obtain ⟨N, Θ, A, hNzero, hΘbij, hAsq, hAcx⟩ := exists_truncation e n φ hφ
  -- package it as a `BoundedFreeComplex` of length `e + 1`
  let C : BoundedFreeComplex R := ⟨e + 1, N, A, hNzero, hAcx⟩
  have hCsq : ∀ i ≤ e, (C.φ i).toLin' ∘ₗ Θ (i + 1) = Θ i ∘ₗ φ i := hAsq
  have hCex : C.Exact := by
    intro i hi
    rcases lt_trichotomy i e with h | h | h
    · exact ker_eq_range_of_ladder (hΘbij i (by omega)) (hΘbij (i + 1) (by omega))
        (hΘbij (i + 2) (by omega)) (hCsq i h.le) (hCsq (i + 1) (by omega))
        (LinearMap.exact_iff.mp (hexφ i h))
    · subst h
      have hinj : Function.Injective (C.φ i).toLin' := by
        refine Function.Injective.of_comp_right (g := Θ (i + 1)) ?_ (hΘbij (i + 1) (by omega)).2
        rw [← LinearMap.coe_comp, hCsq i le_rfl, LinearMap.coe_comp]
        exact (hΘbij i (by omega)).1.comp htop
      rw [LinearMap.ker_eq_bot.2 hinj,
        BoundedFreeComplex.range_eq_bot_of_zero_source (hNzero (i + 2) (by omega)) (C.φ (i + 1))]
    · exact ker_eq_range_of_rank_eq_zero (hNzero (i + 1) (by omega)) _ _
  obtain ⟨M, ψ, hpp, hcx, hexM, hψbij, hψsq⟩ := exists_isPartialPerm_family C hCex
  refine ⟨N, M, fun i => ψ i ∘ₗ Θ i, hpp, hcx, hexM, hNzero (e + 2) (by omega),
    fun i hi => (hψbij i).comp (hΘbij i hi), fun i hi => LinearMap.ext fun v => ?_⟩
  have h1 := LinearMap.congr_fun (hCsq i hi) v
  have h2 := LinearMap.congr_fun (hψsq i) (Θ (i + 1) v)
  simp only [LinearMap.comp_apply] at h1 h2 ⊢
  rw [← h1]
  exact h2.symm

end Helpers

/-- **An exact complex of finite free modules over an Artinian local ring is a direct sum of
trivial complexes** (tag 00MU). -/
public theorem solution {R : Type*} [CommRing R] [IsArtinianRing R] [IsLocalRing R] (e : ℕ)
    (n : ℕ → ℕ) (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (htop : Function.Injective (φ e))
    (hex : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∃ (c : ℕ → ℕ) (g : ∀ i, (Fin (n i) → R) →ₗ[R] ((Fin (c i) → R) × (Fin (c (i + 1)) → R))),
      c (e + 2) = 0 ∧ (∀ i ≤ e + 1, Function.Bijective (g i)) ∧
        (∀ i ≤ e, g i ∘ₗ φ i = LinearMap.inr R _ _ ∘ₗ LinearMap.fst R _ _ ∘ₗ g (i + 1)) := by
  obtain ⟨m, M, θ, hpp, hcx, hexM, hm, hθ, hsq⟩ :=
    exists_partialPerm_model e n φ hφ htop hex
  obtain ⟨c, g, hc0, hg⟩ := exists_normalForm M hpp hcx hexM
  refine ⟨c, fun i => (g i).toLinearMap ∘ₗ θ i, hc0 _ hm,
    fun i hi => (g i).bijective.comp (hθ i hi), fun i hi => ?_⟩
  rw [LinearMap.comp_assoc, hsq i hi, ← LinearMap.comp_assoc, hg i, LinearMap.comp_assoc,
    LinearMap.comp_assoc]

end Stacks.Artinian.FreeComplexSplitting

/-!
# An exact complex of finite free modules over an Artinian local ring splits

Let `R` be a ring and let
`0 → R^{n_{e+1}} →[φ e] R^{n_e} → ⋯ → R^{n_1} →[φ 0] R^{n_0}`
be a complex of finite free `R`-modules, that is `φ i ∘ φ (i + 1) = 0` throughout. A complex of
this shape is *trivial* when it is `0 → ⋯ → 0 → R →[1] R → 0 → ⋯ → 0`, the identity map placed in
two adjacent degrees `j` and `j - 1` with `1 ≤ j ≤ e + 1` and all other terms zero, or else
`0 → ⋯ → 0 → R`, a single copy of `R` in degree `0`. Over an Artinian local ring a complex as
above which is exact at `R^{n_{e+1}}, …, R^{n_1}` — everywhere except possibly at the last
term — is isomorphic to a direct sum of trivial complexes: after a change of bases every
differential is a block matrix of identity blocks and zeros.

## Main results

* `LinearMap.exists_trivialDecomposition_of_injective_of_exact`: a complex of finite free
  modules over an Artinian local ring which is exact away from its last term is isomorphic to a
  direct sum of trivial complexes.

## Implementation notes

The complex is a family of maps indexed by the *target* degree: `φ k : R^{n_{k+1}} → R^{n_k}`, so
`φ k` is the source's `φ_{k+1}` and the source's `e` is `e + 1` here. This is the convention of
the companion statement for the exactness criterion (tag 00N1), which lives in the same situation
(tag 00MS), and it keeps natural subtraction out of the types of the maps. A source complex of
length `e' < e + 1` is the instance with `n j = 0` for `j > e'`, so no length is lost by the
shift: padding a complex by zero modules changes neither its exactness nor its trivial summands.
The data are a family over all of `ℕ`, as a family over `Fin (e + 2)` would put the bound inside
the dependent types; only `n 0, …, n (e + 1)` and `φ 0, …, φ e` are mentioned, the remaining
values being unread junk.

Exactness of `0 → R^{n_{e+1}} → ⋯ → R^{n_0}` at `R^{n_{e+1}}, …, R^{n_1}` is spelled out as
`Function.Exact (φ (k + 1)) (φ k)` for `k < e`, which is exactness at the `e` terms
`R^{n_1}, …, R^{n_e}`, together with `Function.Injective (φ e)`, which is exactness at the top
term `R^{n_{e+1}}`, where the complex is preceded by `0`. Nothing is asked at `R^{n_0}`.

The complex condition `hφ` is the data of the situation (tag 00MS) and is stated in the same
spelling as in the companion statement 00N1, so that the two statements take an identical
situation and the
forward direction of 00N1 feeds this lemma verbatim. It is implied by `hex`, exactness of
`φ (k + 1)` at `φ k` giving `φ k ∘ φ (k + 1) = 0` for the same range `k < e`; it is therefore
redundant rather than restrictive, and dropping it would state the same theorem.

The conclusion is the direct sum of trivial complexes in normal form. Writing `T_j` for the
trivial complex with the identity in degrees `j` and `j - 1` (so `T_0` is `R` in degree `0`
alone), a direct sum `⨁_{j = 0}^{e+1} T_j^{c_j}` has degree-`i` term `R^{c_i} × R^{c_{i+1}}`, the
first factor collecting the upper ends of the `T_i` and the second the lower ends of the
`T_{i+1}`, and its differential out of degree `i + 1` is `(x, y) ↦ (0, x)`, that is
`inr ∘ fst`: it carries the upper end of each `T_{i+1}` by the identity to its lower end and
kills the lower ends of the `T_{i+2}`. So a family of `R`-linear bijections `g i` in the degrees
`i ≤ e + 1` intertwining `φ i` with `inr ∘ fst` is exactly an isomorphism onto such a direct sum,
and the multiplicities `c j` are the numbers of trivial summands of each kind. The conjunct
`c (e + 2) = 0` says that no summand sticks out above degree `e + 1`: a copy of `R` in degree
`e + 1` with zero differential is not a trivial complex of this length. The `g i` are total
linear maps, asserted bijective only for `i ≤ e + 1`, rather than equivalences carrying a proof
`i ≤ e + 1` in their type; their values in the junk degrees are unconstrained, as are the `c j`
for `j > e + 2`.

The hypothesis is `IsArtinianRing R` together with `IsLocalRing R`. The source obtains the lemma
from the depth-zero case (tag 00MY) because an Artinian local ring has depth `0`; the Noetherian
hypothesis of that lemma is free here, an Artinian ring being Noetherian.

Faithfulness. (1) No hypothesis is dead: `htop` and `hex` are the exactness at
`R^{n_{e+1}}, …, R^{n_1}` that drives the splitting off of identity blocks, and `IsArtinianRing R`
with `IsLocalRing R` is what supplies an element killed by the maximal ideal; over `R = ℤ` (local
it is not, Artinian it is not) the complex `0 → ℤ →[2] ℤ` is exact at its top term and has no
trivial summand at all, while `hφ` is the situation's complex condition, redundant as noted above
and restricting nothing.
(2) The scalars are the source's: the modules are the free `R`-modules `Fin (n i) → R`, the maps
are `R`-linear, and the isomorphisms of the conclusion are `R`-linear; no localization or
quotient appears.
(3) The source's canonical maps are pinned, not merely asserted to exist: the differential of the
trivial summand is the identity, spelled as `LinearMap.inr R _ _ ∘ₗ LinearMap.fst R _ _`, and not
an arbitrary isomorphism `R ≃ R`.
(4) The instantiation is not degenerate: with `e = 0`, `n 1 = n 0 = 1` and `φ 0 = id`, the
hypotheses hold and the conclusion is witnessed by `c 1 = 1`, `c 0 = c 2 = 0`, the complex being
the trivial complex `T_1` itself; with all `n i = 0` it is the empty sum, `c = 0`.

## References

* [StackProject 00MU](https://stacks.math.columbia.edu/tag/00MU)
* [WhatExact], D. A. Buchsbaum and D. Eisenbud, *What makes a complex exact?*
-/

/-- **An exact complex of finite free modules over an Artinian local ring is a direct sum of
trivial complexes.** Let `R` be an Artinian local ring and let
`0 → R^{n_{e+1}} →[φ e] R^{n_e} → ⋯ → R^{n_1} →[φ 0] R^{n_0}` be a complex of finite free
`R`-modules which is exact at `R^{n_{e+1}}, …, R^{n_1}`. Then there are multiplicities `c j` and
`R`-linear bijections `g i : R^{n_i} ≃ R^{c_i} × R^{c_{i+1}}` in the degrees `i ≤ e + 1`, with
`c (e + 2) = 0`, carrying each differential `φ i` to `(x, y) ↦ (0, x)`; that is, the complex is
isomorphic to the direct sum of `c_j` copies, for each `0 ≤ j ≤ e + 1`, of the trivial complex
with the identity map of `R` in degrees `j` and `j - 1`. -/
@[stacks 00MU]
public theorem LinearMap.exists_trivialDecomposition_of_injective_of_exact
    {R : Type*} [CommRing R] [IsArtinianRing R] [IsLocalRing R] (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (htop : Function.Injective (φ e))
    (hex : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∃ (c : ℕ → ℕ) (g : ∀ i, (Fin (n i) → R) →ₗ[R] ((Fin (c i) → R) × (Fin (c (i + 1)) → R))),
      c (e + 2) = 0 ∧ (∀ i ≤ e + 1, Function.Bijective (g i)) ∧
        (∀ i ≤ e, g i ∘ₗ φ i = LinearMap.inr R _ _ ∘ₗ LinearMap.fst R _ _ ∘ₗ g (i + 1)) :=
  Stacks.Artinian.FreeComplexSplitting.solution e n φ hφ htop hex
