module

public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusWeights

/-!
# Algebraicity of eigenvalues bounded under every complex embedding

The theorem of Deligne, [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), asserts that the
eigenvalues of the geometric Frobenius on `H^i_c(X_k̄, ℱ_ρ)`, a priori elements of `Q̄_ℓ`, are
algebraic numbers.  Its proof in Weil II obtains this from the weight bound itself: the bound
`|ι α| ≤ q ^ (i / 2)` holds for *every* field embedding `ι : Q̄_ℓ → ℂ`, because the hypotheses on
`ρ` (conclusion (2) of the preceding conjecture: all complex conjugates of the Frobenius
eigenvalues have absolute value `1`) do not depend on `ι`; and an element of `Q̄_ℓ` which is
bounded under every embedding into `ℂ` is algebraic, since a transcendental element can be sent to
any transcendental complex number.

This file proves that last step.

## Main results

* `Stacks.EtaleCohomology.exists_ringHom_complex_eq_of_transcendental`: if `L` is a field of
  characteristic zero of cardinality at most that of `ℂ`, `a ∈ L` is transcendental over `ℚ` and
  `z ∈ ℂ` is transcendental over `ℚ`, then some ring homomorphism `L →+* ℂ` sends `a` to `z`.
* `Stacks.EtaleCohomology.exists_transcendental_lt_norm`: there are transcendental complex
  numbers of arbitrarily large absolute value.
* `Stacks.EtaleCohomology.isAlgebraic_of_forall_norm_le`: an element of such an `L` whose images
  under all ring homomorphisms `L →+* ℂ` are bounded is algebraic over `ℚ`.
* `Stacks.EtaleCohomology.isAlgebraic_of_isRoot_map_of_forall_norm_le`: the same for the complex
  roots of a polynomial `P` over such a field `K` (the characteristic polynomial of the Frobenius
  on a `ℚ_ℓ`-vector space): if for every embedding `ι : K →+* ℂ` the roots of `P.map ι` are
  bounded by `R`, then every root of every `P.map ι` is an algebraic number.
* `Stacks.EtaleCohomology.IsCharpolyMixedOfWeightLE`: every complex root of the characteristic
  polynomial of `f` read along `ι` is a `q`-Weil number of some integer weight at most `i`; unlike
  `Stacks.EtaleCohomology.IsMixedOfWeightLE`, which only sees the eigenvalues lying in the
  coefficient field `K`, this sees all eigenvalues in `K̄`.
* `Stacks.EtaleCohomology.isCharpolyMixedOfWeightLE_of_forall_norm_eq`: if for every embedding
  `ι` every complex root of the characteristic polynomial along `ι` has absolute value
  `q ^ (w / 2)` for an integer `w ≤ i`, then the action is `IsCharpolyMixedOfWeightLE` along
  every `ι`: algebraicity comes for free.

## Implementation notes

The roots of `P.map ι` in `ℂ` are the images of the roots of `P` in an algebraic closure `K̄`
under an extension of `ι` to `K̄`; this is how the eigenvalues of an endomorphism of a
`ℚ_ℓ`-vector space, which lie in `Q̄_ℓ`, are read in `ℂ` throughout this chapter.  The
cardinality hypothesis `#K ≤ #ℂ` holds for `ℚ_ℓ` and for every finite extension of it.
-/

@[expose] public noncomputable section

open Cardinal Polynomial

namespace Stacks.EtaleCohomology

/-- A transcendental element of a field `L` of characteristic zero and cardinality at most `#ℂ` can
be sent to any prescribed transcendental complex number by a ring homomorphism `L →+* ℂ`. -/
public theorem exists_ringHom_complex_eq_of_transcendental {L : Type} [Field L] [CharZero L]
    (hL : #L ≤ #ℂ) {a : L} (ha : Transcendental ℚ a) {z : ℂ} (hz : Transcendental ℚ z) :
    ∃ ι : L →+* ℂ, ι a = z := by
  have hsa : AlgebraicIndepOn ℚ id ({a} : Set L) :=
    (algebraicIndependent_unique_type_iff (x := ((↑) : ({a} : Set L) → L))).2 ha
  obtain ⟨B, haB, hB⟩ := exists_isTranscendenceBasis_superset hsa
  have hsz : AlgebraicIndepOn ℚ id ({z} : Set ℂ) :=
    (algebraicIndependent_unique_type_iff (x := ((↑) : ({z} : Set ℂ) → ℂ))).2 hz
  obtain ⟨C, hzC, hC⟩ := exists_isTranscendenceBasis_superset hsz
  have haB' : a ∈ B := haB rfl
  have hzC' : z ∈ C := hzC rfl
  have hCcard : #C = #ℂ :=
    (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hC
      Cardinal.mk_le_aleph0 (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)).symm
  have hBC : #B ≤ #C := by
    rw [hCcard]
    exact (Cardinal.mk_set_le B).trans hL
  obtain ⟨g⟩ := hBC
  let e : B → C := fun b => Equiv.swap (g ⟨a, haB'⟩) ⟨z, hzC'⟩ (g b)
  have he : Function.Injective e := (Equiv.injective _).comp g.injective
  have hea : e ⟨a, haB'⟩ = ⟨z, hzC'⟩ := Equiv.swap_apply_left _ _
  let v : B → ℂ := ((↑) : C → ℂ) ∘ e
  have hv : AlgebraicIndependent ℚ v := hC.1.comp e he
  let A := Algebra.adjoin ℚ (Set.range ((↑) : B → L))
  let φ : A →ₐ[ℚ] ℂ := (MvPolynomial.aeval v).comp hB.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    show Function.Injective ((MvPolynomial.aeval v) ∘ hB.1.aevalEquiv.symm) from
    Function.Injective.comp (algebraicIndependent_iff_injective_aeval.1 hv)
      hB.1.aevalEquiv.symm.injective
  let : Algebra A ℂ := φ.toRingHom.toAlgebra
  have : Module.IsTorsionFree A ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  have : Algebra.IsAlgebraic A L := hB.isAlgebraic
  let ψ : L →ₐ[A] ℂ := IsAlgClosed.lift
  refine ⟨ψ.toRingHom, ?_⟩
  have hamem : a ∈ A := Algebra.subset_adjoin ⟨⟨a, haB'⟩, rfl⟩
  have h1 : (ψ.toRingHom : L →+* ℂ) a = φ ⟨a, hamem⟩ := ψ.commutes ⟨a, hamem⟩
  rw [h1]
  have h2 : hB.1.aevalEquiv.symm ⟨a, hamem⟩ = MvPolynomial.X ⟨a, haB'⟩ := by
    apply hB.1.aevalEquiv.injective
    rw [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [AlgebraicIndependent.aevalEquiv]
  show MvPolynomial.aeval v (hB.1.aevalEquiv.symm ⟨a, hamem⟩) = z
  rw [h2, MvPolynomial.aeval_X]
  simp [v, hea]

/-- There are transcendental complex numbers of arbitrarily large absolute value. -/
public theorem exists_transcendental_lt_norm (R : ℝ) : ∃ z : ℂ, Transcendental ℚ z ∧ R < ‖z‖ := by
  set R' := max R 0
  have hcount : ((fun t : ℝ => (t : ℂ)) ⁻¹' {x : ℂ | IsAlgebraic ℚ x}).Countable :=
    (Algebraic.countable ℚ ℂ).preimage Complex.ofReal_injective
  have hunc : ¬ (Set.Ioi R').Countable := by
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioi_real, not_le]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨t, ht, htalg⟩ : ∃ t ∈ Set.Ioi R', t ∉ (fun t : ℝ => (t : ℂ)) ⁻¹'
      {x : ℂ | IsAlgebraic ℚ x} := by
    by_contra h
    push Not at h
    exact hunc (hcount.mono h)
  refine ⟨t, htalg, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (le_max_left R 0).trans_lt ((Set.mem_Ioi.1 ht).trans_le (le_abs_self t))

/-- **Bounded under every embedding implies algebraic.**  An element of a field of
characteristic zero and cardinality at most `#ℂ` whose images under all ring homomorphisms into
`ℂ` are bounded in absolute value is algebraic over `ℚ`. -/
public theorem isAlgebraic_of_forall_norm_le {L : Type} [Field L] [CharZero L] (hL : #L ≤ #ℂ)
    {a : L} {R : ℝ} (h : ∀ ι : L →+* ℂ, ‖ι a‖ ≤ R) : IsAlgebraic ℚ a := by
  by_contra ha
  obtain ⟨z, hz, hRz⟩ := exists_transcendental_lt_norm R
  obtain ⟨ι, hι⟩ := exists_ringHom_complex_eq_of_transcendental hL ha hz
  exact absurd (h ι) (not_le.2 (hι ▸ hRz))

/-- **Algebraicity of the complex roots of a polynomial bounded under every embedding.**  Let
`K` be a field of characteristic zero with `#K ≤ #ℂ` (such as `ℚ_ℓ`) and `P ∈ K[X]`.  If for
every embedding `ι : K →+* ℂ` the complex roots of `P.map ι` have absolute value at most `R`,
then every complex root of every `P.map ι` is an algebraic number. -/
public theorem isAlgebraic_of_isRoot_map_of_forall_norm_le {K : Type} [Field K] [CharZero K]
    (hK : #K ≤ #ℂ) {P : K[X]} (hP : P ≠ 0) {R : ℝ}
    (h : ∀ (ι : K →+* ℂ) (z : ℂ), (P.map ι).IsRoot z → ‖z‖ ≤ R) (ι₀ : K →+* ℂ) {z : ℂ}
    (hz : (P.map ι₀).IsRoot z) : IsAlgebraic ℚ z := by
  let L := AlgebraicClosure K
  have hL : #L ≤ #ℂ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K L).trans (max_le hK (Cardinal.aleph0_le_mk ℂ))
  let : Algebra K ℂ := ι₀.toAlgebra
  let ι₀' : L →ₐ[K] ℂ := IsAlgClosed.lift
  have hι₀ : (ι₀'.toRingHom : L →+* ℂ).comp (algebraMap K L) = ι₀ := RingHom.ext ι₀'.commutes
  set Q := P.map (algebraMap K L)
  have hQ0 : Q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).2 hP
  have hroots : (Q.map (ι₀'.toRingHom : L →+* ℂ)).roots = Q.roots.map ι₀'.toRingHom :=
    (roots_map_of_injective_of_card_eq_natDegree (ι₀'.toRingHom : L →+* ℂ).injective
      (IsAlgClosed.splits Q).natDegree_eq_card_roots.symm).symm
  have hQmap : Q.map (ι₀'.toRingHom : L →+* ℂ) = P.map ι₀ := by
    rw [Polynomial.map_map, hι₀]
  have hzmem : z ∈ (Q.map (ι₀'.toRingHom : L →+* ℂ)).roots := by
    rw [hQmap, mem_roots (Polynomial.map_ne_zero_iff ι₀.injective |>.2 hP)]
    exact hz
  rw [hroots, Multiset.mem_map] at hzmem
  obtain ⟨β, hβ, rfl⟩ := hzmem
  have hβalg : IsAlgebraic ℚ β := by
    refine isAlgebraic_of_forall_norm_le hL (R := R) fun ι => h (ι.comp (algebraMap K L)) _ ?_
    rw [← Polynomial.map_map]
    exact ((mem_roots hQ0).1 hβ).map
  exact hβalg.algHom ι₀'.toRingHom.toRatAlgHom

/-! ### Weights of all the eigenvalues -/

section CharpolyWeights

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The endomorphism `f` is mixed of weight at most `i`, relative to `q` and to an embedding `ι` of
the coefficient field in `ℂ`: every complex root of its characteristic polynomial read along `ι` —
that is, the image of every eigenvalue of `f` in `K̄` under an extension of `ι` — is a `q`-Weil
number of some integer weight at most `i`. -/
public def IsCharpolyMixedOfWeightLE [FiniteDimensional K V] (q : ℕ) (ι : K →+* ℂ) (i : ℤ)
    (f : Module.End K V) : Prop :=
  ∀ z : ℂ, (f.charpoly.map ι).IsRoot z → ∃ w ≤ i, IsWeilNumber q w z

/-- Weights of all eigenvalues control the weights of the eigenvalues in `K`. -/
public theorem IsCharpolyMixedOfWeightLE.isMixedOfWeightLE [FiniteDimensional K V] {q : ℕ}
    {ι : K →+* ℂ} {i : ℤ} {f : Module.End K V} (h : IsCharpolyMixedOfWeightLE q ι i f) :
    IsMixedOfWeightLE q ι i f := fun α hα =>
  h (ι α) (((Module.End.hasEigenvalue_iff_isRoot_charpoly f α).1 hα).map (f := ι))

/-- **Weil numbers from bounds under every embedding.** Let `K` be a field of characteristic zero
with `#K ≤ #ℂ` (such as `ℚ_ℓ`), `1 ≤ q`, and `f` an endomorphism of a finite-dimensional `K`-vector
space. If for every embedding `ι : K →+* ℂ` each complex root of the characteristic polynomial of
`f` along `ι` has absolute value `q ^ (w / 2)` for some integer `w ≤ i`, then along every `ι` these
roots are `q`-Weil numbers. -/
public theorem isCharpolyMixedOfWeightLE_of_forall_norm_eq {K : Type} [Field K] [CharZero K]
    (hK : #K ≤ #ℂ) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {q : ℕ}
    (hq : 1 ≤ q) {i : ℤ} {f : Module.End K V}
    (h : ∀ (ι : K →+* ℂ) (z : ℂ), (f.charpoly.map ι).IsRoot z →
      ∃ w : ℤ, w ≤ i ∧ ‖z‖ = (q : ℝ) ^ ((w : ℝ) / 2))
    (ι : K →+* ℂ) : IsCharpolyMixedOfWeightLE q ι i f := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hbound : ∀ (ι : K →+* ℂ) (z : ℂ), (f.charpoly.map ι).IsRoot z →
      ‖z‖ ≤ (q : ℝ) ^ ((i : ℝ) / 2) := fun ι z hz => by
    obtain ⟨w, hw, hz⟩ := h ι z hz
    rw [hz]
    exact Real.rpow_le_rpow_of_exponent_le hq1
      (by linarith [show (w : ℝ) ≤ i by exact_mod_cast hw])
  intro z hz
  obtain ⟨w, hw, hnorm⟩ := h ι z hz
  exact ⟨w, hw, ⟨isAlgebraic_of_isRoot_map_of_forall_norm_le hK f.charpoly_monic.ne_zero
    hbound ι hz, hnorm⟩⟩

end CharpolyWeights

end Stacks.EtaleCohomology

end
