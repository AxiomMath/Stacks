module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs

/-!
# The degree-one part of the quasi-regularity map

Let `R` be a commutative ring and let `g_1, …, g_c ∈ R` generate the ideal `J = (g_1, …, g_c)`.
The canonical map of graded modules
`Φ : (R/J)[X_1, …, X_c] ⊗_{R/J} (R/J) → ⨁_{n ≥ 0} J^n / J^{n+1}`
of `RingTheory.Sequence.quasiRegularCanonicalMap` is injective exactly when the sequence is
quasi-regular (it is always surjective). This file extracts the *degree-one* consequence of that
injectivity, which is the form in which quasi-regularity is used to compare two sets of local
generators of an ideal: a relation `∑ aᵢ gᵢ ∈ J²` forces every coefficient `aᵢ` to lie in `J`.

## Main definitions

* `RingTheory.Sequence.srcCoeff`: extraction of the coefficient of a monomial `X^e` from the
  source `(R/J)[X] ⊗_{R/J} (R/JR)` of the canonical map.

## Main results

* `RingTheory.Sequence.mem_Jid_of_sum_mul_mem_sq`: degree-one injectivity, stated for an
  injective canonical map.
* `RingTheory.Sequence.IsQuasiRegular.coeff_mem_Jid`: the same for a quasi-regular sequence
  `List.ofFn v`.
* `RingTheory.Sequence.exists_coeff_mem_of_mem_smul_Jid`: an element of `𝔪 · (v_1, …, v_c)` is a
  linear combination `∑ wⱼ vⱼ` with every `wⱼ ∈ 𝔪`.

## Implementation notes

Degree one is isolated without introducing a graded decomposition of the canonical map: the
element `ξ = ∑ᵢ Xᵢ ⊗ āᵢ` of the source is written as `∑ᵢ Xᵢ • (1 ⊗ āᵢ)`, so that
`canonicalMap_X_smul` and `tgtMul_lof` put its image in a *single* summand `J^{n+1}/J^{n+2}`
with `n = qrMdeg 0`. This avoids the dependent rewriting that `qrMdeg (Finsupp.single i 1) = 1`
would require, since the degree `qrMdeg 0 + 1` is then one and the same term for every `i`, and
the identification `qrMdeg 0 = 0` is only ever needed inside a `Prop`.

Coefficients are extracted from the source by `srcCoeff`, built from the monomial basis of
`MvPolynomial` rather than from a graded splitting.

`IsQuasiRegular` takes a `List R`, so `IsQuasiRegular.coeff_mem_Jid` reindexes along
`List.length_ofFn`; `Jid_getElem_ofFn` records that this does not change the generated ideal.

## References

* [Stacks Project, Tag 061P](https://stacks.math.columbia.edu/tag/061P), quasi-regular
  sequences, and [Tag 061N](https://stacks.math.columbia.edu/tag/061N), the canonical map.
-/

@[expose] public section

open RingTheory.Sequence

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] {c : ℕ}

/-- Extraction of the coefficient of the monomial `X^e` from the source of the canonical
quasi-regularity map. -/
noncomputable def srcCoeff (g : Fin c → R) (e : Fin c →₀ ℕ) :
    Source R g →ₗ[qrRbar g] qrMbar R g :=
  TensorProduct.lift
    ((LinearMap.lsmul (qrRbar g) (qrMbar R g)).comp
      ((MvPolynomial.basisMonomials (Fin c) (qrRbar g)).coord e))

/-- The coefficient of `X^e` in `X^{e'} ⊗ m̄` is `m̄` if `e' = e`, and `0` otherwise. -/
lemma srcCoeff_srcMono (g : Fin c → R) (e e' : Fin c →₀ ℕ) (m : R) :
    srcCoeff g e (srcMono g e' m)
      = (if e' = e then (1 : qrRbar g) else 0) • (Submodule.Quotient.mk m : qrMbar R g) := by
  simp only [srcCoeff, srcMono, TensorProduct.lift.tmul, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.lsmul_apply]
  congr 1
  rw [show (MvPolynomial.monomial e') (1 : qrRbar g)
      = (MvPolynomial.basisMonomials (Fin c) (qrRbar g)) e' from rfl,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- The zero multi-index has total degree `0`. -/
lemma qrMdeg_zero : qrMdeg (0 : Fin c →₀ ℕ) = 0 := by simp [qrMdeg]

/-- `g^0 = 1` for the zero multi-index. -/
lemma fpow_zero (g : Fin c → R) : fpow g 0 = 1 := by simp [fpow]

/-- The degree-zero monomial `X^0 ⊗ m̄` is `1 ⊗ m̄`. -/
lemma srcMono_zero (g : Fin c → R) (m : R) :
    srcMono g 0 m
      = (1 : MvPolynomial (Fin c) (qrRbar g)) ⊗ₜ[qrRbar g]
        (Submodule.Quotient.mk m : qrMbar R g) := by
  rw [srcMono, MvPolynomial.monomial_zero']
  rfl

/-- `Xᵢ • (1 ⊗ m̄) = Xᵢ ⊗ m̄` in the source of the canonical map. -/
lemma X_smul_srcMono_zero (g : Fin c → R) (i : Fin c) (m : R) :
    (MvPolynomial.X i : MvPolynomial (Fin c) (qrRbar g)) • srcMono g 0 m
      = srcMono g (Finsupp.single i 1) m := by
  rw [srcMono_zero, TensorProduct.smul_tmul', srcMono]
  congr 1
  rw [smul_eq_mul, mul_one, MvPolynomial.X]

/-- The canonical map sends `Xᵢ ⊗ m̄` to `tgtMul g i` applied to the image of `1 ⊗ m̄`. -/
lemma canonicalMap_srcMono_single (g : Fin c → R) (i : Fin c) (m : R) :
    quasiRegularCanonicalMap (M := R) g (srcMono g (Finsupp.single i 1) m)
      = tgtMul g i (quasiRegularCanonicalMap (M := R) g (srcMono g 0 m)) := by
  rw [← X_smul_srcMono_zero, canonicalMap_X_smul]

/-- For `M = R`, the submodule `J^k R` is the ideal `J^k`. -/
lemma mem_JpowM_iff (g : Fin c → R) (k : ℕ) (z : R) :
    z ∈ JpowM R g k ↔ z ∈ Jid g ^ k := by
  simp [JpowM]

/-- The class in `J^k / J^{k+1}` of an element of `J^{k+1}` is zero. -/
lemma tcomp_mk_eq_zero (g : Fin c → R) (k : ℕ) (z : JpowM R g k)
    (hz : (z : R) ∈ JpowM R g (k + 1)) :
    (Submodule.Quotient.mk z : Tcomp R g k) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact hz

/-- Taking classes in `J^k / J^{k+1}` commutes with finite sums. -/
lemma sum_tcomp_mk (g : Fin c → R) (k : ℕ) (y : Fin c → JpowM R g k) :
    ∑ j, (Submodule.Quotient.mk (y j) : Tcomp R g k)
      = Submodule.Quotient.mk (∑ j, y j) := by
  rw [← Submodule.mkQ_apply, map_sum]
  simp [Submodule.mkQ_apply]

/-- The canonical map sends `∑ⱼ Xⱼ ⊗ āⱼ` to the element of degree `qrMdeg 0 + 1` given by
`∑ⱼ tgtMulComp g j (qrMdeg 0) (imgClassLin g 0 (a j))`. -/
lemma canonicalMap_sum_single (g : Fin c → R) (a : Fin c → R) :
    quasiRegularCanonicalMap (M := R) g (∑ j, srcMono g (Finsupp.single j 1) (a j))
      = DirectSum.of (fun k => Tcomp R g k) (qrMdeg (0 : Fin c →₀ ℕ) + 1)
          (∑ j, tgtMulComp g j (qrMdeg (0 : Fin c →₀ ℕ)) (imgClassLin g 0 (a j))) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [canonicalMap_srcMono_single, canonicalMap_srcMono, imgTargetLin]
  rw [LinearMap.coe_comp, Function.comp_apply, DirectSum.lof_eq_of,
    ← DirectSum.lof_eq_of (R := qrRbar g), tgtMul_lof, tgtMulCompBar_coe, DirectSum.lof_eq_of]

/-- **Degree-one injectivity of the canonical quasi-regularity map.** If the canonical map of a
sequence `g₁, …, g_c` is injective (in particular if the sequence is quasi-regular) and
`∑ aᵢ gᵢ ∈ J²` for `J = (g₁, …, g_c)`, then every coefficient `aᵢ` lies in `J`. -/
theorem mem_Jid_of_sum_mul_mem_sq (g : Fin c → R)
    (h : Function.Injective (quasiRegularCanonicalMap (M := R) g))
    (a : Fin c → R) (hsum : ∑ j, a j * g j ∈ Jid g ^ 2) (i : Fin c) :
    a i ∈ Jid g := by
  have hzero : quasiRegularCanonicalMap (M := R) g
      (∑ j, srcMono g (Finsupp.single j 1) (a j)) = 0 := by
    rw [canonicalMap_sum_single]
    refine (congrArg _ ?_).trans (map_zero _)
    rw [show (fun j ↦ tgtMulComp g j (qrMdeg (0 : Fin c →₀ ℕ)) (imgClassLin g 0 (a j)))
        = fun j ↦ (Submodule.Quotient.mk
          (⟨g j * a j, by
            have : g j • ((fpow g (0 : Fin c →₀ ℕ)) • a j) ∈
                JpowM R g (qrMdeg (0 : Fin c →₀ ℕ) + 1) :=
              smul_mem_succ g j _ _ (fpow_smul_mem g 0 (a j))
            simpa [fpow_zero, smul_eq_mul] using this⟩ :
            JpowM R g (qrMdeg (0 : Fin c →₀ ℕ) + 1))) from ?_]
    · rw [sum_tcomp_mk]
      refine tcomp_mk_eq_zero g _ _ ?_
      rw [AddSubmonoidClass.coe_finsetSum]
      have h2 : qrMdeg (0 : Fin c →₀ ℕ) + 1 + 1 = 2 := by rw [qrMdeg_zero]
      rw [h2, mem_JpowM_iff]
      simpa only [mul_comm] using hsum
    · funext j
      rw [imgClassLin, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        tgtMulComp_mk]
      congr 1
      simp [fpowSmulRestrict, fpow_zero, smul_eq_mul]
  have hξ : (∑ j, srcMono g (Finsupp.single j 1) (a j)) = 0 := h (by rw [hzero, map_zero])
  have hcoeff := congrArg (srcCoeff g (Finsupp.single i 1)) hξ
  rw [map_sum, map_zero] at hcoeff
  rw [Finset.sum_congr rfl (fun j _ ↦ srcCoeff_srcMono g (Finsupp.single i 1)
    (Finsupp.single j 1) (a j))] at hcoeff
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by
    have hne : ¬ (Finsupp.single j (1 : ℕ) = Finsupp.single i 1) := fun hc ↦
      hji (Finsupp.single_left_injective one_ne_zero hc)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne), zero_smul])
    (fun hc ↦ absurd (Finset.mem_univ i) hc)] at hcoeff
  rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : Finsupp.single i (1 : ℕ) = Finsupp.single i 1)),
    one_smul] at hcoeff
  simpa using (Submodule.Quotient.mk_eq_zero _).mp hcoeff

omit [CommRing R] in
/-- The entries of `List.ofFn v` have the same range as `v`. -/
lemma range_getElem_ofFn (v : Fin c → R) :
    (Set.range fun i : Fin (List.ofFn v).length ↦ (List.ofFn v)[i]) = Set.range v := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast (List.length_ofFn ..) i, by simp [Fin.cast]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast (List.length_ofFn ..).symm j, by simp [Fin.cast]⟩

/-- The entries of `List.ofFn v` generate the same ideal as `v`. -/
lemma Jid_getElem_ofFn (v : Fin c → R) :
    Jid (fun i : Fin (List.ofFn v).length ↦ (List.ofFn v)[i]) = Jid v := by
  rw [Jid, Jid, range_getElem_ofFn]

/-- **Degree-one injectivity for a quasi-regular sequence.** If `v₁, …, v_c` is a quasi-regular
sequence and `∑ aⱼ vⱼ ∈ J²` for `J = (v₁, …, v_c)`, then every `aⱼ` lies in `J`. -/
theorem IsQuasiRegular.coeff_mem_Jid {v : Fin c → R}
    (h : IsQuasiRegular R (List.ofFn v)) (a : Fin c → R)
    (hsum : ∑ j, a j * v j ∈ Jid v ^ 2) (j : Fin c) : a j ∈ Jid v := by
  set v' : Fin (List.ofFn v).length → R := fun i ↦ (List.ofFn v)[i] with hv'
  have hlen : (List.ofFn v).length = c := List.length_ofFn ..
  have hJ : Jid v' = Jid v := Jid_getElem_ofFn v
  have hsum' : ∑ i, (a ∘ Fin.cast hlen) i * v' i = ∑ i, a i * v i := by
    refine Fintype.sum_bijective (Fin.cast hlen) (finCongr hlen).bijective _ _ fun i ↦ ?_
    simp [hv', Fin.cast]
  have hb : Function.Bijective (quasiRegularCanonicalMap (M := R) v') := h
  have hres := mem_Jid_of_sum_mul_mem_sq v' hb.injective (a ∘ Fin.cast hlen)
    (by rw [hsum', hJ]; exact hsum) (Fin.cast hlen.symm j)
  rw [hJ] at hres
  simpa [Fin.cast] using hres

/-- An element of `𝔪 · (v₁, …, v_c)` is a combination `∑ wⱼ vⱼ` with all coefficients in `𝔪`. -/
lemma exists_coeff_mem_of_mem_smul_Jid {v : Fin c → R} {m : Ideal R} {z : R}
    (hz : z ∈ m • Jid v) : ∃ w : Fin c → R, (∀ j, w j ∈ m) ∧ z = ∑ j, w j * v j := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro b hb y hy
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
    refine ⟨fun j ↦ b * cc j, fun j ↦ Ideal.mul_mem_right _ _ hb, ?_⟩
    simp [← hcc, Finset.mul_sum, mul_assoc]
  · rintro z₁ z₂ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    refine ⟨w₁ + w₂, fun j ↦ add_mem (hw₁ j) (hw₂ j), ?_⟩
    simp [← Finset.sum_add_distrib, add_mul]

end RingTheory.Sequence
