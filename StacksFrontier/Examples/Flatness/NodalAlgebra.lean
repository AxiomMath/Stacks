module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksCore.RingTheory.Spectrum.Prime.Fiber

/-!
# An affine nodal algebra with non-finite presentation

For a commutative ring `R` and an ideal `I` of `R`, the quotient
`R[x, y]/(xy, ay : a ∈ I)` is an `R`-algebra of finite type whose fibres are nodal affine
curves away from the vanishing locus of `I` and affine lines on it.

Its coefficientwise description is what makes it tractable: a polynomial lies in the
relation ideal exactly when each of its coefficients lies in the ideal `⊥`, `I` or `⊤`
according to whether the monomial is free of `y`, divisible by `y` but not by `x`, or
divisible by both. The quotient is therefore a direct sum of copies of `R`, `R ⧸ I` and `0`,
so it is flat as soon as `R ⧸ I` is. Evaluating `x` at `0` and `y` at `1` carries the
relation ideal onto `I`, so finite presentation of the algebra would make `I` finitely
generated. Taking `I` pure and not finitely generated — which is possible, by the example
of a finite flat nonprojective quotient — thus gives a flat algebra of finite type that is
not of finite presentation.

## Main definitions

* `Stacks.Examples.nodalRelationIdeal`: the ideal `(xy, ay : a ∈ I)` of `R[x, y]`.
* `Stacks.Examples.nodalAlgebra`: the quotient algebra `R[x, y]/(xy, ay : a ∈ I)`.

## Main results

* `Stacks.Examples.nodalAlgebra_flat`: the algebra is flat over `R` whenever `R ⧸ I` is.
* `Stacks.Examples.nodalAlgebra_not_finitePresentation`: it is not of finite presentation
  when `I` is not finitely generated.
* `Stacks.Examples.nodalAlgebra_fiber`: every fibre is either the node `k[x, y]/(xy)` or the
  affine line `k[x]`.

Finite type needs no separate statement: it is Mathlib's instance for a quotient of a
polynomial algebra in finitely many variables.

## Implementation notes

The fibre statement is phrased with algebra equivalences over the residue field rather than
unspecified ring isomorphisms. The flatness and non-presentation statements use only the
corresponding properties of `R ⧸ I` and of `I`; the fibre alternatives need neither.

## References

* [Stacks Project, Tag 05LC](https://stacks.math.columbia.edu/tag/05LC)
-/

@[expose] public section

namespace Stacks.Examples

universe u

open MvPolynomial
open scoped TensorProduct

/-- The ideal `(xy, ay : a ∈ I)` of the polynomial ring `R[x, y]`. -/
noncomputable def nodalRelationIdeal (R : Type u) [CommRing R] (I : Ideal R) :
    Ideal (MvPolynomial (Fin 2) R) :=
  Ideal.span (Set.insert
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
    (Set.range fun a : I =>
      MvPolynomial.C (a : R) * MvPolynomial.X (1 : Fin 2)))

/-- The affine algebra `R[x, y]/(xy, ay : a ∈ I)`. -/
abbrev nodalAlgebra (R : Type u) [CommRing R] (I : Ideal R) :=
  MvPolynomial (Fin 2) R ⧸ nodalRelationIdeal R I

/-- The polynomials whose coefficient in each degree `d` lies in `J d`, for a monotone
family of ideals `J`. Monotonicity is what makes this an ideal. -/
private def coefficientIdeal {σ R : Type*} [CommRing R]
    (J : (σ →₀ ℕ) → Ideal R) (hJ : Monotone J) : Ideal (MvPolynomial σ R) where
  carrier := {p | ∀ d, p.coeff d ∈ J d}
  zero_mem' := by simp
  add_mem' := fun hp hq d => by simpa using (J d).add_mem (hp d) (hq d)
  smul_mem' := by
    classical
    intro p q hq d
    change (p * q).coeff d ∈ J d
    rw [coeff_mul]
    apply Ideal.sum_mem
    intro ab hab
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    exact (J d).mul_mem_left _ (hJ (he ▸ le_add_left le_rfl) (hq ab.2))

/-- The family of coefficient ideals cutting out the nodal relation ideal: `⊥` in degrees
free of `y`, the ideal `I` in degrees divisible by `y` but not by `x`, and `⊤` in degrees
divisible by both. -/
private def nodalCoefficientIdeal {R : Type*} [CommRing R] (I : Ideal R)
    (d : Fin 2 →₀ ℕ) : Ideal R :=
  if d 1 = 0 then ⊥ else if d 0 = 0 then I else ⊤

/-- The family of nodal coefficient ideals is monotone in the degree. -/
private lemma nodalCoefficientIdeal_mono {R : Type*} [CommRing R] (I : Ideal R) :
    Monotone (nodalCoefficientIdeal I) := by
  intro d e h
  by_cases he1 : e 1 = 0
  · have hd1 : d 1 = 0 := Nat.eq_zero_of_le_zero (he1 ▸ h 1)
    simp [nodalCoefficientIdeal, he1, hd1]
  by_cases hd1 : d 1 = 0
  · simp [nodalCoefficientIdeal, hd1]
  by_cases he0 : e 0 = 0
  · have hd0 : d 0 = 0 := Nat.eq_zero_of_le_zero (he0 ▸ h 0)
    simp [nodalCoefficientIdeal, he1, hd1, he0, hd0]
  simp [nodalCoefficientIdeal, he1, hd1, he0]

/-- A monomial whose coefficient lies in the nodal coefficient ideal of its degree lies in
the nodal relation ideal. -/
private lemma monomial_mem_nodalRelationIdeal {R : Type*} [CommRing R] (I : Ideal R)
    (d : Fin 2 →₀ ℕ) (a : R) (ha : a ∈ nodalCoefficientIdeal I d) :
    monomial d a ∈ nodalRelationIdeal R I := by
  classical
  by_cases hy : d 1 = 0
  · have : a = 0 := by simpa [nodalCoefficientIdeal, hy] using ha
    simp [this]
  by_cases hx : d 0 = 0
  · have haI : a ∈ I := by simpa [nodalCoefficientIdeal, hy, hx] using ha
    have hd : Finsupp.single 1 1 ≤ d := by
      intro i
      by_cases hi : i = 1
      · subst i
        simp
        omega
      · simp [Finsupp.single_eq_of_ne hi]
    have hm := (nodalRelationIdeal R I).mul_mem_left (monomial (d - Finsupp.single 1 1) 1)
      (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨⟨a, haI⟩, rfl⟩))
    simpa [C_mul_X_eq_monomial, monomial_mul_monomial, tsub_add_cancel_of_le hd] using hm
  · have hd : Finsupp.single 0 1 + Finsupp.single 1 1 ≤ d := by
      intro i
      fin_cases i <;> simp <;> omega
    have hm := (nodalRelationIdeal R I).mul_mem_left
      (monomial (d - (Finsupp.single 0 1 + Finsupp.single 1 1)) a)
      (Ideal.subset_span (Set.mem_insert _ _))
    simpa [X, monomial_mul_monomial, tsub_add_cancel_of_le hd] using hm

/-- The nodal relation ideal is cut out coefficientwise by the nodal coefficient ideals. -/
private lemma nodalRelationIdeal_eq_coefficientIdeal {R : Type*} [CommRing R]
    (I : Ideal R) : nodalRelationIdeal R I =
      coefficientIdeal (nodalCoefficientIdeal I) (nodalCoefficientIdeal_mono I) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | ⟨a, rfl⟩
    · intro d
      change (X (0 : Fin 2) * X 1 : MvPolynomial (Fin 2) R).coeff d ∈ nodalCoefficientIdeal I d
      simp only [X, monomial_mul_monomial, one_mul, coeff_monomial]
      split_ifs with h
      · subst d; simp [nodalCoefficientIdeal]
      · exact Ideal.zero_mem _
    · intro d
      change (C (a : R) * X (1 : Fin 2) : MvPolynomial (Fin 2) R).coeff d ∈
        nodalCoefficientIdeal I d
      simp only [coeff_C_mul, coeff_X]
      split_ifs with h
      · subst d; simp [nodalCoefficientIdeal]
      · simp
  · intro p hp
    rw [← p.support_sum_monomial_coeff]
    exact Ideal.sum_mem _ fun d _ => monomial_mem_nodalRelationIdeal I d _ (hp d)

/-- Reading off the coefficients of a polynomial modulo a family of ideals. -/
private noncomputable def coefficientQuotientMap {σ R : Type*} [CommRing R]
    (J : (σ →₀ ℕ) → Ideal R) :
    MvPolynomial σ R →ₗ[R] Π₀ d, R ⧸ J d := by
  classical
  exact (DFinsupp.mapRange.linearMap fun d => (J d).mkQ).comp
    ((finsuppLequivDFinsupp R).toLinearMap.comp (basisMonomials σ R).repr.toLinearMap)

/-- The coefficientwise quotient map is surjective. -/
private lemma coefficientQuotientMap_surjective {σ R : Type*} [CommRing R]
    (J : (σ →₀ ℕ) → Ideal R) : Function.Surjective (coefficientQuotientMap J) := by
  classical
  have h : Function.Surjective (DFinsupp.mapRange.linearMap fun d => (J d).mkQ) :=
    (DFinsupp.mapRange_surjective _ (fun d => map_zero ((J d).mkQ))).mpr
      fun d => Submodule.mkQ_surjective _
  intro q
  obtain ⟨q', rfl⟩ := h q
  obtain ⟨q'', rfl⟩ := (finsuppLequivDFinsupp R).surjective q'
  obtain ⟨p, rfl⟩ := (basisMonomials σ R).repr.surjective q''
  exact ⟨p, rfl⟩

/-- The kernel of the coefficientwise quotient map is the corresponding coefficient
ideal. -/
private lemma coefficientQuotientMap_ker {σ R : Type*} [CommRing R]
    (J : (σ →₀ ℕ) → Ideal R) (hJ : Monotone J) :
    (coefficientQuotientMap J).ker = (coefficientIdeal J hJ).restrictScalars R := by
  classical
  ext p
  change coefficientQuotientMap J p = 0 ↔ ∀ d, p.coeff d ∈ J d
  rw [DFinsupp.ext_iff]
  simp only [coefficientQuotientMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, DFinsupp.zero_apply]
  change (∀ d, (J d).mkQ (p.coeff d) = 0) ↔ _
  exact forall_congr' fun d => Ideal.Quotient.eq_zero_iff_mem

/-- The affine nodal algebra is flat over its base ring as soon as `R ⧸ I` is. -/
theorem nodalAlgebra_flat (R : Type u) [CommRing R] (I : Ideal R)
    (hflat : Module.Flat R (R ⧸ I)) :
    Module.Flat R (nodalAlgebra R I) := by
  have h : ∀ d, Module.Flat R (R ⧸ nodalCoefficientIdeal I d) := by
    intro d
    have hc : nodalCoefficientIdeal I d = ⊥ ∨ nodalCoefficientIdeal I d = I ∨
        nodalCoefficientIdeal I d = ⊤ := by
      unfold nodalCoefficientIdeal
      split_ifs <;> simp
    rcases hc with hc | hc | hc
    · rw [hc]
      exact Module.Flat.of_linearEquiv (AlgEquiv.quotientBot R R).toLinearEquiv
    · rw [hc]
      exact hflat
    · rw [hc]
      infer_instance
  let f := coefficientQuotientMap (nodalCoefficientIdeal I)
  have hk : f.ker = (nodalRelationIdeal R I).restrictScalars R := by
    rw [nodalRelationIdeal_eq_coefficientIdeal]
    exact coefficientQuotientMap_ker _ _
  let e : nodalAlgebra R I ≃ₗ[R] Π₀ d, R ⧸ nodalCoefficientIdeal I d :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans
      (f.quotKerEquivOfSurjective (coefficientQuotientMap_surjective _))
  exact Module.Flat.of_linearEquiv e

/-- The image of the nodal relation ideal under a ring map is spanned by the images of its
generators. -/
private lemma map_nodalRelationIdeal {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    (f : MvPolynomial (Fin 2) R →+* S) :
    (nodalRelationIdeal R I).map f = Ideal.span (insert (f (X 0 * X 1))
      (Set.range fun a : I => f (C (a : R) * X (1 : Fin 2)))) := by
  rw [nodalRelationIdeal, Ideal.map_span]
  exact congrArg _ (Set.image_insert_eq.trans (congrArg _ (Set.range_comp f _).symm))

/-- The affine nodal algebra is not finitely presented over its base ring when the ideal is
not finitely generated. -/
theorem nodalAlgebra_not_finitePresentation
    (R : Type u) [CommRing R] (I : Ideal R) (hI : ¬ I.FG) :
    ¬ Algebra.FinitePresentation R (nodalAlgebra R I) := by
  intro h
  let f : MvPolynomial (Fin 2) R →+* R :=
    MvPolynomial.eval₂Hom (RingHom.id R) (fun i => if i = 0 then 0 else 1)
  have hf : (nodalRelationIdeal R I).map f = I := by
    rw [map_nodalRelationIdeal]
    simp [f]
  apply hI
  rw [← hf]
  apply Ideal.FG.map
  have hk := Algebra.FinitePresentation.ker_fg_of_mvPolynomial
    (Ideal.Quotient.mkₐ R (nodalRelationIdeal R I)) (Ideal.Quotient.mk_surjective)
  simpa using hk

/-- Base change of a quotient of a polynomial algebra is the quotient of the polynomial
algebra over the base-changed ring by the extended ideal. -/
private noncomputable def polynomialQuotientBaseChange {R S σ : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial σ R)) :
    S ⊗[R] (MvPolynomial σ R ⧸ J) ≃ₐ[S]
      MvPolynomial σ S ⧸ J.map (MvPolynomial.map (algebraMap R S)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv S _ S J).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S) (by
      have he : (MvPolynomial.algebraTensorAlgEquiv R S).toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            MvPolynomial σ R →ₐ[R] S ⊗[R] MvPolynomial σ R).toRingHom =
          MvPolynomial.map (algebraMap R S) := by
        apply RingHom.ext
        intro p
        change MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] p) = _
        simp
      exact (congrArg (fun f => J.map f) he).symm.trans (Ideal.map_map _ _).symm))

/-- Killing `y` in two variables leaves the polynomial algebra in one variable. -/
private noncomputable def quotientYEquiv (S : Type*) [CommRing S] :
    (MvPolynomial (Fin 2) S ⧸ Ideal.span ({X 1} : Set (MvPolynomial (Fin 2) S))) ≃ₐ[S]
      Polynomial S := by
  let J : Ideal (MvPolynomial (Fin 2) S) := Ideal.span {X 1}
  let f : MvPolynomial (Fin 2) S →ₐ[S] Polynomial S :=
    MvPolynomial.aeval (fun i => if i = 0 then Polynomial.X else 0)
  have hf : J ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl
    simp [f]
  let f' := Ideal.Quotient.liftₐ J f hf
  let g : Polynomial S →ₐ[S] MvPolynomial (Fin 2) S ⧸ J :=
    Polynomial.aeval (Ideal.Quotient.mk J (X 0))
  apply AlgEquiv.ofAlgHom f' g
  · apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, g, Polynomial.aeval_X, AlgHom.id_apply]
    change f (X 0) = Polynomial.X
    simp [f]
  · apply Ideal.Quotient.algHom_ext
    ext i
    fin_cases i
    · change g (f (X 0)) = Ideal.Quotient.mk J (X 0)
      simp [g, f]
    · change g (f (X 1)) = Ideal.Quotient.mk J (X 1)
      simp only [f, aeval_X, show (1 : Fin 2) ≠ 0 by decide, ite_false, map_zero]
      have hy : (X (1 : Fin 2) : MvPolynomial (Fin 2) S) ∈ J := Ideal.subset_span rfl
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr hy).symm

/-- The extension of the nodal relation ideal along a ring map is the nodal relation ideal
of the image of the generating family. -/
private lemma mapped_nodalRelationIdeal {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) :
    (nodalRelationIdeal R I).map (MvPolynomial.map f) =
      Ideal.span (insert (X 0 * X 1)
        (Set.range fun a : I => C (f (a : R)) * X (1 : Fin 2))) := by
  rw [map_nodalRelationIdeal]
  simp only [map_mul, map_X, MvPolynomial.map_C]

/-- Where the ideal dies, the nodal relation ideal becomes `(xy)`. -/
private lemma mapped_nodalRelationIdeal_eq_node {R K : Type*} [CommRing R] [CommRing K]
    (I : Ideal R) (f : R →+* K) (h : ∀ a : I, f a = 0) :
    (nodalRelationIdeal R I).map (MvPolynomial.map f) =
      Ideal.span ({X 0 * X 1} : Set (MvPolynomial (Fin 2) K)) := by
  rw [mapped_nodalRelationIdeal]
  simp only [h, map_zero, zero_mul, Set.range_const]
  exact (Ideal.span_insert _ _).trans (by simp)

/-- Where some element of the ideal survives as a unit, the nodal relation ideal becomes
`(y)`. -/
private lemma mapped_nodalRelationIdeal_eq_line {R K : Type*} [CommRing R] [Field K]
    (I : Ideal R) (f : R →+* K) (a : I) (ha : f a ≠ 0) :
    (nodalRelationIdeal R I).map (MvPolynomial.map f) =
      Ideal.span ({X 1} : Set (MvPolynomial (Fin 2) K)) := by
  rw [mapped_nodalRelationIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl | ⟨b, rfl⟩ <;> exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl
    have h := Ideal.mul_mem_left
      (Ideal.span (insert (X 0 * X 1)
        (Set.range fun a : I => C (f (a : R)) * X (1 : Fin 2))))
      (C (f a)⁻¹) (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨a, rfl⟩))
    simpa [← mul_assoc, ← map_mul, ha] using h

/-- Every fibre of the affine nodal algebra is a node or an affine line. -/
theorem nodalAlgebra_fiber (R : Type u) [CommRing R] (I : Ideal R)
    (p : Ideal R) [p.IsPrime] :
    Nonempty (p.Fiber (nodalAlgebra R I) ≃ₐ[p.ResidueField]
      (MvPolynomial (Fin 2) p.ResidueField ⧸
        Ideal.span ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
          Set (MvPolynomial (Fin 2) p.ResidueField)))) ∨
      Nonempty (p.Fiber (nodalAlgebra R I) ≃ₐ[p.ResidueField]
        Polynomial p.ResidueField) := by
  classical
  let e := polynomialQuotientBaseChange (S := p.ResidueField) (nodalRelationIdeal R I)
  by_cases h : ∀ a : I, algebraMap R p.ResidueField a = 0
  · exact Or.inl ⟨e.trans (Ideal.quotientEquivAlgOfEq _
      (mapped_nodalRelationIdeal_eq_node I _ h))⟩
  · push Not at h
    obtain ⟨a, ha⟩ := h
    exact Or.inr ⟨(e.trans (Ideal.quotientEquivAlgOfEq _
      (mapped_nodalRelationIdeal_eq_line I _ a ha))).trans (quotientYEquiv _)⟩

end Stacks.Examples
