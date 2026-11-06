module

public import StacksFrontier.RingTheory.GradedAlgebra.LiftRecordInvariant

/-!
# The recorded relation vector determines the lift up to isomorphism

Step (viii) of the proof of the tangent-space half of Stacks 0DVZ
(`examples-defos.tex:683`) opens with

> *"We conclude that the isomorphism class of `Q` is determined by the image of the vector
> `(G_1, …, G_m)` …"*

This file proves that sentence, in the sharp form: two lifts of `P` over the same square-zero
base whose recorded vectors are **equal** are isomorphic as algebras over the base, by an
isomorphism commuting with the reductions to `P` and preserving the gradings. It is the
injectivity half of the criterion
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`, up to the change of
lifted generators which makes two records with the same class in the cokernel of the Jacobian
actually equal.

The mechanism is that a polynomial with coefficients in the square-zero ideal has a record
which **does not depend on the lift at all**: it is read off from the coefficients and the
generators `x i` of the presentation of `P`. So a lifted relation of one lift is automatically a
relation of the other, and the two presentations of Stacks 0DVZ's step (vi) — which is
`GradedAlgebra.aeval_eq_zero_iff_mem_span_of_flat` — present the same ideal.

## Main definitions

* `GradedAlgebra.polyRecord`: the record of a polynomial whose coefficients lie in the kernel
  of the augmentation, as an element of `I ⊗[k] P`.

## Main results

* `GradedAlgebra.polyRecord_spec`: its defining property, for *every* family of lifts of the
  generators.
* `GradedAlgebra.span_eq_span_of_record_eq`: two lifts with equal records have lifted relations
  generating the same ideal.
* `GradedAlgebra.exists_algEquiv_of_record_eq`: **two lifts with equal records are
  isomorphic**, compatibly with the reductions and the gradings.

## Implementation notes

The independence of `polyRecord` from the lift is the whole point and is visible in its type:
no lift appears in it. That is what lets the record of one lift be evaluated against the other,
which is the step the source performs silently when it says the vector determines the class.

The isomorphism is assembled from `Ideal.quotientKerAlgEquivOfSurjective` on both sides and
`Ideal.quotientEquivAlgOfEq` between them, so it is characterised by
`Φ (aeval q G) = aeval q' G`; compatibility with the reductions and the gradings are then read
off from that formula.

Nothing here is tagged: this is step (viii) of 0DVZ's *proof*, and Stacks does not tag the steps
of a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace GradedAlgebra

universe u v w t

variable {k : Type u} {A : Type v} {P : Type w} {Q : Type t}
  [CommRing k] [CommRing A] [Algebra k A] [CommRing P] [Algebra k P] [CommRing Q] [Algebra A Q]

/-- **The record of a polynomial with coefficients in the square-zero ideal.** It is read off
from the coefficients and the generators `x i` of the presentation of `P`, and **mentions no
lift**: that independence is what makes the recorded vector determine the isomorphism class of
a lift. -/
noncomputable def polyRecord (ε : A →ₐ[k] k) (I : Ideal A) (hεI : ∀ a : A, ε a = 0 → a ∈ I)
    {n : ℕ} (x : Fin n → P) (H : MvPolynomial (Fin n) A)
    (hH : MvPolynomial.map (ε : A →+* k) H = 0) : (↥I) ⊗[k] P :=
  ∑ m ∈ H.support,
    (⟨H.coeff m, hεI _ (by
      have hc := MvPolynomial.coeff_map (ε : A →+* k) H m
      rw [hH, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
      exact hc.symm)⟩ : ↥I) ⊗ₜ[k] aeval x ((MvPolynomial.monomial m) (1 : k))

/-- **The defining property of `polyRecord`**, for *every* family of lifts of the generators:
the comparison map sends the record of `H` to the value of `H` at the lifts. Since the record
does not depend on the lifts, this says that the value of `H` at any two families of lifts of
the generators is recorded by the same element of `I ⊗[k] P`. -/
theorem polyRecord_spec (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A)
    (hεI : ∀ a : A, ε a = 0 → a ∈ I) (θ : (↥I) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    {n : ℕ} {x : Fin n → P} {q : Fin n → Q} (hq : ∀ i, π (q i) = x i)
    (H : MvPolynomial (Fin n) A) (hH : MvPolynomial.map (ε : A →+* k) H = 0) :
    θ (polyRecord ε I hεI x H hH) = aeval q H := by
  classical
  have hconst := map_algebraMap_of_smul ε π hπsmul
  have hmono : ∀ m : Fin n →₀ ℕ,
      π (aeval q ((MvPolynomial.monomial m) (1 : A))) =
        aeval x ((MvPolynomial.monomial m) (1 : k)) := by
    intro m
    rw [MvPolynomial.hom_aeval_eq_aeval_map ε π hconst hq, MvPolynomial.map_monomial, map_one]
  have hterm : ∀ m : Fin n →₀ ℕ, ∀ hm : H.coeff m ∈ I,
      θ ((⟨H.coeff m, hm⟩ : ↥I) ⊗ₜ[k]
          aeval x ((MvPolynomial.monomial m) (1 : k))) =
        aeval q ((MvPolynomial.monomial m) (H.coeff m)) := by
    intro m hm
    rw [← hmono m, hθ]
    rw [show (MvPolynomial.monomial m) (H.coeff m) =
        MvPolynomial.C (H.coeff m) * (MvPolynomial.monomial m) (1 : A) from by
      rw [MvPolynomial.C_mul_monomial, mul_one]]
    rw [map_mul, MvPolynomial.aeval_C, ← Algebra.smul_def]
  rw [polyRecord, map_sum]
  rw [Finset.sum_congr rfl fun m _ => hterm m _]
  rw [← map_sum]
  exact congrArg (aeval q) (MvPolynomial.as_sum H).symm

/-- **Two lifts with equal records have lifted relations generating the same ideal.** The error
term of a lifted relation of one lift has a record which does not mention that lift, so it is
evaluated against the other lift as well; with the two records equal, each lifted relation of
one lift is killed by the evaluation of the other, hence lies in its ideal by the
presentation theorem `GradedAlgebra.aeval_eq_zero_iff_mem_span_of_flat`. -/
theorem span_eq_span_of_record_eq {Q' : Type t} [CommRing Q'] [Algebra A Q']
    (ε : A →ₐ[k] k) (π : Q →+* P) (π' : Q' →+* P) (I : Ideal A)
    [Module.Flat A Q] [Module.Flat A Q'] (hIsq : I * I = ⊥)
    (hεI : ∀ a : A, ε a = 0 → a ∈ I)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπ'smul : ∀ (a : A) (y : Q'), π' (a • y) = ε a • π' y)
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hθinj : Function.Injective θ)
    (θ' : (↥I) ⊗[k] P →+ Q') (hθ' : ∀ (b : ↥I) (y : Q'), θ' (b ⊗ₜ π' y) = (b : A) • y)
    (hθ'inj : Function.Injective θ')
    {n r : ℕ} {x : Fin n → P} {F : Fin r → MvPolynomial (Fin n) k}
    (hxker : ∀ G : MvPolynomial (Fin n) k, aeval x G = 0 → G ∈ Ideal.span (Set.range F))
    {q : Fin n → Q} {q' : Fin n → Q'} (hq : ∀ i, π (q i) = x i) (hq' : ∀ i, π' (q' i) = x i)
    (hqsurj : Function.Surjective (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q))
    (hq'surj : Function.Surjective (aeval q' : MvPolynomial (Fin n) A →ₐ[A] Q'))
    (Flift Flift' : Fin r → MvPolynomial (Fin n) A)
    (hFmap : ∀ j, MvPolynomial.map (ε : A →+* k) (Flift j) = F j)
    (hFval : ∀ j, aeval q (Flift j) = 0)
    (hF'map : ∀ j, MvPolynomial.map (ε : A →+* k) (Flift' j) = F j)
    (hF'val : ∀ j, aeval q' (Flift' j) = 0)
    (G : Fin r → (↥I) ⊗[k] P)
    (hG : ∀ j, θ (G j) = -aeval q (MvPolynomial.map (algebraMap k A) (F j)))
    (hG' : ∀ j, θ' (G j) = -aeval q' (MvPolynomial.map (algebraMap k A) (F j))) :
    Ideal.span (Set.range Flift) = Ideal.span (Set.range Flift') := by
  -- the error term of a lifted relation, and the fact that it reduces to zero
  have herr : ∀ (Fl : Fin r → MvPolynomial (Fin n) A),
      (∀ j, MvPolynomial.map (ε : A →+* k) (Fl j) = F j) → ∀ j,
      MvPolynomial.map (ε : A →+* k)
        (MvPolynomial.map (algebraMap k A) (F j) - Fl j) = 0 := by
    intro Fl hFl j
    rw [map_sub, MvPolynomial.map_map_algebraMap, hFl j, sub_self]
  -- the key step, in a form usable in both directions
  have hkey : ∀ {Q₁ Q₂ : Type t} [CommRing Q₁] [CommRing Q₂] [Algebra A Q₁] [Algebra A Q₂],
      ∀ (π₁ : Q₁ →+* P) (π₂ : Q₂ →+* P) (θ₁ : (↥I) ⊗[k] P →+ Q₁) (θ₂ : (↥I) ⊗[k] P →+ Q₂),
      (∀ (b : ↥I) (y : Q₁), θ₁ (b ⊗ₜ π₁ y) = (b : A) • y) →
      (∀ (b : ↥I) (y : Q₂), θ₂ (b ⊗ₜ π₂ y) = (b : A) • y) →
      Function.Injective θ₂ →
      (∀ (a : A) (y : Q₁), π₁ (a • y) = ε a • π₁ y) →
      (∀ (a : A) (y : Q₂), π₂ (a • y) = ε a • π₂ y) →
      ∀ {q₁ : Fin n → Q₁} {q₂ : Fin n → Q₂}, (∀ i, π₁ (q₁ i) = x i) → (∀ i, π₂ (q₂ i) = x i) →
      ∀ (Fl : Fin r → MvPolynomial (Fin n) A)
        (hFl : ∀ j, MvPolynomial.map (ε : A →+* k) (Fl j) = F j),
      (∀ j, aeval q₂ (Fl j) = 0) →
      (∀ j, θ₁ (G j) = -aeval q₁ (MvPolynomial.map (algebraMap k A) (F j))) →
      (∀ j, θ₂ (G j) = -aeval q₂ (MvPolynomial.map (algebraMap k A) (F j))) →
      ∀ j, aeval q₁ (Fl j) = 0 := by
    intro Q₁ Q₂ _ _ _ _ π₁ π₂ θ₁ θ₂ hθ₁ hθ₂ hθ₂inj hπ₁ hπ₂ q₁ q₂ hq₁ hq₂ Fl hFl hFl0 hG₁ hG₂ j
    have hζ : polyRecord ε I hεI x _ (herr Fl hFl j) = -G j := hθ₂inj <| by
      rw [polyRecord_spec ε π₂ I hεI θ₂ hθ₂ hπ₂ hq₂ _ (herr Fl hFl j), map_sub, hFl0 j, sub_zero,
        map_neg, hG₂ j, neg_neg]
    have hζ₁ := polyRecord_spec ε π₁ I hεI θ₁ hθ₁ hπ₁ hq₁ _ (herr Fl hFl j)
    rw [hζ, map_neg, hG₁ j, neg_neg, map_sub] at hζ₁
    exact sub_eq_self.mp hζ₁.symm
  have h1 : ∀ j, aeval q (Flift' j) = 0 :=
    hkey π π' θ θ' hθ hθ' hθ'inj hπsmul hπ'smul hq hq' Flift' hF'map hF'val hG hG'
  have h2 : ∀ j, aeval q' (Flift j) = 0 :=
    hkey π' π θ' θ hθ' hθ hθinj hπ'smul hπsmul hq' hq Flift hFmap hFval hG' hG
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact (aeval_eq_zero_iff_mem_span_of_flat ε π' I hIsq hπ'smul hεI hxker hq' hq'surj Flift'
      hF'map hF'val (Flift j)).mp (h2 j)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact (aeval_eq_zero_iff_mem_span_of_flat ε π I hIsq hπsmul hεI hxker hq hqsurj Flift
      hFmap hFval (Flift' j)).mp (h1 j)

/-- **Two lifts with equal records are isomorphic.** This is the sentence *"the isomorphism
class of `Q` is determined by the image of the vector `(G_1, …, G_m)`"* of Stacks 0DVZ: with the
lifted relations generating the same ideal, both lifts are the same quotient of
`A[X_1, …, X_n]`, and the isomorphism between them is characterised by
`Φ (aeval q G) = aeval q' G`, from which compatibility with the reductions and preservation of
the gradings are immediate. -/
theorem exists_algEquiv_of_record_eq {Q' : Type t} [CommRing Q'] [Algebra A Q']
    (gradingQ : ℕ → Submodule A Q) (gradingQ' : ℕ → Submodule A Q')
    [GradedAlgebra gradingQ] [GradedAlgebra gradingQ']
    (ε : A →ₐ[k] k) (π : Q →+* P) (π' : Q' →+* P) (I : Ideal A)
    [Module.Flat A Q] [Module.Flat A Q'] (hIsq : I * I = ⊥)
    (hεI : ∀ a : A, ε a = 0 → a ∈ I)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπ'smul : ∀ (a : A) (y : Q'), π' (a • y) = ε a • π' y)
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hθinj : Function.Injective θ)
    (θ' : (↥I) ⊗[k] P →+ Q') (hθ' : ∀ (b : ↥I) (y : Q'), θ' (b ⊗ₜ π' y) = (b : A) • y)
    (hθ'inj : Function.Injective θ')
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {F : Fin r → MvPolynomial (Fin n) k}
    (hxker : ∀ G : MvPolynomial (Fin n) k, aeval x G = 0 → G ∈ Ideal.span (Set.range F))
    {q : Fin n → Q} {q' : Fin n → Q'} (hq : ∀ i, π (q i) = x i) (hq' : ∀ i, π' (q' i) = x i)
    (hqmem : ∀ i, q i ∈ gradingQ (d i)) (hq'mem : ∀ i, q' i ∈ gradingQ' (d i))
    (hqsurj : Function.Surjective (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q))
    (hq'surj : Function.Surjective (aeval q' : MvPolynomial (Fin n) A →ₐ[A] Q'))
    (Flift Flift' : Fin r → MvPolynomial (Fin n) A)
    (hFmap : ∀ j, MvPolynomial.map (ε : A →+* k) (Flift j) = F j)
    (hFval : ∀ j, aeval q (Flift j) = 0)
    (hF'map : ∀ j, MvPolynomial.map (ε : A →+* k) (Flift' j) = F j)
    (hF'val : ∀ j, aeval q' (Flift' j) = 0)
    (G : Fin r → (↥I) ⊗[k] P)
    (hG : ∀ j, θ (G j) = -aeval q (MvPolynomial.map (algebraMap k A) (F j)))
    (hG' : ∀ j, θ' (G j) = -aeval q' (MvPolynomial.map (algebraMap k A) (F j))) :
    ∃ Φ : Q ≃ₐ[A] Q',
      (∀ g : MvPolynomial (Fin n) A, Φ (aeval q g) = aeval q' g) ∧
      (∀ y, π' (Φ y) = π y) ∧
      ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → Φ y ∈ gradingQ' e' := by
  have hspan := span_eq_span_of_record_eq ε π π' I hIsq hεI hπsmul hπ'smul θ hθ hθinj θ' hθ'
    hθ'inj hxker hq hq' hqsurj hq'surj Flift Flift' hFmap hFval hF'map hF'val G hG hG'
  have hker : RingHom.ker (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q) =
      RingHom.ker (aeval q' : MvPolynomial (Fin n) A →ₐ[A] Q') := by
    refine Ideal.ext fun g => ?_
    rw [RingHom.mem_ker, RingHom.mem_ker,
      aeval_eq_zero_iff_mem_span_of_flat ε π I hIsq hπsmul hεI hxker hq hqsurj Flift hFmap
        hFval g,
      aeval_eq_zero_iff_mem_span_of_flat ε π' I hIsq hπ'smul hεI hxker hq' hq'surj Flift'
        hF'map hF'val g, hspan]
  let Φ : Q ≃ₐ[A] Q' := (Ideal.quotientKerAlgEquivOfSurjective hqsurj).symm.trans
    ((Ideal.quotientEquivAlgOfEq A hker).trans (Ideal.quotientKerAlgEquivOfSurjective hq'surj))
  have hΦ : ∀ g : MvPolynomial (Fin n) A, Φ (aeval q g) = aeval q' g := fun g => by
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply,
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply hqsurj g,
      Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · intro y
    obtain ⟨g, rfl⟩ := hqsurj y
    rw [hΦ, MvPolynomial.hom_aeval_eq_aeval_map ε π' (map_algebraMap_of_smul ε π' hπ'smul) hq',
      MvPolynomial.hom_aeval_eq_aeval_map ε π (map_algebraMap_of_smul ε π hπsmul) hq]
  · intro e' y hy
    obtain ⟨g, hgmem, hgy⟩ := exists_isWeightedHomogeneous_aeval_eq gradingQ hqmem hqsurj hy
    rw [← hgy, hΦ]
    exact aeval_mem_grading_of_isWeightedHomogeneous gradingQ' hq'mem hgmem

end GradedAlgebra

end
