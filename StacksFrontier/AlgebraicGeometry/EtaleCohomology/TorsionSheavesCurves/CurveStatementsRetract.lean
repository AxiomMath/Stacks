module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.SmoothReduction

/-!
# The eight statements of Situation 0A52 pass to retracts

In the proof of Lemma 03SD the sheaf `G` is a retract of `f_* f^{-1} G` through the trace of a
finite étale morphism of degree prime to `ℓ` (Tag 03SE), and the statements are proved for the
bigger sheaf. This file supplies the formal step: cohomology of a retract is a retract of
cohomology, compatibly with restriction maps.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_retract` and its surjective
  companion.
* `Stacks.EtaleCohomology.CurveStatements.of_retract`: for `A` a retract of `M`, both killed by a
  prime, with `M` constructible, if statements (1) -- (8) hold for `M` they hold for `A`;
  `Stacks.EtaleCohomology.CurveStatements.of_retract_of_finite` replaces constructibility of `M`
  by the finiteness of its cohomology in the cases of statements (4) and (5).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

section Retract

variable {X : Scheme.{u}} {A M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (s : A ⟶ M) (r : M ⟶ A) (hsr : s ≫ r = 𝟙 A)

include hsr in
/-- Cohomology of a retract injects into cohomology. -/
theorem injective_sheafH_comp_mk₀_of_retract (q : ℕ) :
    Function.Injective fun x : Sheaf.H.{u + 1} A q ↦ x.comp (Ext.mk₀ s) (add_zero q) := by
  intro x y h
  have h' := congrArg (fun z : Sheaf.H.{u + 1} M q ↦ z.comp (Ext.mk₀ r) (add_zero q)) h
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hsr, Ext.comp_mk₀_id] using h'

variable {Y : Scheme.{u}} (i : Y ⟶ X)

/-- Surjectivity of restriction on the bigger sheaf gives it on the retract. -/
private theorem surjective_restriction_of_retract_aux (hsr : s ≫ r = 𝟙 A) (q : ℕ)
    (h : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i M q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i A q) := fun z ↦ by
  obtain ⟨w, hw⟩ := h (z.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map s))
    (add_zero q))
  refine ⟨w.comp (Ext.mk₀ r) (add_zero q), ?_⟩
  rw [etaleCohomologyRestrictionMap_comp_mk₀, hw, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, ← Functor.map_comp, hsr, CategoryTheory.Functor.map_id, Ext.comp_mk₀_id]

include hsr in
/-- Restriction is bijective on the cohomology of a retract when it is on the cohomology of the
bigger sheaf. -/
theorem bijective_etaleCohomologyRestrictionMap_of_retract (q : ℕ)
    (h : Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i M q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i A q) := by
  refine ⟨fun x y hxy ↦ injective_sheafH_comp_mk₀_of_retract s r hsr q (h.1 ?_), fun z ↦ ?_⟩
  · simp only [etaleCohomologyRestrictionMap_comp_mk₀, hxy]
  · exact surjective_restriction_of_retract_aux s r i hsr q h.2 z

include hsr in
/-- Restriction is surjective on the cohomology of a retract when it is on the cohomology of the
bigger sheaf. -/
theorem surjective_etaleCohomologyRestrictionMap_of_retract (q : ℕ)
    (h : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i M q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i A q) :=
  surjective_restriction_of_retract_aux s r i hsr q h

end Retract

/-- **The eight statements pass to a retract, given finiteness for the bigger sheaf.** Let `A` be
a retract of `M`, both killed by a prime `ℓ`, and suppose the cohomology of `M` is finite when `M`
is of torsion prime to the characteristic and when `X` is proper. If statements (1) -- (8) of
Situation 0A52 hold for `M`, they hold for `A`. This form is used when `M` is a finite direct image
whose constructibility is not known but whose cohomology is computed upstairs. -/
theorem CurveStatements.of_retract_of_finite {k : Type u} [Field k] {X : Scheme.{u}}
    {π : X ⟶ Spec (.of k)} {A M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (s : A ⟶ M) (r : M ⟶ A) (hsr : s ≫ r = 𝟙 A) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓA : ℓ • 𝟙 A = 0)
    (hℓM : ℓ • 𝟙 M = 0)
    (hf₄ : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) M →
      ∀ q, Finite (Sheaf.H.{u + 1} M q))
    (hf₅ : IsProper π → ∀ q, Finite (Sheaf.H.{u + 1} M q))
    (h : CurveStatements.{u, 0, u + 1} π M) : CurveStatements.{u, 0, u + 1} π A where
  vanishing q hq :=
    have := h.vanishing q hq
    (injective_sheafH_comp_mk₀_of_retract s r hsr q).subsingleton
  affineVanishing hX q hq :=
    have := h.affineVanishing hX q hq
    (injective_sheafH_comp_mk₀_of_retract s r hsr q).subsingleton
  primePowerVanishing p _ hp htor q hq := by
    by_cases hℓp : ℓ = p
    · subst hℓp
      have := h.primePowerVanishing ℓ hp (isPrimePowerTorsion_of_nsmul_eq_zero hℓM) q hq
      exact (injective_sheafH_comp_mk₀_of_retract s r hsr q).subsingleton
    · have hpp : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp.ne'
      exact subsingleton_sheafH_of_isZero
        (isZero_of_isPrimePowerTorsion_of_isPrimeToCharacteristicTorsion htor
          (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos
            ((Nat.coprime_primes hℓ hpp).mpr hℓp) hℓA)) q
  finite_of_isPrimeToCharacteristicTorsion B hX _ _ _ htor q := by
    rcases coprime_ringExpChar_or_isZero k (S := X) hℓ with hcop | hz
    · have := hf₄ (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos hcop hℓM) q
      exact Finite.of_injective _ (injective_sheafH_comp_mk₀_of_retract s r hsr q)
    · have := subsingleton_sheafH_of_isZero (hz _ hℓA htor) q
      exact Finite.of_subsingleton
  finite_of_isProper B hX _ _ hπ _ q :=
    have := hf₅ hπ q
    Finite.of_injective _ (injective_sheafH_comp_mk₀_of_retract s r hsr q)
  bijective_of_isPrimeToCharacteristicTorsion htor k' _ _ _ _ _ q := by
    rcases coprime_ringExpChar_or_isZero k (S := X) hℓ with hcop | hz
    · exact bijective_etaleCohomologyRestrictionMap_of_retract s r hsr _ q
        (h.bijective_of_isPrimeToCharacteristicTorsion
          (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos hcop hℓM) k' q)
    · exact bijective_etaleCohomologyRestrictionMap_of_isZero _ (hz _ hℓA htor) q
  bijective_of_isProper hπ k' _ _ _ _ _ q :=
    bijective_etaleCohomologyRestrictionMap_of_retract s r hsr _ q (h.bijective_of_isProper hπ k' q)
  surjective U _ :=
    surjective_etaleCohomologyRestrictionMap_of_retract s r hsr U.ι 2 (h.surjective U)

/-- **The eight statements pass to a retract.** Let `A` be a retract of `M`, both killed by a
prime `ℓ`, with `M` constructible. If statements (1) -- (8) of Situation 0A52 hold for `M`, they
hold for `A`: every cohomology group of `A` is a retract of that of `M`, compatibly with
restriction, and the torsion side conditions are met by `M` or force `A = 0`. -/
theorem CurveStatements.of_retract {k : Type u} [Field k] {X : Scheme.{u}}
    {π : X ⟶ Spec (.of k)} {A M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (s : A ⟶ M) (r : M ⟶ A) (hsr : s ≫ r = 𝟙 A) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓA : ℓ • 𝟙 A = 0)
    (hℓM : ℓ • 𝟙 M = 0) (hcM : IsConstructibleOnEveryBigSite M)
    (h : CurveStatements.{u, 0, u + 1} π M) : CurveStatements.{u, 0, u + 1} π A :=
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  CurveStatements.of_retract_of_finite s r hsr hℓ hℓA hℓM
    (fun ht ↦ h.finite_of_isPrimeToCharacteristicTorsion B hX (hcM B hX) ht)
    (fun hπ ↦ h.finite_of_isProper B hX hπ (hcM B hX)) h

end Stacks.EtaleCohomology

end
