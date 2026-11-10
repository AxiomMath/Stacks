module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Basic.Countable.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Set.Countable
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.OfPrime
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic

/-!
# The ring of constants of a derivation

The subalgebra `derivationConstants D` annihilated by a derivation `D`, used in
`StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit`: it is local when the algebra is,
the algebra is integral over it under a torsion condition, and it is Noetherian in the
one-dimensional situation where its maximal ideal is finitely generated.

## References

* D. Ferrand and M. Raynaud, *Fibres formelles d'un anneau local noethérien*,
  Ann. Sci. Éc. Norm. Supér. 3 (1970), 295–311, Proposition 3.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Examples.FlatAlgebraNotFilteredColimit

open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
open scoped RatFunc LaurentSeries

/-- The subalgebra annihilated by a derivation. -/
def derivationConstants {R B M : Type*} [CommSemiring R] [CommSemiring B]
    [AddCommMonoid M] [Algebra R B] [Module B M] [Module R M]
    (D : Derivation R B M) : Subalgebra R B where
  carrier := {x | D x = 0}
  algebraMap_mem' := D.map_algebraMap
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x + y) = 0
    simp only [map_add, hx, hy, add_zero]
  mul_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x * y) = 0
    simp only [D.leibniz, hx, hy, smul_zero, add_zero]

/-- Membership in the constants means that the derivation vanishes. -/
private lemma mem_derivationConstants {R B M : Type*} [CommSemiring R] [CommSemiring B]
    [AddCommMonoid M] [Algebra R B] [Module B M] [Module R M]
    (D : Derivation R B M) (x : B) : x ∈ derivationConstants D ↔ D x = 0 := Iff.rfl

/-- A constant is invertible among the constants exactly when it is invertible in the algebra. -/
lemma isUnit_derivationConstants_iff {R B M : Type*}
    [CommSemiring R] [CommSemiring B] [AddCommMonoid M] [Algebra R B]
    [Module B M] [Module R M] (D : Derivation R B M) (x : derivationConstants D) :
    IsUnit x ↔ IsUnit (x : B) := by
  refine ⟨fun h => h.map (derivationConstants D).val, ?_⟩
  rintro ⟨u, hu⟩
  have hDu : D (u : B) = 0 := hu.symm ▸ x.property
  have hDinv : D (↑u⁻¹ : B) = 0 := by
    have h := congrArg (fun m : M => (↑u⁻¹ : B) • m) (D.leibniz (u : B) (↑u⁻¹ : B))
    simpa only [Units.mul_inv, D.map_one_eq_zero, hDu, smul_zero, add_zero,
      smul_smul, Units.inv_mul, one_smul] using h.symm
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(↑u⁻¹ : B), hDinv⟩, ?_⟩
  apply Subtype.ext
  change (x : B) * (↑u⁻¹ : B) = 1
  rw [← hu, Units.mul_inv]

/-- The constants of a derivation on a local algebra form a local ring. -/
lemma isLocalRing_derivationConstants {R B M : Type*}
    [CommSemiring R] [CommSemiring B] [IsLocalRing B] [AddCommMonoid M] [Algebra R B]
    [Module B M] [Module R M] (D : Derivation R B M) :
    IsLocalRing (derivationConstants D) := by
  apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
  intro x y hxy
  have h := IsLocalRing.isUnit_or_isUnit_of_isUnit_add
    (hxy.map (derivationConstants D).val)
  exact h.imp ((isUnit_derivationConstants_iff D x).mpr)
    ((isUnit_derivationConstants_iff D y).mpr)

/-- An element whose derivative is killed by a power has a constant power. -/
private lemma pow_mem_derivationConstants_of_smul_eq_zero
    {R B M : Type*} [CommSemiring R] [CommSemiring B]
    [AddCommMonoid M] [Algebra R B] [Module B M] [Module R M]
    (D : Derivation R B M) {b : B} {n : ℕ} (h : b ^ n • D b = 0) :
    b ^ (n + 1) ∈ derivationConstants D := by
  rw [mem_derivationConstants, D.leibniz_pow]
  simp only [Nat.add_sub_cancel, h, smul_zero]

/-- Power torsion of a derivative gives integrality over the constants. -/
private lemma isIntegral_derivationConstants_of_smul_eq_zero
    {R B M : Type*} [CommRing R] [CommRing B]
    [AddCommGroup M] [Algebra R B] [Module B M] [Module R M]
    (D : Derivation R B M) {b : B} (h : ∃ n : ℕ, b ^ n • D b = 0) :
    IsIntegral (derivationConstants D) b := by
  obtain ⟨n, hn⟩ := h
  let z : derivationConstants D := ⟨b ^ (n + 1),
    pow_mem_derivationConstants_of_smul_eq_zero D hn⟩
  exact (isIntegral_algebraMap (x := z)).of_pow (Nat.succ_pos n)

/-- If every element differs from a scalar by an element with power-torsion derivative,
then the algebra is integral over its constants. -/
private lemma isIntegral_derivationConstants
    {R B M : Type*} [CommRing R] [CommRing B]
    [AddCommGroup M] [Algebra R B] [Module B M] [Module R M]
    (D : Derivation R B M)
    (h : ∀ b : B, ∃ r : R, ∃ n : ℕ,
      (b - algebraMap R B r) ^ n • D (b - algebraMap R B r) = 0) :
    Algebra.IsIntegral (derivationConstants D) B := by
  constructor
  intro b
  obtain ⟨r, n, hn⟩ := h b
  have hb := isIntegral_derivationConstants_of_smul_eq_zero D ⟨n, hn⟩
  have hr : IsIntegral (derivationConstants D) (algebraMap R B r) :=
    isIntegral_algebraMap (x := algebraMap R (derivationConstants D) r)
  simpa only [sub_add_cancel] using hb.add hr

/-- The maximal ideal of the constants has two generators when the uniformizer-torsion
in the image of the derivation is generated by one derivative over the base ring. -/
private lemma maximalIdeal_derivationConstants_eq_span
    {R B M : Type*} [CommRing R] [CommRing B] [IsLocalRing B]
    [AddCommGroup M] [Algebra R B] [Module B M] [Module R M]
    [IsScalarTower R B M] (D : Derivation R B M)
    (t z : derivationConstants D) (s : B)
    (ht : IsLocalRing.maximalIdeal B = Ideal.span {(t : B)})
    (hz : (z : B) = (t : B) * s)
    (hker : ∀ b : B, (t : B) • D b = 0 → ∃ r : R, D b = r • D s) :
    letI : IsLocalRing (derivationConstants D) := isLocalRing_derivationConstants D
    IsLocalRing.maximalIdeal (derivationConstants D) = Ideal.span {t, z} := by
  have : IsLocalRing (derivationConstants D) := isLocalRing_derivationConstants D
  have htB : (t : B) ∈ IsLocalRing.maximalIdeal B := by
    rw [ht]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hmem (x : derivationConstants D) : x ∈ IsLocalRing.maximalIdeal (derivationConstants D) ↔
      (x : B) ∈ IsLocalRing.maximalIdeal B := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_derivationConstants_iff]
  have htA := (hmem t).mpr htB
  have hzA : z ∈ IsLocalRing.maximalIdeal (derivationConstants D) :=
    (hmem z).mpr (hz ▸ (IsLocalRing.maximalIdeal B).mul_mem_right s htB)
  apply le_antisymm
  · intro x hx
    have hxB : (x : B) ∈ Ideal.span {(t : B)} := by
      rw [← ht]
      exact (hmem x).mp hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hxB
    have hDb : (t : B) • D b = 0 := by
      have h := x.property
      rw [mem_derivationConstants, hb, D.leibniz, t.property, smul_zero, add_zero] at h
      exact h
    obtain ⟨r, hr⟩ := hker b hDb
    have hy : b - algebraMap R B r * s ∈ derivationConstants D := by
      rw [mem_derivationConstants, map_sub, D.leibniz, D.map_algebraMap,
        smul_zero, add_zero, hr, algebraMap_smul, sub_self]
    let y : derivationConstants D := ⟨b - algebraMap R B r * s, hy⟩
    have heq : x = t * y + algebraMap R (derivationConstants D) r * z := by
      apply Subtype.ext
      change (x : B) = (t : B) * (b - algebraMap R B r * s) + algebraMap R B r * (z : B)
      rw [hz, hb]
      ring
    rw [heq]
    exact (Ideal.span {t, z}).add_mem
      ((Ideal.span {t, z}).mul_mem_right y (Ideal.subset_span (by simp)))
      ((Ideal.span {t, z}).mul_mem_left _ (Ideal.subset_span (by simp)))
  · exact Ideal.span_le.mpr (by simpa only [Set.insert_subset_iff, Set.singleton_subset_iff,
      SetLike.mem_coe] using And.intro htA hzA)

/-- An integral subring of a one-dimensional domain is Noetherian when its maximal
ideal is finitely generated. -/
private lemma isNoetherianRing_of_integral_extension_of_fg_maximalIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [Ring.KrullDimLE 1 B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (h : (IsLocalRing.maximalIdeal A).FG) : IsNoetherianRing A := by
  apply IsNoetherianRing.of_prime_ne_bot
  intro I hI hI0
  have hker : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
  obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := B) I (hker.symm ▸ bot_le)
  have hQ0 : Q ≠ ⊥ := by
    intro heq
    apply hI0
    rw [← hQI, heq]
    exact hker
  have := hQ.isMaximal_of_ne_bot hQ0
  have hImax : I.IsMaximal := hQI ▸ (inferInstance : (Q.under A).IsMaximal)
  rwa [IsLocalRing.eq_maximalIdeal hImax]

/-- Power torsion with respect to a constant uniformizer makes the ambient algebra
integral over the constants. -/
lemma isIntegral_derivationConstants_of_uniformizer_torsion
    {R B M : Type*} [CommRing R] [CommRing B]
    [AddCommGroup M] [Algebra R B] [Module B M] [Module R M]
    (D : Derivation R B M) (t : derivationConstants D)
    (hres : ∀ b : B, ∃ (r : R) (c : B), b - algebraMap R B r = (t : B) * c)
    (htors : ∀ m : M, ∃ n : ℕ, (t : B) ^ n • m = 0) :
    Algebra.IsIntegral (derivationConstants D) B := by
  apply isIntegral_derivationConstants D
  intro b
  obtain ⟨r, c, hbc⟩ := hres b
  obtain ⟨n, hn⟩ := htors (D (b - algebraMap R B r))
  refine ⟨r, n, ?_⟩
  calc
    (b - algebraMap R B r) ^ n • D (b - algebraMap R B r) =
        c ^ n • ((t : B) ^ n • D (b - algebraMap R B r)) := by
      conv_lhs => arg 1; rw [hbc, mul_pow, mul_comm]
      rw [mul_smul]
    _ = 0 := by rw [hn, smul_zero]

/-- The one-dimensional derivation construction is Noetherian. -/
lemma isNoetherianRing_derivationConstants
    {R B M : Type*} [CommRing R] [CommRing B] [IsLocalRing B] [IsDomain B]
    [Ring.KrullDimLE 1 B] [AddCommGroup M] [Algebra R B] [Module B M] [Module R M]
    [IsScalarTower R B M] (D : Derivation R B M)
    (t z : derivationConstants D) (s : B)
    (ht : IsLocalRing.maximalIdeal B = Ideal.span {(t : B)})
    (hz : (z : B) = (t : B) * s)
    (hker : ∀ b : B, (t : B) • D b = 0 → ∃ r : R, D b = r • D s)
    (hres : ∀ b : B, ∃ (r : R) (c : B), b - algebraMap R B r = (t : B) * c)
    (htors : ∀ m : M, ∃ n : ℕ, (t : B) ^ n • m = 0) :
    IsNoetherianRing (derivationConstants D) := by
  have := isLocalRing_derivationConstants D
  have := isIntegral_derivationConstants_of_uniformizer_torsion D t hres htors
  apply isNoetherianRing_of_integral_extension_of_fg_maximalIdeal (derivationConstants D) B
  rw [maximalIdeal_derivationConstants_eq_span D t z s ht hz hker]
  exact Submodule.fg_span (Set.toFinite {t, z})

end Stacks.Examples.FlatAlgebraNotFilteredColimit

end
