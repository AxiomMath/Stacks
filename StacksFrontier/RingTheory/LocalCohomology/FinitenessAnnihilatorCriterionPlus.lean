module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.RingTheory.LocalCohomology.AnnihilatorPowerPlus
public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported

/-!
# Finiteness of the local cohomology of a bounded-below complex and annihilators

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization, let `K` be an
object of the bounded-below derived category of `A`-modules and let `n ∈ ℤ`. The local cohomology
modules `H^i_T(K)` are finite for `i ≤ n` as soon as one ideal `J` with `V(J) ⊆ T` annihilates
them in that range, and conversely.

This file proves the implication from finiteness to the existence of the annihilating ideal, and
its form for closed support `T = V(I)`, where the ideal can be taken to be a power of `I`. The
argument is formal: `H^i_T(K)` vanishes below any degree bounding `K` below, and in the finitely
many remaining degrees it is annihilated by its own annihilator, whose zero locus is its support
and therefore lies in `T`; the product of those annihilators is one ideal doing all of them at
once. The reverse implication, from an annihilating ideal to finiteness, is proved in
`StacksFrontier/RingTheory/LocalCohomology/FinitenessAnnihilatorCriterionPlusConverse.lean`, which
imports this file: its inductive step uses the fibre of multiplication by an element of the
annihilating ideal, and the substrate that step needs is the exactness of derived sections with
support on `D⁺`, which is supplied below.

## Main results

* `Stacks.LocalCohomology.localCohomologyWithSupportInPlusIsoUnbounded` — the bounded-below and
  the unbounded local cohomology of a bounded-below object agree.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInPlus_commShift` and
  `Stacks.LocalCohomology.derivedSectionsWithSupportInPlus_isTriangulated` — derived sections
  with support in `T` commute with the shift and are exact on `D⁺`, so a distinguished triangle
  there gives a long exact sequence of local cohomology modules.
* `Stacks.LocalCohomology.support_localCohomologyWithSupportInPlus_subset` — local cohomology
  with support in `T` is supported in `T`.
* `Stacks.LocalCohomology.isZero_localCohomologyWithSupportInPlus_of_lt` — it vanishes below any
  degree bounding the complex below.
* `Stacks.LocalCohomology.exists_annihilator_localCohomologyWithSupportInPlus_of_finite` —
  **Stacks 0EI1, the implication (1) ⟹ (2).**
* `Stacks.LocalCohomology.exists_pow_annihilator_localCohomologyWithSupportInPlus_of_finite` —
  **Stacks 0EI1, the implication (1) ⟹ (3) for closed support.**

## Implementation notes

Finiteness of the cohomology modules of `K`, which the source assumes by taking `K` in
`D⁺_{Coh}(A)`, is not needed for these implications, nor is stability of `T` under
specialization; both are dropped, so what is proved here is stronger than the corresponding part
of the source. The degree bound is an arbitrary integer, as in the source, and the lower end of
the range comes from the bounded-below structure of `K` rather than from a hypothesis.

The equivalence of the source's clauses (2) and (3) under `T = V(I)`, which is what turns the
ideal of clause (2) into a power of `I`, is
`Stacks.LocalCohomology.exists_annihilator_iff_exists_power_annihilator_plus`. The equivalences
the source states, which combine the implications proved here with that one and with the
converse, are `Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_tfae` and
`Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_tfae_zeroLocus` in
`StacksFrontier/RingTheory/LocalCohomology/FinitenessAnnihilatorCriterionPlusEquivalence.lean`.

## References

* [Stacks Project, Tag 0EI1](https://stacks.math.columbia.edu/tag/0EI1)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- **The bounded-below and the unbounded local cohomology of a bounded-below object agree.**
This is the degreewise form of Tag 0EF4's cohomology calculation. -/
def localCohomologyWithSupportInPlusIsoUnbounded (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (i : ℤ) :
    localCohomologyWithSupportInPlus.{u, v} A T K i ≅
      localCohomologyWithSupportIn.{u, v} A T (DerivedCategory.Plus.ι.obj K) i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    ((derivedSectionsWithSupportInPlusIso.{u, v} A T).app K)

/-- **Derived sections with support in `T` commute with the shift on `D⁺`.** This is the general
fact for the bounded-below right derived functor of an additive functor, applied to sections with
support in `T`. -/
@[instance_reducible]
noncomputable instance derivedSectionsWithSupportInPlus_commShift (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) : (derivedSectionsWithSupportInPlus.{u, v} A T).CommShift ℤ :=
  let _ : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
    (sectionsWithSupportInFunctor.{u, v} A T)

/-- **Derived sections with support in `T` are an exact functor of triangulated categories on
`D⁺`.** Consequently the local cohomology modules with support in `T` of the three objects of a
distinguished triangle of `D⁺` fit into a long exact sequence, through
`CategoryTheory.Functor.homologySequence_exact₁` and its companions. -/
instance derivedSectionsWithSupportInPlus_isTriangulated (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) : (derivedSectionsWithSupportInPlus.{u, v} A T).IsTriangulated :=
  let _ : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus
    (sectionsWithSupportInFunctor.{u, v} A T)

/-- Linearly equivalent modules have the same annihilator. -/
public lemma annihilator_eq_of_linearEquiv {A : Type u} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    Module.annihilator A M = Module.annihilator A N :=
  e.annihilator_eq

/-- **Local cohomology with support in `T` of a bounded-below object is supported in `T`.** -/
theorem support_localCohomologyWithSupportInPlus_subset (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (i : ℤ)
    [Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i)] :
    PrimeSpectrum.zeroLocus
      (Module.annihilator A (localCohomologyWithSupportInPlus.{u, v} A T K i) : Set A) ⊆ T := by
  have : Module.Finite A
      (localCohomologyWithSupportIn.{u, v} A T (DerivedCategory.Plus.ι.obj K) i) :=
    Module.Finite.equiv
      (localCohomologyWithSupportInPlusIsoUnbounded.{u, v} A T K i).toLinearEquiv
  rw [annihilator_eq_of_linearEquiv
      (localCohomologyWithSupportInPlusIsoUnbounded.{u, v} A T K i).toLinearEquiv,
    ← Module.support_eq_zeroLocus]
  exact support_localCohomologyWithSupportIn_subset.{u, v} T _ i

/-- **Local cohomology with support in `T` vanishes below any degree bounding the complex
below.** Sections with support in `T` have a bounded-below right derived functor, so `RΓ_T(K)`
lies in degrees `≥ a` whenever `K` does. -/
theorem isZero_localCohomologyWithSupportInPlus_of_lt (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (a i : ℤ)
    [K.IsGE a] (hi : i < a) : IsZero (localCohomologyWithSupportInPlus.{u, v} A T K i) := by
  let F := sectionsWithSupportInFunctor.{u, v} A T
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  have : F.Additive := by
    dsimp only [F]
    infer_instance
  have : ((derivedSectionsWithSupportInPlus.{u, v} A T).obj K).IsGE a :=
    Functor.isGE_rightDerivedFunctorPlus_obj F K a
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ a i hi

/-- The zero locus of the unit ideal is empty. -/
private lemma zeroLocus_top_subset {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) :
    PrimeSpectrum.zeroLocus ((⊤ : Ideal A) : Set A) ⊆ T := by
  simp only [Submodule.top_coe, PrimeSpectrum.zeroLocus_univ, Set.empty_subset]

/-- A family of ideals which is the unit ideal below `a` and whose members have zero locus inside
`T` on the range `[a, a + k - 1]` has a common lower bound on `(-∞, a + k - 1]` whose zero locus
lies in `T`: take the product over the finitely many relevant degrees. -/
private lemma exists_ideal_zeroLocus_subset_le_of_int (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (a : ℤ) (f : ℤ → Ideal A) (htop : ∀ i : ℤ, i < a → f i = ⊤) :
    ∀ k : ℕ, (∀ i : ℤ, a ≤ i → i ≤ a + (k : ℤ) - 1 →
        PrimeSpectrum.zeroLocus (f i : Set A) ⊆ T) →
      ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
        ∀ i : ℤ, i ≤ a + (k : ℤ) - 1 → J ≤ f i := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨⊤, zeroLocus_top_subset T, fun i hi ↦ ?_⟩
    rw [htop i (by omega)]
  | succ k ih =>
    intro hsub
    obtain ⟨J, hJT, hJ⟩ := ih fun i h₁ h₂ ↦ hsub i h₁ (by omega)
    refine ⟨J * f (a + (k : ℤ)), ?_, fun i hi ↦ ?_⟩
    · rw [PrimeSpectrum.zeroLocus_mul]
      exact Set.union_subset hJT (hsub (a + (k : ℤ)) (by omega) (by push_cast; omega))
    · rcases le_or_gt i (a + (k : ℤ) - 1) with h | h
      · exact (Ideal.mul_le_inf.trans inf_le_left).trans (hJ i h)
      · obtain rfl : i = a + (k : ℤ) := by push_cast at hi; omega
        exact Ideal.mul_le_inf.trans inf_le_right

/-- **Stacks 0EI1, the implication (1) ⟹ (2).** Let `A` be a Noetherian ring, let
`T ⊆ Spec(A)` be any subset, let `K` be an object of the bounded-below derived category of
`A`-modules and let `n ∈ ℤ`. If `H^i_T(K)` is finite for every `i ≤ n`, then there is an ideal
`J ⊆ A` with `V(J) ⊆ T` annihilating `H^i_T(K)` for every `i ≤ n`.

Below a degree `a` bounding `K` below the modules vanish, so their annihilator is the unit
ideal; on `[a, n]` each is annihilated by its own annihilator, whose zero locus is its support
and hence contained in `T`; the product of those finitely many ideals is the required `J`. -/
@[stacks 0EI1 "the implication (1) ⟹ (2); the converse (2) ⟹ (1) is not proved"]
theorem exists_annihilator_localCohomologyWithSupportInPlus_of_finite (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (n : ℤ)
    (hfin : ∀ i : ℤ, i ≤ n →
      Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i)) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      ∀ i : ℤ, i ≤ n → J ≤ Module.annihilator A
        (localCohomologyWithSupportInPlus.{u, v} A T K i) := by
  obtain ⟨a, haObj⟩ := K.property
  have : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).mp haObj
  have htop : ∀ i : ℤ, i < a → Module.annihilator A
      (localCohomologyWithSupportInPlus.{u, v} A T K i) = ⊤ := fun i hi ↦
    Module.annihilator_eq_top_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_localCohomologyWithSupportInPlus_of_lt.{u, v} A T K a i hi))
  have hcast : ((max (n - a + 1) 0).toNat : ℤ) = max (n - a + 1) 0 :=
    Int.toNat_of_nonneg (le_max_right (n - a + 1) 0)
  have hsub : ∀ i : ℤ, a ≤ i → i ≤ a + ((max (n - a + 1) 0).toNat : ℤ) - 1 →
      PrimeSpectrum.zeroLocus (Module.annihilator A
        (localCohomologyWithSupportInPlus.{u, v} A T K i) : Set A) ⊆ T := by
    intro i _ h₂
    have := hfin i (by omega)
    exact support_localCohomologyWithSupportInPlus_subset.{u, v} A T K i
  obtain ⟨J, hJT, hJ⟩ := exists_ideal_zeroLocus_subset_le_of_int A T a
    (fun i ↦ Module.annihilator A (localCohomologyWithSupportInPlus.{u, v} A T K i)) htop
    (max (n - a + 1) 0).toNat hsub
  exact ⟨J, hJT, fun i hi ↦ hJ i (by omega)⟩

/-- **Stacks 0EI1, the implication (1) ⟹ (3) for closed support.** Let `A` be a Noetherian ring,
let `I ⊆ A` be an ideal and write `Z = V(I)`, let `K` be an object of the bounded-below derived
category of `A`-modules and let `n ∈ ℤ`. If `H^i_Z(K)` is finite for every `i ≤ n`, then there is
an `e ≥ 0` such that `I ^ e` annihilates `H^i_Z(K)` for every `i ≤ n`.

The ideal produced by the implication `(1) ⟹ (2)` has zero locus inside `V(I)`, so `I` lies in
its radical and a power of `I` lies inside it. -/
@[stacks 0EI1 "the implication (1) ⟹ (3) for closed support T = V(I); (3) ⟹ (1) is not proved"]
theorem exists_pow_annihilator_localCohomologyWithSupportInPlus_of_finite (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (n : ℤ)
    (hfin : ∀ i : ℤ, i ≤ n → Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K i)) :
    ∃ e : ℕ, ∀ i : ℤ, i ≤ n → I ^ e ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A)) K i) :=
  (exists_annihilator_iff_exists_power_annihilator_plus.{u, v} A I K n).mp
    (exists_annihilator_localCohomologyWithSupportInPlus_of_finite.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K n hfin)

end Stacks.LocalCohomology

end
