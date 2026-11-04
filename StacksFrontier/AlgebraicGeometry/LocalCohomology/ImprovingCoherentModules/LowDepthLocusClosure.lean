module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSemilinearLocalization
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSpecialization

import all StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence

/-!
# The closure of the locus of small depth

Let `A` be a Noetherian ring with a dualizing complex, let `T ⊆ Spec(A)` be stable under
specialization and let `M` be a finite `A`-module such that `depth(M_𝔭) ≥ 1` at every prime
`𝔭 ∉ T` admitting an immediate specialization into `T`.  Then the closure of

`B = {𝔭 ∈ T : depth(M_𝔭) ≤ 1}`

is again contained in `T`.  This module also identifies the depth of the stalk of a
quasi-coherent module at a point of an affine open with the depth of the localization of its
sections there.

Without a dualizing complex, for a closed subset `Z` along which `M` has positive depth, the
closure of a set of primes of `Z` of depth at most one is the union of the closures of its
points.

## Main results

* `Stacks.Algebraization.closure_lowDepth_subset_of_isDualizingComplex`: the closure of the
  locus of depth at most one inside `T` stays inside `T`.
* `Stacks.Algebraization.closure_lowDepth_subset_specializations`: inside a closed subset along
  which the depth is positive, every point of the closure of a set of points of depth at most one
  specializes from a point of that set.
* `Stacks.ModuleStalkSpecialization.depth_stalk_eq_depth_localizedModule`: the depth of the
  stalk of a quasi-coherent module at a point of an affine open is the depth of the
  localization of its sections at the corresponding prime.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0DWY](https://stacks.math.columbia.edu/tag/0DWY)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
open Stacks.Algebraization (enatToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- A depth value which is not at least two is the value of `0` or `1`, and in particular is
finite. -/
private theorem exists_eq_le_one_of_not_two_le {e : ℕ∞} (h : ¬ (2 : ℕ∞) ≤ e) :
    ∃ n : ℕ, e = (n : ℕ∞) ∧ (n : ℤ) ≤ 1 := by
  induction e using ENat.recTopCoe with
  | top => exact absurd le_top h
  | coe n =>
    refine ⟨n, rfl, ?_⟩
    have : n < 2 := by exact_mod_cast lt_of_not_ge h
    lia

/-- A prime in the closure (inside `V(p)`) of a set of primes of depth at most one, but not in the
set itself, has depth zero. -/
private theorem not_one_le_depth_of_mem_closure {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (B : Set (PrimeSpectrum A))
    (hB : ∀ q ∈ B, ¬ (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime q.asIdeal)
      (maximalIdeal (Localization.AtPrime q.asIdeal))
      (LocalizedModule q.asIdeal.primeCompl M))
    (hp : (⟨p, fun _ hx => hx⟩ : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) ∈
      closure (Subtype.val ⁻¹' B : Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))))
    (hpB : p ∉ B) :
    ¬ (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) := by
  have hlt := depth_lt_of_mem_closure_of_bounded_depth (M := M) p 1 (Subtype.val ⁻¹' B)
    (fun q hq => (enatToEInt_le_intCast_iff _ 1).mpr (exists_eq_le_one_of_not_two_le (hB _ hq)))
    hp hpB
  obtain ⟨n, hn, -⟩ := (enatToEInt_le_intCast_iff _ 1).mp hlt.le
  rw [hn] at hlt ⊢
  have hn1 : ((n : ℤ) : EInt) < ((1 : ℤ) : EInt) := by simpa [enatToEInt] using hlt
  have hn0 : n < 1 := by exact_mod_cast WithBotTop.coe_lt_coe.mp hn1
  simp only [Nat.lt_one_iff] at hn0
  simp [hn0]

/-- **The closure of the locus of depth at most one inside `T` stays inside `T`.**  Let `A` be a
Noetherian ring with a dualizing complex `K`, let `T ⊆ Spec(A)` be stable under specialization
and let `M` be a finite `A`-module with `depth(M_𝔭) ≥ 1` at every prime `𝔭 ∉ T` admitting an
immediate specialization into `T`.  Then the closure of the set of primes of `T` at which the
depth of `M` is at most one is contained in `T`. -/
public theorem closure_lowDepth_subset_of_isDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (himm : ∀ p q : PrimeSpectrum A, IsImmediateSpecialization p q → q ∈ T → p ∉ T →
      (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) :
    closure {p : PrimeSpectrum A | p ∈ T ∧
        ¬ (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)} ⊆ T := by
  classical
  set d : PrimeSpectrum A → ℕ∞ := fun p => Module.depth (Localization.AtPrime p.asIdeal)
    (maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule p.asIdeal.primeCompl M) with hd
  set B : Set (PrimeSpectrum A) := {p : PrimeSpectrum A | p ∈ T ∧ ¬ (2 : ℕ∞) ≤ d p} with hB
  refine closure_subset_of_generic_mem B T hT ?_
  intro p hp
  by_cases hpB : p ∈ B
  · exact hpB.1
  have hdp := not_one_le_depth_of_mem_closure (M := M) p B (fun q hq => hq.2) hp hpB
  by_contra hpT
  have hex : ∃ q : PrimeSpectrum A, q ∈ B ∧ IsImmediateSpecialization p q := by
    by_contra hcontra
    have hsub : (Subtype.val '' (Subtype.val ⁻¹' B :
          Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)))) ⊆
        {r : PrimeSpectrum A | ∃ n : ℕ, d r = (n : ℕ∞) ∧
          (n : ℤ) + Dualizing.dualizingDimension K r ≤
            Dualizing.dualizingDimension K p - 1} := by
      rintro - ⟨q, hqB, rfl⟩
      obtain ⟨n, hn, hn1⟩ := exists_eq_le_one_of_not_two_le hqB.2
      refine ⟨n, hn, ?_⟩
      have hpr : p ⤳ (q : PrimeSpectrum A) :=
        (PrimeSpectrum.le_iff_specializes p (q : PrimeSpectrum A)).mp q.2
      have hne : p ≠ (q : PrimeSpectrum A) := fun he => hpB (he ▸ hqB)
      obtain ⟨s, hps, hsr, hsp, hsr'⟩ :
          ∃ s : PrimeSpectrum A, p ⤳ s ∧ s ⤳ (q : PrimeSpectrum A) ∧ s ≠ p ∧
            s ≠ (q : PrimeSpectrum A) := by
        by_contra hcon
        refine hcontra ⟨(q : PrimeSpectrum A), hqB, hpr, hne, fun s hps hsr => ?_⟩
        by_cases h1 : s = p
        · exact Or.inl h1
        · by_cases h2 : s = (q : PrimeSpectrum A)
          · exact Or.inr h2
          · exact absurd ⟨s, hps, hsr, h1, h2⟩ hcon
      have h1 : Dualizing.dualizingDimension K s < Dualizing.dualizingDimension K p :=
        Dualizing.dualizingDimension_lt_of_specializes K hK hps (Ne.symm hsp)
      have h2 : Dualizing.dualizingDimension K (q : PrimeSpectrum A) <
          Dualizing.dualizingDimension K s :=
        Dualizing.dualizingDimension_lt_of_specializes K hK hsr hsr'
      lia
    have hpmem : p ∈ closure (Subtype.val '' (Subtype.val ⁻¹' B :
        Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)))) := by
      rwa [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] at hp
    obtain ⟨n, -, hnc⟩ :=
      (isClosed_depth_add_dualizingDimension_sublevel K hK
        (Dualizing.dualizingDimension K p - 1)).closure_subset_iff.mpr hsub hpmem
    lia
  obtain ⟨q, hqB, hqimm⟩ := hex
  exact hdp (himm p q hqimm hqB.1 hpT)

/-- **A set of small depth along a closed set of positive depth is closed under the closure only
through its own specializations.**  Let `A` be a Noetherian ring, `M` a finite `A`-module and
`Z ⊆ Spec(A)` a closed subset at every point of which `depth(M_𝔭) ≥ 1`.  If `B ⊆ Z` consists of
primes at which `depth(M_𝔭) ≤ 1`, then every point of the closure of `B` is a specialization of
a point of `B`: the closure of `B` is the union of the closures of its points. -/
public theorem closure_lowDepth_subset_specializations
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (Z : Set (PrimeSpectrum A)) (hZ : IsClosed Z)
    (hdepth : ∀ p ∈ Z, (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M))
    (B : Set (PrimeSpectrum A)) (hBZ : B ⊆ Z)
    (hB : ∀ p ∈ B, ¬ (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M)) :
    closure B ⊆ {q | ∃ p ∈ B, p ⤳ q} := by
  classical
  set d : PrimeSpectrum A → ℕ∞ := fun p => Module.depth (Localization.AtPrime p.asIdeal)
    (maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule p.asIdeal.primeCompl M) with hd
  have hT : StableUnderSpecialization {q : PrimeSpectrum A | ∃ p ∈ B, p ⤳ q} :=
    fun q q' hqq' ⟨p, hp, hpq⟩ => ⟨p, hp, hpq.trans hqq'⟩
  refine closure_subset_of_generic_mem B _ hT ?_
  intro p hp
  by_cases hpB : p ∈ B
  · exact ⟨p, hpB, specializes_rfl⟩
  exfalso
  have hdp := not_one_le_depth_of_mem_closure (M := M) p B hB hp hpB
  have hpcl : p ∈ closure B := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] at hp
    exact closure_mono (Set.image_preimage_subset _ _) hp
  exact hdp (hdepth p (closure_minimal hBZ hZ hpcl))

end Stacks.Algebraization

namespace Stacks.ModuleStalkSpecialization

variable {X : Scheme.{u}}

/-- **The depth of the stalk is the depth of the localized sections.**  For a quasi-coherent
`𝒪_X`-module `F`, an affine open `U` and a point `y` of `U`, the depth of the stalk `F_y` over
the local ring `𝒪_{X, y}` is the depth of `Γ(F, U)_𝔭` over `Γ(X, U)_𝔭`, where `𝔭` is the prime
of `Γ(X, U)` corresponding to `y`. -/
public theorem depth_stalk_eq_depth_localizedModule (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (y : U) :
    letI := stalkModule F (y : X)
    Module.depth (X.presheaf.stalk (y : X)) (maximalIdeal (X.presheaf.stalk (y : X)))
        (F.presheaf.stalk (y : X)) =
      Module.depth (Localization.AtPrime (hU.primeIdealOf y).asIdeal)
        (maximalIdeal (Localization.AtPrime (hU.primeIdealOf y).asIdeal))
        (LocalizedModule (hU.primeIdealOf y).asIdeal.primeCompl Γ(F, U)) := by
  let := (X.presheaf.germ U (y : X) y.2).hom.toAlgebra
  let := stalkModule F (y : X)
  let := sectionsStalkModule F y.2
  exact Module.depth_maximalIdeal_eq_of_semilinearEquiv (stalkRingEquiv hU y.2)
    (stalkLinearEquiv F hU y.2).toAddEquiv (stalkLinearEquiv_smul F hU y.2)

end Stacks.ModuleStalkSpecialization

end
