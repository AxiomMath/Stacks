module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension
public import StacksFrontier.RingTheory.LocalCohomology.CechModel
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Faltings' annihilator theorem, read on the Čech complex

Let `k` be a field, `A` a finite type `k`-algebra, `M` a finite `A`-module, `g₁, …, g_r ∈ A`,
`Z = V(g₁, …, g_r)`, and let `f ∈ A` vanish on `Z`. Suppose that for every prime `𝔭` with
`f ∉ 𝔭` and every `𝔮 ∈ Z` containing `𝔭`

`depth(M_𝔭) + dim((A/𝔭)_𝔮) > σ + 1`.

Then some power of `f` annihilates the cohomology of the extended Čech complex `C^•(g; M)` in
every degree `j ≤ σ + 1`.

This is the claim at the start of the proof of [Stacks, Tag 0EL1]: Faltings' annihilator theorem
[Stacks, Tag 0EFC], applied with `T = Z` and `T' = V(f)`, gives an ideal `J` with `V(J) ⊆ V(f)`
annihilating `H^j_Z(M)` for `j ≤ σ + 1`; since `V(J) ⊆ V(f)`, a power of `f` lies in `J`; and
`H^j_Z(M)` is the cohomology of the Čech complex [Stacks, Tag 0A6R].

## Main results

* `Stacks.Algebraization.exists_pow_smul_cechHomology_eq_zero`: the statement above.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- An annihilation passes along a linear isomorphism of modules. -/
theorem smul_eq_zero_of_iso {A : Type u} [CommRing A] {P Q : ModuleCat.{u} A} (e : P ≅ Q)
    (a : A) (h : ∀ x : P, a • x = 0) (y : Q) : a • y = 0 := by
  have hy : y = e.hom (e.inv y) := by
    rw [← ConcreteCategory.comp_apply, e.inv_hom_id, ConcreteCategory.id_apply]
  rw [hy, ← map_smul, h, map_zero]

/-- **Faltings' annihilator theorem, read on the Čech complex.** For a finite type algebra `A`
over a field, a finite `A`-module `M`, a finite family `g` and an element `f` vanishing on
`V(g)`, the depth–dimension bound `> σ + 1` at the pairs `𝔭 ⊆ 𝔮` with `f ∉ 𝔭` and `𝔮 ∈ V(g)`
makes a power of `f` annihilate the cohomology of the extended Čech complex `C^•(g; M)` in every
degree `j ≤ σ + 1`. -/
theorem exists_pow_smul_cechHomology_eq_zero (k : Type u) [Field k] (A : Type u) [CommRing A]
    [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    {r : ℕ} (g : Fin r → A) (f : A) (hf : f ∈ (Ideal.span (Set.range g)).radical) (σ : ℕ)
    (hdepth : ∀ p q : PrimeSpectrum A, f ∉ p.asIdeal →
      q ∈ PrimeSpectrum.zeroLocus (Set.range g) → p.asIdeal ≤ q.asIdeal →
      depthAddRelativeDim A M p q > (((σ + 1 : ℕ) : ℤ) : EInt)) :
    ∃ c : ℕ, ∀ j : ℕ, j ≤ σ + 1 →
      ∀ x : (_root_.Cech.cechComplex g M).homology j, f ^ c • x = 0 := by
  set I : Ideal A := Ideal.span (Set.range g) with hIdef
  have hI : I.FG := by
    classical
    exact ⟨(Finset.univ.image g), by simp [hIdef]⟩
  set T : Set (PrimeSpectrum A) := PrimeSpectrum.zeroLocus (I : Set A)
  set T' : Set (PrimeSpectrum A) := PrimeSpectrum.zeroLocus ({f} : Set A)
  have hrad (J : Ideal A) : PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ↔ f ∈ J.radical := by
    rw [show T' = _ from (PrimeSpectrum.zeroLocus_span {f}).symm,
      PrimeSpectrum.zeroLocus_subset_zeroLocus_iff,
      Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  have hTT' : T ⊆ T' := (hrad I).2 hf
  have hsu (s : Set A) : StableUnderSpecialization (PrimeSpectrum.zeroLocus s) :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  have hT := hsu (I : Set A)
  have hT' := hsu ({f} : Set A)
  obtain ⟨omega, homega⟩ := exists_isDualizingComplex_of_finiteType_field k A
  obtain ⟨J, hJT', hJ⟩ :=
    (Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff A M T T' hTT' hT hT'
      ((σ + 1 : ℕ) : ℤ) (by positivity) omega homega).mpr fun p q hp hq hpq => by
        refine hdepth p q (fun hfp => hp ?_) ?_ hpq
        · simpa [T'] using hfp
        · have : q ∈ T := hq
          simpa [T, hIdef, PrimeSpectrum.zeroLocus_span] using this
  have hfJ : f ∈ J.radical := (hrad J).1 hJT'
  obtain ⟨c, hc⟩ := hfJ
  refine ⟨c, fun j hj x => ?_⟩
  have hann : ∀ y : Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) j,
      f ^ c • y = 0 :=
    fun y => Module.mem_annihilator.mp (hJ j (by exact_mod_cast hj) hc) y
  let e : Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) j ≅
      (_root_.Cech.cechComplex g M).homology j :=
    Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule A I hI
        (ModuleCat.of A M) j ≪≫
      Stacks.LocalCohomology.localCohomologyIsoExtendedCechHomology.{u, u} g (ModuleCat.of A M)
        I hI rfl j ≪≫
      HomologicalComplex.extendHomologyIso (_root_.Cech.cechComplex g (ModuleCat.of A M))
        ComplexShape.embeddingUpNat (by simp)
  exact smul_eq_zero_of_iso e _ hann x

end Stacks.Algebraization

end
