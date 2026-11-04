module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartVertex
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.EssentialConstancyModFiniteLengthCharts
public import StacksFrontier.RingTheory.Noetherian.DirectSystemTransitionImageKernelEnlarge

/-!
# Stacks 0EHK: the essential constancy of the `Ext` system, reduced to the points of the charts

Let `(M_n)` be a finite module model over a Noetherian local ring `A` with `𝔞 = 𝔪`, and `ω` a
dualizing complex. This file reduces the essential constancy modulo finite length of the system
`n ↦ Ext^{-i}_A(M_n, ω)` (`Stacks.Algebraization.dualizingExtSystem`) to a statement at the
primes `𝔮 ⊇ I B` of the completed chart rings `B = (A_f)^∧_{I A_f}`, for `f ∈ 𝔪`: that the
kernel of `Ext^{-i}_B(X/I^{n+1}X, ω_B) → Ext^{-i}_B(X, ω_B)`, `X` the chart vertex, dies in a
later term after localizing at `𝔮`. That is the globalisation in the last paragraph of the
source's proof; the statement at `𝔮` is its per-point paragraph.

## Main results

* `Stacks.Algebraization.exists_range_eq_chartTransport_of_forall_prime` — over one chart.
* `Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_chartPrimes`
  — over all charts.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)

/-- The per-point condition over the chart `D(f)`: at every prime `𝔮 ⊇ I B` of the completed
chart ring, the kernel of `β_n : Ext^{-i}_B(X/I^{n+1}X, ω_B) → Ext^{-i}_B(X, ω_B)` dies in a later
term after localizing at `𝔮`. -/
public def ChartPrimeKernelCondition (f : S.A) (ω : DerivedCategory (ModuleCat.{u} S.A))
    (i : ℤ) : Prop :=
  ∀ (n : ℕ) (q : PrimeSpectrum (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f))),
    (S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap (Localization.Away f)
      (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)))
        ≤ q.asIdeal →
    ∃ (m : ℕ) (h : n ≤ m), q ∉ Module.support _
      (LinearMap.range (((dualizingExtSystem (chartVertexTower S M f)
          (chartTransportComplex S.I f ω) i).map (homOfLE h)).hom ∘ₗ
        (LinearMap.ker (chartCocone S M f (chartTransportComplex S.I f ω) i n)).subtype))

/-- **Over one chart, the images of the transition maps of the transported `Ext` system stop
growing**, granted the per-point condition. -/
public theorem exists_range_eq_chartTransport_of_forall_prime (hM : IsFiniteModuleModel S M)
    (f : S.A) (hf : f ∈ S.a) (ω : DerivedCategory (ModuleCat.{u} S.A))
    (hω : Dualizing.IsDualizingComplex ω) (i : ℤ)
    (hzero : ChartPrimeKernelCondition S M f ω i) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range ((dualizingExtSystem (chartTransportSystem S.I f M)
          (chartTransportComplex S.I f ω) i).map (homOfLE hmn)).hom =
        LinearMap.range ((dualizingExtSystem (chartTransportSystem S.I f M)
          (chartTransportComplex S.I f ω) i).map (homOfLE (hm.trans hmn))).hom := by
  let B := AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)
  let ωB := chartTransportComplex S.I f ω
  have hωB : Dualizing.IsDualizingComplex ωB := isDualizingComplex_chartTransportComplex S.I f ω hω
  let D := dualizingExtSystem (chartVertexTower S M f) ωB i
  have hfinN : Module.Finite B (chartVertex S M f) :=
    finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel S M hM hf
  have hfinT : ∀ n : ℕ, Module.Finite B ((chartVertexTower S M f).obj (op n)) := fun n =>
    Module.Finite.quotient B _
  have hNoeth : ∀ n : ℕ, IsNoetherian B (D.obj n) := fun n => by
    have := finite_dualizingExtSystem (chartVertexTower S M f) hfinT ωB hωB i n
    infer_instance
  have : Module.Finite B ((dualizingExtFunctor ωB i).obj (op (chartVertex S M f))) :=
    finite_dualizingExtFunctor_obj _ hfinN ωB hωB i
  have hann : ∀ n : ℕ, ∃ k : ℕ,
      ((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap _ B)) ^ k •
        (⊤ : Submodule B (D.obj n)) = ⊥ := fun n =>
    ⟨n + 1, smul_top_dualizingExtSystem_eq_bot _ ωB i n (pow_smul_top_quotient_eq_bot _ _ _)⟩
  obtain ⟨a, ha⟩ := Stacks.exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus_of_ker_le
    D hNoeth _ hann (chartCocone S M f ωB i) (fun m n h => chartCocone_comp S M f ωB i h)
    (fun n => LinearMap.ker (chartCocone S M f ωB i n)) (fun n => le_rfl) hzero
  refine ⟨a, fun m hm => ?_⟩
  obtain ⟨k, hk⟩ := ha m hm
  refine ⟨k, fun n hmn hkn => ?_⟩
  exact (range_map_eq_iff_of_iso (dualizingExtSystemMapIso
    (chartTransportSystemIsoTower S M f hM hf) ωB i) hmn (hm.trans hmn)).mpr (hk n hmn hkn)

/-- **Stacks 0EHK, the globalisation.** Over a Noetherian local ring with `𝔞 = 𝔪`, for a finite
module model and a dualizing complex, the `Ext` system is essentially constant modulo modules of
finite length as soon as the per-point condition holds over every chart `D(f)`, `f ∈ 𝔪`. -/
public theorem isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_chartPrimes
    [IsLocalRing S.A] (hmax : IsLocalRing.maximalIdeal S.A = S.a) (hM : IsFiniteModuleModel S M)
    (ω : DerivedCategory (ModuleCat.{u} S.A)) (hω : Dualizing.IsDualizingComplex ω) (i : ℤ)
    (hpoint : ∀ f : S.A, f ∈ S.a → ChartPrimeKernelCondition S M f ω i) :
    IsEssentiallyConstantModFiniteLength S.A S.I (dualizingExtSystem M ω i) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal S.A))
  have hfa : ∀ j, f j ∈ S.a := fun j => hmax ▸ (hf ▸ Ideal.subset_span ⟨j, rfl⟩)
  refine isEssentiallyConstantModFiniteLength_of_chart S.I (dualizingExtSystem M ω i)
    (finite_dualizingExtSystem M hM.1 ω hω i)
    (fun n => ⟨n + 1, smul_top_dualizingExtSystem_eq_bot M ω i n (hM.2.1 n)⟩) f hf
    fun j => ?_
  exact exists_localized₀_range_eq_of_chartTransport S.I (f j) M hM.1
    (fun n => ⟨n + 1, hM.2.1 n⟩) ω hω i
    (exists_range_eq_chartTransport_of_forall_prime S M hM (f j) (hfa j) ω hω i
      (hpoint (f j) (hfa j)))

end Stacks.Algebraization

end
