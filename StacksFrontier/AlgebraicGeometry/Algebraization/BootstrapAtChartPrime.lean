module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituationAtPoint
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapTransport
public import StacksFrontier.AlgebraicGeometry.Algebraization.ChartPrimePoint
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkChartComparison

/-!
# The bootstrap situation at a prime of a completed chart

In the situation of Stacks 0EHK — an algebraization situation with `A` local, `𝔪 = 𝔞`, a
dualizing complex, `d ≥ cd(A, I)`, and a finite module model `(M_n)` whose coherent adic system
satisfies the `(s, s + d)`-inequalities — fix a point `y ∈ U ∩ Y`, a chart `f ∉ 𝔭_y`, the
completed chart ring `B = (A_f)^∧_I`, the prime `𝔮` of `B` over `y` and a `B`-module `N` with
`N / Iⁿ⁺¹N ≅ (M_n)_f` compatibly (the chart vertex). The source's proof applies Stacks 0EFR at
`B_𝔮` with `s` replaced by `s - δ(y)`, "by assumption (3) via Lemma 0EJ4"; the per-point step of
this library reads it at the `I`-adic completion `(B_𝔮)^∧`, where Stacks 0EFR is available in
its canonical form. This file carries out that hypothesis check.

Stacks 0EJ4 (3) (`satisfiesDepthInequalities_iff_bootstrapSituation`) gives a bootstrap situation
over the completed local ring `𝒪_{U,y}^∧` with the completed stalk `ℱ_y^∧`. It is transported
(`BootstrapSituation.congr`) along `𝒪_{U,y}^∧ ≅ (B_𝔮)^∧` and `ℱ_y^∧ ≅ (N_𝔮)^∧`
(`completedStalkChartAddEquiv`).

## Main results

* `Stacks.Algebraization.exists_bootstrapSituation_chartCompletion` — the bootstrap situation over
  `(B_𝔮)^∧` with module `(N_𝔮)^∧`, locus the closed point and bounds `s - δ(y)` and `d`.
* `Stacks.Algebraization.exists_chartCompletionBootstrap` — the same, indexed by a prime
  `𝔮 ⊇ I B` of the completed chart ring rather than by a point, in the shape
  `Stacks.Algebraization.ChartCompletionBootstrap`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

section Transport

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (z : S.Y)
  (hyz : S.U.ι.base y = S.Yι.base z) (f : S.A)
  (hf : f ∉ (underlyingPrime S y).asIdeal) (hI : S.I ≤ (underlyingPrime S y).asIdeal)
  [(chartPrimeOfPoint S y f).IsPrime]
  (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (hM : IsFiniteModuleModel S M)
  {N : Type u} [AddCommGroup N]
  [Module (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
    (Localization.Away f)) N]
  [Module S.A N] [Module (Localization.Away f) N] [IsScalarTower S.A (Localization.Away f) N]
  [IsScalarTower (Localization.Away f)
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) N]
  [IsScalarTower S.A
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)) N]

/-- The localization `B_𝔮` of the completed chart ring at the prime over `y`. -/
abbrev chartLocalRing : Type u :=
  Localization.AtPrime (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
    (Ideal.map_mono hI)).asIdeal

/-- The localization `N_𝔮` of a module over the completed chart ring. -/
abbrev chartLocalModule : Type u :=
  LocalizedModule (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
    (Ideal.map_mono hI)).asIdeal.primeCompl N

/-- The ideal `I B_𝔮`. -/
abbrev chartLocalIdeal : Ideal (chartLocalRing S y f hI) :=
  ((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap (Localization.Away f)
    (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)))).map
      (algebraMap _ (chartLocalRing S y f hI))

/-- `I B_𝔮` lies in the maximal ideal of `B_𝔮`. -/
theorem chartLocalIdeal_le_maximalIdeal :
    chartLocalIdeal S y f hI ≤ maximalIdeal (chartLocalRing S y f hI) := by
  rw [chartLocalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono (map_le_adicPrimeOver _ _)

/-- The `I`-adic completion of `B_𝔮` is local. -/
private theorem isLocalRing_adicCompletion_chartLocalIdeal :
    IsLocalRing (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI)) :=
  Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal
    (chartLocalIdeal S y f hI) (chartLocalIdeal_le_maximalIdeal S y f hI)

/-- The `𝒪_{U,y}`-module structure of the formal stalk, read over `A` through
`baseToPointStalk`. -/
abbrev formalStalkModuleA (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    letI : Algebra S.A (S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
    Module S.A (formalStalk F y) :=
  letI : Algebra S.A (S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
  Module.compHom _ (algebraMap S.A (S.U.toScheme.presheaf.stalk y))

/-- An ideal extended from the base along an algebra equivalence. -/
theorem map_map_algEquiv_eq {A R₁ R₂ : Type*} [CommRing A] [CommRing R₁] [CommRing R₂]
    [Algebra A R₁] [Algebra A R₂] (σ : R₁ ≃ₐ[A] R₂) (I : Ideal A) :
    (I.map (algebraMap A R₁)).map (σ.toRingEquiv : R₁ →+* R₂) = I.map (algebraMap A R₂) := by
  rw [Ideal.map_map]
  congr 1
  ext a
  exact σ.commutes a

/-- The ideal `I 𝒪_{U,y}^∧` corresponds to `I (B_𝔮)^∧` under any `A`-algebra comparison. -/
theorem completedLocalIdeal_map_chartRingEquiv
    [Algebra S.A (S.U.toScheme.presheaf.stalk y)]
    (halg : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y)
    (σ : completedLocalRing (idealOnOpen S) y ≃ₐ[S.A]
      AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI)) :
    (completedLocalIdeal (idealOnOpen S) y).map
        (σ.toRingEquiv : completedLocalRing (idealOnOpen S) y →+* _) =
      (chartLocalIdeal S y f hI).map (algebraMap (chartLocalRing S y f hI)
        (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI))) := by
  have h0 : IdealSheafData.stalk (idealOnOpen S) y =
      S.I.map (algebraMap S.A (S.U.toScheme.presheaf.stalk y)) := by
    rw [stalk_idealOnOpen_eq_map, halg]
  have hst : completedLocalIdeal (idealOnOpen S) y =
      S.I.map (algebraMap S.A (completedLocalRing (idealOnOpen S) y)) := by
    refine (congrArg (Ideal.map (algebraMap (S.U.toScheme.presheaf.stalk y)
      (completedLocalRing (idealOnOpen S) y))) h0).trans ?_
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hst, map_map_algEquiv_eq, chartLocalIdeal]
  simp only [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

include hf hI hyz in
/-- **The bootstrap situation over the completion `(B_𝔮)^∧` of `B_𝔮`**, with module `(N_𝔮)^∧`,
locus the closed point and bounds `s - δ(y)` and `d`: the situation of Stacks 0EJ4 (3) at `y`,
transported along `𝒪_{U,y}^∧ ≅ (B_𝔮)^∧` and `ℱ_y^∧ ≅ (N_𝔮)^∧`. -/
theorem exists_bootstrapSituation_chartCompletion (s d : ℤ)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (hineq : SatisfiesDepthInequalities S (coherentAdicSystemOfFiniteModuleModel S M hM) s (s + d))
    (hδ : S.distanceToZ z ≠ ⊤)
    (e : ∀ n : ℕ, LocalizedModule (Submonoid.powers f) (M.obj (op n)) ≃ₗ[Localization.Away f]
      (N ⧸ (((S.I.map (algebraMap S.A (Localization.Away f))).map (algebraMap
        (Localization.Away f) (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)))) ^ (n + 1) •
        (⊤ : Submodule (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
          (Localization.Away f)) N))))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (z : LocalizedModule (Submonoid.powers f) (M.obj (op n))),
      AdicCompletion.transitionMap _ N (Nat.succ_le_succ h) (e n z) =
        e m (LocalizedModule.map (Submonoid.powers f) (M.map (homOfLE h).op).hom z)) :
    haveI := Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal
      (chartLocalIdeal S y f hI) (chartLocalIdeal_le_maximalIdeal S y f hI)
    ∃ B : BootstrapSituation.{u, u, u},
      B.A = AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI) ∧
      HEq B.commRing (inferInstance :
        CommRing (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI))) ∧
      HEq B.I ((chartLocalIdeal S y f hI).map (algebraMap (chartLocalRing S y f hI)
        (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI)))) ∧
      B.M = AdicCompletion (chartLocalIdeal S y f hI) (chartLocalModule S y f hI (N := N)) ∧
      HEq B.addCommGroup (inferInstance : AddCommGroup
        (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalModule S y f hI (N := N)))) ∧
      HEq B.module (inferInstance : Module
        (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI))
        (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalModule S y f hI (N := N)))) ∧
      HEq B.T ({closedPoint (AdicCompletion (chartLocalIdeal S y f hI)
        (chartLocalRing S y f hI))} : Set (PrimeSpectrum
          (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI)))) ∧
      B.s = s - ((S.distanceToZ z).toNat : ℤ) ∧ B.d = d := by
  let : Algebra S.A (S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
  have halg : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y := rfl
  have hloc := isLocalization_pointStalk S y halg
  let : Algebra (Localization.Away f) (S.U.toScheme.presheaf.stalk y) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f)
      (S.U.toScheme.presheaf.stalk y) (Submonoid.powers f) (underlyingPrime S y).asIdeal.primeCompl
      (powers_le_primeCompl S y f hf)
  have : IsScalarTower S.A (Localization.Away f) (S.U.toScheme.presheaf.stalk y) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f)
      (S.U.toScheme.presheaf.stalk y) (Submonoid.powers f) (underlyingPrime S y).asIdeal.primeCompl
      (powers_le_primeCompl S y f hf)
  let := formalStalkModuleA S y (coherentAdicSystemOfFiniteModuleModel S M hM)
  have : IsScalarTower S.A (S.U.toScheme.presheaf.stalk y)
      (formalStalk (coherentAdicSystemOfFiniteModuleModel S M hM) y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨σ, ψ, hσ⟩ := exists_completedLocalRing_chartRingEquiv S y f hf hI
    (chartLocalRing S y f hI) halg
  let e' := completedStalkChartAddEquiv S y f hf hI M (chartLocalRing S y f hI)
    (LocalizedModule.mkLinearMap (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
      (Ideal.map_mono hI)).asIdeal.primeCompl N) e halg hM he
  have he' := completedStalkChartAddEquiv_smul S y f hf hI M (chartLocalRing S y f hI)
    (LocalizedModule.mkLinearMap (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
      (Ideal.map_mono hI)).asIdeal.primeCompl N) e halg hM he σ ψ hσ
  have hB := (satisfiesDepthInequalities_iff_bootstrapSituation.{u, u} S
    (coherentAdicSystemOfFiniteModuleModel S M hM) s d hcd hdual).mp hineq y z hyz hδ
  obtain ⟨B, hlocal, -, hBT, hBA, hBcomm, hBI, hBM, hBadd, hBmod, hBs, hBd⟩ :=
    exists_bootstrapSituation_closedPoint S (coherentAdicSystemOfFiniteModuleModel S M hM) s d
      y z hyz hB
  cases B
  rename_i A bc bn bI bM ba bmod bf bT bsub bstable bs bd bdual bcd bdepth bcomp
  cases hBA
  cases hBcomm
  cases hBI
  cases hBM
  cases hBadd
  cases hBmod
  let B0 : BootstrapSituation.{u, u, u} :=
    { A := completedLocalRing (idealOnOpen S) y
      commRing := inferInstance
      isNoetherianRing := bn
      I := completedLocalIdeal (idealOnOpen S) y
      M := completedStalk (idealOnOpen S) (coherentAdicSystemOfFiniteModuleModel S M hM) y
      addCommGroup := inferInstance
      module := inferInstance
      finite := bf
      T := bT
      subset_adicLocus := bsub
      stableUnderSpecialization := bstable
      s := bs
      d := bd
      dualizing := bdual
      cohomologicalDimension_le := bcd
      depth_or_depth_add_dimension := bdepth
      completedLocalDepth := bcomp }
  have := isLocalRing_adicCompletion_chartLocalIdeal S y f hI
  have hIeq : B0.I.map (σ.toRingEquiv : B0.A →+* _) = (chartLocalIdeal S y f hI).map
      (algebraMap (chartLocalRing S y f hI)
        (AdicCompletion (chartLocalIdeal S y f hI) (chartLocalRing S y f hI))) :=
    completedLocalIdeal_map_chartRingEquiv S y f hI halg σ
  have : IsLocalRing (completedLocalRing (idealOnOpen S) y) :=
    isLocalRing_completedLocalRing S y z hyz
  have hTeq : ∀ r : PrimeSpectrum (AdicCompletion (chartLocalIdeal S y f hI)
      (chartLocalRing S y f hI)), PrimeSpectrum.comap
      (σ.toRingEquiv : B0.A →+* _) r ∈ B0.T ↔ r = closedPoint _ := by
    intro r
    have hBT' : B0.T = {closedPoint (completedLocalRing (idealOnOpen S) y)} := hBT
    rw [hBT', Set.mem_singleton_iff]
    have hc := IsLocalRing.comap_closedPoint
      (σ.toRingEquiv : completedLocalRing (idealOnOpen S) y →+* AdicCompletion
        (chartLocalIdeal S y f hI) (chartLocalRing S y f hI))
    refine ⟨fun h => PrimeSpectrum.comap_injective_of_surjective _ σ.toRingEquiv.surjective
      (h.trans hc.symm), ?_⟩
    rintro rfl
    exact hc
  refine ⟨BootstrapSituation.congr B0 σ.toRingEquiv e' he', rfl, HEq.rfl,
    heq_of_eq ((BootstrapSituation.congr_I B0 σ.toRingEquiv e' he').trans hIeq), rfl, HEq.rfl,
    HEq.rfl, heq_of_eq (Set.ext hTeq), hBs, hBd⟩

end Transport

section ChartPrime

variable (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (f : S.A)
  (N : Type u) [AddCommGroup N] [Module (chartRing S f) N]
  [Module S.A N] [Module (Localization.Away f) N] [IsScalarTower S.A (Localization.Away f) N]
  [IsScalarTower (Localization.Away f) (chartRing S f) N] [IsScalarTower S.A (chartRing S f) N]

/-- **The bootstrap situation over the completion of `B_𝔮`**, at a prime `𝔮 ⊇ I B` of the
completed chart ring `B = chartRing S f`: a bootstrap situation (Stacks 0EFU) whose ring is the
`I`-adic completion of `B_𝔮`, which is local and complete, whose module is the completion of
`N_𝔮`, whose locus is the closed point and whose bounds are `s - δ` and `d`. -/
def ChartCompletionBootstrap (s d : ℤ) (δ : ℕ) (q : PrimeSpectrum (chartRing S f)) : Prop :=
  ∃ (B : BootstrapSituation.{u, u, u}) (_ : IsLocalRing B.A) (_ : IsAdicComplete B.I B.A),
    B.A = AdicCompletion ((chartIdeal S f).map (algebraMap _ (Localization.AtPrime q.asIdeal)))
      (Localization.AtPrime q.asIdeal) ∧
    HEq B.commRing (inferInstance : CommRing (AdicCompletion ((chartIdeal S f).map
      (algebraMap _ (Localization.AtPrime q.asIdeal))) (Localization.AtPrime q.asIdeal))) ∧
    HEq B.I (((chartIdeal S f).map (algebraMap _ (Localization.AtPrime q.asIdeal))).map
      (algebraMap (Localization.AtPrime q.asIdeal) (AdicCompletion ((chartIdeal S f).map
        (algebraMap _ (Localization.AtPrime q.asIdeal))) (Localization.AtPrime q.asIdeal)))) ∧
    B.M = AdicCompletion ((chartIdeal S f).map (algebraMap _ (Localization.AtPrime q.asIdeal)))
      (LocalizedModule q.asIdeal.primeCompl N) ∧
    HEq B.addCommGroup (inferInstance : AddCommGroup (AdicCompletion ((chartIdeal S f).map
      (algebraMap _ (Localization.AtPrime q.asIdeal))) (LocalizedModule q.asIdeal.primeCompl N))) ∧
    HEq B.module (inferInstance : Module (AdicCompletion ((chartIdeal S f).map
      (algebraMap _ (Localization.AtPrime q.asIdeal))) (Localization.AtPrime q.asIdeal))
      (AdicCompletion ((chartIdeal S f).map (algebraMap _ (Localization.AtPrime q.asIdeal)))
        (LocalizedModule q.asIdeal.primeCompl N))) ∧
    (∀ hloc : IsLocalRing B.A, B.T = {@closedPoint B.A B.commRing.toCommSemiring hloc}) ∧
    B.s = s - δ ∧ B.d = d

/-- **Stacks 0EJ4 (3) read at a prime of a completed chart** — the hypothesis check of the
per-point paragraph of the proof of Stacks 0EHK. Under the hypotheses of Stacks 0EHK, for a chart
`f ∈ 𝔞`, a chart vertex `N` with levels `N / Iⁿ⁺¹N ≅ (M_n)_f` and a prime `𝔮 ⊇ I B`, with `z` the
point of `Y` under `𝔮`, the completion of `B_𝔮` carries a bootstrap situation with module the
completion of `N_𝔮`, locus the closed point and bounds `s - δ^Y_Z(z)` and `d`. -/
theorem exists_chartCompletionBootstrap [IsLocalRing S.A]
    (hmax : IsLocalRing.maximalIdeal S.A = S.a) (hM : IsFiniteModuleModel S M) (s d : ℤ)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (hineq : SatisfiesDepthInequalities S (coherentAdicSystemOfFiniteModuleModel S M hM) s (s + d))
    (hf : f ∈ S.a)
    (e : ∀ n : ℕ, LocalizedModule (Submonoid.powers f) (M.obj (op n)) ≃ₗ[Localization.Away f]
      (N ⧸ (chartIdeal S f ^ (n + 1) • (⊤ : Submodule (chartRing S f) N))))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : LocalizedModule (Submonoid.powers f) (M.obj (op n))),
      AdicCompletion.transitionMap _ N (Nat.succ_le_succ h) (e n x) =
        e m (LocalizedModule.map (Submonoid.powers f) (M.map (homOfLE h).op).hom x))
    (q : PrimeSpectrum (chartRing S f)) (hq : chartIdeal S f ≤ q.asIdeal) :
    ∃ z : S.Y, S.Yι.base z = PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q ∧
      ChartCompletionBootstrap S f N s d (S.distanceToZ z).toNat q := by
  set P := PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q with hP
  have hPa : ¬ S.a ≤ P.asIdeal := not_le_comap_chartRing q hf
  have hPI : S.I ≤ P.asIdeal := le_comap_chartRing q hq
  let y := pointOfPrime S P hPa
  let z := pointOfPrimeY S P hPI
  have hyz : S.U.ι.base y = S.Yι.base z := base_pointOfPrime_eq S P hPa hPI
  have hfy : f ∉ (underlyingPrime S y).asIdeal := notMem_comap_chartRing q
  have := isPrime_chartPrimeOfPoint S y f hfy
  have : (Ideal.map (algebraMap S.A (Localization.Away f)) P.asIdeal).IsPrime :=
    isPrime_chartPrimeOfPoint S y f hfy
  have hδ : S.distanceToZ z ≠ ⊤ := distanceToZ_ne_top S hmax z
  refine ⟨z, Yι_base_pointOfPrimeY S P hPI, ?_⟩
  obtain ⟨B, hBA, hBc, hBI, hBM, hBadd, hBmod, hBT, hBs, hBd⟩ :=
    exists_bootstrapSituation_chartCompletion S y z hyz f hfy hPI M hM s d hdual hcd hineq hδ e he
  have hq' : q = adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
      (Ideal.map_mono hPI) := eq_completedChartPrime_pointOfPrime q hf hq
  revert B
  rw [hq']
  intro B hBA hBc hBI hBM hBadd hBmod hBT hBs hBd
  cases B
  rename_i A bc bn bI bM ba bmod bf bT bsub bstable bs bd bdual bcd bdepth bcomp
  cases hBA
  cases hBc
  cases hBI
  cases hBM
  cases hBadd
  cases hBmod
  cases hBT
  have hloc := isLocalRing_adicCompletion_chartLocalIdeal S y f hPI
  have hcomp : IsAdicComplete ((chartLocalIdeal S y f hPI).map (algebraMap _
      (AdicCompletion (chartLocalIdeal S y f hPI) (chartLocalRing S y f hPI))))
      (AdicCompletion (chartLocalIdeal S y f hPI) (chartLocalRing S y f hPI)) :=
    AdicCompletion.isAdicComplete_self _ (Ideal.fg_of_isNoetherianRing _)
  exact ⟨_, hloc, hcomp, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, fun _ => rfl, hBs, hBd⟩

end ChartPrime

end Stacks.Algebraization

end
