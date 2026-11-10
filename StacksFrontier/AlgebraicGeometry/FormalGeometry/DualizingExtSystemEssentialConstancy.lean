module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemPointTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartReduction
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapAtChartPrime
public import StacksFrontier.AlgebraicGeometry.Algebraization.ClosedFibreAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCanonicalAdicQuotientRange
public import StacksFrontier.RingTheory.Dualizing.NormalizedShiftFlatLocal

/-!
# Stacks 0EHK: the `Ext` system of a finite module model is essentially constant

In the situation of [Stacks, Tag 0EHK] — an algebraization situation over a Noetherian local
ring `(A, 𝔪)` with `𝔞 = 𝔪`, a finite module model `(M_n)` whose coherent adic system satisfies
the `(s, s + d)`-inequalities, `d ≥ cd(A, I)` and a normalized dualizing complex `ω` — the
inverse system `n ↦ Ext^{-i}_A(M_n, ω)` is essentially constant modulo modules of finite length
for every `i ≤ s`. This is the core of the source's proof.

The globalisation over the charts `D(f)`, `f ∈ 𝔪`, is
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_chartPrimes`;
it leaves a condition at each prime `𝔮 ⊇ I B` of a completed chart ring `B = (A_f)^∧`. There the
source applies [Stacks, Tag 0EFR] to `B_𝔮` with `s` replaced by `s - δ(y)` (the hypothesis check
is `Stacks.Algebraization.exists_chartCompletionBootstrap`), and dualizes by local duality at
`(B_𝔮)^∧` (`Stacks.Algebraization.exists_notMem_support_range_ker_of_localDuality`), in the degree
`i - dim(A/𝔭)` in which the transported dualizing complex is normalized.

## Main results

* `Stacks.Algebraization.chartVertexLevel` — the levels `(M_n)_f ≅ X/I^{n+1}X` of the chart
  vertex.
* `Stacks.Algebraization.isNormalizedDualizingComplex_pointCompletionComplex` — the transported
  dualizing complex over `(B_𝔮)^∧`, shifted by `dim(A/𝔭)`, is normalized.
* `Stacks.Algebraization.chartPrimeKernelCondition` — the per-point condition over every chart.
* `Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem` — the
  essential constancy.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

section Levels

variable (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) (f : S.A)

/-- A quotient of a `B`-module restricted to `A_f` is the quotient with its own `A_f`-action. -/
public def restrictScalarsQuotientEquiv {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    {N : Type u} [AddCommGroup N] [Module T N] [Module R N] [IsScalarTower R T N]
    (p : Submodule T N) :
    ((ModuleCat.restrictScalars.{u} (algebraMap R T)).obj (ModuleCat.of T (N ⧸ p))) ≃ₗ[R]
      (N ⧸ p) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (algebraMap R T a • y) = Submodule.Quotient.mk (a • y)
      rw [algebraMap_smul]
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The levels of the chart vertex**: `(M_n)_f ≅ X / I^{n+1} X`, for `X` the chart vertex. -/
public def chartVertexLevel (hM : IsFiniteModuleModel S M) (hf : f ∈ S.a) (n : ℕ) :
    LocalizedModule (Submonoid.powers f) (M.obj (op n)) ≃ₗ[Localization.Away f]
      ((chartVertex S M f) ⧸
        (chartIdeal S f ^ (n + 1) • (⊤ : Submodule (chartRing S f) (chartVertex S M f)))) :=
  (Shrink.linearEquiv (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) (M.obj (op n)))).symm ≪≫ₗ
    ((localizedModuleFunctorAdicQuotientNatIso S M hM hf).app (op n)).symm.toLinearEquiv ≪≫ₗ
    restrictScalarsQuotientEquiv _

/-- The localization functor on morphisms, read through `Shrink`, is `LocalizedModule.map`. -/
public theorem localizedModuleFunctor_map_symm_shrink {R : Type u} [CommRing R] (T : Submonoid R)
    {X Y : ModuleCat.{u} R} (g : X ⟶ Y) (x : LocalizedModule T X) :
    ((ModuleCat.localizedModuleFunctor T).map g).hom
        ((Shrink.linearEquiv (Localization T) (LocalizedModule T X)).symm x) =
      (Shrink.linearEquiv (Localization T) (LocalizedModule T Y)).symm
        (LocalizedModule.map T g.hom x) := by
  let F₁ : LocalizedModule T X →ₗ[R] Y.localizedModule T :=
    IsLocalizedModule.map T (X.localizedModuleMkLinearMap T) (Y.localizedModuleMkLinearMap T)
        g.hom ∘ₗ (Shrink.linearEquiv R (LocalizedModule T X)).symm.toLinearMap
  let F₂ : LocalizedModule T X →ₗ[R] Y.localizedModule T :=
    (Shrink.linearEquiv R (LocalizedModule T Y)).symm.toLinearMap ∘ₗ
      (LocalizedModule.map T g.hom).restrictScalars R
  have hF : F₁ = F₂ := by
    refine IsLocalizedModule.linearMap_ext T (LocalizedModule.mkLinearMap T X)
      (Y.localizedModuleMkLinearMap T) (LinearMap.ext fun m => ?_)
    change IsLocalizedModule.map T (X.localizedModuleMkLinearMap T)
        (Y.localizedModuleMkLinearMap T) g.hom (X.localizedModuleMkLinearMap T m) = _
    rw [IsLocalizedModule.map_apply]
    change _ = (Shrink.linearEquiv R (LocalizedModule T Y)).symm
      (LocalizedModule.map T g.hom (LocalizedModule.mk m 1))
    rw [LocalizedModule.map_mk]
    rfl
  exact LinearMap.congr_fun hF x

/-- The levels of the chart vertex are compatible with the transition maps. -/
public theorem chartVertexLevel_transition (hM : IsFiniteModuleModel S M) (hf : f ∈ S.a)
    {m n : ℕ} (h : m ≤ n) (x : LocalizedModule (Submonoid.powers f) (M.obj (op n))) :
    AdicCompletion.transitionMap _ (chartVertex S M f) (Nat.succ_le_succ h)
        (chartVertexLevel S M f hM hf n x) =
      chartVertexLevel S M f hM hf m
        (LocalizedModule.map (Submonoid.powers f) (M.map (homOfLE h).op).hom x) := by
  have hnat := (localizedModuleFunctorAdicQuotientNatIso S M hM hf).inv.naturality_apply
    (homOfLE h).op ((Shrink.linearEquiv (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) (M.obj (op n)))).symm x)
  change ((localizedModuleFunctorAdicQuotientNatIso S M hM hf).inv.app (op m)).hom
    (((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).map
      (M.map (homOfLE h).op)).hom _) = _ at hnat
  rw [localizedModuleFunctor_map_symm_shrink (Submonoid.powers f) (M.map (homOfLE h).op) x]
    at hnat
  exact hnat.symm

end Levels

section ChartPoint

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp)

variable {S : AlgebraizationSituation.{u}} {f : S.A} (q : PrimeSpectrum (chartRing S f))

/-- **A prime `𝔮 ⊇ I B` of the completed chart ring is generated by the prime of `A` under it.**
Every element of `B` agrees modulo `I B` with an element of `A_f`. -/
public theorem map_comap_chartRing_eq (hq : chartIdeal S f ≤ q.asIdeal) :
    (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal.map
      (algebraMap S.A (chartRing S f)) = q.asIdeal := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  set P := PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q
  have hIB : chartIdeal S f ≤ P.asIdeal.map (algebraMap S.A (chartRing S f)) := by
    rw [chartIdeal_eq_map]
    exact Ideal.map_mono (le_comap_chartRing q hq)
  obtain ⟨r, hr⟩ := AdicCompletion.exists_sub_mem_map_pow
    (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.fg_of_isNoetherianRing _) 1 x
  rw [pow_one] at hr
  have hrq : algebraMap (Localization.Away f) (chartRing S f) r ∈ q.asIdeal := by
    simpa using q.asIdeal.sub_mem hx (hq hr)
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj (Submonoid.powers f) r
  have hat' : algebraMap (Localization.Away f) (chartRing S f) r *
      algebraMap S.A (chartRing S f) t = algebraMap S.A (chartRing S f) a := by
    rw [algebraMap_chartRing_apply, algebraMap_chartRing_apply, ← map_mul]
    exact congrArg _ hat
  have hut : IsUnit (algebraMap S.A (chartRing S f) (t : S.A)) := by
    rw [algebraMap_chartRing_apply]
    exact (IsLocalization.map_units (Localization.Away f) t).map _
  have ha : a ∈ P.asIdeal := by
    change algebraMap S.A (chartRing S f) a ∈ q.asIdeal
    rw [← hat']
    exact q.asIdeal.mul_mem_right _ hrq
  have hr' : algebraMap (Localization.Away f) (chartRing S f) r ∈
      P.asIdeal.map (algebraMap S.A (chartRing S f)) := by
    have : algebraMap (Localization.Away f) (chartRing S f) r =
        algebraMap S.A (chartRing S f) a * ↑hut.unit⁻¹ := by
      rw [← hat', mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  have hxr : x = (x - algebraMap (Localization.Away f) (chartRing S f) r) +
      algebraMap (Localization.Away f) (chartRing S f) r := by ring
  rw [hxr]
  exact Ideal.add_mem _ (hIB hr) hr'

/-- The structure map `A → (B_𝔮)^∧`, through `A_f`, `B` and `B_𝔮`. -/
public abbrev pointStructureMap : S.A →+* pointCompletion (chartIdeal S f) q :=
  (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion (chartIdeal S f) q)).comp
    ((algebraMap (chartRing S f) (Localization.AtPrime q.asIdeal)).comp
      ((algebraMap (Localization.Away f) (chartRing S f)).comp
        (algebraMap S.A (Localization.Away f))))

/-- The structure map `A → (B_𝔮)^∧` is flat. -/
public theorem flat_pointStructureMap : (pointStructureMap q).Flat := by
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.comp ?_ ?_) ?_) ?_
  · exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f))
  · exact RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)
  · exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ q.asIdeal.primeCompl)
  · exact RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)

/-- The image of `I B` in `B_𝔮` lies in the maximal ideal, for `𝔮 ⊇ I B`. -/
private theorem map_chartIdeal_le_maximalIdeal_atPrime (hq : chartIdeal S f ≤ q.asIdeal) :
    (chartIdeal S f).map (algebraMap (chartRing S f) (Localization.AtPrime q.asIdeal)) ≤
      maximalIdeal (Localization.AtPrime q.asIdeal) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hq

/-- **The maximal ideal of `(B_𝔮)^∧` is generated by the prime of `A` under `𝔮`.** -/
public theorem map_pointStructureMap_eq (hq : chartIdeal S f ≤ q.asIdeal) :
    letI := isLocalRing_pointCompletion (chartIdeal S f) q hq
    (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal.map (pointStructureMap q) =
      maximalIdeal (pointCompletion (chartIdeal S f) q) := by
  let := isLocalRing_pointCompletion (chartIdeal S f) q hq
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have hJ := map_chartIdeal_le_maximalIdeal_atPrime q hq
  have hmax : maximalIdeal (pointCompletion (chartIdeal S f) q) =
      (maximalIdeal (Localization.AtPrime q.asIdeal)).map
        (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion (chartIdeal S f) q)) :=
    (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ hJ
      (Ideal.fg_of_isNoetherianRing _))).symm
  rw [hmax, ← Localization.AtPrime.map_eq_maximalIdeal]
  refine Eq.trans ?_ (congrArg (fun K : Ideal (chartRing S f) => (K.map (algebraMap (chartRing S f)
    (Localization.AtPrime q.asIdeal))).map (algebraMap (Localization.AtPrime q.asIdeal)
      (pointCompletion (chartIdeal S f) q))) (map_comap_chartRing_eq q hq))
  simp only [Ideal.map_map]
  rfl

/-- **The maximal ideal of `(B_𝔮)^∧` lies over the prime of `A` under `𝔮`.** -/
public theorem comap_pointStructureMap_eq (hq : chartIdeal S f ≤ q.asIdeal) :
    letI := isLocalRing_pointCompletion (chartIdeal S f) q hq
    (maximalIdeal (pointCompletion (chartIdeal S f) q)).comap (pointStructureMap q) =
      (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal := by
  let := isLocalRing_pointCompletion (chartIdeal S f) q hq
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have hJ := map_chartIdeal_le_maximalIdeal_atPrime q hq
  change ((((maximalIdeal (pointCompletion (chartIdeal S f) q)).comap
    (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion (chartIdeal S f) q))).comap
      (algebraMap (chartRing S f) (Localization.AtPrime q.asIdeal))).comap
        (algebraMap S.A (chartRing S f))) = _
  rw [comap_maximalIdeal_adicCompletion _ hJ]
  change ((maximalIdeal (Localization.AtPrime q.asIdeal)).under (chartRing S f)).comap _ = _
  rw [Localization.AtPrime.under_maximalIdeal (I := q.asIdeal)]
  rfl

/-- **The transported dualizing complex is normalized after the shift by `dim(A/𝔭)`**, for `𝔭`
the prime of `A` under `𝔮`. -/
public theorem isNormalizedDualizingComplex_pointCompletionComplex [IsLocalRing S.A]
    (hq : chartIdeal S f ≤ q.asIdeal) (ω : DerivedCategory (ModuleCat.{u} S.A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) (e : ℕ)
    (he : ringKrullDim (S.A ⧸ (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal) =
      (e : WithBot ℕ∞)) :
    letI := isLocalRing_pointCompletion (chartIdeal S f) q hq
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((pointCompletionComplex (chartIdeal S f) q (chartTransportComplex S.I f ω))⟦-(e : ℤ)⟧) := by
  let := isLocalRing_pointCompletion (chartIdeal S f) q hq
  have halg : algebraMap S.A (pointCompletion (chartIdeal S f) q) = pointStructureMap q :=
    RingHom.ext fun _ => rfl
  have : Module.Flat S.A (pointCompletion (chartIdeal S f) q) :=
    RingHom.flat_algebraMap_iff.mp (halg ▸ flat_pointStructureMap q)
  have h := Dualizing.isNormalizedDualizingComplex_totalDerivedExtensionScalars_shift ω hω
    (PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q).asIdeal
    (halg ▸ comap_pointStructureMap_eq q hq) (halg ▸ map_pointStructureMap_eq q hq) e he
  refine (Dualizing.isNormalizedDualizingComplex_congr ((shiftFunctor _ (-(e : ℤ))).mapIso ?_)).mp h
  let g₀ := algebraMap S.A (Localization.Away f)
  let g₁ := algebraMap (Localization.Away f) (chartRing S f)
  let g₂ := algebraMap (chartRing S f) (Localization.AtPrime q.asIdeal)
  let g₃ := algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion (chartIdeal S f) q)
  have c1 : (totalDerivedExtensionScalars.{u, u, u} (g₂.comp (g₁.comp g₀))).functor.obj ω ≅
      (totalDerivedExtensionScalars.{u, u, u} g₂).functor.obj
        ((totalDerivedExtensionScalars.{u, u, u} g₁).functor.obj
          ((totalDerivedExtensionScalars.{u, u, u} g₀).functor.obj ω)) :=
    ((totalDerivedExtensionScalarsComp.{u, u} (g₁.comp g₀) g₂).app ω).symm ≪≫
      (totalDerivedExtensionScalars.{u, u, u} g₂).functor.mapIso
        ((totalDerivedExtensionScalarsComp.{u, u} g₀ g₁).app ω).symm
  have c2 : (totalDerivedExtensionScalars.{u, u, u} (g₃.comp (g₂.comp (g₁.comp g₀)))).functor.obj
      ω ≅ (totalDerivedExtensionScalars.{u, u, u} g₃).functor.obj
        ((totalDerivedExtensionScalars.{u, u, u} (g₂.comp (g₁.comp g₀))).functor.obj ω) :=
    ((totalDerivedExtensionScalarsComp.{u, u} (g₂.comp (g₁.comp g₀)) g₃).app ω).symm
  rw [halg]
  exact c2 ≪≫ (totalDerivedExtensionScalars.{u, u, u} g₃).functor.mapIso c1

end ChartPoint

section Main

variable (S : AlgebraizationSituation.{u}) (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)

/-- **Stacks 0EHK, the per-point condition over a chart.** Under the hypotheses of Stacks 0EHK,
for `i ≤ s` and every chart `f ∈ 𝔪`, at every prime `𝔮 ⊇ I B` of the completed chart ring the
kernel of `Ext^{-i}_B(X/I^{n+1}X, ω_B) → Ext^{-i}_B(X, ω_B)` dies in a later term after
localizing at `𝔮`. -/
public theorem chartPrimeKernelCondition [IsLocalRing S.A]
    (hmax : IsLocalRing.maximalIdeal S.A = S.a) (hM : IsFiniteModuleModel S M) (d s : ℤ)
    (ω : DerivedCategory (ModuleCat.{u} S.A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hineq : SatisfiesDepthInequalities S (coherentAdicSystemOfFiniteModuleModel S M hM) s (s + d))
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (i : ℤ) (hi : i ≤ s) (f : S.A) (hf : f ∈ S.a) :
    ChartPrimeKernelCondition S M f ω i := by
  intro n q hq
  -- the chart vertex, with `A` acting through `A_f`
  let : Module S.A (chartVertex S M f) :=
    Module.compHom _ (algebraMap S.A (Localization.Away f))
  have : IsScalarTower S.A (Localization.Away f) (chartVertex S M f) :=
    ⟨fun a b x => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have : IsScalarTower S.A (chartRing S f) (chartVertex S M f) :=
    ⟨fun a b x => by
      rw [Algebra.smul_def, mul_smul, algebraMap_chartRing_apply, algebraMap_smul]
      rfl⟩
  have hfinX : Module.Finite (chartRing S f) (chartVertex S M f) :=
    finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel S M hM hf
  obtain ⟨z, hz, Bs, hloc, hcomp, hBA, hBc, hBI, hBM, hBadd, hBmod, hBT, hBs, hBd⟩ :=
    exists_chartCompletionBootstrap S M f (chartVertex S M f) hmax hM s d ⟨ω, hω.1⟩ hcd hineq hf
      (chartVertexLevel S M f hM hf) (fun h x => chartVertexLevel_transition S M f hM hf h x) q hq
  -- the point `y` of `U` under `𝔮`, and `e = dim(A/𝔭)`
  set P := PrimeSpectrum.comap (algebraMap S.A (chartRing S f)) q with hP
  have hPa : ¬ S.a ≤ P.asIdeal := not_le_comap_chartRing q hf
  have hPI : S.I ≤ P.asIdeal := le_comap_chartRing q hq
  have hyz : S.U.ι.base (pointOfPrime S P hPa) = S.Yι.base z :=
    (base_pointOfPrime_eq S P hPa hPI).trans ((Yι_base_pointOfPrimeY S P hPI).trans hz.symm)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_underlyingPrime_eq S (pointOfPrime S P hPa)
  have hδe : ((S.distanceToZ z).toNat : ℤ) ≤ e := by
    have h1 := distanceToZ_le_ringKrullDim_quotient S hmax.symm (pointOfPrime S P hPa) z hyz
    rw [he] at h1
    have h2 : S.distanceToZ z ≤ (e : ℕ∞) := by exact_mod_cast h1
    have h3 := ENat.toNat_le_toNat h2 (ENat.natCast_ne_top e)
    rw [ENat.toNat_natCast] at h3
    exact_mod_cast h3
  have hj : i - e ≤ Bs.s := by
    rw [hBs]
    omega
  -- the canonical form of Stacks 0EFR over `(B_𝔮)^∧`
  have key := @exists_range_le_range_localCohomology_adicQuotient Bs hloc hcomp (hBT hloc)
    (i - e) hj
  clear hBT hBs hBd hj
  cases Bs
  rename_i A bc bn bI bM ba bmod bf bT bsub bstable bs bd bdual bcd bdepth
  cases hBA
  cases hBc
  cases hBI
  cases hBM
  cases hBadd
  cases hBmod
  let := isLocalRing_pointCompletion (chartIdeal S f) q hq
  have hsurj := range_le_range_pointTower_of_adicQuotient (chartIdeal S f) q (chartVertex S M f)
    _ (pointBaseIso (chartIdeal S f) q (chartVertex S M f))
    (Stacks.LocalCohomology.localCohomologyModuleFunctor _ (i - e)) key
  have hωB : Dualizing.IsDualizingComplex (chartTransportComplex S.I f ω) :=
    isDualizingComplex_chartTransportComplex S.I f ω hω.1
  exact exists_notMem_support_range_ker_of_localDuality (chartIdeal S f) q hq
    (chartVertex S M f) (chartTransportComplex S.I f ω) hωB i e
    (isNormalizedDualizingComplex_pointCompletionComplex q hq ω hω e he) hsurj n

/-- **Stacks 0EHK, the essential constancy of the `Ext` system.** Let `(A, 𝔪)` be a Noetherian
local ring with `𝔞 = 𝔪` in the algebraization situation, `(M_n)` a finite module model whose
coherent adic system satisfies the `(s, s + d)`-inequalities, `d ≥ cd(A, I)`, and `ω` a
normalized dualizing complex. Then for every `i ≤ s` the inverse system
`n ↦ Ext^{-i}_A(M_n, ω)` is essentially constant modulo modules of finite length. -/
public theorem isEssentiallyConstantModFiniteLength_dualizingExtSystem [IsLocalRing S.A]
    (hmax : IsLocalRing.maximalIdeal S.A = S.a) (hM : IsFiniteModuleModel S M) (d s : ℤ)
    (ω : DerivedCategory (ModuleCat.{u} S.A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hineq : SatisfiesDepthInequalities S (coherentAdicSystemOfFiniteModuleModel S M hM) s (s + d))
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d) :
    ∀ i : ℤ, i ≤ s → IsEssentiallyConstantModFiniteLength S.A S.I (dualizingExtSystem M ω i) :=
  fun i hi => isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_chartPrimes S M hmax hM
    ω hω.1 i fun f hf => chartPrimeKernelCondition S M hmax hM d s ω hω hineq hcd i hi f hf

end Main

end Stacks.Algebraization

end
