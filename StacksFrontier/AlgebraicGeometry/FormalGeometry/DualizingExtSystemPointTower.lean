module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtSystemChartPoint
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyProjections
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeCancellation

/-!
# Stacks 0EHK: the adic tower at a prime of the chart ring, over `(B_𝔮)^∧`

Let `B` be a Noetherian ring, `I_B` an ideal, `𝔮` a prime and `R = (B_𝔮)^∧` the `I_B`-adic
completion of `B_𝔮`. For a `B`-module `X`, the per-point step
`Stacks.Algebraization.exists_notMem_support_range_ker_of_localDuality` is phrased with the base
change `R ⊗ T_n` of the adic tower `T_n = X/I_B^{n+1}X`, while the canonical form of
[Stacks, Tag 0EFR] (`Stacks.Algebraization.exists_range_le_range_localCohomology_adicQuotient`) is
phrased with the adic tower `P/I^nP` of an `R`-module `P`. Given an isomorphism `R ⊗ X ≅ P`, this
file identifies the two towers (with a shift of one in the index) compatibly with the
projections, and transports the hypothesis of the per-point step from one to the other.

## Main results

* `Stacks.Algebraization.pointLevelMap` — the comparison `R ⊗ T_n → P/I^{n+1}P`.
* `Stacks.Algebraization.isIso_pointLevelMap` — it is an isomorphism.
* `Stacks.Algebraization.range_le_range_pointTower_of_adicQuotient` — the transport of the
  hypothesis of the per-point step.
* `Stacks.Algebraization.pointBaseIso` — `R ⊗_B X` is the completion of `X_𝔮`, for `X` finite.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.ProEtale

universe u

namespace Stacks.Algebraization

section PointTower

variable {B : Type u} [CommRing B] [IsNoetherianRing B] (IB : Ideal B) (q : PrimeSpectrum B)

/-- The ideal `I_B R` of `R = (B_𝔮)^∧`. -/
public abbrev pointIdeal : Ideal (pointCompletion IB q) :=
  (IB.map (algebraMap B (Localization.AtPrime q.asIdeal))).map
    (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))

/-- The adjunction between the two-step extension of scalars `B → B_𝔮 → R` and restriction. -/
public abbrev pointAdj :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.AtPrime q.asIdeal)) ⋙
        ModuleCat.extendScalars.{u, u, u}
          (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))) ⊣
      (ModuleCat.restrictScalars.{u}
          (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q)) ⋙
        ModuleCat.restrictScalars.{u} (algebraMap B (Localization.AtPrime q.asIdeal))) :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap B (Localization.AtPrime q.asIdeal))).comp
    (ModuleCat.extendRestrictScalarsAdj
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q)))

omit [IsNoetherianRing B] in
/-- `(I_B R)^k` is the extension of `I_B^k`. -/
public theorem pointIdeal_pow (k : ℕ) :
    pointIdeal IB q ^ k = ((IB ^ k).map (algebraMap B (Localization.AtPrime q.asIdeal))).map
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q)) := by
  rw [Ideal.map_pow, Ideal.map_pow]

omit [IsNoetherianRing B] in
/-- **The base change of the `n`-th adic quotient is killed by `(I_B R)^{n+1}`.** -/
public theorem pow_smul_top_pointTower_eq_bot (X : ModuleCat.{u} B) (n : ℕ) :
    pointIdeal IB q ^ (n + 1) •
      (⊤ : Submodule (pointCompletion IB q) ((pointTower IB q X).obj (op n))) = ⊥ := by
  let W := (pointTower IB q X).obj (op n)
  have hann : pointIdeal IB q ^ (n + 1) ≤ Module.annihilator (pointCompletion IB q) W := by
    rw [pointIdeal_pow, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap, Module.mem_annihilator]
    intro w
    let a := algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q)
      (algebraMap B (Localization.AtPrime q.asIdeal) b)
    let φ : W ⟶ W := ModuleCat.ofHom (a • LinearMap.id)
    suffices hφ : φ = 0 from congrArg (fun g => g.hom w) hφ
    apply ((pointAdj IB q).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_zero,
      Limits.comp_zero]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have hx : b • x = 0 := by
      induction x using Submodule.Quotient.induction_on with
      | _ y =>
        exact (Submodule.Quotient.mk_eq_zero (IB ^ (n + 1) • (⊤ : Submodule B X))).mpr
          (Submodule.smul_mem_smul hb Submodule.mem_top)
    have h1 := ((pointAdj IB q).unit.app ((Stacks.Examples.adicQuotientTower IB X).obj
      (op n))).hom.map_smul b x
    rw [hx, map_zero] at h1
    exact h1.symm
  exact le_bot_iff.mp (Submodule.smul_le.mpr fun a ha w _ =>
    (Submodule.mem_bot _).mpr (Module.mem_annihilator.mp (hann ha) w))

section Level

variable (X : ModuleCat.{u} B) (P : ModuleCat.{u} (pointCompletion IB q))
  (α : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).obj
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.AtPrime q.asIdeal))).obj X) ≅
      P)

/-- The adic tower `n ↦ P/(I_B R)^n P` of an `R`-module. -/
public abbrev pointAdicSystem : ℕᵒᵖ ⥤ ModuleCat.{u} (pointCompletion IB q) :=
  adicQuotientModuleSystem (pointCompletion IB q) (pointIdeal IB q) P

/-- The projections `P → P/(I_B R)^n P`. -/
public abbrev pointAdicProj (n : ℕ) : P ⟶ (pointAdicSystem IB q P).obj (op n) :=
  Dualizing.adicQuotientProjection (pointCompletion IB q) (pointIdeal IB q) P n

omit [IsNoetherianRing B] in
/-- An element of `Jᵏ` kills `M/JᵏM`. -/
public theorem smul_eq_zero_of_mem_pow {T : Type u} [CommRing T] (K : Ideal T) {M : Type u}
    [AddCommGroup M] [Module T M] {k : ℕ} {r : T} (hr : r ∈ K ^ k)
    (y : M ⧸ (K ^ k • (⊤ : Submodule T M))) : r • y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | _ z =>
    rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr Submodule.mem_top)

omit [IsNoetherianRing B] in
/-- The image in `R` of an element of `I_B^k` lies in `(I_B R)^k`. -/
public theorem algebraMap_mem_pointIdeal_pow {b : B} {k : ℕ} (hb : b ∈ IB ^ k) :
    algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q)
      (algebraMap B (Localization.AtPrime q.asIdeal) b) ∈ pointIdeal IB q ^ k := by
  rw [pointIdeal_pow]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hb)

/-- The `R`-module `P`, restricted to `B` along `B → B_𝔮 → R`. -/
public def pointRestrict (W : ModuleCat.{u} (pointCompletion IB q)) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars.{u} (algebraMap B (Localization.AtPrime q.asIdeal))).obj
    ((ModuleCat.restrictScalars.{u}
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).obj W)

/-- The base change `R ⊗_B X` along `B → B_𝔮 → R`. -/
public abbrev pointBase : ModuleCat.{u} (pointCompletion IB q) :=
  (ModuleCat.extendScalars.{u, u, u}
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).obj
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap B (Localization.AtPrime q.asIdeal))).obj X)

/-- The `B`-linear map `X → P/I^{n+1}P` adjoint to `R ⊗ X ≅ P → P/I^{n+1}P`. -/
public def pointLevelAdjX (n : ℕ) :
    X ⟶ pointRestrict IB q ((pointAdicSystem IB q P).obj (op (n + 1))) :=
  (pointAdj IB q).homEquiv _ _ (α.hom ≫ pointAdicProj IB q P (n + 1))

omit [IsNoetherianRing B] in
/-- `pointLevelAdjX` kills `I_B^{n+1} X`. -/
public theorem le_ker_pointLevelAdjX (n : ℕ) :
    IB ^ (n + 1) • (⊤ : Submodule B X) ≤ LinearMap.ker (pointLevelAdjX IB q X P α n).hom := by
  refine Submodule.smul_le.mpr fun b hb x _ => LinearMap.mem_ker.mpr ?_
  rw [(pointLevelAdjX IB q X P α n).hom.map_smul]
  exact smul_eq_zero_of_mem_pow (pointIdeal IB q) (algebraMap_mem_pointIdeal_pow IB q hb) _

/-- The `B`-linear map `T_n = X/I_B^{n+1}X → P/I^{n+1}P` induced by `α`. -/
public def pointLevelAdj (n : ℕ) :
    ModuleCat.of B ((Stacks.Examples.adicQuotientTower IB X).obj (op n)) ⟶
      ModuleCat.of B (pointRestrict IB q ((pointAdicSystem IB q P).obj (op (n + 1)))) :=
  ModuleCat.ofHom (Submodule.liftQ _ (pointLevelAdjX IB q X P α n).hom
    (le_ker_pointLevelAdjX IB q X P α n))

/-- **The comparison `R ⊗ T_n → P/I^{n+1}P`** of the base changed adic tower of `X` with the adic
tower of `P`, induced by `α : R ⊗ X ≅ P`. -/
public def pointLevelMap (n : ℕ) :
    (pointTower IB q X).obj (op n) ⟶ (pointAdicSystem IB q P).obj (op (n + 1)) :=
  ((pointAdj IB q).homEquiv _ _).symm (pointLevelAdj IB q X P α n)

omit [IsNoetherianRing B] in
/-- The comparison commutes with the projections. -/
public theorem pointTowerProj_comp_pointLevelMap (n : ℕ) :
    pointTowerProj IB q X n ≫ pointLevelMap IB q X P α n =
      α.hom ≫ pointAdicProj IB q P (n + 1) := by
  have h1 : ModuleCat.ofHom (Submodule.mkQ _) ≫ pointLevelAdj IB q X P α n =
      (pointAdj IB q).homEquiv _ _ (α.hom ≫ pointAdicProj IB q P (n + 1)) :=
    ModuleCat.hom_ext (Submodule.liftQ_mkQ _ _ _)
  have h2 := (pointAdj IB q).homEquiv_naturality_left_symm
    (ModuleCat.ofHom (Submodule.mkQ _) : X ⟶ (Stacks.Examples.adicQuotientTower IB X).obj (op n))
    (pointLevelAdj IB q X P α n)
  exact h2.symm.trans ((congrArg _ h1).trans (Equiv.symm_apply_apply _ _))

omit [IsNoetherianRing B] in
/-- Extension of scalars preserves epimorphisms. -/
public theorem epi_extendScalars_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) (hg : Epi g) :
    Epi ((ModuleCat.extendScalars.{u, u, u} f).map g) := by
  have : (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  infer_instance

/-- The projections of the base changed tower are epimorphisms. -/
public instance epi_pointTowerProj (n : ℕ) : Epi (pointTowerProj IB q X n) :=
  epi_extendScalars_map _ _ (epi_extendScalars_map _ _
    ((ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)))

omit [IsNoetherianRing B] in
/-- The projections of the base changed tower form a cone. -/
public theorem pointTowerProj_comp_map {m n : ℕ} (h : n ≤ m) :
    pointTowerProj IB q X m ≫ (pointTower IB q X).map (homOfLE h).op =
      pointTowerProj IB q X n := by
  have hX : (ModuleCat.ofHom (Submodule.mkQ _) :
      X ⟶ (Stacks.Examples.adicQuotientTower IB X).obj (op m)) ≫
        (Stacks.Examples.adicQuotientTower IB X).map (homOfLE h).op =
      ModuleCat.ofHom (Submodule.mkQ _) :=
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  have := congrArg (fun g => (ModuleCat.extendScalars.{u, u, u}
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).map
        ((ModuleCat.extendScalars.{u, u, u}
          (algebraMap B (Localization.AtPrime q.asIdeal))).map g)) hX
  exact ((Functor.map_comp _ _ _).symm.trans (congrArg (ModuleCat.extendScalars.{u, u, u}
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).map
        (Functor.map_comp _ _ _).symm)).trans this

omit [IsNoetherianRing B] in
/-- The comparison is natural in `n`. -/
public theorem pointLevelMap_naturality {m n : ℕ} (h : n ≤ m) :
    (pointTower IB q X).map (homOfLE h).op ≫ pointLevelMap IB q X P α n =
      pointLevelMap IB q X P α m ≫
        (pointAdicSystem IB q P).map (homOfLE (Nat.succ_le_succ h)).op := by
  rw [← cancel_epi (pointTowerProj IB q X m), ← Category.assoc, pointTowerProj_comp_map,
    pointTowerProj_comp_pointLevelMap, ← Category.assoc, pointTowerProj_comp_pointLevelMap,
    Category.assoc, Dualizing.adicQuotientProjection_comp_map]

omit [IsNoetherianRing B] in
/-- **The comparison `R ⊗ T_n → P/I^{n+1}P` is an isomorphism.** -/
public theorem isIso_pointLevelMap (n : ℕ) : IsIso (pointLevelMap IB q X P α n) := by
  have hcomm := pointTowerProj_comp_pointLevelMap IB q X P α n
  have hsurjπ : Function.Surjective (pointTowerProj IB q X n).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hα := ConcreteCategory.bijective_of_isIso α.hom
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨z, rfl⟩ := hsurjπ y
    have h1 := congrArg (fun g => g.hom z) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    rw [hy] at h1
    have h2 : α.hom.hom z ∈ pointIdeal IB q ^ (n + 1) • (⊤ : Submodule _ P) :=
      (Submodule.Quotient.mk_eq_zero _).mp h1.symm
    have h3 : z ∈ pointIdeal IB q ^ (n + 1) •
        (⊤ : Submodule (pointCompletion IB q) (pointBase IB q X)) := by
      have h4 := Submodule.mem_map_of_mem (f := α.inv.hom) h2
      rw [Submodule.map_smul''] at h4
      have h5 : α.inv.hom (α.hom.hom z) = z := congrArg (fun g => g.hom z) α.hom_inv_id
      rw [h5] at h4
      exact Submodule.smul_mono le_rfl le_top h4
    have h6 := Submodule.mem_map_of_mem (f := (pointTowerProj IB q X n).hom) h3
    rw [Submodule.map_smul''] at h6
    have h7 := Submodule.smul_mono (le_refl (pointIdeal IB q ^ (n + 1))) le_top h6
    rw [pow_smul_top_pointTower_eq_bot] at h7
    exact (Submodule.mem_bot _).mp h7
  · intro w
    obtain ⟨z, rfl⟩ := (Submodule.mkQ_surjective _ : Function.Surjective
      (Submodule.mkQ (pointIdeal IB q ^ (n + 1) • (⊤ : Submodule _ P)))) w
    obtain ⟨z', rfl⟩ := hα.2 z
    exact ⟨(pointTowerProj IB q X n).hom z', congrArg (fun g => g.hom z') hcomm⟩

omit [IsNoetherianRing B] in
include α in
/-- **Transport of the hypothesis of the per-point step from the adic tower of `P` to the base
changed adic tower of `X`**, along `α : R ⊗ X ≅ P`, for any functor `H` (in the application, local
cohomology). -/
public theorem range_le_range_pointTower_of_adicQuotient
    (H : ModuleCat.{u} (pointCompletion IB q) ⥤ ModuleCat.{u} (pointCompletion IB q))
    (h : ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m,
      LinearMap.range (H.map ((pointAdicSystem IB q P).map (homOfLE h).op)).hom ≤
        LinearMap.range (H.map (pointAdicProj IB q P n)).hom) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m,
      LinearMap.range (H.map ((pointTower IB q X).map (homOfLE h).op)).hom ≤
        LinearMap.range (H.map (pointTowerProj IB q X n)).hom := by
  intro n
  obtain ⟨m, hm, hle⟩ := h (n + 1)
  have hnm : n ≤ m := by omega
  refine ⟨m, hnm, ?_⟩
  have := isIso_pointLevelMap IB q X P α n
  have := isIso_pointLevelMap IB q X P α m
  let βn := asIso (pointLevelMap IB q X P α n)
  let βm := asIso (pointLevelMap IB q X P α m)
  have hT : (pointTower IB q X).map (homOfLE hnm).op =
      (βm.hom ≫ (pointAdicSystem IB q P).map (homOfLE (Nat.succ_le_succ hnm)).op) ≫ βn.inv := by
    rw [Iso.eq_comp_inv]
    exact pointLevelMap_naturality IB q X P α hnm
  have hS : (pointAdicSystem IB q P).map (homOfLE (Nat.succ_le_succ hnm)).op =
      (pointAdicSystem IB q P).map (homOfLE (Nat.le_succ m)).op ≫
        (pointAdicSystem IB q P).map (homOfLE hm).op := by
    rw [← Functor.map_comp]
    rfl
  have hc : pointTowerProj IB q X n = (α.hom ≫ pointAdicProj IB q P (n + 1)) ≫ βn.inv := by
    rw [Iso.eq_comp_inv]
    exact pointTowerProj_comp_pointLevelMap IB q X P α n
  have hα : ∀ z, (H.map α.hom).hom ((H.map α.inv).hom z) = z := fun z => by
    rw [← ModuleCat.comp_apply, ← H.map_comp, α.inv_hom_id, H.map_id]
    rfl
  rw [hT, hS, hc]
  rintro _ ⟨x, rfl⟩
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  obtain ⟨z, hz⟩ := hle (LinearMap.mem_range_self _
    ((H.map ((pointAdicSystem IB q P).map (homOfLE (Nat.le_succ m)).op)).hom
      ((H.map βm.hom).hom x)))
  refine ⟨(H.map α.inv).hom z, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, hα, hz]

end Level

section BaseIso

variable (X : ModuleCat.{u} B) [Module.Finite B X]

/-- **`R ⊗_B X` is the completion of `X_𝔮`**, for `X` finite over `B`. -/
public def pointBaseIso : pointBase IB q X ≅ ModuleCat.of (pointCompletion IB q)
    (AdicCompletion (IB.map (algebraMap B (Localization.AtPrime q.asIdeal)))
      (LocalizedModule q.asIdeal.primeCompl X)) :=
  haveI : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  (ModuleCat.extendScalars.{u, u, u}
      (algebraMap (Localization.AtPrime q.asIdeal) (pointCompletion IB q))).mapIso
      (Stacks.TensorProductPushout.extendScalarsObjIso X ≪≫
        (((isLocalizedModule_iff_isBaseChange q.asIdeal.primeCompl
          (Localization.AtPrime q.asIdeal) (LocalizedModule.mkLinearMap q.asIdeal.primeCompl X)).mp
            inferInstance).equiv.toModuleIso)) ≪≫
    Stacks.TensorProductPushout.extendScalarsObjIso
      (ModuleCat.of (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl X)) ≪≫
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
      (IB.map (algebraMap B (Localization.AtPrime q.asIdeal)))
      (LocalizedModule q.asIdeal.primeCompl X)).toModuleIso

end BaseIso

end PointTower

end Stacks.Algebraization

end
