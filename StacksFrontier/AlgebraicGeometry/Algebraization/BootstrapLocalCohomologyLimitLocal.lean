module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapCompletionSituation
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniverse
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.RingTheory.LocalCohomology.TorsionFlatDescent

/-!
# Local cohomology as a limit over a local bootstrap situation

In the bootstrap situation of [Stacks, Tag 0EFU] with `A` local and `T = {𝔪}`, Stacks 0EFR asserts
that `Hⁱ_𝔪(M) → lim Hⁱ_𝔪(M/IⁿM)` is an isomorphism for `i ≤ s`. Write `A^∧`, `M^∧` for the `I`-adic
completions and `T'` for the preimage of `T`. For any specialization-stable `T ⊆ V(I)`, the cone
`Hⁱ_T(M) → {Hⁱ_T(M/IⁿM)}` is a limit cone as soon as the cone
`Hⁱ_{T'}(M^∧) → {Hⁱ_{T'}(M^∧/(I A^∧)ⁿM^∧)}` is; so the limit assertion of Stacks 0EFR for a local
bootstrap situation follows from the same assertion for `I`-adically complete local situations.

## Main results

* `Stacks.Algebraization.isLimitLocalCohomologyAdicConeOfAdicCompletion` — the descent for a
  Noetherian ring, an ideal, a finite module and a specialization-stable `T ⊆ V(I)`.
* `Stacks.Algebraization.nonempty_isLimit_cone_of_adicCompletion` — the descent for a bootstrap
  situation and its completion (`Stacks.Algebraization.BootstrapSituation.adicCompletion`).
* `Stacks.Algebraization.nonempty_isLimit_cone_of_eq_closedPoint_of_complete` — the limit assertion
  of Stacks 0EFR for a local bootstrap situation at its closed point, from the same assertion for
  `I`-adically complete local situations (`hcomplete`).

## References

* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
* [Stacks Project, Tag 0EF5](https://stacks.math.columbia.edu/tag/0EF5)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open Stacks.LocalCohomology

universe u w

namespace Stacks.Algebraization

section Comparison

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- The completion `A → A^∧` is bijective modulo `I`. -/
theorem bijective_quotientMap_adicCompletion :
    Function.Bijective (Ideal.quotientMap (I.map (algebraMap A (AdicCompletion I A)))
      (algebraMap A (AdicCompletion I A)) Ideal.le_comap_map) := by
  have key (a : A) (x : AdicCompletion I A) :
      algebraMap A (AdicCompletion I A) a - x ∈ I.map (algebraMap A (AdicCompletion I A)) ↔
        Ideal.Quotient.mk I a = AdicCompletion.evalOneₐ I x := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I (Ideal.fg_of_isNoetherianRing I),
      RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (RingHom.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk I) a).congr_left
  refine ⟨Ideal.quotientMap_injective' fun a ha => ?_, fun y => ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using (key a 0).1 (by simpa using ha))
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I) (AdicCompletion.evalOneₐ I x)
    exact ⟨_, by rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, key a, ha]⟩

variable (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

omit [Module.Finite A M] in
/-- An element of the completion lies in `(I A^∧)ⁿ M^∧` exactly when its `n`-th component vanishes.
-/
theorem mem_map_pow_smul_top_iff_eval_eq_zero (n : ℕ) (y : AdicCompletion I M) :
    y ∈ (I.map (algebraMap A (AdicCompletion I A)) ^ n •
        (⊤ : Submodule (AdicCompletion I A) (AdicCompletion I M))) ↔
      AdicCompletion.eval I M n y = 0 := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
    Submodule.restrictScalars_top,
    AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing I), LinearMap.mem_ker]

/-- The inclusion `M → M^∧`, as a map semilinear over `A → A^∧`. -/
def ofSemilinear : M →ₛₗ[algebraMap A (AdicCompletion I A)] AdicCompletion I M where
  toFun := AdicCompletion.of I M
  map_add' x y := map_add (AdicCompletion.of I M) x y
  map_smul' a m := by
    rw [map_smul, ← algebraMap_smul (AdicCompletion I A) a (AdicCompletion.of I M m)]

/-- The map `M/IⁿM → M^∧/(I A^∧)ⁿ M^∧` induced by `M → M^∧`. -/
def quotientOfSemilinear (n : ℕ) :
    M ⧸ (I ^ n • (⊤ : Submodule A M)) →ₛₗ[algebraMap A (AdicCompletion I A)]
      AdicCompletion I M ⧸ (I.map (algebraMap A (AdicCompletion I A)) ^ n •
        (⊤ : Submodule (AdicCompletion I A) (AdicCompletion I M))) :=
  Submodule.mapQ _ _ (ofSemilinear I M) (Submodule.smul_le.mpr fun a ha m _ => by
    rw [Submodule.mem_comap, map_smulₛₗ]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha)

omit [Module.Finite A M] in
/-- The map `M/IⁿM → M^∧/(I A^∧)ⁿ M^∧` is bijective. -/
theorem bijective_quotientOfSemilinear (n : ℕ) :
    Function.Bijective (quotientOfSemilinear I M n) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (AdicCompletion.of I M x) =
      Submodule.Quotient.mk (AdicCompletion.of I M y) at hxy
    rw [Submodule.Quotient.eq, ← map_sub, mem_map_pow_smul_top_iff_eval_eq_zero,
      AdicCompletion.eval_of, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxy
    exact (Submodule.Quotient.eq _).mpr hxy
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M n z)
    refine ⟨Submodule.Quotient.mk m, ?_⟩
    show Submodule.Quotient.mk (AdicCompletion.of I M m) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq, mem_map_pow_smul_top_iff_eval_eq_zero, map_sub,
      AdicCompletion.eval_of, Submodule.mkQ_apply, hm, sub_self]

/-- The quotient maps `M/IⁿM → M^∧/(I A^∧)ⁿ M^∧`, as a map from the tower of `M` to the restriction
of scalars of the tower of `M^∧`. -/
def towerToCompletion :
    idealPowerQuotientTower.{u, u} I (ModuleCat.of A M) ⟶
      idealPowerQuotientTower.{u, u} (I.map (algebraMap A (AdicCompletion I A)))
          (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M)) ⋙
        ModuleCat.restrictScalars.{u} (algebraMap A (AdicCompletion I A)) where
  app n := ModuleCat.semilinearMapAddEquiv _ _ _ (quotientOfSemilinear I M n.unop)
  naturality m n g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- The inclusion `M → M^∧` into the restriction of scalars of `M^∧`. -/
def toCompletion :
    ModuleCat.of A M ⟶ (ModuleCat.restrictScalars.{u} (algebraMap A (AdicCompletion I A))).obj
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M)) :=
  ModuleCat.semilinearMapAddEquiv _ _ _ (ofSemilinear I M)

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- The two quotient maps are compatible with the inclusion `M → M^∧`. -/
theorem idealPowerQuotientCone_π_comp_towerToCompletion (n : ℕᵒᵖ) :
    (idealPowerQuotientCone.{u, u} I (ModuleCat.of A M)).π.app n ≫
        (towerToCompletion I M).app n =
      toCompletion I M ≫ (ModuleCat.restrictScalars.{u} (algebraMap A (AdicCompletion I A))).map
        ((idealPowerQuotientCone.{u, u} (I.map (algebraMap A (AdicCompletion I A)))
          (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M))).π.app n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The adjunction between extension and restriction of scalars along `A → A^∧`. -/
abbrev completionAdj :=
  ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A (AdicCompletion I A))

/-- The comparison `A^∧ ⊗_A (M/IⁿM) → M^∧/(I A^∧)ⁿ M^∧`, natural in `n`. -/
def towerCompletionComparison :
    idealPowerQuotientTower.{u, u} I (ModuleCat.of A M) ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A)) ⟶
      idealPowerQuotientTower.{u, u} (I.map (algebraMap A (AdicCompletion I A)))
          (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M)) where
  app n := ((completionAdj I).homEquiv _ _).symm ((towerToCompletion I M).app n)
  naturality m n g := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm,
      (towerToCompletion I M).naturality, Functor.comp_map,
      Adjunction.homEquiv_naturality_right_symm]

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- Each quotient `M/IⁿM` is `I`-power torsion. -/
theorem isIPowerTorsion_idealPowerQuotientTower_obj (n : ℕᵒᵖ) :
    IsIPowerTorsion A ((idealPowerQuotientTower.{u, u} I (ModuleCat.of A M)).obj n) I := by
  intro x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨n.unop + 1, n.unop.succ_pos, fun a ha => ?_⟩
  show a • (Submodule.Quotient.mk m : M ⧸ I ^ n.unop • (⊤ : Submodule A M)) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right n.unop.le_succ ha) Submodule.mem_top

omit [Module.Finite A M] in
/-- The comparison `A^∧ ⊗_A (M/IⁿM) → M^∧/(I A^∧)ⁿ M^∧` is an isomorphism. -/
theorem isIso_towerCompletionComparison_app (n : ℕᵒᵖ) :
    IsIso ((towerCompletionComparison I M).app n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hunit := bijective_extendRestrictScalarsAdj_unit_app I
    (AdicCompletion.flat_of_isNoetherian I) (bijective_quotientMap_adicCompletion I) _
    (isIPowerTorsion_idealPowerQuotientTower_obj I M n)
  have h := (completionAdj I).homEquiv_unit _ _
    (((completionAdj I).homEquiv _ _).symm ((towerToCompletion I M).app n))
  rw [Equiv.apply_symm_apply] at h
  have hc (x : (idealPowerQuotientTower.{u, u} I (ModuleCat.of A M)).obj n) :
      (towerCompletionComparison I M).app n ((completionAdj I).unit.app _ x) =
        (towerToCompletion I M).app n x :=
    (congrArg (fun φ => φ.hom x) h).symm
  have hb := bijective_quotientOfSemilinear I M n.unop
  refine ⟨fun y₁ y₂ hy => ?_, fun z => ?_⟩
  · obtain ⟨x₁, rfl⟩ := hunit.2 y₁
    obtain ⟨x₂, rfl⟩ := hunit.2 y₂
    have : (towerToCompletion I M).app n x₁ = (towerToCompletion I M).app n x₂ := by
      rwa [← hc, ← hc]
    rw [hb.1 this]
  · obtain ⟨x, hx⟩ := hb.2 z
    exact ⟨_, (hc x).trans hx⟩

/-- The comparison of towers `A^∧ ⊗_A (M/IⁿM) → M^∧/(I A^∧)ⁿ M^∧` is an isomorphism. -/
instance isIso_towerCompletionComparison : IsIso (towerCompletionComparison I M) := by
  have := isIso_towerCompletionComparison_app I M
  exact NatIso.isIso_of_isIso_app _

/-- The comparison `A^∧ ⊗_A M → M^∧`. -/
def completionComparison :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A))).obj
        (ModuleCat.of A M) ⟶ ModuleCat.of (AdicCompletion I A) (AdicCompletion I M) :=
  ((completionAdj I).homEquiv _ _).symm (toCompletion I M)

/-- For a finite module `M` over a Noetherian ring, the comparison `A^∧ ⊗_A M → M^∧` is an
isomorphism. -/
instance isIso_completionComparison : IsIso (completionComparison I M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let e := IPowerTorsion.tensorModuleCatEquiv.{u, u, u} (S := AdicCompletion I A)
    (ModuleCat.of A M)
  refine (Function.Bijective.of_comp_iff _ e.bijective).mp ?_
  have : ⇑(completionComparison I M) ∘ ⇑e =
      ⇑(AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M) := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      change (completionComparison I M) (e (b ⊗ₜ[A] m)) = AdicCompletion.ofTensorProduct I M _
      rw [IPowerTorsion.tensorModuleCatEquiv_tmul, AdicCompletion.ofTensorProduct_tmul]
      rfl
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  rw [this]
  exact (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).bijective

/-- The quotient cone of `M`, extended to `A^∧` and composed with the comparison of towers, is the
quotient cone of `M^∧`. -/
def extendScalarsIdealPowerQuotientConeIso :
    (Cone.postcompose (towerCompletionComparison I M)).obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A))).mapCone
          (idealPowerQuotientCone.{u, u} I (ModuleCat.of A M))) ≅
      idealPowerQuotientCone.{u, u} (I.map (algebraMap A (AdicCompletion I A)))
        (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M)) :=
  Cone.ext (@asIso _ _ _ _ (completionComparison I M) (isIso_completionComparison I M))
    (fun n => by
      change (ModuleCat.extendScalars _).map _ ≫
          ((completionAdj I).homEquiv _ _).symm ((towerToCompletion I M).app n) =
        ((completionAdj I).homEquiv _ _).symm (toCompletion I M) ≫ _
      exact ((completionAdj I).homEquiv_naturality_left_symm
          ((idealPowerQuotientCone.{u, u} I (ModuleCat.of A M)).π.app n)
          ((towerToCompletion I M).app n)).symm.trans
        ((congrArg ((completionAdj I).homEquiv _ _).symm
          (idealPowerQuotientCone_π_comp_towerToCompletion I M n)).trans
        ((completionAdj I).homEquiv_naturality_right_symm (toCompletion I M) _)))

/-- Let `A` be a Noetherian ring, `I` an ideal, `M` a finite module and `T ⊆ V(I)`
specialization-stable, and let `A^∧`, `M^∧`, `T'` be the `I`-adic completions and the preimage of
`T`. If `Hⁱ_{T'}(M^∧) → lim Hⁱ_{T'}(M^∧/(I A^∧)ⁿM^∧)` is a limit cone, so is
`Hⁱ_T(M) → lim Hⁱ_T(M/IⁿM)`. -/
def isLimitLocalCohomologyAdicConeOfAdicCompletion (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hTI : T ⊆ PrimeSpectrum.zeroLocus (I : Set A)) (i : ℤ)
    (h : IsLimit (localCohomologyAdicCone.{u, u} (AdicCompletion I A)
      ((PrimeSpectrum.comap (algebraMap A (AdicCompletion I A))) ⁻¹' T)
      (I.map (algebraMap A (AdicCompletion I A))) i
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M)))) :
    IsLimit (localCohomologyAdicCone.{u, u} A T I i (ModuleCat.of A M)) :=
  let R := ModuleCat.restrictScalars.{u} (algebraMap A (AdicCompletion I A))
  let H' := localCohomologyWithSupportInModuleFunctor.{u, u} (AdicCompletion I A)
    ((PrimeSpectrum.comap (algebraMap A (AdicCompletion I A))) ⁻¹' T) i
  let qc' := idealPowerQuotientCone.{u, u} (I.map (algebraMap A (AdicCompletion I A)))
    (ModuleCat.of (AdicCompletion I A) (AdicCompletion I M))
  let E := ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A))
  let qc := idealPowerQuotientCone.{u, u} I (ModuleCat.of A M)
  haveI : PreservesLimitsOfSize.{0, 0} R := (completionAdj I).rightAdjoint_preservesLimits
  let h₁ : IsLimit ((H' ⋙ R).mapCone qc') :=
    (isLimitOfPreserves R h).ofIsoLimit (Cone.ext (Iso.refl _))
  let h₂ : IsLimit ((H' ⋙ R).mapCone
      ((Cone.postcompose (towerCompletionComparison I M)).obj (E.mapCone qc))) :=
    h₁.ofIsoLimit ((Cone.functoriality _ (H' ⋙ R)).mapIso
      (extendScalarsIdealPowerQuotientConeIso I M)).symm
  let h₃ : IsLimit ((Cone.postcompose
      (Functor.whiskerRight (towerCompletionComparison I M) (H' ⋙ R))).obj
        ((H' ⋙ R).mapCone (E.mapCone qc))) :=
    h₂.ofIsoLimit (Functor.mapConePostcompose (H' ⋙ R))
  let h₄ : IsLimit ((H' ⋙ R).mapCone (E.mapCone qc)) :=
    (IsLimit.postcomposeHomEquiv
      (Functor.isoWhiskerRight (asIso (towerCompletionComparison I M)) (H' ⋙ R)) _) h₃
  let h₅ : IsLimit ((E ⋙ H' ⋙ R).mapCone qc) := h₄.ofIsoLimit (Cone.ext (Iso.refl _))
  IsLimit.mapConeEquiv
    (localCohomologyModuleTorsionDescentIso (AdicCompletion.flat_of_isNoetherian I) T hT I hTI
      (bijective_quotientMap_adicCompletion I) i).symm h₅

end Comparison

/-! ### The bootstrap situation -/

/-- For a bootstrap situation `S`, if `Hⁱ_{T'}(M^∧) → lim Hⁱ_{T'}(M^∧/I'ⁿM^∧)` is a limit cone for
the completed situation of [Stacks, Tag 0EFV] (G), then `Hⁱ_T(M) → lim Hⁱ_T(M/IⁿM)` is a limit
cone. -/
theorem nonempty_isLimit_cone_of_adicCompletion (S : BootstrapSituation.{u, u, w}) (i : ℤ)
    (h : Nonempty (IsLimit (Bootstrap.cone.{u, u} S.adicCompletion i))) :
    Nonempty (IsLimit (Bootstrap.cone.{u, u} S i)) :=
  ⟨isLimitLocalCohomologyAdicConeOfAdicCompletion S.I S.M S.T S.stableUnderSpecialization
    S.subset_adicLocus i h.some⟩

/-- The limit assertion of [Stacks, Tag 0EFR] from the complete case: in the bootstrap situation
with `A` local and `T = {𝔪}`, `Hⁱ_𝔪(M) → lim Hⁱ_𝔪(M/IⁿM)` is a limit cone for every `i ≤ s`, given
the same assertion for bootstrap situations whose ring is moreover `I`-adically complete
(`hcomplete`). -/
theorem nonempty_isLimit_cone_of_eq_closedPoint_of_complete
    (hcomplete : ∀ (S' : BootstrapSituation.{u, u, u}) [IsLocalRing S'.A]
      [IsAdicComplete S'.I S'.A], S'.T = {IsLocalRing.closedPoint S'.A} → ∀ i : ℤ, i ≤ S'.s →
        Nonempty (IsLimit (Bootstrap.cone.{u, u} S' i)))
    (S : BootstrapSituation.{u, u, w}) [IsLocalRing S.A]
    (hT : S.T = {IsLocalRing.closedPoint S.A}) (i : ℤ) (hi : i ≤ S.s) :
    Nonempty (IsLimit (Bootstrap.cone.{u, u} S i)) := by
  let S₀ := S.reuniverse
  have : IsLocalRing S₀.A := ‹IsLocalRing S.A›
  have : IsLocalRing S₀.adicCompletion.A := S₀.isLocalRing_adicCompletion hT
  have : IsAdicComplete S₀.adicCompletion.I S₀.adicCompletion.A :=
    S₀.isAdicComplete_adicCompletion
  exact nonempty_isLimit_cone_of_adicCompletion S₀ i
    (hcomplete S₀.adicCompletion (S₀.adicCompletion_T_eq hT) i hi)

end Stacks.Algebraization

end
