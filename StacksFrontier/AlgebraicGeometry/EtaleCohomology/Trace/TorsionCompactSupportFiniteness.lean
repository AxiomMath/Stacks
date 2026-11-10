module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportSheafFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CompactSupportFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLeray

/-!
# Finiteness of `Hⁱ_c(X_k̄, F)` for constructible `ℓ`-power torsion sheaves, in any dimension

Let `X` be separated of finite type over a finite field `k`, `k̄` an algebraic closure of `k`, and
`F` a constructible sheaf of `ℤ_ℓ`-modules on `X_étale` killed by `ℓ^N`. Then every
`Hⁱ_c(X_k̄, F)` is finite. `F` is the restriction of scalars of a constructible sheaf `G` of
`ℤ/ℓ^N`-modules (coextension of scalars along `ℤ_ℓ ⟶ ℤ/ℓ^N`, whose kernel `ℓ^N ℤ_ℓ` kills `F`),
`Hⁱ_c(X_k̄, -)` commutes with restriction of scalars, and `Hⁱ_c(X_k̄, G) = Hⁱ_c` over `k̄` of
`G|_{X_k̄}` is a finite `ℤ/ℓ^N`-module (Stacks 0GL0 over a field,
`Stacks.EtaleCohomology.TorsionModules.module_finite_compactlySupportedCohomologyGroup_zmod`).
This is the input `Stacks.EtaleCohomology.LAdicSheaf.TorsionCompactSupportFinitenessInput` of the
Leray weight implication (Stacks 03V3, 03VH). Stacks 0GKV enters as `h0GKV` until it lands.

The cohomology `Hⁱ_c(X_k̄, -)` here is the one of
`Stacks.EtaleCohomology.compactSupportSheafCohomology`, built in the standard model of the derived
category (`HasDerivedCategory.standard`).

## Main results

* `AlgebraicGeometry.BigEtaleSite.contains_spec_of_isAlgebraic`.
* `Stacks.EtaleCohomology.finite_compactSupportSheafCohomology_zmod_of_isConstructible`.
* `Stacks.EtaleCohomology.LAdicSheaf.torsionCompactSupportFinitenessInput_of_0GKV`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

section Finite

/-- The spectrum of an algebraic extension of a finite field is an object of every big étale
site: the extension is countable. -/
theorem _root_.AlgebraicGeometry.BigEtaleSite.contains_spec_of_isAlgebraic (B : BigEtaleSite.{u})
    (k : Type u) [Field k] [Finite k] (K : Type u) [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] :
    B.Contains (Spec (.of K)) := by
  have hk : Cardinal.mk K ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max k K).trans
      (max_le (Cardinal.mk_le_aleph0) le_rfl)
  change (Spec (.of K)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact (max_le le_rfl hk).trans_lt B.aleph0_lt_cutoff


variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Finite k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]

/-- **`Hⁱ_c(X_k̄, G)` is finite** for a constructible sheaf `G` of `ℤ/ℓ^m`-modules on a scheme
separated of finite type over a finite field, in any dimension: it is `Hⁱ_c` over `k̄` of
`G|_{X_k̄}`, which is finite by Stacks 0GL0 over the field `k̄`. `h0GKV` is Stacks 0GKV. -/
theorem finite_compactSupportSheafCohomology_zmod_of_isConstructible (ℓ m : ℕ) [Fact ℓ.Prime]
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ)))
    (G : EtaleModules.{u, 0} (ZMod (ℓ ^ m)) X.1)
    (hG : IsBigSiteConstructibleEtaleModule B X (ZMod (ℓ ^ m)) G) (i : ℤ) :
    Finite ((compactSupportSheafCohomology (ZMod (ℓ ^ m)) f j kbar i).obj G) := by
  have : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let Λ := ZMod (ℓ ^ m)
  let gX := pullback.fst f (specAlgebraMap k kbar)
  let fX := pullback.snd f (specAlgebraMap k kbar)
  have hY : B.Contains (pullback f (specAlgebraMap k kbar)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fX
      (BigEtaleSite.contains_spec_of_isAlgebraic B k kbar)
  let XB : B.Scheme := B.obj _ hY
  let gB : XB ⟶ X := ObjectProperty.homMk gX
  have hc := isConstructibleEtaleModule_inverseImage B Λ gB hG
  have h0 := TorsionModules.module_finite_compactlySupportedCohomologyGroup_zmod B XB fX
    (compactificationFieldBaseChange f j kbar) ℓ m h0GKV
    ((etaleModuleInverseImage.{u, 0} Λ gX).obj G) hc (isTorsionEtaleModule_zmod _ _) i
  let e₁ : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ gX).obj G) :=
    ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app G).symm
  let e₂ : (compactSupportSheafCohomology Λ f j kbar i).obj G ≅
      (compactlySupportedCohomologyGroup.{u, 0} kbar fX
        (compactificationFieldBaseChange f j kbar) Λ i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((etaleModuleInverseImage.{u, 0} Λ gX).obj
            G)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
      (compactSupportFrobeniusCohomologySingleIso f j kbar G ≪≫
        DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} Λ
          (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd j.toBase (specAlgebraMap k kbar))).mapIso
              ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e₁))) ≪≫
        derivedDirectImageSectionsExtensionByZeroIso f j kbar Λ _)
  have : Module.Finite Λ ((compactSupportSheafCohomology Λ f j kbar i).obj G) :=
    Module.Finite.equiv e₂.symm.toLinearEquiv
  exact Module.finite_of_finite Λ

end Finite

namespace LAdicSheaf

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`LAdicSheaf.TorsionCompactSupportFinitenessInput` from Stacks 0GKV**: for `X` separated of
finite type over a finite field `k`, `k̄` an algebraic closure of `k` and `F` a constructible sheaf
of `ℤ_ℓ`-modules on `X` killed by `ℓ^N`, every `H^a_c(X_k̄, F)` is finite. `F` is the restriction
of scalars along `ℤ_ℓ ⟶ ℤ/ℓ^N` of the constructible sheaf `Hom_{ℤ_ℓ}(ℤ/ℓ^N, F)`, `H^a_c(X_k̄, -)`
commutes with restriction of scalars
(`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyGroupRestrictScalarsIso`), and
`Stacks.EtaleCohomology.finite_compactSupportSheafCohomology_zmod_of_isConstructible` applies.
`h0GKV` is Stacks 0GKV. -/
theorem torsionCompactSupportFinitenessInput_of_0GKV
    (h0GKV : ∀ (X S : B.Scheme) (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
      [GeometricallyConnected f], (∀ s, topologicalKrullDim (f.fiber s) ≤ 1) →
      ∀ [IsNoetherian S.obj] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ),
        IsBigSiteConstructibleEtaleModule B S (ZMod ℓ) (rightDerivedConstantUnit f q (ZMod ℓ))) :
    LAdicSheaf.TorsionCompactSupportFinitenessInput B ℓ := by
  intro k _ _ kbar _ _ _ p q _ _ _ _ X _ f _ _ _ j F hF ⟨N, hN⟩ a
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  let ρ : ℤ_[ℓ] →+* ZMod (ℓ ^ N) := PadicInt.toZModPow N
  have hρ : Function.Surjective ρ := ZMod.ringHom_surjective ρ
  have hker : ∀ (V : X.1.Etaleᵒᵖ), ∀ c ∈ RingHom.ker ρ, ∀ x : F.obj.obj V, c • x = 0 := by
    intro V c hc x
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hc
    obtain ⟨d, rfl⟩ := hc
    have hx : (ℓ ^ N : ℕ) • x = 0 := by
      rw [← etaleModules_map_nsmul_id_apply ℤ_[ℓ] F (ℓ ^ N) V x, hN, Functor.map_zero]
      rfl
    rw [mul_comm, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]
  let G := (etaleModuleCoextendScalars ρ X.1).obj F
  let ε : (etaleModuleRestrictScalars ρ X.1).obj G ≅ F :=
    etaleModuleRestrictCoextendScalarsIso ρ hρ F hker
  have hG : IsBigSiteConstructibleEtaleModule B X (ZMod (ℓ ^ N)) G :=
    isConstructibleEtaleModule_of_restrictScalars ρ hρ B X G
      (IsBigSiteConstructibleEtaleModule.of_iso B ℤ_[ℓ] ε.symm hF)
  have hfin := finite_compactSupportSheafCohomology_zmod_of_isConstructible B X f j kbar ℓ N h0GKV
    G hG a
  let eK : (etaleModuleRestrictScalars ρ X.1).mapCochainComplexPlus.obj
        ((sheafSingleComplex (ZMod (ℓ ^ N))).obj G) ≅
      (sheafSingleComplex ℤ_[ℓ]).obj ((etaleModuleRestrictScalars ρ X.1).obj G) :=
    ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleRestrictScalars ρ X.1) (ComplexShape.up ℤ) 0).app G)
  let e : (ModuleCat.restrictScalars.{u + 1} ρ).obj
        ((compactSupportSheafCohomology (ZMod (ℓ ^ N)) f j kbar a).obj G) ≅
      (compactSupportSheafCohomology ℤ_[ℓ] f j kbar a).obj F :=
    compactSupportFrobeniusCohomologyGroupRestrictScalarsIso ρ f j kbar
        ((sheafSingleComplex (ZMod (ℓ ^ N))).obj G) a ≪≫
      (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) a).mapIso eK ≪≫
      (compactSupportSheafCohomology ℤ_[ℓ] f j kbar a).mapIso ε
  have : Finite ((ModuleCat.restrictScalars.{u + 1} ρ).obj
      ((compactSupportSheafCohomology (ZMod (ℓ ^ N)) f j kbar a).obj G)) := hfin
  exact Finite.of_equiv _ e.toLinearEquiv.toEquiv

end LAdicSheaf

end Stacks.EtaleCohomology

end
