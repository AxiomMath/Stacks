module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ExtensionByZeroCurveCohomology
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Finite compactly supported cohomology of constructible torsion sheaves on curves

[Stacks, Tag 0GKR]: let `k` be an algebraically closed field, `X` a separated scheme of finite
type over `k` of dimension at most one, `Λ` a Noetherian ring and `F` a constructible sheaf of
`Λ`-modules on `X_étale` which is torsion. Then `H^q_c(X, F)` is a finite `Λ`-module.

## Main results

* `Stacks.EtaleCohomology.topologicalKrullDim_le_one_of_isOpenImmersion_of_denseRange`: the
  closure of a curve in a scheme of finite type over a field is a curve.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_compactlySupportedCohomologyGroup` —
  **Tag 0GKR**.

## Implementation notes

The proof is the source's. For a compactification `j : X ⟶ X̄`, `H^q_c(X, F)` is
`H^q(X̄, j_!F)` (the composite `RΓ(Spec k, -) ∘ Rf̄_* = RΓ(X̄, -)` and the exactness of `j_!`).
The scheme-theoretic closure `Z̄` of `X` in `X̄` is proper over `k` and of dimension at most one,
`j` factors as an open immersion `t : X ⟶ Z̄` followed by the closed immersion `ι : Z̄ ⟶ X̄`, and
`j_!F = ι_* t_!F` with `H^q(X̄, ι_* t_!F) = H^q(Z̄, t_!F)` since `ι` is integral. The last group is
finite by the extension-by-zero form of Tag 0GJI, part (2)
(`Stacks.EtaleCohomology.module_finite_etaleCohomology_extensionByZero_of_forall`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

-- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the module universe `u + 1` and its
-- unification against `ModuleCat.{max (u + 1) r}` fails with a universe error instead of
-- backtracking, so it is switched off here.
attribute [-instance] hasSheafifyEtale

/-! ### The closure of a curve is a curve -/

section Dimension

open Stacks.Chow in
/-- **The closure of a curve is a curve.** Let `Z` be a quasi-compact scheme locally of finite
type over a field `k` and `t : X ⟶ Z` an open immersion with dense image from a scheme of
dimension at most one. Then `Z` has dimension at most one: every point of `Z` specializes from a
generic point of an irreducible component, which lies in the dense open `X`
(`AlgebraicGeometry.genericPoints_mem_of_dense`), the relative dimension over `k` drops along
specializations (Stacks 02JW) and does not grow along `t`, and it is at most one on `X`. -/
theorem topologicalKrullDim_le_one_of_isOpenImmersion_of_denseRange {k : Type u} [Field k]
    {Z X : Scheme.{u}} (s : Z ⟶ Spec (.of k)) [LocallyOfFiniteType s] [CompactSpace Z]
    (t : X ⟶ Z) [IsOpenImmersion t] (ht : DenseRange t.base)
    (hX : topologicalKrullDim X ≤ 1) : topologicalKrullDim Z ≤ 1 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian Z := ⟨⟩
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
  have h :=
    Stacks.Intersection.ProjectionFormula.topologicalKrullDim_le_of_forall_relativeDimension_le
    k s Set.univ isClosed_univ 1 fun z _ => by
      obtain ⟨η, hη⟩ := exists_genericPoints_specializes z
      obtain ⟨x, hx⟩ := genericPoints_mem_of_dense t.opensRange
        (by rw [Scheme.Hom.coe_opensRange]; exact ht) η
      have h1 := relativeDimension_le_of_mem_closure (fieldChowSituation k) s
        (specializes_iff_mem_closure.1 hη)
      have h2 := relativeDimension_comp_eq_add_trdeg (fieldChowSituation k).dimensionFunction s t x
      have h3 := relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
        (fun t _ => fieldChowSituation_dimensionFunction_eq_zero k t) (t ≫ s) isClosed_univ
        (r := 1) (by rwa [topologicalKrullDim_univ]) (Set.mem_univ x)
      rw [hx] at h2
      have h3' : relativeDimension (fieldChowSituation k).dimensionFunction (t ≫ s) x ≤ 1 := by
        exact_mod_cast h3
      have h4 : relativeDimension (fieldChowSituation k).dimensionFunction s z ≤ 1 := by omega
      exact_mod_cast h4
  rwa [topologicalKrullDim_univ] at h

end Dimension

/-! ### Compactly supported cohomology as cohomology on the compactification -/

section CompactSupport

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-- **`H^q(X̄, ι_* G) = H^q(Z, G)` for a closed immersion `ι : Z ⟶ X̄`**, on sheaves of
`Λ`-modules: `ι_*` is exact (Tag 03QP, an integral morphism) and preserves injectives, and global
sections on `X̄` of `ι_* G` are global sections of `G`. -/
def etaleModuleCohomologyDirectImageIsoOfIsClosedImmersion {Z W : Scheme.{u}} (ι : Z ⟶ W)
    [IsClosedImmersion ι] (n : ℕ) (G : EtaleModules.{u, r} Λ Z) :
    ((etaleModuleGlobalSections.{u, r} Λ W).rightDerived n).obj
        ((etaleModuleDirectImage.{u, r} Λ ι).obj G) ≅
      ((etaleModuleGlobalSections.{u, r} Λ Z).rightDerived n).obj G :=
  have hex := etaleModuleDirectImage_exact_of_isIntegralHom Λ ι
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ ι) :=
    ((exactFunctor_iff _).1 hex).1
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, r} Λ ι) :=
    ((exactFunctor_iff _).1 hex).2
  have hac : ∀ I : EtaleModules.{u, r} Λ Z, Injective I →
      (etaleModuleGlobalSections.{u, r} Λ W).rightAcyclic
        ((etaleModuleDirectImage.{u, r} Λ ι).obj I) := fun I _ =>
    (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp => by
      obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      exact Functor.isZero_rightDerived_obj_injective_succ _ _ _
  ((Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic
      (etaleModuleDirectImage.{u, r} Λ ι) (etaleModuleGlobalSections.{u, r} Λ W) hac n).app
        G).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (etaleModuleGlobalSectionsDirectImageIso ι Λ) n).app G

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))

/-- **`H^n_c(X, F) = H^n(X̄, j_!F)`** for a compactification `j : X ⟶ X̄` (Definition 0GJZ): the
composite of `Rf̄_*` with `RΓ(Spec k, -)` is `RΓ(X̄, -)`, the direct image preserving injectives,
and `Rj_!(F[0]) = (j_!F)[0]`, extension by zero being exact. -/
def compactlySupportedCohomologyGroupSingleIso (n : ℕ) (F : EtaleModules.{u, r} Λ X) :
    (compactlySupportedCohomologyGroup.{u, r} k f j Λ n).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj F) ≅
      ((etaleModuleGlobalSections.{u, r} Λ j.space).rightDerived n).obj
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F) :=
  let e₁ := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleExtensionByZero.{u, r} Λ j.immersion) 0).app F
  let e₂ := rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, r} Λ j.toBase)
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k)))
    (etaleModuleGlobalSections.{u, r} Λ j.space)
    (etaleModuleGlobalSectionsDirectImageIso j.toBase Λ)
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) n).mapIso
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of k))).mapIso
        ((etaleModuleDerivedDirectImage.{u, r} Λ j.toBase).mapIso e₁.symm)) ≪≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) n).mapIso
      (e₂.app _).symm ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleGlobalSections.{u, r} Λ j.space)
      n).app _).symm

end CompactSupport

/-! ### Tag 0GKR -/

section Tag

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [local instance] HasDerivedCategory.standard

namespace TorsionModules

/-- A torsion sheaf of `Λ`-modules is prime-to-`1` torsion. -/
theorem isPrimeToCharacteristicTorsion_one_of_isTorsionEtaleModule {Λ : Type r} [Ring Λ]
    {X : Scheme.{u}} {F : EtaleModules.{u, r} Λ X} (ht : IsTorsionEtaleModule.{u, r} Λ X F) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology 1
      ((etaleModuleForgetAb.{u, r} Λ X).obj F) := fun V x => by
  obtain ⟨R, hR, h⟩ := ht V x
  exact ⟨R, hR, fun W g hg => by
    obtain ⟨n, hn, hz⟩ := h W g hg
    exact ⟨n, hn, Nat.coprime_one_right n, hz⟩⟩

/-- Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` of
dimension at most one, `Λ` a Noetherian ring, and `F` a constructible sheaf of `Λ`-modules on
`X_étale` which is torsion. Then `H^q_c(X, F)` is a finite `Λ`-module for every `q`.

`H^q_c(X, F)` is `Stacks.EtaleCohomology.compactlySupportedCohomologyGroup` of Definition 0GJZ, the
`q`-th cohomology of `RΓ(Spec k, Rf̄_* j_! F)`, at `F` placed in degree zero; the statement holds
for every compactification `j : X ⟶ X̄` of `X` over `k`, through which it is computed.
Constructibility is `Stacks.EtaleCohomology.IsBigSiteConstructibleEtaleModule` (Tag 03RW (3), read
on the small étale site of Tag 021B of a big étale site `B` containing `X`) and torsion is
`Stacks.EtaleCohomology.IsTorsionEtaleModule`. -/
@[stacks 0GKR, sga "4 XVII 5.3.8" "special case"]
theorem module_finite_compactlySupportedCohomologyGroup {k : Type u} [Field k] [IsAlgClosed k]
    (B : BigEtaleSite.{u}) (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hdim : topologicalKrullDim X.obj ≤ 1)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    (F : EtaleModules.{u, r} Λ X.obj) (hc : IsBigSiteConstructibleEtaleModule B X Λ F)
    (ht : IsTorsionEtaleModule.{u, r} Λ X.obj F) (q : ℤ) :
    Module.Finite Λ ((compactlySupportedCohomologyGroup.{u, r} k f j Λ q).obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj F)) := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f
  rcases lt_or_ge q 0 with hq | hq
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_compactlySupportedCohomologyGroup_single_of_neg k f j Λ F q hq)
    have : Finite ((compactlySupportedCohomologyGroup.{u, r} k f j Λ q).obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj F)) :=
      Finite.of_subsingleton
    exact Module.Finite.of_finite
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    -- the closure `Z̄` of `X` in the compactification
    let i := 𝟙 X.obj
    let Zb := j.closedSpace i
    let ι := j.closedSpaceι i
    let t := (j.closedImmersion i).toImage
    let πZ : Zb ⟶ Spec (.of k) := ι ≫ j.toBase
    have : IsProper πZ := inferInstanceAs (IsProper (j.closedSpaceι i ≫ j.toBase))
    have : CompactSpace Zb := QuasiCompact.compactSpace_of_compactSpace πZ
    have hdimZ : topologicalKrullDim Zb ≤ 1 :=
      topologicalKrullDim_le_one_of_isOpenImmersion_of_denseRange πZ t
        (IsDominant.denseRange (f := t)) hdim
    have hfin := module_finite_etaleCohomology_extensionByZero_of_forall B X πZ t Λ hdimZ 1
      (fun _ _ _ => Or.inr ‹IsProper πZ›) n F hc
      (isPrimeToCharacteristicTorsion_one_of_isTorsionEtaleModule ht)
    -- `j_! F = ι_* t_! F`
    let e₁ : (etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F ≅
        (etaleModuleDirectImage.{u, r} Λ ι).obj ((etaleModuleExtensionByZero.{u, r} Λ t).obj F) :=
      (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapIso
          ((Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X.obj) _ _).app F).symm ≪≫
        (etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ i t j.immersion ι
          (j.isPullback_restrictClosed i)).app F
    let e : (compactlySupportedCohomologyGroup.{u, r} k f j Λ n).obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X.obj) 0).obj F) ≅
        ((etaleModuleGlobalSections.{u, r} Λ Zb).rightDerived n).obj
          ((etaleModuleExtensionByZero.{u, r} Λ t).obj F) :=
      compactlySupportedCohomologyGroupSingleIso Λ k f j n F ≪≫
        ((etaleModuleGlobalSections.{u, r} Λ j.space).rightDerived n).mapIso e₁ ≪≫
        etaleModuleCohomologyDirectImageIsoOfIsClosedImmersion Λ ι n _
    exact Module.Finite.equiv e.symm.toLinearEquiv

end TorsionModules

end Tag

end Stacks.EtaleCohomology

end
