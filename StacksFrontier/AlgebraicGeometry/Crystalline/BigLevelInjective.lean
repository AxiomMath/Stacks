module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.ChangeBaseAbelianInjectives
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules

/-!
# Restriction to a finite level carries injective modules to injective modules

Let `X/S` be a global crystalline situation with affine base, `S_e ⊂ S` a finite divided power
level and `u_e : CRIS(X/S_e) ⥤ CRIS(X/S)` change of divided power base along `S_e ⟶ S`.  This
file proves that the restriction `N ↦ N_e` of sheaves of `𝒪_{X/S}`-modules along `u_e` carries
injective modules to injective modules — the first half of the hint of [Stacks, Tag 07MV] ("the
sheaves `F_e` are injective modules too"), at module coefficients on the big crystalline site.

## How

Restriction along `u_e` is the right adjoint of the module-level lower shriek
`u_{e!} = SheafOfModules.pullback`, so it suffices that `u_{e!}` preserve monomorphisms.  At module
coefficients this is not formal (it is false for the inclusion of the small crystalline site,
whose lower shriek is `Crystalline.GlobalCrystallineSituation.SmallSite.moduleLowerShriek`); here
it holds because `u_e` is *sieve-like*: every slice functor `CRIS(X/S_e)/W ⥤ CRIS(X/S)/u_e(W)` is
an equivalence
(`...isEquivalence_overPost_levelChangeBase`), so by [Stacks, Tag 0798] in the form
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence` the underlying
abelian sheaf of `u_{e!}M` is the abelian lower shriek of the underlying abelian sheaf of `M`.
The abelian lower shriek along a change of base is exact
(`...preservesFiniteLimits_changeBaseAbelianLowerShriek`, [Stacks, Tag 00X4]), and forgetting the
module structure is faithful and preserves monomorphisms.

## Main results

* `Crystalline.GlobalCrystallineSituation.isIso_levelLowerShriekForgetComparison` — the
  comparison of [Stacks, Tag 0798] for `u_e` is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.preservesMonomorphisms_levelLowerShriek` — the
  module-level lower shriek along `u_e` preserves monomorphisms.
* `Crystalline.GlobalCrystallineSituation.injective_levelPullback_obj` — **`N_e` is injective
  for `N` injective.**
* `Crystalline.GlobalCrystallineSituation.rightAcyclic_levelPullback_obj` — hence `N_e` is
  acyclic for `Γ(CRIS(X/S_e), -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline.GlobalCrystallineSituation

open SmallSite

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme] {e : ℕ} (he : S.IsLevel e)

/-- The structure sheaf `𝒪_{X/S_e}` as the inverse image of `𝒪_{X/S}` along `u_e`, the spelling
of the general lower shriek of modules. -/
abbrev levelChangeBaseRing : Sheaf (topology (S.levelSituation he)) RingCat.{u} :=
  Stacks.SheafOfModules.inverseImageRing (topology (S.levelSituation he)) (topology S)
    (S.levelChangeBase he) (crystallineStructureSheaf S)

/-- The identity structure morphism of sheaves of rings along `u_e`, in the spelling of the
general lower shriek of modules. -/
abbrev levelStructureMap : S.levelChangeBaseRing he ⟶ S.levelChangeBaseRing he :=
  Stacks.SheafOfModules.structureMap (topology (S.levelSituation he)) (topology S)
    (S.levelChangeBase he) (crystallineStructureSheaf S)

/-- The modules over `u_e^{-1}𝒪_{X/S}` are the modules over `𝒪_{X/S_e}`, which form an abelian
category; registered locally so that instance search does not try the general instance at an
undetermined universe. -/
local instance instAbelianLevelRingModules :
    Abelian (SheafOfModules.{u + 1} (S.levelChangeBaseRing he)) :=
  instAbelianBigModuleSheaf (S.levelSituation he)

/-- **The comparison of [Stacks, Tag 0798] is an isomorphism for `u_e`**: the slice functors of
`u_e` are equivalences and the structure morphism of rings is the identity. -/
theorem isIso_levelLowerShriekForgetComparison :
    IsIso (Stacks.SheafOfModules.lowerShriekForgetComparison.{u, u + 1} (S.levelChangeBase he)
      (S.levelStructureMap he)) :=
  Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_sliceEquivalence _ _ _ _

/-- **The module-level lower shriek along `u_e` preserves monomorphisms.**  Its underlying
abelian sheaf is the abelian lower shriek of the underlying abelian sheaf
(`isIso_levelLowerShriekForgetComparison`), which is exact, [Stacks, Tag 00X4]. -/
instance preservesMonomorphisms_levelLowerShriek :
    (SheafOfModules.pullback.{u + 1} (S.levelStructureMap he)).PreservesMonomorphisms := by
  have := S.isIso_levelLowerShriekForgetComparison he
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (S.levelChangeBase he) AddCommGrpCat.{u + 1} (topology (S.levelSituation he))
      (topology S)) :=
    preservesFiniteLimits_changeBaseAbelianLowerShriek _ _ _ _ _
  have : PreservesFiniteLimits ((S.levelChangeBase he).sheafPullback AddCommGrpCat.{u + 1}
      (topology (S.levelSituation he)) (topology S)) :=
    preservesFiniteLimits_of_natIso
      (Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _).symm
  refine ⟨fun {A B} m hm => ?_⟩
  let c := Stacks.SheafOfModules.lowerShriekForgetComparison.{u, u + 1} (S.levelChangeBase he)
    (S.levelStructureMap he)
  have hc := c.naturality m
  have h₁ : Mono ((SheafOfModules.toSheaf.{u + 1} (S.levelChangeBaseRing he) ⋙
      (S.levelChangeBase he).sheafPullback AddCommGrpCat.{u + 1} (topology (S.levelSituation he))
        (topology S)).map m) := by
    change Mono (((S.levelChangeBase he).sheafPullback AddCommGrpCat.{u + 1} _ _).map
      ((SheafOfModules.toSheaf.{u + 1} (S.levelChangeBaseRing he)).map m))
    infer_instance
  have h₂ : Mono ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).map
      ((SheafOfModules.pullback.{u + 1} (S.levelStructureMap he)).map m)) := by
    have e : c.app A ≫ (SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).map
        ((SheafOfModules.pullback.{u + 1} (S.levelStructureMap he)).map m) =
          (SheafOfModules.toSheaf.{u + 1} (S.levelChangeBaseRing he) ⋙
            (S.levelChangeBase he).sheafPullback AddCommGrpCat.{u + 1}
              (topology (S.levelSituation he)) (topology S)).map m ≫ c.app B := hc.symm
    have hg : (SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).map
        ((SheafOfModules.pullback.{u + 1} (S.levelStructureMap he)).map m) =
          inv (c.app A) ≫ ((SheafOfModules.toSheaf.{u + 1} (S.levelChangeBaseRing he) ⋙
            (S.levelChangeBase he).sheafPullback AddCommGrpCat.{u + 1}
              (topology (S.levelSituation he)) (topology S)).map m ≫ c.app B) := by
      rw [← e, IsIso.inv_hom_id_assoc]
    rw [hg]
    have hA : IsIso (c.app A) := NatIso.isIso_app_of_isIso c A
    have hB : IsIso (c.app B) := NatIso.isIso_app_of_isIso c B
    exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _
      (@mono_comp _ _ _ _ _ _ h₁ _ (IsIso.mono_of_iso _))
  exact (SheafOfModules.toSheaf.{u + 1} _).mono_of_mono_map h₂

/-- **Restriction to a finite level carries injective modules to injective modules**: the first
half of the hint of [Stacks, Tag 07MV], at module coefficients on the big crystalline site. -/
theorem injective_levelPullback_obj (N : BigModuleSheaf S) [Injective N] :
    Injective ((S.levelPullback he).obj N) :=
  Injective.injective_of_adjoint
    (SheafOfModules.pullbackPushforwardAdjunction.{u + 1} (S.levelStructureMap he)) N

/-- **Restriction to a finite level carries injective modules to `Γ(CRIS(X/S_e), -)`-acyclic
modules.** -/
theorem rightAcyclic_levelPullback_obj
    [HasDerivedCategory.{w'} (BigModuleSheaf (S.levelSituation he))]
    [HasDerivedCategory.{w} (ModuleCat.{u + 1} Γ((S.levelSituation he).S.scheme, ⊤))]
    (N : BigModuleSheaf S) [Injective N] :
    (bigBaseModuleGlobalSections (S.levelSituation he)).rightAcyclic
      ((S.levelPullback he).obj N) :=
  have := S.injective_levelPullback_obj he N
  Functor.rightAcyclic_of_injective _ _

end Crystalline.GlobalCrystallineSituation
