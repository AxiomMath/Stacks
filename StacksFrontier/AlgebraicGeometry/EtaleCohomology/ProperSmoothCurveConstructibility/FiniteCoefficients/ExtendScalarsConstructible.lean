module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ExtensionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstructibleExtendScalars
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.ExtendScalarsCofan
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ZModForgetConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction

/-!
# `𝒢 ⊗_ℤ Λ̲` is constructible for a constructible sheaf `𝒢` of `ℤ/ℓ`-modules

Let `ℓ` be a prime, `Λ` a Noetherian ring and `𝒢` a constructible sheaf of `ℤ/ℓ`-modules on the
small étale site of a scheme `S`. The sheaf of `Λ`-modules `𝒢 ⊗_ℤ Λ̲`
(`Stacks.EtaleCohomology.FiniteCoefficients.zmodExtendScalars`) is constructible. This is
[Stacks, Tag 0GKB] (`Stacks.EtaleCohomology.isConstructibleModuleSheaf_extendScalars`) for the
ring map `ℤ → Λ`, applied to `𝒢` viewed as a sheaf of `ℤ`-modules, which is constructible because
its underlying abelian sheaf is ([Stacks, Tag 03RW]).

The constructibility predicate of the model `EtaleModules Λ S` is read on the small étale site
of Tag 021B; extension of scalars commutes with that transport because both composites are left
adjoint to the same functor (restriction of scalars commutes with restriction of sheaves along
the dense subsite inclusion on the nose).

## Main results

* `Stacks.EtaleCohomology.FiniteCoefficients.isConstructibleEtaleModule_zmodExtendScalars`.

## References

* [Stacks Project, Tag 0GKB](https://stacks.math.columbia.edu/tag/0GKB)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.FiniteCoefficients

/-- `sheafCompose` carries an isomorphism of coefficient functors to an isomorphism. -/
def sheafComposeIsoOfIso {C : Type*} [Category C] (J : GrothendieckTopology C) {A B : Type*}
    [Category A] [Category B] {F F' : A ⥤ B} [J.HasSheafCompose F] [J.HasSheafCompose F']
    (e : F ≅ F') : sheafCompose J F ≅ sheafCompose J F' where
  hom := sheafCompose_map J e.hom
  inv := sheafCompose_map J e.inv
  hom_inv_id := by rw [← sheafCompose_comp, e.hom_inv_id, sheafCompose_id]
  inv_hom_id := by rw [← sheafCompose_comp, e.inv_hom_id, sheafCompose_id]

/-- Forgetting a `ℤ/ℓ`-module structure to abelian groups and reading the result as a `ℤ`-module
is restriction of scalars along `ℤ → ℤ/ℓ`. -/
def moduleCatIntEquivalenceForgetIso (ℓ : ℕ) :
    forget₂ (ModuleCat.{u} (ZMod ℓ)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.moduleCatIntEquivalence.{u}.functor ≅
      ModuleCat.restrictScalars.{u} (Int.castRingHom (ZMod ℓ)) :=
  Functor.isoWhiskerLeft (ModuleCat.restrictScalars.{u} (Int.castRingHom (ZMod ℓ)))
    AddCommGrpCat.moduleCatIntEquivalence.{u}.counitIso ≪≫
    Functor.rightUnitor _

section

attribute [local instance] preservesSheafification_forget₂_moduleCat_smallEtale
  moduleCat_hasLimitsOfSize

variable (Λ : Type (u + 1)) [CommRing Λ] (ℓ : ℕ) [Fact ℓ.Prime] {S : Scheme.{u}}
  (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- **Extension of scalars commutes with the transport to the small étale site of Tag 021B.**
Both composites are left adjoint to the same functor: restriction of scalars commutes with
restriction of sheaves along the dense subsite inclusion on the nose. -/
def etaleModuleToBoundedSiteExtendScalarsIso :
    extendScalarsSheaf.{u + 1} S.smallEtaleTopology ℤ Λ (Int.castRingHom Λ) ⋙
        etaleModuleToBoundedSite.{u, u + 1} Λ B hS ≅
      etaleModuleToBoundedSite.{u, 0} ℤ B hS ⋙
        extendScalarsSheaf.{u + 1} (SmallEtale.topology B S hS) ℤ Λ (Int.castRingHom Λ) :=
  let eΛ := SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)
  let eℤ := SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} ℤ)
  let resM := sheafCompose S.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))
  let resB := sheafCompose (SmallEtale.topology B S hS)
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ))
  let adj₁ := (extendScalarsSheafAdj.{u + 1} S.smallEtaleTopology ℤ Λ (Int.castRingHom Λ)).comp
    eΛ.symm.toAdjunction
  let adj₂ := eℤ.symm.toAdjunction.comp
    (extendScalarsSheafAdj.{u + 1} (SmallEtale.topology B S hS) ℤ Λ (Int.castRingHom Λ))
  -- the commutation of restriction of scalars with the transport, on the nose
  let c : eΛ.inverse ⋙ resB ≅ resM ⋙ eℤ.inverse := Iso.refl _
  let e : resB ⋙ eℤ.functor ≅ eΛ.functor ⋙ resM :=
    Functor.isoWhiskerRight eΛ.unitIso (resB ⋙ eℤ.functor) ≪≫
      Functor.isoWhiskerLeft eΛ.functor (Functor.isoWhiskerRight c eℤ.functor ≪≫
        Functor.isoWhiskerLeft resM eℤ.counitIso)
  adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e)

variable {Λ ℓ} in
/-- **`𝒢 ⊗_ℤ Λ̲` is constructible for a constructible sheaf `𝒢` of `ℤ/ℓ`-modules** and a
Noetherian ring `Λ`: [Stacks, Tag 0GKB] for `ℤ → Λ`, applied to `𝒢` viewed as a sheaf of
`ℤ`-modules ([Stacks, Tag 03RW]). -/
theorem isConstructibleEtaleModule_zmodExtendScalars [IsNoetherianRing Λ]
    (G : EtaleModules.{u, 0} (ZMod ℓ) S) (hG : IsConstructibleEtaleModule (ZMod ℓ) G) :
    IsConstructibleEtaleModule Λ (zmodExtendScalars S.smallEtaleTopology Λ ℓ G) := by
  let B := BigEtaleSite.containing S
  let hS := BigEtaleSite.contains_containing S
  let X' : B.Scheme := B.obj S hS
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B X' Λ
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, 0, 0} B X' ℤ
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : HasWeakSheafify (SmallEtale.topology B X'.obj X'.property) (ModuleCat.{u + 1} Λ) :=
    moduleSheaf_hasWeakSheafify.{u, u + 1} B _ _ Λ
  have : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ f ↦
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B ℤ f
  have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{u + 1} ℤ) := fun T V ↦
    SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B ℤ T V
  have : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ f ↦
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1, u + 1} B Λ f
  have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{u + 1} Λ) := fun T V ↦
    SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1, u + 1} B Λ T V
  let GB := (etaleModuleToBoundedSite.{u, 0} (ZMod ℓ) B hS).obj G
  have hℤ : IsConstructibleModuleSheaf B X' ℤ
      ((etaleModuleToBoundedSite.{u, 0} ℤ B hS).obj (zmodToInt S.smallEtaleTopology ℓ G)) := by
    have : ∀ (T : B.Scheme),
        HasWeakSheafify (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1} :=
      fun _ ↦ inferInstance
    have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
        HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
          AddCommGrpCat.{u + 1} := fun _ _ ↦ inferInstance
    have : ∀ (S T : B.Scheme) (f : T ⟶ S),
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ f ↦
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (AlgebraicGeometry.smallEtaleBaseChange B f)
        AddCommGrpCat.{u + 1} _ _).isRightAdjoint
    have h₁ := isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_zmod.{u, 0} B ℓ X' GB hG
    have h₂ := isConstructibleModuleSheaf_moduleCatIntEquivalence B X' _ h₁
    exact ObjectProperty.prop_of_iso _
      ((sheafComposeIsoOfIso (SmallEtale.topology B S hS)
        (moduleCatIntEquivalenceForgetIso.{u + 1} ℓ)).app GB) h₂
  exact ObjectProperty.prop_of_iso
    (fun F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ) ↦
      IsConstructibleModuleSheaf B X' Λ F)
    ((etaleModuleToBoundedSiteExtendScalarsIso Λ B hS).app
      (zmodToInt S.smallEtaleTopology ℓ G)).symm
    (isConstructibleModuleSheaf_extendScalars.{u, u + 1, 0, u + 1} B X' ℤ Λ
      (Int.castRingHom Λ) _ hℤ)

end

end Stacks.EtaleCohomology.FiniteCoefficients

end
