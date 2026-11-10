module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsAlongSurjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.EtaleModuleFunctoriality

/-!
# Constructibility of a sheaf of `𝔽_p`-modules from that of its underlying abelian sheaf

Let `G` be a sheaf of `𝔽_p`-modules on Mathlib's small étale site of a scheme `T` of a big étale
site `B`. If its underlying abelian sheaf, read on the small étale site of Stacks 021B, is a
constructible abelian sheaf, then `G` is a constructible sheaf of `𝔽_p`-modules: as a sheaf of
`ℤ`-modules it is constructible, extension of scalars along `ℤ ⟶ 𝔽_p` preserves constructibility
([Stacks, Tag 0GKB]), and extending the scalars of a sheaf of `𝔽_p`-modules back from `ℤ` gives it
back, `ℤ ⟶ 𝔽_p` being surjective.

## Main results

* `Stacks.ArtinSchreier.isIso_etaleModuleExtendScalarsAdj_counit_app`: along a surjection of
  rings, the counit of extension and restriction of scalars of étale sheaves is invertible.
* `Stacks.ArtinSchreier.isConstructibleEtaleModule_zmod_of_forget`: a sheaf of `𝔽_p`-modules whose
  underlying abelian sheaf is constructible is constructible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

section Counit

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (hρ : Function.Surjective ρ)
  (X : Scheme.{u})

open scoped ChangeOfRings _root_.Stacks.TensorProduct in
include hρ in
/-- Along a surjection of rings the counit `S ⊗_R N ⟶ N` of extension and restriction of scalars
is invertible, in any universe of modules. -/
theorem isIso_extendRestrictScalarsAdj_counit_app' (N : ModuleCat.{u + 1} Λ') :
    IsIso ((ModuleCat.extendRestrictScalarsAdj.{u + 1} ρ).counit.app N) := by
  have hb := Stacks.ModuleCat.bijective_one_tmul ρ hρ (M := (ModuleCat.restrictScalars ρ).obj N)
    (fun a ha n => by rw [show a • n = ρ a • n from rfl, RingHom.mem_ker.1 ha, zero_smul])
  have hcomp : ∀ n : N, ((ModuleCat.extendRestrictScalarsAdj.{u + 1} ρ).counit.app N).hom
      ((1 : Λ') ⊗ₜ[Λ, ρ] (show (ModuleCat.restrictScalars ρ).obj N from n)) = n := fun n => by
    change (1 : Λ') • n = n
    exact one_smul _ _
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy => ?_, fun n => ⟨_, hcomp n⟩⟩
  obtain ⟨x', rfl⟩ := hb.2 x
  obtain ⟨y', rfl⟩ := hb.2 y
  exact congrArg _ ((hcomp x').symm.trans (hxy.trans (hcomp y')) : x' = y')

include hρ in
/-- **Along a surjection of rings, extending the scalars of a sheaf of modules restricted from the
target gives it back.** -/
theorem isIso_etaleModuleExtendScalarsAdj_counit_app (G : EtaleModules.{u, 0} Λ' X) :
    IsIso ((etaleModuleExtendScalarsAdj ρ X).counit.app G) := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1} ρ
  let c := (adj.whiskerRight X.Etaleᵒᵖ).counit.app G.obj
  have hc : IsIso c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ c fun V =>
    isIso_extendRestrictScalarsAdj_counit_app' ρ hρ (G.obj.obj V)
  have hP := (Presheaf.isSheaf_of_iso_iff (asIso c)).2 G.property
  have := isIso_toSheafify X.smallEtaleTopology hP
  have hlift : IsIso (sheafifyLift X.smallEtaleTopology c G.property) :=
    IsIso.of_isIso_fac_left (toSheafify_sheafifyLift X.smallEtaleTopology c G.property)
  have hmap : IsIso ((sheafToPresheaf X.smallEtaleTopology _).map
      ((etaleModuleExtendScalarsAdj ρ X).counit.app G)) := by
    change IsIso ((Sheaf.adjunction X.smallEtaleTopology adj).counit.app G).hom
    rw [Sheaf.adjunction_counit_app_hom]
    exact hlift
  exact isIso_of_reflects_iso _ (sheafToPresheaf X.smallEtaleTopology _)

end Counit

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **A sheaf of `𝔽_p`-modules whose underlying abelian sheaf is constructible is
constructible.** -/
theorem isConstructibleEtaleModule_zmod_of_forget (B : BigEtaleSite.{u}) (T : B.Scheme) (p : ℕ)
    [Fact p.Prime] (G : EtaleModules.{u, 0} (ZMod p) T.obj)
    (K : Sheaf T.obj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (etaleModuleForgetAb.{u, 0} (ZMod p) T.obj).obj G ≅ K)
    (hK : IsConstructibleAbelianSheaf B T
      ((SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}).inverse.obj K)) :
    IsBigSiteConstructibleEtaleModule B T (ZMod p) G := by
  have := fun (S T : B.Scheme) (f : T ⟶ S) =>
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B ℤ f
  have := SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B ℤ
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let Gℤ := (etaleModuleRestrictScalars φ T.obj).obj G
  let J := SmallEtale.topology B T.obj T.property
  let E := Sheaf.coefficientEquivalence J AddCommGrpCat.moduleCatIntEquivalence.{u + 1}
  let inv := (SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}).inverse
  have hQ := isConstructibleModuleSheaf_moduleCatIntEquivalence B T _ hK
  let iso2 : inv.obj ((etaleModuleForgetAb.{u, 0} (ZMod p) T.obj).obj G) ≅
      E.inverse.obj ((etaleModulesToSmallEtale B T ℤ).obj Gℤ) :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _)
  let iso3 : E.functor.obj (inv.obj K) ≅ (etaleModulesToSmallEtale B T ℤ).obj Gℤ :=
    E.functor.mapIso (inv.mapIso e.symm ≪≫ iso2) ≪≫ E.counitIso.app _
  have hℤ : IsBigSiteConstructibleEtaleModule B T ℤ Gℤ :=
    isConstructibleModuleSheaf_congr B ℤ T iso3 hQ
  have h2 := isConstructibleEtaleModule_etaleModuleExtendScalars B T φ Gℤ hℤ
  have := isIso_etaleModuleExtendScalarsAdj_counit_app φ (ZMod.intCast_surjective) T.obj G
  exact IsBigSiteConstructibleEtaleModule.of_iso B (ZMod p)
    (asIso ((etaleModuleExtendScalarsAdj φ T.obj).counit.app G)) h2

end Stacks.ArtinSchreier

end
