module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianAdjunctionForget
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# Abelian inverse images commuting with the universe lift

Let `v : A ⥤ B` be a continuous functor of sites and let `f`, `f'` be morphisms of topoi
`Sh(B) → Sh(A)`, on sheaves of sets in the universes `t` and `max t s`, whose direct images are
both restriction along `v`. This file gives a criterion for the abelian inverse images of `f` and
`f'` to commute with lifting the universe of abelian sheaves from `t` to `max t s`:

`(F ⋙ ULift) ↦ f'⁻¹(F ⋙ ULift)` is `F ↦ (f⁻¹F) ⋙ ULift`.

The comparison is the mate of the identification of the two restrictions along `v` with the lift
(`Stacks.Sheaves.UniverseLift.sheafPushforwardContinuousULiftIso`). It is invertible as soon as the
unit of `f` is invertible, the inverse image of `f'` is fully faithful, and the lift of every
`f⁻¹F` lies, as a sheaf of sets, in the essential image of the inverse image of `f'`.

## Main definitions

* `Stacks.Topos.AbelianPushforward.abelianPushforwardIsoSheafPushforwardContinuous`: the abelian
  direct image of a morphism of topoi whose direct image of sheaves of sets is restriction along a
  continuous functor is restriction of abelian sheaves along that functor.
* `Stacks.Topos.AbelianPushforward.abelianInverseImageULiftIso`: the comparison of the two
  abelian inverse images with the universe lift, under the criterion above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.UniverseLift

namespace Stacks.Topos.AbelianPushforward

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianMonoidalCategorySheaf
  Stacks.Sites.AbelianPullback.braidedCategorySheaf
  Stacks.Sites.AbelianPullback.preservesFiniteLimitsSheafPushforward
  Stacks.Sites.AbelianPullback.braidedSheafPushforward
  Stacks.Sites.AbelianPullback.braidedPushforwardOfTopoi

universe w s t u₀ v₀ u₁ v₁

variable {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B] (v : A ⥤ B)
  (JA : GrothendieckTopology A) (JB : GrothendieckTopology B) [v.IsContinuous JA JB]

/-- **The abelian direct image of a morphism of topoi given by restriction along a continuous
functor is restriction of abelian sheaves along that functor.** -/
def abelianPushforwardIsoSheafPushforwardContinuous
    [(v.sheafPushforwardContinuous (Type w) JA JB).IsRightAdjoint]
    (f : MorphismOfTopoi (Sheaf JB (Type w)) (Sheaf JA (Type w)))
    (α : f.pushforward ≅ v.sheafPushforwardContinuous (Type w) JA JB) :
    abelianPushforward JB f ≅ v.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB :=
  Functor.isoWhiskerLeft (Sites.AbelianSheaf.internalSheaf JB)
      (Functor.isoWhiskerRight (Functor.mapCommGrpNatIso α)
        (Sites.AbelianSheaf.externalSheaf JA)) ≪≫
    Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso v JA JB

section ULift

variable [(v.sheafPushforwardContinuous (Type t) JA JB).IsRightAdjoint]
  [(v.sheafPushforwardContinuous (Type (max t s)) JA JB).IsRightAdjoint]
  (f : MorphismOfTopoi (Sheaf JB (Type t)) (Sheaf JA (Type t)))
  (f' : MorphismOfTopoi (Sheaf JB (Type (max t s))) (Sheaf JA (Type (max t s))))
  (α : f.pushforward ≅ v.sheafPushforwardContinuous (Type t) JA JB)
  (α' : f'.pushforward ≅ v.sheafPushforwardContinuous (Type (max t s)) JA JB)

/-- The abelian adjunction of a morphism of topoi given by restriction along `v`, with the
abelian direct image read as restriction of abelian sheaves along `v`. -/
def abelianInverseImageAdjRestriction (f : MorphismOfTopoi (Sheaf JB (Type w)) (Sheaf JA (Type w)))
    [(v.sheafPushforwardContinuous (Type w) JA JB).IsRightAdjoint]
    (α : f.pushforward ≅ v.sheafPushforwardContinuous (Type w) JA JB) :
    Sites.abelianInverseImage f ⊣ v.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB :=
  (abelianInverseImageAdjPushforward JB f).ofNatIsoRight
    (abelianPushforwardIsoSheafPushforwardContinuous v JA JB f α)

/-- **The comparison of the two abelian inverse images with the universe lift**: the mate of the
commutation of restriction along `v` with the lift. -/
def abelianInverseImageULiftHom :
    uliftSheafFunctor.{s, t} JA ⋙ Sites.abelianInverseImage f' ⟶
      Sites.abelianInverseImage f ⋙ uliftSheafFunctor.{s, t} JB :=
  ((mateEquiv (abelianInverseImageAdjRestriction v JA JB f α)
    (abelianInverseImageAdjRestriction v JA JB f' α')).symm
      (TwoSquare.mk _ _ _ _ (sheafPushforwardContinuousULiftIso JA JB v).hom))

/-- The component of the comparison, as the mate formula computes it. -/
theorem abelianInverseImageULiftHom_app (F : Sheaf JA AddCommGrpCat.{t}) :
    (abelianInverseImageULiftHom v JA JB f f' α α').app F =
      (Sites.abelianInverseImage f').map ((uliftSheafFunctor.{s, t} JA).map
          ((abelianInverseImageAdjRestriction v JA JB f α).unit.app F)) ≫
        (Sites.abelianInverseImage f').map
          ((sheafPushforwardContinuousULiftIso JA JB v).hom.app
            ((Sites.abelianInverseImage f).obj F)) ≫
        (abelianInverseImageAdjRestriction v JA JB f' α').counit.app
          ((uliftSheafFunctor.{s, t} JB).obj ((Sites.abelianInverseImage f).obj F)) := by
  simp [abelianInverseImageULiftHom, mateEquiv]

/-- The counit of the abelian adjunction is, on underlying sheaves of sets, the counit of the
adjunction of sheaves of sets. -/
theorem abelianInverseImageAdjPushforward_counit_app_forget
    (f : MorphismOfTopoi (Sheaf JB (Type w)) (Sheaf JA (Type w))) (M : Sheaf JB AddCommGrpCat.{w}) :
    (sheafCompose JB (forget AddCommGrpCat.{w})).map
        ((abelianInverseImageAdjPushforward JB f).counit.app M) =
      f.adj.counit.app ((sheafCompose JB (forget AddCommGrpCat.{w})).obj M) := by
  refine Eq.trans (congrArg (sheafCompose JB (forget AddCommGrpCat.{w})).map
    (Adjunction.homEquiv_symm_id _ _).symm) ?_
  exact (abelianInverseImageAdjPushforward_homEquiv_symm_forget JB f _ M (𝟙 _)).trans
    ((congrArg (f.adj.homEquiv _ _).symm
      (CategoryTheory.Functor.map_id (sheafCompose JA (forget AddCommGrpCat.{w})) _)).trans
        (Adjunction.homEquiv_symm_id _ _))

include α in
omit [(v.sheafPushforwardContinuous (Type (max t s)) JA JB).IsRightAdjoint] in
/-- The unit of the abelian adjunction of `f` is invertible when that of `f` on sheaves of sets
is. -/
theorem isIso_abelianInverseImageAdjRestriction_unit_app (hunit : IsIso f.adj.unit)
    (F : Sheaf JA AddCommGrpCat.{t}) :
    IsIso ((abelianInverseImageAdjRestriction v JA JB f α).unit.app F) := by
  have h : (abelianInverseImageAdjRestriction v JA JB f α).unit.app F =
      (abelianInverseImageAdjPushforward JB f).unit.app F ≫
        (abelianPushforwardIsoSheafPushforwardContinuous v JA JB f α).hom.app _ := by
    rw [← Adjunction.homEquiv_id, abelianInverseImageAdjRestriction,
      Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
  have : IsIso ((sheafCompose JA (forget AddCommGrpCat.{t})).map
      ((abelianInverseImageAdjPushforward JB f).unit.app F)) := by
    rw [abelianInverseImageAdjPushforward_unit_forget]
    exact NatIso.isIso_app_of_isIso f.adj.unit _
  have : IsIso ((abelianInverseImageAdjPushforward JB f).unit.app F) :=
    isIso_of_reflects_iso _ (sheafCompose JA (forget AddCommGrpCat.{t}))
  rw [h]
  infer_instance

omit [(v.sheafPushforwardContinuous (Type t) JA JB).IsRightAdjoint]
  [(v.sheafPushforwardContinuous (Type (max t s)) JA JB).IsRightAdjoint] in
/-- The counit of the abelian adjunction of `f'` is invertible at an abelian sheaf whose
underlying sheaf of sets lies in the essential image of the inverse image of `f'`, when that
inverse image is fully faithful. -/
theorem isIso_abelianInverseImageAdjRestriction_counit_app
    [(v.sheafPushforwardContinuous (Type w) JA JB).IsRightAdjoint]
    (f' : MorphismOfTopoi (Sheaf JB (Type w)) (Sheaf JA (Type w)))
    (α' : f'.pushforward ≅ v.sheafPushforwardContinuous (Type w) JA JB) [f'.inverseImage.Full]
    [f'.inverseImage.Faithful] (M : Sheaf JB AddCommGrpCat.{w})
    (hM : f'.inverseImage.essImage ((sheafCompose JB (forget AddCommGrpCat.{w})).obj M)) :
    IsIso ((abelianInverseImageAdjRestriction v JA JB f' α').counit.app M) := by
  have h : (abelianInverseImageAdjRestriction v JA JB f' α').counit.app M =
      (Sites.abelianInverseImage f').map
          ((abelianPushforwardIsoSheafPushforwardContinuous v JA JB f' α').inv.app M) ≫
        (abelianInverseImageAdjPushforward JB f').counit.app M := by
    rw [← Adjunction.homEquiv_symm_id, abelianInverseImageAdjRestriction,
      Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.id_comp,
      Adjunction.homEquiv_counit]
  have : IsIso ((sheafCompose JB (forget AddCommGrpCat.{w})).map
      ((abelianInverseImageAdjPushforward JB f').counit.app M)) := by
    rw [abelianInverseImageAdjPushforward_counit_app_forget]
    exact (f'.adj.isIso_counit_app_iff_mem_essImage).2 hM
  have : IsIso ((abelianInverseImageAdjPushforward JB f').counit.app M) :=
    isIso_of_reflects_iso _ (sheafCompose JB (forget AddCommGrpCat.{w}))
  rw [h]
  infer_instance

/-- Forgetting the group operations commutes with lifting the universe. -/
def forgetULiftIso {C : Type u₀} [Category.{v₀} C] (J : GrothendieckTopology C)
    (N : Sheaf J AddCommGrpCat.{t}) :
    (sheafCompose J (forget AddCommGrpCat.{max t s})).obj ((uliftSheafFunctor.{s, t} J).obj N) ≅
      (sheafCompose J uliftFunctor.{s, t}).obj
        ((sheafCompose J (forget AddCommGrpCat.{t})).obj N) :=
  (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

include α' in
/-- **The abelian inverse images of `f` and `f'` commute with the universe lift**, as soon as the
unit of `f` is invertible, the inverse image of `f'` is fully faithful, and the lift of every
`f⁻¹F` lies, as a sheaf of sets, in the essential image of the inverse image of `f'`. -/
def abelianInverseImageULiftIso (hunit : IsIso f.adj.unit) [f'.inverseImage.Full]
    [f'.inverseImage.Faithful]
    (hess : ∀ F : Sheaf JA (Type t), f'.inverseImage.essImage
      ((sheafCompose JB uliftFunctor.{s, t}).obj (f.inverseImage.obj F))) :
    uliftSheafFunctor.{s, t} JA ⋙ Sites.abelianInverseImage f' ≅
      Sites.abelianInverseImage f ⋙ uliftSheafFunctor.{s, t} JB :=
  have : ∀ F, IsIso ((abelianInverseImageULiftHom v JA JB f f' α α').app F) := fun F => by
    rw [abelianInverseImageULiftHom_app]
    have := isIso_abelianInverseImageAdjRestriction_unit_app v JA JB f α hunit F
    have := isIso_abelianInverseImageAdjRestriction_counit_app v JA JB f' α' _
      (f'.inverseImage.essImage.prop_of_iso
        (forgetULiftIso.{s, t} JB ((Sites.abelianInverseImage f).obj F)).symm
        (hess ((sheafCompose JA (forget AddCommGrpCat.{t})).obj F)))
    infer_instance
  have := NatIso.isIso_of_isIso_app (abelianInverseImageULiftHom v JA JB f f' α α')
  asIso (abelianInverseImageULiftHom v JA JB f f' α α')

end ULift

section CohomologyTransfer

variable {𝒜 𝒜' ℬ ℬ' : Type*} [Category* 𝒜] [Category* 𝒜'] [Category* ℬ] [Category* ℬ']
  [Abelian 𝒜] [Abelian 𝒜'] [Abelian ℬ] [Abelian ℬ']
  [HasInjectiveResolutions 𝒜] [HasInjectiveResolutions 𝒜'] [HasInjectiveResolutions ℬ]
  [HasInjectiveResolutions ℬ']
  (LA : 𝒜 ⥤ 𝒜') [LA.Additive] [PreservesFiniteLimits LA] [PreservesFiniteColimits LA]
  [LA.PreservesInjectiveObjects]
  (LB : ℬ ⥤ ℬ') [LB.Additive] [PreservesFiniteLimits LB] [PreservesFiniteColimits LB]
  [LB.PreservesInjectiveObjects]
  (h : 𝒜 ⥤ ℬ) (h' : 𝒜' ⥤ ℬ')
  (ΓA : 𝒜 ⥤ AddCommGrpCat.{t}) (ΓA' : 𝒜' ⥤ AddCommGrpCat.{max t s}) [ΓA.Additive] [ΓA'.Additive]
  (ΓB : ℬ ⥤ AddCommGrpCat.{t}) (ΓB' : ℬ' ⥤ AddCommGrpCat.{max t s}) [ΓB.Additive] [ΓB'.Additive]
  [AddCommGrpCat.uliftFunctor.{s, t}.PreservesHomology]

/-- **Transferring a comparison of cohomology along the universe lift.** Suppose that exact
functors `LA`, `LB`, carrying injective objects to injective objects, lift the universe of the
two sides compatibly with the global sections functors and with the functors `h`, `h'`. Then a
comparison `h' ⋙ Rⁿ ΓB' ≅ Rⁿ ΓA'` in the larger universe gives `h ⋙ Rⁿ ΓB ≅ Rⁿ ΓA` in the
smaller one: both sides are lifted by `Stacks`'s `rightDerivedIsoOfSquare`, and the lift of abelian
groups is fully faithful. -/
def rightDerivedCompIsoOfULift
    (sqA : ΓA ⋙ AddCommGrpCat.uliftFunctor.{s, t} ≅ LA ⋙ ΓA')
    (sqB : ΓB ⋙ AddCommGrpCat.uliftFunctor.{s, t} ≅ LB ⋙ ΓB')
    (σ : LA ⋙ h' ≅ h ⋙ LB) (n : ℕ) (e' : h' ⋙ ΓB'.rightDerived n ≅ ΓA'.rightDerived n) :
    h ⋙ ΓB.rightDerived n ≅ ΓA.rightDerived n :=
  ((Functor.FullyFaithful.whiskeringRight AddCommGrpCat.uliftFunctorFullyFaithful
      𝒜).preimageIso (X := h ⋙ ΓB.rightDerived n) (Y := ΓA.rightDerived n)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft h
        (Functor.rightDerivedIsoOfSquare LB ΓB ΓB' AddCommGrpCat.uliftFunctor.{s, t} sqB n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight σ.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft LA e' ≪≫
      (Functor.rightDerivedIsoOfSquare LA ΓA ΓA' AddCommGrpCat.uliftFunctor.{s, t} sqA n).symm))

end CohomologyTransfer

end Stacks.Topos.AbelianPushforward

end
