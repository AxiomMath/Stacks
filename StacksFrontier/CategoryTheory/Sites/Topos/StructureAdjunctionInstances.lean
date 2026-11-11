module

public import StacksFrontier.CategoryTheory.Sites.Topos.StructureAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianAdjunctionForget
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.GrpSheaf
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianRelocalizationAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction

/-!
# Adjoint pairs on sheaves of groups, abelian groups, rings and modules along a morphism of topoi

For a morphism of topoi `f = (f⁻¹, f_*) : Sh(C) → Sh(D)`, this file packages, as instances of
`Stacks.Topos.StructureAdjunction`, the adjoint pairs `(f⁻¹, f_*)` on sheaves of groups, of
abelian groups, of commutative rings and of modules over a fixed ring, each compatible with
taking the underlying sheaves of sets. These are four of the seven cases of Stacks 00YV.

* Groups: a sheaf of groups is a group object in sheaves of sets
  (`CategoryTheory.Sites.GrpSheaf.equivalence`), and the adjunction is Mathlib's
  `CategoryTheory.Adjunction.mapGrp` applied to `f⁻¹ ⊣ f_*`, both functors being cartesian
  monoidal because they preserve finite products.
* Abelian groups: `Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward`, built the
  same way from commutative group objects.
* Commutative rings: `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`.
* Modules over a ring `Λ`: the lift of the abelian adjunction to sheaves of `Λ`-modules,
  `Stacks.ModuleCatLift.moduleLiftAdjunction`, the action of `Λ` being the image of the action
  under the (additive) functors.

In each case the underlying sheaf of sets of `f⁻¹ F`, resp. `f_* G`, is *equal* to `f⁻¹`, resp.
`f_*`, of the underlying sheaf of sets, and so is the unit of the adjunction.

## Main definitions

* `Stacks.Topos.grpStructureAdjunction`, `Stacks.Topos.addCommGrpStructureAdjunction`,
  `Stacks.Topos.commRingStructureAdjunction`, `Stacks.Topos.moduleStructureAdjunction`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Topos

universe w v u v' u' r

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

section Grp

open scoped Stacks.SheafLimitsProd

/-- The direct image of a morphism of topoi is braided monoidal for the cartesian monoidal
structures, since it preserves limits. -/
noncomputable local instance pushforwardBraidedGrp : f.pushforward.Braided :=
  letI : PreservesLimitsOfSize.{0, 0} f.pushforward := f.adj.rightAdjoint_preservesLimits
  .ofChosenFiniteProducts _

/-- The inverse image of a morphism of topoi is braided monoidal for the cartesian monoidal
structures, since it preserves finite limits. -/
noncomputable local instance inverseImageBraidedGrp : f.inverseImage.Braided :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  .ofChosenFiniteProducts _

/-- The direct image of sheaves of groups along a morphism of topoi: internalize the group
operations, push them forward along `f_*`, and read the resulting operations off on sections. -/
noncomputable def grpPushforward : Sheaf J GrpCat.{w} ⥤ Sheaf K GrpCat.{w} :=
  Sites.GrpSheaf.internalSheaf J ⋙ f.pushforward.mapGrp ⋙ Sites.GrpSheaf.externalSheaf K

/-- The inverse image of sheaves of groups is left adjoint to the direct image: both are the
functors induced on group objects by `f⁻¹ ⊣ f_*`, read through the identification of sheaves of
groups with group objects in sheaves of sets. -/
noncomputable def grpInverseImageAdjPushforward :
    Sites.grpInverseImage f ⊣ grpPushforward f :=
  ((Sites.GrpSheaf.equivalence K).toAdjunction.comp f.adj.mapGrp).comp
    (Sites.GrpSheaf.equivalence J).symm.toAdjunction

/-- **Stacks 00YV for groups.** A morphism of topoi gives an adjoint pair `(f⁻¹, f_*)` on sheaves
of groups compatible with taking the underlying sheaves of sets. -/
noncomputable def grpStructureAdjunction [J.HasSheafCompose (forget GrpCat.{w})]
    [K.HasSheafCompose (forget GrpCat.{w})] :
    StructureAdjunction f (forget GrpCat.{w}) where
  inverseImage := Sites.grpInverseImage f
  pushforward := grpPushforward f
  adj := grpInverseImageAdjPushforward f
  inverseImageForgetIso := Iso.refl _
  pushforwardForgetIso := Iso.refl _
  forget_map_unit_app F :=
    (congrArg (fun t => _ ≫ t) ((Category.id_comp _).trans (f.pushforward.map_id _))).trans <|
      (Category.comp_id _).trans <|
        (show _ = f.adj.unit.app ((sheafCompose K (forget GrpCat.{w})).obj F) ≫
            f.pushforward.map (𝟙 _) from rfl).trans <|
          (congrArg (fun t => _ ≫ t) (f.pushforward.map_id _)).trans (Category.comp_id _)

end Grp

section AddCommGrp

/-- **Stacks 00YV for abelian groups.** A morphism of topoi gives an adjoint pair `(f⁻¹, f_*)` on
sheaves of abelian groups compatible with taking the underlying sheaves of sets. -/
noncomputable def addCommGrpStructureAdjunction [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})] :
    StructureAdjunction f (forget AddCommGrpCat.{w}) where
  inverseImage := Sites.abelianInverseImage f
  pushforward := AbelianPushforward.abelianPushforward J f
  adj := AbelianPushforward.abelianInverseImageAdjPushforward J f
  inverseImageForgetIso := Sites.abelianInverseImage_forgetIso f
  pushforwardForgetIso := AbelianPushforward.abelianPushforward_forgetIso J f
  forget_map_unit_app F :=
    (congrArg (fun t => _ ≫ t) ((Category.id_comp _).trans (f.pushforward.map_id _))).trans <|
      (Category.comp_id _).trans <|
        AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget J f F

end AddCommGrp

section CommRing

variable [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w})]

/-- **Stacks 00YV for rings.** A morphism of topoi gives an adjoint pair `(f⁻¹, f_*)` on sheaves
of (commutative) rings compatible with taking the underlying sheaves of sets. -/
noncomputable def commRingStructureAdjunction :
    StructureAdjunction f (forget CommRingCat.{w}) where
  inverseImage := Sheaves.ToposPushforward.inverseImageCommRingFunctor f
  pushforward := Sheaves.ToposPushforward.pushforwardCommRingFunctor f
  adj := Sheaves.ToposPushforward.commRingImageAdjunction f
  inverseImageForgetIso := Sheaves.ToposPushforward.inverseImageCommRingForgetIso J f
  pushforwardForgetIso := Sheaves.ToposPushforward.pushforwardCommRingForgetIso f
  forget_map_unit_app F :=
    (congrArg (fun t => _ ≫ t) ((Category.id_comp _).trans (f.pushforward.map_id _))).trans <|
      (Category.comp_id _).trans <|
        Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_unit_app f F

end CommRing

section Module

variable (Λ : Type r) [Ring Λ]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))] [K.HasSheafCompose (forget (ModuleCat.{w} Λ))]

/-- The direct image of abelian sheaves along a morphism of topoi is additive: it preserves
finite limits, hence binary products and the terminal object, hence zero morphisms. -/
instance abelianPushforward_additive :
    (AbelianPushforward.abelianPushforward J f).Additive := by
  have : HasZeroObject (Sheaf K AddCommGrpCat.{w}) := hasZeroObject_of_hasTerminal_object
  have : HasZeroObject (Sheaf J AddCommGrpCat.{w}) := hasZeroObject_of_hasTerminal_object
  have : (AbelianPushforward.abelianPushforward J f).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  exact Functor.additive_of_preserves_binary_products _

/-- The direct image of sheaves of `Λ`-modules along a morphism of topoi: the direct image of the
underlying abelian sheaf, with `Λ` acting through the image of its action. -/
noncomputable def modulePushforward : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf K (ModuleCat.{w} Λ) :=
  ModuleCatLift.moduleLift Λ J K (AbelianPushforward.abelianPushforward J f)

/-- The inverse image of sheaves of `Λ`-modules is left adjoint to the direct image: the lift to
sheaves of `Λ`-modules of the adjunction on abelian sheaves. -/
noncomputable def moduleInverseImageAdjPushforward :
    ModuleCatLift.moduleLift Λ K J (Sites.abelianInverseImage f) ⊣ modulePushforward f Λ :=
  ModuleCatLift.moduleLiftAdjunction Λ K J _ _
    (AbelianPushforward.abelianInverseImageAdjPushforward J f)

/-- **Stacks 00YV for modules over a fixed ring.** A morphism of topoi gives an adjoint pair
`(f⁻¹, f_*)` on sheaves of `Λ`-modules compatible with taking the underlying sheaves of sets. -/
noncomputable def moduleStructureAdjunction :
    StructureAdjunction f (forget (ModuleCat.{w} Λ)) where
  inverseImage := ModuleCatLift.moduleLift Λ K J (Sites.abelianInverseImage f)
  pushforward := modulePushforward f Λ
  adj := moduleInverseImageAdjPushforward f Λ
  inverseImageForgetIso := Iso.refl _
  pushforwardForgetIso := Iso.refl _
  forget_map_unit_app F :=
    (congrArg (fun t => _ ≫ t) ((Category.id_comp _).trans (f.pushforward.map_id _))).trans <|
      (Category.comp_id _).trans <|
        (congrArg (sheafCompose K (forget AddCommGrpCat.{w})).map
          (ModuleCatLift.sheafCompose_map_moduleLiftAdjunction_unit_app Λ K J _ _
            (AbelianPushforward.abelianInverseImageAdjPushforward J f) F)).trans
          (AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget J f _)

end Module

end Stacks.Topos
