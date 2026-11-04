module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ModulePushforwardLocalization

/-!
# Restriction to the site of elements as a left adjoint of the localized direct image

Let `X` be a ringed topos presented by a site `(C, J)`, let `F` be a sheaf of sets on `C` and let
`j : X_F ⟶ X` be the localization of `X` at `F`. By Stacks 04IE part (2) the pullback `j^*` of
sheaves of modules is restriction to the site of elements of `F`
(`AlgebraicGeometry.RingedTopos.localizationModulePullbackIso`). Transporting the adjunction
`j^* ⊣ j_*` of Stacks 03D7 along that identification exhibits restriction to the site of elements
as a left adjoint of the direct image `j_*` of sheaves of modules.

The unit of `j^* ⊣ j_*` followed by `j_*` of the identification is the unit of the
inverse-image adjunction of Stacks 03D3 followed by the direct image of the inverse-image
identification of Stacks 03D2; both of these are the identity on underlying sheaves of sets.

## Main definitions

* `AlgebraicGeometry.RingedTopos.elementRestrictionAdjunction`: restriction of sheaves of modules
  to the site of elements is left adjoint to the direct image along the localization morphism.

## Main results

* `RingedTopos.pullbackAdjPushforwardModules_unit_app_localizationModulePullbackIso`:
  the unit of `j^* ⊣ j_*` followed by `j_*` of Stacks 04IE's identification is the unit of the
  inverse-image adjunction followed by the direct image of the inverse-image identification.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_unit_app_comp_directImageModules_map`:
  on underlying sheaves of sets, the unit of the inverse-image adjunction followed by the direct
  image of a morphism is the unit of `f⁻¹ ⊣ f_*` followed by the direct image of the underlying
  morphism.
* `CategoryTheory.Adjunction.comp_unit_app_map_transport`: the unit of a composite adjunction
  followed by the right adjoints of a comparison isomorphism built from a transported counit.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

section

universe w w' v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- On underlying sheaves of sets, the unit of the inverse-image adjunction of Stacks 03D3 followed
by the direct image of a morphism is the unit of `f⁻¹ ⊣ f_*` followed by the direct image of the
underlying morphism. -/
theorem moduleSheafFunctor_map_unit_app_comp_directImageModules_map (N : SheafOfModules.{w'} O)
    {P : SheafOfModules.{w} (inverseImageRingSheaf f O)}
    (x : (inverseImageModules f O).obj N ⟶ P) :
    (Sheaf.moduleSheafFunctor O).map ((inverseImageAdjDirectImageModules f O).unit.app N ≫
        (directImageModules f O).map x) =
      f.adj.unit.app ((Sheaf.moduleSheafFunctor O).obj N) ≫
        f.pushforward.map ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map x) := by
  rw [Functor.map_comp, moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app,
    moduleSheafFunctor_map_directImageModules_map]
  rfl

end

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedTopos

universe u

variable (X : RingedTopos.{u, u, u}) (F : X.Topos)

/-- Let `adj₁ : I ⊣ D` and `adj₂ : E ⊣ RS₀`, let `e : RS₀ ≅ RS` and `ρ : I ≅ Q ⋙ RS`, and
suppose the counit of `adj₂.ofNatIsoRight e` is invertible. Then the unit of `adj₁.comp adj₂` at
`N`, followed by `D ⋙ RS₀` applied to the isomorphism `I ⋙ E ≅ Q` built from `ρ` and that
counit, is the unit of `adj₁` at `N` followed by `D` applied to `ρ.hom.app N ≫ e.inv.app _`. -/
theorem _root_.CategoryTheory.Adjunction.comp_unit_app_map_transport
    {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {I : 𝒜 ⥤ ℬ} {D : ℬ ⥤ 𝒜} {E : ℬ ⥤ 𝒞} {RS₀ RS : 𝒞 ⥤ ℬ} {Q : 𝒜 ⥤ 𝒞}
    (adj₁ : I ⊣ D) (adj₂ : E ⊣ RS₀) (e : RS₀ ≅ RS) (ρ : I ≅ Q ⋙ RS)
    (hc : IsIso (adj₂.ofNatIsoRight e).counit) (N : 𝒜) :
    (adj₁.comp adj₂).unit.app N ≫ D.map (RS₀.map
      ((Functor.isoWhiskerRight ρ E ≪≫ Functor.associator Q RS E ≪≫
        Functor.isoWhiskerLeft Q (@asIso _ _ _ _ (adj₂.ofNatIsoRight e).counit hc) ≪≫
        Functor.rightUnitor Q).hom.app N)) =
      adj₁.unit.app N ≫ D.map (ρ.hom.app N ≫ e.inv.app (Q.obj N)) := by
  simp only [Adjunction.comp_unit_app, Category.assoc, ← Functor.map_comp]
  congr 2
  simp [Adjunction.ofNatIsoRight]

/-- Restriction of scalars along the ring map `fSharpCommRing` of the localization morphism is
restriction of scalars along the comparison of the inverse image of the structure sheaf with its
restriction to the site of elements. -/
theorem restrictScalars_fSharp_localization_eq :
    SheafOfModules.restrictScalars.{u}
      (commRingSheafMap (elementTopology X F)
        (fSharpCommRing (localizationMorphism X F).toRingedToposModulesHom)
        (inverseImageRingSheaf (localizationMorphism X F).toRingedToposModulesHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf (localizedRingedTopos X F).O).property) =
      SheafOfModules.restrictScalars.{u}
        (restrictionRingIso (elementTopology X F) X.J (elementProjection X F)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom :=
  congrArg SheafOfModules.restrictScalars
    ((commRingSheafMap_fSharpCommRing (localizationMorphism X F).toRingedToposModulesHom).trans
      (ringFsharpInverseImage_localizationMorphism X F))

/-- The unit of `j^* ⊣ j_*` followed by `j_*` of Stacks 04IE's identification of `j^*` with
restriction is the unit of the inverse-image adjunction of Stacks 03D3 followed by the direct
image of the inverse-image identification of Stacks 03D2 and of the retyping of restriction of
scalars. -/
theorem pullbackAdjPushforwardModules_unit_app_localizationModulePullbackIso
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (localizationMorphism X F).toRingedToposModulesHom).unit.app N ≫
      (Stacks.Sheaves.RingedToposModules.pushforwardModules
        (localizationMorphism X F).toRingedToposModulesHom).map
        ((localizationModulePullbackIso X F).hom.app N) =
    (inverseImageAdjDirectImageModules (localizationMorphism X F).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unit.app N ≫
      (directImageModules (localizationMorphism X F).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        ((restrictionModuleIso (elementTopology X F) X.J (elementProjection X F)
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom.app N ≫
          (eqToIso (restrictScalars_fSharp_localization_eq X F)).inv.app _) := by
  have ff := AlgebraicGeometry.RingedSite.restrictScalarsFullyFaithful
    (restrictionRingIso (elementTopology X F) X.J (elementProjection X F)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).hom
  exact Adjunction.comp_unit_app_map_transport
    (inverseImageAdjDirectImageModules (localizationMorphism X F).toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (extendRestrictScalarsAdjunction (elementTopology X F)
        (fSharpCommRing (localizationMorphism X F).toRingedToposModulesHom)
        (inverseImageRingSheaf (localizationMorphism X F).toRingedToposModulesHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf (localizedRingedTopos X F).O).property)
    (eqToIso (restrictScalars_fSharp_localization_eq X F))
    (restrictionModuleIso (elementTopology X F) X.J (elementProjection X F)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (@Adjunction.counit_isIso_of_R_fully_faithful _ _ _ _ _ _ _ ff.full ff.faithful) N

/-- Restriction to the site of elements is left adjoint to the direct image along the
localization morphism. -/
noncomputable def elementRestrictionAdjunction :
    elementRestrictionModules X F ⊣
      Stacks.Sheaves.RingedToposModules.pushforwardModules.{u, u, u, u, u, u}
        (localizationMorphism X F).toRingedToposModulesHom :=
  (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    (localizationMorphism X F).toRingedToposModulesHom).ofNatIsoLeft
      (localizationModulePullbackIso X F)

end AlgebraicGeometry.RingedTopos

end
