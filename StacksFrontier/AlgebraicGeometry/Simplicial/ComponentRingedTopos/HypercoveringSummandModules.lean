module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleBoundedBelowEquivalenceUnconditional
public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.StructureSheafAugmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableSummandRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Restriction of modules on the total site of a hypercovering to the summand slices

Let `C` be a site with equalizers and fibre products, `O_C` a sheaf of commutative rings on it
and `K` a hypercovering of `C`, with `K_n = {U_{n,i}}_{i ∈ I_n}`. Remark 0D9W equips the total
site `(C/K)_total` with `O = a⁻¹O_C`, and the degree-`n` component `C/K_n` with its restriction
`O_n`. Since `C/K_n` is the disjoint union of the slices `C/U_{n,i}`, an `O_n`-module `G` has
components `G_i`, which are `O_C|_{U_{n,i}}`-modules (Stacks 0D9U).

Here `O` is the structure sheaf of the ringed augmentation
`Stacks.CategoryTheory.Hypercovering.hypercoveringRingedAugmentation`, the inverse image `a⁻¹O_C`
along the morphism of topoi of Stacks 0D70. For a sheaf of `O_C`-modules `M`, the `i`-th
component of `(a^*M)_n` is `M|_{U_{n,i}}`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.hypercoveringStructureRingIso`: the identification of
  `a⁻¹O_C` with the restriction of `O_C` along the localization functor `j_total`, which is
  continuous and cocontinuous.
* `Stacks.CategoryTheory.Hypercovering.hypercoveringSummandRestriction`: restriction of
  `O_n`-modules to the summand `C/U_{n,i}`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.hypercoveringPullbackModulesRestrictionIso`: the pullback
  of modules along `a` is restriction of sections along `j_total`, scalars being identified by
  `hypercoveringStructureRingIso`.
* `Stacks.CategoryTheory.Hypercovering.hypercoveringSummandRestrictionPullbackIso`: the `i`-th
  component of `(a^*M)_n` is `M|_{U_{n,i}}`.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
  (O : Sheaf K RingCat.{ww'})

/-- The inverse images of a sheaf of rings along two isomorphic finite-product-preserving functors
of sheaves of sets are isomorphic. -/
noncomputable def pullbackRingSheafIsoOfNatIso (ε : Φ ≅ Φ') :
    pullbackRingSheaf J Φ O ≅ pullbackRingSheaf J Φ' O where
  hom := pullbackRingSheafMapOfNatTrans J O ε.hom
  inv := pullbackRingSheafMapOfNatTrans J O ε.inv
  hom_inv_id := Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ RingCat.hom_ext (RingHom.ext fun x ↦
    congrFun (congrArg (fun m ↦ m.hom.app U) (ε.hom_inv_id_app (Sheaf.ringSheaf O))) x)))
  inv_hom_id := Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ RingCat.hom_ext (RingHom.ext fun x ↦
    congrFun (congrArg (fun m ↦ m.hom.app U) (ε.inv_hom_id_app (Sheaf.ringSheaf O))) x)))

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]
  (G : X.C ⥤ Y.C) [hG : G.IsContinuous X.J Y.J]
  [hGP : PreservesFiniteProducts (G.sheafPushforwardContinuous (Type u) X.J Y.J)]
  (ε : f.toToposHom.inverseImage ≅ G.sheafPushforwardContinuous (Type u) X.J Y.J)

/-- For a morphism of ringed topoi with invertible structure map whose inverse image is
isomorphic to restriction along a continuous functor `G` of the underlying sites, the structure
sheaf of the source is the restriction of the structure sheaf of the target along `G`. -/
noncomputable def structureRingIsoOfInverseImageIso :
    Stacks.SheafOfModules.Tensor.ringSheaf X.O ≅
      (G.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (asIso f.toModulesHom.fSharpInverseImage).symm ≪≫
    pullbackRingSheafIsoOfNatIso X.J (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ε ≪≫
      restrictionRingIso X.J Y.J G (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- **The pullback of modules along a morphism of ringed topoi with invertible structure map
whose inverse image is restriction along a continuous functor `G` is restriction of sections
along `G`**, scalars being identified by `structureRingIsoOfInverseImageIso`. -/
noncomputable def pullbackModulesIsoRestrictionOfInverseImageIso :
    f.toModulesHom.pullbackModules ≅
      restrictionModules X.J Y.J G (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        SheafOfModules.restrictScalars (structureRingIsoOfInverseImageIso f G ε).hom :=
  Functor.isoWhiskerLeft _ f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso ≪≫
    Functor.isoWhiskerRight
      (pullbackModuleFunctorIsoOfNatIso X.J (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ε
        (pullbackRingSheafMapOfNatTrans X.J (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ε.hom)
        (ringSheafMap_pullbackRingSheafMapOfNatTrans _ _ _)) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (restrictionModuleIso X.J Y.J G (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _) _ ≪≫
    eqToIso rfl

end AlgebraicGeometry.RingedToposHom

namespace SheafOfModules

variable {𝒯 : Type u} [Category.{u} 𝒯] {𝒦 : Type u} [Category.{u} 𝒦] {𝒲 : Type u}
  [Category.{u} 𝒲] {𝒞 : Type u} [Category.{u} 𝒞]
  {JT : GrothendieckTopology 𝒯} {JK : GrothendieckTopology 𝒦} {JW : GrothendieckTopology 𝒲}
  {JC : GrothendieckTopology 𝒞}
  (c : 𝒦 ⥤ 𝒯) [hc : c.IsContinuous JK JT] (G : 𝒯 ⥤ 𝒞) [hG : G.IsContinuous JT JC]
  (s : 𝒲 ⥤ 𝒦) [hs : s.IsContinuous JW JK]
  (R : Sheaf JC RingCat.{u}) {O : Sheaf JT RingCat.{u}}
  (ρ : O ≅ (G.sheafPushforwardContinuous RingCat.{u} JT JC).obj R) {S : Sheaf JW RingCat.{u}}
  (τ : S ⟶ (s.sheafPushforwardContinuous RingCat.{u} JW JK).obj
    ((c.sheafPushforwardContinuous RingCat.{u} JK JT).obj
      ((G.sheafPushforwardContinuous RingCat.{u} JT JC).obj R)))

/-- Restriction of sections along `G`, followed by restriction of scalars along an isomorphism
`ρ : O ≅ G^s R`, then restriction to `𝒦` along `c` and back along `c^s ρ⁻¹`, then restriction
along `s`, is restriction of sections along `s ⋙ c ⋙ G`. -/
noncomputable def pushforwardRestrictScalarsCancelIso :
    SheafOfModules.pushforward.{u} (F := G)
        (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} JT JC).obj R)) ⋙
      SheafOfModules.restrictScalars.{u} ρ.hom ⋙
        SheafOfModules.pushforward.{u} (F := c)
          (𝟙 ((c.sheafPushforwardContinuous RingCat.{u} JK JT).obj O)) ⋙
          SheafOfModules.restrictScalars.{u}
            ((c.sheafPushforwardContinuous RingCat.{u} JK JT).map ρ.inv) ⋙
            SheafOfModules.pushforward.{u} (F := s) τ ≅
      haveI : (c ⋙ G).IsContinuous JK JC := Functor.isContinuous_comp c G JK JT JC
      haveI : (s ⋙ c ⋙ G).IsContinuous JW JC :=
        Functor.isContinuous_comp s (c ⋙ G) JW JK JC
      SheafOfModules.pushforward.{u} (F := s ⋙ c ⋙ G) τ := by
  haveI : (c ⋙ G).IsContinuous JK JC := Functor.isContinuous_comp c G JK JT JC
  haveI : (s ⋙ c ⋙ G).IsContinuous JW JC := Functor.isContinuous_comp s (c ⋙ G) JW JK JC
  have hρ : SheafOfModules.restrictScalars.{u} ρ.hom ⋙
      SheafOfModules.pushforward.{u} (F := c)
        (𝟙 ((c.sheafPushforwardContinuous RingCat.{u} JK JT).obj O)) =
      SheafOfModules.pushforward.{u} (F := c)
          (𝟙 ((c.sheafPushforwardContinuous RingCat.{u} JK JT).obj
            ((G.sheafPushforwardContinuous RingCat.{u} JT JC).obj R))) ⋙
        SheafOfModules.restrictScalars.{u}
          ((c.sheafPushforwardContinuous RingCat.{u} JK JT).map ρ.hom) := rfl
  refine Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (eqToIso hρ) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId _ _ (by
        rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id])) _)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.leftUnitor _)) ≪≫
    (Functor.associator _ _ _).symm ≪≫ ?_
  refine Functor.isoWhiskerRight (SheafOfModules.pushforwardComp _ _) _ ≪≫
    SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr ?_
  exact Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

end SheafOfModules

namespace Stacks.CategoryTheory.Hypercovering

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})

/-- The localization functor `j_total : (C/K)_total ⥤ C`, with its source read as the total
category of the simplicial-site situation of the hypercovering. -/
abbrev jTotal : (hypercoveringSituation J H).totalCategory ⥤ C :=
  totalForget H.toSimplicialObject

/-- `j_total` is continuous (Stacks 0D85). -/
instance jTotal_isContinuous :
    (jTotal J H).IsContinuous (hypercoveringSituation J H).totalTopology J.toGrothendieck :=
  totalForget_isContinuous J.toGrothendieck H.toSimplicialObject

/-- `j_total` is cocontinuous. -/
instance jTotal_isCocontinuous :
    (jTotal J H).IsCocontinuous (hypercoveringSituation J H).totalTopology J.toGrothendieck :=
  totalForget_isCocontinuous J.toGrothendieck H.toSimplicialObject

/-- Restriction of sheaves of sets along `j_total` preserves finite products. -/
instance jTotal_preservesFiniteProducts :
    PreservesFiniteProducts ((jTotal J H).sheafPushforwardContinuous (Type u)
      (hypercoveringSituation J H).totalTopology J.toGrothendieck) :=
  ⟨fun _ ↦ Functor.preservesLimitsOfShape_sheafPushforwardContinuous _ _ _ (Type u) _⟩

/-- **The inverse image of the total augmentation of Stacks 0D70 is restriction along
`j_total`** (Stacks 0D8B). -/
def hypercoveringTotalInverseImageIso :
    (Augmentation.totalMorphismOfTopoi (hypercoveringSituation J H) (Cat.of C)
        J.toGrothendieck (hypercoveringAugmentation J H)).inverseImage ≅
      (jTotal J H).sheafPushforwardContinuous (Type u)
        (hypercoveringSituation J H).totalTopology J.toGrothendieck :=
  CocontinuousSimplicialSite.Augmentation.totalInverseImageIso
      (augmentation J.toGrothendieck H.toSimplicialObject) ≪≫
    totalInverseImageIso J.toGrothendieck H.toSimplicialObject

/-- **`a⁻¹O_C` is the restriction of `O_C` along `j_total`**, as sheaves of rings. -/
abbrev hypercoveringStructureRingIso :=
  AlgebraicGeometry.RingedToposHom.structureRingIsoOfInverseImageIso
    (hypercoveringRingedAugmentation J H OC).totalRingedHom (jTotal J H)
    (hG := totalForget_isContinuous J.toGrothendieck H.toSimplicialObject)
    (hGP := jTotal_preservesFiniteProducts J H) (hypercoveringTotalInverseImageIso J H)

/-- **The pullback of modules along the augmentation of a hypercovering is restriction of
sections along `j_total`**, scalars being identified by `hypercoveringStructureRingIso`. -/
abbrev hypercoveringPullbackModulesRestrictionIso :=
  AlgebraicGeometry.RingedToposHom.pullbackModulesIsoRestrictionOfInverseImageIso
    (hypercoveringRingedAugmentation J H OC).totalRingedHom (jTotal J H)
    (hG := totalForget_isContinuous J.toGrothendieck H.toSimplicialObject)
    (hGP := jTotal_preservesFiniteProducts J H) (hypercoveringTotalInverseImageIso J H)

/-- The comparison of the restriction to the degree-`n` component of `O_C` along `j_total` with
the component structure sheaf `O_n`, induced by `hypercoveringStructureRingIso`. -/
abbrev hypercoveringComponentRingMap (n : SimplexCategory) :=
  ((componentFunctor (hypercoveringSituation J H) n).sheafPushforwardContinuous RingCat.{u}
      ((hypercoveringSituation J H).componentTopology n)
      (hypercoveringSituation J H).totalTopology).map
    (hypercoveringStructureRingIso J H OC).inv

/-- **Restriction of `O_n`-modules to the summand `C/U_{n,i}` of the degree-`n` component**, the
`i`-th component `G_i` of an `O_n`-module `G` under `Mod(O_n) = ∏_i Mod(O_C|_{U_{n,i}})`
(Stacks 0D9U), for the structure sheaf `O = a⁻¹O_C` of the ringed augmentation of the
hypercovering. The scalars `O_n|_{U_{n,i}} = O_C|_{U_{n,i}}` are identified through
`hypercoveringStructureRingIso`. -/
def hypercoveringSummandRestriction (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) :
    SheafOfModules.{u} (componentRingSheaf (hypercoveringSituation J H)
        ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O)
        n) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf OC).over
        ((H.toSimplicialObject.obj (op n)).obj i)) :=
  SheafOfModules.restrictScalars (hypercoveringComponentRingMap J H OC n) ⋙
    summandRestriction (pretopologyRingedSite J OC) H.toSimplicialObject n i

/-- The inclusion of the summand `C/U_{n,i}` into the degree-`n` component is continuous. -/
instance summandFunctor_isContinuous_hypercovering (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) :
    (summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i).IsContinuous
      (J.toGrothendieck.over ((H.toSimplicialObject.obj (op n)).obj i))
      ((hypercoveringSituation J H).componentTopology n) :=
  summandFunctor_isContinuous (pretopologyRingedSite J OC) H.toSimplicialObject n i

/-- The composite of the inclusion of the summand `C/U_{n,i}`, the component inclusion and
`j_total` is continuous. -/
instance summandComposite_isContinuous (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) :
    (summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i ⋙
        componentFunctor (hypercoveringSituation J H) n ⋙ jTotal J H).IsContinuous
      (J.toGrothendieck.over ((H.toSimplicialObject.obj (op n)).obj i)) J.toGrothendieck :=
  haveI := @Functor.isContinuous_comp _ _ _ _ _ _ (componentFunctor (hypercoveringSituation J H) n)
    (jTotal J H) ((hypercoveringSituation J H).componentTopology n)
    (hypercoveringSituation J H).totalTopology J.toGrothendieck
    (componentFunctor_isContinuous (hypercoveringSituation J H) n)
    (totalForget_isContinuous J.toGrothendieck H.toSimplicialObject)
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ ((hypercoveringSituation J H).componentTopology n) _
    (summandFunctor_isContinuous (pretopologyRingedSite J OC) H.toSimplicialObject n i) this

/-- The summand ring map, transported along `summandForgetIso`, is the identity of
`O_C|_{U_{n,i}}`. -/
theorem hypercoveringSummandRingMap_comp (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) :
    summandRingMap (pretopologyRingedSite J OC) H.toSimplicialObject n i ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (show summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i ⋙
              componentFunctor (hypercoveringSituation J H) n ⋙ jTotal J H ≅ _ from
            summandForgetIso (pretopologyRingedSite J OC) H.toSimplicialObject n i).inv
          RingCat.{u} (J.toGrothendieck.over ((H.toSimplicialObject.obj (op n)).obj i))
          J.toGrothendieck).app (Stacks.SheafOfModules.Tensor.ringSheaf OC) =
      𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf OC).over
        ((H.toSimplicialObject.obj (op n)).obj i)) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ RingCat.hom_ext (RingHom.ext fun x ↦ by
    show (Stacks.SheafOfModules.Tensor.ringSheaf OC).obj.map (𝟙 W.unop.left).op x = x
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl)))

/-- **The `i`-th component of `(a^*M)_n` is `M|_{U_{n,i}}`.** For a sheaf of `O_C`-modules `M`,
the restriction of the pullback `a^*M` to the degree-`n` component, read on the summand
`C/U_{n,i}`, is the restriction of `M` to `C/U_{n,i}`. -/
def hypercoveringSummandRestrictionPullbackIso (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) :
    (hypercoveringSummandRestriction J H OC n i).obj
        ((componentModuleRestriction (hypercoveringSituation J H)
          ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O)
          n).obj
          ((hypercoveringRingedAugmentation J H
            OC).totalRingedHom.toModulesHom.pullbackModules.obj M)) ≅
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf OC)
        ((H.toSimplicialObject.obj (op n)).obj i)).obj M :=
  (hypercoveringSummandRestriction J H OC n i).mapIso
      ((componentModuleRestriction (hypercoveringSituation J H)
        ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O)
        n).mapIso ((hypercoveringPullbackModulesRestrictionIso J H OC).app M)) ≪≫
    (SheafOfModules.pushforwardRestrictScalarsCancelIso
      (componentFunctor (hypercoveringSituation J H) n) (jTotal J H)
      (summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i)
      (Stacks.SheafOfModules.Tensor.ringSheaf OC) (hypercoveringStructureRingIso J H OC)
      (summandRingMap (pretopologyRingedSite J OC) H.toSimplicialObject n i)
      (hc := componentFunctor_isContinuous (hypercoveringSituation J H) n)
      (hs := summandFunctor_isContinuous (pretopologyRingedSite J OC)
        H.toSimplicialObject n i)
      (hG := totalForget_isContinuous J.toGrothendieck H.toSimplicialObject)).app M ≪≫
    (SheafOfModules.pushforwardCongr₂ _
      (show summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i ⋙
          componentFunctor (hypercoveringSituation J H) n ⋙ jTotal J H ≅ _ from
        summandForgetIso (pretopologyRingedSite J OC) H.toSimplicialObject n i).symm
      (hypercoveringSummandRingMap_comp J H OC n i)).app M

end Stacks.CategoryTheory.Hypercovering

end
