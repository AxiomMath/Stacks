module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModules

/-!
# Chart restrictions across the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site, `X` an algebraic space over `T` and
`Λ X` its lower-shriek extension, an algebraic space over `S` with the same étale charts. The
restriction of an `𝒪_{Λ X}`-module `M` to the chart attached to a chart `U` of `X` is the
restriction to `U` of the corresponding `𝒪_X`-module, as modules on one and the same scheme.

## Main definitions

* `AlgebraicGeometry.Space.chartOpensRelocalizeIso` and
  `AlgebraicGeometry.Space.chartOpensRelocalizeInverseIso`: the index functors of the two chart
  restrictions agree, by isomorphisms whose components are identities of open subschemes.
* `AlgebraicGeometry.Space.restrictToChartRelocalizeInverseIso`: the restriction of the
  `𝒪_X`-module attached to `M` to `U` is the restriction of `M` to the chart of `Λ X` attached
  to `U`.
* `AlgebraicGeometry.Space.restrictToChartRelocalizeFunctorIso`: the restriction of the
  `𝒪_{Λ X}`-module attached to `F` to a chart `U'` of `Λ X` is the restriction of `F` to the
  chart of `X` attached to `U'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B T hT X)

/-- The inclusion of the chart cut out by a Zariski open of an étale chart into that chart. -/
def chartOpensι {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS Y)
    (V : (etaleChartScheme B S hS U).Opens) : (chartOpens B S hS U).obj V ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartOpenOverι B S hS U V) rfl)

/-- The structure sheaf's `Γ` followed by `forget₂` sends the opposite of an identity to the
identity. -/
private theorem forget₂_Γ_map_id_op (Y : Scheme.{u}) :
    (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (𝟙 Y).op) = 𝟙 _ := by
  rw [op_id, Scheme.Γ.map_id]
  exact (forget₂ CommRingCat RingCat).map_id _

section Functor

variable (U : SmallEtale B T hT X)

/-- The open subscheme cut out by `V`, read over `S`, has the structure morphism of the
relocalization of the chart it cuts out of `U`. -/
theorem chartOpensRelocalize_w (V : (etaleChartScheme B T hT U).Opens) :
    𝟙 _ ≫ (chartOpenOver B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) V).hom =
      ((SmallEtale.relocalize B hT hS g X hX).functor.obj
        ((chartOpens B T hT U).obj V)).obj.left.hom :=
  (Category.id_comp _).trans
    (Over.w ((SmallEtale.relocalize B hT hS g X hX).functor.map (chartOpensι U V)).hom.left)

/-- `AlgebraicGeometry.Space.chartOpensRelocalize_w`, read in the other direction. -/
theorem chartOpensRelocalize_w' (V : (etaleChartScheme B T hT U).Opens) :
    𝟙 _ ≫ ((SmallEtale.relocalize B hT hS g X hX).functor.obj
        ((chartOpens B T hT U).obj V)).obj.left.hom =
      (chartOpenOver B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) V).hom :=
  (Category.id_comp _).trans
    (((Category.id_comp _).symm.trans (chartOpensRelocalize_w B hT hS g hX U V)).symm)

/-- The identity of the open subscheme cut out by `V`, as a morphism over `S`. -/
def chartOpensRelocalizeOverHom (V : (etaleChartScheme B T hT U).Opens) :
    chartOpenOver B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) V ⟶
      ((SmallEtale.relocalize B hT hS g X hX).functor.obj
        ((chartOpens B T hT U).obj V)).obj.left :=
  Over.homMk (𝟙 _) (chartOpensRelocalize_w B hT hS g hX U V)

/-- `AlgebraicGeometry.Space.chartOpensRelocalizeOverHom` is compatible with the inclusions into
the relocalized chart. -/
theorem chartOpensRelocalizeOverHom_comp (V : (etaleChartScheme B T hT U).Opens) :
    chartOpensRelocalizeOverHom B hT hS g hX U V ≫
        ((SmallEtale.relocalize B hT hS g X hX).functor.map (chartOpensι U V)).hom.left =
      chartOpenOverι B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) V :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The identity of a Zariski open of a chart `U` of `X`, from the chart it cuts out of the
relocalized chart to the relocalization of the chart it cuts out of `U`. -/
def chartOpensRelocalizeHom (V : (etaleChartScheme B T hT U).Opens) :
    (chartOpens B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U)).obj V ⟶
      (SmallEtale.relocalize B hT hS g X hX).functor.obj ((chartOpens B T hT U).obj V) :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartOpensRelocalizeOverHom B hT hS g hX U V)
    ((congrArg (fun k => yoneda.map _ ≫ k) (CostructuredArrow.w
        ((SmallEtale.relocalize B hT hS g X hX).functor.map (chartOpensι U V)).hom).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans
          (congrArg yoneda.map (chartOpensRelocalizeOverHom_comp B hT hS g hX U V)))))))

/-- The inverse identity morphism over `S` is compatible with the inclusions into the
relocalized chart. -/
theorem chartOpensRelocalizeInvOver_comp (V : (etaleChartScheme B T hT U).Opens) :
    (Over.homMk (𝟙 _) (chartOpensRelocalize_w' B hT hS g hX U V) :
      ((SmallEtale.relocalize B hT hS g X hX).functor.obj
        ((chartOpens B T hT U).obj V)).obj.left ⟶
        chartOpenOver B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) V) ≫
        chartOpenOverι B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) V =
      ((SmallEtale.relocalize B hT hS g X hX).functor.map (chartOpensι U V)).hom.left :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The inverse of `AlgebraicGeometry.Space.chartOpensRelocalizeHom`. -/
def chartOpensRelocalizeInv (V : (etaleChartScheme B T hT U).Opens) :
    (SmallEtale.relocalize B hT hS g X hX).functor.obj ((chartOpens B T hT U).obj V) ⟶
      (chartOpens B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U)).obj V :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk (𝟙 _) (chartOpensRelocalize_w' B hT hS g hX U V))
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map
          (chartOpensRelocalizeInvOver_comp B hT hS g hX U V)))).trans
      (CostructuredArrow.w
        ((SmallEtale.relocalize B hT hS g X hX).functor.map (chartOpensι U V)).hom))))

/-- **The index functor of the chart restriction commutes with relocalization.** -/
def chartOpensRelocalizeIso :
    chartOpens B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) ≅
      chartOpens B T hT U ⋙ (SmallEtale.relocalize B hT hS g X hX).functor :=
  NatIso.ofComponents
    (fun V ↦
      { hom := chartOpensRelocalizeHom B hT hS g hX U V
        inv := chartOpensRelocalizeInv B hT hS g hX U V
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          apply CostructuredArrow.hom_ext
          apply Over.OverMorphism.ext
          exact Category.id_comp _
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          apply CostructuredArrow.hom_ext
          apply Over.OverMorphism.ext
          exact Category.id_comp _ })
    (fun {V V'} i ↦ hom_ext_of_toScheme_map_eq B S hS
      ((Category.comp_id ((etaleChartScheme B T hT U).homOfLE i.le)).trans
        (Category.id_comp ((etaleChartScheme B T hT U).homOfLE i.le)).symm))

/-- The change of scalars of the chart restriction of `U` along the relocalization is that of
the relocalized chart. -/
theorem chartRestrictionSheafHom_relocalize :
    letI := isContinuous_chartOpens B T hT X hX U
    letI := isContinuous_chartOpens B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX)
      ((SmallEtale.relocalize B hT hS g X hX).functor.obj U)
    @CategoryStruct.comp _ _ (chartScheme U).ringCatSheaf _ _
      (chartRestrictionSheafHom B T hT hX U ≫
        ((chartOpens B T hT U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B T hT X)
            (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX))))
      ((@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _
        (chartOpensRelocalizeIso B hT hS g hX U).hom RingCat.{u} _
        (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS _)
        (isContinuous_chartOpens B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX)
          ((SmallEtale.relocalize B hT hS g X hX).functor.obj U))
        (Functor.isContinuous_comp _ _ (Opens.grothendieckTopology (chartScheme U))
          (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _))).app
        (relocalizeRingSheaf B hT hS g X hX)) =
      chartRestrictionSheafHom B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  have h : (relocalizeRingSheaf B hT hS g X hX).obj.map
      ((chartOpensRelocalizeIso B hT hS g hX U).hom.app V.unop).op = 𝟙 _ :=
    forget₂_Γ_map_id_op _
  refine (congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans ?_
  refine (NatTrans.comp_app _ _ V).trans ?_
  refine (congrArg (· ≫ _) ((congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans (NatTrans.comp_app _ _ V))).trans ?_
  exact (congrArg₂ (· ≫ ·) (Category.comp_id _) h).trans (Category.comp_id _)

/-- **The chart restriction of the `𝒪_X`-module attached to an `𝒪_{Λ X}`-module.** Its
restriction to a chart `U` of `X` is the restriction of `M` to the chart of `Λ X` attached to
`U`, as modules on the same scheme. -/
def restrictToChartRelocalizeInverseIso
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    restrictToChart B T hT hX ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M) U ≅
      restrictToChart B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX) M
        ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) := by
  letI i1 := isContinuous_chartOpens B T hT X hX U
  letI i2 := isContinuous_chartOpens B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX)
    ((SmallEtale.relocalize B hT hS g X hX).functor.obj U)
  letI i5 : (chartOpens B T hT U ⋙ (SmallEtale.relocalize B hT hS g X hX).functor).IsContinuous
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS _) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B T hT X) _
  refine restrictToChartIsoPushforward B T hT hX U _ ≪≫
    (SheafOfModules.pushforwardComp (chartRestrictionSheafHom B T hT hX U)
      (𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B T hT X)
        (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX)))).app M ≪≫
    (@SheafOfModules.pushforwardCongr₂ (chartScheme U).Opens _
      (SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)) _
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS _)
      (chartOpens B S hS ((SmallEtale.relocalize B hT hS g X hX).functor.obj U))
      (chartOpens B T hT U ⋙ (SmallEtale.relocalize B hT hS g X hX).functor)
      (chartScheme U).ringCatSheaf (relocalizeRingSheaf B hT hS g X hX) i2 i5
      (chartRestrictionSheafHom B T hT hX U ≫
        ((chartOpens B T hT U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B T hT X)
            (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX))))
      (chartRestrictionSheafHom B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        ((SmallEtale.relocalize B hT hS g X hX).functor.obj U))
      (chartOpensRelocalizeIso B hT hS g hX U)
      (chartRestrictionSheafHom_relocalize B hT hS g hX U)).app M ≪≫
    (restrictToChartIsoPushforward B S hS _
      ((SmallEtale.relocalize B hT hS g X hX).functor.obj U) M).symm

end Functor

section Inverse

variable (U : SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X))

/-- The open subscheme cut out by `V`, read over `T`, has the structure morphism of the chart of
`X` attached to the chart it cuts out of `U`. -/
theorem chartOpensRelocalizeInverse_w (V : (etaleChartScheme B S hS U).Opens) :
    𝟙 _ ≫ (chartOpenOver B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) V).hom =
      ((SmallEtale.relocalize B hT hS g X hX).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left.hom :=
  (Category.id_comp _).trans
    (Over.w ((SmallEtale.relocalize B hT hS g X hX).inverse.map (chartOpensι U V)).hom.left)

/-- `AlgebraicGeometry.Space.chartOpensRelocalizeInverse_w`, read in the other direction. -/
theorem chartOpensRelocalizeInverse_w' (V : (etaleChartScheme B S hS U).Opens) :
    𝟙 _ ≫ ((SmallEtale.relocalize B hT hS g X hX).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left.hom =
      (chartOpenOver B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) V).hom :=
  (Category.id_comp _).trans
    (((Category.id_comp _).symm.trans (chartOpensRelocalizeInverse_w B hT hS g hX U V)).symm)

/-- The identity of the open subscheme cut out by `V`, as a morphism over `T`. -/
def chartOpensRelocalizeInverseOverHom (V : (etaleChartScheme B S hS U).Opens) :
    chartOpenOver B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) V ⟶
      ((SmallEtale.relocalize B hT hS g X hX).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left :=
  Over.homMk (𝟙 _) (chartOpensRelocalizeInverse_w' B hT hS g hX U V)

/-- `AlgebraicGeometry.Space.chartOpensRelocalizeInverseOverHom` is compatible with the inclusions
into the chart of `X` attached to `U`. -/
theorem chartOpensRelocalizeInverseOverHom_comp (V : (etaleChartScheme B S hS U).Opens) :
    chartOpensRelocalizeInverseOverHom B hT hS g hX U V ≫
        ((SmallEtale.relocalize B hT hS g X hX).inverse.map (chartOpensι U V)).hom.left =
      chartOpenOverι B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) V :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The identity of a Zariski open of a chart `U` of `Λ X`, from the chart it cuts out of the
chart of `X` attached to `U` to the chart of `X` attached to the chart it cuts out. -/
def chartOpensRelocalizeInverseHom (V : (etaleChartScheme B S hS U).Opens) :
    (chartOpens B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U)).obj V ⟶
      (SmallEtale.relocalize B hT hS g X hX).inverse.obj ((chartOpens B S hS U).obj V) :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (chartOpensRelocalizeInverseOverHom B hT hS g hX U V)
    ((congrArg (fun k => yoneda.map _ ≫ k) (CostructuredArrow.w
        ((SmallEtale.relocalize B hT hS g X hX).inverse.map (chartOpensι U V)).hom).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans
          (congrArg yoneda.map (chartOpensRelocalizeInverseOverHom_comp B hT hS g hX U V)))))))

/-- The inverse identity morphism over `T` is compatible with the inclusions into the chart of `X`
attached to `U`. -/
theorem chartOpensRelocalizeInverseInvOver_comp (V : (etaleChartScheme B S hS U).Opens) :
    (Over.homMk (𝟙 _) (chartOpensRelocalizeInverse_w B hT hS g hX U V) :
      ((SmallEtale.relocalize B hT hS g X hX).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left ⟶
        chartOpenOver B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) V) ≫
        chartOpenOverι B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) V =
      ((SmallEtale.relocalize B hT hS g X hX).inverse.map (chartOpensι U V)).hom.left :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The inverse of `AlgebraicGeometry.Space.chartOpensRelocalizeInverseHom`. -/
def chartOpensRelocalizeInverseInv (V : (etaleChartScheme B S hS U).Opens) :
    (SmallEtale.relocalize B hT hS g X hX).inverse.obj ((chartOpens B S hS U).obj V) ⟶
      (chartOpens B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U)).obj V :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk (𝟙 _) (chartOpensRelocalizeInverse_w B hT hS g hX U V))
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map
          (chartOpensRelocalizeInverseInvOver_comp B hT hS g hX U V)))).trans
      (CostructuredArrow.w
        ((SmallEtale.relocalize B hT hS g X hX).inverse.map (chartOpensι U V)).hom))))

/-- **The index functor of the chart restriction commutes with the inverse relocalization.** -/
def chartOpensRelocalizeInverseIso :
    chartOpens B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) ≅
      chartOpens B S hS U ⋙ (SmallEtale.relocalize B hT hS g X hX).inverse :=
  NatIso.ofComponents
    (fun V ↦
      { hom := chartOpensRelocalizeInverseHom B hT hS g hX U V
        inv := chartOpensRelocalizeInverseInv B hT hS g hX U V
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          apply CostructuredArrow.hom_ext
          apply Over.OverMorphism.ext
          exact Category.id_comp _
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          apply CostructuredArrow.hom_ext
          apply Over.OverMorphism.ext
          exact Category.id_comp _ })
    (fun {V V'} i ↦ hom_ext_of_toScheme_map_eq B T hT
      ((Category.comp_id ((etaleChartScheme B S hS U).homOfLE i.le)).trans
        (Category.id_comp ((etaleChartScheme B S hS U).homOfLE i.le)).symm))

/-- The counit of the equivalence of small étale sites, read in `Λ X`, is the identity on
underlying schemes, so the structure sheaf sends it to the identity. -/
theorem relocalizeRingSheaf_map_counit
    (W : SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)) :
    (relocalizeRingSheaf B hT hS g X hX).obj.map
      ((SmallEtale.relocalize B hT hS g X hX).counit.app W).op = 𝟙 _ :=
  forget₂_Γ_map_id_op _

/-- The change of scalars of the chart restriction of `U` along the inverse relocalization is
that of the chart of `X` attached to `U`. -/
theorem chartRestrictionSheafHom_relocalizeInverse :
    letI := isContinuous_chartOpens B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX) U
    letI := isContinuous_chartOpens B T hT X hX
      ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U)
    @CategoryStruct.comp _ _ (chartScheme U).ringCatSheaf _ _
      (chartRestrictionSheafHom B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX) U ≫
        ((chartOpens B S hS U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (Stacks.SheafOfModules.reindexBackSharp (J := SmallEtale.topology B S hS _)
            (J' := SmallEtale.topology B T hT X) (SmallEtale.relocalize B hT hS g X hX)
            (relocalizeRingSheaf B hT hS g X hX)))
      ((@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _
        (chartOpensRelocalizeInverseIso B hT hS g hX U).hom RingCat.{u} _
        (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B T hT X)
        (isContinuous_chartOpens B T hT X hX
          ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U))
        (Functor.isContinuous_comp _ _ (Opens.grothendieckTopology (chartScheme U))
          (SmallEtale.topology B S hS _) (SmallEtale.topology B T hT X))).app
        (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B T hT X)
          (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX))) =
      chartRestrictionSheafHom B T hT hX
        ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  have h : (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B T hT X)
      (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX)).obj.map
      ((chartOpensRelocalizeInverseIso B hT hS g hX U).hom.app V.unop).op = 𝟙 _ :=
    forget₂_Γ_map_id_op _
  refine (congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans ?_
  refine (NatTrans.comp_app _ _ V).trans ?_
  refine (congrArg (· ≫ _) ((congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans (NatTrans.comp_app _ _ V))).trans ?_
  exact (congrArg₂ (· ≫ ·) ((congrArg (_ ≫ ·)
    (relocalizeRingSheaf_map_counit B hT hS g hX ((chartOpens B S hS U).obj V.unop))).trans
    (Category.comp_id _)) h).trans (Category.comp_id _)

/-- **The chart restriction of the `𝒪_{Λ X}`-module attached to an `𝒪_X`-module.** Its
restriction to a chart `U` of `Λ X` is the restriction of `F` to the chart of `X` attached to
`U`, as modules on the same scheme. -/
def restrictToChartRelocalizeFunctorIso (F : Modules.{u, u} B T hT X hX) :
    restrictToChart B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX)
        ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj F) U ≅
      restrictToChart B T hT hX F ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) := by
  letI i1 := isContinuous_chartOpens B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX) U
  letI i2 := isContinuous_chartOpens B T hT X hX
    ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U)
  letI i5 : (chartOpens B S hS U ⋙ (SmallEtale.relocalize B hT hS g X hX).inverse).IsContinuous
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B T hT X) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS _) _
  refine restrictToChartIsoPushforward B S hS _ U _ ≪≫
    (SheafOfModules.pushforwardComp
      (chartRestrictionSheafHom B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX) U)
      (Stacks.SheafOfModules.reindexBackSharp (J := SmallEtale.topology B S hS _)
        (J' := SmallEtale.topology B T hT X) (SmallEtale.relocalize B hT hS g X hX)
        (relocalizeRingSheaf B hT hS g X hX))).app F ≪≫
    (@SheafOfModules.pushforwardCongr₂ (chartScheme U).Opens _ (SmallEtale B T hT X) _
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B T hT X)
      (chartOpens B T hT ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U))
      (chartOpens B S hS U ⋙ (SmallEtale.relocalize B hT hS g X hX).inverse)
      (chartScheme U).ringCatSheaf
      (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B T hT X)
        (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX)) i2 i5
      (chartRestrictionSheafHom B S hS (isAlgebraicSpace_relocalize' B hT hS g X hX) U ≫
        ((chartOpens B S hS U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (Stacks.SheafOfModules.reindexBackSharp (J := SmallEtale.topology B S hS _)
            (J' := SmallEtale.topology B T hT X) (SmallEtale.relocalize B hT hS g X hX)
            (relocalizeRingSheaf B hT hS g X hX)))
      (chartRestrictionSheafHom B T hT hX ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U))
      (chartOpensRelocalizeInverseIso B hT hS g hX U)
      (chartRestrictionSheafHom_relocalizeInverse B hT hS g hX U)).app F ≪≫
    (restrictToChartIsoPushforward B T hT hX
      ((SmallEtale.relocalize B hT hS g X hX).inverse.obj U) F).symm

end Inverse

end AlgebraicGeometry.Space

end
