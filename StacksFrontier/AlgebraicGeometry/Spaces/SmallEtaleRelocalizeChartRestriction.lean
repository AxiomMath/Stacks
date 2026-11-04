module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModules

/-!
# Chart restrictions on an algebraic space and on its lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site, `X` an algebraic space over `W` and `Λ_h X`
its lower-shriek extension, an algebraic space over `S` with the same étale charts.  The
restriction of an `𝒪_{Λ_h X}`-module `M` to the chart attached to a chart `U` of `X` is the
restriction to `U` of the corresponding `𝒪_X`-module, as modules on one and the same scheme, and
symmetrically for the inverse equivalence.

## Main definitions

* `AlgebraicGeometry.Space.chartOpensRelocalizeIsoSE` and
  `AlgebraicGeometry.Space.chartOpensRelocalizeInverseIsoSE`: the index functors of the two chart
  restrictions agree, by isomorphisms whose components are identities of open subschemes.
* `AlgebraicGeometry.Space.restrictToChartRelocalizeInverseIsoSE`: the restriction of the
  `𝒪_X`-module attached to `M` to `U` is the restriction of `M` to the chart of `Λ_h X`
  attached to `U`.
* `AlgebraicGeometry.Space.restrictToChartRelocalizeFunctorIsoSE`: the restriction of the
  `𝒪_{Λ_h X}`-module attached to `F` to a chart `U'` of `Λ_h X` is the restriction of `F` to
  the chart of `X` attached to `U'`.

## Implementation notes

The functor of `AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence` acts on morphisms of
charts without changing the underlying morphisms of schemes, on the nose; its inverse does so up
to the equation `AlgebraicGeometry.Space.relocalizeChartsInverse_map_left_left`, and its counit
has identity underlying morphisms by
`AlgebraicGeometry.Space.relocalizeChartsDescentIso_hom_left_left`.  These are the only
properties of the equivalence the comparisons use.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B W hW X)
  (hX' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj X))

/-- The inclusion of the chart cut out by a Zariski open of an étale chart into that chart. -/
def chartOpensιSE {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : SmallEtale B S hS Y)
    (V : (etaleChartScheme B S hS U).Opens) : (chartOpens B S hS U).obj V ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartOpenOverι B S hS U V) rfl)

section Functor

variable (U : SmallEtale B W hW X)

/-- The open subscheme cut out by `V`, read over `S`, has the structure morphism of the
relocalization of the chart it cuts out of `U`. -/
theorem chartOpensRelocalize_wSE (V : (etaleChartScheme B W hW U).Opens) :
    𝟙 _ ≫ (chartOpenOver B S hS
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) V).hom =
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj
        ((chartOpens B W hW U).obj V)).obj.left.hom :=
  (Category.id_comp _).trans
    (Over.w
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.map (chartOpensιSE U V)).hom.left)

/-- `AlgebraicGeometry.Space.chartOpensRelocalize_wSE`, read in the other direction. -/
theorem chartOpensRelocalize_wSE' (V : (etaleChartScheme B W hW U).Opens) :
    𝟙 _ ≫ ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj
        ((chartOpens B W hW U).obj V)).obj.left.hom =
      (chartOpenOver B S hS
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) V).hom :=
  (Category.id_comp _).trans
    (((Category.id_comp _).symm.trans (chartOpensRelocalize_wSE B W S hW hS h U V)).symm)

/-- The identity of the open subscheme cut out by `V`, as a morphism over `S`. -/
def chartOpensRelocalizeOverHomSE (V : (etaleChartScheme B W hW U).Opens) :
    chartOpenOver B S hS ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) V ⟶
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj
        ((chartOpens B W hW U).obj V)).obj.left :=
  Over.homMk (𝟙 _) (chartOpensRelocalize_wSE B W S hW hS h U V)

/-- `AlgebraicGeometry.Space.chartOpensRelocalizeOverHomSE` is compatible with the inclusions into
the relocalized chart. -/
theorem chartOpensRelocalizeOverHom_compSE (V : (etaleChartScheme B W hW U).Opens) :
    chartOpensRelocalizeOverHomSE B W S hW hS h U V ≫
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.map
          (chartOpensιSE U V)).hom.left =
      chartOpenOverι B S hS ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) V :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The identity of a Zariski open of a chart `U` of `X`, from the chart it cuts out of the
relocalized chart to the relocalization of the chart it cuts out of `U`. -/
def chartOpensRelocalizeHomSE (V : (etaleChartScheme B W hW U).Opens) :
    (chartOpens B S hS ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U)).obj V ⟶
      (SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj
        ((chartOpens B W hW U).obj V) :=
  ObjectProperty.homMk (CostructuredArrow.homMk (chartOpensRelocalizeOverHomSE B W S hW hS h U V)
    ((congrArg (fun k => yoneda.map _ ≫ k) (CostructuredArrow.w
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.map
          (chartOpensιSE U V)).hom).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans
          (congrArg yoneda.map (chartOpensRelocalizeOverHom_compSE B W S hW hS h U V)))))))

/-- The inverse identity morphism over `S` is compatible with the inclusions into the
relocalized chart. -/
theorem chartOpensRelocalizeInvOver_compSE (V : (etaleChartScheme B W hW U).Opens) :
    (Over.homMk (𝟙 _) (chartOpensRelocalize_wSE' B W S hW hS h U V) :
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj
        ((chartOpens B W hW U).obj V)).obj.left ⟶
        chartOpenOver B S hS ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) V) ≫
        chartOpenOverι B S hS ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) V =
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.map
        (chartOpensιSE U V)).hom.left :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- The inverse of `AlgebraicGeometry.Space.chartOpensRelocalizeHomSE`. -/
def chartOpensRelocalizeInvSE (V : (etaleChartScheme B W hW U).Opens) :
    (SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj ((chartOpens B W hW U).obj V) ⟶
      (chartOpens B S hS
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U)).obj V :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk (𝟙 _) (chartOpensRelocalize_wSE' B W S hW hS h U V))
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map
          (chartOpensRelocalizeInvOver_compSE B W S hW hS h U V)))).trans
      (CostructuredArrow.w
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.map (chartOpensιSE U V)).hom))))

/-- **The index functor of the chart restriction commutes with relocalization.** -/
def chartOpensRelocalizeIsoSE :
    chartOpens B S hS ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) ≅
      chartOpens B W hW U ⋙ (SmallEtale.relocalizeEquivalence B W S hW hS h X).functor :=
  NatIso.ofComponents
    (fun V ↦
      { hom := chartOpensRelocalizeHomSE B W S hW hS h U V
        inv := chartOpensRelocalizeInvSE B W S hW hS h U V
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
      ((Category.comp_id ((etaleChartScheme B W hW U).homOfLE i.le)).trans
        (Category.id_comp ((etaleChartScheme B W hW U).homOfLE i.le)).symm))

/-- The change of scalars of the chart restriction of `U` along the relocalization is that of
the relocalized chart. -/
theorem chartRestrictionSheafHom_relocalizeSE :
    letI := isContinuous_chartOpens B W hW X hX U
    letI := isContinuous_chartOpens B S hS _ (hX')
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U)
    @CategoryStruct.comp _ _ (chartScheme U).ringCatSheaf _ _
      (chartRestrictionSheafHom B W hW hX U ≫
        ((chartOpens B W hW U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B W hW X)
            (SmallEtale.relocalizeEquivalence B W S hW hS h X)
            (relocalizeRingSheafSE B W S hW hS h hX'))))
      ((@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _
        (chartOpensRelocalizeIsoSE B W S hW hS h U).hom RingCat.{u} _
        (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS _)
        (isContinuous_chartOpens B S hS _ (hX')
          ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U))
        (Functor.isContinuous_comp _ _ (Opens.grothendieckTopology (chartScheme U))
          (SmallEtale.topology B W hW X) (SmallEtale.topology B S hS _))).app
        (relocalizeRingSheafSE B W S hW hS h hX')) =
      chartRestrictionSheafHom B S hS (hX')
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  have hh : (relocalizeRingSheafSE B W S hW hS h hX').obj.map
      ((chartOpensRelocalizeIsoSE B W S hW hS h U).hom.app V.unop).op = 𝟙 _ := by
    change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (𝟙 _).op) = 𝟙 _
    simp
  refine (congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans ?_
  refine (NatTrans.comp_app _ _ V).trans ?_
  refine (congrArg (· ≫ _) ((congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans (NatTrans.comp_app _ _ V))).trans ?_
  refine (congrArg₂ (· ≫ ·) (Category.comp_id _) hh).trans ?_
  exact Category.comp_id _

/-- **The chart restriction of the `𝒪_X`-module attached to an `𝒪_{Λ X}`-module.** Its
restriction to a chart `U` of `X` is the restriction of `M` to the chart of `Λ X` attached to
`U`, as modules on the same scheme. -/
def restrictToChartRelocalizeInverseIsoSE
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)
      (hX')) :
    restrictToChart B W hW hX
        ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').inverse.obj M) U ≅
      restrictToChart B S hS (hX') M
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) := by
  letI i1 := isContinuous_chartOpens B W hW X hX U
  letI i2 := isContinuous_chartOpens B S hS _ (hX')
    ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U)
  letI i5 : (chartOpens B W hW U ⋙
      (SmallEtale.relocalizeEquivalence B W S hW hS h X).functor).IsContinuous
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS _) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B W hW X) _
  refine restrictToChartIsoPushforward B W hW hX U _ ≪≫
    (SheafOfModules.pushforwardComp (chartRestrictionSheafHom B W hW hX U)
      (𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B W hW X)
        (SmallEtale.relocalizeEquivalence B W S hW hS h X)
        (relocalizeRingSheafSE B W S hW hS h hX')))).app M ≪≫
    (@SheafOfModules.pushforwardCongr₂ (chartScheme U).Opens _
      (SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)) _
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS _)
      (chartOpens B S hS ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U))
      (chartOpens B W hW U ⋙ (SmallEtale.relocalizeEquivalence B W S hW hS h X).functor)
      (chartScheme U).ringCatSheaf (relocalizeRingSheafSE B W S hW hS h hX') i2 i5
      (chartRestrictionSheafHom B W hW hX U ≫
        ((chartOpens B W hW U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B W hW X)
            (SmallEtale.relocalizeEquivalence B W S hW hS h X)
            (relocalizeRingSheafSE B W S hW hS h hX'))))
      (chartRestrictionSheafHom B S hS (hX')
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U))
      (chartOpensRelocalizeIsoSE B W S hW hS h U)
      (chartRestrictionSheafHom_relocalizeSE B W S hW hS h hX hX' U)).app M ≪≫
    (restrictToChartIsoPushforward B S hS _
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).functor.obj U) M).symm

end Functor

section Inverse

/-- The inverse of the equivalence of small étale sites does not change the underlying morphism
of schemes of a morphism of charts. -/
theorem relocalizeEquivalence_inverse_map_hom_left_left
    {V V' : SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)} (f : V ⟶ V') :
    ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.map f).hom.left.left =
      f.hom.left.left :=
  relocalizeChartsInverse_map_left_left B W S hW hS h X f.hom

variable (U : SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor h).obj X))

/-- The open subscheme cut out by `V`, read over `T`, has the structure morphism of the chart of
`X` attached to the chart it cuts out of `U`. -/
theorem chartOpensRelocalizeInverse_wSE (V : (etaleChartScheme B S hS U).Opens) :
    𝟙 _ ≫ (chartOpenOver B W hW
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) V).hom =
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left.hom :=
  (congrArg (· ≫ _) ((Category.id_comp _).trans
      (relocalizeEquivalence_inverse_map_hom_left_left B W S hW hS h
        (chartOpensιSE U V)).symm)).trans
    (Over.w ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.map
      (chartOpensιSE U V)).hom.left)

/-- `AlgebraicGeometry.Space.chartOpensRelocalizeInverse_wSE`, read in the other direction. -/
theorem chartOpensRelocalizeInverse_wSE' (V : (etaleChartScheme B S hS U).Opens) :
    𝟙 _ ≫ ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left.hom =
      (chartOpenOver B W hW
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) V).hom :=
  (Category.id_comp _).trans
    (((Category.id_comp _).symm.trans (chartOpensRelocalizeInverse_wSE B W S hW hS h U V)).symm)

/-- The identity of the open subscheme cut out by `V`, as a morphism over `T`. -/
def chartOpensRelocalizeInverseOverHomSE (V : (etaleChartScheme B S hS U).Opens) :
    chartOpenOver B W hW ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) V ⟶
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left :=
  Over.homMk (𝟙 _) (chartOpensRelocalizeInverse_wSE' B W S hW hS h U V)

/-- `AlgebraicGeometry.Space.chartOpensRelocalizeInverseOverHomSE` is compatible with the
inclusions into the chart of `X` attached to `U`. -/
theorem chartOpensRelocalizeInverseOverHom_compSE (V : (etaleChartScheme B S hS U).Opens) :
    chartOpensRelocalizeInverseOverHomSE B W S hW hS h U V ≫
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.map
          (chartOpensιSE U V)).hom.left =
      chartOpenOverι B W hW ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) V :=
  Over.OverMorphism.ext ((Category.id_comp _).trans
    (relocalizeEquivalence_inverse_map_hom_left_left B W S hW hS h (chartOpensιSE U V)))

/-- The identity of a Zariski open of a chart `U` of `Λ X`, from the chart it cuts out of the
chart of `X` attached to `U` to the chart of `X` attached to the chart it cuts out. -/
def chartOpensRelocalizeInverseHomSE (V : (etaleChartScheme B S hS U).Opens) :
    (chartOpens B W hW ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U)).obj V ⟶
      (SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj
        ((chartOpens B S hS U).obj V) :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (chartOpensRelocalizeInverseOverHomSE B W S hW hS h U V)
    ((congrArg (fun k => yoneda.map _ ≫ k) (CostructuredArrow.w
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.map
          (chartOpensιSE U V)).hom).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans
          (congrArg yoneda.map (chartOpensRelocalizeInverseOverHom_compSE B W S hW hS h U V)))))))

/-- The inverse identity morphism over `T` is compatible with the inclusions into the chart of `X`
attached to `U`. -/
theorem chartOpensRelocalizeInverseInvOver_compSE (V : (etaleChartScheme B S hS U).Opens) :
    (Over.homMk (𝟙 _) (chartOpensRelocalizeInverse_wSE B W S hW hS h U V) :
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj
        ((chartOpens B S hS U).obj V)).obj.left ⟶
        chartOpenOver B W hW ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) V) ≫
        chartOpenOverι B W hW ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) V =
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.map
        (chartOpensιSE U V)).hom.left :=
  Over.OverMorphism.ext ((Category.id_comp _).trans
    (relocalizeEquivalence_inverse_map_hom_left_left B W S hW hS h (chartOpensιSE U V)).symm)

/-- The inverse of `AlgebraicGeometry.Space.chartOpensRelocalizeInverseHomSE`. -/
def chartOpensRelocalizeInverseInvSE (V : (etaleChartScheme B S hS U).Opens) :
    (SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj ((chartOpens B S hS U).obj V) ⟶
      (chartOpens B W hW
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U)).obj V :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk (𝟙 _) (chartOpensRelocalizeInverse_wSE B W S hW hS h U V))
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ _)
        ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map
          (chartOpensRelocalizeInverseInvOver_compSE B W S hW hS h U V)))).trans
      (CostructuredArrow.w
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.map (chartOpensιSE U V)).hom))))

/-- **The index functor of the chart restriction commutes with the inverse relocalization.** -/
def chartOpensRelocalizeInverseIsoSE :
    chartOpens B W hW ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) ≅
      chartOpens B S hS U ⋙ (SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse :=
  NatIso.ofComponents
    (fun V ↦
      { hom := chartOpensRelocalizeInverseHomSE B W S hW hS h U V
        inv := chartOpensRelocalizeInverseInvSE B W S hW hS h U V
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
    (fun {V V'} i ↦ by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply Over.OverMorphism.ext
      simp only [ObjectProperty.FullSubcategory.comp_hom, CostructuredArrow.comp_left,
        Over.comp_left]
      exact (Category.comp_id _).trans
        ((relocalizeEquivalence_inverse_map_hom_left_left B W S hW hS h
          ((chartOpens B S hS U).map i)).symm.trans (Category.id_comp _).symm))

/-- The counit of the equivalence of small étale sites, read in `Λ X`, is the identity on
underlying schemes, so the structure sheaf sends it to the identity. -/
theorem relocalizeRingSheaf_map_counitSE
    (V₀ : SmallEtale B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)) :
    (relocalizeRingSheafSE B W S hW hS h hX').obj.map
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).counit.app V₀).op = 𝟙 _ := by
  have e : ((SmallEtale.relocalizeEquivalence B W S hW hS h X).counit.app V₀).hom.left.left =
      𝟙 _ := relocalizeChartsDescentIso_hom_left_left B W S hW hS h V₀.obj
  change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (B.inclusion.map
    ((SmallEtale.relocalizeEquivalence B W S hW hS h X).counit.app V₀).hom.left.left).op) = 𝟙 _
  have e2 : B.inclusion.map
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).counit.app V₀).hom.left.left = 𝟙 _ := by
    rw [e]; exact B.inclusion.map_id _
  rw [e2]
  exact (congrArg (forget₂ CommRingCat RingCat).map (Scheme.Γ.map_id _)).trans
    ((forget₂ CommRingCat RingCat).map_id _)

/-- The change of scalars of the chart restriction of `U` along the inverse relocalization is
that of the chart of `X` attached to `U`. -/
theorem chartRestrictionSheafHom_relocalizeInverseSE :
    letI := isContinuous_chartOpens B S hS _ (hX') U
    letI := isContinuous_chartOpens B W hW X hX
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U)
    @CategoryStruct.comp _ _ (chartScheme U).ringCatSheaf _ _
      (chartRestrictionSheafHom B S hS (hX') U ≫
        ((chartOpens B S hS U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (Stacks.SheafOfModules.reindexBackSharp (J := SmallEtale.topology B S hS _)
            (J' := SmallEtale.topology B W hW X) (SmallEtale.relocalizeEquivalence B W S hW hS h X)
            (relocalizeRingSheafSE B W S hW hS h hX')))
      ((@Functor.sheafPushforwardContinuousNatTrans _ _ _ _ _ _
        (chartOpensRelocalizeInverseIsoSE B W S hW hS h U).hom RingCat.{u} _
        (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B W hW X)
        (isContinuous_chartOpens B W hW X hX
          ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U))
        (Functor.isContinuous_comp _ _ (Opens.grothendieckTopology (chartScheme U))
          (SmallEtale.topology B S hS _) (SmallEtale.topology B W hW X))).app
        (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B W hW X)
          (SmallEtale.relocalizeEquivalence B W S hW hS h X)
          (relocalizeRingSheafSE B W S hW hS h hX'))) =
      chartRestrictionSheafHom B W hW hX
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  have hh : (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B W hW X)
      (SmallEtale.relocalizeEquivalence B W S hW hS h X)
      (relocalizeRingSheafSE B W S hW hS h hX')).obj.map
      ((chartOpensRelocalizeInverseIsoSE B W S hW hS h U).hom.app V.unop).op = 𝟙 _ := by
    change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (𝟙 _).op) = 𝟙 _
    simp
  have h' := relocalizeRingSheaf_map_counitSE B W S hW hS h hX' ((chartOpens B S hS U).obj V.unop)
  refine (congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans ?_
  refine (NatTrans.comp_app _ _ V).trans ?_
  refine (congrArg (· ≫ _) ((congrArg (fun k => NatTrans.app k V)
    (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans (NatTrans.comp_app _ _ V))).trans ?_
  refine (congrArg₂ (· ≫ ·) ((congrArg (_ ≫ ·) h').trans (Category.comp_id _)) hh).trans ?_
  exact Category.comp_id _

/-- **The chart restriction of the `𝒪_{Λ X}`-module attached to an `𝒪_X`-module.** Its
restriction to a chart `U` of `Λ X` is the restriction of `F` to the chart of `X` attached to
`U`, as modules on the same scheme. -/
def restrictToChartRelocalizeFunctorIsoSE (F : Modules.{u, u} B W hW X hX) :
    restrictToChart B S hS (hX')
        ((relocalizeModulesEquivalenceSE B W S hW hS h hX hX').functor.obj F) U ≅
      restrictToChart B W hW hX F
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) := by
  letI i1 := isContinuous_chartOpens B S hS _ (hX') U
  letI i2 := isContinuous_chartOpens B W hW X hX
    ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U)
  letI i5 : (chartOpens B S hS U ⋙
      (SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse).IsContinuous
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B W hW X) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS _) _
  refine restrictToChartIsoPushforward B S hS _ U _ ≪≫
    (SheafOfModules.pushforwardComp
      (chartRestrictionSheafHom B S hS (hX') U)
      (Stacks.SheafOfModules.reindexBackSharp (J := SmallEtale.topology B S hS _)
        (J' := SmallEtale.topology B W hW X) (SmallEtale.relocalizeEquivalence B W S hW hS h X)
        (relocalizeRingSheafSE B W S hW hS h hX'))).app F ≪≫
    (@SheafOfModules.pushforwardCongr₂ (chartScheme U).Opens _ (SmallEtale B W hW X) _
      (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B W hW X)
      (chartOpens B W hW ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U))
      (chartOpens B S hS U ⋙ (SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse)
      (chartScheme U).ringCatSheaf
      (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B W hW X)
        (SmallEtale.relocalizeEquivalence B W S hW hS h X)
        (relocalizeRingSheafSE B W S hW hS h hX')) i2 i5
      (chartRestrictionSheafHom B S hS (hX') U ≫
        ((chartOpens B S hS U).sheafPushforwardContinuous RingCat.{u} _ _).map
          (Stacks.SheafOfModules.reindexBackSharp (J := SmallEtale.topology B S hS _)
            (J' := SmallEtale.topology B W hW X) (SmallEtale.relocalizeEquivalence B W S hW hS h X)
            (relocalizeRingSheafSE B W S hW hS h hX')))
      (chartRestrictionSheafHom B W hW hX
        ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U))
      (chartOpensRelocalizeInverseIsoSE B W S hW hS h U)
      (chartRestrictionSheafHom_relocalizeInverseSE B W S hW hS h hX hX' U)).app F ≪≫
    (restrictToChartIsoPushforward B W hW hX
      ((SmallEtale.relocalizeEquivalence B W S hW hS h X).inverse.obj U) F).symm

end Inverse

end AlgebraicGeometry.Space

end
