module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# The inverse image of the structure sheaf after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` for `B` and let `f' : X' ⟶ Y'` be its inverse image on the enlarged
site. The comparison of inverse images of sheaves of sets
(`AlgebraicGeometry.SiteEnlargement.inverseImageComparison`) carries the ring operations along,
so it identifies `f⁻¹𝒪_Y` with the restriction of `f'⁻¹𝒪_{Y'}` as sheaves of commutative rings,
and the identification carries the structure map `f'⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}` to `f⁻¹𝒪_Y ⟶ 𝒪_X`.

## Main definitions

* `AlgebraicGeometry.SiteEnlargement.inverseImageRingComparison`: the identification.

## Main results

* `AlgebraicGeometry.SiteEnlargement.inverseImageRingComparison_fSharpInverseImage`: the
  compatibility with the structure maps.

## Implementation notes

Every factor of the identification but one is the identity on underlying sheaves of sets: the
inverse image along restriction is restriction
(`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`) and inverse images compose
(`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafComp`). The one remaining factor is
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans` of the comparison of inverse
images, which is a ring map because a natural transformation of finite-product-preserving
functors respects the transported ring operations.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.SiteEnlargement

section General

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']

/-- A natural transformation between finite-product-preserving functors of sheaves of sets induces
a morphism between the inverse images of a sheaf of commutative rings along them: the morphism of
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans` of the underlying sheaves of rings,
read back through the full faithfulness of forgetting commutativity. -/
def pullbackCommRingSheafMapOfNatTrans (θ : Φ ⟶ Φ') (O : Sheaf K CommRingCat.{ww'}) :
    pullbackCommRingSheaf J Φ O ⟶ pullbackCommRingSheaf J Φ' O :=
  (fullyFaithfulForgetCommRingSheaf J).preimage
    (pullbackRingSheafMapOfNatTrans J (Stacks.SheafOfModules.Tensor.ringSheaf O) θ)

/-- The morphism induced by a natural transformation is that transformation on underlying sheaves
of sets. -/
theorem forget_map_pullbackCommRingSheafMapOfNatTrans (θ : Φ ⟶ Φ')
    (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose J (forget CommRingCat.{ww})).map (pullbackCommRingSheafMapOfNatTrans J θ O) =
      θ.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) := by
  refine Sheaf.hom_ext_sections fun X s => ?_
  change RingCat.Hom.hom (((Stacks.forgetCommRingSheaf J).map
    (pullbackCommRingSheafMapOfNatTrans J θ O)).hom.app X) s = _
  have e := (fullyFaithfulForgetCommRingSheaf J).map_preimage
    (X := pullbackCommRingSheaf J Φ O) (Y := pullbackCommRingSheaf J Φ' O)
    (pullbackRingSheafMapOfNatTrans J (Stacks.SheafOfModules.Tensor.ringSheaf O) θ)
  exact congrArg (fun m : pullbackRingSheaf J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶
    pullbackRingSheaf J Φ' (Stacks.SheafOfModules.Tensor.ringSheaf O) =>
      RingCat.Hom.hom (m.hom.app X) s) e

/-- The morphism induced by a natural isomorphism is an isomorphism. -/
instance isIso_pullbackCommRingSheafMapOfNatTrans (θ : Φ ⟶ Φ') [IsIso θ]
    (O : Sheaf K CommRingCat.{ww'}) : IsIso (pullbackCommRingSheafMapOfNatTrans J θ O) := by
  have : IsIso ((sheafCompose J (forget CommRingCat.{ww})).map
      (pullbackCommRingSheafMapOfNatTrans J θ O)) := by
    rw [forget_map_pullbackCommRingSheafMapOfNatTrans]
    exact NatIso.isIso_app_of_isIso θ _
  exact isIso_of_reflects_iso _ (sheafCompose J (forget CommRingCat.{ww}))

end General

section Square

universe w vX uX vY uY vX' uX' vY' uY'

variable {CX : Type uX} [Category.{vX} CX] {CY : Type uY} [Category.{vY} CY]
  {CX' : Type uX'} [Category.{vX'} CX'] {CY' : Type uY'} [Category.{vY'} CY']
  (JX : GrothendieckTopology CX) (JY : GrothendieckTopology CY)
  (JX' : GrothendieckTopology CX') (JY' : GrothendieckTopology CY')
  [JX.HasSheafCompose (forget RingCat.{w})] [JY.HasSheafCompose (forget RingCat.{w})]
  [JX'.HasSheafCompose (forget RingCat.{w})] [JY'.HasSheafCompose (forget RingCat.{w})]
  [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JX'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JX.HasSheafCompose (forget CommRingCat.{w})] [JY.HasSheafCompose (forget CommRingCat.{w})]
  [JX'.HasSheafCompose (forget CommRingCat.{w})] [JY'.HasSheafCompose (forget CommRingCat.{w})]
  (GX : CX ⥤ CX') (GY : CY ⥤ CY') [GX.IsContinuous JX JX'] [GY.IsContinuous JY JY']
  (L : Sheaf JY (Type w) ⥤ Sheaf JX (Type w)) [PreservesFiniteProducts L]
  (L' : Sheaf JY' (Type w) ⥤ Sheaf JX' (Type w)) [PreservesFiniteProducts L']
  [PreservesFiniteProducts (GX.sheafPushforwardContinuous (Type w) JX JX')]
  [PreservesFiniteProducts (GY.sheafPushforwardContinuous (Type w) JY JY')]
  (θ : GY.sheafPushforwardContinuous (Type w) JY JY' ⋙ L ⟶
    L' ⋙ GX.sheafPushforwardContinuous (Type w) JX JX')
  (O : Sheaf JY' CommRingCat.{w})

/-- The inverse image along a finite-product-preserving functor of a morphism of sheaves of
commutative rings is, on underlying sheaves of sets, the image of the underlying morphism. -/
theorem forget_map_pullbackCommRingSheafMap {O₁ O₂ : Sheaf JY CommRingCat.{w}} (a : O₁ ⟶ O₂) :
    (sheafCompose JX (forget CommRingCat.{w})).map (pullbackCommRingSheafMap JX L a) =
      L.map ((sheafCompose JY (forget CommRingCat.{w})).map a) :=
  (congrArg (sheafCompose JX (forget RingCat.{w})).map
    (forgetCommRingSheaf_map_pullbackCommRingSheafMap JX L a)).trans
    (ringSheafMap_pullbackRingSheafMap JX L ((Stacks.forgetCommRingSheaf JY).map a))

/-- **Transport of ring operations around a square of functors of sheaves of sets.** For a
natural transformation `θ : R_Y ⋙ L ⟶ L' ⋙ R_X`, with `R_X`, `R_Y` restrictions along continuous
functors and `L`, `L'` preserving finite products, the induced morphism from the inverse image
along `L` of a restricted sheaf of commutative rings to the restriction of its inverse image
along `L'`. -/
def squareCommRingSheafMap :
    pullbackCommRingSheaf JX L ((GY.sheafPushforwardContinuous CommRingCat.{w} JY JY').obj O) ⟶
      (GX.sheafPushforwardContinuous CommRingCat.{w} JX JX').obj (pullbackCommRingSheaf JX' L' O) :=
  pullbackCommRingSheafMap JX L (restrictionCommRingIso.{w} JY JY' GY O).inv ≫
    (pullbackCommRingSheafComp JY JX (GY.sheafPushforwardContinuous (Type w) JY JY') L O).hom ≫
    pullbackCommRingSheafMapOfNatTrans JX θ O ≫
    (pullbackCommRingSheafComp JX' JX L' (GX.sheafPushforwardContinuous (Type w) JX JX') O).inv ≫
    (restrictionCommRingIso.{w} JX JX' GX (pullbackCommRingSheaf JX' L' O)).hom

/-- The transported morphism is `θ` on sections. -/
theorem squareCommRingSheafMap_apply (U : CXᵒᵖ)
    (x : ((sheafCompose JX (forget CommRingCat.{w})).obj (pullbackCommRingSheaf JX L
      ((GY.sheafPushforwardContinuous CommRingCat.{w} JY JY').obj O))).obj.obj U) :
    ((sheafCompose JX (forget CommRingCat.{w})).map
        (squareCommRingSheafMap JX JY JX' JY' GX GY L L' θ O)).hom.app U x =
      (θ.app ((sheafCompose JY' (forget CommRingCat.{w})).obj O)).hom.app U x := by
  have ha := (forget_map_pullbackCommRingSheafMap JX JY L
    (restrictionCommRingIso.{w} JY JY' GY O).inv).trans
    ((congrArg L.map (restrictionCommRingIso_inv_forget.{w} JY JY' GY O)).trans (L.map_id _))
  have hd := forget_map_pullbackCommRingSheafComp_hom JX' JX L'
    (GX.sheafPushforwardContinuous (Type w) JX JX') O
  have hd' : (sheafCompose JX (forget CommRingCat.{w})).map
      (pullbackCommRingSheafComp JX' JX L' (GX.sheafPushforwardContinuous (Type w) JX JX') O).inv =
        𝟙 _ :=
    (Category.comp_id _).symm.trans ((congrArg (_ ≫ ·) hd.symm).trans (Iso.map_inv_hom_id _ _))
  have hall : (sheafCompose JX (forget CommRingCat.{w})).map
      (squareCommRingSheafMap JX JY JX' JY' GX GY L L' θ O) =
        (sheafCompose JX (forget CommRingCat.{w})).map
          (pullbackCommRingSheafMapOfNatTrans JX θ O) := by
    simp only [squareCommRingSheafMap, Functor.map_comp, ha, hd', restrictionCommRingIso_hom_forget,
      forget_map_pullbackCommRingSheafComp_hom]
    rfl
  exact congrArg (fun m => m.hom.app U x)
    (hall.trans (forget_map_pullbackCommRingSheafMapOfNatTrans JX θ O))

/-- The transported morphism is `θ` on underlying sheaves of sets. -/
theorem forget_map_squareCommRingSheafMap :
    (sheafCompose JX (forget CommRingCat.{w})).map
        (squareCommRingSheafMap JX JY JX' JY' GX GY L L' θ O) =
      θ.app ((sheafCompose JY' (forget CommRingCat.{w})).obj O) :=
  Sheaf.hom_ext_sections fun U x => squareCommRingSheafMap_apply JX JY JX' JY' GX GY L L' θ O U x

/-- The transported morphism is an isomorphism when `θ` is one. -/
instance isIso_squareCommRingSheafMap [IsIso θ] :
    IsIso (squareCommRingSheafMap JX JY JX' JY' GX GY L L' θ O) := by
  have : IsIso ((sheafCompose JX (forget CommRingCat.{w})).map
      (squareCommRingSheafMap JX JY JX' JY' GX GY L L' θ O)) := by
    rw [forget_map_squareCommRingSheafMap]
    exact NatIso.isIso_app_of_isIso θ _
  exact isIso_of_reflects_iso _ (sheafCompose JX (forget CommRingCat.{w}))

end Square

open Space

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}}
  {hS : B.Contains S} (hS' : B'.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Restriction of sheaves of commutative rings along the transport of étale charts. -/
abbrev restrictRingSheaf (X : AlgebraicSpaces B S hS) :
    Sheaf (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
        CommRingCat.{u} ⥤ Sheaf (Space.SmallEtale.topology B S hS X.obj) CommRingCat.{u} :=
  (chartTransport B B' h S hS X).sheafPushforwardContinuous CommRingCat.{u}
    (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)

/-- Restriction of sheaves of sets along the transport of étale charts preserves finite
products. -/
instance (X : AlgebraicSpaces B S hS) : PreservesFiniteProducts (restrictSheaf h hS' X) :=
  inferInstance

/-- The inverse image functor of the small étale topos morphism of `f` preserves finite
products. -/
instance : PreservesFiniteProducts (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage :=
  haveI := (smallEtaleRingedToposHom B S hS f).toToposHom.preservesFiniteLimits
  inferInstance

/-- The inverse image functor of the small étale topos morphism of `f'` preserves finite
products. -/
instance : PreservesFiniteProducts
    (smallEtaleRingedToposHom B' S hS'
      ((changeBigSite B B' h S hS).map f)).toToposHom.inverseImage :=
  haveI := (smallEtaleRingedToposHom B' S hS'
    ((changeBigSite B B' h S hS).map f)).toToposHom.preservesFiniteLimits
  inferInstance

/-- **The inverse image of the structure sheaf of `Y` is the restriction of the inverse image of
the structure sheaf of `Y'`**, as sheaves of commutative rings on the small étale site of `X`: the
comparison of inverse images of sheaves of sets, carrying the ring operations along. -/
def inverseImageRingComparison :
    (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O ≅
      (restrictRingSheaf h hS' X).obj
        ((inverseImageCommRingFunctor (smallEtaleRingedToposHom B' S hS'
          ((changeBigSite B B' h S hS).map f)).toToposHom).obj
            (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).O) :=
  @asIso _ _ _ _ (squareCommRingSheafMap.{u} (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B S hS Y.obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj Y).obj)
    (chartTransport B B' h S hS X) (chartTransport B B' h S hS Y)
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
    (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)).toToposHom.inverseImage
    (inverseImageComparison h hS' f)
    (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).O)
    (isIso_squareCommRingSheafMap.{u} (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B S hS Y.obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj Y).obj)
    (chartTransport B B' h S hS X) (chartTransport B B' h S hS Y)
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
    (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)).toToposHom.inverseImage
    (inverseImageComparison h hS' f)
    (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).O)

/-- The comparison of inverse images of the structure sheaf is, on underlying sheaves of sets, the
comparison of inverse images of sheaves of sets. -/
theorem forget_map_inverseImageRingComparison_hom :
    (sheafCompose (Space.SmallEtale.topology B S hS X.obj) (forget CommRingCat.{u})).map
        (inverseImageRingComparison h hS' f).hom =
      (inverseImageComparison h hS' f).app
        ((sheafCompose (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj Y).obj)
          (forget CommRingCat.{u})).obj
            (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).O) :=
  forget_map_squareCommRingSheafMap.{u} (Space.SmallEtale.topology B S hS X.obj)
    (Space.SmallEtale.topology B S hS Y.obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj X).obj)
    (Space.SmallEtale.topology B' S hS' ((changeBigSite B B' h S hS).obj Y).obj)
    (chartTransport B B' h S hS X) (chartTransport B B' h S hS Y)
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage
    (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)).toToposHom.inverseImage
    (inverseImageComparison h hS' f)
    (smallEtaleRingedTopos B' S hS' ((changeBigSite B B' h S hS).obj Y)).O

/-- **The identification of inverse images of structure sheaves carries the structure map of `f'`
to that of `f`**: the identification followed by the restriction of `f'⁻¹𝒪_{Y'} ⟶ 𝒪_{X'}` is
`f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
theorem inverseImageRingComparison_fSharpInverseImage :
    ((inverseImageRingComparison h hS' f).hom ≫ (restrictRingSheaf h hS' X).map
        (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f)).fSharpInverseImage :
      (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
          (smallEtaleRingedTopos B S hS Y).O ⟶ (smallEtaleRingedTopos B S hS X).O) =
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage := by
  apply (sheafCompose (Space.SmallEtale.topology B S hS X.obj)
    (forget CommRingCat.{u})).map_injective
  refine (Functor.map_comp _ _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) (forget_map_inverseImageRingComparison_hom h hS' f)
    (congrArg (restrictSheaf h hS' X).map
      (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
        (smallEtaleRingedToposHom B' S hS' ((changeBigSite B B' h S hS).map f))))).trans ?_
  exact (inverseImageComparison_fSharpInverseImageForget h hS' f).trans
    (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
      (smallEtaleRingedToposHom B S hS f)).symm

end AlgebraicGeometry.SiteEnlargement

end
