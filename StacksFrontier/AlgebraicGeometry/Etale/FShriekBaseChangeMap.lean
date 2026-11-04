module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion

/-!
# The base-change map of the direct image with compact support

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, with `f` locally quasi-finite,
and let `F` be an abelian sheaf on the small étale site of `X`. This file constructs the
base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)` of Stacks 0F5J and shows that it is functorial in `F`.

The construction is the one of the source. The base-change maps on finite-support sections over
the étale test objects of `Y` assemble, by their naturality in the test object and in the sheaf,
into a map `c : f_{p!}F ⟶ g_*(f'_!(p⁻¹F))` of abelian presheaves on the small étale site of `Y`;
since the target is a sheaf, `c` factors uniquely through the sheafification `f_!F` of `f_{p!}F`,
and transposing the resulting map through the inverse-image adjunction along `g` gives the
base-change map. That it is an isomorphism is Stacks 0F5J proper and is proved in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeIso`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fiberBaseChangePresheafApp` and
  `AlgebraicGeometry.SmallEtale.fiberBaseChangePresheafMap` — the map `c` of the source, over a
  single test object and as a map of abelian presheaves.
* `AlgebraicGeometry.SmallEtale.fShriekBaseChangePushforwardMap` — the factorization of `c`
  through the sheafification, a map `f_!F ⟶ g_*(f'_!(p⁻¹F))` of abelian sheaves.
* `AlgebraicGeometry.SmallEtale.fShriekBaseChangeMap` — the base-change map
  `g⁻¹f_!F ⟶ f'_!(p⁻¹F)`, with `AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatTrans` the same
  map read as a morphism of functors, which is its functoriality in `F`.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupportPushforward_map_eq` and
  `AlgebraicGeometry.SmallEtale.finiteSupportPushforward_map_sheaf_eq` — the two functorial
  actions of the finite-support direct image presheaf of Stacks 0F6M, read through the
  identification of its values with the groups of finite-support sections.
* `AlgebraicGeometry.SmallEtale.fiberBaseChangePresheafApp_naturality` and
  `AlgebraicGeometry.SmallEtale.fiberBaseChangePresheafApp_sheafMap` — the components of `c`
  commute with the restriction maps and are functorial in the sheaf.
* `AlgebraicGeometry.SmallEtale.toSheafify_comp_fShriekBaseChangePushforwardMap` and
  `AlgebraicGeometry.SmallEtale.toSheafify_app_comp_fShriekBaseChangePushforwardMap` — the
  defining property of the factorization through the sheafification.
* `AlgebraicGeometry.SmallEtale.fShriekBaseChangeMap_triangle` — the base-change map is the
  transpose of that factorization, which is what computes it on germs.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u + 1}` for the scheme universe `u`, rather than the
universe `max (u + 1) v` at which the finite-support direct image is available: the criterion
`AlgebraicGeometry.isIso_of_isIso_etaleStalkMap` by which the base-change map is shown to be an
isomorphism holds at `u + 1`, the points of the small étale site living relative to `Type u`.
Instantiating the finite-support side there costs nothing, the supports indexing its colimits
being already small at `u + 1`; this is the same choice as in
`StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero`.

The values of the finite-support direct image presheaf are identified with the colimits
`colim_Z H_Z(F)` only up to the equalities carried by
`AlgebraicGeometry.SmallEtale.FiniteSupportPushforwardSpec`, so every component of `c` is written
with those identifications; the two lemmas `finiteSupportPushforward_map_eq'` and
`finiteSupportPushforward_map_sheaf_eq'` put the two functorial actions of the presheaf in the
same form, and the naturality of `c` is then the naturality already proved of the base-change
maps on finite-support sections.

## References

* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F78](https://stacks.math.columbia.edu/tag/0F78)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

section Presheaf

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The restriction maps of the finite-support direct image presheaf are the maps on
finite-support sections given by base change of supports. -/
public theorem finiteSupportPushforward_map_eq
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V) :
    eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F V).symm ≫
        ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F).map i.op ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F V₁) =
      finiteSupportBaseChangeHom B f F i := by
  refine colimit.hom_ext fun E => ?_
  exact ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).2.map_restrict
    F i E).trans (finiteSupportBaseChangeHom_ι B f F i E).symm

/-- The restriction maps of the finite-support direct image presheaf, read through the
identification of its values with the groups of finite-support sections. -/
public theorem finiteSupportPushforward_map_eq'
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V) :
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F).map i.op =
      eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F V) ≫
        finiteSupportBaseChangeHom B f F i ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F V₁).symm := by
  rw [← finiteSupportPushforward_map_eq B f F i]
  simp

/-- The action of a morphism of abelian sheaves on the finite-support direct image presheaf is
the induced map of the colimits of supported sections. -/
public theorem finiteSupportPushforward_map_sheaf_eq
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (V : SmallEtale B Y.obj Y.property) :
    eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F V).symm ≫
        ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.map φ).app (op V) ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq G V) =
      colim.map (finiteSupportDiagramMap B f φ V) := by
  refine colimit.hom_ext fun E => ?_
  exact ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).2.map_sheaf
    φ V E).trans (colimit.ι_map (finiteSupportDiagramMap B f φ V) E).symm

/-- The action of a morphism of abelian sheaves on the finite-support direct image presheaf,
read through the identification of its values with the groups of finite-support sections. -/
public theorem finiteSupportPushforward_map_sheaf_eq'
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (V : SmallEtale B Y.obj Y.property) :
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.map φ).app (op V) =
      eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq F V) ≫
        colim.map (finiteSupportDiagramMap B f φ V) ≫
        eqToHom ((finiteSupportPushforward.{u, u + 1} B f
          (fun _ => inferInstance)).2.obj_eq G V).symm := by
  rw [← finiteSupportPushforward_map_sheaf_eq B f φ V]
  simp

end Presheaf

section Square

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- The component over an étale test object `V` of `Y` of the map `c` of the proof of
Stacks 0F5J: the base-change map on finite-support sections, followed by the sheafification
map of the finite-support direct image along `f'`. -/
public def fiberBaseChangePresheafApp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (V : SmallEtale B Y.obj Y.property) :
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F).obj (op V) ⟶
      ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)).obj.obj
        (op (baseChange B g V)) :=
  eqToHom ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).2.obj_eq F V) ≫
    fiberBaseChangeColimitMap.{u, u + 1} B p f' f g sq V F ≫
    eqToHom ((finiteSupportPushforward.{u, u + 1} B f'
      (fun _ => inferInstance)).2.obj_eq ((abPullback.{u, u + 1} B p).obj F)
      (baseChange B g V)).symm ≫
    (toSheafify (SmallEtale.topology B Y'.obj Y'.property)
      ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
        ((abPullback.{u, u + 1} B p).obj F))).app (op (baseChange B g V))

/-- The components of the map `c` commute with the restriction maps of the two presheaves. -/
public theorem fiberBaseChangePresheafApp_naturality
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    {V V₁ : SmallEtale B Y.obj Y.property} (i : V₁ ⟶ V) :
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F).map i.op ≫
        fiberBaseChangePresheafApp.{u} B p f' f g sq F V₁ =
      fiberBaseChangePresheafApp.{u} B p f' f g sq F V ≫
        ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)).obj.map
          ((smallEtaleBaseChange B g).map i).op := by
  rw [fiberBaseChangePresheafApp, fiberBaseChangePresheafApp,
    finiteSupportPushforward_map_eq' B f F i,
    show ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)).obj.map
        ((smallEtaleBaseChange B g).map i).op =
      (sheafify (SmallEtale.topology B Y'.obj Y'.property)
        ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
          ((abPullback.{u, u + 1} B p).obj F))).map
        ((smallEtaleBaseChange B g).map i).op from rfl,
    ]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← (toSheafify (SmallEtale.topology B Y'.obj Y'.property)
      ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.obj
        ((abPullback.{u, u + 1} B p).obj F))).naturality
      ((smallEtaleBaseChange B g).map i).op,
    finiteSupportPushforward_map_eq' B f' ((abPullback.{u, u + 1} B p).obj F)
      ((smallEtaleBaseChange B g).map i)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (fiberBaseChangeColimitMap_restriction.{u, u + 1} B p f' f g sq i F)]

/-- The components of the map `c` are functorial in the abelian sheaf. -/
public theorem fiberBaseChangePresheafApp_sheafMap
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (V : SmallEtale B Y.obj Y.property) :
    ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.map φ).app (op V) ≫
        fiberBaseChangePresheafApp.{u} B p f' f g sq G V =
      fiberBaseChangePresheafApp.{u} B p f' f g sq F V ≫
        ((fShriekFunctor.{u, u + 1} B f').map ((abPullback.{u, u + 1} B p).map φ)).hom.app
          (op (baseChange B g V)) := by
  rw [fiberBaseChangePresheafApp, fiberBaseChangePresheafApp,
    finiteSupportPushforward_map_sheaf_eq' B f φ V,
    show ((fShriekFunctor.{u, u + 1} B f').map ((abPullback.{u, u + 1} B p).map φ)).hom.app
        (op (baseChange B g V)) =
      (sheafifyMap (SmallEtale.topology B Y'.obj Y'.property)
        ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.map
          ((abPullback.{u, u + 1} B p).map φ))).app (op (baseChange B g V)) from rfl]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← NatTrans.comp_app, ← toSheafify_naturality
      (SmallEtale.topology B Y'.obj Y'.property)
      ((finiteSupportPushforward.{u, u + 1} B f' (fun _ => inferInstance)).1.map
        ((abPullback.{u, u + 1} B p).map φ)),
    NatTrans.comp_app,
    finiteSupportPushforward_map_sheaf_eq' B f' ((abPullback.{u, u + 1} B p).map φ)
      (baseChange B g V)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (fiberBaseChangeColimitMap_natural.{u, u + 1} B p f' f g sq V φ)]

/-- **Stacks 0F5J.** The map `c` of the proof: the map of abelian presheaves on the small étale
site of `Y` from the finite-support direct image `f_{p!}F` to the direct image along `g` of
`f'_!(p⁻¹F)`. -/
@[stacks 0F5J "the map c of abelian presheaves"]
public def fiberBaseChangePresheafMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F ⟶
      (smallEtaleBaseChange B g).op ⋙
        ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)).obj where
  app W := fiberBaseChangePresheafApp.{u} B p f' f g sq F W.unop
  naturality _ _ m := fiberBaseChangePresheafApp_naturality.{u} B p f' f g sq F m.unop

/-- The map `c` is functorial in the abelian sheaf. -/
public theorem fiberBaseChangePresheafMap_sheafMap
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.map φ ≫
        fiberBaseChangePresheafMap.{u} B p f' f g sq G =
      fiberBaseChangePresheafMap.{u} B p f' f g sq F ≫
        Functor.whiskerLeft (smallEtaleBaseChange B g).op
          ((fShriekFunctor.{u, u + 1} B f').map ((abPullback.{u, u + 1} B p).map φ)).hom :=
  NatTrans.ext (funext fun W => fiberBaseChangePresheafApp_sheafMap.{u} B p f' f g sq φ W.unop)

/-- The map `f_!F ⟶ g_*(f'_!(p⁻¹F))` of abelian sheaves on the small étale site of `Y` obtained
from the map `c` by sheafification: the unique map whose composite with the sheafification map
of `f_{p!}F` is `c`. -/
public def fShriekBaseChangePushforwardMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (fShriekFunctor.{u, u + 1} B f).obj F ⟶
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Y'.obj Y'.property)).obj
          ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F)) :=
  ObjectProperty.homMk (sheafifyLift (SmallEtale.topology B Y.obj Y.property)
    (fiberBaseChangePresheafMap.{u} B p f' f g sq F)
    (((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property)).obj
        ((fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F))).property)

/-- The defining property of the sheafified map: composed with the sheafification map of
`f_{p!}F` it is the map `c`. -/
public theorem toSheafify_comp_fShriekBaseChangePushforwardMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F) ≫
        (fShriekBaseChangePushforwardMap.{u} B p f' f g sq F).hom =
      fiberBaseChangePresheafMap.{u} B p f' f g sq F :=
  toSheafify_sheafifyLift _ _ _

/-- **Stacks 0F5J.** The base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)` of abelian sheaves on the small
étale site of `Y'`: the map `c` of the source, sheafified and transposed through the
inverse-image adjunction along `g`. -/
@[stacks 0F5J "the base-change map of sheaves, before it is shown to be an isomorphism"]
public def fShriekBaseChangeMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (abPullback.{u, u + 1} B g).obj ((fShriekFunctor.{u, u + 1} B f).obj F) ⟶
      (fShriekFunctor.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B p).obj F) :=
  (((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property)).homEquiv
    ((fShriekFunctor.{u, u + 1} B f).obj F)
    ((fShriekFunctor.{u, u + 1} B f').obj
      ((abPullback.{u, u + 1} B p).obj F))).symm
    (fShriekBaseChangePushforwardMap.{u} B p f' f g sq F)

/-- The base-change map is the transpose of the sheafified map `c`: the unit of the
inverse-image adjunction followed by the direct image of the base-change map is that map. -/
public theorem fShriekBaseChangeMap_triangle
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    ((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B Y'.obj Y'.property)).unit.app
          ((fShriekFunctor.{u, u + 1} B f).obj F) ≫
        ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).map
          (fShriekBaseChangeMap.{u} B p f' f g sq F) =
      fShriekBaseChangePushforwardMap.{u} B p f' f g sq F := by
  have h := ((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B Y'.obj Y'.property)).homEquiv_unit
    (f := fShriekBaseChangeMap.{u} B p f' f g sq F)
  rw [← h, fShriekBaseChangeMap, Equiv.apply_symm_apply]

/-- The defining property of the sheafified map, over an étale test object. -/
public theorem toSheafify_app_comp_fShriekBaseChangePushforwardMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (V : SmallEtale B Y.obj Y.property) :
    (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, u + 1} B f
            (fun _ => inferInstance)).1.obj F)).app (op V) ≫
        (fShriekBaseChangePushforwardMap.{u} B p f' f g sq F).hom.app (op V) =
      fiberBaseChangePresheafApp.{u} B p f' f g sq F V := by
  have h := NatTrans.congr_app
    (toSheafify_comp_fShriekBaseChangePushforwardMap.{u} B p f' f g sq F) (op V)
  rw [NatTrans.comp_app] at h
  exact h

/-- Two maps of sheaves out of a sheafification agree as soon as they agree after the
sheafification map. -/
private theorem sheaf_hom_ext_of_toSheafify
    {P : (SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {Q : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}}
    {x y : (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{u + 1}).obj P ⟶ Q}
    (h : toSheafify (SmallEtale.topology B Y.obj Y.property) P ≫ x.hom =
      toSheafify (SmallEtale.topology B Y.obj Y.property) P ≫ y.hom) : x = y :=
  ((sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
    AddCommGrpCat.{u + 1}).homEquiv P Q).injective (by
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      exact h)

/-- The sheafified map `c` is functorial in the abelian sheaf. -/
public theorem fShriekBaseChangePushforwardMap_natural
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (fShriekFunctor.{u, u + 1} B f).map φ ≫
        fShriekBaseChangePushforwardMap.{u} B p f' f g sq G =
      fShriekBaseChangePushforwardMap.{u} B p f' f g sq F ≫
        ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B Y'.obj Y'.property)).map
          ((fShriekFunctor.{u, u + 1} B f').map ((abPullback.{u, u + 1} B p).map φ)) := by
  refine sheaf_hom_ext_of_toSheafify.{u} B (NatTrans.ext (funext fun W => ?_))
  obtain ⟨V⟩ := W
  rw [NatTrans.comp_app, NatTrans.comp_app]
  show (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F)).app
        (op V) ≫
      (sheafifyMap (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.map φ)).app
          (op V) ≫
        (fShriekBaseChangePushforwardMap.{u} B p f' f g sq G).hom.app (op V) =
    (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.obj F)).app
        (op V) ≫
      (fShriekBaseChangePushforwardMap.{u} B p f' f g sq F).hom.app (op V) ≫
        ((fShriekFunctor.{u, u + 1} B f').map
          ((abPullback.{u, u + 1} B p).map φ)).hom.app (op (baseChange B g V))
  rw [← Category.assoc, ← NatTrans.comp_app,
    ← toSheafify_naturality (SmallEtale.topology B Y.obj Y.property)
      ((finiteSupportPushforward.{u, u + 1} B f (fun _ => inferInstance)).1.map φ),
    NatTrans.comp_app, Category.assoc,
    toSheafify_app_comp_fShriekBaseChangePushforwardMap.{u} B p f' f g sq G V]
  exact (fiberBaseChangePresheafApp_sheafMap.{u} B p f' f g sq φ V).trans
    ((congrArg (fun k => k ≫ ((fShriekFunctor.{u, u + 1} B f').map
          ((abPullback.{u, u + 1} B p).map φ)).hom.app (op (baseChange B g V)))
        (toSheafify_app_comp_fShriekBaseChangePushforwardMap.{u} B p f' f g sq F V).symm).trans
      (Category.assoc _ _ _))

/-- **Stacks 0F5J.** The base-change map `g⁻¹f_!F ⟶ f'_!(p⁻¹F)` is functorial in `F`: it is a
morphism of functors on abelian sheaves on the small étale site of `X`. -/
@[stacks 0F5J "functoriality in the sheaf of the base-change map of sheaves"]
public def fShriekBaseChangeNatTrans :
    fShriekFunctor.{u, u + 1} B f ⋙ abPullback.{u, u + 1} B g ⟶
      abPullback.{u, u + 1} B p ⋙ fShriekFunctor.{u, u + 1} B f' where
  app F := fShriekBaseChangeMap.{u} B p f' f g sq F
  naturality F G φ := by
    have hstar := fShriekBaseChangePushforwardMap_natural.{u} B p f' f g sq φ
    have hleft := ((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Y'.obj Y'.property)).homEquiv_naturality_left_symm
      ((fShriekFunctor.{u, u + 1} B f).map φ)
      (fShriekBaseChangePushforwardMap.{u} B p f' f g sq G)
    have hright := ((smallEtaleBaseChange B g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B Y'.obj Y'.property)).homEquiv_naturality_right_symm
      (fShriekBaseChangePushforwardMap.{u} B p f' f g sq F)
      ((fShriekFunctor.{u, u + 1} B f').map ((abPullback.{u, u + 1} B p).map φ))
    exact hleft.symm.trans ((congrArg _ hstar).trans hright)

end Square

end AlgebraicGeometry.SmallEtale

end
