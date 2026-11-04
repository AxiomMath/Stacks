module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupoidPushforward

/-!
# The morphism of base changes induced by a morphism of affine groupoid schemes

Let `F : G' ⟶ G` be a morphism of groupoid schemes over a scheme `S`, with affine object and
arrow schemes, and write `C` and `C'` for the two rings of invariant functions, so that `F`
induces `AlgebraicGeometry.GroupoidScheme.invariantRingMap F : C →+* C'`. Base changing `G`
along an extension `C ⟶ C₁` and `G'` along an extension `C' ⟶ C'₁` produces two groupoid
schemes over *different* bases, `Spec C₁` and `Spec C'₁`. Given a map `ψ : C₁ →+* C'₁`
compatible with `invariantRingMap F`, this file constructs a morphism of groupoid schemes over
`Spec C₁` from the pushforward (`Stacks.Groupoids.GroupoidScheme.pushforward`) of the base change
of `G'` along `Spec C'₁ ⟶ Spec C₁` to the base change of `G`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.baseChangeMapObjects` and
  `AlgebraicGeometry.GroupoidScheme.baseChangeMapArrows`: the maps on object and arrow schemes.
* `AlgebraicGeometry.GroupoidScheme.baseChangeHom`: the induced morphism of groupoid schemes,
  from the pushforward of the base change of `G'` to the base change of `G`.
* `AlgebraicGeometry.GroupoidScheme.tensorBaseRing`: the extension `C' ⟶ C' ⊗[C] C₁` of the
  invariant ring of `G'` determined by an extension `C ⟶ C₁` of the invariant ring of `G`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange.source_isPullback` and
  `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange.target_isPullback`: the source
  and target maps of a base change are the base changes of the source and target maps of `G`.
* `AlgebraicGeometry.GroupoidScheme.baseChangeHom_mapArrows_left_comp_arrowsProjection` and
  its companion on objects characterize the induced morphism by its compatibility with the two
  projections.
* `AlgebraicGeometry.GroupoidScheme.source_isPullback_baseChangeHom` and
  `AlgebraicGeometry.GroupoidScheme.target_isPullback_baseChangeHom`: the source and target
  squares of the induced morphism are cartesian as soon as those of `F` are;
  `AlgebraicGeometry.GroupoidScheme.source_isPullback_mapArrows_baseChangeHom` and
  `AlgebraicGeometry.GroupoidScheme.target_isPullback_mapArrows_baseChangeHom` are the same
  statements read off the morphism itself.
* `AlgebraicGeometry.GroupoidScheme.invariantRingMap_baseChangeHom_canonicalMap` and
  `AlgebraicGeometry.GroupoidScheme.invariantRingMap_baseChangeHom_comp_ofBijective`: the map
  on invariant rings induced by the new morphism is the given extension `C₁ ⟶ C'₁`, read
  through the canonical maps of Tag 03BK from the two new base rings to the two rings of
  invariant functions.
* `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange.isAffine_objects` and
  `AlgebraicGeometry.GroupoidScheme.AffineInvariantBaseChange.isAffine_arrows`: the object and
  arrow schemes of a base change are affine.
* `AlgebraicGeometry.GroupoidScheme.isPullback_baseChangeMapObjects` and
  `AlgebraicGeometry.GroupoidScheme.etale_baseChangeMapObjects`: if `Spec C'₁` is the fibre
  product of `Spec C'` and `Spec C₁` over `Spec C`, then the square formed by the map on object
  schemes of the induced morphism, the map on object schemes of `F` and the two projections is
  cartesian, so the former is étale as soon as the latter is.
* `AlgebraicGeometry.GroupoidScheme.isPullback_invariantSpectrumMap_tensorBaseRing`: the
  spectrum of `C' ⊗[C] C₁` is the fibre product of `Spec C'` and `Spec C₁` over `Spec C`.
* `AlgebraicGeometry.GroupoidScheme.isPullback_baseChangeMapObjects_tensorBaseRing` and
  `AlgebraicGeometry.GroupoidScheme.etale_baseChangeMapObjects_tensorBaseRing`: the same two
  statements for `C'₁ = C' ⊗[C] C₁`, with no hypothesis beyond `F`.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT8](https://stacks.math.columbia.edu/tag/0DT8)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

/-! ### Lifts into a fibre product of an over category, on underlying schemes -/

/-- The first projection of a lift into a fibre product of `Over S`, on underlying schemes. -/
@[reassoc]
theorem overFibreProduct_lift_left_comp_fst {S : Scheme.{u}} {X Y Z : Over S} (a b : Y ⟶ Z)
    (f g : X ⟶ Y) (w : f ≫ a = g ≫ b) :
    (pullback.lift f g w).left ≫ (pullback.fst a b).left = f.left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left (pullback.lift_fst f g w)

/-- The second projection of a lift into a fibre product of `Over S`, on underlying schemes. -/
@[reassoc]
theorem overFibreProduct_lift_left_comp_snd {S : Scheme.{u}} {X Y Z : Over S} (a b : Y ⟶ Z)
    (f g : X ⟶ Y) (w : f ≫ a = g ≫ b) :
    (pullback.lift f g w).left ≫ (pullback.snd a b).left = g.left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left (pullback.lift_snd f g w)

namespace GroupoidScheme

/-! ### The map on composable arrows induced by a morphism of groupoid schemes -/

section Composable

variable {S : Scheme.{u}} {G G' : GroupoidScheme S}

/-- The map induced on composable arrows reads the first arrow of a composable pair through
the map on arrows. -/
theorem mapComposable_comp_fst (F : GroupoidScheme.Hom G' G) :
    F.mapComposable ≫ pullback.fst G.source G.target =
      pullback.fst G'.source G'.target ≫ F.mapArrows :=
  pullback.lift_fst _ _ _

/-- The map induced on composable arrows reads the second arrow of a composable pair through
the map on arrows. -/
theorem mapComposable_comp_snd (F : GroupoidScheme.Hom G' G) :
    F.mapComposable ≫ pullback.snd G.source G.target =
      pullback.snd G'.source G'.target ≫ F.mapArrows :=
  pullback.lift_snd _ _ _

/-- The map induced on composable arrows, against the first projection, on underlying
schemes. -/
@[reassoc]
theorem mapComposable_comp_fst_left (F : GroupoidScheme.Hom G' G) :
    F.mapComposable.left ≫ (pullback.fst G.source G.target).left =
      (pullback.fst G'.source G'.target).left ≫ F.mapArrows.left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left (mapComposable_comp_fst F)

/-- The map induced on composable arrows, against the second projection, on underlying
schemes. -/
@[reassoc]
theorem mapComposable_comp_snd_left (F : GroupoidScheme.Hom G' G) :
    F.mapComposable.left ≫ (pullback.snd G.source G.target).left =
      (pullback.snd G'.source G'.target).left ≫ F.mapArrows.left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left (mapComposable_comp_snd F)

/-- Compatibility of a morphism of groupoid schemes with composition, on underlying
schemes. -/
@[reassoc]
theorem comp_left_comp_mapArrows_left (F : GroupoidScheme.Hom G' G) :
    G'.comp.left ≫ F.mapArrows.left = F.mapComposable.left ≫ G.comp.left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left F.comp_mapArrows

/-- Compatibility of a morphism of groupoid schemes with the identity sections, on underlying
schemes. -/
@[reassoc]
theorem map_identity_left (F : GroupoidScheme.Hom G' G) :
    F.mapObjects.left ≫ G.identity.left = G'.identity.left ≫ F.mapArrows.left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left F.map_identity

/-- The canonical morphism from the arrow scheme of `G'` to the invariant spectrum of `G'`
intertwines the map on arrows with the map on invariant rings. -/
theorem mapArrows_comp_arrowsToInvariantSpectrum (F : GroupoidScheme.Hom G' G) :
    F.mapArrows.left ≫ arrowsToInvariantSpectrum G =
      arrowsToInvariantSpectrum G' ≫
        Spec.map (CommRingCat.ofHom (invariantRingMap F)) := by
  change F.mapArrows.left ≫ G.source.left ≫ objectsToInvariantSpectrum G =
    (G'.source.left ≫ objectsToInvariantSpectrum G') ≫ _
  rw [← Category.assoc, F.map_source_left, Category.assoc,
    mapObjects_comp_objectsToInvariantSpectrum F, Category.assoc]

end Composable

/-! ### The source and target maps of a base change -/

namespace AffineInvariantBaseChange

variable {S : Scheme.{u}} {G : GroupoidScheme S} {C₁ : Type u} [CommRing C₁]
  [Algebra (invariantRing G) C₁]

/-- The object scheme of a base change is affine. -/
instance isAffine_objects (bc : AffineInvariantBaseChange G C₁) :
    IsAffine bc.groupoid.objects.left :=
  IsAffine.of_isIso bc.objectsIso.hom

/-- The arrow scheme of a base change is affine. -/
instance isAffine_arrows (bc : AffineInvariantBaseChange G C₁) :
    IsAffine bc.groupoid.arrows.left :=
  IsAffine.of_isIso bc.arrowsIso.hom

/-- The projection to the scheme of composable arrows, against the first projection. -/
@[reassoc]
theorem composableProjection_comp_fst (bc : AffineInvariantBaseChange G C₁) :
    bc.composableProjection ≫ (pullback.fst G.source G.target).left =
      (pullback.fst bc.groupoid.source bc.groupoid.target).left ≫ bc.arrowsProjection :=
  bc.composableProjection_fst

/-- The projection to the scheme of composable arrows, against the second projection. -/
@[reassoc]
theorem composableProjection_comp_snd (bc : AffineInvariantBaseChange G C₁) :
    bc.composableProjection ≫ (pullback.snd G.source G.target).left =
      (pullback.snd bc.groupoid.source bc.groupoid.target).left ≫ bc.arrowsProjection :=
  bc.composableProjection_snd

/-- The projection to the arrow scheme of `G` is compatible with composition. -/
@[reassoc]
theorem comp_left_comp_arrowsProjection (bc : AffineInvariantBaseChange G C₁) :
    bc.groupoid.comp.left ≫ bc.arrowsProjection = bc.composableProjection ≫ G.comp.left :=
  bc.projection_comp

/-- The source map of a base change is the base change of the source map of `G`. -/
theorem source_isPullback (bc : AffineInvariantBaseChange G C₁) :
    IsPullback bc.arrowsProjection bc.groupoid.source.left G.source.left
      bc.objectsProjection := by
  refine IsPullback.of_bot (v₂₁ := bc.groupoid.objects.hom)
    (v₂₂ := objectsToInvariantSpectrum G) ?_ bc.projection_source bc.objects_isPullback
  rw [Over.w bc.groupoid.source]
  exact bc.arrows_isPullback

/-- The target map of a base change is the base change of the target map of `G`. -/
theorem target_isPullback [IsAffine G.objects.left] [IsAffine G.arrows.left]
    (bc : AffineInvariantBaseChange G C₁) :
    IsPullback bc.arrowsProjection bc.groupoid.target.left G.target.left
      bc.objectsProjection := by
  refine IsPullback.of_bot (v₂₁ := bc.groupoid.objects.hom)
    (v₂₂ := objectsToInvariantSpectrum G) ?_ bc.projection_target bc.objects_isPullback
  rw [Over.w bc.groupoid.target, ← source_comp_objectsToInvariantSpectrum G]
  exact bc.arrows_isPullback

end AffineInvariantBaseChange

/-! ### The induced morphism of base changes -/

section Induced

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} {C₁ C'₁ : Type u} [CommRing C₁]
  [CommRing C'₁] [Algebra (invariantRing G) C₁] [Algebra (invariantRing G') C'₁]
  (F : GroupoidScheme.Hom G' G) (ψ : C₁ →+* C'₁)
  (hψ : ψ.comp (algebraMap (invariantRing G) C₁) =
    (algebraMap (invariantRing G') C'₁).comp (invariantRingMap F))
  (bc : AffineInvariantBaseChange G C₁) (bc' : AffineInvariantBaseChange G' C'₁)

include hψ in
/-- The square formed by the two extensions of the invariant rings and the map on invariant
rings commutes after applying `Spec`. -/
theorem invariantSpectrumMap_comp_specMap_invariantRingMap :
    invariantSpectrumMap G' C'₁ ≫ Spec.map (CommRingCat.ofHom (invariantRingMap F)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ invariantSpectrumMap G C₁ := by
  change Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G') C'₁)) ≫
      Spec.map (CommRingCat.ofHom (invariantRingMap F)) =
    Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G) C₁))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]

/-- The map on object schemes of the morphism induced by `F` between the two base changes: the
lift of the map on object schemes of `F` against the cartesian object square of the base change
of `G`. -/
def baseChangeMapObjects : bc'.groupoid.objects.left ⟶ bc.groupoid.objects.left :=
  bc.objects_isPullback.lift (bc'.objectsProjection ≫ F.mapObjects.left)
    (bc'.groupoid.objects.hom ≫ Spec.map (CommRingCat.ofHom ψ)) (by
      rw [Category.assoc, mapObjects_comp_objectsToInvariantSpectrum F, ← Category.assoc,
        bc'.objects_isPullback.w, Category.assoc,
        invariantSpectrumMap_comp_specMap_invariantRingMap F ψ hψ, ← Category.assoc])

/-- The map on arrow schemes of the morphism induced by `F` between the two base changes: the
lift of the map on arrow schemes of `F` against the cartesian arrow square of the base change
of `G`. -/
def baseChangeMapArrows : bc'.groupoid.arrows.left ⟶ bc.groupoid.arrows.left :=
  bc.arrows_isPullback.lift (bc'.arrowsProjection ≫ F.mapArrows.left)
    (bc'.groupoid.arrows.hom ≫ Spec.map (CommRingCat.ofHom ψ)) (by
      rw [Category.assoc, mapArrows_comp_arrowsToInvariantSpectrum F, ← Category.assoc,
        bc'.arrows_isPullback.w, Category.assoc,
        invariantSpectrumMap_comp_specMap_invariantRingMap F ψ hψ, ← Category.assoc])

/-- **The map on object schemes is `F` over the two projections.** -/
@[reassoc]
theorem baseChangeMapObjects_comp_objectsProjection :
    baseChangeMapObjects F ψ hψ bc bc' ≫ bc.objectsProjection =
      bc'.objectsProjection ≫ F.mapObjects.left :=
  bc.objects_isPullback.lift_fst _ _ _

/-- **The map on object schemes lies over the map of new base rings.** -/
@[reassoc]
theorem baseChangeMapObjects_comp_hom :
    baseChangeMapObjects F ψ hψ bc bc' ≫ bc.groupoid.objects.hom =
      bc'.groupoid.objects.hom ≫ Spec.map (CommRingCat.ofHom ψ) :=
  bc.objects_isPullback.lift_snd _ _ _

/-- **The map on arrow schemes is `F` over the two projections.** -/
@[reassoc]
theorem baseChangeMapArrows_comp_arrowsProjection :
    baseChangeMapArrows F ψ hψ bc bc' ≫ bc.arrowsProjection =
      bc'.arrowsProjection ≫ F.mapArrows.left :=
  bc.arrows_isPullback.lift_fst _ _ _

/-- **The map on arrow schemes lies over the map of new base rings.** -/
@[reassoc]
theorem baseChangeMapArrows_comp_hom :
    baseChangeMapArrows F ψ hψ bc bc' ≫ bc.groupoid.arrows.hom =
      bc'.groupoid.arrows.hom ≫ Spec.map (CommRingCat.ofHom ψ) :=
  bc.arrows_isPullback.lift_snd _ _ _

/-- A map of base changes commutes with a structure morphism `s' → s` of groupoid schemes as
soon as it does after the cartesian projections and over the new base rings. -/
private theorem comp_eq_of_cartesian_lift {X X' Y Y' GX GX' GY GY' B B' C : Scheme.{u}}
    {pY : Y ⟶ GY} {hY : Y ⟶ B} {gY : GY ⟶ C} {c : B ⟶ C}
    (hpb : IsPullback pY hY gY c) (mX : X' ⟶ X) (mY : Y' ⟶ Y) (s : X ⟶ Y) (s' : X' ⟶ Y')
    {pX : X ⟶ GX} {pX' : X' ⟶ GX'} {pY' : Y' ⟶ GY'} {hX : X ⟶ B} {hX' : X' ⟶ B'}
    {hY' : Y' ⟶ B'} {fX : GX' ⟶ GX} {fY : GY' ⟶ GY} {gs : GX ⟶ GY} {gs' : GX' ⟶ GY'}
    {ψ : B' ⟶ B} (h₁ : mX ≫ pX = pX' ≫ fX) (h₂ : mX ≫ hX = hX' ≫ ψ)
    (h₃ : mY ≫ pY = pY' ≫ fY) (h₄ : mY ≫ hY = hY' ≫ ψ) (h₅ : pX ≫ gs = s ≫ pY)
    (h₆ : pX' ≫ gs' = s' ≫ pY') (h₇ : fX ≫ gs = gs' ≫ fY) (h₈ : s ≫ hY = hX)
    (h₉ : s' ≫ hY' = hX') : mX ≫ s = s' ≫ mY := by
  refine hpb.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, ← h₅, reassoc_of% h₁, h₇, h₃,
      ← Category.assoc s', ← h₆, Category.assoc]
  · rw [Category.assoc, Category.assoc, h₈, h₄, h₂, ← h₉, Category.assoc]

/-- The two maps are compatible with the source maps of the two base changes. -/
theorem baseChangeMapArrows_comp_source :
    baseChangeMapArrows F ψ hψ bc bc' ≫ bc.groupoid.source.left =
      bc'.groupoid.source.left ≫ baseChangeMapObjects F ψ hψ bc bc' :=
  comp_eq_of_cartesian_lift bc.objects_isPullback _ _ _ _
    (baseChangeMapArrows_comp_arrowsProjection F ψ hψ bc bc')
    (baseChangeMapArrows_comp_hom F ψ hψ bc bc')
    (baseChangeMapObjects_comp_objectsProjection F ψ hψ bc bc')
    (baseChangeMapObjects_comp_hom F ψ hψ bc bc') bc.projection_source bc'.projection_source
    F.map_source_left (Over.w bc.groupoid.source) (Over.w bc'.groupoid.source)

/-- The two maps are compatible with the target maps of the two base changes. -/
theorem baseChangeMapArrows_comp_target :
    baseChangeMapArrows F ψ hψ bc bc' ≫ bc.groupoid.target.left =
      bc'.groupoid.target.left ≫ baseChangeMapObjects F ψ hψ bc bc' :=
  comp_eq_of_cartesian_lift bc.objects_isPullback _ _ _ _
    (baseChangeMapArrows_comp_arrowsProjection F ψ hψ bc bc')
    (baseChangeMapArrows_comp_hom F ψ hψ bc bc')
    (baseChangeMapObjects_comp_objectsProjection F ψ hψ bc bc')
    (baseChangeMapObjects_comp_hom F ψ hψ bc bc') bc.projection_target bc'.projection_target
    F.map_target_left (Over.w bc.groupoid.target) (Over.w bc'.groupoid.target)

/-- The two maps are compatible with the identity sections of the two base changes. -/
theorem baseChangeMapObjects_comp_identity :
    baseChangeMapObjects F ψ hψ bc bc' ≫ bc.groupoid.identity.left =
      bc'.groupoid.identity.left ≫ baseChangeMapArrows F ψ hψ bc bc' :=
  comp_eq_of_cartesian_lift bc.arrows_isPullback _ _ _ _
    (baseChangeMapObjects_comp_objectsProjection F ψ hψ bc bc')
    (baseChangeMapObjects_comp_hom F ψ hψ bc bc')
    (baseChangeMapArrows_comp_arrowsProjection F ψ hψ bc bc')
    (baseChangeMapArrows_comp_hom F ψ hψ bc bc') bc.projection_identity bc'.projection_identity
    (map_identity_left F) (Over.w bc.groupoid.identity) (Over.w bc'.groupoid.identity)

/-- The map on object schemes of the induced morphism, as a morphism over the new base ring of
`G`. -/
def baseChangeHomObjects :
    (Over.map (Spec.map (CommRingCat.ofHom ψ))).obj bc'.groupoid.objects ⟶
      bc.groupoid.objects :=
  Over.homMk (baseChangeMapObjects F ψ hψ bc bc')
    (baseChangeMapObjects_comp_hom F ψ hψ bc bc')

/-- The map on arrow schemes of the induced morphism, as a morphism over the new base ring of
`G`. -/
def baseChangeHomArrows :
    (Over.map (Spec.map (CommRingCat.ofHom ψ))).obj bc'.groupoid.arrows ⟶
      bc.groupoid.arrows :=
  Over.homMk (baseChangeMapArrows F ψ hψ bc bc')
    (baseChangeMapArrows_comp_hom F ψ hψ bc bc')

/-- The underlying morphism of schemes of `baseChangeHomObjects` is `baseChangeMapObjects`. -/
@[simp]
theorem baseChangeHomObjects_left :
    (baseChangeHomObjects F ψ hψ bc bc').left = baseChangeMapObjects F ψ hψ bc bc' := rfl

/-- The underlying morphism of schemes of `baseChangeHomArrows` is `baseChangeMapArrows`. -/
@[simp]
theorem baseChangeHomArrows_left :
    (baseChangeHomArrows F ψ hψ bc bc').left = baseChangeMapArrows F ψ hψ bc bc' := rfl

/-- The two lifts into the schemes of composable arrows agree over the scheme of composable
arrows of `G`. The two arrows `p` and `q` are the generalized arrows of the base change of `G'`
underlying `a` and `b`. -/
theorem lift_comp_composableProjection {T : Over (Spec (.of C₁))}
    (a b : T ⟶ (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).arrows)
    (w' : (a ≫ baseChangeHomArrows F ψ hψ bc bc') ≫ bc.groupoid.source =
      (b ≫ baseChangeHomArrows F ψ hψ bc bc') ≫ bc.groupoid.target)
    {base : T.left ⟶ Spec (.of C'₁)}
    (p q : (Over.mk base : Over (Spec (.of C'₁))) ⟶ bc'.groupoid.arrows)
    (hpa : (a ≫ baseChangeHomArrows F ψ hψ bc bc').left =
      p.left ≫ baseChangeMapArrows F ψ hψ bc bc')
    (hqb : (b ≫ baseChangeHomArrows F ψ hψ bc bc').left =
      q.left ≫ baseChangeMapArrows F ψ hψ bc bc')
    (wpq : p ≫ bc'.groupoid.source = q ≫ bc'.groupoid.target) :
    (pullback.lift (a ≫ baseChangeHomArrows F ψ hψ bc bc')
        (b ≫ baseChangeHomArrows F ψ hψ bc bc') w').left ≫ bc.composableProjection =
      (pullback.lift p q wpq).left ≫ bc'.composableProjection ≫ F.mapComposable.left := by
  refine (overFibreProduct_isPullback G.source G.target).hom_ext ?_ ?_
  · simp only [Category.assoc, AffineInvariantBaseChange.composableProjection_comp_fst,
      AffineInvariantBaseChange.composableProjection_comp_fst_assoc,
      mapComposable_comp_fst_left, overFibreProduct_lift_left_comp_fst_assoc,
      hpa, baseChangeMapArrows_comp_arrowsProjection]
  · simp only [Category.assoc, AffineInvariantBaseChange.composableProjection_comp_snd,
      AffineInvariantBaseChange.composableProjection_comp_snd_assoc,
      mapComposable_comp_snd_left, overFibreProduct_lift_left_comp_snd_assoc,
      hqb, baseChangeMapArrows_comp_arrowsProjection]

/-- **Compatibility of the induced morphism with composition of generalized arrows.** -/
theorem baseChangeHomArrows_compose (T : Over (Spec (.of C₁)))
    (a b : T ⟶ (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).arrows)
    (w : a ≫ (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).source =
      b ≫ (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).target)
    (w' : (a ≫ baseChangeHomArrows F ψ hψ bc bc') ≫ bc.groupoid.source =
      (b ≫ baseChangeHomArrows F ψ hψ bc bc') ≫ bc.groupoid.target) :
    (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).compose a b w ≫
        baseChangeHomArrows F ψ hψ bc bc' =
      bc.groupoid.compose (a ≫ baseChangeHomArrows F ψ hψ bc bc')
        (b ≫ baseChangeHomArrows F ψ hψ bc bc') w' := by
  have hb : (a.left ≫ bc'.groupoid.arrows.hom) ≫ Spec.map (CommRingCat.ofHom ψ) = T.hom :=
    Stacks.Groupoids.GroupoidScheme.arrows_base _ _ a
  have hbb : b.left ≫ bc'.groupoid.arrows.hom = a.left ≫ bc'.groupoid.arrows.hom :=
    Stacks.Groupoids.GroupoidScheme.arrows_base_of_source _ _ a b w
  have wpq : overDescend (Spec.map (CommRingCat.ofHom ψ)) a rfl ≫ bc'.groupoid.source =
      overDescend (Spec.map (CommRingCat.ofHom ψ)) b hbb ≫ bc'.groupoid.target := by
    have hw := congrArg Over.Hom.left w
    exact Over.OverMorphism.ext hw
  have hL : ((bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).compose a b w).left =
      (pullback.lift (overDescend (Spec.map (CommRingCat.ofHom ψ)) a rfl)
        (overDescend (Spec.map (CommRingCat.ofHom ψ)) b hbb) wpq).left ≫
        bc'.groupoid.comp.left := by
    rw [Stacks.Groupoids.GroupoidScheme.pushforward_compose
      (Spec.map (CommRingCat.ofHom ψ)) bc'.groupoid hb a b _ _ rfl rfl wpq w]
    rfl
  have key := lift_comp_composableProjection F ψ hψ bc bc' a b w'
    (overDescend (Spec.map (CommRingCat.ofHom ψ)) a rfl)
    (overDescend (Spec.map (CommRingCat.ofHom ψ)) b hbb) rfl rfl wpq
  refine Over.OverMorphism.ext (bc.arrows_isPullback.hom_ext ?_ ?_)
  · have hlhs : ((bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).compose a b w ≫
          baseChangeHomArrows F ψ hψ bc bc').left ≫ bc.arrowsProjection =
        ((pullback.lift (overDescend (Spec.map (CommRingCat.ofHom ψ)) a rfl)
            (overDescend (Spec.map (CommRingCat.ofHom ψ)) b hbb) wpq).left ≫
          bc'.composableProjection ≫ F.mapComposable.left) ≫ G.comp.left := by
      have hcl : ((bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).compose a b w ≫
            baseChangeHomArrows F ψ hψ bc bc').left =
          ((pullback.lift (overDescend (Spec.map (CommRingCat.ofHom ψ)) a rfl)
            (overDescend (Spec.map (CommRingCat.ofHom ψ)) b hbb) wpq).left ≫
            bc'.groupoid.comp.left) ≫ baseChangeMapArrows F ψ hψ bc bc' := by
        rw [← hL]
        exact rfl
      rw [hcl]
      simp only [Category.assoc,
        baseChangeMapArrows_comp_arrowsProjection,
        AffineInvariantBaseChange.comp_left_comp_arrowsProjection_assoc,
        comp_left_comp_mapArrows_left]
    have hrhs : (bc.groupoid.compose (a ≫ baseChangeHomArrows F ψ hψ bc bc')
            (b ≫ baseChangeHomArrows F ψ hψ bc bc') w').left ≫ bc.arrowsProjection =
        ((pullback.lift (a ≫ baseChangeHomArrows F ψ hψ bc bc')
            (b ≫ baseChangeHomArrows F ψ hψ bc bc') w').left ≫
          bc.composableProjection) ≫ G.comp.left := by
      have hr : (bc.groupoid.compose (a ≫ baseChangeHomArrows F ψ hψ bc bc')
            (b ≫ baseChangeHomArrows F ψ hψ bc bc') w').left =
          (pullback.lift (a ≫ baseChangeHomArrows F ψ hψ bc bc')
            (b ≫ baseChangeHomArrows F ψ hψ bc bc') w').left ≫ bc.groupoid.comp.left := rfl
      rw [hr, Category.assoc,
        AffineInvariantBaseChange.comp_left_comp_arrowsProjection, ← Category.assoc]
    rw [hlhs, hrhs, key]
  · exact (Over.w _).trans (Over.w _).symm

/-- **The morphism of base changes induced by a morphism of affine groupoid schemes**, from the
base change of `G'`, regarded as a groupoid scheme over the new base ring of `G` through
`Spec ψ`, to the base change of `G`. -/
def baseChangeHom :
    GroupoidScheme.Hom (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ)))
      bc.groupoid where
  mapObjects := baseChangeHomObjects F ψ hψ bc bc'
  mapArrows := baseChangeHomArrows F ψ hψ bc bc'
  map_source := Over.OverMorphism.ext (baseChangeMapArrows_comp_source F ψ hψ bc bc')
  map_target := Over.OverMorphism.ext (baseChangeMapArrows_comp_target F ψ hψ bc bc')
  map_identity := Over.OverMorphism.ext (baseChangeMapObjects_comp_identity F ψ hψ bc bc')
  map_comp := baseChangeHomArrows_compose F ψ hψ bc bc'

/-- **The map on object schemes of the induced morphism is the lift of the map on object
schemes of `F`.** -/
@[simp]
theorem baseChangeHom_mapObjects_left :
    (baseChangeHom F ψ hψ bc bc').mapObjects.left = baseChangeMapObjects F ψ hψ bc bc' := rfl

/-- **The map on arrow schemes of the induced morphism is the lift of the map on arrow schemes
of `F`.** -/
@[simp]
theorem baseChangeHom_mapArrows_left :
    (baseChangeHom F ψ hψ bc bc').mapArrows.left = baseChangeMapArrows F ψ hψ bc bc' := rfl

/-- The induced morphism is compatible with the projections to the object scheme of `G`. -/
@[reassoc]
theorem baseChangeHom_mapObjects_left_comp_objectsProjection :
    (baseChangeHom F ψ hψ bc bc').mapObjects.left ≫ bc.objectsProjection =
      bc'.objectsProjection ≫ F.mapObjects.left :=
  baseChangeMapObjects_comp_objectsProjection F ψ hψ bc bc'

/-- The induced morphism is compatible with the projections to the arrow scheme of `G`. -/
@[reassoc]
theorem baseChangeHom_mapArrows_left_comp_arrowsProjection :
    (baseChangeHom F ψ hψ bc bc').mapArrows.left ≫ bc.arrowsProjection =
      bc'.arrowsProjection ≫ F.mapArrows.left :=
  baseChangeMapArrows_comp_arrowsProjection F ψ hψ bc bc'

/-! ### The cartesian squares of the induced morphism -/

/-- **The source square of the induced morphism is cartesian** as soon as the source square of
`F` is. -/
theorem source_isPullback_baseChangeHom
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left) :
    IsPullback (baseChangeMapArrows F ψ hψ bc bc') bc'.groupoid.source.left
      bc.groupoid.source.left (baseChangeMapObjects F ψ hψ bc bc') := by
  refine IsPullback.of_right (h₁₂ := bc.arrowsProjection) (h₂₂ := bc.objectsProjection) ?_
    (baseChangeMapArrows_comp_source F ψ hψ bc bc') bc.source_isPullback
  rw [baseChangeMapArrows_comp_arrowsProjection, baseChangeMapObjects_comp_objectsProjection]
  exact bc'.source_isPullback.paste_horiz hsource

/-- **The target square of the induced morphism is cartesian** as soon as the target square of
`F` is. -/
theorem target_isPullback_baseChangeHom [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left) :
    IsPullback (baseChangeMapArrows F ψ hψ bc bc') bc'.groupoid.target.left
      bc.groupoid.target.left (baseChangeMapObjects F ψ hψ bc bc') := by
  refine IsPullback.of_right (h₁₂ := bc.arrowsProjection) (h₂₂ := bc.objectsProjection) ?_
    (baseChangeMapArrows_comp_target F ψ hψ bc bc') bc.target_isPullback
  rw [baseChangeMapArrows_comp_arrowsProjection, baseChangeMapObjects_comp_objectsProjection]
  exact bc'.target_isPullback.paste_horiz htarget

/-- **The square formed by the map on object schemes of the induced morphism, the map on object
schemes of `F` and the two projections is cartesian**, as soon as the new base ring of `G'`
presents `Spec C'₁` as the fibre product `Spec C' ×_{Spec C} Spec C₁`. -/
theorem isPullback_baseChangeMapObjects
    (hbase : IsPullback (invariantSpectrumMap G' C'₁) (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (invariantRingMap F))) (invariantSpectrumMap G C₁)) :
    IsPullback bc'.objectsProjection (baseChangeMapObjects F ψ hψ bc bc')
      F.mapObjects.left bc.objectsProjection := by
  refine IsPullback.of_bot (v₂₁ := bc.groupoid.objects.hom)
    (v₂₂ := objectsToInvariantSpectrum G) ?_
    (baseChangeMapObjects_comp_objectsProjection F ψ hψ bc bc').symm bc.objects_isPullback
  rw [baseChangeMapObjects_comp_hom, mapObjects_comp_objectsToInvariantSpectrum F]
  exact bc'.objects_isPullback.paste_vert hbase

/-- **The map on object schemes of the induced morphism is étale as soon as the map on object
schemes of `F` is**, as soon as the new base ring of `G'` presents `Spec C'₁` as the fibre
product `Spec C' ×_{Spec C} Spec C₁`. -/
theorem etale_baseChangeMapObjects [Etale F.mapObjects.left]
    (hbase : IsPullback (invariantSpectrumMap G' C'₁) (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (invariantRingMap F))) (invariantSpectrumMap G C₁)) :
    Etale (baseChangeMapObjects F ψ hψ bc bc') :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
    (isPullback_baseChangeMapObjects F ψ hψ bc bc' hbase) inferInstance

/-! ### The induced map on invariant rings -/

/-- Pullback of global functions from the new base ring of `G` along the map on object schemes
of the induced morphism is pullback along the given map of new base rings. -/
theorem invInvariantSpectrum_appTop_baseChangeMapObjects :
    (Scheme.ΓSpecIso (.of C₁)).inv ≫ bc.groupoid.objects.hom.appTop ≫
        (baseChangeMapObjects F ψ hψ bc bc').appTop =
      CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (.of C'₁)).inv ≫
        bc'.groupoid.objects.hom.appTop := by
  rw [← Scheme.Hom.comp_appTop, baseChangeMapObjects_comp_hom, Scheme.Hom.comp_appTop,
    Scheme.ΓSpecIso_inv_naturality_assoc]

/-- **The map on invariant rings induced by the new morphism is the given map of new base
rings.** Read through the canonical maps of Tag 03BK from the two new base rings to the two
rings of invariant functions, `invariantRingMap` of the induced morphism is `ψ`. -/
theorem invariantRingMap_baseChangeHom_canonicalMap (x : C₁) :
    (invariantRingMap (baseChangeHom F ψ hψ bc bc')
        (bc.canonicalMapToInvariantFunctions x)).1 =
      (bc'.canonicalMapToInvariantFunctions (ψ x)).1 :=
  congrArg (fun k => k.hom x) (invInvariantSpectrum_appTop_baseChangeMapObjects F ψ hψ bc bc')

/-- The source square of `AlgebraicGeometry.GroupoidScheme.baseChangeHom` is cartesian as soon
as the source square of `F` is. -/
theorem source_isPullback_mapArrows_baseChangeHom
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left) :
    IsPullback (baseChangeHom F ψ hψ bc bc').mapArrows.left
      (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).source.left
      bc.groupoid.source.left (baseChangeHom F ψ hψ bc bc').mapObjects.left :=
  source_isPullback_baseChangeHom F ψ hψ bc bc' hsource

/-- The target square of `AlgebraicGeometry.GroupoidScheme.baseChangeHom` is cartesian as soon
as the target square of `F` is. -/
theorem target_isPullback_mapArrows_baseChangeHom [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left) :
    IsPullback (baseChangeHom F ψ hψ bc bc').mapArrows.left
      (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ))).target.left
      bc.groupoid.target.left (baseChangeHom F ψ hψ bc bc').mapObjects.left :=
  target_isPullback_baseChangeHom F ψ hψ bc bc' htarget

/-- **The map on invariant rings of the induced morphism, transported along the two bijections
of Tag 03BK, is the given map of new base rings.** -/
theorem invariantRingMap_baseChangeHom_comp_ofBijective
    (hbc : Function.Bijective bc.canonicalMapToInvariantFunctions)
    (hbc' : Function.Bijective bc'.canonicalMapToInvariantFunctions) :
    (invariantRingMap (baseChangeHom F ψ hψ bc bc')).comp
        (RingEquiv.ofBijective _ hbc).toRingHom =
      (RingEquiv.ofBijective _ hbc').toRingHom.comp ψ :=
  RingHom.ext fun x =>
    Subtype.ext (invariantRingMap_baseChangeHom_canonicalMap F ψ hψ bc bc' x)

end Induced

/-! ### The tensor product as the new base ring of `G'` -/

section Tensor

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  (C₁ : Type u) [CommRing C₁] [Algebra (invariantRing G) C₁]

/-- The invariant ring of `G'`, as an algebra over the invariant ring of `G` through the map on
invariant rings induced by `F`. -/
@[instance_reducible]
def invariantRingAlgebra : Algebra (invariantRing G) (invariantRing G') :=
  (invariantRingMap F).toAlgebra

/-- The specified extension of the invariant ring of `G'` determined by an extension `C₁` of
the invariant ring of `G`: the tensor product `C' ⊗[C] C₁`. -/
abbrev tensorBaseRing : Type u :=
  letI := invariantRingAlgebra F
  invariantRing G' ⊗[invariantRing G] C₁

/-- The base change of the map on invariant rings: the right inclusion of `C₁` into
`C' ⊗[C] C₁`. -/
def tensorBaseRingMap : C₁ →+* tensorBaseRing F C₁ :=
  letI := invariantRingAlgebra F
  (Algebra.TensorProduct.includeRight :
    C₁ →ₐ[invariantRing G] tensorBaseRing F C₁).toRingHom

/-- The square of the four rings `C`, `C₁`, `C'` and `C' ⊗[C] C₁` commutes. -/
theorem tensorBaseRing_compatible :
    letI := invariantRingAlgebra F
    (tensorBaseRingMap F C₁).comp (algebraMap (invariantRing G) C₁) =
      (algebraMap (invariantRing G') (tensorBaseRing F C₁)).comp (invariantRingMap F) := by
  let : Algebra (invariantRing G) (invariantRing G') := invariantRingAlgebra F
  have h := Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    (R := invariantRing G) (A := invariantRing G') (B := C₁)
  exact RingHom.ext fun c => (DFunLike.congr_fun h c).symm

/-- **The spectrum of `C' ⊗[C] C₁` is the fibre product `Spec C' ×_{Spec C} Spec C₁`.** -/
theorem isPullback_invariantSpectrumMap_tensorBaseRing :
    letI := invariantRingAlgebra F
    IsPullback (invariantSpectrumMap G' (tensorBaseRing F C₁))
      (Spec.map (CommRingCat.ofHom (tensorBaseRingMap F C₁)))
      (Spec.map (CommRingCat.ofHom (invariantRingMap F)))
      (invariantSpectrumMap G C₁) :=
  let := invariantRingAlgebra F
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (invariantRing G) (invariantRing G') C₁)

variable (bc : AffineInvariantBaseChange G C₁)
  (bc' : AffineInvariantBaseChange G' (tensorBaseRing F C₁))

/-- **The square formed by the map on object schemes of the induced morphism, the map on object
schemes of `F` and the two projections is cartesian**, when the new base ring of `G'` is the
tensor product `C' ⊗[C] C₁`. -/
theorem isPullback_baseChangeMapObjects_tensorBaseRing :
    IsPullback bc'.objectsProjection
      (baseChangeMapObjects F (tensorBaseRingMap F C₁) (tensorBaseRing_compatible F C₁) bc bc')
      F.mapObjects.left bc.objectsProjection :=
  isPullback_baseChangeMapObjects F _ _ bc bc'
    (isPullback_invariantSpectrumMap_tensorBaseRing F C₁)

/-- **The map on object schemes of the induced morphism is étale as soon as the map on object
schemes of `F` is**, when the new base ring of `G'` is the tensor product `C' ⊗[C] C₁`. -/
theorem etale_baseChangeMapObjects_tensorBaseRing [Etale F.mapObjects.left] :
    Etale (baseChangeMapObjects F (tensorBaseRingMap F C₁)
      (tensorBaseRing_compatible F C₁) bc bc') :=
  etale_baseChangeMapObjects F _ _ bc bc'
    (isPullback_invariantSpectrumMap_tensorBaseRing F C₁)

end Tensor

end AlgebraicGeometry.GroupoidScheme

end

end
