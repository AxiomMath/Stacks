module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.TransitionIsBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallAffineEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChangeIdComp

/-! # The coherence of the comparison of Stacks 0EYL's transitions with étale base change

The comparison

`transitionIso a : system.u a ⋙ levelEtale i ≅ levelEtale j ⋙ smallEtaleBaseChange (stageMap a)`

identifies each transition functor of the site system of Stacks 0EYL with base change of small
étale sites. We prove its coherence: its behaviour on an identity arrow and on a composite.

## Main definitions

* `AlgebraicGeometry.smallEtaleBaseChange_factoredIdIso` — base change along a morphism only
  *provably* an identity is the identity functor.
* `stageIdIso` — base change along the transition morphism of an identity arrow is the identity
  functor, by `stageMap_id`.
* `stageCompIso` — base change along the transition morphisms of `a` and `b` composes to base
  change along the transition morphism of `a ≫ b`, by `stageMap_comp`.
* `AlgebraicGeometry.smallAffineEtaleBaseChange_factoredIdIso` and
  `..._factoredCompIso` — the same two transports on the small *affine* étale site, each pinned by
  the fully faithful inclusion into the small étale site
  (`..._factoredIdIso_hom_app_inclusion`, `..._factoredCompIso_hom_app_inclusion`).

## Main results

* `transitionIso_id_hom_app` — **the identity law.** At an identity arrow the comparison is, read
  across `stageIdIso`, the canonical identification coming from
  `InverseSystemOfFiniteSites.id_map`.
* `transitionIso_comp_hom_app` — **the composition law.** At a composite `a ≫ b` the comparison
  is the comparison at `a`, followed by the base change along `stageMap a` of the comparison at
  `b`, read across `stageCompIso` and the canonical identification coming from
  `InverseSystemOfFiniteSites.comp`.
* `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_unit` and
  `..._hom_app_assoc` — **the unit and associativity coherence of Stacks 021J's comparison of
  successive small étale base changes**, in the factored spelling.

## Implementation notes

A morphism of the small étale site of `X_i` into a base change is determined by its composite
with the projection onto the object based from (`AlgebraicGeometry.SmallEtale.hom_ext_fst`), the
remaining projection being the structure morphism; that composite is computed on both sides by
`componentIso_hom_fst`. So the two laws reduce to the fields `transitionFst_id` and
`transitionFst_comp` of `AffineEtaleSiteColimit`.

The comparison functors are transported along `stageMap_id` and `stageMap_comp`, because
`stageMap (𝟙 i)` and `stageMap (a ≫ b)` are only provably, not syntactically, an identity and a
composite. Each transport is built by substituting the equation away, so no `eqToHom` enters the
geometry.

No affineness and no limit cone is used: the fibre products live in the bounded category of any
big étale site and the squares are data of `AffineEtaleSiteColimit`.

## References

* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Over

end CategoryTheory.Over

namespace AlgebraicGeometry

universe w

variable (B : AlgebraicGeometry.BigEtaleSite.{w})

/-- **Base change along a morphism that is provably an identity is the identity functor.** This is
`AlgebraicGeometry.smallEtaleBaseChangeId` transported along a proof `g = 𝟙 S`. -/
def smallEtaleBaseChange_factoredIdIso {S : B.Scheme} (g : S ⟶ S) (hg : g = 𝟙 S) :
    smallEtaleBaseChange B g ≅ 𝟭 (SmallEtale B S.obj S.property) :=
  eqToIso (congrArg (fun k => smallEtaleBaseChange B k) hg) ≪≫ smallEtaleBaseChangeId B

/-- On underlying objects, the identity comparison is the projection of the fibre product with the
identity onto the object based from. This is the identity-arrow companion of
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst`. -/
theorem smallEtaleBaseChange_factoredIdIso_hom_app_left {S : B.Scheme} (g : S ⟶ S) (hg : g = 𝟙 S)
    (Z : SmallEtale B S.obj S.property) :
    ((smallEtaleBaseChange_factoredIdIso B g hg).hom.app Z).hom.left =
      Limits.pullback.fst Z.obj.hom g := by
  subst hg
  have h0 : smallEtaleBaseChange_factoredIdIso B (𝟙 S) rfl = smallEtaleBaseChangeId B := by
    simp [smallEtaleBaseChange_factoredIdIso]
  have h : (SmallEtale.inclusion B S.obj S.property).map
      ((smallEtaleBaseChangeId B).hom.app Z) =
      (Over.pullbackId (X := S)).hom.app Z.obj := by
    rw [smallEtaleBaseChangeId, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    change (Over.pullbackId (X := S)).hom.app Z.obj ≫ 𝟙 _ ≫ 𝟙 _ =
      (Over.pullbackId (X := S)).hom.app Z.obj
    rw [Category.id_comp, Category.comp_id]
  rw [h0]
  exact (congrArg Over.Hom.left h).trans (Over.pullbackId_hom_app_left Z.obj)

/-- A functor preserves an equality of two-step composites. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Y' Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, h, F.map_comp]

/-- **The projection onto the object based from is natural for base change.** The base change of a
morphism of the small étale site of `S`, followed by the projection, is the projection followed by
the morphism. -/
theorem toScheme_map_smallEtaleBaseChange_map_fst {S T : B.Scheme} (h : T ⟶ S)
    {X Y : SmallEtale B S.obj S.property} (φ : X ⟶ Y) :
    (SmallEtale.toScheme B T.obj T.property).map ((smallEtaleBaseChange B h).map φ) ≫
        B.inclusion.map (Limits.pullback.fst Y.obj.hom h) =
      B.inclusion.map (Limits.pullback.fst X.obj.hom h) ≫
        (SmallEtale.toScheme B S.obj S.property).map φ := by
  have key : ((smallEtaleBaseChange B h).map φ).hom.left ≫ Limits.pullback.fst Y.obj.hom h =
      Limits.pullback.fst X.obj.hom h ≫ φ.hom.left :=
    Limits.pullback.lift_fst _ _ _
  exact map_comp_eq_map_comp B.inclusion key

/-! ### The pseudofunctor coherence of small étale base change

The two laws below are the unit and associativity coherence of Stacks 021J's comparison
`AlgebraicGeometry.smallEtaleBaseChange_compIso`, in the *factored* spelling, where each composite
morphism is presented by a term only provably equal to the composite.
-/

/-- The computation of the projection of the factored composition comparison, read in schemes.
This is `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_hom_app_fst` with the fully
faithful inclusion of the bounded category applied to it. -/
theorem toScheme_map_smallEtaleBaseChange_factoredCompIso_hom_app_fst (X Y Z : B.Scheme)
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg)
    (W : SmallEtale B Z.obj Z.property) :
    (SmallEtale.toScheme B X.obj X.property).map
          ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app W) ≫
        B.inclusion.map (Limits.pullback.fst W.obj.hom fg) =
      B.inclusion.map (Limits.pullback.fst ((smallEtaleBaseChange B g).obj W).obj.hom f) ≫
        B.inclusion.map (Limits.pullback.fst W.obj.hom g) :=
  map_comp_eq_map_comp B.inclusion
    (smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z f g fg hfg W)

/-- **The unit law of small étale base change.** Base change along a morphism `g` that is provably
an identity contributes nothing to the composition comparison: at a factorisation `g ≫ f = f` the
factored composition comparison is the factored identity comparison, base changed along `f`. -/
theorem smallEtaleBaseChange_factoredCompIso_hom_app_unit {S T : B.Scheme} (g : T ⟶ T)
    (hg : g = 𝟙 T) (f : T ⟶ S) (hgf : g ≫ f = f) (W : SmallEtale B S.obj S.property) :
    (smallEtaleBaseChange_factoredCompIso B T T S g f f hgf).hom.app W =
      (smallEtaleBaseChange_factoredIdIso B g hg).hom.app
        ((smallEtaleBaseChange B f).obj W) := by
  refine AlgebraicGeometry.SmallEtale.hom_ext_fst f _ _ ?_
  have key : ((smallEtaleBaseChange_factoredCompIso B T T S g f f hgf).hom.app W).hom.left ≫
        Limits.pullback.fst W.obj.hom f =
      ((smallEtaleBaseChange_factoredIdIso B g hg).hom.app
          ((smallEtaleBaseChange B f).obj W)).hom.left ≫ Limits.pullback.fst W.obj.hom f :=
    (smallEtaleBaseChange_factoredCompIso_hom_app_fst B T T S g f f hgf W).trans
      (congrArg (fun z => z ≫ Limits.pullback.fst W.obj.hom f)
        (smallEtaleBaseChange_factoredIdIso_hom_app_left B g hg
          ((smallEtaleBaseChange B f).obj W)).symm)
  exact map_comp_eq_map_comp B.inclusion key

/-- **The associativity law of small étale base change.** For `f : X ⟶ Y`, `g : Y ⟶ Z` and
`h : Z ⟶ U` with chosen composites, the two ways of comparing the threefold composite of base
changes with base change along `f ≫ g ≫ h` agree. -/
theorem smallEtaleBaseChange_factoredCompIso_hom_app_assoc {X Y Z U : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ U) (fg : X ⟶ Z) (hfg : f ≫ g = fg) (gh : Y ⟶ U)
    (hgh : g ≫ h = gh) (fgh : X ⟶ U) (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh)
    (W : SmallEtale B U.obj U.property) :
    (smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app
          ((smallEtaleBaseChange B h).obj W) ≫
        (smallEtaleBaseChange_factoredCompIso B X Z U fg h fgh hfgh).hom.app W =
      (smallEtaleBaseChange B f).map
          ((smallEtaleBaseChange_factoredCompIso B Y Z U g h gh hgh).hom.app W) ≫
        (smallEtaleBaseChange_factoredCompIso B X Y U f gh fgh hfgh').hom.app W := by
  refine AlgebraicGeometry.SmallEtale.hom_ext_fst fgh _ _ ?_
  have hβ := toScheme_map_smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Z U fg h fgh hfgh W
  have hε := toScheme_map_smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y U f gh fgh hfgh' W
  have hγ := toScheme_map_smallEtaleBaseChange_factoredCompIso_hom_app_fst B Y Z U g h gh hgh W
  have hA2 := (Category.assoc _ _ _).symm.trans
    (((toScheme_map_smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z f g fg hfg
          ((smallEtaleBaseChange B h).obj W)) =≫
        B.inclusion.map (Limits.pullback.fst W.obj.hom h)).trans (Category.assoc _ _ _))
  have hnat2 := (Category.assoc _ _ _).symm.trans
    (((toScheme_map_smallEtaleBaseChange_map_fst B f
          ((smallEtaleBaseChange_factoredCompIso B Y Z U g h gh hgh).hom.app W)) =≫
        B.inclusion.map (Limits.pullback.fst W.obj.hom gh)).trans (Category.assoc _ _ _))
  have e1 := (((SmallEtale.toScheme B X.obj X.property).map_comp
        ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app
          ((smallEtaleBaseChange B h).obj W))
        ((smallEtaleBaseChange_factoredCompIso B X Z U fg h fgh hfgh).hom.app W)) =≫
      B.inclusion.map (Limits.pullback.fst W.obj.hom fgh)).trans (Category.assoc _ _ _)
  have f1 := (((SmallEtale.toScheme B X.obj X.property).map_comp
        ((smallEtaleBaseChange B f).map
          ((smallEtaleBaseChange_factoredCompIso B Y Z U g h gh hgh).hom.app W))
        ((smallEtaleBaseChange_factoredCompIso B X Y U f gh fgh hfgh').hom.app W)) =≫
      B.inclusion.map (Limits.pullback.fst W.obj.hom fgh)).trans (Category.assoc _ _ _)
  have hL := e1.trans ((_ ≫= hβ).trans hA2)
  have hR := f1.trans ((_ ≫= hε).trans (hnat2.trans (_ ≫= hγ)))
  exact hL.trans hR.symm

/-! ### The same transports on the small affine étale site

`AlgebraicGeometry.smallAffineEtaleBaseChangeId` and
`AlgebraicGeometry.smallAffineEtaleBaseChangeComp` are the small affine étale pseudofunctor data,
each obtained from its small étale counterpart by cancelling the fully faithful inclusion. The
transports below are their versions for a morphism only *provably* an identity or a composite,
and each is pinned by the inclusion: its image is the corresponding small étale transport.
-/

section AffineTransports

variable {S T U : B.Scheme} [IsAffine S.obj] [IsAffine T.obj] [IsAffine U.obj]

/-- Small affine étale base change is small étale base change, on morphisms, read through the
inclusion. This is `AlgebraicGeometry.smallAffineEtaleBaseChange_comp_inclusion` evaluated at a
morphism. -/
theorem inclusion_map_smallAffineEtaleBaseChange_map (f : T ⟶ S)
    {X Y : SmallAffineEtale B S.obj S.property} (φ : X ⟶ Y) :
    (SmallAffineEtale.inclusion B T.obj T.property).map
        ((smallAffineEtaleBaseChange B f).map φ) =
      (smallEtaleBaseChange B f).map
        ((SmallAffineEtale.inclusion B S.obj S.property).map φ) :=
  rfl

/-- **Base change along a morphism of affine schemes that is provably an identity is the identity
functor**, on small affine étale categories. The small affine étale companion of
`AlgebraicGeometry.smallEtaleBaseChange_factoredIdIso`, built from it by cancelling the fully
faithful inclusion into the small étale category. -/
def smallAffineEtaleBaseChange_factoredIdIso (g : S ⟶ S) (hg : g = 𝟙 S) :
    smallAffineEtaleBaseChange B g ≅ 𝟭 (SmallAffineEtale B S.obj S.property) :=
  Functor.fullyFaithfulCancelRight (SmallAffineEtale.inclusion B S.obj S.property)
    (Functor.isoWhiskerLeft (SmallAffineEtale.inclusion B S.obj S.property)
        (smallEtaleBaseChange_factoredIdIso B g hg) ≪≫
      (SmallAffineEtale.inclusion B S.obj S.property).rightUnitor ≪≫
      (SmallAffineEtale.inclusion B S.obj S.property).leftUnitor.symm)

/-- The identity-arrow transport of small affine étale base change *is* the small étale one, read
through the fully faithful inclusion. -/
@[simp]
theorem smallAffineEtaleBaseChange_factoredIdIso_hom_app_inclusion (g : S ⟶ S) (hg : g = 𝟙 S)
    (Y : SmallAffineEtale B S.obj S.property) :
    (SmallAffineEtale.inclusion B S.obj S.property).map
        ((smallAffineEtaleBaseChange_factoredIdIso B g hg).hom.app Y) =
      (smallEtaleBaseChange_factoredIdIso B g hg).hom.app
        ((SmallAffineEtale.inclusion B S.obj S.property).obj Y) := by
  rw [smallAffineEtaleBaseChange_factoredIdIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  change (smallEtaleBaseChange_factoredIdIso B g hg).hom.app
      ((SmallAffineEtale.inclusion B S.obj S.property).obj Y) ≫ 𝟙 _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

/-- **Base change along a morphism of affine schemes that is provably a composite is the composite
of the base changes**, on small affine étale categories. The small affine étale companion of
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`, built from it by cancelling the fully
faithful inclusion into the small étale category. -/
def smallAffineEtaleBaseChange_factoredCompIso (f : U ⟶ T) (g : T ⟶ S) (fg : U ⟶ S)
    (hfg : f ≫ g = fg) :
    smallAffineEtaleBaseChange B g ⋙ smallAffineEtaleBaseChange B f ≅
      smallAffineEtaleBaseChange B fg :=
  Functor.fullyFaithfulCancelRight (SmallAffineEtale.inclusion B U.obj U.property)
    (Functor.isoWhiskerLeft (SmallAffineEtale.inclusion B S.obj S.property)
      (smallEtaleBaseChange_factoredCompIso B U T S f g fg hfg))

/-- The composite transport of small affine étale base change *is* the small étale one, read
through the fully faithful inclusion. -/
@[simp]
theorem smallAffineEtaleBaseChange_factoredCompIso_hom_app_inclusion (f : U ⟶ T) (g : T ⟶ S)
    (fg : U ⟶ S) (hfg : f ≫ g = fg) (Y : SmallAffineEtale B S.obj S.property) :
    (SmallAffineEtale.inclusion B U.obj U.property).map
        ((smallAffineEtaleBaseChange_factoredCompIso B f g fg hfg).hom.app Y) =
      (smallEtaleBaseChange_factoredCompIso B U T S f g fg hfg).hom.app
        ((SmallAffineEtale.inclusion B S.obj S.property).obj Y) :=
  Functor.map_preimage _ _

end AffineTransports

end AlgebraicGeometry

universe v u

namespace Stacks.EtaleCohomology.TransitionBaseChange

variable {I : Type v} [Preorder I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX)

/-! ### The identity law -/

/-- **Base change along the transition morphism of an identity arrow is the identity functor.** -/
def stageIdIso (i : E.system.I) :
    AlgebraicGeometry.smallEtaleBaseChange B (stageMap E (𝟙 i)) ≅
      𝟭 (AlgebraicGeometry.SmallEtale B (D.obj (stage E i)) (hD (stage E i))) :=
  AlgebraicGeometry.smallEtaleBaseChange_factoredIdIso B (stageMap E (𝟙 i)) (stageMap_id E i)

/-- The identity comparison of the stages, read in schemes, is the projection of the fibre product
onto the object based from. -/
theorem toS_map_stageIdIso_hom_app (i : E.system.I) (Y : E.system.C i) :
    (toS E i).map ((stageIdIso E i).hom.app ((levelEtale E i).obj Y)) = fstProj E (𝟙 i) Y :=
  congrArg B.inclusion.map
    (AlgebraicGeometry.smallEtaleBaseChange_factoredIdIso_hom_app_left B (stageMap E (𝟙 i))
      (stageMap_id E i) ((levelEtale E i).obj Y))

/-- **The identity law of the comparison of Stacks 0EYL's transitions with étale base change.** At
an identity arrow of the index category the comparison is, read across `stageIdIso`, the canonical
identification of `(system.u (𝟙 i)).obj Y` with `Y` coming from
`InverseSystemOfFiniteSites.id_map`. -/
theorem transitionIso_id_hom_app (i : E.system.I) (Y : E.system.C i) :
    (transitionIso E (𝟙 i)).hom.app Y ≫ (stageIdIso E i).hom.app ((levelEtale E i).obj Y) =
      (levelEtale E i).map (eqToHom (Functor.congr_obj (E.system.id_map i) Y)) := by
  refine (AlgebraicGeometry.SmallEtale.inclusion B (D.obj (stage E i))
    (hD (stage E i))).map_injective (Over.OverMorphism.ext (B.inclusion.map_injective ?_))
  change (toS E i).map ((transitionIso E (𝟙 i)).hom.app Y ≫
      (stageIdIso E i).hom.app ((levelEtale E i).obj Y)) =
    (toS E i).map ((levelEtale E i).map (eqToHom (Functor.congr_obj (E.system.id_map i) Y)))
  rw [Functor.map_comp, toS_map_stageIdIso_hom_app, transitionIso_hom_app,
    componentIso_hom_fst, E.transitionFst_id i Y]
  rfl

/-! ### The composition law -/

/-- **Base change along the transition morphisms of `a` and `b` composes to base change along the
transition morphism of `a ≫ b`**, by `stageMap_comp`. -/
def stageCompIso {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k) :
    AlgebraicGeometry.smallEtaleBaseChange B (stageMap E b) ⋙
        AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a) ≅
      AlgebraicGeometry.smallEtaleBaseChange B (stageMap E (a ≫ b)) :=
  AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso B _ _ _ (stageMap E a) (stageMap E b)
    (stageMap E (a ≫ b)) (stageMap_comp E a b).symm

/-- The composition comparison of the stages, read in schemes, carries the projection of the
one-step fibre product to the composite of the two projections of the iterated one. -/
theorem toS_map_stageCompIso_hom_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (Y : E.system.C k) :
    (toS E i).map ((stageCompIso E a b).hom.app ((levelEtale E k).obj Y)) ≫
        B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom
          (stageMap E (a ≫ b))) =
      B.inclusion.map (Limits.pullback.fst
          ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E b)).obj
            ((levelEtale E k).obj Y)).obj.hom (stageMap E a)) ≫
        B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom (stageMap E b)) :=
  AlgebraicGeometry.toScheme_map_smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ _ _
    (stageMap E a) (stageMap E b) (stageMap E (a ≫ b)) (stageMap_comp E a b).symm
    ((levelEtale E k).obj Y)

/-- **The two projection computations of the composition law, bundled.** The base change along
`stageMap a` of the comparison at `b`, followed by the composition comparison and the projection
of the one-step fibre product, is the projection onto the level `j` followed by the chosen
projection of the transition at `b`. -/
theorem toS_map_transitionIso_baseChange_fst {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (Y : E.system.C k) :
    (toS E i).map ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
          ((transitionIso E b).hom.app Y)) ≫
        (toS E i).map ((stageCompIso E a b).hom.app ((levelEtale E k).obj Y)) ≫
          B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom
            (stageMap E (a ≫ b))) =
      B.inclusion.map (Limits.pullback.fst
          ((levelEtale E j).obj ((E.system.u b).obj Y)).obj.hom (stageMap E a)) ≫
        (E.transitionFst b).app Y := by
  have hbase : (toS E i).map ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
          ((transitionIso E b).hom.app Y)) ≫
        B.inclusion.map (Limits.pullback.fst
          ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E b)).obj
            ((levelEtale E k).obj Y)).obj.hom (stageMap E a)) =
      B.inclusion.map (Limits.pullback.fst
          ((levelEtale E j).obj ((E.system.u b).obj Y)).obj.hom (stageMap E a)) ≫
        (toS E j).map ((transitionIso E b).hom.app Y) :=
    AlgebraicGeometry.toScheme_map_smallEtaleBaseChange_map_fst B (stageMap E a)
      ((transitionIso E b).hom.app Y)
  have hfst : (toS E j).map ((transitionIso E b).hom.app Y) ≫
      B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom (stageMap E b)) =
      (E.transitionFst b).app Y :=
    componentIso_hom_fst E b Y
  have hcomp : (toS E i).map ((stageCompIso E a b).hom.app ((levelEtale E k).obj Y)) ≫
      B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom
            (stageMap E (a ≫ b))) =
      B.inclusion.map (Limits.pullback.fst
          ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E b)).obj
            ((levelEtale E k).obj Y)).obj.hom (stageMap E a)) ≫
        B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom (stageMap E b)) :=
    toS_map_stageCompIso_hom_app E a b Y
  exact (((toS E i).map ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
          ((transitionIso E b).hom.app Y))) ≫= hcomp).trans
    (((Category.assoc _ _ _).symm.trans (hbase =≫ (B.inclusion.map (Limits.pullback.fst
            ((levelEtale E k).obj Y).obj.hom (stageMap E b))))).trans
      ((Category.assoc _ _ _).trans ((B.inclusion.map (Limits.pullback.fst
          ((levelEtale E j).obj ((E.system.u b).obj Y)).obj.hom (stageMap E a))) ≫= hfst)))

/-- **The whole projection computation of the composition law.** The composite of the comparison
at `a`, the base change of the comparison at `b`, the composition comparison and the projection of
the one-step fibre product is the composite of the two chosen projections of the system. -/
theorem toS_map_transitionIso_comp_fst {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (Y : E.system.C k) :
    (toS E i).map ((transitionIso E a).hom.app ((E.system.u b).obj Y)) ≫
        (toS E i).map ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
            ((transitionIso E b).hom.app Y)) ≫
          (toS E i).map ((stageCompIso E a b).hom.app ((levelEtale E k).obj Y)) ≫
            B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom
              (stageMap E (a ≫ b))) =
      (E.transitionFst a).app ((E.system.u b).obj Y) ≫ (E.transitionFst b).app Y := by
  have hA : (toS E i).map ((transitionIso E a).hom.app ((E.system.u b).obj Y)) ≫
      B.inclusion.map (Limits.pullback.fst
          ((levelEtale E j).obj ((E.system.u b).obj Y)).obj.hom (stageMap E a)) =
      (E.transitionFst a).app ((E.system.u b).obj Y) :=
    componentIso_hom_fst E a ((E.system.u b).obj Y)
  exact (((toS E i).map ((transitionIso E a).hom.app ((E.system.u b).obj Y))) ≫=
      toS_map_transitionIso_baseChange_fst E a b Y).trans
    ((Category.assoc _ _ _).symm.trans (hA =≫ ((E.transitionFst b).app Y)))

/-- **The composition law of the comparison of Stacks 0EYL's transitions with étale base change.**
At a composite `a ≫ b` the comparison is the comparison at `a`, followed by the base change along
`stageMap a` of the comparison at `b`, read across `stageCompIso` and the canonical identification
of `(system.u (a ≫ b)).obj Y` with `(system.u a).obj ((system.u b).obj Y)` coming from
`InverseSystemOfFiniteSites.comp`. -/
theorem transitionIso_comp_hom_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (Y : E.system.C k) :
    (transitionIso E (a ≫ b)).hom.app Y =
      (levelEtale E i).map (eqToHom (Functor.congr_obj (E.system.comp a b) Y)) ≫
        (transitionIso E a).hom.app ((E.system.u b).obj Y) ≫
          (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
              ((transitionIso E b).hom.app Y) ≫
            (stageCompIso E a b).hom.app ((levelEtale E k).obj Y) := by
  refine hom_ext_fst E (a ≫ b) _ _ ?_
  have hL : (toS E i).map ((transitionIso E (a ≫ b)).hom.app Y) ≫
      B.inclusion.map (Limits.pullback.fst ((levelEtale E k).obj Y).obj.hom
        (stageMap E (a ≫ b))) = (E.transitionFst (a ≫ b)).app Y :=
    componentIso_hom_fst E (a ≫ b) Y
  rw [hL, E.transitionFst_comp a b Y]
  simp only [Functor.map_comp, Category.assoc]
  rw [toS_map_transitionIso_comp_fst]
  rfl

end Stacks.EtaleCohomology.TransitionBaseChange

end
