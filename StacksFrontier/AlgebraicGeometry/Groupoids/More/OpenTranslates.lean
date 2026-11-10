module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointsOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Translation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksCore.Tactic.StacksAttribute

/-!
# Open translates in a groupoid scheme over a field

For a groupoid scheme whose object scheme is the spectrum of a field `k`, composing an arbitrary
family of arrows with the arrows in an open subset of the arrow scheme has open image.  The
argument restricts the groupoid twice — first to `Spec k` along the given identification, then
along an algebraically closed extension `k'` chosen so that the arrow under consideration lifts
to a point whose source and target are `k'`-rational — and translates the open subset by that
lifted point.  Translation is an automorphism of the restricted arrow scheme, and the canonical
map from the restricted arrow scheme down to the original one is surjective and open, so the
image of the translate is an open neighbourhood of the point in question inside the image of
the composition.

## Main results

* `AlgebraicGeometry.isOpen_image_comp_of_isOpen` states that the image of the indicated
  composition is open.

## Implementation notes

The family `Z ⟶ R` is written in the over category of `S`: any scheme morphism to `R` equips
its domain with the uniquely determined map to `S`.  The pullback of `Z ⟶ R` with
`R ×_U R ⟶ R` is canonically `Z ×_{s,U,t} R`; restricting its second arrow to `W` gives
`Z ×_{s,U,t} W`.  The map whose image occurs in the result is composition.

Two points of a fibre product with the same projections agree as soon as the residue field of
one projection surjects onto the tensor product of residue fields; that is the content of
`pullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso`, which is what identifies the point
produced by the translation with the point produced by the universal property.

## References

* [Stacks Project, Tag 0B7V](https://stacks.math.columbia.edu/tag/0B7V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The canonical map on arrows out of a realization of a restriction factors through the
identification of its arrow scheme with the canonical one. -/
private lemma restrictionHom_mapArrows_left_eq {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (H : GroupoidScheme.Restriction G g) :
    H.hom.mapArrows.left =
      eqToHom (congrArg Over.left H.arrows_eq) ≫ (restrictionArrowsToArrows G g).left := by
  simpa only [Over.comp_left, Over.eqToHom_left] using
    congrArg (fun q : H.groupoid.arrows ⟶ G.arrows => q.left) H.mapArrows_eq

/-- The canonical map on arrows out of a realization of a restriction is an open map, because
it factors the canonical map out of the chosen iterated fibre product through an
isomorphism. -/
private lemma restrictionHom_arrows_isOpenMap {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (k k' : Type u) [Field k] [Field k']
    (e : G.objects.left ≅ Spec (.of k)) (e' : U'.left ≅ Spec (.of k'))
    (H : GroupoidScheme.Restriction G g) :
    IsOpenMap H.hom.mapArrows.left := by
  have hraw : IsOpenMap (restrictionArrowsToArrows G g).left := by
    have : UniversallyOpen (restrictionArrowsToArrows G g).left := by
      simpa [restrictionDiagramMorphisms] using
        universallyOpen_restrictionDiagramMorphisms G g k k' e e' (11 : Fin 12)
    exact Scheme.Hom.isOpenMap _
  rw [restrictionHom_mapArrows_left_eq]
  change IsOpenMap (fun x => (restrictionArrowsToArrows G g).left.base
    ((eqToHom (congrArg Over.left H.arrows_eq)).base x))
  exact hraw.comp (Scheme.Hom.homeomorph (eqToHom (congrArg Over.left H.arrows_eq))).isOpenMap

/-- The canonical map on arrows out of a realization of a restriction is surjective. -/
private lemma restrictionHom_arrows_surjective {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (k k' : Type u) [Field k] [Field k']
    (e : G.objects.left ≅ Spec (.of k)) (e' : U'.left ≅ Spec (.of k'))
    (H : GroupoidScheme.Restriction G g) :
    Surjective H.hom.mapArrows.left := by
  have : Surjective (restrictionArrowsToArrows G g).left := by
    simpa [restrictionDiagramMorphisms] using
      surjective_restrictionDiagramMorphisms G g k k' e e' (11 : Fin 12)
  rw [restrictionHom_mapArrows_left_eq]
  infer_instance

/-- The canonical map on arrows out of a realization of a restriction, on points. -/
private lemma restrictionHom_mapArrows_apply {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (H : GroupoidScheme.Restriction G g)
    (x : H.groupoid.arrows.left) :
    H.hom.mapArrows.left.base x =
      (restrictionArrowsToArrows G g).left.base
        ((eqToHom (congrArg Over.left H.arrows_eq)) x) := by
  rw [restrictionHom_mapArrows_left_eq]
  simp

/-- A composite of morphisms of `Over S` with open underlying maps is an open map. -/
private lemma overComp_isOpenMap {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsOpenMap f.left) (hg : IsOpenMap g.left) :
    IsOpenMap (f ≫ g).left := by
  rw [Over.comp_left]
  change IsOpenMap (fun x => g.left.base (f.left.base x))
  exact hg.comp hf

/-- A composite of morphisms of `Over S` with surjective underlying maps is surjective. -/
private lemma overComp_surjective {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f.left] [Surjective g.left] :
    Surjective (f ≫ g).left := by
  rw [Over.comp_left]
  infer_instance

/-- When the first leg of a fibre product induces an isomorphism of residue fields at a triplet,
the spectrum of the tensor product of residue fields has a single point. -/
private lemma pullbackTensorSpec_subsingleton
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (T : Scheme.Pullback.Triplet f g)
    (hres : IsIso (f.residueFieldMap T.x)) : Subsingleton (Spec T.tensor) := by
  have : IsIso (pushout.inr
      ((Z.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((Z.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) := inferInstance
  let hSpecIso : Spec T.tensor ≅ Spec (CommRingCat.of (Y.residueField T.y)) :=
    Scheme.Spec.mapIso (asIso (pushout.inr
      ((Z.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((Z.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))).op
  have : Subsingleton (Spec (CommRingCat.of (Y.residueField T.y))) := by
    have : Subsingleton (PrimeSpectrum (Y.residueField T.y)) := inferInstance
    infer_instance
  exact hSpecIso.hom.homeomorph.subsingleton

/-- Two points of a fibre product with the same projections agree, provided the first leg
induces an isomorphism of residue fields at their common first projection. -/
private lemma pullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p q : ↑(pullback f g))
    (hfst : (pullback.fst f g).base p = (pullback.fst f g).base q)
    (hsnd : (pullback.snd f g).base p = (pullback.snd f g).base q)
    (hres : IsIso (f.residueFieldMap ((pullback.fst f g).base p))) : p = q := by
  classical
  apply Scheme.Pullback.carrierEquiv.injective
  refine Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨Scheme.Pullback.Triplet.ext hfst hsnd, ?_⟩
  have hres' : IsIso (f.residueFieldMap (Scheme.Pullback.Triplet.ofPoint q).x) := by
    change IsIso (f.residueFieldMap ((pullback.fst f g).base q))
    rwa [← hfst]
  exact (pullbackTensorSpec_subsingleton f g _ hres').elim _ _

/-- A morphism that is an open immersion, followed by one inducing an isomorphism of residue
fields at a point, followed by an open immersion, induces an isomorphism of residue fields. -/
private lemma residueFieldMap_isIso_of_eq_comp {X X' Y' Y : Scheme.{u}}
    (a : X ⟶ X') (b : X' ⟶ Y') (c : Y' ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion c]
    (φ : X ⟶ Y) (hφ : φ = a ≫ b ≫ c) (x : X) (hx : IsIso (b.residueFieldMap (a x))) :
    IsIso (φ.residueFieldMap x) := by
  subst hφ
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
  have hcb : IsIso (c.residueFieldMap (b (a x)) ≫ b.residueFieldMap (a x)) :=
    @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hx
  exact @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ hcb inferInstance

/-- Invertibility of the residue-field map of the source or target transfers from the canonical
arrow scheme of a restriction to any realization of it. -/
private lemma restriction_residueFieldMap_isIso {S : Scheme.{u}}
    {G : GroupoidScheme S} {U' : Over S} {g : U' ⟶ G.objects}
    (H : GroupoidScheme.Restriction G g)
    (σ : H.groupoid.arrows ⟶ H.groupoid.objects) (σ' : restrictionArrows G g ⟶ U')
    (hσ : σ = eqToHom H.arrows_eq ≫ σ' ≫ eqToHom H.objects_eq.symm)
    (x : H.groupoid.arrows.left)
    (hx : IsIso (σ'.left.residueFieldMap ((eqToHom (congrArg Over.left H.arrows_eq)) x))) :
    IsIso (σ.left.residueFieldMap x) :=
  residueFieldMap_isIso_of_eq_comp (eqToHom (congrArg Over.left H.arrows_eq)) σ'.left
    (eqToHom (congrArg Over.left H.objects_eq).symm) _
    (by simpa only [Over.comp_left, Over.eqToHom_left] using
      congrArg (fun q : H.groupoid.arrows ⟶ H.groupoid.objects => q.left) hσ) x hx

/-- Two points of the legs of a cospan in `Over S` with the same image lift to a point of the
pullback. -/
lemma exists_preimage_overPullback {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : X.left) (y : Y.left) (h : f.left.base x = g.left.base y) :
    ∃ t : (pullback f g).left, (pullback.fst f g).left.base t = x ∧
      (pullback.snd f g).left.base t = y := by
  obtain ⟨t, ht₁, ht₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f.left) (g := g.left) x y h
  refine ⟨(PreservesPullback.iso (Over.forget S) f g).inv.base t, ?_, ?_⟩
  · have heq := congrArg (fun m => m.base t) (PreservesPullback.iso_inv_fst (Over.forget S) f g)
    simpa [Scheme.Hom.comp_apply] using heq.trans ht₁
  · have heq := congrArg (fun m => m.base t) (PreservesPullback.iso_inv_snd (Over.forget S) f g)
    simpa [Scheme.Hom.comp_apply] using heq.trans ht₂

/-- Two points of the legs of a cospan in `Over S` with the same image are the images of the
closed point of a single `Over S`-scheme with commuting maps to the legs. -/
private lemma exists_overSpec_point_of_eq {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Z)
    (g : Y ⟶ Z) (x : X.left) (y : Y.left) (h : f.left.base x = g.left.base y) :
    ∃ (T : Over S) (a : T ⟶ X) (b : T ⟶ Y) (t : T.left),
      a ≫ f = b ≫ g ∧ a.left.base t = x ∧ b.left.base t = y := by
  obtain ⟨pt, hx, hy⟩ := exists_preimage_overPullback f g x y h
  let spec := (pullback f g).left.fromSpecResidueField pt
  let ι : Over.mk (spec ≫ (pullback f g).hom) ⟶ pullback f g := Over.homMk spec rfl
  have hpt : spec.base (IsLocalRing.closedPoint ((pullback f g).left.residueField pt)) = pt := by
    simpa [spec] using Scheme.fromSpecResidueField_apply pt (IsLocalRing.closedPoint _)
  refine ⟨_, ι ≫ pullback.fst f g, ι ≫ pullback.snd f g,
    IsLocalRing.closedPoint ((pullback f g).left.residueField pt),
    by simp [pullback.condition], ?_, ?_⟩
  · exact (congrArg (pullback.fst f g).left.base hpt).trans hx
  · exact (congrArg (pullback.snd f g).left.base hpt).trans hy

/-- Two points of a pullback in `Over S` with the same projections agree, provided the first leg
induces an isomorphism of residue fields at their common first projection. -/
private lemma overPullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso {S : Scheme.{u}}
    {X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z) (p q : (pullback f g).left)
    (hfst : (pullback.fst f g).left.base p = (pullback.fst f g).left.base q)
    (hsnd : (pullback.snd f g).left.base p = (pullback.snd f g).left.base q)
    (hres : IsIso (f.left.residueFieldMap ((pullback.fst f g).left.base p))) : p = q := by
  let e := PreservesPullback.iso (Over.forget S) f g
  have hf : ∀ t, (pullback.fst f.left g.left).base (e.hom.base t) =
      (pullback.fst f g).left.base t := fun t => by
    simpa [e, Scheme.Hom.comp_apply] using
      congrArg (fun m => m.base t) (PreservesPullback.iso_hom_fst (Over.forget S) f g)
  have hs : ∀ t, (pullback.snd f.left g.left).base (e.hom.base t) =
      (pullback.snd f g).left.base t := fun t => by
    simpa [e, Scheme.Hom.comp_apply] using
      congrArg (fun m => m.base t) (PreservesPullback.iso_hom_snd (Over.forget S) f g)
  apply (Scheme.Hom.homeomorph e.hom).injective
  exact pullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso f.left g.left
    (e.hom.base p) (e.hom.base q) ((hf p).trans (hfst.trans (hf q).symm))
    ((hs p).trans (hsnd.trans (hs q).symm)) (by rw [hf]; exact hres)

/-- An arrow of `G` over `T` whose source and target come from a restriction `H` of `G` lifts to an
arrow of `H` with the same source and target. -/
public lemma GroupoidScheme.Restriction.exists_arrow_lift {S : Scheme.{u}} {G : GroupoidScheme S}
    {U' : Over S} {g : U' ⟶ G.objects} (H : GroupoidScheme.Restriction G g) {T : Over S}
    (u a : T ⟶ H.groupoid.objects) (w : T ⟶ G.arrows)
    (hs : w ≫ G.source = u ≫ H.hom.mapObjects) (ht : w ≫ G.target = a ≫ H.hom.mapObjects) :
    ∃ h : T ⟶ H.groupoid.arrows, h ≫ H.groupoid.source = u ∧ h ≫ H.groupoid.target = a ∧
      h ≫ H.hom.mapArrows = w := by
  obtain ⟨hff⟩ := H.evaluation_fullyFaithful T
  let e : G.EvaluationHom (u ≫ H.hom.mapObjects) (a ≫ H.hom.mapObjects) :=
    { arrow := w, source_eq := hs, target_eq := ht }
  refine ⟨(hff.preimage e).arrow, (hff.preimage e).source_eq, (hff.preimage e).target_eq, ?_⟩
  simpa [GroupoidScheme.Hom.evaluation, e] using congrArg (·.arrow) (hff.map_preimage e)

/-- **Stacks Project, Tag 0B7V.** If the objects of a groupoid scheme form the spectrum
of a field, the image of the composition of a family of arrows with an open set of arrows
is open. -/
@[stacks 0B7V]
public theorem isOpen_image_comp_of_isOpen
    {S : Scheme.{u}} (G : GroupoidScheme S) (k : Type u) [Field k]
    (hobjects : G.objects.left ≅ Spec (.of k))
    (Z : Over S) (f : Z ⟶ G.arrows) (W : G.arrows.left.Opens) :
    let p := pullback.snd f (pullback.fst G.source G.target)
    IsOpen ((p ≫ G.comp).left.base ''
      {x | (p ≫ pullback.snd G.source G.target).left.base x ∈ W}) := by
  classical
  dsimp only
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  let structureMap : Spec (.of k) ⟶ S := hobjects.symm.hom ≫ G.objects.hom
  let g0 : Over.mk structureMap ⟶ G.objects :=
    Over.homMk hobjects.symm.hom (by dsimp [structureMap])
  let H0 := GroupoidScheme.restrict G g0
  let h0field : H0.groupoid.objects.left ≅ Spec (.of k) :=
    eqToIso (congrArg Over.left H0.objects_eq)
  have : Surjective H0.hom.mapArrows.left :=
    restrictionHom_arrows_surjective G g0 k k hobjects (Iso.refl _) H0
  let p := pullback.snd f (pullback.fst G.source G.target)
  let z := (pullback.fst f (pullback.fst G.source G.target)).left.base x
  let ξ := p.left.base x
  let r := f.left.base z
  let w := (pullback.snd G.source G.target).left.base ξ
  obtain ⟨r0, hr0⟩ := H0.hom.mapArrows.left.surjective r
  obtain ⟨k', hK, halg, i, hrest⟩ :=
    GroupoidScheme.exists_isIso_source_target_over_isAlgClosed
      structureMap H0.groupoid H0.objects_eq r0
  extract_lets g1 at hrest
  obtain ⟨rRaw, hrest'⟩ := hrest
  extract_lets rPointRaw at hrest'
  obtain ⟨hrRaw, hsrcRaw, htgtRaw⟩ := hrest'
  let H1 := GroupoidScheme.restrict H0.groupoid g1
  have h1eq : H1.groupoid.objects.left = Spec (.of k') :=
    (congrArg Over.left H1.objects_eq).trans rfl
  let h1field : H1.groupoid.objects.left ≅ Spec (.of k') := eqToIso h1eq
  have h1arrows : H1.groupoid.arrows.left =
      (restrictionArrows H0.groupoid g1).left := congrArg Over.left H1.arrows_eq
  let r1 : H1.groupoid.arrows.left :=
    (Scheme.Hom.homeomorph (eqToHom h1arrows)).symm rPointRaw
  have hr1raw : (eqToHom h1arrows) r1 = rPointRaw :=
    (Scheme.Hom.homeomorph (eqToHom h1arrows)).apply_symm_apply _
  have hsrc : IsIso (H1.groupoid.source.left.residueFieldMap r1) :=
    restriction_residueFieldMap_isIso H1 _ _ H1.source_eq r1 (by
      rw [hr1raw]
      simpa [g1] using hsrcRaw)
  have htgt : IsIso (H1.groupoid.target.left.residueFieldMap r1) :=
    restriction_residueFieldMap_isIso H1 _ _ H1.target_eq r1 (by
      rw [hr1raw]
      simpa [g1] using htgtRaw)
  let mapArrow : H1.groupoid.arrows ⟶ G.arrows :=
    H1.hom.mapArrows ≫ H0.hom.mapArrows
  have hOpen0 := restrictionHom_arrows_isOpenMap G g0 k k hobjects (Iso.refl _) H0
  have hOpen1 := restrictionHom_arrows_isOpenMap H0.groupoid g1 k k' h0field
    (Iso.refl _) H1
  have hOpen : IsOpenMap mapArrow.left :=
    overComp_isOpenMap H1.hom.mapArrows H0.hom.mapArrows hOpen1 hOpen0
  have : Surjective H1.hom.mapArrows.left :=
    restrictionHom_arrows_surjective H0.groupoid g1 k k' h0field
      (Iso.refl _) H1
  have hSurj : Surjective mapArrow.left :=
    overComp_surjective H1.hom.mapArrows H0.hom.mapArrows
  let W1 : Set H1.groupoid.arrows.left := mapArrow.left.base ⁻¹' (W : Set G.arrows.left)
  have hW1 : IsOpen W1 := W.2.preimage mapArrow.left.continuous
  let translate := GroupoidScheme.translationByPoint H1.groupoid k' h1eq r1
  have : IsIso translate :=
    GroupoidScheme.translationByPoint_isIso H1.groupoid k' h1eq r1
  have : IsIso translate.left := by
    change IsIso ((Over.forget S).map translate)
    infer_instance
  have hTranslateOpen : IsOpen (translate.left.base '' W1) := by
    have : UniversallyOpen translate.left := inferInstance
    exact translate.left.isOpenMap W1 hW1
  let F := GroupoidScheme.Hom.comp H1.hom H0.hom
  let pairMap := F.mapComposable
  have hr1map : H1.hom.mapArrows.left.base r1 = r0 := by
    rw [restrictionHom_mapArrows_apply, hr1raw, hrRaw]
  have hmapr : mapArrow.left.base r1 = r := by
    change H0.hom.mapArrows.left.base (H1.hom.mapArrows.left.base r1) = r
    rw [hr1map, hr0]
  have : Subsingleton H1.groupoid.objects.left := h1field.hom.homeomorph.subsingleton
  let a := GroupoidScheme.sourceNormalizedArrow H1.groupoid k' h1eq r1
  let ha := GroupoidScheme.sourceNormalizedArrow_source H1.groupoid k' h1eq r1
  let V := mapArrow.left.base '' (translate.left.base '' W1)
  have hVopen : IsOpen V := hOpen _ hTranslateOpen
  let q := H1.groupoid.target ≫ a
  have hq : q ≫ H1.groupoid.source = (𝟙 H1.groupoid.arrows) ≫ H1.groupoid.target := by
    simp [q, a, ha]
  let d : H1.groupoid.arrows ⟶ pullback H1.groupoid.source H1.groupoid.target :=
    pullback.lift q (𝟙 H1.groupoid.arrows) hq
  have hqmap : (q ≫ F.mapArrows) ≫ G.source =
      ((𝟙 H1.groupoid.arrows) ≫ F.mapArrows) ≫ G.target := by
    simp [F.map_source, F.map_target, reassoc_of% hq]
  have hcompMap := F.map_comp H1.groupoid.arrows q (𝟙 H1.groupoid.arrows) hq hqmap
  have hpairMapFst : pairMap ≫ pullback.fst G.source G.target =
      pullback.fst H1.groupoid.source H1.groupoid.target ≫ F.mapArrows := by
    dsimp [pairMap, GroupoidScheme.Hom.mapComposable, pullback.map]
    exact pullback.lift_fst _ _ _
  have hpairMapSnd : pairMap ≫ pullback.snd G.source G.target =
      pullback.snd H1.groupoid.source H1.groupoid.target ≫ F.mapArrows := by
    dsimp [pairMap, GroupoidScheme.Hom.mapComposable, pullback.map]
    exact pullback.lift_snd _ _ _
  have hdFst : d ≫ pullback.fst H1.groupoid.source H1.groupoid.target = q :=
    pullback.lift_fst _ _ _
  have hdSnd : d ≫ pullback.snd H1.groupoid.source H1.groupoid.target =
      𝟙 H1.groupoid.arrows := pullback.lift_snd _ _ _
  have hdPair : d ≫ pairMap =
      pullback.lift (q ≫ F.mapArrows) ((𝟙 H1.groupoid.arrows) ≫ F.mapArrows) hqmap := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp [hpairMapFst, reassoc_of% hdFst]
    · rw [pullback.lift_snd]
      simp [hpairMapSnd, reassoc_of% hdSnd]
  have htranslateMap : translate ≫ mapArrow = d ≫ pairMap ≫ G.comp := by
    change (H1.groupoid.compose q (𝟙 H1.groupoid.arrows) hq ≫ F.mapArrows) =
      d ≫ pairMap ≫ G.comp
    calc
      H1.groupoid.compose q (𝟙 H1.groupoid.arrows) hq ≫ F.mapArrows =
          G.compose (q ≫ F.mapArrows) ((𝟙 H1.groupoid.arrows) ≫ F.mapArrows) hqmap :=
        hcompMap
      _ = d ≫ pairMap ≫ G.comp := by
          rw [show G.compose (q ≫ F.mapArrows)
              ((𝟙 H1.groupoid.arrows) ≫ F.mapArrows) hqmap =
              pullback.lift (q ≫ F.mapArrows) ((𝟙 H1.groupoid.arrows) ≫ F.mapArrows)
                hqmap ≫ G.comp from rfl, ← hdPair]
          rfl
  have htargetA : ∀ w' : H1.groupoid.arrows.left,
      (H1.groupoid.target ≫ a).left.base w' = r1 := fun w' => by
    change a.left.base (H1.groupoid.target.left.base w') = r1
    rw [Subsingleton.elim (H1.groupoid.target.left.base w') (H1.groupoid.source.left r1)]
    exact GroupoidScheme.sourceNormalizedArrow_apply H1.groupoid k' h1eq r1
  have hdFirst : ∀ w' : H1.groupoid.arrows.left,
      (pullback.fst H1.groupoid.source H1.groupoid.target).left.base (d.left.base w') = r1 :=
    fun w' => by
      have hp := congrArg (fun m => m.base w') (congrArg Over.Hom.left hdFst)
      rw [Over.comp_left, Scheme.Hom.comp_apply] at hp
      exact hp.trans (htargetA w')
  have hdSecond : ∀ w' : H1.groupoid.arrows.left,
      (pullback.snd H1.groupoid.source H1.groupoid.target).left.base (d.left.base w') = w' :=
    fun w' => by
      have hp := congrArg (fun m => m.base w') (congrArg Over.Hom.left hdSnd)
      rw [Over.comp_left, Scheme.Hom.comp_apply] at hp
      simpa using hp
  have hVsub : V ⊆ (p ≫ G.comp).left.base ''
      {x | (p ≫ pullback.snd G.source G.target).left.base x ∈ W} := by
    rintro _ ⟨v', ⟨w', hw', rfl⟩, rfl⟩
    let pair0Pt := pairMap.left.base (d.left.base w')
    have hpair0First : (pullback.fst G.source G.target).left.base pair0Pt = r := by
      have hp := congrArg (fun m => m.base (d.left.base w'))
        (congrArg Over.Hom.left hpairMapFst)
      have hp' : (pullback.fst G.source G.target).left.base pair0Pt =
          (pullback.fst H1.groupoid.source H1.groupoid.target ≫ F.mapArrows).left.base
            (d.left.base w') := by
        simpa [pair0Pt, Over.comp_left, Scheme.Hom.comp_apply] using hp
      rw [hp', Over.comp_left, Scheme.Hom.comp_apply, hdFirst w']
      change mapArrow.left.base r1 = r
      exact hmapr
    obtain ⟨x', -, hx'pair⟩ := exists_preimage_overPullback f
      (pullback.fst G.source G.target) z pair0Pt (by rw [hpair0First])
    have hx'W : (pullback.snd G.source G.target).left.base
        ((pullback.snd f (pullback.fst G.source G.target)).left.base x') ∈ W := by
      have hsecond : (pullback.snd G.source G.target).left.base pair0Pt =
          mapArrow.left.base w' := by
        have hsnd := congrArg (fun m => m.base (d.left.base w'))
          (congrArg Over.Hom.left hpairMapSnd)
        calc
          (pullback.snd G.source G.target).left.base pair0Pt =
              F.mapArrows.left.base
                ((pullback.snd H1.groupoid.source H1.groupoid.target).left.base
                  (d.left.base w')) := by
            simpa [pair0Pt, Scheme.Hom.comp_apply] using hsnd
          _ = mapArrow.left.base w' := by rw [hdSecond w']; rfl
      rw [hx'pair, hsecond]
      exact hw'
    refine ⟨x', hx'W, ?_⟩
    have hcompPoint : (p ≫ G.comp).left.base x' =
        mapArrow.left.base (translate.left.base w') := by
      change G.comp.left.base
        ((pullback.snd f (pullback.fst G.source G.target)).left.base x') = _
      rw [hx'pair]
      change (d ≫ pairMap ≫ G.comp).left.base w' = _
      have h := congrArg (fun m : H1.groupoid.arrows ⟶ G.arrows => m.left.base w')
        htranslateMap
      simpa [Scheme.Hom.comp_apply, d] using h.symm
    rw [hcompPoint]
  have hyV : (p ≫ G.comp).left.base x ∈ V := by
    let qTarget := p ≫ pullback.fst G.source G.target
    have hxq : qTarget.left.base x = r := by
      have hcond := congrArg (fun m : pullback f (pullback.fst G.source G.target) ⟶ G.arrows =>
        m.left.base x) (pullback.condition (f := f)
          (g := pullback.fst G.source G.target))
      simpa [qTarget, r, ξ, p, z, Scheme.Hom.comp_apply] using hcond.symm
    have hqCompat : mapArrow.left.base r1 = qTarget.left.base x := by
      rw [hmapr, hxq]
    obtain ⟨T1, rT1, xT, t0, hfirst, hrT1point, hxTpoint⟩ :=
      exists_overSpec_point_of_eq mapArrow qTarget r1 x hqCompat
    let rT := rT1 ≫ mapArrow
    have hqPairCondition : (xT ≫ p ≫ pullback.fst G.source G.target) ≫ G.source =
        (xT ≫ p ≫ pullback.snd G.source G.target) ≫ G.target := by
      simpa only [Category.assoc] using
        congrArg (fun m => xT ≫ p ≫ m)
          (pullback.condition (f := G.source) (g := G.target))
    have hqCommon : rT ≫ G.source =
        xT ≫ p ≫ pullback.snd G.source G.target ≫ G.target :=
      (congrArg (· ≫ G.source) hfirst).trans hqPairCondition
    let wT := xT ≫ p ≫ pullback.snd G.source G.target
    have : Subsingleton G.objects.left := hobjects.hom.homeomorph.subsingleton
    let u0 : H1.groupoid.objects.left :=
      (Scheme.Hom.homeomorph (eqToHom h1eq)).symm (IsLocalRing.closedPoint k')
    have hObjPts : (F.mapObjects.left).base u0 = (wT ≫ G.source).left.base t0 :=
      Subsingleton.elim _ _
    obtain ⟨T2, uT, eT, t2, hq2Comm, -, heTpoint⟩ :=
      exists_overSpec_point_of_eq F.mapObjects (wT ≫ G.source) u0 t0 hObjPts
    let rT2 := eT ≫ rT1
    let xT2 := eT ≫ xT
    let wT2 := eT ≫ wT
    have hq2Target : wT2 ≫ G.target = rT2 ≫ H1.groupoid.source ≫ F.mapObjects := by
      calc
        wT2 ≫ G.target = eT ≫ wT ≫ G.target := rfl
        _ = eT ≫ rT ≫ G.source := by
          simpa [wT, Category.assoc] using congrArg (fun m => eT ≫ m) hqCommon.symm
        _ = rT2 ≫ H1.groupoid.source ≫ F.mapObjects := by
          calc
            eT ≫ rT ≫ G.source = eT ≫ rT1 ≫ (F.mapArrows ≫ G.source) := by
              simp [rT, mapArrow, F, GroupoidScheme.Hom.comp, Category.assoc]
            _ = eT ≫ rT1 ≫ (H1.groupoid.source ≫ F.mapObjects) := by
              rw [F.map_source]
            _ = rT2 ≫ H1.groupoid.source ≫ F.mapObjects := by
              simp [rT2, Category.assoc]
    let aT := rT2 ≫ H1.groupoid.source
    obtain ⟨h0, h0src, h0tgt, hh0⟩ := H0.exists_arrow_lift (uT ≫ H1.hom.mapObjects)
      (aT ≫ H1.hom.mapObjects) wT2
      (by simpa [wT2, F, GroupoidScheme.Hom.comp, Category.assoc] using hq2Comm.symm)
      (by simpa [aT, F, GroupoidScheme.Hom.comp, Category.assoc] using hq2Target)
    obtain ⟨h1, -, h1tgt, hh1⟩ := H1.exists_arrow_lift uT aT h0 h0src h0tgt
    have hhLiftArrow : h1 ≫ F.mapArrows = wT2 := by
      rw [← hh0, ← hh1]
      simp [F, GroupoidScheme.Hom.comp]
    let pairT : T2 ⟶ pullback H1.groupoid.source H1.groupoid.target :=
      pullback.lift rT2 h1 h1tgt.symm
    let w' := h1.left.base t2
    have hwTpoint : wT.left.base t0 = w := by
      change (pullback.snd G.source G.target).left.base (p.left.base (xT.left.base t0)) = w
      rw [hxTpoint]
    have hwT2point : wT2.left.base t2 = w := by
      change wT.left.base (eT.left.base t2) = w
      rwa [heTpoint]
    have hw' : w' ∈ W1 := by
      have hhw : mapArrow.left.base w' = w := by
        have hp := congrArg (fun m => m.left.base t2) hhLiftArrow
        change mapArrow.left.base w' = wT2.left.base t2 at hp
        rwa [hwT2point] at hp
      change mapArrow.left.base w' ∈ W
      rwa [hhw]
    change (p ≫ G.comp).left.base x ∈ mapArrow.left.base ''
      (translate.left.base '' W1)
    refine ⟨translate.left.base w', ⟨w', hw', rfl⟩, ?_⟩
    let pairTPt := pairT.left.base t2
    have hrT2point : rT2.left.base t2 = r1 := by
      change rT1.left.base (eT.left.base t2) = r1
      rwa [heTpoint]
    have hpairTfstHom :
        pairT ≫ pullback.fst H1.groupoid.source H1.groupoid.target = rT2 :=
      pullback.lift_fst _ _ _
    have hpairTsndHom :
        pairT ≫ pullback.snd H1.groupoid.source H1.groupoid.target = h1 :=
      pullback.lift_snd _ _ _
    have hpairTfst : (pullback.fst H1.groupoid.source H1.groupoid.target).left.base
        pairTPt = r1 :=
      (congrArg (fun m => m.left.base t2) hpairTfstHom).trans hrT2point
    have hpairTsnd : (pullback.snd H1.groupoid.source H1.groupoid.target).left.base
        pairTPt = w' :=
      congrArg (fun m => m.left.base t2) hpairTsndHom
    have hpairDEq : d.left.base w' = pairTPt :=
      overPullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso _ _ _ _
        ((hdFirst w').trans hpairTfst.symm) ((hdSecond w').trans hpairTsnd.symm)
        (by rwa [hdFirst w'])
    have hfirst2 : rT2 ≫ F.mapArrows = xT2 ≫ p ≫ pullback.fst G.source G.target := by
      calc
        rT2 ≫ F.mapArrows = eT ≫ (rT1 ≫ mapArrow) := by
          simp [rT2, F, GroupoidScheme.Hom.comp, mapArrow, Category.assoc]
        _ = eT ≫ (xT ≫ p ≫ pullback.fst G.source G.target) :=
          congrArg (eT ≫ ·) hfirst
        _ = xT2 ≫ p ≫ pullback.fst G.source G.target := rfl
    have hPairMapExact : pairT ≫ pairMap = xT2 ≫ p := by
      refine pullback.hom_ext ?_ ?_
      · calc
          pairT ≫ pairMap ≫ pullback.fst G.source G.target =
              pairT ≫ pullback.fst H1.groupoid.source H1.groupoid.target ≫
                F.mapArrows := by
            simpa only [Category.assoc] using congrArg (pairT ≫ ·) hpairMapFst
          _ = rT2 ≫ F.mapArrows :=
            congrArg (fun m => m ≫ F.mapArrows) hpairTfstHom
          _ = xT2 ≫ p ≫ pullback.fst G.source G.target := hfirst2
      · calc
          pairT ≫ pairMap ≫ pullback.snd G.source G.target =
              pairT ≫ pullback.snd H1.groupoid.source H1.groupoid.target ≫
                F.mapArrows := by
            simpa only [Category.assoc] using congrArg (pairT ≫ ·) hpairMapSnd
          _ = h1 ≫ F.mapArrows :=
            congrArg (fun m => m ≫ F.mapArrows) hpairTsndHom
          _ = wT2 := hhLiftArrow
          _ = xT2 ≫ p ≫ pullback.snd G.source G.target := by
            simp [wT2, xT2, wT, Category.assoc]
    have hxT2point : xT2.left.base t2 = x := by
      change xT.left.base (eT.left.base t2) = x
      rwa [heTpoint]
    have hpairMapPt : pairMap.left.base pairTPt = ξ := by
      have hp := congrArg (fun m => m.base t2) (congrArg Over.Hom.left hPairMapExact)
      rw [Over.comp_left, Scheme.Hom.comp_apply] at hp
      simpa [pairTPt, ξ, p] using hp.trans
        (congrArg (fun q => p.left.base q) hxT2point)
    have htransPoint : mapArrow.left.base (translate.left.base w') =
        G.comp.left.base (pairMap.left.base (d.left.base w')) := by
      have hp := congrArg (fun m => m.left.base w') htranslateMap
      simpa [Scheme.Hom.comp_apply, d] using hp
    rw [htransPoint, hpairDEq, hpairMapPt]
    simp [Over.comp_left, ξ, p]
  exact ⟨V, hVsub, hVopen, hyV⟩

end AlgebraicGeometry
