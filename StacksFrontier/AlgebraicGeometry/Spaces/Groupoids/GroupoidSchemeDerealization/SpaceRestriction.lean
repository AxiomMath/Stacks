module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Represented algebraic spaces and restrictions of groupoids in algebraic spaces

The space-level half of the de-realization in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization`:

* facts about groupoids in functors: `Deformation.GroupoidInFunctors.left_inverse_unique`,
  `Deformation.GroupoidInFunctors.compose_source` and `compose_target`;
* the algebraic spaces represented by schemes over `S` which the big fppf site contains, the
  scheme representing a representable presheaf (`AlgebraicGeometry.Space.representingScheme`)
  and the de-realization of a morphism into a represented space
  (`AlgebraicGeometry.Space.derealize`);
* restrictions of a groupoid in algebraic spaces: the composition data, the description of an
  arrow of a restriction by its source, its target and its underlying arrow
  (`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restriction_arrow_ext`), and restriction along a
  morphism precomposed with an isomorphism
  (`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsCompIso`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.GroupoidInFunctors

/-- The underlying arrow of the composite, in the evaluated groupoid, of the arrows determined by
two composable sections is their `compose`. -/
private theorem evaluationArrowEquiv_comp_symm {J : Type u} [Category.{v} J]
    (G : GroupoidInFunctors J) (J' : J) (x y z : G.Evaluation J') (a b : G.arrows.obj J')
    (hax : G.source.app J' a = x) (hay : G.target.app J' a = y)
    (hby : G.source.app J' b = y) (hbz : G.target.app J' b = z) :
    letI := G.evaluationGroupoid J'
    (G.evaluationArrowEquiv J' x z
      ((G.evaluationArrowEquiv J' x y).symm ⟨a, hax, hay⟩ ≫
        (G.evaluationArrowEquiv J' y z).symm ⟨b, hby, hbz⟩)).1 =
      G.compose J' b a (hby.trans hay.symm) := by
  let := G.evaluationGroupoid J'
  refine (G.evaluationArrowEquiv_comp J' _ _).trans ?_
  refine congrArg (G.comp.app J') (Subtype.ext (Prod.ext ?_ ?_))
  · exact congrArg Subtype.val ((G.evaluationArrowEquiv J' y z).apply_symm_apply _)
  · exact congrArg Subtype.val ((G.evaluationArrowEquiv J' x y).apply_symm_apply _)

/-- **Left inverses in a groupoid in functors are unique.**  Two arrows which compose with a
given arrow to the identity at its source are equal.

This is stated in terms of `compose` and `identity` only.  It deliberately avoids
`Deformation.inverseArrow`, and so avoids `Groupoid.inv` and the transport of the source and
target indices along `Hom.map_source` and `Hom.map_target`, whose
bookkeeping obstructs a direct proof.  The two objects are taken as parameters of type
`Deformation.GroupoidInFunctors.Evaluation`, as in
`Deformation.GroupoidInFunctors.identity_eq_of_idempotent`, because the `Groupoid` instance is
keyed on `Evaluation` and instance search does not see through it from `G.objects.obj T`. -/
theorem left_inverse_unique {J : Type u} [Category.{v} J] (G : GroupoidInFunctors J) (J' : J)
    (x y : G.Evaluation J') (a b c : G.arrows.obj J')
    (hax : G.source.app J' a = x) (hay : G.target.app J' a = y)
    (hbx : G.source.app J' b = y) (hby : G.target.app J' b = x)
    (hcx : G.source.app J' c = y) (hcy : G.target.app J' c = x)
    (hb : G.compose J' b a (hbx.trans hay.symm) = G.identity J' x)
    (hc : G.compose J' c a (hcx.trans hay.symm) = G.identity J' x) :
    b = c := by
  let := G.evaluationGroupoid J'
  have key : ∀ (d : G.arrows.obj J') (hdx : G.source.app J' d = y) (hdy : G.target.app J' d = x),
      G.compose J' d a (hdx.trans hay.symm) = G.identity J' x →
      ((G.evaluationArrowEquiv J' x y).symm ⟨a, hax, hay⟩) ≫
        ((G.evaluationArrowEquiv J' y x).symm ⟨d, hdx, hdy⟩) = 𝟙 x := by
    intro d hdx hdy hd
    refine (G.evaluationArrowEquiv J' x x).injective (Subtype.ext ?_)
    exact (evaluationArrowEquiv_comp_symm G J' x y x a d hax hay hdx hdy).trans
      (hd.trans (G.evaluationArrowEquiv_id J' x).symm)
  have hβγ := (cancel_epi ((G.evaluationArrowEquiv J' x y).symm ⟨a, hax, hay⟩)).1
    ((key b hbx hby hb).trans (key c hcx hcy hc).symm)
  exact ((congrArg Subtype.val
    ((G.evaluationArrowEquiv J' y x).apply_symm_apply ⟨b, hbx, hby⟩)).symm.trans
    (congrArg (fun k => (G.evaluationArrowEquiv J' y x k).1) hβγ)).trans
    (congrArg Subtype.val ((G.evaluationArrowEquiv J' y x).apply_symm_apply ⟨c, hcx, hcy⟩))

/-- The source of a composite is the source of the arrow composed first.  The repository has no
`compose_source`; it is read off the subtype that `evaluationArrowEquiv` lands in. -/
theorem compose_source {J : Type u} [Category.{v} J] (G : GroupoidInFunctors J) (J' : J)
    (x y z : G.Evaluation J') (a b : G.arrows.obj J')
    (hax : G.source.app J' a = x) (hay : G.target.app J' a = y)
    (hby : G.source.app J' b = y) (hbz : G.target.app J' b = z) :
    G.source.app J' (G.compose J' b a (hby.trans hay.symm)) = x := by
  let := G.evaluationGroupoid J'
  exact (congrArg (G.source.app J')
    (evaluationArrowEquiv_comp_symm G J' x y z a b hax hay hby hbz)).symm.trans
    (G.evaluationArrowEquiv J' x z
      ((G.evaluationArrowEquiv J' x y).symm ⟨a, hax, hay⟩ ≫
        (G.evaluationArrowEquiv J' y z).symm ⟨b, hby, hbz⟩)).2.1

/-- The target of a composite is the target of the arrow composed last. -/
theorem compose_target {J : Type u} [Category.{v} J] (G : GroupoidInFunctors J) (J' : J)
    (x y z : G.Evaluation J') (a b : G.arrows.obj J')
    (hax : G.source.app J' a = x) (hay : G.target.app J' a = y)
    (hby : G.source.app J' b = y) (hbz : G.target.app J' b = z) :
    G.target.app J' (G.compose J' b a (hby.trans hay.symm)) = z := by
  let := G.evaluationGroupoid J'
  exact (congrArg (G.target.app J')
    (evaluationArrowEquiv_comp_symm G J' x y z a b hax hay hby hbz)).symm.trans
    (G.evaluationArrowEquiv J' x z
      ((G.evaluationArrowEquiv J' x y).symm ⟨a, hax, hay⟩ ≫
        (G.evaluationArrowEquiv J' y z).symm ⟨b, hby, hbz⟩)).2.2

end Deformation.GroupoidInFunctors

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)

/-! ### Objects and morphisms of the site are schemes over `S` -/

/-- The big fppf site over `S` contains the scheme over `S` underlying any of its objects. -/
theorem contains_siteToOver_obj (T : BigFppfOver C S hS) :
    C.Contains ((siteToOver C hS).obj T).left :=
  T.left.2

/-- An object of the big fppf site over `S` is the scheme over `S` it determines, regarded in
the site. -/
theorem schemeSiteObject_siteToOver_obj (T : BigFppfOver C S hS) :
    schemeSiteObject C hS (contains_siteToOver_obj C hS T) = T :=
  rfl

/-- A morphism of the big fppf site over `S` is the morphism of schemes over `S` it determines,
regarded in the site. -/
theorem schemeSiteMap_siteToOver_map {T T' : BigFppfOver C S hS} (f : T ⟶ T') :
    schemeSiteMap C hS (contains_siteToOver_obj C hS T) (contains_siteToOver_obj C hS T')
        ((siteToOver C hS).map f) = f :=
  rfl

/-- The functor to schemes returns a morphism of schemes over `S` regarded in the site as the
morphism of schemes it came from. -/
theorem toScheme_map_schemeSiteMap_eq {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    (BigFppfOver.toScheme C S hS).map (schemeSiteMap C hS hX hY f) = f.left :=
  congrArg (fun m : X ⟶ Y => m.left) (siteToOver_map_schemeSiteMap C hS hX hY f)

/-! ### Algebraic spaces represented by schemes -/

/-- The algebraic space over `S` represented by a scheme over `S` which the site contains. -/
noncomputable abbrev siteSchemeSpace {X : Over S} (hX : C.Contains X.left) :
    AlgebraicSpaces C S hS :=
  ⟨yoneda.obj (schemeSiteObject C hS hX), isAlgebraicSpace_yoneda C S hS _⟩

/-- The morphism of algebraic spaces over `S` represented by a morphism of schemes over `S`
between two schemes which the site contains. -/
noncomputable abbrev siteSchemeSpaceMap {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) : siteSchemeSpace C hS hX ⟶ siteSchemeSpace C hS hY :=
  ObjectProperty.homMk (yoneda.map (schemeSiteMap C hS hX hY f))

/-- A morphism of schemes over `S` between two schemes which the site contains is étale exactly
when the morphism of algebraic spaces it represents is. -/
theorem isEtale_schemeSpaceMap_iff {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    IsEtale C S hS (siteSchemeSpaceMap C hS hX hY f).hom ↔ Etale f.left := by
  have h : (siteSchemeSpaceMap C hS hX hY f).hom = yoneda.map (schemeSiteMap C hS hX hY f) := rfl
  rw [h, isEtale_iff_presheaf_of_yoneda C S hS,
    presheaf_yoneda_map_iff C S hS AlgebraicGeometry.Etale.etale_isStableUnderBaseChange,
    toScheme_map_schemeSiteMap_eq]
  exact Iff.rfl

/-- A morphism of schemes over `S` between two schemes which the site contains is separated
exactly when the morphism of algebraic spaces it represents is. -/
theorem isSeparated_schemeSpaceMap_iff {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    IsSeparated C S hS (siteSchemeSpaceMap C hS hX hY f).hom ↔
      AlgebraicGeometry.IsSeparated f.left := by
  have h : (siteSchemeSpaceMap C hS hX hY f).hom = yoneda.map (schemeSiteMap C hS hX hY f) := rfl
  rw [h, isSeparated_yoneda_map_iff C S hS, toScheme_map_schemeSiteMap_eq]
  exact Iff.rfl

/-- A morphism of schemes over `S` between two schemes which the site contains is finite exactly
when the morphism of algebraic spaces it represents is.

Finiteness of a morphism of algebraic spaces is the conjunction of relative representability
with finiteness of every represented base change, by
`AlgebraicGeometry.Space.isFinite_iff_representable`; the first conjunct is automatic for a
Yoneda image, and the second is finiteness of the underlying morphism of schemes. -/
theorem isFinite_schemeSpaceMap_iff {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    IsFinite C S hS (siteSchemeSpaceMap C hS hX hY f).hom ↔
      _root_.AlgebraicGeometry.IsFinite f.left := by
  have h : (siteSchemeSpaceMap C hS hX hY f).hom = yoneda.map (schemeSiteMap C hS hX hY f) := rfl
  rw [h, isFinite_iff_representable C S hS _
      (isAlgebraicSpace_yoneda C S hS (schemeSiteObject C hS hX))
      (isAlgebraicSpace_yoneda C S hS (schemeSiteObject C hS hY)),
    presheaf_yoneda_map_iff C S hS
      (P := @_root_.AlgebraicGeometry.IsFinite.{u}) inferInstance,
    toScheme_map_schemeSiteMap_eq]
  exact and_iff_right (CategoryTheory.Functor.relativelyRepresentable.map yoneda _)

/-- Two morphisms of the site into a fibre product of schemes over `S` which the site contains
agree as soon as their composites with the two projections agree.

The square of `AlgebraicGeometry.Space.schemeSitePullbackCone` is cartesian in the site, by
`AlgebraicGeometry.Space.schemeSitePullbackCone_isLimit`, so a morphism into its vertex is its
two components. -/
theorem schemeSiteMap_pullback_hom_ext {X Y Z : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hZ : C.Contains Z.left) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hP : C.Contains (pullback f g).left) {T : BigFppfOver C S hS}
    (a b : T ⟶ schemeSiteObject C hS hP)
    (hfst : a ≫ schemeSiteMap C hS hP hX (pullback.fst f g) =
      b ≫ schemeSiteMap C hS hP hX (pullback.fst f g))
    (hsnd : a ≫ schemeSiteMap C hS hP hY (pullback.snd f g) =
      b ≫ schemeSiteMap C hS hP hY (pullback.snd f g)) :
    a = b :=
  PullbackCone.IsLimit.hom_ext (schemeSitePullbackCone_isLimit C hS hX hY hZ f g hP) hfst hsnd

/-- A morphism of schemes over `S` between two schemes which the site contains is an open
immersion exactly when the morphism of algebraic spaces it represents is.

Unlike finiteness, being an open immersion carries no relative-representability clause for a
morphism of algebraic spaces — `AlgebraicGeometry.Space.IsOpenImmersion` is the presheaf
property outright — so this is `AlgebraicGeometry.Space.presheaf_yoneda_map_iff` directly. -/
theorem isOpenImmersion_schemeSpaceMap_iff {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    IsOpenImmersion C S hS (siteSchemeSpaceMap C hS hX hY f).hom ↔
      _root_.AlgebraicGeometry.IsOpenImmersion f.left := by
  have h : (siteSchemeSpaceMap C hS hX hY f).hom = yoneda.map (schemeSiteMap C hS hX hY f) := rfl
  rw [h]
  have h2 := presheaf_yoneda_map_iff C S hS
    (P := (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
    inferInstance (schemeSiteMap C hS hX hY f)
  rw [toScheme_map_schemeSiteMap_eq] at h2
  exact h2

/-- **Membership in the open cut out by an open subspace.**  A scheme point of `V` lies in
`AlgebraicGeometry.Space.opensOfOpenSubspace` exactly when the point of the space it comes from
lies in the subspace.

The carrier of that open is by definition the image under
`AlgebraicGeometry.Space.pointsToScheme` of the range of the subspace's inclusion on points, and
`AlgebraicGeometry.Space.pointsToScheme` is injective, so image-membership is
range-membership. -/
theorem mem_opensOfOpenSubspace (V : BigFppfOver C S hS) (A : Subfunctor (yoneda.obj V))
    (hA : IsOpenSubspace C S hS A) (x : points C S hS (yoneda.obj V)) :
    pointsToScheme C S hS V x ∈ opensOfOpenSubspace C S hS V A hA ↔
      x ∈ Set.range (pointsMap C S hS A.toFunctor A.ι) :=
  (injective_pointsToScheme C S hS V).mem_set_image

/-- Two morphisms of schemes over `S` between schemes which the site contains agree as soon as
the morphisms of presheaves they represent agree: Yoneda is faithful, and
`AlgebraicGeometry.Space.siteToOver_map_schemeSiteMap` recovers a morphism of schemes from the
morphism of the site it determines. -/
theorem schemeSiteMap_yoneda_injective {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) {a b : X ⟶ Y}
    (h : yoneda.map (schemeSiteMap C hS hX hY a) = yoneda.map (schemeSiteMap C hS hX hY b)) :
    a = b := by
  have h' := congrArg (siteToOver C hS).map (yoneda.map_injective h)
  rwa [siteToOver_map_schemeSiteMap, siteToOver_map_schemeSiteMap] at h'

/-- Two sections of a pullback of presheaves of types agree as soon as their images under the
two projections agree.

A section of such a pullback is a pair of sections with the same image in the base, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.pullbackAppEquiv`, and that equivalence reads the
pair off along the two projections. -/
theorem pullback_app_ext {F G H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (T : (BigFppfOver C S hS)ᵒᵖ) (x y : (pullback f g).obj T)
    (hfst : (pullback.fst f g).app T x = (pullback.fst f g).app T y)
    (hsnd : (pullback.snd f g).app T x = (pullback.snd f g).app T y) :
    x = y := by
  refine (GroupoidInAlgebraicSpaces.pullbackAppEquiv f g T).injective (Subtype.ext (Prod.ext ?_ ?_))
  · rw [GroupoidInAlgebraicSpaces.pullbackAppEquiv_fst,
      GroupoidInAlgebraicSpaces.pullbackAppEquiv_fst, hfst]
  · rw [GroupoidInAlgebraicSpaces.pullbackAppEquiv_snd,
      GroupoidInAlgebraicSpaces.pullbackAppEquiv_snd, hsnd]

/-! ### De-realization of a representable algebraic space -/

variable (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)

/-- The scheme over `S` representing a representable presheaf on the big fppf site over `S`. -/
noncomputable def representingScheme [F.IsRepresentable] : Over S :=
  (siteToOver C hS).obj F.reprX

/-- The site contains the scheme representing a representable presheaf. -/
theorem contains_representingScheme [F.IsRepresentable] :
    C.Contains (representingScheme C hS F).left :=
  contains_siteToOver_obj C hS F.reprX

/-- A representable presheaf on the big fppf site over `S` is the presheaf represented by a
scheme over `S` which the site contains. -/
noncomputable def representingSchemeIso [F.IsRepresentable] :
    F ≅ yoneda.obj (schemeSiteObject C hS (contains_representingScheme C hS F)) :=
  F.reprW.symm

/-- The morphism of schemes over `S` underlying a morphism from a representable presheaf on the
big fppf site over `S` to the presheaf represented by a scheme which the site contains. -/
noncomputable def derealize [F.IsRepresentable] {Y : Over S} (hY : C.Contains Y.left)
    (f : F ⟶ yoneda.obj (schemeSiteObject C hS hY)) : representingScheme C hS F ⟶ Y :=
  (siteToOver C hS).map (yoneda.preimage ((representingSchemeIso C hS F).inv ≫ f))

/-- The morphism of presheaves represented by `AlgebraicGeometry.Space.derealize` is the given
one, read through the identification of its source with its representing scheme. -/
theorem derealize_spec [F.IsRepresentable] {Y : Over S} (hY : C.Contains Y.left)
    (f : F ⟶ yoneda.obj (schemeSiteObject C hS hY)) :
    yoneda.map (schemeSiteMap C hS (contains_representingScheme C hS F) hY
        (derealize C hS F hY f)) = (representingSchemeIso C hS F).inv ≫ f := by
  show yoneda.map (yoneda.preimage ((representingSchemeIso C hS F).inv ≫ f)) = _
  exact yoneda.map_preimage _

/-- An étale morphism out of an algebraic space identified with a represented presheaf is étale
after every representable base change. -/
theorem presheaf_etale_of_isEtale_iso {T : BigFppfOver C S hS}
    {H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (e : yoneda.obj T ≅ F) (f : F ⟶ H)
    (hf : IsEtale C S hS f) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf (e.hom ≫ f) := by
  refine hf T e.hom ?_
  have hid := (presheaf_yoneda_map_iff C S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange (𝟙 T)).2 inferInstance
  have h := MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS))) e.hom (𝟙 (yoneda.obj T)) (by simpa using hid)
  simpa using h

/-! ### Transport of cartesian squares along isomorphisms of the cospan -/

/-- A cartesian square stays cartesian after composing each leg of its cospan with an
isomorphism. -/
theorem isPullback_comp_iso {𝒞 : Type*} [Category 𝒞] {W W' Z Z' Y P : 𝒞}
    {l : P ⟶ W'} {r : P ⟶ Z'} {f : W' ⟶ Y} {g : Z' ⟶ Y}
    (h : IsPullback l r f g) (i : W ≅ W') (j : Z ≅ Z') :
    IsPullback (l ≫ i.inv) (r ≫ j.inv) (i.hom ≫ f) (j.hom ≫ g) := by
  have w : (l ≫ i.inv) ≫ i.hom ≫ f = (r ≫ j.inv) ≫ j.hom ≫ g := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact h.w
  refine IsPullback.of_isLimit (c := PullbackCone.mk (l ≫ i.inv) (r ≫ j.inv) w)
    (PullbackCone.isLimitAux' _ fun s => ?_)
  have hs : (s.fst ≫ i.hom) ≫ f = (s.snd ≫ j.hom) ≫ g := by
    have hc := s.condition
    simp only [Category.assoc] at hc ⊢
    exact hc
  refine ⟨h.lift (s.fst ≫ i.hom) (s.snd ≫ j.hom) hs, ?_, ?_, ?_⟩
  · show h.lift (s.fst ≫ i.hom) (s.snd ≫ j.hom) hs ≫ l ≫ i.inv = s.fst
    rw [← Category.assoc, h.lift_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · show h.lift (s.fst ≫ i.hom) (s.snd ≫ j.hom) hs ≫ r ≫ j.inv = s.snd
    rw [← Category.assoc, h.lift_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro m hm₁ hm₂
    replace hm₁ : m ≫ l ≫ i.inv = s.fst := hm₁
    replace hm₂ : m ≫ r ≫ j.inv = s.snd := hm₂
    refine h.hom_ext ?_ ?_
    · rw [h.lift_fst]
      exact (Iso.comp_inv_eq i).1 ((Category.assoc m l i.inv).trans hm₁)
    · rw [h.lift_snd]
      exact (Iso.comp_inv_eq j).1 ((Category.assoc m r j.inv).trans hm₂)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The two underlying arrows of a composable pair of arrows of a restriction are composable in
the ambient groupoid: the source of the one composed last is the target of the one composed
first. -/
theorem restrictionUnderlying_composable (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    (fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionArrowsToArrows G g) ≫ G.source =
      (fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionArrowsToArrows G g) ≫ G.target :=
  calc (fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionArrowsToArrows G g) ≫ G.source
      = fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionArrowsToArrows G g ≫ G.source := Category.assoc _ _ _
    _ = fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionSource G g ≫ g :=
        congrArg (fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫ ·)
          (restriction_condition G g).symm
    _ = (fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionSource G g) ≫ g := (Category.assoc _ _ _).symm
    _ = (fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionTarget G g) ≫ g :=
        congrArg (· ≫ g) (fiberProduct_condition _ _)
    _ = fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionTarget G g ≫ g := Category.assoc _ _ _
    _ = fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionArrowsToArrows G g ≫ G.target :=
        congrArg (fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫ ·)
          (restriction_condition' G g).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The pair of underlying arrows of a composable pair of arrows of a restriction, as a section
of the space of composable pairs of the ambient groupoid. -/
noncomputable def restrictionUnderlyingLift (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g) (restrictionTarget G g) ⟶
      AlgebraicSpaces.fiberProduct C S hS G.source G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift
    (fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
      restrictionArrowsToArrows G g)
    (fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
      restrictionArrowsToArrows G g)
    (restrictionUnderlying_composable G g)

/-- The arrow composed last, read off the pair. -/
theorem restrictionUnderlyingLift_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionUnderlyingLift G g ≫ fiberProductFst G.source G.target =
      fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
        restrictionArrowsToArrows G g :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_fst _ _ _

/-- The arrow composed first, read off the pair. -/
theorem restrictionUnderlyingLift_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionUnderlyingLift G g ≫ fiberProductSnd G.source G.target =
      fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
        restrictionArrowsToArrows G g :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_snd _ _ _

/-- **The underlying arrow of a composite, at morphism level.**  The arrow of the ambient
groupoid underlying the composite of a composable pair of arrows of a restriction is the
composite, in the ambient groupoid, of the pair of its two underlying arrows.

This is the morphism-level form of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionCompositionData_underlying_comp_app`,
which states it section by section.  Both sides are sections of the space of composable pairs of
the ambient groupoid, so `AlgebraicGeometry.Space.pullback_app_ext` reduces the equality to the
two underlying arrows, read off by
`AlgebraicGeometry.Space.composableToPullback_fst_app`/`_snd_app` on one side and by
`restrictionUnderlyingLift_comp_fst`/`_comp_snd` on the other. -/
theorem restrictionCompositionData_underlying_eq (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    (restrictionCompositionData G g).underlying = restrictionUnderlyingLift G g ≫ G.comp := by
  have hfst : (restrictionUnderlyingLift G g).hom ≫
      pullback.fst G.source.hom G.target.hom =
      (fiberProductFst (restrictionSource G g) (restrictionTarget G g)).hom ≫
        (restrictionArrowsToArrows G g).hom :=
    congrArg (fun k => k.hom) (restrictionUnderlyingLift_comp_fst G g)
  have hsnd : (restrictionUnderlyingLift G g).hom ≫
      pullback.snd G.source.hom G.target.hom =
      (fiberProductSnd (restrictionSource G g) (restrictionTarget G g)).hom ≫
        (restrictionArrowsToArrows G g).hom :=
    congrArg (fun k => k.hom) (restrictionUnderlyingLift_comp_snd G g)
  apply ObjectProperty.hom_ext
  ext T z
  have hfst' := congrArg (fun k => k z) (NatTrans.congr_app hfst T)
  have hsnd' := congrArg (fun k => k z) (NatTrans.congr_app hsnd T)
  show (restrictionCompositionData G g).underlying.hom.app T z =
    (restrictionUnderlyingLift G g ≫ G.comp).hom.app T z
  rw [restrictionCompositionData_underlying_comp_app]
  refine congrArg ((G.comp.hom.app T)) (Space.pullback_app_ext C hS _ _ T _ _ ?_ ?_)
  · exact (Space.composableToPullback_fst_app C hS _ _ T _).trans hfst'.symm
  · exact (Space.composableToPullback_snd_app C hS _ _ T _).trans hsnd'.symm

/-! ### An arrow of a restriction is its source, its target and its underlying arrow -/

/-- **The space-level counterpart of `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext`.**
Two sections of the arrow space of a restriction with the same source, the same target and the
same underlying arrow of the ambient groupoid are equal.

This comes from the field `evaluation_fullyFaithful` of the restriction and nothing else: a fully
faithful functor is injective on arrows, and an arrow of an evaluated groupoid in functors is its
underlying section.  It needs no access to the restriction's composition, which the `Restriction`
structure does not expose, and so it serves for the identity, the inverse and the composition
alike. -/
theorem restriction_arrow_ext (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} {g : U' ⟶ G.objects} (R : Restriction G g)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x y : R.groupoid.toGroupoidInFunctors.Evaluation T)
    (a b : R.groupoid.arrows.obj.obj T)
    (has : R.groupoid.source.hom.app T a = x)
    (hat : R.groupoid.target.hom.app T a = y)
    (hbs : R.groupoid.source.hom.app T b = x)
    (hbt : R.groupoid.target.hom.app T b = y)
    (harr : R.hom.toGroupoidHom.mapArrows.app T a =
      R.hom.toGroupoidHom.mapArrows.app T b) :
    a = b := by
  have hff := Classical.choice (R.evaluation_fullyFaithful T)
  have ha : (R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y
      ((R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y).symm
        ⟨a, has, hat⟩)).1 = a :=
    congrArg Subtype.val
      ((R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y).apply_symm_apply _)
  have hb : (R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y
      ((R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y).symm
        ⟨b, hbs, hbt⟩)).1 = b :=
    congrArg Subtype.val
      ((R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y).apply_symm_apply _)
  have hmap : (R.hom.toGroupoidHom.evaluation T).map
        ((R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y).symm ⟨a, has, hat⟩) =
      (R.hom.toGroupoidHom.evaluation T).map
        ((R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y).symm
          ⟨b, hbs, hbt⟩) := by
    refine (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).injective (Subtype.ext ?_)
    refine (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
      R.hom.toGroupoidHom T _).trans ?_
    refine Eq.trans ?_ (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
      R.hom.toGroupoidHom T _).symm
    refine (congrArg (R.hom.toGroupoidHom.mapArrows.app T) ha).trans ?_
    exact harr.trans (congrArg (R.hom.toGroupoidHom.mapArrows.app T) hb).symm
  exact congrArg Subtype.val
    ((R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x y).symm.injective
      (hff.map_injective hmap))

/-- **The identity of a restriction, recognised by its underlying arrow.**  A section of the
arrow space of a restriction whose source and target are both a given point, and whose underlying
arrow of the ambient groupoid is the ambient identity arrow there, is the identity of the
restriction at that point.

This is `restriction_arrow_ext` against the field `map_id` of the morphism of groupoids: the
identity of the restriction has that source, that target and that underlying arrow. -/
theorem restriction_identity_eq (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} {g : U' ⟶ G.objects} (R : Restriction G g)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : R.groupoid.toGroupoidInFunctors.Evaluation T)
    (a : R.groupoid.arrows.obj.obj T)
    (has : R.groupoid.source.hom.app T a = x)
    (hat : R.groupoid.target.hom.app T a = x)
    (harr : R.hom.toGroupoidHom.mapArrows.app T a =
      G.toGroupoidInFunctors.identity T (R.hom.toGroupoidHom.mapObjects.app T x)) :
    R.groupoid.toGroupoidInFunctors.identity T x = a := by
  refine restriction_arrow_ext G R T x x _ a ?_ ?_ has hat ?_
  · exact (R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.1
  · exact (R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.2
  · exact (R.hom.toGroupoidHom.map_id T x).trans harr.symm

/-- **The inverse of a restriction, recognised through the ambient groupoid.**  Two sections of
the arrow space of a restriction with the source and the target of an inverse of a given arrow,
whose underlying arrows of the ambient groupoid both compose with the underlying arrow of the
given one to the ambient identity, are equal.

The composite of either with the given arrow has the point for its source and its target, and
has the ambient identity arrow for its underlying arrow by the field `map_comp` of the morphism
of groupoids, so it is the identity of the restriction by `restriction_arrow_ext`; and left
inverses are unique, by `Deformation.GroupoidInFunctors.left_inverse_unique`. -/
theorem restriction_left_inverse_unique (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} {g : U' ⟶ G.objects} (R : Restriction G g)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (x y : R.groupoid.toGroupoidInFunctors.Evaluation T)
    (a b c : R.groupoid.arrows.obj.obj T)
    (has : R.groupoid.source.hom.app T a = x)
    (hat : R.groupoid.target.hom.app T a = y)
    (hbs : R.groupoid.source.hom.app T b = y)
    (hbt : R.groupoid.target.hom.app T b = x)
    (hcs : R.groupoid.source.hom.app T c = y)
    (hct : R.groupoid.target.hom.app T c = x)
    (wb : G.source.hom.app T (R.hom.toGroupoidHom.mapArrows.app T b) =
      G.target.hom.app T (R.hom.toGroupoidHom.mapArrows.app T a))
    (wc : G.source.hom.app T (R.hom.toGroupoidHom.mapArrows.app T c) =
      G.target.hom.app T (R.hom.toGroupoidHom.mapArrows.app T a))
    (hb : G.toGroupoidInFunctors.compose T (R.hom.toGroupoidHom.mapArrows.app T b)
        (R.hom.toGroupoidHom.mapArrows.app T a) wb =
      G.toGroupoidInFunctors.identity T (R.hom.toGroupoidHom.mapObjects.app T x))
    (hc : G.toGroupoidInFunctors.compose T (R.hom.toGroupoidHom.mapArrows.app T c)
        (R.hom.toGroupoidHom.mapArrows.app T a) wc =
      G.toGroupoidInFunctors.identity T (R.hom.toGroupoidHom.mapObjects.app T x)) :
    b = c := by
  have key : ∀ (d : R.groupoid.arrows.obj.obj T)
      (hds : R.groupoid.source.hom.app T d = y)
      (hdt : R.groupoid.target.hom.app T d = x)
      (wd : G.source.hom.app T (R.hom.toGroupoidHom.mapArrows.app T d) =
        G.target.hom.app T (R.hom.toGroupoidHom.mapArrows.app T a)),
      G.toGroupoidInFunctors.compose T (R.hom.toGroupoidHom.mapArrows.app T d)
          (R.hom.toGroupoidHom.mapArrows.app T a) wd =
        G.toGroupoidInFunctors.identity T (R.hom.toGroupoidHom.mapObjects.app T x) →
      R.groupoid.toGroupoidInFunctors.compose T d a (hds.trans hat.symm) =
        R.groupoid.toGroupoidInFunctors.identity T x := by
    intro d hds hdt wd hd
    refine restriction_arrow_ext G R T x x
      (R.groupoid.toGroupoidInFunctors.compose T d a (hds.trans hat.symm))
      (R.groupoid.toGroupoidInFunctors.identity T x) ?_ ?_ ?_ ?_ ?_
    · exact Deformation.GroupoidInFunctors.compose_source
        R.groupoid.toGroupoidInFunctors T x y x a d has hat hds hdt
    · exact Deformation.GroupoidInFunctors.compose_target
        R.groupoid.toGroupoidInFunctors T x y x a d has hat hds hdt
    · exact (R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.1
    · exact (R.groupoid.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2.2
    · refine Eq.trans ?_ (R.hom.toGroupoidHom.map_id T x).symm
      refine Eq.trans ?_ hd
      exact (R.hom.toGroupoidHom.map_comp T d a (hds.trans hat.symm)).symm
  exact Deformation.GroupoidInFunctors.left_inverse_unique
    R.groupoid.toGroupoidInFunctors T x y a b c has hat hbs hbt hcs hct
    (key b hbs hbt wb hb) (key c hcs hct wc hc)

/-! ### Restricting along a morphism precomposed with an isomorphism -/

/-- The first factor of the restricted arrow space, read on the cospan of the precomposed
morphism: it is still cartesian, because the comparison is an isomorphism. -/
theorem isPullback_restrictionTargetFactorComp (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    IsPullback (fiberProductFst g G.target ≫ E.inv) (fiberProductSnd g G.target)
      (E.hom ≫ g) G.target := by
  have h := Space.isPullback_comp_iso
    (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target) E (Iso.refl G.arrows)
  simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp] using h

/-- The second factor of the restricted arrow space, read on the cospan of the precomposed
morphism. -/
theorem isPullback_restrictionSourceFactorComp (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    IsPullback (fiberProductFst G.source g) (fiberProductSnd G.source g ≫ E.inv)
      G.source (E.hom ≫ g) := by
  have h := Space.isPullback_comp_iso
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g) (Iso.refl G.arrows) E
  simpa only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp] using h

/-- The first factor is unchanged, up to the isomorphism, on precomposing the restricting
morphism with it. -/
noncomputable def restrictionTargetFactorCompIso (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    AlgebraicSpaces.fiberProduct C S hS (E.hom ≫ g) G.target ≅
      AlgebraicSpaces.fiberProduct C S hS g G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS (E.hom ≫ g) G.target).isoIsPullback _ _
    (isPullback_restrictionTargetFactorComp G E g)

/-- The second factor is likewise unchanged. -/
noncomputable def restrictionSourceFactorCompIso (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    AlgebraicSpaces.fiberProduct C S hS G.source (E.hom ≫ g) ≅
      AlgebraicSpaces.fiberProduct C S hS G.source g :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source (E.hom ≫ g)).isoIsPullback _ _
    (isPullback_restrictionSourceFactorComp G E g)

/-- The first factor's identification carries the lift of the target across, up to the
isomorphism: the two lifts live in the two different spaces. -/
theorem restrictionTargetFactorCompIso_hom_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionTargetFactorCompIso G E g).hom ≫ fiberProductFst g G.target ≫ E.inv =
      fiberProductFst (E.hom ≫ g) G.target :=
  IsPullback.isoIsPullback_hom_fst _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS (E.hom ≫ g) G.target)
    (isPullback_restrictionTargetFactorComp G E g)

/-- The first factor's identification carries the projection to the ambient arrows across. -/
theorem restrictionTargetFactorCompIso_hom_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionTargetFactorCompIso G E g).hom ≫ fiberProductSnd g G.target =
      fiberProductSnd (E.hom ≫ g) G.target :=
  IsPullback.isoIsPullback_hom_snd _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS (E.hom ≫ g) G.target)
    (isPullback_restrictionTargetFactorComp G E g)

/-- The second factor's identification carries the projection to the ambient arrows across. -/
theorem restrictionSourceFactorCompIso_hom_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionSourceFactorCompIso G E g).hom ≫ fiberProductFst G.source g =
      fiberProductFst G.source (E.hom ≫ g) :=
  IsPullback.isoIsPullback_hom_fst _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source (E.hom ≫ g))
    (isPullback_restrictionSourceFactorComp G E g)

/-- The second factor's identification carries the lift of the source across, up to the
isomorphism. -/
theorem restrictionSourceFactorCompIso_hom_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionSourceFactorCompIso G E g).hom ≫ fiberProductSnd G.source g ≫ E.inv =
      fiberProductSnd G.source (E.hom ≫ g) :=
  IsPullback.isoIsPullback_hom_snd _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source (E.hom ≫ g))
    (isPullback_restrictionSourceFactorComp G E g)

/-- The arrow space of the restriction along `g`, read on the cospan of the precomposed
morphism. -/
theorem isPullback_restrictionArrowsComp (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    IsPullback
      (fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g) ≫
        (restrictionTargetFactorCompIso G E g).inv)
      (fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g) ≫
        (restrictionSourceFactorCompIso G E g).inv)
      (fiberProductSnd (E.hom ≫ g) G.target)
      (fiberProductFst G.source (E.hom ≫ g)) := by
  have h := Space.isPullback_comp_iso
    (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (fiberProductSnd g G.target) (fiberProductFst G.source g))
    (restrictionTargetFactorCompIso G E g) (restrictionSourceFactorCompIso G E g)
  rwa [restrictionTargetFactorCompIso_hom_comp_snd,
    restrictionSourceFactorCompIso_hom_comp_fst] at h

/-- **Restricting along a morphism precomposed with an isomorphism.**  The arrow space of the
restriction of a groupoid in algebraic spaces along `E.hom ≫ g` is canonically isomorphic to the
arrow space of the restriction along `g`.

This is what lets the output of a de-realization be used.  De-realizing a representable algebraic
space produces a scheme together with an *isomorphism* onto that space, so a restriction taken
along a morphism out of the space has to be compared with the restriction along the
corresponding morphism out of the scheme; nothing in the library did that. -/
noncomputable def restrictionArrowsCompIso (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    restrictionArrows G (E.hom ≫ g) ≅ restrictionArrows G g :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS
    (fiberProductSnd (E.hom ≫ g) G.target)
    (fiberProductFst G.source (E.hom ≫ g))).isoIsPullback _ _
    (isPullback_restrictionArrowsComp G E g)

/-- The identification carries the first projection of the iterated fibre product across. -/
theorem restrictionArrowsCompIso_hom_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionArrowsCompIso G E g).hom ≫
        fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g) ≫
        (restrictionTargetFactorCompIso G E g).inv =
      fiberProductFst (fiberProductSnd (E.hom ≫ g) G.target)
        (fiberProductFst G.source (E.hom ≫ g)) :=
  IsPullback.isoIsPullback_hom_fst _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (fiberProductSnd (E.hom ≫ g) G.target)
      (fiberProductFst G.source (E.hom ≫ g)))
    (isPullback_restrictionArrowsComp G E g)

/-- The identification carries the second projection of the iterated fibre product across. -/
theorem restrictionArrowsCompIso_hom_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionArrowsCompIso G E g).hom ≫
        fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g) ≫
        (restrictionSourceFactorCompIso G E g).inv =
      fiberProductSnd (fiberProductSnd (E.hom ≫ g) G.target)
        (fiberProductFst G.source (E.hom ≫ g)) :=
  IsPullback.isoIsPullback_hom_snd _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (fiberProductSnd (E.hom ≫ g) G.target)
      (fiberProductFst G.source (E.hom ≫ g)))
    (isPullback_restrictionArrowsComp G E g)

/-- The identification carries the projection to the ambient arrows across. -/
theorem restrictionArrowsCompIso_hom_comp_arrowsToArrows
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionArrowsCompIso G E g).hom ≫ restrictionArrowsToArrows G g =
      restrictionArrowsToArrows G (E.hom ≫ g) := by
  have h0 : ((restrictionArrowsCompIso G E g).hom ≫
        fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g)) ≫
      (restrictionTargetFactorCompIso G E g).inv =
      fiberProductFst (fiberProductSnd (E.hom ≫ g) G.target)
        (fiberProductFst G.source (E.hom ≫ g)) :=
    (Category.assoc _ _ _).trans (restrictionArrowsCompIso_hom_comp_fst G E g)
  have h1 := (Iso.comp_inv_eq _).1 h0
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ fiberProductSnd g G.target) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun k =>
    fiberProductFst (fiberProductSnd (E.hom ≫ g) G.target)
      (fiberProductFst G.source (E.hom ≫ g)) ≫ k)
    (restrictionTargetFactorCompIso_hom_comp_snd G E g)

/-- The identification carries the lift of the target across, up to the isomorphism: the two
lifts live in the two different spaces. -/
theorem restrictionArrowsCompIso_hom_comp_target (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionArrowsCompIso G E g).hom ≫ restrictionTarget G g =
      restrictionTarget G (E.hom ≫ g) ≫ E.hom := by
  have h0 : ((restrictionArrowsCompIso G E g).hom ≫
        fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g)) ≫
      (restrictionTargetFactorCompIso G E g).inv =
      fiberProductFst (fiberProductSnd (E.hom ≫ g) G.target)
        (fiberProductFst G.source (E.hom ≫ g)) :=
    (Category.assoc _ _ _).trans (restrictionArrowsCompIso_hom_comp_fst G E g)
  have h1 := (Iso.comp_inv_eq _).1 h0
  have h2₀ : ((restrictionTargetFactorCompIso G E g).hom ≫ fiberProductFst g G.target) ≫
      E.inv = fiberProductFst (E.hom ≫ g) G.target :=
    (Category.assoc _ _ _).trans (restrictionTargetFactorCompIso_hom_comp_fst G E g)
  have h2 := (Iso.comp_inv_eq _).1 h2₀
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ fiberProductFst g G.target) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k =>
    fiberProductFst (fiberProductSnd (E.hom ≫ g) G.target)
      (fiberProductFst G.source (E.hom ≫ g)) ≫ k) h2).trans ?_
  exact (Category.assoc _ _ _).symm

/-- The identification carries the lift of the source across, up to the isomorphism. -/
theorem restrictionArrowsCompIso_hom_comp_source (G : GroupoidInAlgebraicSpaces C S hS B)
    {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) (g : U₂ ⟶ G.objects) :
    (restrictionArrowsCompIso G E g).hom ≫ restrictionSource G g =
      restrictionSource G (E.hom ≫ g) ≫ E.hom := by
  have h0 : ((restrictionArrowsCompIso G E g).hom ≫
        fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g)) ≫
      (restrictionSourceFactorCompIso G E g).inv =
      fiberProductSnd (fiberProductSnd (E.hom ≫ g) G.target)
        (fiberProductFst G.source (E.hom ≫ g)) :=
    (Category.assoc _ _ _).trans (restrictionArrowsCompIso_hom_comp_snd G E g)
  have h1 := (Iso.comp_inv_eq _).1 h0
  have h2₀ : ((restrictionSourceFactorCompIso G E g).hom ≫ fiberProductSnd G.source g) ≫
      E.inv = fiberProductSnd G.source (E.hom ≫ g) :=
    (Category.assoc _ _ _).trans (restrictionSourceFactorCompIso_hom_comp_snd G E g)
  have h2 := (Iso.comp_inv_eq _).1 h2₀
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ fiberProductSnd G.source g) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k =>
    fiberProductSnd (fiberProductSnd (E.hom ≫ g) G.target)
      (fiberProductFst G.source (E.hom ≫ g)) ≫ k) h2).trans ?_
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
