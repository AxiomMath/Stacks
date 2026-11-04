module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.OpenSaturation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction

/-!
# Open immersions between quotient sheaves of a restricted equivalence relation

Let `j = (t, s) : R ⟶ U ×_S U` be an equivalence relation of schemes over `S` whose source and
target maps are surjective, flat and locally of finite presentation, and let `g : U' ⟶ U` be
flat and locally of finite presentation. The map `U'/R' ⟶ U/R` of quotient sheaves on the big
fppf site over `S` induced by restricting `j` along `g` is then representable and an open
immersion.

## Main definitions

* `AlgebraicGeometry.PreRelation.restrictionMap`: a morphism of pre-relations lying over
  `f : U ⟶ U'` carries the restriction along `g : X ⟶ U` to the restriction along `g ≫ f`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_restrictedQuotientMap`: **Stacks 02WU**, the open
  immersion of quotient sheaves.
* `AlgebraicGeometry.restrictQuotientSheafMap_property_of_extendsRelation`: a property of
  morphisms stable under isomorphism holds for the map of quotient sheaves of a restricted
  pre-relation as soon as it holds for the map of quotient sheaves of the restriction of the
  pre-relation underlying a groupoid scheme extending it.

## Implementation notes

The proof reduces to Tag 046M. The equivalence relation `j` is extended to a groupoid scheme
`G` (`AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation`), whose source and target maps
inherit the fppf data of `j`. The saturation of `g` is the image of the reach map
`U' ×_{g, U, t} R ⟶ U`, which is flat and locally of finite presentation and therefore open;
corestricting the reach map to that open subscheme makes it in addition surjective, hence an
fppf covering, so Tag 046M applies to the restriction of `G` along `g`.

Transporting the conclusion from `G` back to `j` is the content of
`AlgebraicGeometry.restrictQuotientSheafMap_property_of_extendsRelation`, stated for an
arbitrary site and an arbitrary morphism property stable under isomorphism. A groupoid scheme
extending `j` carries its schemes of objects and arrows only propositionally, so the comparison
is a composite of two isomorphisms of quotient sheaves, one for the base relation and one for
the restricted relation; the third isomorphism, identifying the arrow scheme of a restricted
groupoid with the restriction of the underlying pre-relation, is
`AlgebraicGeometry.GroupoidScheme.restrictionQuotientIso`.

## References

* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u v w

namespace AlgebraicGeometry

namespace PreRelation

variable {S : Scheme.{u}} {R R' U U' X : Over S}

/-- A morphism `r : R ⟶ R'` of pre-relations lying over `f : U ⟶ U'` carries the restriction of
the source pre-relation along `g : X ⟶ U` to the restriction of the target pre-relation along
any `g' : X ⟶ U'` factoring as `g ≫ f`. -/
def restrictionMap (j : PreRelation R U) (j' : PreRelation R' U') (r : R ⟶ R') (f : U ⟶ U')
    (hrel : r ≫ j' = j ≫ prod.map f f) {g : X ⟶ U} {g' : X ⟶ U'} (hg : g ≫ f = g') :
    restriction j g ⟶ restriction j' g' :=
  pullback.lift (pullback.fst (prod.map g g) j) (pullback.snd (prod.map g g) j ≫ r) (by
    subst hg
    rw [← prod.map_map, pullback.condition_assoc, Category.assoc, hrel])

variable (j : PreRelation R U) (j' : PreRelation R' U') (r : R ⟶ R') (f : U ⟶ U')
  (hrel : r ≫ j' = j ≫ prod.map f f) {g : X ⟶ U} {g' : X ⟶ U'} (hg : g ≫ f = g')

/-- The comparison of restrictions is compatible with the projection onto the ambient square of
the restricted pre-relation. -/
@[simp]
theorem restrictionMap_comp_fst :
    restrictionMap j j' r f hrel hg ≫ pullback.fst (prod.map g' g') j' =
      pullback.fst (prod.map g g) j :=
  pullback.lift_fst _ _ _

/-- The comparison of restrictions commutes with the source maps. -/
theorem restrictionMap_comp_source :
    restrictionMap j j' r f hrel hg ≫ (restrict j' g').source = (restrict j g).source := by
  show restrictionMap j j' r f hrel hg ≫ pullback.fst (prod.map g' g') j' ≫ prod.snd =
    pullback.fst (prod.map g g) j ≫ prod.snd
  rw [← Category.assoc, restrictionMap_comp_fst]

/-- The comparison of restrictions commutes with the target maps. -/
theorem restrictionMap_comp_target :
    restrictionMap j j' r f hrel hg ≫ (restrict j' g').target = (restrict j g).target := by
  show restrictionMap j j' r f hrel hg ≫ pullback.fst (prod.map g' g') j' ≫ prod.fst =
    pullback.fst (prod.map g g) j ≫ prod.fst
  rw [← Category.assoc, restrictionMap_comp_fst]

end PreRelation

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C] {R U U' : Over S}

/-- A property of morphisms of presheaves stable under isomorphism holds for a morphism of
sheaves once it holds for its composite with an isomorphism of sheaves. -/
private theorem property_hom_of_isoHom_comp (J : GrothendieckTopology C)
    (P : MorphismProperty (Cᵒᵖ ⥤ Type u)) [P.RespectsIso]
    {A A' D : Sheaf J (Type u)} (e : A ≅ A') (f : A' ⟶ D) (h : P (e.hom ≫ f).hom) :
    P f.hom := by
  have : IsIso e.hom.hom := (ObjectProperty.isIso_hom_iff _).2 inferInstance
  exact (P.cancel_left_of_respectsIso e.hom.hom f.hom).1 h

/-- A property of morphisms of presheaves stable under isomorphism holds for the map of
quotient sheaves induced by restricting a pre-relation `j` along `g` as soon as it holds for
the map induced by restricting the pre-relation of a groupoid scheme extending `j` along the
corresponding morphism. -/
theorem restrictQuotientSheafMap_property_of_extendsRelation
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (P : MorphismProperty (Cᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (j : PreRelation R U) (G : GroupoidScheme S) (hG : ExtendsRelation j G) (g : U' ⟶ U)
    (h : P (restrictQuotientSheafMap J F (groupoidPreRelation G)
      (g ≫ eqToHom hG.objects_eq.symm)).hom) :
    P (restrictQuotientSheafMap J F j g).hom := by
  let jG := groupoidPreRelation G
  let e : U ⟶ G.objects := eqToHom hG.objects_eq.symm
  let eInv : G.objects ⟶ U := eqToHom hG.objects_eq
  let r : R ⟶ G.arrows := eqToHom hG.arrows_eq.symm
  let rInv : G.arrows ⟶ R := eqToHom hG.arrows_eq
  have he : e ≫ eInv = 𝟙 U := by simp [e, eInv]
  have heInv : eInv ≫ e = 𝟙 G.objects := by simp [e, eInv]
  have hrInv : rInv ≫ r = 𝟙 G.arrows := by simp [r, rInv]
  have hsrc : r ≫ G.source ≫ eInv = j.source := hG.source_eq
  have htar : r ≫ G.target ≫ eInv = j.target := hG.target_eq
  have hGs : jG.source = G.source := prod.lift_snd _ _
  have hGt : jG.target = G.target := prod.lift_fst _ _
  have hs : r ≫ jG.source = j.source ≫ e := by
    rw [hGs, ← hsrc, Category.assoc, Category.assoc, heInv, Category.comp_id]
  have ht : r ≫ jG.target = j.target ≫ e := by
    rw [hGt, ← htar, Category.assoc, Category.assoc, heInv, Category.comp_id]
  have hsInv : rInv ≫ j.source = jG.source ≫ eInv := by
    rw [hGs, ← hsrc, ← Category.assoc, ← Category.assoc, hrInv, Category.id_comp]
  have htInv : rInv ≫ j.target = jG.target ≫ eInv := by
    rw [hGt, ← htar, ← Category.assoc, ← Category.assoc, hrInv, Category.id_comp]
  have hrel : r ≫ jG = j ≫ prod.map e e := by
    apply prod.hom_ext
    · simpa [PreRelation.target, Category.assoc] using ht
    · simpa [PreRelation.source, Category.assoc] using hs
  have hrelInv : rInv ≫ j = jG ≫ prod.map eInv eInv := by
    apply prod.hom_ext
    · simpa [PreRelation.target, Category.assoc] using htInv
    · simpa [PreRelation.source, Category.assoc] using hsInv
  have hge : g ≫ e ≫ eInv = g := by rw [he, Category.comp_id]
  -- The two comparisons of quotient sheaves, for the base and for the restricted relation.
  let isoBase := quotientSheafMapIso J F jG j rInv eInv r e hsInv htInv hs ht heInv he
  let cFwd := PreRelation.restrictionMap j jG r e hrel (g := g) (g' := g ≫ e) rfl
  let cBack := PreRelation.restrictionMap jG j rInv eInv hrelInv (g := g ≫ e) (g' := g) hge
  let isoRest := quotientSheafMapIso J F (PreRelation.restrict j g)
    (PreRelation.restrict jG (g ≫ e)) cFwd (𝟙 U') cBack (𝟙 U')
    (by simpa using PreRelation.restrictionMap_comp_source j jG r e hrel (g := g) rfl)
    (by simpa using PreRelation.restrictionMap_comp_target j jG r e hrel (g := g) rfl)
    (by simpa using PreRelation.restrictionMap_comp_source jG j rInv eInv hrelInv hge)
    (by simpa using PreRelation.restrictionMap_comp_target jG j rInv eInv hrelInv hge)
    (by simp) (by simp)
  have hfactor : isoRest.hom ≫ restrictQuotientSheafMap J F jG (g ≫ e) ≫ isoBase.hom =
      restrictQuotientSheafMap J F j g := by
    show (quotientSheafMap J F (PreRelation.restrict j g) (PreRelation.restrict jG (g ≫ e))
          cFwd (𝟙 U') _ _ ≫
        quotientSheafMap J F (PreRelation.restrict jG (g ≫ e)) jG
          (pullback.snd (prod.map (g ≫ e) (g ≫ e)) jG) (g ≫ e) _ _) ≫
        quotientSheafMap J F jG j rInv eInv hsInv htInv =
      quotientSheafMap J F (PreRelation.restrict j g) j
        (pullback.snd (prod.map g g) j) g _ _
    rw [Category.assoc, quotientSheafMap_comp, quotientSheafMap_comp]
    exact quotientSheafMap_eq_of_obj_eq J F (PreRelation.restrict j g) j
      ((cFwd ≫ pullback.snd (prod.map (g ≫ e) (g ≫ e)) jG) ≫ rInv)
      (pullback.snd (prod.map g g) j) ((𝟙 U' ≫ g ≫ e) ≫ eInv) g _ _ _ _
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id])
  have hmap : (isoRest.hom.hom ≫ (restrictQuotientSheafMap J F jG (g ≫ e)).hom) ≫
      isoBase.hom.hom = (restrictQuotientSheafMap J F j g).hom := by
    rw [Category.assoc]
    exact congrArg (fun x => x.hom) hfactor
  have : IsIso isoRest.hom.hom := (ObjectProperty.isIso_hom_iff _).2 inferInstance
  have : IsIso isoBase.hom.hom := (ObjectProperty.isIso_hom_iff _).2 inferInstance
  rw [← hmap]
  exact MorphismProperty.RespectsIso.postcomp P isoBase.hom.hom _
    (MorphismProperty.RespectsIso.precomp P isoRest.hom.hom _ h)

/-- **Stacks 02WU.** Let `j = (t, s) : R ⟶ U ×_S U` be an equivalence relation of schemes over
`S` whose source and target maps are surjective, flat and locally of finite presentation, and
let `g : U' ⟶ U` be flat and locally of finite presentation. The induced map `U'/R' ⟶ U/R` of
quotient sheaves on the big fppf site over `S` is representable and an open immersion. -/
@[stacks 02WU]
theorem isOpenImmersion_restrictedQuotientMap (B : BigFppfSite.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (j : PreRelation R U) (g : U' ⟶ U) [IsEquivalenceRelation j.target j.source]
    (hs_surj : Surjective j.source.left) (ht_surj : Surjective j.target.left)
    (hs_flat : Flat j.source.left) (ht_flat : Flat j.target.left)
    (hs_lfp : LocallyOfFinitePresentation j.source.left)
    (ht_lfp : LocallyOfFinitePresentation j.target.left)
    (hg_flat : Flat g.left) (hg_lfp : LocallyOfFinitePresentation g.left) :
    Space.IsOpenImmersion B S hS
      (restrictQuotientSheafMap (BigFppfOver.topology B S hS)
        (CategoryTheory.Over.post (X := B.obj hS) B.inclusion) j g).hom := by
  classical
  let G := groupoidSchemeOfIsEquivalenceRelation j
  have hG : ExtendsRelation j G := groupoidSchemeOfIsEquivalenceRelation_extendsRelation j
  obtain ⟨⟨hGs_surj, hGs_flat, hGs_lfp⟩, hGt_surj, hGt_flat, hGt_lfp⟩ :=
    flat_locallyOfFinitePresentation_surjective_of_extendsRelation j G hG hs_surj ht_surj
      hs_flat ht_flat hs_lfp ht_lfp
  have : Surjective G.source.left := hGs_surj
  have : Flat G.source.left := hGs_flat
  have : LocallyOfFinitePresentation G.source.left := hGs_lfp
  have : Surjective G.target.left := hGt_surj
  have : Flat G.target.left := hGt_flat
  have : LocallyOfFinitePresentation G.target.left := hGt_lfp
  let e : U ⟶ G.objects := eqToHom hG.objects_eq.symm
  have : IsIso e.left := by
    simpa only [CategoryTheory.Over.forget_map] using
      (show IsIso ((CategoryTheory.Over.forget S).map e) from inferInstance)
  let gg : U' ⟶ G.objects := g ≫ e
  have : Flat gg.left := inferInstanceAs (Flat (g.left ≫ e.left))
  have : LocallyOfFinitePresentation gg.left :=
    inferInstanceAs (LocallyOfFinitePresentation (g.left ≫ e.left))
  -- The reach map of `gg`; the saturation of `gg` is its image.
  let q : pullback gg G.target ⟶ G.objects := GroupoidScheme.restrictionReachMap G gg
  have hq := flat_locallyOfFinitePresentation_pullbackSnd_comp_source G gg
  have : Flat q.left := hq.1
  have : LocallyOfFinitePresentation q.left := hq.2
  let W : G.objects.left.Opens := ⟨Set.range q.left.base, q.left.isOpenMap.isOpen_range⟩
  have hW : Set.range q.left.base ⊆ Set.range W.ι.base := by simp [W]
  have hWsurj : Set.range W.ι.base ⊆ Set.range q.left.base := by simp [W]
  let Wover : Over S := CategoryTheory.Over.mk (W.ι ≫ G.objects.hom)
  let i : Wover ⟶ G.objects := CategoryTheory.Over.homMk W.ι (by simp [Wover])
  have : IsOpenImmersion i.left := by
    show IsOpenImmersion W.ι; infer_instance
  let kScheme : (pullback gg G.target).left ⟶ Wover.left := IsOpenImmersion.lift W.ι q.left hW
  let k : pullback gg G.target ⟶ Wover := CategoryTheory.Over.homMk kScheme (by
    show kScheme ≫ W.ι ≫ G.objects.hom = (pullback gg G.target).hom
    calc kScheme ≫ W.ι ≫ G.objects.hom = q.left ≫ G.objects.hom := by
          rw [← Category.assoc, IsOpenImmersion.lift_fac (f := W.ι) (g := q.left) hW]
      _ = (pullback gg G.target).hom := q.w)
  have hk : k ≫ i = q := by
    ext
    show kScheme ≫ W.ι = q.left
    exact IsOpenImmersion.lift_fac (f := W.ι) (g := q.left) hW
  have hcore := corestriction_flat_locallyOfFinitePresentation_surjective q.left W hW hWsurj
  have : Flat k.left := by change Flat kScheme; exact hcore.1
  have : LocallyOfFinitePresentation k.left := by
    show LocallyOfFinitePresentation kScheme; exact hcore.2.1
  have : Surjective k.left := by change Surjective kScheme; exact hcore.2.2
  have hrange : Set.range i.left.base = Set.range q.left.base := by
    show Set.range W.ι.base = Set.range q.left.base
    rw [Scheme.Opens.range_ι]
    rfl
  have hGroup := GroupoidScheme.isOpenImmersion_restrictionQuotientMap_of_open_image B S hS G
    gg i k hk hrange (isLocallySurjective_presheafToSheaf_map_yoneda_map B hS k)
  rw [GroupoidScheme.restrictionQuotientMap_eq] at hGroup
  exact restrictQuotientSheafMap_property_of_extendsRelation _ _ _ j G hG g
    (property_hom_of_isoHom_comp _ _ _ _ hGroup)

end AlgebraicGeometry

end
