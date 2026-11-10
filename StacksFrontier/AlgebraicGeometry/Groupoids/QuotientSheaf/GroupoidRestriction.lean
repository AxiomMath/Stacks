module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.Functoriality
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction

/-!
# Quotient sheaves of restricted groupoid schemes

Let `G` be a groupoid scheme over `S` with scheme of objects `U` and scheme of arrows `R`,
and let `g : U' ⟶ U` be a morphism of `S`-schemes. Restricting `G` along `g` gives a groupoid
scheme with objects `U'` and a canonical morphism to `G`, hence a map `U'/R' ⟶ U/R` of
quotient sheaves. That map is always injective, and it is bijective as soon as the map
`U' ×_{g, U, t} R ⟶ U` reading off the source of an arrow whose target lifts along `g`
induces a surjection of sheaves.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap` is the induced map `U'/R' ⟶ U/R`.
* `AlgebraicGeometry.GroupoidScheme.restrictionReachMap` is the map
  `U' ×_{g, U, t} R ⟶ U` sending an arrow whose target lifts along `g` to its source.
* `AlgebraicGeometry.GroupoidScheme.restrictionQuotientIso` identifies the quotient sheaf of a
  restricted groupoid scheme with the quotient sheaf of the restriction of the underlying
  pre-relation.

## Main results

* `AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap_eq` reads the induced map as the
  one induced by the restriction of the underlying pre-relation.
* `AlgebraicGeometry.GroupoidScheme.mono_restrictionQuotientMap` is injectivity.
* `AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_reach` is bijectivity
  under local surjectivity of the reach map, and
  `AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_objects` is the special
  case where `g` itself is locally surjective.
* `AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_reach_cover` and
  `AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_objects_cover` are the two
  criteria phrased by a singleton covering of the site.

## Implementation notes

The site is presented by an arbitrary functor `F : C ⥤ Over S` into `S`-schemes, which covers
the big and small Zariski, étale, fppf, smooth and syntomic sites at once. A surjection of
sheaves is expressed as local surjectivity of the corresponding map of sheafified functors of
points.

Injectivity is not proved again: the arrow scheme of the restricted groupoid is identified
with the restriction of the pre-relation `(t, s) : R ⟶ U ×_S U` along `g`, so that the
induced map of quotient sheaves is the one of
`Stacks.Groupoids.restrictQuotientSheafMap` up to an isomorphism of quotient sheaves, and
`Stacks.Groupoids.restrictQuotientSheafMap_mono` applies because the pre-relation underlying a
groupoid scheme is a pre-equivalence relation. The identification is needed because a
restriction is given abstractly, by its structure maps together with equalities identifying
them with the displayed fibre products.

Surjectivity is proved directly rather than deduced from
`Stacks.Groupoids.restrictQuotientSheafMap_isIso`, whose hypothesis is local surjectivity of
`g`: the reach map is weaker, and the point of the proof is that the two composites
`U' ×_{g, U, t} R ⟶ U ⟶ U/R` through the source and through the target agree, the target one
factoring through `U'/R'`.

For the two singleton-covering criteria, fullness of the site functor is what lifts a morphism
of schemes between objects of the site to a morphism of the site.

## References

* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u v w

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- If a morphism of `S`-schemes between objects of the site generates a covering sieve, then
it induces a locally surjective map of sheafified functors of points. -/
private theorem isLocallySurjective_sheafifyMap_yonedaMap_of_singleton_cover
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S) (hF : F.Full)
    {A B : Over S} (f : A ⟶ B) (X Y : C) (eA : F.obj X ≅ A) (eB : F.obj Y ≅ B)
    (a : X ⟶ Y) (ha : F.map a ≫ eB.hom = eA.hom ≫ f)
    (hcover : Sieve.generate (Presieve.singleton a) ∈ J Y) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map (F.op.whiskerLeft (yoneda.map f))) := by
  let _ : F.Full := hF
  have _ : Presheaf.IsLocallySurjective J (F.op.whiskerLeft (yoneda.map f)) := by
    refine ⟨?_⟩
    intro Z s
    let b := F.preimage (s ≫ eB.inv)
    have hb : F.map b = s ≫ eB.inv := by simp [b]
    refine J.superset_covering ?_ (J.pullback_stable b hcover)
    intro W c hc
    change Sieve.generate (Presieve.singleton a) (c ≫ b) at hc
    obtain ⟨X', d, k, hk, hdk⟩ := hc
    obtain ⟨rfl⟩ := hk
    refine ⟨F.map d ≫ eA.hom, ?_⟩
    change (F.map d ≫ eA.hom) ≫ f = F.map c ≫ s
    calc
      (F.map d ≫ eA.hom) ≫ f = F.map d ≫ F.map a ≫ eB.hom := by rw [Category.assoc, ← ha]
      _ = F.map (d ≫ a) ≫ eB.hom := by rw [← Category.assoc, ← Functor.map_comp]
      _ = F.map (c ≫ b) ≫ eB.hom := by rw [hdk]
      _ = (F.map c ≫ F.map b) ≫ eB.hom := by rw [← Functor.map_comp]
      _ = (F.map c ≫ s ≫ eB.inv) ≫ eB.hom := by rw [hb]
      _ = F.map c ≫ s := by simp [Category.assoc]
  let φ := F.op.whiskerLeft (yoneda.map f)
  have _ : Presheaf.IsLocallySurjective J (toSheafify J (F.op ⋙ yoneda.obj A)) :=
    Stacks.Sheafification.isLocallySurjective_toSheafify_type J _
  have _ : Presheaf.IsLocallySurjective J (toSheafify J (F.op ⋙ yoneda.obj B)) :=
    Stacks.Sheafification.isLocallySurjective_toSheafify_type J _
  have _ : Presheaf.IsLocallySurjective J
      (toSheafify J (F.op ⋙ yoneda.obj A) ≫
        ((presheafToSheaf J (Type u)).map φ).hom) := by
    rw [show toSheafify J (F.op ⋙ yoneda.obj A) ≫ ((presheafToSheaf J (Type u)).map φ).hom =
      φ ≫ toSheafify J (F.op ⋙ yoneda.obj B) from (toSheafify_naturality J φ).symm]
    infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective J
    (toSheafify J (F.op ⋙ yoneda.obj A)) ((presheafToSheaf J (Type u)).map φ).hom

namespace GroupoidScheme

/-- The map of quotient sheaves induced by the canonical morphism from a restricted groupoid
scheme to the original one. -/
noncomputable abbrev restrictionQuotientMap (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g) :
    quotientSheaf J F (groupoidPreRelation H.groupoid) ⟶
      quotientSheaf J F (groupoidPreRelation G) :=
  quotientSheafMap J F (groupoidPreRelation H.groupoid) (groupoidPreRelation G)
    H.hom.mapArrows H.hom.mapObjects
    (by simpa [groupoidPreRelation, PreRelation.source] using H.hom.map_source)
    (by simpa [groupoidPreRelation, PreRelation.target] using H.hom.map_target)

/-- The source of an arrow of `G` whose target lifts along `g`, as a morphism
`U' ×_{g, U, t} R ⟶ U`. -/
noncomputable abbrev restrictionReachMap (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) : pullback g G.target ⟶ G.objects :=
  pullback.snd g G.target ≫ G.source

/-- The comparison from the arrow scheme of a restricted groupoid to the restriction of the
underlying pre-relation. -/
private noncomputable def restrictionArrowsToRestriction (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    restrictionArrows G g ⟶
      AlgebraicGeometry.PreRelation.restriction (groupoidPreRelation G) g :=
  pullback.lift (prod.lift (restrictionTarget G g) (restrictionSource G g))
    (restrictionArrowsToArrows G g) (by
      simp only [groupoidPreRelation, prod.lift_map, prod.comp_lift,
        ← restriction_condition' G g, restriction_condition G g])

/-- The comparison from the restriction of the pre-relation underlying a groupoid scheme to the
arrow scheme of the restricted groupoid. -/
private noncomputable def restrictionToRestrictionArrows (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    AlgebraicGeometry.PreRelation.restriction (groupoidPreRelation G) g ⟶
      restrictionArrows G g :=
  pullback.lift
    (pullback.lift (pullback.fst (prod.map g g) (groupoidPreRelation G) ≫ prod.fst)
      (pullback.snd (prod.map g g) (groupoidPreRelation G))
      (by
        simpa only [groupoidPreRelation, Category.assoc, prod.map_fst, prod.lift_fst] using
          pullback.condition_assoc (f := prod.map g g) (g := groupoidPreRelation G) prod.fst))
    (pullback.lift (pullback.snd (prod.map g g) (groupoidPreRelation G))
      (pullback.fst (prod.map g g) (groupoidPreRelation G) ≫ prod.snd)
      (by
        simpa only [groupoidPreRelation, Category.assoc, prod.map_snd, prod.lift_snd] using
          (pullback.condition_assoc (f := prod.map g g)
            (g := groupoidPreRelation G) prod.snd).symm))
    (by simp only [pullback.lift_snd, pullback.lift_fst])

/-- The arrow scheme of the restriction of a groupoid scheme along `g` is the restriction along
`g` of the pre-relation underlying that groupoid scheme. -/
private noncomputable def restrictionArrowsIso (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    restrictionArrows G g ≅
      AlgebraicGeometry.PreRelation.restriction (groupoidPreRelation G) g := by
  refine ⟨restrictionArrowsToRestriction G g, restrictionToRestrictionArrows G g, ?_, ?_⟩
  all_goals repeat' (first | apply pullback.hom_ext | apply prod.hom_ext)
  all_goals simp only [restrictionArrows, AlgebraicGeometry.PreRelation.restriction,
    Category.assoc, restrictionToRestrictionArrows, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, restrictionArrowsToRestriction,
    prod.lift_fst, prod.lift_snd, prod.comp_lift, groupoidPreRelation, restrictionTarget,
    restrictionSource, restrictionArrowsToArrows, pullback.condition, Category.id_comp]

/-- Under the identification of arrow schemes, the restricted pre-relation is the pair of the
target and the source of the restricted groupoid. -/
private theorem restrictionArrowsIso_hom_comp_restrict (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    (restrictionArrowsIso G g).hom ≫
        AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g =
      prod.lift (restrictionTarget G g) (restrictionSource G g) := by
  change restrictionArrowsToRestriction G g ≫ _ = _
  exact pullback.lift_fst _ _ _

/-- A structure map of the restricted groupoid, read through the identification of arrow
schemes, is the corresponding projection of the restricted pre-relation. -/
private theorem arrowsEq_comp_restrict_comp (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (H : Restriction G g) (π : U' ⨯ U' ⟶ U') (k : restrictionArrows G g ⟶ U')
    (hk : prod.lift (restrictionTarget G g) (restrictionSource G g) ≫ π = k)
    (m : H.groupoid.arrows ⟶ H.groupoid.objects)
    (hm : m = eqToHom H.arrows_eq ≫ k ≫ eqToHom H.objects_eq.symm) :
    (eqToHom H.arrows_eq ≫ (restrictionArrowsIso G g).hom) ≫
        (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g ≫ π) =
      m ≫ eqToHom H.objects_eq := by
  rw [Category.assoc, ← Category.assoc (restrictionArrowsIso G g).hom,
    restrictionArrowsIso_hom_comp_restrict, hk, hm]
  simp

private theorem restriction_arrowsEq_comp_restrict_target (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (H : Restriction G g) :
    (eqToHom H.arrows_eq ≫ (restrictionArrowsIso G g).hom) ≫
        (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g).target =
      (groupoidPreRelation H.groupoid).target ≫ eqToHom H.objects_eq :=
  arrowsEq_comp_restrict_comp G g H prod.fst _ (prod.lift_fst _ _) _
    (by simpa [groupoidPreRelation, PreRelation.target] using H.target_eq)

private theorem restriction_arrowsEq_comp_restrict_source (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) (H : Restriction G g) :
    (eqToHom H.arrows_eq ≫ (restrictionArrowsIso G g).hom) ≫
        (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g).source =
      (groupoidPreRelation H.groupoid).source ≫ eqToHom H.objects_eq :=
  arrowsEq_comp_restrict_comp G g H prod.snd _ (prod.lift_snd _ _) _
    (by simpa [groupoidPreRelation, PreRelation.source] using H.source_eq)

/-- The quotient sheaf of a restricted groupoid scheme agrees with the quotient sheaf of the
restriction of the pre-relation underlying the original groupoid scheme. -/
@[no_expose]
noncomputable def restrictionQuotientIso (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g) :
    quotientSheaf J F (groupoidPreRelation H.groupoid) ≅
      quotientSheaf J F (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g) := by
  let r := eqToHom H.arrows_eq ≫ (restrictionArrowsIso G g).hom
  let f := eqToHom H.objects_eq
  let rInv := (restrictionArrowsIso G g).inv ≫ eqToHom H.arrows_eq.symm
  let fInv := eqToHom H.objects_eq.symm
  have hr : r ≫ (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g).target =
      (groupoidPreRelation H.groupoid).target ≫ f :=
    restriction_arrowsEq_comp_restrict_target G g H
  have hs : r ≫ (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g).source =
      (groupoidPreRelation H.groupoid).source ≫ f :=
    restriction_arrowsEq_comp_restrict_source G g H
  have hrInv : rInv ≫ (groupoidPreRelation H.groupoid).target =
      (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g).target ≫ fInv := by
    calc
      rInv ≫ (groupoidPreRelation H.groupoid).target =
          rInv ≫ ((groupoidPreRelation H.groupoid).target ≫ f) ≫ fInv := by
        simp [f, fInv, Category.assoc]
      _ = rInv ≫ (r ≫ (AlgebraicGeometry.PreRelation.restrict
          (groupoidPreRelation G) g).target) ≫ fInv := by rw [← hr]
      _ = _ := by
        simp [r, rInv, fInv, groupoidPreRelation, PreRelation.target]
  have hsInv : rInv ≫ (groupoidPreRelation H.groupoid).source =
      (AlgebraicGeometry.PreRelation.restrict (groupoidPreRelation G) g).source ≫ fInv := by
    calc
      rInv ≫ (groupoidPreRelation H.groupoid).source =
          rInv ≫ ((groupoidPreRelation H.groupoid).source ≫ f) ≫ fInv := by
        simp [f, fInv, Category.assoc]
      _ = rInv ≫ (r ≫ (AlgebraicGeometry.PreRelation.restrict
          (groupoidPreRelation G) g).source) ≫ fInv := by rw [← hs]
      _ = _ := by
        simp [r, rInv, fInv, groupoidPreRelation, PreRelation.source]
  exact quotientSheafMapIso J F _ _ r f rInv fInv hs hr hsInv hrInv (by simp [f, fInv])
    (by simp [f, fInv])

/-- The map of quotient sheaves induced by a restriction of groupoid schemes is the map induced
by the restriction of the underlying pre-relation, read through the identification of quotient
sheaves. -/
theorem restrictionQuotientMap_eq (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g) :
    restrictionQuotientMap J F G g H =
      (restrictionQuotientIso J F G g H).hom ≫
        restrictQuotientSheafMap J F (groupoidPreRelation G) g := by
  let jH := groupoidPreRelation H.groupoid
  let jG := groupoidPreRelation G
  let jR := AlgebraicGeometry.PreRelation.restrict jG g
  let r := eqToHom H.arrows_eq ≫ (restrictionArrowsIso G g).hom
  let f := eqToHom H.objects_eq
  have hsrc : r ≫ jR.source = jH.source ≫ f := restriction_arrowsEq_comp_restrict_source G g H
  have htar : r ≫ jR.target = jH.target ≫ f := restriction_arrowsEq_comp_restrict_target G g H
  have hφ : (restrictionQuotientIso J F G g H).hom =
      quotientSheafMap J F jH jR r f hsrc htar := rfl
  have hsr : pullback.snd (prod.map g g) jG ≫ jG.source = jR.source ≫ g := by
    change pullback.snd (prod.map g g) jG ≫ jG ≫ prod.snd =
      (pullback.fst (prod.map g g) jG ≫ prod.snd) ≫ g
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc, prod.map_snd]
  have htr : pullback.snd (prod.map g g) jG ≫ jG.target = jR.target ≫ g := by
    change pullback.snd (prod.map g g) jG ≫ jG ≫ prod.fst =
      (pullback.fst (prod.map g g) jG ≫ prod.fst) ≫ g
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc, prod.map_fst]
  have hfs : (r ≫ pullback.snd (prod.map g g) jG) ≫ jG.source = jH.source ≫ f ≫ g := by
    rw [Category.assoc, hsr, ← Category.assoc, hsrc, Category.assoc]
  have hft : (r ≫ pullback.snd (prod.map g g) jG) ≫ jG.target = jH.target ≫ f ≫ g := by
    rw [Category.assoc, htr, ← Category.assoc, htar, Category.assoc]
  change quotientSheafMap J F jH jG H.hom.mapArrows H.hom.mapObjects _ _ = _
  rw [hφ, restrictQuotientSheafMap,
    quotientSheafMap_comp J F jH jR jG r f hsrc htar
      (pullback.snd (prod.map g g) jG) g hsr htr]
  exact quotientSheafMap_eq_of_obj_eq J F jH jG H.hom.mapArrows
    (r ≫ pullback.snd (prod.map g g) jG) H.hom.mapObjects (f ≫ g) _ _ hfs hft H.mapObjects_eq

private theorem whiskerLeft_restrictionReachMap_comp_toQuotientSheaf
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) :
    F.op.whiskerLeft (yoneda.map (restrictionReachMap G g)) ≫
        toQuotientSheaf J F (groupoidPreRelation G) =
      F.op.whiskerLeft (yoneda.map (pullback.fst g G.target ≫ g)) ≫
        toQuotientSheaf J F (groupoidPreRelation G) := by
  have h := congrArg (fun q => F.op.whiskerLeft (yoneda.map (pullback.snd g G.target)) ≫ q)
    (sourceMap_toQuotientSheaf J F (groupoidPreRelation G))
  simp only [sourceMap, targetMap, groupoidPreRelation, PreRelation.source,
    PreRelation.target, prod.lift_snd, prod.lift_fst] at h
  change (F.op.whiskerLeft (yoneda.map (pullback.snd g G.target)) ≫
      F.op.whiskerLeft (yoneda.map G.source)) ≫ toQuotientSheaf J F (groupoidPreRelation G) =
    (F.op.whiskerLeft (yoneda.map (pullback.snd g G.target)) ≫
      F.op.whiskerLeft (yoneda.map G.target)) ≫ toQuotientSheaf J F (groupoidPreRelation G) at h
  rw [← Functor.whiskerLeft_comp, ← Functor.map_comp] at h
  simpa [restrictionReachMap, Category.assoc, pullback.condition] using h

/-- If the reach map is locally surjective after sheafification, then the map of quotient
sheaves induced by the restriction is an epimorphism. -/
private theorem epi_restrictionQuotientMap_of_reach (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g)
    (hreach : Sheaf.IsLocallySurjective ((presheafToSheaf J (Type u)).map
      (F.op.whiskerLeft (yoneda.map (restrictionReachMap G g))))) :
    Epi (restrictionQuotientMap J F G g H) := by
  let V := pullback g G.target
  let t := pullback.fst g G.target
  let s := restrictionReachMap G g
  let tH := t ≫ eqToHom H.objects_eq.symm
  let jG := groupoidPreRelation G
  let jH := groupoidPreRelation H.groupoid
  let mapS := (presheafToSheaf J (Type u)).map (F.op.whiskerLeft (yoneda.map s))
  let mapT := (presheafToSheaf J (Type u)).map (F.op.whiskerLeft (yoneda.map tH))
  let qG := (presheafToSheaf J (Type u)).map (toQuotientPresheaf F jG)
  let qH := (presheafToSheaf J (Type u)).map (toQuotientPresheaf F jH)
  have hqfac : toQuotientSheaf J F jH ≫ (restrictionQuotientMap J F G g H).hom =
      F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫ toQuotientSheaf J F jG :=
    toQuotientSheaf_comp_quotientSheafMap J F jH jG _ _ _ _
  have hleft : toSheafify J (points F V) ≫ mapS.hom ≫ qG.hom =
      F.op.whiskerLeft (yoneda.map s) ≫ toQuotientSheaf J F jG := by
    change (toSheafify J (points F V) ≫
      sheafifyMap J (F.op.whiskerLeft (yoneda.map s))) ≫ qG.hom = _
    rw [← toSheafify_naturality, Category.assoc,
      toSheafify_comp_sheafifyMap_toQuotientPresheaf]
  have hright : toSheafify J (points F V) ≫
        mapT.hom ≫ qH.hom ≫ (restrictionQuotientMap J F G g H).hom =
      F.op.whiskerLeft (yoneda.map (t ≫ g)) ≫ toQuotientSheaf J F jG := by
    change (toSheafify J (points F V) ≫
      sheafifyMap J (F.op.whiskerLeft (yoneda.map tH))) ≫ qH.hom ≫
        (restrictionQuotientMap J F G g H).hom = _
    rw [← toSheafify_naturality]
    change (F.op.whiskerLeft (yoneda.map tH) ≫
      (toSheafify J (points F H.groupoid.objects) ≫ qH.hom)) ≫
        (restrictionQuotientMap J F G g H).hom = _
    rw [toSheafify_comp_sheafifyMap_toQuotientPresheaf J F jH]
    change F.op.whiskerLeft (yoneda.map tH) ≫
      (toQuotientSheaf J F jH ≫ (restrictionQuotientMap J F G g H).hom) = _
    rw [hqfac, ← Category.assoc, ← Functor.whiskerLeft_comp, ← Functor.map_comp]
    simp [tH, H.mapObjects_eq, Category.assoc]
  have hfac : mapS ≫ qG = mapT ≫ qH ≫ restrictionQuotientMap J F G g H := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (hQ := (quotientSheaf J F jG).property)
    change toSheafify J (points F V) ≫ mapS.hom ≫ qG.hom =
      toSheafify J (points F V) ≫
        mapT.hom ≫ qH.hom ≫ (restrictionQuotientMap J F G g H).hom
    exact hleft.trans
      ((whiskerLeft_restrictionReachMap_comp_toQuotientSheaf J F G g).trans hright.symm)
  have _ : Epi mapS := (Sheaf.isLocallySurjective_iff_epi mapS).mp hreach
  have _ : Epi qG := (Sheaf.isLocallySurjective_iff_epi qG).mp
    (isLocallySurjective_sheafifyMap_toQuotientPresheaf J F jG)
  have _ : Epi qH := (Sheaf.isLocallySurjective_iff_epi qH).mp
    (isLocallySurjective_sheafifyMap_toQuotientPresheaf J F jH)
  have _ : Epi (qH ≫ restrictionQuotientMap J F G g H) := epi_of_epi_fac (h := mapS ≫ qG) hfac.symm
  exact (epi_comp_iff_of_epi qH (restrictionQuotientMap J F G g H)).mp inferInstance

/-- **Stacks 02VH.** The map from the quotient sheaf of a restricted groupoid scheme to the
quotient sheaf of the original one is injective. -/
@[stacks 02VH "injectivity of the quotient map"]
theorem mono_restrictionQuotientMap (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g) :
    Mono (restrictionQuotientMap J F G g H) := by
  rw [restrictionQuotientMap_eq]
  have _ := restrictQuotientSheafMap_mono J F (groupoidPreRelation G) g
    (groupoidPreRelation_isPreEquivalenceRelation G)
  infer_instance

/-- **Stacks 02VH.** If every object is locally the source of an arrow whose target lifts along
`g`, then the map of quotient sheaves induced by the restriction is bijective. -/
@[stacks 02VH "bijectivity when the reach map is surjective"]
theorem isIso_restrictionQuotientMap_of_reach (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g)
    (hreach : Sheaf.IsLocallySurjective ((presheafToSheaf J (Type u)).map
      (F.op.whiskerLeft (yoneda.map (restrictionReachMap G g))))) :
    IsIso (restrictionQuotientMap J F G g H) := by
  have _ : Epi (restrictionQuotientMap J F G g H) :=
    epi_restrictionQuotientMap_of_reach J F G g H hreach
  have _ : Mono (restrictionQuotientMap J F G g H) := mono_restrictionQuotientMap J F G g H
  exact isIso_of_mono_of_epi (restrictionQuotientMap J F G g H)

/-- The reach map is locally surjective as soon as the restricting map is: the identity arrow
at an object of `U'` is a section of it over `g`. -/
private theorem isLocallySurjective_restrictionReachMap_of_objects
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (hg : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map (F.op.whiskerLeft (yoneda.map g)))) :
    Sheaf.IsLocallySurjective ((presheafToSheaf J (Type u)).map
      (F.op.whiskerLeft (yoneda.map (restrictionReachMap G g)))) := by
  let idLift : U' ⟶ pullback g G.target :=
    pullback.lift (𝟙 U') (g ≫ G.identity) (by simp [Category.assoc, G.target_identity])
  have hsection : idLift ≫ restrictionReachMap G g = g := by
    change idLift ≫ pullback.snd g G.target ≫ G.source = g
    rw [← Category.assoc, pullback.lift_snd]
    simp [Category.assoc, G.source_identity]
  have hα : F.op.whiskerLeft (yoneda.map idLift) ≫
      F.op.whiskerLeft (yoneda.map (restrictionReachMap G g)) =
      F.op.whiskerLeft (yoneda.map g) := by
    rw [← Functor.whiskerLeft_comp, ← Functor.map_comp, hsection]
  have hmap := congrArg (presheafToSheaf J (Type u)).map hα
  rw [Functor.map_comp] at hmap
  have hfac := congrArg (fun q => q.hom) hmap
  let _ : Presheaf.IsLocallySurjective J
    (((presheafToSheaf J (Type u)).map (F.op.whiskerLeft (yoneda.map g))).hom) := hg
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac

/-- **Stacks 02VH.** If the restricting map is locally surjective on functors of points, then
the map of quotient sheaves induced by the restriction is bijective. -/
@[stacks 02VH "bijectivity when the restricting map is surjective"]
theorem isIso_restrictionQuotientMap_of_objects (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g)
    (hg : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map (F.op.whiskerLeft (yoneda.map g)))) :
    IsIso (restrictionQuotientMap J F G g H) :=
  isIso_restrictionQuotientMap_of_reach J F G g H
    (isLocallySurjective_restrictionReachMap_of_objects J F G g hg)

/-- **Stacks 02VH.** If the reach map is, up to isomorphisms identifying its source and its
target with objects of the site, a singleton covering, then the map of quotient sheaves induced
by the restriction is bijective. -/
@[stacks 02VH "bijectivity when the reach map is a covering"]
theorem isIso_restrictionQuotientMap_of_reach_cover (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (hF : F.Full) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g)
    (X Y : C) (eX : F.obj X ≅ pullback g G.target) (eY : F.obj Y ≅ G.objects)
    (a : X ⟶ Y) (ha : F.map a ≫ eY.hom = eX.hom ≫ restrictionReachMap G g)
    (hcover : Sieve.generate (Presieve.singleton a) ∈ J Y) :
    IsIso (restrictionQuotientMap J F G g H) :=
  isIso_restrictionQuotientMap_of_reach J F G g H
    (isLocallySurjective_sheafifyMap_yonedaMap_of_singleton_cover J F hF
      (restrictionReachMap G g) X Y eX eY a ha hcover)

/-- **Stacks 02VH.** If the restricting map is, up to isomorphisms identifying its source and
its target with objects of the site, a singleton covering, then the map of quotient sheaves
induced by the restriction is bijective. -/
@[stacks 02VH "bijectivity when the restricting map is a covering"]
theorem isIso_restrictionQuotientMap_of_objects_cover (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (hF : F.Full) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g)
    (X Y : C) (eX : F.obj X ≅ U') (eY : F.obj Y ≅ G.objects)
    (a : X ⟶ Y) (ha : F.map a ≫ eY.hom = eX.hom ≫ g)
    (hcover : Sieve.generate (Presieve.singleton a) ∈ J Y) :
    IsIso (restrictionQuotientMap J F G g H) :=
  isIso_restrictionQuotientMap_of_objects J F G g H
    (isLocallySurjective_sheafifyMap_yonedaMap_of_singleton_cover J F hF g X Y eX eY a ha
      hcover)

end GroupoidScheme

end AlgebraicGeometry

end
