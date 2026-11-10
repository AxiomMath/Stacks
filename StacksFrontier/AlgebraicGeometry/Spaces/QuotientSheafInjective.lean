module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injectivity of the maps between quotient sheaves

The quotient sheaf `U/R` of a pre-relation is the sheafification of a pointwise coequalizer.
This file computes the *sections* of that coequalizer when the pre-relation is a
pre-equivalence relation — two points of `U` have the same image exactly when they are
related, with no further equivalence closure — and draws the injectivity consequences for a
morphism of pre-relations, for the restriction of a pre-relation along a morphism, and for the
restriction of a groupoid scheme.

Three statements of the source are reached:

* equality in the quotient *presheaf* of a pre-equivalence relation is the relation itself:
  the pointwise half of Groupoids, Lemma **045Y**;
* the restriction `U'/R' → U/R` of a pre-equivalence relation along `g : U' → U` is injective,
  with no hypothesis on `g`: the injectivity half of Groupoids, Lemma **045Z**;
* the restriction `U'/R' → U/R` of a *groupoid scheme* along `g` is injective: the injectivity
  half of Groupoids, Lemma **02VH**.

## Main definitions

* `Stacks.Groupoids.relQuotientPresheaf`: the presheaf whose sections over `T` are the
  `F.obj T`-points of `U` modulo the relation induced by a pre-equivalence relation.
* `AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap`: the map of quotient sheaves induced
  by the canonical morphism from a restricted groupoid scheme to the original one.
* `AlgebraicGeometry.GroupoidScheme.restrictionReachMap`: the map sending an arrow whose target
  lifts along `g` to its source.

## Main results

* `Stacks.Groupoids.rel_of_toQuotientPresheaf_apply_eq`: two points of `U` with the same
  image in the quotient presheaf of a pre-equivalence relation are related, with no
  equivalence closure taken.
* `Stacks.Groupoids.mono_quotientPresheafMap_of_relLift` and
  `Stacks.Groupoids.mono_quotientSheafMap_of_relLift`: a morphism of pre-relations whose
  target relation reflects along the map on bases induces a monomorphism of quotient
  presheaves, hence of quotient sheaves.
* `Stacks.Groupoids.mono_quotientSheafMap_restrict`: the injectivity half of Groupoids,
  Lemma **045Z**.
* `AlgebraicGeometry.GroupoidScheme.mono_restrictionQuotientMap`: the injectivity half of
  Groupoids, Lemma **02VH**.

## Implementation notes

Injectivity needs *no* local description of sheafification. The quotient presheaf of a
pre-equivalence relation is computed here as a quotient of a set of points, which is
elementary; the map of quotient *presheaves* is then shown to be pointwise injective; and
`Stacks.Groupoids.quotientSheafMap` is by construction the sheafification of that map, so
Mathlib's `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape` applied to
`CategoryTheory.presheafToSheaf` — left exact for `HasSheafify` — carries the monomorphism
across. In particular the two universes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf` are left free, unlike for the
surjectivity half in `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocallySurjective`,
which is constrained by Mathlib's locally-surjective-sheafification instance.

The quotient presheaf is a coequalizer of presheaves of types and is therefore *not*
described here by iterating the relation: for a pre-equivalence relation the relation is
already transitive, so the comparison map to the quotient by the relation is used only in the
direction that pushes an equality in the coequalizer forward, which needs nothing but the
universal property.

For a groupoid scheme, injectivity of `U'/R' → U/R` reduces to the statement that an arrow of
`G` between two points lifting along `g` is itself a point of the arrow scheme of the
restriction. That is read off the explicit fibre-product description of
`AlgebraicGeometry.restrictionArrows` recorded in
`AlgebraicGeometry.GroupoidScheme.Restriction`, so the general criterion applies with the
groupoid's own pre-equivalence relation; no comparison of the restricted groupoid with the
restricted pre-relation is needed.

No Stacks tag attribute is placed on anything in this file. Tags **02VH**, **045Z** and
**045Y** all belong to Groupoids, Chapter 39; the declarations are left unregistered here. In
any case only one of the two conclusions of 02VH and of 045Z is proved here, so neither tag
would be earned by this file alone: the surjectivity conclusions need the companion file named
above.

## References

* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
* [Stacks Project, Tag 045Y](https://stacks.math.columbia.edu/tag/045Y)
* [Stacks Project, Tag 02V8](https://stacks.math.columbia.edu/tag/02V8)
* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 0232](https://stacks.math.columbia.edu/tag/0232)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]
variable (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U)

/-- The `F.obj T`-points of `U` modulo the relation induced by the pre-relation `j`. -/
abbrev relClasses (T : C) : Type u := Quot (j.Rel (T := F.obj T))

/-- Precomposition with `F.map f` descends to relation classes: if two points are related by
a point of `R`, their restrictions are related by its restriction. -/
def relClassesMap {T T' : C} (f : T ⟶ T') : relClasses F j T' → relClasses F j T :=
  Quot.lift (fun a => Quot.mk _ (F.map f ≫ a)) (by
    rintro a b ⟨r, hrt, hrs⟩
    exact Quot.sound ⟨F.map f ≫ r, by rw [Category.assoc, hrt],
      by rw [Category.assoc, hrs]⟩)

/-- `relClassesMap` sends the class of a point `a` to the class of its restriction
`F.map f ≫ a`. -/
@[simp]
theorem relClassesMap_mk {T T' : C} (f : T ⟶ T') (a : F.obj T' ⟶ U) :
    relClassesMap F j f (Quot.mk _ a) = Quot.mk _ (F.map f ≫ a) := rfl

/-- The presheaf of relation classes of a pre-relation. For a pre-equivalence relation it is
the quotient presheaf; see `Stacks.Groupoids.toQuotientPresheaf_apply_eq_iff_related`. -/
@[sga "3 IV 3.1.2", sga "3 IV 4.4.9" "The presheaf i(X)/i(R)"]
def relQuotientPresheaf : Cᵒᵖ ⥤ Type u where
  obj T := relClasses F j T.unop
  map {_ _} f := TypeCat.ofHom (relClassesMap F j f.unop)
  map_id T := by
    apply TypeCat.homEquiv.injective
    funext a
    induction a using Quot.ind with
    | mk a => simp
  map_comp {T T' T''} f g := by
    apply TypeCat.homEquiv.injective
    funext a
    induction a using Quot.ind with
    | mk a => simp [Category.assoc]

/-- The sections of `relQuotientPresheaf` over `T` are the relation classes of `F.obj T`-points. -/
@[simp]
theorem relQuotientPresheaf_obj (T : Cᵒᵖ) :
    (relQuotientPresheaf F j).obj T = relClasses F j T.unop := rfl

/-- The projection of the functor of points of `U` onto the presheaf of relation classes. -/
def toRelQuotientPresheaf : points F U ⟶ relQuotientPresheaf F j where
  app T := TypeCat.ofHom (fun a => Quot.mk (j.Rel (T := F.obj T.unop)) a)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext a
    rfl

/-- `toRelQuotientPresheaf` sends a point to its relation class. -/
@[simp]
theorem toRelQuotientPresheaf_app (T : C) (a : F.obj T ⟶ U) :
    (toRelQuotientPresheaf F j).app (op T) a = Quot.mk _ a := rfl

/-- For a pre-equivalence relation, the projection onto relation classes identifies the source
and the target of a point of `R`. -/
theorem sourceMap_toRelQuotientPresheaf (hj : IsPreEquivalenceRelation j) :
    sourceMap F j ≫ toRelQuotientPresheaf F j =
      targetMap F j ≫ toRelQuotientPresheaf F j := by
  ext T r
  exact Quot.sound ((hj (F.obj T.unop)).symm ⟨r, rfl, rfl⟩)

/-- The comparison map from the quotient presheaf to the presheaf of relation classes. -/
noncomputable def relQuotientPresheafDesc (hj : IsPreEquivalenceRelation j) :
    quotientPresheaf F j ⟶ relQuotientPresheaf F j :=
  coequalizer.desc (toRelQuotientPresheaf F j) (sourceMap_toRelQuotientPresheaf F j hj)

/-- The comparison map `relQuotientPresheafDesc` restricts, along the projection onto the
quotient presheaf, to the projection onto relation classes. -/
@[simp]
theorem toQuotientPresheaf_relQuotientPresheafDesc (hj : IsPreEquivalenceRelation j) :
    toQuotientPresheaf F j ≫ relQuotientPresheafDesc F j hj = toRelQuotientPresheaf F j :=
  coequalizer.π_desc _ _

/-- Related points have the same image in the quotient presheaf. This needs no hypothesis on
the pre-relation: it is the coequalizer relation. -/
theorem toQuotientPresheaf_apply_eq_of_rel (T : C) {a b : F.obj T ⟶ U} (h : j.Rel a b) :
    (toQuotientPresheaf F j).app (op T) a = (toQuotientPresheaf F j).app (op T) b := by
  obtain ⟨r, hrt, hrs⟩ := h
  have h0 := NatTrans.congr_app
    (coequalizer.condition (sourceMap F j) (targetMap F j)) (op T)
  have hc := congrArg (fun k => k r) h0
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hc
  rw [← hrt, ← hrs]
  exact hc.symm

/-- For a pre-equivalence relation, points with the same image in the quotient presheaf are
related. -/
@[sga "3 IV 3.1.2" "partial"]
theorem rel_of_toQuotientPresheaf_apply_eq (hj : IsPreEquivalenceRelation j)
    (T : C) {a b : F.obj T ⟶ U}
    (h : (toQuotientPresheaf F j).app (op T) a = (toQuotientPresheaf F j).app (op T) b) :
    j.Rel a b := by
  have key : Quot.mk (j.Rel (T := F.obj T)) a = Quot.mk (j.Rel (T := F.obj T)) b := by
    have ha := NatTrans.congr_app (toQuotientPresheaf_relQuotientPresheafDesc F j hj) (op T)
    have hA := congrArg (fun k => k a) ha
    have hB := congrArg (fun k => k b) ha
    simp only [NatTrans.comp_app] at hA hB
    rw [← toRelQuotientPresheaf_app F j T a, ← toRelQuotientPresheaf_app F j T b, ← hA, ← hB]
    simp only [ConcreteCategory.comp_apply]
    rw [h]
  exact (hj (F.obj T)).eqvGen_iff.mp (Quot.eqvGen_exact key)


section Map

variable {R' U' : Over S} (j' : PreRelation R' U') (r : R ⟶ R') (f : U ⟶ U')
  (hs : r ≫ j'.source = j.source ≫ f) (ht : r ≫ j'.target = j.target ≫ f)

/-- The induced morphism of quotient presheaves commutes with the canonical projections. -/
theorem toQuotientPresheaf_comp_quotientPresheafMap :
    toQuotientPresheaf F j ≫ quotientPresheafMap F j j' r f hs ht =
      F.op.whiskerLeft (yoneda.map f) ≫ toQuotientPresheaf F j' := by
  dsimp [quotientPresheafMap, toQuotientPresheaf]
  rw [coequalizer.π_desc]

/-- A morphism of pre-relations whose map on bases reflects the target relation into the
source relation induces a monomorphism of quotient presheaves. -/
theorem mono_quotientPresheafMap_of_relLift (hj' : IsPreEquivalenceRelation j')
    (hlift : ∀ (T : C) (a b : F.obj T ⟶ U), j'.Rel (a ≫ f) (b ≫ f) → j.Rel a b) :
    Mono (quotientPresheafMap F j j' r f hs ht) := by
  rw [NatTrans.mono_iff_mono_app]
  intro X
  obtain ⟨T⟩ := X
  rw [CategoryTheory.mono_iff_injective]
  intro x y hxy
  obtain ⟨a, rfl⟩ := quotientProjection_surjective F j (op T) x
  obtain ⟨b, rfl⟩ := quotientProjection_surjective F j (op T) y
  have key : ∀ c : F.obj T ⟶ U, (quotientPresheafMap F j j' r f hs ht).app (op T)
      ((toQuotientPresheaf F j).app (op T) c) = (toQuotientPresheaf F j').app (op T) (c ≫ f) :=
    fun c => congrArg (fun k => k c) (NatTrans.congr_app
      (toQuotientPresheaf_comp_quotientPresheafMap F j j' r f hs ht) (op T))
  have hab : (toQuotientPresheaf F j').app (op T) (a ≫ f) =
      (toQuotientPresheaf F j').app (op T) (b ≫ f) := by
    rw [← key, ← key]; exact hxy
  exact toQuotientPresheaf_apply_eq_of_rel F j T
    (hlift T a b (rel_of_toQuotientPresheaf_apply_eq F j' hj' T hab))

/-- The same morphism of pre-relations induces a monomorphism of quotient sheaves:
sheafification is left exact, hence preserves monomorphisms. -/
theorem mono_quotientSheafMap_of_relLift (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (hj' : IsPreEquivalenceRelation j')
    (hlift : ∀ (T : C) (a b : F.obj T ⟶ U), j'.Rel (a ≫ f) (b ≫ f) → j.Rel a b) :
    Mono (quotientSheafMap J F j j' r f hs ht) := by
  have : Mono (quotientPresheafMap F j j' r f hs ht) :=
    mono_quotientPresheafMap_of_relLift F j j' r f hs ht hj' hlift
  exact inferInstanceAs
    (Mono ((presheafToSheaf J (Type u)).map (quotientPresheafMap F j j' r f hs ht)))

end Map

/-- Restriction of a pre-relation along `g` reflects the relation on points: an arrow of `j`
between two points of the form `x ≫ g`, `y ≫ g` is an arrow of the restriction between `x`
and `y`. -/
theorem rel_restrict_of_rel_comp {U'' : Over S} (g : U'' ⟶ U)
    {T : Over S} {x y : T ⟶ U''} (h : j.Rel (x ≫ g) (y ≫ g)) :
    (AlgebraicGeometry.PreRelation.restrict j g).Rel x y := by
  obtain ⟨r, hr₁, hr₂⟩ := h
  have hcomm : prod.lift x y ≫ prod.map g g = r ≫ j := by
    apply prod.hom_ext
    all_goals simp [Category.assoc, hr₁, hr₂]
  refine ⟨pullback.lift (prod.lift x y) r hcomm, ?_, ?_⟩
  all_goals rw [← Category.assoc, pullback.lift_fst]; simp

/-- **Groupoids, Lemma 045Z, injectivity.** Let `j : R → U ×_S U` be a pre-equivalence
relation and `g : U' → U` a morphism, and let `j'` be the restriction of `j` to `U'`. Then the
induced map of quotient sheaves `U'/R' → U/R` is a monomorphism, with no hypothesis on `g`.

This is one of that lemma's two conclusions; surjectivity of the same map under a surjectivity
hypothesis on `g` is
`Stacks.Groupoids.isLocallySurjective_quotientSheafMap_restrict`. -/
@[sga "3 IV 4.4.10" "Monomorphism clause"]
theorem mono_quotientSheafMap_restrict (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (hj : IsPreEquivalenceRelation j)
    {U'' : Over S} (g : U'' ⟶ U) :
    Mono (quotientSheafMap J F (AlgebraicGeometry.PreRelation.restrict j g) j
      (pullback.snd (prod.map g g) j) g
      (restrict_pullback_snd_source j g) (restrict_pullback_snd_target j g)) :=
  mono_quotientSheafMap_of_relLift F _ j _ g _ _ J hj
    (fun _ _ _ h => rel_restrict_of_rel_comp j g h)

section Groupoid

variable (G : GroupoidScheme S) {U₀ : Over S} (g : U₀ ⟶ G.objects)
  (H : AlgebraicGeometry.GroupoidScheme.Restriction G g)

/-- Transporting along the identification of the arrow scheme of a restriction turns its
target map into the projection `AlgebraicGeometry.restrictionTarget`. -/
theorem restriction_transport_target {T : Over S} (pt : T ⟶ restrictionArrows G g) :
    (pt ≫ eqToHom H.arrows_eq.symm) ≫ H.groupoid.target =
      pt ≫ restrictionTarget G g ≫ eqToHom H.objects_eq.symm := by
  rw [H.target_eq, Category.assoc, ← Category.assoc (eqToHom H.arrows_eq.symm),
    eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- Transporting along the identification of the arrow scheme of a restriction turns its
source map into the projection `AlgebraicGeometry.restrictionSource`. -/
theorem restriction_transport_source {T : Over S} (pt : T ⟶ restrictionArrows G g) :
    (pt ≫ eqToHom H.arrows_eq.symm) ≫ H.groupoid.source =
      pt ≫ restrictionSource G g ≫ eqToHom H.objects_eq.symm := by
  rw [H.source_eq, Category.assoc, ← Category.assoc (eqToHom H.arrows_eq.symm),
    eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- A `T`-point of the arrow scheme of a restriction is a triple: a lift of the target, an
arrow of `G`, and a lift of the source. -/
theorem exists_restrictionArrows_point {T : Over S} (a b : T ⟶ U₀) (q : T ⟶ G.arrows)
    (hqt : a ≫ g = q ≫ G.target) (hqs : q ≫ G.source = b ≫ g) :
    ∃ pt : T ⟶ restrictionArrows G g,
      pt ≫ restrictionTarget G g = a ∧ pt ≫ restrictionSource G g = b := by
  change ∃ pt : T ⟶ pullback (pullback.snd g G.target) (pullback.fst G.source g),
      pt ≫ (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
        pullback.fst g G.target) = a ∧
      pt ≫ (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) ≫
        pullback.snd G.source g) = b
  refine ⟨pullback.lift (pullback.lift a q hqt) (pullback.lift q b hqs)
    (by rw [pullback.lift_snd, pullback.lift_fst]), ?_, ?_⟩
  · rw [pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [pullback.lift_snd_assoc, pullback.lift_snd]

/-- Two points of the restricted groupoid which are related in `G` are related in the
restriction: the arrow of `G` realising the relation is itself an arrow of the restriction,
because both of its ends lift along `g`. -/
theorem rel_restriction_of_rel_mapObjects {T : Over S} {a b : T ⟶ H.groupoid.objects}
    (h : (groupoidPreRelation G).Rel (a ≫ H.hom.mapObjects) (b ≫ H.hom.mapObjects)) :
    (groupoidPreRelation H.groupoid).Rel a b := by
  obtain ⟨q, hqt, hqs⟩ := h
  simp only [groupoidPreRelation, PreRelation.target, PreRelation.source,
    prod.lift_fst, prod.lift_snd, H.mapObjects_eq] at hqt hqs
  obtain ⟨pt, hT, hS⟩ := exists_restrictionArrows_point G g
    (a ≫ eqToHom H.objects_eq) (b ≫ eqToHom H.objects_eq) q
    (by rw [Category.assoc]; exact hqt.symm) (by rw [Category.assoc]; exact hqs)
  have aux : ∀ (p : H.groupoid.arrows ⟶ H.groupoid.objects) (p' : restrictionArrows G g ⟶ U₀)
      (c : T ⟶ H.groupoid.objects),
      (pt ≫ eqToHom H.arrows_eq.symm) ≫ p = pt ≫ p' ≫ eqToHom H.objects_eq.symm →
      pt ≫ p' = c ≫ eqToHom H.objects_eq → (pt ≫ eqToHom H.arrows_eq.symm) ≫ p = c := by
    intro p p' c h₁ h₂
    rw [h₁, ← Category.assoc, h₂, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact ⟨pt ≫ eqToHom H.arrows_eq.symm,
    aux _ _ _ (by simpa [groupoidPreRelation, PreRelation.target] using
      restriction_transport_target G g H pt) hT,
    aux _ _ _ (by simpa [groupoidPreRelation, PreRelation.source] using
      restriction_transport_source G g H pt) hS⟩

/-- The restricting map factors through the reach map, by way of the neutral element: so a
surjectivity hypothesis on `g` implies the one on
`AlgebraicGeometry.GroupoidScheme.restrictionReachMap`. -/
theorem restrictionReachMap_section :
    pullback.lift (𝟙 U₀) (g ≫ G.identity) (by simp [Category.assoc, G.target_identity]) ≫
      AlgebraicGeometry.GroupoidScheme.restrictionReachMap G g = g := by
  rw [AlgebraicGeometry.GroupoidScheme.restrictionReachMap, ← Category.assoc, pullback.lift_snd]
  simp [Category.assoc, G.source_identity]

end Groupoid

end Stacks.Groupoids

end
