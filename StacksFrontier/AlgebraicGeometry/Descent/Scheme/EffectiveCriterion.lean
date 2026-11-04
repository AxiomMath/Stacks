module

public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GluingPoints
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData

/-!
# A criterion for a descent datum of schemes to be effective

A descent datum relative to a single morphism `a : X ⟶ S` is effective when it is isomorphic to
the canonical descent datum of a scheme over `S`.  That definition quantifies over the whole
category of descent data, so to verify it one has to produce a morphism of descent data, which
means producing its compatibility square in the category of products in `Over S`.  This file
turns that into three pieces of concrete geometry: a scheme `U` over `S`, a morphism from the
underlying scheme of the datum to `U` making it a fibre product `X ×_S U`, and the statement
that the two pullbacks of that morphism to `V ×_S X` agree.

## Main definitions

* `AlgebraicGeometry.DescentData.srcPullbackMap` and
  `AlgebraicGeometry.DescentData.tgtPullbackMap` are the maps induced on the source and the
  target of the gluing isomorphisms by a morphism of the underlying schemes.
* `AlgebraicGeometry.DescentData.homOfGluingPullback` and
  `AlgebraicGeometry.DescentData.isoOfGluingPullback` build a morphism, respectively an
  isomorphism, of descent data from a morphism of the underlying schemes.
* `AlgebraicGeometry.DescentData.canonicalProjection` is the projection of the canonical
  descent datum of `U` onto `U`.

## Main results

* `AlgebraicGeometry.DescentData.hom_comm_iff_gluingPullback` identifies the compatibility
  condition on a morphism of descent data with its fibre-product form.
* `AlgebraicGeometry.DescentData.canonicalFunctor_gluingPullbackIso_hom_snd_projection`:
  the gluing isomorphism of a canonical descent datum carries the projection onto `U` of the
  second factor to the projection of the first.  This is the invariance that the criterion asks
  for, and it is what makes the criterion non-vacuous.
* `AlgebraicGeometry.DescentData.isEffective_of_isPullback`: **the criterion.** A descent datum
  relative to `a : X ⟶ S` is effective as soon as there are a scheme `U` over `S` and a morphism
  `φ` from the underlying scheme of the datum to `U` which exhibits the datum as `X ×_S U` and
  whose two pullbacks to the fibre product agree.
* `AlgebraicGeometry.DescentData.isEffective_of_isPullback_prod` is the same criterion with the
  invariance written on the products taken in `Over S`.
* `AlgebraicGeometry.DescentData.isEffective_canonicalFunctor_obj` applies the criterion to a
  canonical descent datum, which is what shows that its hypotheses are satisfiable.

That a gluing isomorphism, written on the literal fibre products, preserves the two base
components is used throughout and is not proved here: it is
`AlgebraicGeometry.DescentData.gluingPullbackIso_hom_fst'` and
`AlgebraicGeometry.DescentData.gluingPullbackIso_hom_snd` of
`StacksFrontier/AlgebraicGeometry/BoundedFibreDescent/GluingPoints.lean`, which this module
imports.  It carried a second declaration of each until they were merged onto those.

## Implementation notes

A descent datum for a single morphism is a `Unit`-indexed `AlgebraicGeometry.DescentData`, so a
morphism of such data is one morphism `u` of schemes over `X` together with one compatibility
square.  That square lives over the product `X ⨯ X` taken in `Over S`;
`AlgebraicGeometry.DescentData.hom_comm_iff_gluingPullback` moves it to the literal fibre
product `X ×_S X` by conjugating with `CategoryTheory.Over.prodLeftIsoPullback`, which is an
isomorphism, so the two forms are equivalent and the fibre-product one can be used to *build*
the morphism and not only to read it off.

The canonical descent datum of `U` is the pullback of its trivial datum, so its gluing
isomorphism is described by `AlgebraicGeometry.DescentData.PullbackFunctor.gluing`, whose
right-hand side involves the gluing isomorphism of the trivial datum — the symmetry of
`U ×_S S` and `S ×_S U`.  Composing that description with the two projections of the target
fibre product yields the three equations that characterise the canonical gluing isomorphism:
two of them hold for any datum, and the third is the invariance of the projection onto `U`.

Both components of a morphism into the underlying scheme `X ×_S U` of a canonical datum are
determined by its composites with the projection onto `U` and with the structure morphism to
`X`; that is `AlgebraicGeometry.DescentData.canonical_hom_ext`.  The criterion is proved by
checking the three components of the compatibility square, the first two of which are formal
consequences of the two base components of the gluing isomorphisms.

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

/-! ### The gluing isomorphism on the literal fibre products -/

section Base

variable {ι : Type v} {S : Scheme.{u}} {Y : ι → Scheme.{u}} {g : ∀ i, Y i ⟶ S}

end Base

/-! ### Morphisms of descent data for a single morphism -/

section Single

variable {S X : Scheme.{u}} {a : X ⟶ S}
  {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}

/-- The map induced on the sources of the gluing isomorphisms by a morphism of the underlying
schemes. -/
def srcPullbackMap (u : D.obj () ⟶ E.obj ()) :
    pullback ((D.obj ()).hom ≫ a) a ⟶ pullback ((E.obj ()).hom ≫ a) a :=
  pullback.map _ _ _ _ u.left (𝟙 X) (𝟙 S) (by simp) (by simp)

/-- The map induced on the targets of the gluing isomorphisms by a morphism of the underlying
schemes. -/
def tgtPullbackMap (u : D.obj () ⟶ E.obj ()) :
    pullback a ((D.obj ()).hom ≫ a) ⟶ pullback a ((E.obj ()).hom ≫ a) :=
  pullback.map _ _ _ _ (𝟙 X) u.left (𝟙 S) (by simp) (by simp)

/-- `srcPullbackMap u` acts as `u.left` on the first factor. -/
@[reassoc (attr := simp)]
lemma srcPullbackMap_fst (u : D.obj () ⟶ E.obj ()) :
    srcPullbackMap u ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u.left :=
  pullback.lift_fst _ _ _

/-- `srcPullbackMap u` is the identity on the second factor. -/
@[reassoc (attr := simp)]
lemma srcPullbackMap_snd (u : D.obj () ⟶ E.obj ()) :
    srcPullbackMap u ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `tgtPullbackMap u` is the identity on the first factor. -/
@[reassoc (attr := simp)]
lemma tgtPullbackMap_fst (u : D.obj () ⟶ E.obj ()) :
    tgtPullbackMap u ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- `tgtPullbackMap u` acts as `u.left` on the second factor. -/
@[reassoc (attr := simp)]
lemma tgtPullbackMap_snd (u : D.obj () ⟶ E.obj ()) :
    tgtPullbackMap u ≫ pullback.snd _ _ = pullback.snd _ _ ≫ u.left :=
  pullback.lift_snd _ _ _

/-- The map on the product in `Over S` induced by a morphism of the underlying schemes,
transported to the literal fibre products. -/
private lemma prodMap_left_eq {A B C₀ E₀ : Over S} (p : A ⟶ C₀) (q : B ⟶ E₀) :
    (Over.prodLeftIsoPullback A B).inv ≫ (prod.map p q).left ≫
        (Over.prodLeftIsoPullback C₀ E₀).hom =
      pullback.map A.hom B.hom C₀.hom E₀.hom p.left q.left (𝟙 S) (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.lift_fst]
    rw [← Over.comp_left, prod.map_fst, Over.comp_left]
    simp
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.lift_snd]
    rw [← Over.comp_left, prod.map_snd, Over.comp_left]
    simp

/-- The gluing isomorphism on the literal fibre products is the gluing isomorphism in `Over S`,
conjugated by `CategoryTheory.Over.prodLeftIsoPullback`. -/
private lemma gluingPullbackIso_hom_eq (D : DescentData (S := S) (X := fun _ : Unit ↦ X)
    (fun _ ↦ a)) :
    (D.gluingPullbackIso () ()).hom =
      (Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)).inv ≫
        (D.gluing () ()).hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ()))).hom := by
  simp only [DescentData.gluingPullbackIso, DescentData.gluingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map]

/-- The compatibility condition required of a morphism of descent data, in fibre-product form.
Both forms are conjugates of each other by `CategoryTheory.Over.prodLeftIsoPullback`, so either
may be used to build the morphism. -/
lemma hom_comm_iff_gluingPullback (u : D.obj () ⟶ E.obj ()) :
    (srcPullbackMap u ≫ (E.gluingPullbackIso () ()).hom =
        (D.gluingPullbackIso () ()).hom ≫ tgtPullbackMap u) ↔
      prod.map ((Over.map a).map u) (𝟙 (Over.mk a)) ≫ (E.gluing () ()).hom.left =
        (D.gluing () ()).hom.left ≫ prod.map (𝟙 (Over.mk a)) ((Over.map a).map u) := by
  set sD := Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a) with hsD
  set sE := Over.prodLeftIsoPullback ((Over.map a).obj (E.obj ())) (Over.mk a) with hsE
  set tD := Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ())) with htD
  set tE := Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (E.obj ())) with htE
  have hs : srcPullbackMap u =
      sD.inv ≫ (prod.map ((Over.map a).map u) (𝟙 (Over.mk a))).left ≫ sE.hom := by
    simpa [hsD, hsE, srcPullbackMap] using
      (prodMap_left_eq ((Over.map a).map u) (𝟙 (Over.mk a))).symm
  have ht : tgtPullbackMap u =
      tD.inv ≫ (prod.map (𝟙 (Over.mk a)) ((Over.map a).map u)).left ≫ tE.hom := by
    simpa [htD, htE, tgtPullbackMap] using
      (prodMap_left_eq (𝟙 (Over.mk a)) ((Over.map a).map u)).symm
  have hD : (D.gluingPullbackIso () ()).hom =
      sD.inv ≫ (D.gluing () ()).hom.left.left ≫ tD.hom := gluingPullbackIso_hom_eq D
  have hE : (E.gluingPullbackIso () ()).hom =
      sE.inv ≫ (E.gluing () ()).hom.left.left ≫ tE.hom := gluingPullbackIso_hom_eq E
  rw [hs, ht, hD, hE]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    have h' := congrArg (fun k ↦ sD.hom ≫ k ≫ tE.inv) h
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] at h'
    simpa only [Over.comp_left] using h'
  · intro h
    have h' := congrArg (fun k ↦ sD.inv ≫ (Over.Hom.left k) ≫ tE.hom) h
    simp only [Over.comp_left, Category.assoc] at h'
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'

/-- A morphism of descent data for a single morphism, built from a morphism of the underlying
schemes satisfying the compatibility condition in fibre-product form. -/
def homOfGluingPullback (u : D.obj () ⟶ E.obj ())
    (h : srcPullbackMap u ≫ (E.gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso () ()).hom ≫ tgtPullbackMap u) :
    D ⟶ E where
  hom _ := u
  comm _ _ := (hom_comm_iff_gluingPullback u).mp h

/-- Every component of `homOfGluingPullback u h` is `u`. -/
@[simp]
lemma homOfGluingPullback_hom (u : D.obj () ⟶ E.obj ())
    (h : srcPullbackMap u ≫ (E.gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso () ()).hom ≫ tgtPullbackMap u) (i : Unit) :
    (homOfGluingPullback u h).hom i = u := rfl

/-- An isomorphism of descent data for a single morphism, built from an isomorphism of the
underlying schemes satisfying the compatibility condition in fibre-product form. -/
def isoOfGluingPullback (u : D.obj () ≅ E.obj ())
    (h : srcPullbackMap u.hom ≫ (E.gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso () ()).hom ≫ tgtPullbackMap u.hom) :
    D ≅ E where
  hom := homOfGluingPullback u.hom h
  inv := homOfGluingPullback u.inv (by
    have hsrc : srcPullbackMap u.inv ≫ srcPullbackMap u.hom =
        𝟙 (pullback ((E.obj ()).hom ≫ a) a) := by
      apply pullback.hom_ext
      · rw [Category.assoc, srcPullbackMap_fst, srcPullbackMap_fst_assoc, Category.id_comp,
          ← Over.comp_left, u.inv_hom_id, Over.id_left, Category.comp_id]
      · rw [Category.assoc, srcPullbackMap_snd, srcPullbackMap_snd, Category.id_comp]
    have htgt : tgtPullbackMap u.hom ≫ tgtPullbackMap u.inv =
        𝟙 (pullback a ((D.obj ()).hom ≫ a)) := by
      apply pullback.hom_ext
      · rw [Category.assoc, tgtPullbackMap_fst, tgtPullbackMap_fst, Category.id_comp]
      · rw [Category.assoc, tgtPullbackMap_snd, tgtPullbackMap_snd_assoc, Category.id_comp,
          ← Over.comp_left, u.hom_inv_id, Over.id_left, Category.comp_id]
    calc srcPullbackMap u.inv ≫ (D.gluingPullbackIso () ()).hom
        = srcPullbackMap u.inv ≫ ((D.gluingPullbackIso () ()).hom ≫ tgtPullbackMap u.hom) ≫
            tgtPullbackMap u.inv := by
          rw [Category.assoc, htgt, Category.comp_id]
      _ = (srcPullbackMap u.inv ≫ srcPullbackMap u.hom) ≫ (E.gluingPullbackIso () ()).hom ≫
            tgtPullbackMap u.inv := by
          rw [← h]; simp only [Category.assoc]
      _ = (E.gluingPullbackIso () ()).hom ≫ tgtPullbackMap u.inv := by
          rw [hsrc, Category.id_comp])
  hom_inv_id := DescentData.hom_ext fun _ ↦ u.hom_inv_id
  inv_hom_id := DescentData.hom_ext fun _ ↦ u.inv_hom_id

end Single

/-! ### The canonical descent datum -/

section Canonical

variable {S X : Scheme.{u}} (f : X ⟶ S) (U : Over S)

/-- The pullback functor used to form the canonical descent datum. -/
abbrev canonicalPullbackFunctor :
    PullbackFunctor (𝟙 S) f (𝟙 S) f (by simp) :=
  pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)

/-- The underlying scheme of the canonical descent datum of `U` is `X ×_S U`. -/
def canonicalObjIso :
    (((canonicalFunctor f).obj U).obj ()) ≅ (Over.pullback f).obj U :=
  (canonicalPullbackFunctor f).objIso ((trivialFunctor S).obj U)

/-- The projection of the canonical descent datum of `U` onto `U`. -/
def canonicalProjection : (((canonicalFunctor f).obj U).obj ()).left ⟶ U.left :=
  (canonicalObjIso f U).hom.left ≫ pullback.fst U.hom f

/-- The two halves of the isomorphism `canonicalObjIso` compose to the identity on `X ×_S U`. -/
private lemma canonicalObjIso_inv_hom_left :
    (canonicalObjIso f U).inv.left ≫ (canonicalObjIso f U).hom.left =
      𝟙 ((Over.pullback f).obj U).left := by
  rw [← Over.comp_left, (canonicalObjIso f U).inv_hom_id, Over.id_left]

/-- A morphism into the underlying scheme of a canonical descent datum is determined by its
composites with the projection onto `U` and with the structure morphism to `X`. -/
lemma canonical_hom_ext {W : Scheme.{u}}
    {p q : W ⟶ (((canonicalFunctor f).obj U).obj ()).left}
    (h₁ : p ≫ canonicalProjection f U = q ≫ canonicalProjection f U)
    (h₂ : p ≫ (((canonicalFunctor f).obj U).obj ()).hom =
      q ≫ (((canonicalFunctor f).obj U).obj ()).hom) : p = q := by
  have hiso : IsIso (canonicalObjIso f U).hom.left :=
    ((Over.forget X).mapIso (canonicalObjIso f U)).isIso_hom
  rw [← cancel_mono (canonicalObjIso f U).hom.left]
  apply pullback.hom_ext
  · simpa only [canonicalProjection, Category.assoc] using h₁
  · have hw := Over.w (canonicalObjIso f U).hom
    have h₂' := h₂
    rw [show (((canonicalFunctor f).obj U).obj ()).hom =
        (canonicalObjIso f U).hom.left ≫ ((Over.pullback f).obj U).hom from hw.symm] at h₂'
    simpa only [Category.assoc, Over.pullback_obj_hom] using h₂'

/-- The gluing isomorphism of a canonical descent datum carries the projection onto `U` of the
second factor to the projection of the first factor: the projection is invariant. -/
lemma canonicalFunctor_gluingPullbackIso_hom_snd_projection :
    (((canonicalFunctor f).obj U).gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫
        canonicalProjection f U =
      pullback.fst _ _ ≫ canonicalProjection f U := by
  have hglue := (canonicalPullbackFunctor f).gluing ((trivialFunctor S).obj U)
  have hcomp := congrArg
    (fun k ↦ k ≫ pullback.snd (𝟙 S) ((((trivialFunctor S).obj U).obj ()).hom ≫ 𝟙 S)) hglue
  simp only [Category.assoc] at hcomp
  rw [(canonicalPullbackFunctor f).targetMap_snd ((trivialFunctor S).obj U)] at hcomp
  have h1 : (Over.prodLeftIsoPullback (Over.mk (𝟙 S))
        ((Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ()))).hom ≫
        pullback.snd (𝟙 S) ((((trivialFunctor S).obj U).obj ()).hom ≫ 𝟙 S) =
      (prod.snd : Over.mk (𝟙 S) ⨯ (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ()) ⟶
        (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ())).left :=
    Over.prodLeftIsoPullback_hom_snd ..
  have h2 : Over.Hom.left (Over.Hom.left (((trivialFunctor S).obj U).gluing () ()).hom) ≫
      (prod.snd : Over.mk (𝟙 S) ⨯ (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ()) ⟶
        (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ())).left =
      (prod.fst : (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ()) ⨯ Over.mk (𝟙 S) ⟶
        (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ())).left := by
    rw [← Over.comp_left]
    refine congrArg Over.Hom.left ?_
    show (prod.braiding ((Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ()))
        (Over.mk (𝟙 S))).hom ≫ prod.snd = prod.fst
    simp
  have h3 : (Over.prodLeftIsoPullback
        ((Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ())) (Over.mk (𝟙 S))).inv ≫
      (prod.fst : (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ()) ⨯ Over.mk (𝟙 S) ⟶
        (Over.map (𝟙 S)).obj (((trivialFunctor S).obj U).obj ())).left =
      pullback.fst ((((trivialFunctor S).obj U).obj ()).hom ≫ 𝟙 S) (𝟙 S) :=
    Over.prodLeftIsoPullback_inv_fst ..
  have htriv : (((trivialFunctor S).obj U).gluingPullbackIso () ()).hom ≫
      pullback.snd (𝟙 S) ((((trivialFunctor S).obj U).obj ()).hom ≫ 𝟙 S) =
        pullback.fst ((((trivialFunctor S).obj U).obj ()).hom ≫ 𝟙 S) (𝟙 S) := by
    simp only [DescentData.gluingPullbackIso, DescentData.gluingIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Over.forget_map, Category.assoc]
    rw [h1, h2, h3]
  rw [htriv, (canonicalPullbackFunctor f).sourceMap_fst ((trivialFunctor S).obj U)] at hcomp
  exact hcomp

end Canonical

/-! ### The criterion -/

section Criterion

variable {S X : Scheme.{u}} {a : X ⟶ S}
  {D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}

/-- **A descent datum of schemes relative to one morphism is effective as soon as its underlying
scheme is a fibre product `X ×_S U` by an invariant projection.**  Explicitly: let
`a : X ⟶ S` be a morphism of schemes, let `D` be a descent datum relative to `a` with underlying
`X`-scheme `V`, let `U` be a scheme over `S` and let `φ : V ⟶ U` be a morphism such that

* the square with sides `φ`, the structure morphism `V ⟶ X`, `U ⟶ S` and `a` is a fibre product
  square, and
* the two pullbacks of `φ` to `V ×_S X`, namely along the first projection and along the gluing
  isomorphism followed by the second projection, agree.

Then `D` is effective. -/
theorem isEffective_of_isPullback (U : Over S) (φ : (D.obj ()).left ⟶ U.left)
    (hpb : IsPullback φ (D.obj ()).hom U.hom a)
    (hinv : (D.gluingPullbackIso () ()).hom ≫ pullback.snd _ _ ≫ φ =
      pullback.fst _ _ ≫ φ) :
    D.IsEffective := by
  -- the isomorphism of underlying schemes over `X`
  let e₀ : (D.obj ()).left ≅ pullback U.hom a := hpb.isoPullback
  let e : D.obj () ≅ (Over.pullback a).obj U :=
    Over.isoMk e₀ (by simpa only [Over.pullback_obj_hom] using hpb.isoPullback_hom_snd)
  let u : D.obj () ⟶ ((canonicalFunctor a).obj U).obj () :=
    e.hom ≫ (canonicalObjIso a U).inv
  have hφ : u.left ≫ canonicalProjection a U = φ := by
    simp only [u, canonicalProjection, Over.comp_left, Category.assoc]
    rw [← Category.assoc ((canonicalObjIso a U).inv.left), canonicalObjIso_inv_hom_left,
      Category.id_comp]
    simpa only [e, Over.isoMk_hom_left] using hpb.isoPullback_hom_fst
  have hu : IsIso u := by
    have : IsIso (canonicalObjIso a U).inv := Iso.isIso_inv _
    have : IsIso e.hom := Iso.isIso_hom _
    infer_instance
  -- the compatibility square, checked on the three components of the target
  have hcomm : srcPullbackMap u ≫ (((canonicalFunctor a).obj U).gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso () ()).hom ≫ tgtPullbackMap u := by
    apply pullback.hom_ext
    · rw [Category.assoc, gluingPullbackIso_hom_fst', srcPullbackMap_fst_assoc,
        Category.assoc, tgtPullbackMap_fst, gluingPullbackIso_hom_fst', Over.w u]
    · apply canonical_hom_ext a U
      · rw [Category.assoc, Category.assoc,
          canonicalFunctor_gluingPullbackIso_hom_snd_projection,
          srcPullbackMap_fst_assoc, hφ, Category.assoc, Category.assoc,
          tgtPullbackMap_snd_assoc, hφ, hinv]
      · rw [Category.assoc, Category.assoc, gluingPullbackIso_hom_snd, srcPullbackMap_snd,
          Category.assoc, Category.assoc, tgtPullbackMap_snd_assoc, Over.w u,
          gluingPullbackIso_hom_snd]
  exact ⟨U, ⟨(isoOfGluingPullback (asIso u) hcomm).symm⟩⟩

/-- `AlgebraicGeometry.DescentData.isEffective_of_isPullback` with the invariance of `φ` written
on the products taken in `Over S` instead of on the literal fibre products.  This is the form in
which the gluing isomorphism of a descent datum is given. -/
theorem isEffective_of_isPullback_prod (U : Over S) (φ : (D.obj ()).left ⟶ U.left)
    (hpb : IsPullback φ (D.obj ()).hom U.hom a)
    (hinv : (D.gluing () ()).hom.left.left ≫
        (prod.snd : Over.mk a ⨯ (Over.map a).obj (D.obj ()) ⟶
          (Over.map a).obj (D.obj ())).left ≫ φ =
      (prod.fst : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶
        (Over.map a).obj (D.obj ())).left ≫ φ) :
    D.IsEffective := by
  refine isEffective_of_isPullback U φ hpb ?_
  have hfst : pullback.fst ((D.obj ()).hom ≫ a) a =
      (Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)).inv ≫
        (prod.fst : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶
          (Over.map a).obj (D.obj ())).left :=
    (show (Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)).inv ≫
        (prod.fst : (Over.map a).obj (D.obj ()) ⨯ Over.mk a ⟶
          (Over.map a).obj (D.obj ())).left =
        pullback.fst ((D.obj ()).hom ≫ a) a from
      Over.prodLeftIsoPullback_inv_fst ..).symm
  have hsnd₀ : (Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ()))).hom ≫
      pullback.snd a ((D.obj ()).hom ≫ a) =
      (prod.snd : Over.mk a ⨯ (Over.map a).obj (D.obj ()) ⟶
        (Over.map a).obj (D.obj ())).left :=
    Over.prodLeftIsoPullback_hom_snd ..
  have hsnd : (Over.prodLeftIsoPullback (Over.mk a) ((Over.map a).obj (D.obj ()))).hom ≫
      pullback.snd a ((D.obj ()).hom ≫ a) ≫ φ =
      (prod.snd : Over.mk a ⨯ (Over.map a).obj (D.obj ()) ⟶
        (Over.map a).obj (D.obj ())).left ≫ φ := by
    rw [← Category.assoc, hsnd₀]
  rw [gluingPullbackIso_hom_eq D, hfst, Category.assoc, Category.assoc, Category.assoc, hsnd]
  exact congrArg
    (fun k ↦ (Over.prodLeftIsoPullback ((Over.map a).obj (D.obj ())) (Over.mk a)).inv ≫ k) hinv

/-- The hypotheses of `AlgebraicGeometry.DescentData.isEffective_of_isPullback` are satisfiable:
a canonical descent datum satisfies them, with `U` the scheme it is the canonical datum of and
`φ` the projection onto `U`.  The conclusion is of course immediate for a canonical datum; what
this records is that the criterion is not vacuous. -/
theorem isEffective_canonicalFunctor_obj {S X : Scheme.{u}} (f : X ⟶ S) (U : Over S) :
    ((canonicalFunctor f).obj U).IsEffective := by
  refine isEffective_of_isPullback U (canonicalProjection f U) ?_
    (canonicalFunctor_gluingPullbackIso_hom_snd_projection f U)
  have hw : (canonicalObjIso f U).hom.left ≫ pullback.snd U.hom f =
      (((canonicalFunctor f).obj U).obj ()).hom := by
    simpa only [Over.pullback_obj_hom] using Over.w (canonicalObjIso f U).hom
  refine (IsPullback.of_hasPullback U.hom f).of_iso
    ((Over.forget X).mapIso (canonicalObjIso f U)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map,
      canonicalProjection, ← Category.assoc,
      canonicalObjIso_inv_hom_left]
    exact (Category.id_comp _).symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map,
      ← hw, ← Category.assoc, canonicalObjIso_inv_hom_left]
    exact (Category.id_comp _).symm

end Criterion

end AlgebraicGeometry.DescentData

end

end
