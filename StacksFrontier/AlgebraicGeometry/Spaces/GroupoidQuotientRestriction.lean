module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction

/-!
# Quotient sheaves of a restricted groupoid scheme

Let `G` be a groupoid scheme over `S` and `g : U' ⟶ G.objects` a morphism of `S`-schemes, and
let `H` be a restriction of `G` along `g`. The canonical morphism of groupoid schemes from
`H.groupoid` to `G` induces a map `U'/R' ⟶ U/R` of quotient sheaves, and that map is
injective.

The comparison rests on the functoriality of `Stacks.Groupoids.quotientSheafMap`: the map
induced by a morphism of pre-relations depends only on the map on the objects, and it is
compatible with composition and identities. Those statements are
`Stacks.Groupoids.quotientSheafMap_eq_of_obj_eq`, `Stacks.Groupoids.quotientSheafMap_comp`
and `Stacks.Groupoids.quotientSheafMap_id` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.restrictionQuotientMap` is the map of quotient sheaves induced
  by the canonical morphism out of a restricted groupoid.
* `AlgebraicGeometry.groupoidRestrictionQuotientIso` identifies the quotient by the restricted
  groupoid with the quotient by the restricted relation.

## Main results

* `AlgebraicGeometry.restrictionQuotientMap_factor` factors the restriction map of quotient
  sheaves through `Stacks.Groupoids.restrictQuotientSheafMap`.
* Injectivity is `AlgebraicGeometry.GroupoidScheme.mono_restrictionQuotientMap` of
  `StacksFrontier/AlgebraicGeometry/Groupoids/QuotientSheaf/GroupoidRestriction.lean`, which carries
  the same `@[stacks 02VH "injectivity of the quotient map"]` clause.

## Implementation notes

The site is presented by an arbitrary functor `F : C ⥤ Over S` into `S`-schemes, so the
statements cover the big and small Zariski, étale, fppf, smooth and syntomic sites at once.

Every statement about maps out of a quotient sheaf reduces to
`Stacks.Groupoids.quotientSheaf_hom_ext`: two such maps agree as soon as they agree after the
canonical projection, because that projection is a coequalizer followed by sheafification.
In particular `Stacks.Groupoids.quotientSheafMap` does not depend on the chosen map on the
relation schemes, only on the map on objects, which is what makes the comparison with the
restricted relation an isomorphism without checking anything on arrows.

A restriction of a groupoid scheme is only characterized up to the equalities recorded in
`AlgebraicGeometry.GroupoidScheme.Restriction`, so the comparison with the restricted relation
is the isomorphism `AlgebraicGeometry.restrictionIso` conjugated by the `eqToHom`s of
those equalities. Injectivity is then inherited from
`Stacks.Groupoids.restrictQuotientSheafMap_mono` applied to the pre-equivalence relation
underlying `G`.

## References

* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

open Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- The quotient sheaf of a restricted groupoid scheme agrees with the quotient sheaf of the
restricted pre-relation. -/
noncomputable def groupoidRestrictionQuotientIso (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : GroupoidScheme.Restriction G g) :
    quotientSheaf J F (groupoidPreRelation H.groupoid) ≅
      quotientSheaf J F (PreRelation.restrict (groupoidPreRelation G) g) := by
  let r := eqToHom H.arrows_eq ≫ (restrictionIso G g).hom
  let f := eqToHom H.objects_eq
  let rInv := (restrictionIso G g).inv ≫ eqToHom H.arrows_eq.symm
  let fInv := eqToHom H.objects_eq.symm
  have hr : r ≫ (PreRelation.restrict (groupoidPreRelation G) g).target =
      (groupoidPreRelation H.groupoid).target ≫ f := by
    dsimp [r, f]
    change (eqToHom H.arrows_eq ≫ ((restrictionIso G g).hom ≫
      PreRelation.restrict (groupoidPreRelation G) g)) ≫ prod.fst =
      ((groupoidPreRelation H.groupoid) ≫ prod.fst) ≫ eqToHom H.objects_eq
    rw [Category.assoc, restrictionIso_relation]
    simp only [groupoidPreRelation, prod.lift_fst]
    rw [H.target_eq]
    simp [Category.assoc]
  have hs : r ≫ (PreRelation.restrict (groupoidPreRelation G) g).source =
      (groupoidPreRelation H.groupoid).source ≫ f := by
    dsimp [r, f]
    change (eqToHom H.arrows_eq ≫ ((restrictionIso G g).hom ≫
      PreRelation.restrict (groupoidPreRelation G) g)) ≫ prod.snd =
      ((groupoidPreRelation H.groupoid) ≫ prod.snd) ≫ eqToHom H.objects_eq
    rw [Category.assoc, restrictionIso_relation]
    simp only [groupoidPreRelation, prod.lift_snd]
    rw [H.source_eq]
    simp [Category.assoc]
  have hrInv : rInv ≫ (groupoidPreRelation H.groupoid).target =
      (PreRelation.restrict (groupoidPreRelation G) g).target ≫ fInv := by
    calc
      rInv ≫ (groupoidPreRelation H.groupoid).target =
          rInv ≫ ((groupoidPreRelation H.groupoid).target ≫ f) ≫ fInv := by
        simp [f, fInv, Category.assoc]
      _ = rInv ≫ (r ≫ (PreRelation.restrict (groupoidPreRelation G) g).target) ≫ fInv := by
        rw [← hr]
      _ = _ := by simp [r, rInv, fInv, groupoidPreRelation, PreRelation.target]
  have hsInv : rInv ≫ (groupoidPreRelation H.groupoid).source =
      (PreRelation.restrict (groupoidPreRelation G) g).source ≫ fInv := by
    calc
      rInv ≫ (groupoidPreRelation H.groupoid).source =
          rInv ≫ ((groupoidPreRelation H.groupoid).source ≫ f) ≫ fInv := by
        simp [f, fInv, Category.assoc]
      _ = rInv ≫ (r ≫ (PreRelation.restrict (groupoidPreRelation G) g).source) ≫ fInv := by
        rw [← hs]
      _ = _ := by simp [r, rInv, fInv, groupoidPreRelation, PreRelation.source]
  let φ := quotientSheafMap J F (groupoidPreRelation H.groupoid)
    (PreRelation.restrict (groupoidPreRelation G) g) r f hs hr
  let ψ := quotientSheafMap J F (PreRelation.restrict (groupoidPreRelation G) g)
    (groupoidPreRelation H.groupoid) rInv fInv hsInv hrInv
  refine ⟨φ, ψ, ?_, ?_⟩
  · apply quotientSheaf_hom_ext J F _ _ _
    change (toQuotientSheaf J F _ ≫ (quotientSheafMap J F _ _ r f hs hr).hom) ≫
      (quotientSheafMap J F _ _ rInv fInv hsInv hrInv).hom = toQuotientSheaf J F _
    rw [toQuotientSheaf_comp_quotientSheafMap J F _ _ r f hs hr]
    change (F.op.whiskerLeft (yoneda.map f) ≫
      toQuotientSheaf J F (PreRelation.restrict (groupoidPreRelation G) g)) ≫
      (quotientSheafMap J F _ _ rInv fInv hsInv hrInv).hom =
      toQuotientSheaf J F (groupoidPreRelation H.groupoid)
    rw [Category.assoc,
      toQuotientSheaf_comp_quotientSheafMap J F _ _ rInv fInv hsInv hrInv]
    have hcomp : sheafifyMap J (F.op.whiskerLeft (yoneda.map f)) ≫
        sheafifyMap J (F.op.whiskerLeft (yoneda.map fInv)) = 𝟙 _ := by
      rw [← sheafifyMap_comp]
      simp [← Functor.whiskerLeft_comp, ← Functor.map_comp, f, fInv]
    calc
      _ = (toSheafify J (points F H.groupoid.objects) ≫
          (sheafifyMap J (F.op.whiskerLeft (yoneda.map f)) ≫
            sheafifyMap J (F.op.whiskerLeft (yoneda.map fInv)))) ≫
          sheafifyMap J (toQuotientPresheaf F (groupoidPreRelation H.groupoid)) := by
        simp [Category.assoc]
      _ = _ := by rw [hcomp]; simp
  · apply quotientSheaf_hom_ext J F _ _ _
    change (toQuotientSheaf J F _ ≫ (quotientSheafMap J F _ _ rInv fInv hsInv hrInv).hom) ≫
      (quotientSheafMap J F _ _ r f hs hr).hom = toQuotientSheaf J F _
    rw [toQuotientSheaf_comp_quotientSheafMap J F _ _ rInv fInv hsInv hrInv]
    change (F.op.whiskerLeft (yoneda.map fInv) ≫
      toQuotientSheaf J F (groupoidPreRelation H.groupoid)) ≫
      (quotientSheafMap J F _ _ r f hs hr).hom =
      toQuotientSheaf J F (PreRelation.restrict (groupoidPreRelation G) g)
    rw [Category.assoc, toQuotientSheaf_comp_quotientSheafMap J F _ _ r f hs hr]
    have hcomp : sheafifyMap J (F.op.whiskerLeft (yoneda.map fInv)) ≫
        sheafifyMap J (F.op.whiskerLeft (yoneda.map f)) = 𝟙 _ := by
      rw [← sheafifyMap_comp]
      simp [← Functor.whiskerLeft_comp, ← Functor.map_comp, f, fInv]
    calc
      _ = (toSheafify J (points F U') ≫
          (sheafifyMap J (F.op.whiskerLeft (yoneda.map fInv)) ≫
            sheafifyMap J (F.op.whiskerLeft (yoneda.map f)))) ≫
          sheafifyMap J (toQuotientPresheaf F
            (PreRelation.restrict (groupoidPreRelation G) g)) := by
        simp [Category.assoc]
      _ = _ := by rw [hcomp]; simp

/-- The restriction map of quotient sheaves of a groupoid scheme is the comparison with the
restricted relation followed by the restriction map of the relation's quotient sheaves. -/
theorem restrictionQuotientMap_factor (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] (F : C ⥤ Over S) (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (H : GroupoidScheme.Restriction G g) :
    GroupoidScheme.restrictionQuotientMap J F G g H =
      (groupoidRestrictionQuotientIso J F G g H).hom ≫
        restrictQuotientSheafMap J F (groupoidPreRelation G) g := by
  let jH := groupoidPreRelation H.groupoid
  let jG := groupoidPreRelation G
  let jR := PreRelation.restrict jG g
  change quotientSheafMap J F jH jG H.hom.mapArrows H.hom.mapObjects _ _ = _
  rw [restrictQuotientSheafMap]
  exact (quotientSheafMap_eq_of_obj_eq J F jH jG H.hom.mapArrows _ H.hom.mapObjects _ _ _ _ _
    H.mapObjects_eq).trans (quotientSheafMap_comp J F jH jR jG _ _ _ _ _ _ _ _).symm

end AlgebraicGeometry

end
