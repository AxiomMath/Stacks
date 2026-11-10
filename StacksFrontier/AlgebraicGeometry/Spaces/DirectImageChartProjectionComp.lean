module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedTarget

/-!
# The chart projections of an iterated direct image

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`.  The
sections of a direct image `f_*F` over an étale scheme chart `V` of `Y` are a limit over the
étale scheme charts of `X` above `X ×_Y V`, and
`AlgebraicGeometry.Space.directImageChartProjection` is the projection to one of them.  For the
composite `f ≫ g` the index of that limit is a chart of `X` above `X ×_Z W`, while for the
iterated direct image `g_*(f_*F)` one first projects to a chart `V` of `Y` above `Y ×_Z W` and
then to a chart of `X` above `X ×_Y V`.  **This file proves that the two readings agree**, across
the comparison [Stacks Project, Tag 03G2], part (3), of the direct image along a composite with
the iterated one:

`AlgebraicGeometry.Space.directImageChartProjection_pushforwardRingSheafCompInv`.

The index of the one-step reading attached to a pair of charts is
`AlgebraicGeometry.Space.chartBaseChangeComp`, the one already used for the composition law of
the structure map, so the chartwise pullbacks on the two sides are the same by
`AlgebraicGeometry.Space.chartPullback_comp_chart`.

**Why this comparison is needed.**  The comorphism of a morphism `c : X ⟶ W` read through a
thickening `Z ⊆ X` with inclusion `i : Z ⟶ X` lands in `(i ≫ c)_*(i^{-1}𝒪_X)`, a sheaf depending
on `c` only through `i ≫ c`; but
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartProjection.lean` reads it
on charts only after transporting it across the comparison of iterated direct images, whose
splitting *does* depend on `c`.  So two morphisms `c, c'` agreeing on the thickening have their
chart readings indexed by charts of `X` above `X ×_W V` for `c` and for `c'` separately — two
different index categories, which cannot be compared term by term.  The index category of the
one-step reading, by charts of `Z` above `Z ×_W V`, depends only on `i ≫ c` and is therefore
common to both; this file is what moves a reading onto it.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_comparison`: **on a sheaf restricted from
  the spaces-étale site, the chart projection is restriction along the given morphism of the
  geometric comparison** `AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison`.
* `AlgebraicGeometry.Space.directImageChartProjection_presentation`: the same for an arbitrary
  sheaf of sets presented on the spaces-étale site.
* `AlgebraicGeometry.Space.directImageChartProjection_smallToposMorphismTypeU_comp`: **the chart
  projection of the direct image along a composite, at the index attached to a pair of charts, is
  the chart projection of `g_*` followed by the chart projection of `f_*`**, across the
  comparison of [Stacks Project, Tag 03G2], part (3).
* `AlgebraicGeometry.Space.directImageChartProjection_pushforwardRingSheafCompInv`: the same for
  a sheaf of rings and the comparison
  `AlgebraicGeometry.Space.pushforwardRingSheafCompInv`, which is the form the deformation theory
  of [Stacks Project, Tag 0CKE] consumes.

## Implementation notes

The argument is the one the composition law for the structure map
(`AlgebraicGeometry.Space.structureSharpRanSet_comp`) runs at the structure sheaf, carried out
once and for all at an arbitrary sheaf.  Everything reduces to the spaces-étale site, where the
direct image is restriction along base change and the comparison of iterated direct images is
restriction along the composition isomorphism
`AlgebraicGeometry.Space.spacesBaseChange_comp`; the transport through the comparison
equivalences of [Stacks Project, Tag 03G1] is exactly
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_presentation`, and the passage from a
presented sheaf to an arbitrary one is naturality of the chart projection in the sheaf.

The one new identification is
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso_hom_app_restriction`: at a sheaf restricted
from the spaces-étale site, the comparison of the quasi-inverse of the comparison equivalence
with the right Kan extension is the inverse unit of that equivalence followed by the unit of the
Kan-extension adjunction.  It is `AlgebraicGeometry.Space.comparisonUnitIso_hom` with the unit
cancelled, and it is what lets `AlgebraicGeometry.Space.ranProj_unit_app` compute the chart
projection.

Both reassociations are stated at an abstract category with every morphism a variable and
discharged by `exact`, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` require for these
composites: `CategoryTheory.Category.assoc` on the geometric terms fails at `implicit`
transparency, because `(functor ⋙ inverse).obj H` and `inverse.obj (functor.obj H)` are only
definitionally equal.  The presentation of an arbitrary sheaf on the spaces-étale site is taken
as a parameter of a private auxiliary statement rather than produced inside the proof, so that
no definitional unfolding of the quasi-inverse appears in a goal.

**No `@[stacks]` attribute is placed.**  What is proved here is a chart-level reading of the
comparison of [Stacks Project, Tag 03G2], part (3), internal to this development, not a
statement of the Stacks project; the comparison itself is registered on
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1), the comparison of the
  two étale sites.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), parts (1) and (3), the
  direct image and its compatibility with composition.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this comparison
  is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- Cancelling a left inverse off the left of a composite. -/
private theorem eq_comp_of_comp_eq {Cc : Type*} [Category Cc] {A Bb D : Cc}
    (p : A ⟶ Bb) (p' : Bb ⟶ A) (r : Bb ⟶ D) (s : A ⟶ D)
    (hp : p' ≫ p = 𝟙 Bb) (h : p ≫ r = s) : r = p' ≫ s := by
  rw [← h, ← Category.assoc, hp, Category.id_comp]

/-- Cancelling an isomorphism off the right of a composite. -/
private theorem comp_cancel_hom_inv {Cc : Type*} [Category Cc] {A Bb D : Cc} (p : A ⟶ Bb)
    (q : Bb ⟶ D) (q' : D ⟶ Bb) (hq : q ≫ q' = 𝟙 Bb) : (p ≫ q) ≫ q' = p := by
  rw [Category.assoc, hq, Category.comp_id]

/-! ### The chart projection on a sheaf coming from the spaces-étale site -/

/-- **At a sheaf restricted from the spaces-étale site, the comparison of the quasi-inverse of
the comparison equivalence of [Stacks Project, Tag 03G1] with the right Kan extension along the
comparison functor is the inverse unit of that equivalence followed by the unit of the
Kan-extension adjunction.**

This is `AlgebraicGeometry.Space.comparisonUnitIso_hom` — which says that the two compose to the
unit — with the unit isomorphism of the equivalence cancelled off the left. -/
theorem smallEtaleComparisonRanIso_hom_app_restriction
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (smallEtaleComparisonRanIso B S hS X).hom.app
        ((smallEtaleComparisonRestriction B S hS X).obj H) =
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app H ≫
        (comparisonAdjunction B S hS X).unit.app H :=
  eq_comp_of_comp_eq
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.hom.app H)
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app H)
    ((smallEtaleComparisonRanIso B S hS X).hom.app
      ((smallEtaleComparisonRestriction B S hS X).obj H))
    ((comparisonAdjunction B S hS X).unit.app H)
    (Iso.inv_hom_id_app _ H) (comparisonUnitIso_hom B S hS X H)

/-- **On a sheaf restricted from the spaces-étale site, the chart projection of the direct image
is restriction of the geometric comparison.**

For a sheaf `H` on the spaces-étale site of `X`, a section of `f_*(H|_{X_étale})` over an étale
scheme chart `V` of `Y` is a section of `H` over `X ×_Y V` by
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison`, and its projection to a chart of
`X` above `X ×_Y V` is its restriction along the morphism to `X ×_Y V` indexing that chart. -/
theorem directImageChartProjection_comparison (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj
      ((smallEtaleComparisonRestriction B S hS X).obj H)) :
    (directImageChartProjection B S hS f V j).app
        ((smallEtaleComparisonRestriction B S hS X).obj H) a =
      H.obj.map j.hom
        (((smallToposMorphismTypeU_comparison B S hS f).hom.app H).hom.app (op V) a) := by
  have h2 : ((smallToposMorphismTypeU_comparison B S hS f).hom.app H).hom.app (op V) a =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app H).hom.app
        (op (chartBaseChange B S hS f V)) a := rfl
  rw [h2]
  refine Eq.trans ?_ (ranProj_unit_app B S hS X (chartBaseChange B S hS f V) H j
    (((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app H).hom.app
      (op (chartBaseChange B S hS f V)) a))
  change (ranProj B S hS X (chartBaseChange B S hS f V) j).app
      ((smallEtaleComparisonRestriction B S hS X).obj H)
      (((smallEtaleComparisonRanIso B S hS X).hom.app
        ((smallEtaleComparisonRestriction B S hS X).obj H)).hom.app
        (op (chartBaseChange B S hS f V)) a) = _
  exact congrArg ((ranProj B S hS X (chartBaseChange B S hS f V) j).app
      ((smallEtaleComparisonRestriction B S hS X).obj H))
    (Sheaf.hom_congr_app_apply (smallEtaleComparisonRanIso_hom_app_restriction B S hS H)
      (op (chartBaseChange B S hS f V)) a)

/-- **The chart projection of the direct image of an arbitrary sheaf, read through a presentation
of it on the spaces-étale site.**  This is
`AlgebraicGeometry.Space.directImageChartProjection_comparison` moved across a morphism
`F ⟶ H|_{X_étale}` by naturality of the chart projection in the sheaf,
`AlgebraicGeometry.Space.directImageChartProjection_map`. -/
theorem directImageChartProjection_presentation (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (e : F ⟶ (smallEtaleComparisonRestriction B S hS X).obj H)
    (a : (smallEtaleDirectImage B S hS f ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj F) :
    e.hom.app j.right ((directImageChartProjection B S hS f V j).app F a) =
      H.obj.map j.hom
        (((smallEtaleDirectImage B S hS f).map e ≫
          (smallToposMorphismTypeU_comparison B S hS f).hom.app H).hom.app (op V) a) :=
  (directImageChartProjection_map B S hS f V j e a).symm.trans
    (directImageChartProjection_comparison B S hS f V j H _)

/-! ### The chart projections of an iterated direct image -/

/-- `AlgebraicGeometry.Space.directImageChartProjection_smallToposMorphismTypeU_comp` with a
presentation of the sheaf on the spaces-étale site taken as a parameter: every sheaf has one,
and keeping it abstract is what stops the quasi-inverse of the comparison equivalence from
appearing in a goal. -/
private theorem directImageChartProjection_comp_aux (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (e : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H)
    (α : (smallEtaleDirectImage B S hS g ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Z.1) (op W)).obj
      ((smallEtaleDirectImage B S hS f).obj F)) :
    (directImageChartProjection B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app F
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app F).hom.app (op W) α) =
      (directImageChartProjection B S hS f j.right.unop k).app F
        ((directImageChartProjection B S hS g W j).app
          ((smallEtaleDirectImage B S hS f).obj F) α) := by
  refine Function.LeftInverse.injective
    (f := e.hom.hom.app k.right) (g := e.inv.hom.app k.right)
    (fun x => Sheaf.iso_inv_hom_app_apply e k.right x) ?_
  have hL := directImageChartProjection_presentation B S hS (f ≫ g) W
    (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom)) F H e.hom
    (((smallToposMorphismTypeU_comp B S hS f g).hom.app F).hom.app (op W) α)
  have hR := directImageChartProjection_presentation B S hS f j.right.unop k F H e.hom
    ((directImageChartProjection B S hS g W j).app
      ((smallEtaleDirectImage B S hS f).obj F) α)
  have hM := directImageChartProjection_presentation B S hS g W j
    ((smallEtaleDirectImage B S hS f).obj F)
    (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H)
    ((smallEtaleDirectImage B S hS f).map e.hom ≫
      (smallToposMorphismTypeU_comparison B S hS f).hom.app H) α
  refine hL.trans (Eq.trans ?_ (hR.trans (congrArg (H.obj.map k.hom) hM)).symm)
  refine (Functor.map_comp_apply H.obj (chartBaseChangeComp B S hS f g W j).op k.hom _).trans ?_
  refine congrArg (H.obj.map k.hom) ?_
  have hsec := Sheaf.hom_congr_app_apply
    (smallToposMorphismTypeU_comp_presentation B S hS f g F H e) (op W) α
  refine (congrArg (H.obj.map (chartBaseChangeComp B S hS f g W j).op) hsec.symm).trans ?_
  refine (Functor.map_comp_apply H.obj
    ((spacesBaseChange_comp B S hS f g).inv.app ((comparisonFunctor B S hS Z).obj W)).op
    (chartBaseChangeComp B S hS f g W j).op _).symm.trans ?_
  have hcbc : chartBaseChangeComp B S hS f g W j ≫
      (spacesBaseChange_comp B S hS f g).inv.app ((comparisonFunctor B S hS Z).obj W) =
      (spacesBaseChange B S hS f).functor.map j.hom.unop :=
    comp_cancel_hom_inv _ _ _ (Iso.hom_inv_id_app _ _)
  exact congrArg (fun m : chartBaseChange B S hS f j.right.unop ⟶
      (spacesBaseChange B S hS f).functor.obj (chartBaseChange B S hS g W) =>
    H.obj.map m.op _) hcbc

/-- **The chart projection of the direct image along a composite factors as the chart projection
of `g_*` followed by the chart projection of `f_*`.**

Given a chart `j` of `Y` above `Y ×_Z W` and a chart `k` of `X` above `X ×_Y j`, the index of the
one-step limit attached to them is `AlgebraicGeometry.Space.chartBaseChangeComp`, and projecting
a section of `(f ≫ g)_*F` over `W` to it — after transporting it to the iterated direct image
across the comparison of [Stacks Project, Tag 03G2], part (3) — is projecting first to `j` and
then to `k`.

This is the statement of sheaves of sets; the form the deformation theory uses is
`AlgebraicGeometry.Space.directImageChartProjection_pushforwardRingSheafCompInv`. -/
theorem directImageChartProjection_smallToposMorphismTypeU_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (α : (smallEtaleDirectImage B S hS g ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS Z.1) (op W)).obj
      ((smallEtaleDirectImage B S hS f).obj F)) :
    (directImageChartProjection B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app F
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app F).hom.app (op W) α) =
      (directImageChartProjection B S hS f j.right.unop k).app F
        ((directImageChartProjection B S hS g W j).app
          ((smallEtaleDirectImage B S hS f).obj F) α) :=
  directImageChartProjection_comp_aux B S hS f g W j k F
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F)
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app F).symm α

/-- **The comparison of iterated direct images of a sheaf of rings is, on sections, the
comparison of the underlying sheaves of sets.**  Its second factor is the identity on sections
by construction, and its first is the given natural transformation by
`Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans`. -/
theorem app_pushforwardRingSheafCompInv (f : X ⟶ Y) (g : Y ⟶ Z)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u})
    (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (a : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Z.1)
      (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O).obj.obj V)) :
    (pushforwardRingSheafCompInv B S hS f g O).hom.app V a =
      ((smallToposMorphismTypeU_comp B S hS f g).inv.app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj O)).hom.app V a := rfl

/-- **The chart projection of the direct image of a sheaf of rings along a composite factors,
across `AlgebraicGeometry.Space.pushforwardRingSheafCompInv`, as the chart projection of `g_*`
followed by the chart projection of `f_*`.**

This is the common-index comparison the deformation theory of [Stacks Project, Tag 0CKE] needs:
the right hand side is the reading of a section of `(f ≫ g)_*O` over `W` at a chart of `X` above
`X ×_Z W`, an index depending only on the composite, and the left hand side is its reading
through a chart of `Y`, the index of which depends on the splitting of the composite.  So two
sections of `(f ≫ g)_*O` whose one-step readings agree have agreeing two-step readings for
*every* splitting, which is what makes the readings of two morphisms agreeing on a thickening
comparable. -/
theorem directImageChartProjection_pushforwardRingSheafCompInv (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u})
    (a : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Z.1)
      (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O).obj.obj (op W))) :
    (directImageChartProjection B S hS f j.right.unop k).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj O)
        ((directImageChartProjection B S hS g W j).app
          ((smallEtaleDirectImage B S hS f).obj
            ((sheafCompose (SmallEtale.topology B S hS X.1)
              (CategoryTheory.forget RingCat.{u})).obj O))
          ((pushforwardRingSheafCompInv B S hS f g O).hom.app (op W) a)) =
      (directImageChartProjection B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (CategoryTheory.forget RingCat.{u})).obj O) a := by
  set F := (sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).obj O
  have hcancel := Sheaf.hom_congr_app_apply
    ((smallToposMorphismTypeU_comp B S hS f g).app F).inv_hom_id (op W) a
  exact (directImageChartProjection_smallToposMorphismTypeU_comp B S hS f g W j k F
    (((smallToposMorphismTypeU_comp B S hS f g).inv.app F).hom.app (op W) a)).symm.trans
    (congrArg ((directImageChartProjection B S hS (f ≫ g) W
      (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app F) hcancel)

end AlgebraicGeometry.Space

end
