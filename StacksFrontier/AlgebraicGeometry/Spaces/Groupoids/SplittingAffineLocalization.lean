module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingEtaleScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingAffineLocalization

/-!
# Shrinking a splitting to an affine étale neighbourhood

Let `(U, R, s, t, c)` be a groupoid scheme in the splitting situation of Stacks 0DTB at a point
`u` of `U`, with `U` affine and with `s` and `t` flat and locally of finite presentation.
**Stacks 0DTD** supplies a scheme `U'`, a separated étale morphism `U' ⟶ U`, a point `u'` of
`U'` over `u` with `κ(u) = κ(u')`, and a splitting `P` of `R' = R|_{U'}` over `u'`.  Then `U'`
can be shrunk to an *affine* étale neighbourhood: there is an affine open `U'' ⊆ U'` containing
`u'` such that the restriction of `R'` to `U''` is split over `u'`.  This is **Stacks 0DTE**.

The argument is the one of Stacks 04RZ with "strong splitting" replaced by "splitting" and the
appeal to Stacks 04RX replaced by an appeal to Stacks 0DTD.  Its first three paragraphs use
nothing about the splitting beyond conditions (a) and (b) of Stacks 04RK, so they are shared
verbatim with the strongly split case, as
`Stacks.Groupoids.GroupoidScheme.exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid`:
the source and the target of `P` are finite locally free, so the orbit of `u'` under `P` is a
finite set of points, which lies in an affine open because `U` is affine and `U' ⟶ U` is
separated and quasi-finite, and Stacks 03JE then produces a `P`-invariant affine open
`U'' ⊆ U'` containing `u'`.  The last paragraph differs: condition (c) of part (2) of
Stacks 04RK is a condition on the *stabilizer*, and a point of the stabilizer of `R'|_{U''}`
over `u'` maps to a point of the stabilizer of `R'` over `u'`, whose arrow therefore lies in `P`
and, its source lying in `U''`, already lies in `P|_{U''}`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.Splitting` and
  `Stacks.Groupoids.GroupoidScheme.IsSplitAt`: part (2) of Stacks 04RK for a groupoid scheme —
  an open finite subgroupoid containing the arrow of every point of the stabilizer group scheme
  lying over the given point — and the assertion that one exists.
* `Stacks.Groupoids.GroupoidScheme.EtaleSplitting`: the output of **Stacks 0DTD** in the form
  its consumer uses.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Splitting.compIso`: a splitting of a realization
  of a restriction, transported along the comparison of two restrictions.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isSplitAt_restrictInvariantOpen`: the last paragraph of the
  proof, isolated.  The restriction of a splitting to an invariant open of the object scheme is
  a splitting of the restricted groupoid over every point of that open lying over the given
  point.
* `Stacks.Groupoids.GroupoidScheme.isSplitAt_of_contains_stabilizer` and
  `Stacks.Groupoids.GroupoidScheme.exists_etale_separated_scheme_isSplitAt_scheme`: the output
  of **Stacks 0DTD**, de-realized to the level of schemes.
* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isSplitAt`: **Stacks 0DTE**.

## Implementation notes

Both the hypothesis and the conclusion are about restrictions of groupoid schemes, which this
library realizes by `AlgebraicGeometry.GroupoidScheme.Restriction`, and the conclusion is stated
for an arbitrary groupoid scheme realizing the restriction rather than for the one built by
`Classical.choice`; the ambient groupoid of the conclusion is the restriction of `R' = R|_{U'}`
to `U''` rather than the restriction of `R` to `U''`.  Both readings are those of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/StrongSplittingAffineLocalization.lean`, whose
construction of the restricted subgroupoid is reused here unchanged.

The de-realization of the splitting is the one piece with no analogue in the strongly split
case.  A splitting of a groupoid *scheme* is a condition on the points of the stabilizer scheme
`AlgebraicGeometry.stabilizer`, while Stacks 0DTD delivers a condition on the points of the
stabilizer of a groupoid in algebraic spaces; the two are matched by sending a point `g` of the
stabilizer scheme to the field-valued point of the stabilizer space whose arrow and whose base
point are the images of `g` under the two projections of the stabilizer, which are a composable
pair precisely because the source and the target of the arrow of `g` agree *as morphisms* and
not merely as points.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 04MW](https://stacks.math.columbia.edu/tag/04MW)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RZ](https://stacks.math.columbia.edu/tag/04RZ)
* [Stacks Project, Tag 07S0](https://stacks.math.columbia.edu/tag/07S0)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 0DTD](https://stacks.math.columbia.edu/tag/0DTD)
* [Stacks Project, Tag 0DTE](https://stacks.math.columbia.edu/tag/0DTE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_splittingAffineLocalization
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_splittingAffineLocalization
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_splittingAffineLocalization.has_limit _

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}
  {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) {g : U₂ ⟶ G.objects}
  (R : Restriction G g) (R' : Restriction G (E.hom ≫ g))

/-! ### Transporting a splitting across the comparison of two restrictions -/

/-- The comparison of the stabilizers of the two restrictions: the point of the stabilizer of the
restriction along `g` with the image arrow and the image base point. -/
def stabilizerCompMap : (stabilizer R'.groupoid).left ⟶ (stabilizer R.groupoid).left :=
  pullback.lift
    (stabilizerArrow R'.groupoid ≫ (Restriction.arrowsCompIso E R R').hom.hom)
    ((stabilizer R'.groupoid).hom ≫ (Restriction.objectsCompHom E R R').hom)
    (stabilizerArrow_condition R.groupoid _ _
      (by rw [Category.assoc, Restriction.arrowsCompIso_hom_hom_comp_source,
        ← Category.assoc, stabilizerArrow_source])
      (by rw [Category.assoc, Restriction.arrowsCompIso_hom_hom_comp_target,
        ← Category.assoc, stabilizerArrow_target]))

/-- The arrow underlying the image of a point of the stabilizer is the image of its arrow. -/
theorem stabilizerCompMap_comp_stabilizerArrow :
    stabilizerCompMap E R R' ≫ stabilizerArrow R.groupoid =
      stabilizerArrow R'.groupoid ≫ (Restriction.arrowsCompIso E R R').hom.hom :=
  pullback.lift_fst _ _ _

/-- The image of a point of the stabilizer lies over the image of the point it lies over. -/
theorem stabilizerCompMap_comp_hom :
    stabilizerCompMap E R R' ≫ (stabilizer R.groupoid).hom =
      (stabilizer R'.groupoid).hom ≫ (Restriction.objectsCompHom E R R').hom :=
  pullback.lift_snd _ _ _

/-- **A splitting, pulled back along the comparison.**  The preimage of a splitting at a point of
the object space of a realization of the restriction along `g` is a splitting at any point of the
object space of a realization of the restriction along `E.hom ≫ g` which the comparison of the
object spaces carries to it. -/
def Splitting.compIso {u : Space.points C S hS R.groupoid.objects.obj}
    (P : Splitting R.groupoid u)
    (u' : Space.points C S hS R'.groupoid.objects.obj)
    (hu : Space.pointsMap C S hS R'.groupoid.objects.obj
      (Restriction.objectsCompHom E R R').hom u' = u) :
    Splitting R'.groupoid u' :=
  { OpenFiniteSubgroupoid.compIso E R R' P.toOpenFiniteSubgroupoid with
    contains_stabilizer := by
      intro h hh
      have hhom : Space.pointsMap C S hS (stabilizer R.groupoid).left
          (stabilizer R.groupoid).hom
          (Space.pointsMap C S hS (stabilizer R'.groupoid).left
            (stabilizerCompMap E R R') h) = u := by
        rw [← Space.pointsMap_comp_apply, stabilizerCompMap_comp_hom,
          Space.pointsMap_comp_apply, hh]
        exact hu
      obtain ⟨q, hq⟩ := P.contains_stabilizer (Space.pointsMap C S hS
        (stabilizer R'.groupoid).left (stabilizerCompMap E R R') h) hhom
      obtain ⟨q', hq'⟩ := OpenFiniteSubgroupoid.exists_pointsMap_compIso E R R'
        P.toOpenFiniteSubgroupoid q
      refine ⟨q', ?_⟩
      refine pointsMap_injective_of_isIso (Restriction.arrowsCompIso E R R').hom.hom ?_
      change Space.pointsMap C S hS R'.groupoid.arrows.obj
          (Restriction.arrowsCompIso E R R').hom.hom
          (Space.pointsMap C S hS
            (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).toFunctor
            (P.arrows.preimage (Restriction.arrowsCompIso E R R').hom.hom).ι q') = _
      rw [← Space.pointsMap_comp_apply, hq', hq, ← Space.pointsMap_comp_apply,
        stabilizerCompMap_comp_stabilizerArrow, Space.pointsMap_comp_apply] }

/-- **A splitting across an equality of restricting morphisms.**  A splitting of a realization of
the restriction along `g` gives one of a realization of the restriction along any morphism equal
to `g` precomposed with an isomorphism. -/
theorem nonempty_splitting_of_eq {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂)
    {g : U₂ ⟶ G.objects} (R : Restriction G g)
    {u : Space.points C S hS R.groupoid.objects.obj} (Q : Splitting R.groupoid u)
    (m : U₁ ⟶ G.objects) (hm : E.hom ≫ g = m) (Rm : Restriction G m)
    (u' : Space.points C S hS Rm.groupoid.objects.obj)
    (hu' : Space.pointsMap C S hS Rm.groupoid.objects.obj
      (eqToHom Rm.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm).hom u' = u) :
    Nonempty (Splitting Rm.groupoid u') := by
  subst hm
  exact ⟨Splitting.compIso E R Rm Q u' hu'⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {H : GroupoidScheme S}

/-! ### Splittings of a groupoid scheme -/

/-- A splitting of a groupoid scheme `R` over a point `u` of its object scheme: an open
subscheme `P ⊆ R` which is a groupoid scheme on the same object scheme with `s|_P` and `t|_P`
finite, and which contains the arrow underlying every point of the stabilizer group scheme
lying over `u`. -/
structure Splitting (G : GroupoidScheme S) (u : G.objects.left) extends
    OpenFiniteSubgroupoid G where
  /-- Every point of the stabilizer lying over `u` has its underlying arrow in the
  subgroupoid. -/
  contains_stabilizer : ∀ g : (AlgebraicGeometry.stabilizer G).left,
    (AlgebraicGeometry.stabilizer G).hom.base g = u →
      ∃ p : subgroupoid.arrows.left,
        inclusion.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow G).base g

/-- A groupoid scheme is *split* over a point of its object scheme when a splitting there
exists. -/
abbrev IsSplitAt (G : GroupoidScheme S) (u : G.objects.left) : Prop :=
  Nonempty (Splitting G u)

/-! ### The stabilizer of a groupoid scheme -/

/-- The projection of the stabilizer to the arrow scheme has source the point it lies over. -/
theorem stabilizerFst_comp_source (G : GroupoidScheme S) :
    pullback.fst (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G) ≫ G.source =
      pullback.snd (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G) := by
  have h := pullback.condition (f := AlgebraicGeometry.sourceTarget G)
    (g := AlgebraicGeometry.diagonal G)
  rw [← Category.comp_id (pullback.snd (AlgebraicGeometry.sourceTarget G)
      (AlgebraicGeometry.diagonal G)),
    ← CartesianMonoidalCategory.lift_snd (𝟙 G.objects) (𝟙 G.objects), ← Category.assoc, ← h]
  simp [AlgebraicGeometry.sourceTarget]

/-- The projection of the stabilizer to the arrow scheme has target the point it lies over. -/
theorem stabilizerFst_comp_target (G : GroupoidScheme S) :
    pullback.fst (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G) ≫ G.target =
      pullback.snd (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G) := by
  have h := pullback.condition (f := AlgebraicGeometry.sourceTarget G)
    (g := AlgebraicGeometry.diagonal G)
  rw [← Category.comp_id (pullback.snd (AlgebraicGeometry.sourceTarget G)
      (AlgebraicGeometry.diagonal G)),
    ← CartesianMonoidalCategory.lift_fst (𝟙 G.objects) (𝟙 G.objects), ← Category.assoc, ← h]
  simp [AlgebraicGeometry.sourceTarget]

/-- A morphism out of the arrow scheme which sends the arrow of the stabilizer to the point it lies
over does so on points. -/
private theorem base_stabilizerArrow_of_fst_comp_eq (G : GroupoidScheme S)
    (f : G.arrows ⟶ G.objects)
    (hf : pullback.fst (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G) ≫ f =
      pullback.snd (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G))
    (g : (AlgebraicGeometry.stabilizer G).left) :
    f.left.base ((AlgebraicGeometry.stabilizerArrow G).base g) =
      (AlgebraicGeometry.stabilizer G).hom.base g := by
  have h := congrArg
    (fun k : pullback (AlgebraicGeometry.sourceTarget G) (AlgebraicGeometry.diagonal G) ⟶
      G.objects => k.left.base g) hf
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
  exact h

/-- The underlying arrow of a point of the stabilizer has source that point of the object
scheme. -/
theorem source_stabilizerArrow (G : GroupoidScheme S)
    (g : (AlgebraicGeometry.stabilizer G).left) :
    G.source.left.base ((AlgebraicGeometry.stabilizerArrow G).base g) =
      (AlgebraicGeometry.stabilizer G).hom.base g :=
  base_stabilizerArrow_of_fst_comp_eq G _ (stabilizerFst_comp_source G) g

/-- The underlying arrow of a point of the stabilizer has target that point of the object
scheme. -/
theorem target_stabilizerArrow (G : GroupoidScheme S)
    (g : (AlgebraicGeometry.stabilizer G).left) :
    G.target.left.base ((AlgebraicGeometry.stabilizerArrow G).base g) =
      (AlgebraicGeometry.stabilizer G).hom.base g :=
  base_stabilizerArrow_of_fst_comp_eq G _ (stabilizerFst_comp_target G) g

/-! ### Restricting a splitting to an invariant open -/

/-- Let `P` be a splitting of a groupoid scheme `R` over a point `u` of its object scheme, let
`V` be a `P`-invariant open of the object scheme and let `R|_V` be the restriction of `R` along
`V`.  Then the restriction of `P` to `V` is a splitting of `R|_V` over every point of `V` lying
over `u`.

A point of the stabilizer of `R|_V` lying over such a point has an image in the stabilizer of
`R` lying over `u`, so its underlying arrow lies in `P`; that arrow has its source in `V`, so it
already lies in the restriction of `P` to `V`. -/
theorem isSplitAt_restrictInvariantOpen {u : H.objects.left} (P : Splitting H u)
    (V : P.subgroupoid.objects.left.Opens) (hV : IsInvariantOpen P.subgroupoid V)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction H
      (invariantOpenToObjects P.toOpenFiniteSubgroupoid V hV))
    (w : R.groupoid.objects.left) (hw : R.hom.mapObjects.left.base w = u) :
    IsSplitAt R.groupoid w := by
  have hmapArrows := isOpenImmersion_restriction_mapArrows
    (invariantOpenToObjects P.toOpenFiniteSubgroupoid V hV) R
  have hisoObjects : IsIso P.inclusion.mapObjects.left := by
    rw [P.mapObjects_eq]
    exact inferInstanceAs (IsIso ((Over.forget S).map (eqToHom P.objects_eq)))
  refine ⟨{ invariantOpenSubgroupoidRestriction P.toOpenFiniteSubgroupoid V hV R with
    contains_stabilizer := ?_ }⟩
  intro g hg
  -- an endpoint of the arrow of `R|_V` underlying the point of the stabilizer, and its image
  set r := (AlgebraicGeometry.stabilizerArrow R.groupoid).base g with hrdef
  have hends : ∀ (a : R.groupoid.arrows.left ⟶ R.groupoid.objects.left)
      (b : H.arrows.left ⟶ H.objects.left),
      R.hom.mapArrows.left ≫ b = a ≫ R.hom.mapObjects.left → a.base r = w →
        b.base (R.hom.mapArrows.left.base r) = u := by
    intro a b hab ha
    have h := congrArg (fun k : R.groupoid.arrows.left ⟶ H.objects.left => k.base r) hab
    simp only [Scheme.Hom.comp_apply] at h
    rw [h, ha, hw]
  have hsrc := hends _ _ R.hom.map_source_left ((source_stabilizerArrow R.groupoid g).trans hg)
  have htgt := hends _ _ R.hom.map_target_left ((target_stabilizerArrow R.groupoid g).trans hg)
  -- the image of the point of the stabilizer in the stabilizer of the ambient groupoid
  have hstabhom := congrArg
    (fun k : (AlgebraicGeometry.stabilizerOverBase R.groupoid).left ⟶ H.objects.left => k.base g)
    (AlgebraicGeometry.stabilizerMap_left_comp_hom R.hom)
  have hstabarr := congrArg
    (fun k : (AlgebraicGeometry.stabilizerOverBase R.groupoid).left ⟶ H.arrows.left => k.base g)
    (AlgebraicGeometry.stabilizerMap_left_comp_stabilizerArrow R.hom)
  simp only [Scheme.Hom.comp_apply] at hstabhom hstabarr
  obtain ⟨p, hp⟩ := P.contains_stabilizer
    ((AlgebraicGeometry.stabilizerMap R.hom).left.base g) (by rw [hstabhom, hg]; exact hw)
  rw [hstabarr, ← hrdef] at hp
  -- the image of `w` in the object scheme of the subgroupoid
  have hwV : (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
      ((eqToHom R.objects_eq).left.base w) ∈ V := by
    have hmem : (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
        ((eqToHom R.objects_eq).left.base w) ∈
          (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.opensRange :=
      Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
    rwa [opensRange_restrictInvariantOpenHom_mapObjects P.subgroupoid V hV] at hmem
  have hobj : P.inclusion.mapObjects.left.base
      ((restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
        ((eqToHom R.objects_eq).left.base w)) = u := by
    have hmo : R.hom.mapObjects = eqToHom R.objects_eq ≫
        ((restrictInvariantOpenHom P.subgroupoid V hV).mapObjects ≫
          P.inclusion.mapObjects) := R.mapObjects_eq
    have h := congrArg (fun k : R.groupoid.objects ⟶ H.objects => k.left.base w) hmo
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h.symm.trans hw
  have hpsrc : P.subgroupoid.source.left.base p =
      (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
        ((eqToHom R.objects_eq).left.base w) := by
    have h := congrArg (fun k : P.subgroupoid.arrows.left ⟶ H.objects.left => k.base p)
      P.inclusion.map_source_left
    simp only [Scheme.Hom.comp_apply] at h
    refine P.inclusion.mapObjects.left.isOpenEmbedding.injective ?_
    rw [← h, hp, hsrc, hobj]
  have hpmem : p ∈ invariantArrows P.subgroupoid V := by
    rw [mem_invariantArrows_iff, hpsrc]
    exact hwV
  obtain ⟨q, hq⟩ : ∃ q, (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows.left.base q = p :=
    Scheme.Hom.mem_opensRange.mp (by
      rw [opensRange_restrictInvariantOpenHom_mapArrows P.subgroupoid V hV]
      exact hpmem)
  refine ⟨q, R.hom.mapArrows.left.isOpenEmbedding.injective ?_⟩
  have hcomp := congrArg
    (fun k : (restrictInvariantOpen P.subgroupoid V hV).arrows ⟶ H.arrows => k.left.base q)
    (invariantOpenMapArrows_arrow P.toOpenFiniteSubgroupoid V hV R)
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at hcomp
  show R.hom.mapArrows.left.base
    ((invariantOpenMapArrows P.toOpenFiniteSubgroupoid V hV R).left.base q) = _
  rw [hcomp, invariantOpenToArrows]
  simp only [Over.comp_left, Scheme.Hom.comp_apply]
  rw [hq, hp]

/-! ### The de-realized splitting -/

section Derealization

open AlgebraicGeometry.Space

/-- The map on points of a morphism of schemes of the site, read through the identification of
the points of a represented presheaf with the points of the representing scheme. -/
theorem pointsMap_yoneda_pointsEquivScheme_symm (C : BigFppfSite.{u}) (hS : C.Contains S)
    {Y Z : Over S} (hY : C.Contains Y.left) (hZ : C.Contains Z.left) (f : Y ⟶ Z) (z : Y.left) :
    Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hY))
        (yoneda.map (schemeSiteMap C hS hY hZ f))
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hY)).symm z) =
      (pointsEquivScheme C S hS (schemeSiteObject C hS hZ)).symm (f.left.base z) := by
  refine injective_pointsToScheme C S hS (schemeSiteObject C hS hZ) ?_
  refine (pointsToScheme_pointsMap_yoneda C S hS (schemeSiteMap C hS hY hZ f) _).trans ?_
  refine Eq.trans ?_ (pointsToScheme_pointsEquivScheme_symm C hS
    (schemeSiteObject C hS hZ) (f.left.base z)).symm
  rw [toScheme_map_schemeSiteMap_eq]
  exact congrArg f.left.base
    (pointsToScheme_pointsEquivScheme_symm C hS (schemeSiteObject C hS hY) z)

variable (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  {X : Over S} (hX : C.Contains X.left) (p : X ⟶ G.objects)
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)
  (Rs : GroupoidInAlgebraicSpaces.Restriction (G.realization C hS hU hR hP)
    (realizationMap G C hS hU hR hP hX p))
  (Q : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid Rs.groupoid)
  (hCP : C.Contains (restrictionComposablePairs G p).left)
  (Gr : AlgebraicGeometry.GroupoidScheme.Restriction G p)

include hX hRA in
/-- The stabilizer of a realization of the restriction lies in the big fppf site: it is a fibre
product of the arrow scheme of the restriction with the scheme being restricted to. -/
theorem contains_stabilizerOverBase :
    C.Contains (AlgebraicGeometry.stabilizerOverBase Gr.groupoid).left := by
  refine C.contains_pullback_left (AlgebraicGeometry.sourceTarget Gr.groupoid)
    (AlgebraicGeometry.diagonal Gr.groupoid) ?_ ?_
  · rw [Gr.arrows_eq]
    exact hRA
  · rw [Gr.objects_eq]
    exact hX

include hA hB hRA hCP in
/-- **A splitting de-realized to the scheme level.**  If a splitting of a realization of the
restriction of the realization of `R` contains the arrow of every point of the stabilizer lying
over the point carried by a point `x` of the object scheme, then the open of the arrow scheme it
cuts out is a splitting of every realization of the restriction over `x`.

A point of the stabilizer of the restriction of the groupoid *scheme* over `x` is read as a
field-valued point of the stabilizer of the realized restriction, its arrow and its base point
being the images of that point under the two projections of the stabilizer; the hypothesis
applies to it, and membership in the open cut out by the splitting is membership of the
corresponding point of the arrow space in the arrows of the splitting. -/
theorem isSplitAt_of_contains_stabilizer (x : Gr.groupoid.objects.left)
    (hcontains : ∀ h : Space.points C S hS
        (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).left,
      Space.pointsMap C S hS (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).left
          (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).hom h =
        derealizedObjectPoint G C hS hU hR hP hX p Rs Gr x →
      ∃ q : Space.points C S hS Q.arrows.toFunctor,
        Space.pointsMap C S hS Q.arrows.toFunctor Q.arrows.ι q =
          Space.pointsMap C S hS (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).left
            (GroupoidInAlgebraicSpaces.stabilizerArrow Rs.groupoid) h) :
    IsSplitAt Gr.groupoid x := by
  have hSt : C.Contains (AlgebraicGeometry.stabilizerOverBase Gr.groupoid).left :=
    contains_stabilizerOverBase G C hX p hRA Gr
  -- the arrow and the base point of a point of the stabilizer, as morphisms of the site
  have hsrc : (yoneda.map (schemeSiteMap C hS hSt hRA
          (pullback.fst (AlgebraicGeometry.sourceTarget Gr.groupoid)
            (AlgebraicGeometry.diagonal Gr.groupoid) ≫ eqToHom Gr.arrows_eq)) ≫
        (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) ≫
        Rs.groupoid.source.hom =
      yoneda.map (schemeSiteMap C hS hSt hX
          (pullback.snd (AlgebraicGeometry.sourceTarget Gr.groupoid)
            (AlgebraicGeometry.diagonal Gr.groupoid) ≫ eqToHom Gr.objects_eq)) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm := by
    rw [Category.assoc, restrictionArrowsSpaceIso_hom_comp_source, ← Category.assoc,
      ← yoneda.map_comp, ← schemeSiteMap_comp]
    refine congrArg (fun k => yoneda.map (schemeSiteMap C hS hSt hX k) ≫
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) ?_
    rw [Category.assoc, ← Gr.source_comp_eqToHom, ← Category.assoc,
      stabilizerFst_comp_source]
  have htgt : (yoneda.map (schemeSiteMap C hS hSt hRA
          (pullback.fst (AlgebraicGeometry.sourceTarget Gr.groupoid)
            (AlgebraicGeometry.diagonal Gr.groupoid) ≫ eqToHom Gr.arrows_eq)) ≫
        (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom) ≫
        Rs.groupoid.target.hom =
      yoneda.map (schemeSiteMap C hS hSt hX
          (pullback.snd (AlgebraicGeometry.sourceTarget Gr.groupoid)
            (AlgebraicGeometry.diagonal Gr.groupoid) ≫ eqToHom Gr.objects_eq)) ≫
        eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm := by
    rw [Category.assoc, restrictionArrowsSpaceIso_hom_comp_target, ← Category.assoc,
      ← yoneda.map_comp, ← schemeSiteMap_comp]
    refine congrArg (fun k => yoneda.map (schemeSiteMap C hS hSt hX k) ≫
      eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm) ?_
    rw [Category.assoc, ← Gr.target_comp_eqToHom, ← Category.assoc,
      stabilizerFst_comp_target]
  -- the de-realized point of the stabilizer of the realized restriction
  obtain ⟨Θ, hΘa, hΘo⟩ : ∃ Θ : yoneda.obj (schemeSiteObject C hS hSt) ⟶
      (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).left,
      Θ ≫ GroupoidInAlgebraicSpaces.stabilizerArrow Rs.groupoid =
          yoneda.map (schemeSiteMap C hS hSt hRA
            (pullback.fst (AlgebraicGeometry.sourceTarget Gr.groupoid)
              (AlgebraicGeometry.diagonal Gr.groupoid) ≫ eqToHom Gr.arrows_eq)) ≫
            (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom ∧
        Θ ≫ (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).hom =
          yoneda.map (schemeSiteMap C hS hSt hX
            (pullback.snd (AlgebraicGeometry.sourceTarget Gr.groupoid)
              (AlgebraicGeometry.diagonal Gr.groupoid) ≫ eqToHom Gr.objects_eq)) ≫
            eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm :=
    ⟨pullback.lift _ _ (GroupoidInAlgebraicSpaces.stabilizerArrow_condition Rs.groupoid _ _
        hsrc htgt),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  refine ⟨{ splittingOpenFiniteSubgroupoid G C hS hU hR hP hX p hA hB hRA Rs Q hCP Gr with
    contains_stabilizer := ?_ }⟩
  intro g hg
  -- the de-realized point of the stabilizer lies over the de-realized point of the object scheme
  have hΘobase : Space.pointsMap C S hS (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).left
      (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).hom
      (Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hSt)) Θ
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hSt)).symm g)) =
      derealizedObjectPoint G C hS hU hR hP hX p Rs Gr x := by
    rw [← Space.pointsMap_comp_apply, hΘo, Space.pointsMap_comp_apply,
      pointsMap_yoneda_pointsEquivScheme_symm]
    refine congrArg (fun z => Space.pointsMap C S hS
      (yoneda.obj (schemeSiteObject C hS hX))
      (eqToHom (restrictionObjectsObj_eq G C hS hU hR hP hX p Rs).symm)
      ((pointsEquivScheme C S hS (schemeSiteObject C hS hX)).symm z)) ?_
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg (fun z : Gr.groupoid.objects.left => (eqToHom Gr.objects_eq).left.base z) hg
  -- and its arrow is the point of the arrow space carried by the arrow of `g`
  have hΘabase : Space.pointsMap C S hS (GroupoidInAlgebraicSpaces.stabilizer Rs.groupoid).left
      (GroupoidInAlgebraicSpaces.stabilizerArrow Rs.groupoid)
      (Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hSt)) Θ
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hSt)).symm g)) =
      Space.pointsMap C S hS (yoneda.obj (schemeSiteObject C hS hRA))
        (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
        ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm
          ((eqToHom Gr.arrows_eq).left.base
            ((AlgebraicGeometry.stabilizerArrow Gr.groupoid).base g))) := by
    rw [← Space.pointsMap_comp_apply, hΘa, Space.pointsMap_comp_apply,
      pointsMap_yoneda_pointsEquivScheme_symm]
    refine congrArg (fun z => Space.pointsMap C S hS
      (yoneda.obj (schemeSiteObject C hS hRA))
      (restrictionArrowsSpaceIso G C hS hU hR hP hX p hA hB hRA Rs).hom
      ((pointsEquivScheme C S hS (schemeSiteObject C hS hRA)).symm z)) ?_
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  -- the arrow lies in the open cut out by the splitting
  have hmem : (eqToHom Gr.arrows_eq).left.base
      ((AlgebraicGeometry.stabilizerArrow Gr.groupoid).base g) ∈
      splittingOpens G C hS hU hR hP hX p hA hB hRA Rs Q := by
    refine (mem_splittingOpens_iff_of_eq G C hS hU hR hP hX p hA hB hRA Rs Q
      (pointsToScheme_pointsEquivScheme_symm C hS (schemeSiteObject C hS hRA)
        ((eqToHom Gr.arrows_eq).left.base
          ((AlgebraicGeometry.stabilizerArrow Gr.groupoid).base g)))).2 ?_
    obtain ⟨q, hq⟩ := hcontains _ hΘobase
    exact ⟨q, hq.trans hΘabase⟩
  refine ⟨⟨(eqToHom Gr.arrows_eq).left.base
    ((AlgebraicGeometry.stabilizerArrow Gr.groupoid).base g), hmem⟩, ?_⟩
  show (splittingIncl G C hS hU hR hP hX p hA hB hRA Rs Q Gr).left.base
    ⟨(eqToHom Gr.arrows_eq).left.base
      ((AlgebraicGeometry.stabilizerArrow Gr.groupoid).base g), hmem⟩ = _
  refine Eq.trans ?_ (eqToHom_arrows_apply_symm G p Gr _)
  show (openOverι (AlgebraicGeometry.restrictionArrows G p)
      (splittingOpens G C hS hU hR hP hX p hA hB hRA Rs Q) ≫
    eqToHom Gr.arrows_eq.symm).left.base ⟨(eqToHom Gr.arrows_eq).left.base
      ((AlgebraicGeometry.stabilizerArrow Gr.groupoid).base g), hmem⟩ = _
  rfl

end Derealization

/-! ### The output of Stacks 0DTD at the level of schemes -/

section Derealized

open AlgebraicGeometry.Space

variable (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  {Y : Over S} (hY : C.Contains Y.left) (q : Y ⟶ G.objects) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  {U' : AlgebraicSpaces C S hS} (e : yoneda.obj (schemeSiteObject C hS hY) ≅ U'.obj)
  (v : U'.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))

/-- **A splitting de-realized.**  A splitting of a realization of the restriction of the
realization of `R` along a morphism from `U'`, at the field-valued point of `U'` of Stacks 0DTD,
is a splitting of every groupoid scheme realizing `R|_Y` over the point of its object scheme
carried by `y`.

The splitting is first transported along the identification of `U'` with the presheaf
represented by `Y`, and then de-realized. -/
theorem isSplitAt_of_derealize
    (hA : C.Contains (pullback q G.target).left)
    (hB : C.Contains (pullback G.source q).left)
    (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G q).left)
    (hCP : C.Contains (restrictionComposablePairs G q).left)
    (g : U' ⟶ (G.realization C hS hU hR hP).objects)
    (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hY hU q))
    (hsplit : GroupoidInAlgebraicSpaces.IsSplitAt
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid
      ((residueSectionValuedPoint G C hS u hK U' v).class C S hS U'.obj))
    (Gr : AlgebraicGeometry.GroupoidScheme.Restriction G q) (y : Y.left)
    (hy : y = (derealizeResiduePoint G C hS hY e u hK v).left.base
      (IsLocalRing.closedPoint (G.objects.left.residueField u))) :
    IsSplitAt Gr.groupoid ((eqToHom Gr.objects_eq.symm).left.base y) := by
  obtain ⟨Q⟩ := hsplit
  have hfix : ∀ w : Space.points C S hS U'.obj,
      pointsMap C S hS U'.obj
        (eqToHom (GroupoidInAlgebraicSpaces.restrict
          (G.realization C hS hU hR hP) g).objects_eq.symm).hom w = w :=
    fun w => congrFun (pointsMap_id C S hS U'.obj) w
  obtain ⟨Q'⟩ := GroupoidInAlgebraicSpaces.nonempty_splitting_of_eq
    (derealizeSpaceIso C hS hY e)
    (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g) Q
    (realizationMap G C hS hU hR hP hY q)
    (derealizeSpaceIso_hom_comp G C hS hU hR hP hY q e g he)
    (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
      (realizationMap G C hS hU hR hP hY q))
    (derealizedObjectPoint G C hS hU hR hP hY q
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        (realizationMap G C hS hU hR hP hY q)) Gr
      ((eqToHom Gr.objects_eq.symm).left.base y))
    ((pointsMap_derealizedObjectPoint_eq G C hS hU hR hP hY q u hK e v g _ _ Gr y hy).trans
      (hfix _))
  exact isSplitAt_of_contains_stabilizer G C hS hU hR hP hY q hA hB hRA _
    Q'.toOpenFiniteSubgroupoid hCP Gr _ Q'.contains_stabilizer

end Derealized

/-- **The output of Stacks 0DTD, at the level of schemes.**  In the splitting situation of
Stacks 0DTB, with the source flat and locally of finite presentation, there are a scheme `Y` over
`S`, a separated étale morphism `q : Y ⟶ U`, and a point `y` of `Y` above `u` with
`κ(u) = κ(y)`, such that every groupoid scheme realizing the restriction `R|_Y` is split over the
point of its object scheme carried by `y`. -/
theorem exists_etale_separated_scheme_isSplitAt_scheme
    (D : AlgebraicGeometry.Space.SplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left) (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (hflat : AlgebraicGeometry.Flat D.groupoid.source.left)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation D.groupoid.source.left) :
    ∃ (Y : Over D.S) (q : Y ⟶ D.groupoid.objects) (y : Y.left),
      AlgebraicGeometry.IsSeparated q.left ∧ AlgebraicGeometry.Etale q.left ∧
      q.left.base y = D.u ∧ IsIso (q.left.residueFieldMap y) ∧
      ∀ Gr : AlgebraicGeometry.GroupoidScheme.Restriction D.groupoid q,
        IsSplitAt Gr.groupoid ((eqToHom Gr.objects_eq.symm).left.base y) := by
  obtain ⟨U', g, hrep, hetale, hsep, v, hv, hsplit⟩ :=
    exists_etale_separated_scheme_split D C hS hU hR hP hK hflat hfp
  obtain ⟨Y, hY, q, e, hqet, he⟩ :=
    exists_etale_scheme_of_isRepresentable D.groupoid C hS hU hR hP U' hrep g hetale
  have hA : C.Contains (pullback q D.groupoid.target).left :=
    C.contains_pullback_left q D.groupoid.target hY hR
  have hB : C.Contains (pullback D.groupoid.source q).left :=
    C.contains_pullback_left D.groupoid.source q hR hY
  have hRA : C.Contains (AlgebraicGeometry.restrictionArrows D.groupoid q).left :=
    C.contains_pullback_left (pullback.snd q D.groupoid.target)
      (pullback.fst D.groupoid.source q) hA hB
  have hCP : C.Contains (restrictionComposablePairs D.groupoid q).left :=
    C.contains_pullback_left (AlgebraicGeometry.restrictionSource D.groupoid q)
      (AlgebraicGeometry.restrictionTarget D.groupoid q) hRA hRA
  obtain ⟨hyu, hyiso⟩ := isIso_residueFieldMap_derealizeResiduePoint D.groupoid C hS hU hY q
    e g.hom he D.u hK v hv
  exact ⟨Y, q, _, isSeparated_derealize D.groupoid C hS hU hY q e g.hom he hsep, hqet,
    hyu, hyiso, fun Gr => isSplitAt_of_derealize D.groupoid C hS hU hR hP hY q D.u hK
      e v hA hB hRA hCP g he hsplit Gr _ rfl⟩

/-! ### Stacks 0DTE -/

/-- The output of **Stacks 0DTD** in the form in which the shrinking step consumes it: a scheme
`U'` with a separated étale morphism `g : U' ⟶ U` to the object scheme of a groupoid scheme `R`,
the restriction `R' = R|_{U'}`, a point `u'` of `U'` above the given point `u` of `U` with
`κ(u) = κ(u')`, and a splitting of `R'` over `u'`.

The point and the splitting are recorded on the object scheme of the restriction, which the
field `AlgebraicGeometry.GroupoidScheme.Restriction.objects_eq` says is `U'` itself. -/
structure EtaleSplitting (G : GroupoidScheme S) (u : G.objects.left) where
  /-- The scheme `U'`. -/
  objects : Over S
  /-- The morphism `g : U' ⟶ U`. -/
  projection : objects ⟶ G.objects
  /-- `g` is separated. -/
  [projection_isSeparated : IsSeparated projection.left]
  /-- `g` is étale. -/
  [projection_etale : Etale projection.left]
  /-- The restriction `R' = R|_{U'}`. -/
  restriction : AlgebraicGeometry.GroupoidScheme.Restriction G projection
  /-- The point `u'` of `U'`, read on the object scheme of `R'`. -/
  point : restriction.groupoid.objects.left
  /-- The point `u'` lies over `u`. -/
  point_over : restriction.hom.mapObjects.left.base point = u
  /-- The residue field extension `κ(u) ⊆ κ(u')` is trivial. -/
  residueFieldMap_isIso : IsIso (restriction.hom.mapObjects.left.residueFieldMap point)
  /-- A splitting of `R'` over `u'`. -/
  splitting : Splitting restriction.groupoid point

attribute [instance] EtaleSplitting.projection_isSeparated EtaleSplitting.projection_etale

/-- **The shrinking step.**  Let `R` be a groupoid scheme with affine object scheme whose source
and target are flat and locally of finite presentation, and let the output of Stacks 0DTD at `u`
be given — a separated étale `g : U' ⟶ U`, the restriction `R' = R|_{U'}`, a point `u'` of `U'`
over `u` with `κ(u) = κ(u')` and a splitting of `R'` over `u'`.  Then there is an affine open
`U'' ⊆ U'` containing `u'` such that the restriction of `R'` to `U''` is split over `u'`.

Nothing about the splitting beyond conditions (a) and (b) of **Stacks 04RK** enters the
production of `U''`; condition (c) at `u'` for the restricted splitting is
`Stacks.Groupoids.GroupoidScheme.isSplitAt_restrictInvariantOpen`. -/
theorem exists_isAffine_isSplitAt_of_etaleSplitting
    {G : GroupoidScheme S} [IsAffine G.objects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    {u : G.objects.left} (E : EtaleSplitting G u) :
    ∃ (U'' : Over S) (j : U'' ⟶ E.restriction.groupoid.objects) (u'' : U''.left),
      IsAffine U''.left ∧ IsOpenImmersion j.left ∧
      Etale (j ≫ E.restriction.hom.mapObjects).left ∧
      (j ≫ E.restriction.hom.mapObjects).left.base u'' = u ∧
      IsIso ((j ≫ E.restriction.hom.mapObjects).left.residueFieldMap u'') ∧
      ∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction E.restriction.groupoid j,
        IsSplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base u'') := by
  -- the morphism from the object scheme of `R'` to `U` is étale
  have hmoEq : E.restriction.hom.mapObjects.left =
      (eqToHom E.restriction.objects_eq).left ≫ E.projection.left := by
    rw [E.restriction.mapObjects_eq]
    rfl
  have hisoEq : IsIso (eqToHom E.restriction.objects_eq).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom E.restriction.objects_eq)))
  have hmoEt : Etale E.restriction.hom.mapObjects.left := by
    rw [hmoEq]
    infer_instance
  -- the shrinking of `U'`, which uses only conditions (a) and (b) of the splitting
  obtain ⟨V, hVinv, w, hVaff, hjw⟩ :=
    exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid E.restriction
      E.splitting.toOpenFiniteSubgroupoid E.point
  refine ⟨(restrictInvariantOpen E.splitting.subgroupoid V hVinv).objects,
    invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv, w, hVaff,
    isOpenImmersion_invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv, ?_,
    ?_, ?_, ?_⟩
  · rw [Over.comp_left]
    infer_instance
  · rw [Over.comp_left, Scheme.Hom.comp_apply, hjw]
    exact E.point_over
  · rw [Over.comp_left, Scheme.residueFieldMap_comp]
    have hjw' : (invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv).left w =
      E.point := hjw
    have h1 : IsIso (E.restriction.hom.mapObjects.left.residueFieldMap
        ((invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv).left w)) := by
      rw [hjw']
      exact E.residueFieldMap_isIso
    have h2 : IsIso
        ((invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv).left.residueFieldMap
          w) := inferInstance
    exact IsIso.comp_isIso' h1 h2
  · intro R''
    refine isSplitAt_restrictInvariantOpen E.splitting V hVinv R'' _ ?_
    have hmo : R''.hom.mapObjects = eqToHom R''.objects_eq ≫
      invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv := R''.mapObjects_eq
    have h := congrArg
      (fun k : R''.groupoid.objects ⟶ E.restriction.groupoid.objects =>
        k.left.base ((eqToHom R''.objects_eq.symm).left.base w)) hmo
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    rw [h, over_eqToHom_apply_symm R''.objects_eq w, hjw]

/-- **The output of Stacks 0DTD as `EtaleSplitting`.**  In the splitting situation of
Stacks 0DTB, with the source flat and locally of finite presentation, there are a scheme `U'`
over `S`, a separated étale `g : U' ⟶ U`, the restriction `R' = R|_{U'}`, a point `u'` of `U'`
over `u` with `κ(u) = κ(u')`, and a splitting of `R'` over `u'`. -/
theorem nonempty_etaleSplitting_scheme
    (D : AlgebraicGeometry.Space.SplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left) (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (hflat : AlgebraicGeometry.Flat D.groupoid.source.left)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation D.groupoid.source.left) :
    Nonempty (EtaleSplitting D.groupoid D.u) := by
  obtain ⟨Y, q, y, hsep, het, hyu, hyiso, hsplit⟩ :=
    exists_etale_separated_scheme_isSplitAt_scheme D C hS hU hR hP hK hflat hfp
  obtain ⟨hpoint, hpiso⟩ := isIso_residueFieldMap_restriction_mapObjects D.groupoid q D.u
    (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q) y hyu hyiso
  obtain ⟨Q⟩ := hsplit (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q)
  exact ⟨{ objects := Y
           projection := q
           projection_isSeparated := hsep
           projection_etale := het
           restriction := AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q
           point := (eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
             D.groupoid q).objects_eq.symm).left.base y
           point_over := hpoint
           residueFieldMap_isIso := hpiso
           splitting := Q }⟩

/-- **Stacks Project, Tag 0DTE.**

In the splitting situation of Stacks 0DTB, with `s` and `t` in addition flat and locally of
finite presentation and with `U` affine, there are an affine scheme `U''`, an étale morphism
`U'' ⟶ U` and a point `u''` of `U''` over `u` with `κ(u) = κ(u'')`, such that the restriction of
`R` to `U''` is split over `u''`.

The étale neighbourhood `U'` of Stacks 0DTD is shrunk to an affine one: `U''` is an invariant
affine open of the object scheme of the splitting of `R' = R|_{U'}`, so `U'' ⟶ U'` is an open
immersion and the restriction of that splitting to `U''` is a splitting of `R'|_{U''}` over
`u''`.  The restriction is taken in two steps, as the restriction of `R'` to `U''`; its
identification with the restriction of `R` along the composite `U'' ⟶ U' ⟶ U` is
Stacks 04MW. -/
@[stacks 0DTE "in Situation 0DTB with s, t flat and locally of finite presentation and U affine:
an affine scheme U'', an étale U'' ⟶ U and a point u'' over u with κ(u) = κ(u''), such that
R|_{U''} is SPLIT over u'' -- all of it PRODUCED: the neighbourhood, the point and the splitting
are conclusions of this theorem, never inputs to it. Splitting is Stacks 04RK part (2) read for a
groupoid scheme, stated in
this file as `Splitting`: an open subscheme P of the arrow scheme which (a) is a groupoid scheme
on the same object scheme, with composition the restriction of the ambient one, (b) has s|_P and
t|_P finite, and (c) contains the arrow underlying every point of the stabilizer group scheme
`AlgebraicGeometry.stabilizer` lying over the point; (a) and (b) are `OpenFiniteSubgroupoid`,
which carries the 04RK attribute, and (c) is the field `contains_stabilizer`. The situation
hypothesis is
`AlgebraicGeometry.Space.SplittingSituation`, which carries the 0DTB attribute, and not the
stronger `StrongSplittingSituation` of Tag 04RL. R|_{U''} is covered in its two-step reading, as
the restriction to U'' of R' = R|_{U'} for the étale neighbourhood U' of Stacks 0DTD, rather
than as the restriction of R along the composite U'' ⟶ U' ⟶ U; the identification of the two is
Stacks 04MW, which this library has as the comparison diagram `doubleRestrictionDiagram` and not
as an identification of realizations. The conclusion is stronger than the tag in two respects:
U'' ⟶ U' is an open immersion, not merely étale, and the splitting is produced for EVERY
groupoid scheme realizing that restriction. Beyond Situation 0DTB the hypotheses are that the
big fppf site contains the base, object, arrow and composable-pair schemes and Spec κ(u), this
library's standing ambient requirement"]
theorem exists_isAffine_isSplitAt
    (D : AlgebraicGeometry.Space.SplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left) (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    [IsAffine D.groupoid.objects.left]
    [Flat D.groupoid.source.left] [LocallyOfFinitePresentation D.groupoid.source.left]
    [Flat D.groupoid.target.left] [LocallyOfFinitePresentation D.groupoid.target.left] :
    ∃ (U' : Over D.S) (g : U' ⟶ D.groupoid.objects)
      (R' : AlgebraicGeometry.GroupoidScheme.Restriction D.groupoid g)
      (U'' : Over D.S) (j : U'' ⟶ R'.groupoid.objects) (u'' : U''.left),
      IsAffine U''.left ∧ IsOpenImmersion j.left ∧
      Etale (j ≫ R'.hom.mapObjects).left ∧
      (j ≫ R'.hom.mapObjects).left.base u'' = D.u ∧
      IsIso ((j ≫ R'.hom.mapObjects).left.residueFieldMap u'') ∧
      ∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction R'.groupoid j,
        IsSplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base u'') := by
  obtain ⟨E⟩ := nonempty_etaleSplitting_scheme D C hS hU hR hP hK inferInstance inferInstance
  obtain ⟨U'', j, u'', hU''⟩ := exists_isAffine_isSplitAt_of_etaleSplitting E
  exact ⟨E.objects, E.projection, E.restriction, U'', j, u'', hU''⟩

end Stacks.Groupoids.GroupoidScheme

end

end
