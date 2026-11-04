module

public import StacksFrontier.AlgebraicGeometry.SegreGlue.Minor
public import StacksFrontier.AlgebraicGeometry.SegreProjection.Projections

/-!
# The two Segre projections, glued

`StacksFrontier/AlgebraicGeometry/SegreProjection/Projections.lean` constructs the partially
defined Segre projections and proves that their domains cover `AlgebraicGeometry.Proj` of the
Segre product, but does not glue them: gluing needs their agreement on overlaps, and that is the
content of `StacksFrontier/AlgebraicGeometry/SegreGlue/Overlap.lean` together with the minor
relation of `StacksFrontier/AlgebraicGeometry/SegreGlue/Minor.lean`.  This file performs the
gluing.

The cover used is **not** the cover by the domains of definition but the finer cover by the
standard charts `D₊(x_i y_j)`, indexed by pairs `(i, j)`.  That is what makes the overlaps
tractable: a chart carries the substitution at `y_j`, and the overlap of the charts at `(i, j)`
and at `(i', k)` is a standard open on which *both* substitutions are defined at the degree-two
element `x_i x_{i'}`, by the minor relation.

## Main definitions

* `Stacks.AlgebraicGeometry.SegreGlue.projLeftGlued`: the projection
  `Proj (Segre product) ⟶ Proj R[x_i]`, defined on the whole of the source.
* `Stacks.AlgebraicGeometry.SegreGlue.projRightGlued`: the mirror image.

## Main results

* `Stacks.AlgebraicGeometry.SegreGlue.mapAwayHom_substLeft_compat`: **the overlap step.**  On the
  overlap of the charts at `(i, j)` and at `(i', k)` the two local morphisms agree.  Its proof is
  the whole argument in miniature: raise `x_i` and `x_{i'}` to the product `x_i x_{i'}`, at which
  both substitutions are defined on the overlap, with
  `Stacks.AlgebraicGeometry.ProjTwistChain.homOfLE_mapAwayHom`, and then compare the two
  substitutions at that one element with
  `Stacks.AlgebraicGeometry.SegreGlue.homOfLE_mapAwayHom_comm`.

* `Stacks.AlgebraicGeometry.SegreGlue.ι_projLeftGlued` and
  `Stacks.AlgebraicGeometry.SegreGlue.ι_projRightGlued`: on the chart at `(i, j)` the glued
  morphism is the morphism of affine schemes attached to the map
  `R[x]_{(x_i)} → S_{(x_i y_j)}` of degree-zero homogeneous localisations.  This is the only
  handle on the glued morphisms, and anything proved about them has to go through it.

* `Stacks.AlgebraicGeometry.SegreGlue.ι_projLeftGlued_eq_projLeft` and
  `Stacks.AlgebraicGeometry.SegreGlue.ι_projRightGlued_eq_projRight`: on each chart the glued
  morphism agrees with the partially defined projection
  `Stacks.AlgebraicGeometry.SegreProjection.projLeft`, so it really is the gluing of those and not
  merely a morphism assembled from the same local data.

* `Stacks.AlgebraicGeometry.SegreGlue.iSup_basicOpen_substLeftGraded_X_eq_top`: the charts cover,
  which is `Stacks.AlgebraicGeometry.SegreCharts.iSup_basicOpen_genSub_eq_top` rewritten along
  `Stacks.AlgebraicGeometry.SegreProjection.substLeftGraded_X`.

## Implementation notes

The gluing is `CategoryTheory.Limits`-free: it is
`AlgebraicGeometry.Scheme.Cover.glueMorphisms` applied to
`AlgebraicGeometry.Scheme.Opens.iSupOpenCover`, whose compatibility condition is stated as a
pullback square and is converted to the square of `AlgebraicGeometry.Scheme.homOfLE`s by
`AlgebraicGeometry.isPullback_opens_inf_le`, exactly as in
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`.  The resulting morphism is out of
`(⨆ p, D₊(x_i y_j)).toScheme`, and is transported to `Proj` of the Segre product by the two
isomorphisms `AlgebraicGeometry.Scheme.topIso` and `AlgebraicGeometry.Scheme.isoOfEq`, as in
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`.

Both gradings are definitions rather than instances in this development, so they are taken as
instance binders, as everywhere else in the Segre files.

## What is not done

Nothing is proved here about the *pair* of glued morphisms, and in particular nothing about
whether the induced morphism to the product of the two projective spaces is an isomorphism; that
is `StacksFrontier/AlgebraicGeometry/SegreGlue/Product.lean`, where it remains open.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.RingTheory.SegreProduct Stacks.RingTheory.SegreProjection
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.SegreProjection

namespace Stacks.AlgebraicGeometry.SegreGlue

universe u v

variable (R : Type u) [CommRing R] (X Y : Type v) [GradedAlgebra (grading R X Y)]

/-! ### The standard charts, written through the substitutions -/

/-- The standard charts cover, written with the chart at `(i, j)` presented as the locus where the
substitution at `y_j` is defined at `x_i`.  Presenting it that way, rather than as `D₊(x_i y_j)`,
is what lets `Stacks.AlgebraicGeometry.ProjTwistChain.mapAwayHom` be applied to the chart with no
transport along an equality of opens. -/
public theorem iSup_basicOpen_substLeftGraded_X_eq_top :
    (⨆ p : X × Y, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (substLeftGraded R X Y p.2 (MvPolynomial.X p.1))) = ⊤ := by
  rw [← SegreCharts.iSup_basicOpen_genSub_eq_top R X Y]
  exact iSup_congr fun p => by rw [substLeftGraded_X]

/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreGlue.iSup_basicOpen_substLeftGraded_X_eq_top`. -/
public theorem iSup_basicOpen_substRightGraded_X_eq_top :
    (⨆ p : X × Y, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
      (substRightGraded R X Y p.1 (MvPolynomial.X p.2))) = ⊤ := by
  rw [← SegreCharts.iSup_basicOpen_genSub_eq_top R X Y]
  exact iSup_congr fun p => by rw [substRightGraded_X]

/-! ### The overlap step -/

variable [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)]

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)] in
/-- **The overlap step for the projection to the first factor.**  The local morphisms attached to
the charts at `p` and at `q` agree on the overlap of those charts, even though they come from two
*different* graded ring homomorphisms. -/
public theorem mapAwayHom_substLeft_compat (p q : X × Y) :
    (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
        (inf_le_left : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substLeftGraded R X Y p.2 (MvPolynomial.X p.1)) ⊓
            AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substLeftGraded R X Y q.2 (MvPolynomial.X q.1)) ≤ _) ≫
        mapAwayHom (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
          (substLeftGraded R X Y p.2) one_pos (X_mem R X p.1) =
      (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
        (inf_le_right : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substLeftGraded R X Y p.2 (MvPolynomial.X p.1)) ⊓
            AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substLeftGraded R X Y q.2 (MvPolynomial.X q.1)) ≤ _) ≫
        mapAwayHom (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
          (substLeftGraded R X Y q.2) one_pos (X_mem R X q.1) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', k⟩ := q
  have hgen : ∀ (a : X) (b : Y), AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y b (MvPolynomial.X a)) =
      AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (a, b)) :=
    fun a b => by rw [substLeftGraded_X]
  have hVl : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y j (MvPolynomial.X i)) ⊓
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y k (MvPolynomial.X i')) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y j (MvPolynomial.X i * MvPolynomial.X i')) := by
    rw [hgen i j, hgen i' k]
    exact inf_basicOpen_genSub_le_substLeft R X Y i i' j k
  have hVr : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y j (MvPolynomial.X i)) ⊓
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y k (MvPolynomial.X i')) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y k (MvPolynomial.X i * MvPolynomial.X i')) := by
    rw [hgen i j, hgen i' k]
    exact inf_basicOpen_genSub_le_substLeft' R X Y i i' j k
  have hVx : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y j (MvPolynomial.X i)) ⊓
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y k (MvPolynomial.X i')) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y j (MvPolynomial.X i * MvPolynomial.X i') *
          substLeftGraded R X Y k (MvPolynomial.X i * MvPolynomial.X i')) := by
    rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact le_inf hVl hVr
  rw [homOfLE_mapAwayHom (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
      (substLeftGraded R X Y j) one_pos two_pos (X_mem R X i) (X_mem R X i')
      (X_mul_X_mem R X i i') rfl hVl inf_le_left,
    homOfLE_mapAwayHom (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
      (substLeftGraded R X Y k) one_pos two_pos (X_mem R X i') (X_mem R X i)
      (X_mul_X_mem R X i i') (mul_comm _ _) hVr inf_le_right]
  exact homOfLE_mapAwayHom_comm (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
    (substLeftGraded R X Y j) (substLeftGraded R X Y k) (crossComm_substLeftGraded R X Y j k)
    two_pos (X_mul_X_mem R X i i') rfl hVx hVl hVr

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)] in
/-- **The overlap step for the projection to the second factor**, the mirror image of
`Stacks.AlgebraicGeometry.SegreGlue.mapAwayHom_substLeft_compat`. -/
public theorem mapAwayHom_substRight_compat (p q : X × Y) :
    (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
        (inf_le_left : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substRightGraded R X Y p.1 (MvPolynomial.X p.2)) ⊓
            AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substRightGraded R X Y q.1 (MvPolynomial.X q.2)) ≤ _) ≫
        mapAwayHom (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
          (substRightGraded R X Y p.1) one_pos (X_mem R Y p.2) =
      (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
        (inf_le_right : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substRightGraded R X Y p.1 (MvPolynomial.X p.2)) ⊓
            AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substRightGraded R X Y q.1 (MvPolynomial.X q.2)) ≤ _) ≫
        mapAwayHom (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
          (substRightGraded R X Y q.1) one_pos (X_mem R Y q.2) := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', k⟩ := q
  have hgen : ∀ (a : X) (b : Y), AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y a (MvPolynomial.X b)) =
      AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (a, b)) :=
    fun a b => by rw [substRightGraded_X]
  have hVl : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i (MvPolynomial.X j)) ⊓
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i' (MvPolynomial.X k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i (MvPolynomial.X j * MvPolynomial.X k)) := by
    rw [hgen i j, hgen i' k]
    exact inf_basicOpen_genSub_le_substRight R X Y i i' j k
  have hVr : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i (MvPolynomial.X j)) ⊓
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i' (MvPolynomial.X k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i' (MvPolynomial.X j * MvPolynomial.X k)) := by
    rw [hgen i j, hgen i' k]
    exact inf_basicOpen_genSub_le_substRight' R X Y i i' j k
  have hVx : AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i (MvPolynomial.X j)) ⊓
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i' (MvPolynomial.X k)) ≤
      AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i (MvPolynomial.X j * MvPolynomial.X k) *
          substRightGraded R X Y i' (MvPolynomial.X j * MvPolynomial.X k)) := by
    rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact le_inf hVl hVr
  rw [homOfLE_mapAwayHom (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
      (substRightGraded R X Y i) one_pos two_pos (X_mem R Y j) (X_mem R Y k)
      (X_mul_X_mem R Y j k) rfl hVl inf_le_left,
    homOfLE_mapAwayHom (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
      (substRightGraded R X Y i') one_pos two_pos (X_mem R Y k) (X_mem R Y j)
      (X_mul_X_mem R Y j k) (mul_comm _ _) hVr inf_le_right]
  exact homOfLE_mapAwayHom_comm (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
    (substRightGraded R X Y i) (substRightGraded R X Y i') (crossComm_substRightGraded R X Y i i')
    two_pos (X_mul_X_mem R Y j k) rfl hVx hVl hVr

/-! ### The glued projections -/

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)] in
/-- **The Segre projection to the first factor.**  The partially defined projections of
`Stacks.AlgebraicGeometry.SegreProjection.projLeft`, glued over the standard charts into a single
morphism defined on the whole of `AlgebraicGeometry.Proj` of the Segre product. -/
public def projLeftGlued :
    AlgebraicGeometry.Proj (grading R X Y) ⟶
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule X R) :=
  (Scheme.topIso _).inv ≫
    ((AlgebraicGeometry.Proj (grading R X Y)).isoOfEq
      (iSup_basicOpen_substLeftGraded_X_eq_top R X Y).symm).hom ≫
    (Scheme.Opens.iSupOpenCover (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen
        (grading R X Y) (substLeftGraded R X Y p.2 (MvPolynomial.X p.1)))).glueMorphisms
      (fun p => mapAwayHom (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
        (substLeftGraded R X Y p.2) one_pos (X_mem R X p.1))
      (fun p q => by
        dsimp only [Scheme.Opens.iSupOpenCover]
        rw [← cancel_epi (AlgebraicGeometry.isPullback_opens_inf_le
            (le_iSup (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substLeftGraded R X Y p.2 (MvPolynomial.X p.1))) p)
            (le_iSup (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substLeftGraded R X Y p.2 (MvPolynomial.X p.1))) q)).isoPullback.hom,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_fst,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_snd]
        exact mapAwayHom_substLeft_compat R X Y p q)

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)] in
/-- **The Segre projection to the second factor**, the mirror image of
`Stacks.AlgebraicGeometry.SegreGlue.projLeftGlued`. -/
public def projRightGlued :
    AlgebraicGeometry.Proj (grading R X Y) ⟶
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule Y R) :=
  (Scheme.topIso _).inv ≫
    ((AlgebraicGeometry.Proj (grading R X Y)).isoOfEq
      (iSup_basicOpen_substRightGraded_X_eq_top R X Y).symm).hom ≫
    (Scheme.Opens.iSupOpenCover (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen
        (grading R X Y) (substRightGraded R X Y p.1 (MvPolynomial.X p.2)))).glueMorphisms
      (fun p => mapAwayHom (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
        (substRightGraded R X Y p.1) one_pos (X_mem R Y p.2))
      (fun p q => by
        dsimp only [Scheme.Opens.iSupOpenCover]
        rw [← cancel_epi (AlgebraicGeometry.isPullback_opens_inf_le
            (le_iSup (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substRightGraded R X Y p.1 (MvPolynomial.X p.2))) p)
            (le_iSup (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
              (substRightGraded R X Y p.1 (MvPolynomial.X p.2))) q)).isoPullback.hom,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_fst,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_snd]
        exact mapAwayHom_substRight_compat R X Y p q)

/-! ### The glued projections on a standard chart -/

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)] in
/-- **The glued projection on a standard chart.**  On `D₊(x_i y_j)` the projection to the first
factor is the morphism of affine schemes attached to the map `R[x]_{(x_i)} → S_{(x_i y_j)}` of
degree-zero homogeneous localisations. -/
@[reassoc]
public theorem ι_projLeftGlued (p : X × Y) :
    (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y p.2 (MvPolynomial.X p.1))).ι ≫ projLeftGlued R X Y =
      mapAwayHom (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
        (substLeftGraded R X Y p.2) one_pos (X_mem R X p.1) := by
  have h0 : (Scheme.topIso (AlgebraicGeometry.Proj (grading R X Y))).inv ≫
      ((AlgebraicGeometry.Proj (grading R X Y)).isoOfEq
        (iSup_basicOpen_substLeftGraded_X_eq_top R X Y).symm).hom ≫
        (⨆ p : X × Y, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substLeftGraded R X Y p.2 (MvPolynomial.X p.1))).ι =
      𝟙 (AlgebraicGeometry.Proj (grading R X Y)) := by
    rw [Scheme.isoOfEq_hom_ι]
    simp
  have h1 : (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y p.2 (MvPolynomial.X p.1))).ι ≫
      (Scheme.topIso (AlgebraicGeometry.Proj (grading R X Y))).inv ≫
      ((AlgebraicGeometry.Proj (grading R X Y)).isoOfEq
        (iSup_basicOpen_substLeftGraded_X_eq_top R X Y).symm).hom =
      (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
        (le_iSup (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substLeftGraded R X Y p.2 (MvPolynomial.X p.1))) p) := by
    rw [← cancel_mono (Scheme.Opens.ι _), Scheme.homOfLE_ι, Category.assoc, Category.assoc, h0,
      Category.comp_id]
  rw [projLeftGlued, reassoc_of% h1]
  exact (Scheme.Opens.iSupOpenCover (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen
    (grading R X Y) (substLeftGraded R X Y p.2 (MvPolynomial.X p.1)))).ι_glueMorphisms _ _ p

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)] in
/-- The mirror image of `Stacks.AlgebraicGeometry.SegreGlue.ι_projLeftGlued`. -/
@[reassoc]
public theorem ι_projRightGlued (p : X × Y) :
    (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y p.1 (MvPolynomial.X p.2))).ι ≫ projRightGlued R X Y =
      mapAwayHom (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
        (substRightGraded R X Y p.1) one_pos (X_mem R Y p.2) := by
  have h0 : (Scheme.topIso (AlgebraicGeometry.Proj (grading R X Y))).inv ≫
      ((AlgebraicGeometry.Proj (grading R X Y)).isoOfEq
        (iSup_basicOpen_substRightGraded_X_eq_top R X Y).symm).hom ≫
        (⨆ p : X × Y, AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substRightGraded R X Y p.1 (MvPolynomial.X p.2))).ι =
      𝟙 (AlgebraicGeometry.Proj (grading R X Y)) := by
    rw [Scheme.isoOfEq_hom_ι]
    simp
  have h1 : (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y p.1 (MvPolynomial.X p.2))).ι ≫
      (Scheme.topIso (AlgebraicGeometry.Proj (grading R X Y))).inv ≫
      ((AlgebraicGeometry.Proj (grading R X Y)).isoOfEq
        (iSup_basicOpen_substRightGraded_X_eq_top R X Y).symm).hom =
      (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
        (le_iSup (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen (grading R X Y)
          (substRightGraded R X Y p.1 (MvPolynomial.X p.2))) p) := by
    rw [← cancel_mono (Scheme.Opens.ι _), Scheme.homOfLE_ι, Category.assoc, Category.assoc, h0,
      Category.comp_id]
  rw [projRightGlued, reassoc_of% h1]
  exact (Scheme.Opens.iSupOpenCover (fun p : X × Y => AlgebraicGeometry.Proj.basicOpen
    (grading R X Y) (substRightGraded R X Y p.1 (MvPolynomial.X p.2)))).ι_glueMorphisms _ _ p

/-! ### The glued projections really do glue the partial projections -/

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule Y R)] in
/-- **The glued projection restricts to the partial projection.**  On the chart at `(i, j)` the
morphism `Stacks.AlgebraicGeometry.SegreGlue.projLeftGlued` agrees with
`Stacks.AlgebraicGeometry.SegreProjection.projLeft R X Y j`, which is defined only on the domain of
definition of the substitution at `y_j`.  This is what makes the glued morphism *the* gluing of the
partial projections rather than merely a morphism built from the same local data. -/
public theorem ι_projLeftGlued_eq_projLeft (i : X) (j : Y) :
    (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substLeftGraded R X Y j (MvPolynomial.X i))).ι ≫ projLeftGlued R X Y =
      (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
          (basicOpen_le_mapDomain (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
            (substLeftGraded R X Y j) one_pos (X_mem R X i)) ≫
        projLeft R X Y j := by
  rw [projLeft, homOfLE_mapHom, ι_projLeftGlued R X Y (i, j)]

omit [GradedAlgebra (MvPolynomial.homogeneousSubmodule X R)] in
/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreGlue.ι_projLeftGlued_eq_projLeft`. -/
public theorem ι_projRightGlued_eq_projRight (i : X) (j : Y) :
    (AlgebraicGeometry.Proj.basicOpen (grading R X Y)
        (substRightGraded R X Y i (MvPolynomial.X j))).ι ≫ projRightGlued R X Y =
      (AlgebraicGeometry.Proj (grading R X Y)).homOfLE
          (basicOpen_le_mapDomain (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
            (substRightGraded R X Y i) one_pos (X_mem R Y j)) ≫
        projRight R X Y i := by
  rw [projRight, homOfLE_mapHom, ι_projRightGlued R X Y (i, j)]

end Stacks.AlgebraicGeometry.SegreGlue

end
