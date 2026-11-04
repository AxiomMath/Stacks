module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.RestrictionAffineQuotient
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.KernelPair
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.OpenSaturation
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveCoproduct
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaDesc
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient of a finite locally free groupoid scheme by a scheme

Let `(U, R, s, t, c)` be a groupoid scheme over a scheme `S` whose source and target maps are
finite locally free and whose pair of target and source maps is an equivalence relation, and
let `V` be an invariant affine open of `U`.  The restriction of the groupoid to `V` has an
affine quotient `M_V` (Stacks 03BM), and `M_V` is an open subspace of the fppf quotient sheaf
`U/R` (Stacks 02WU).  The square formed by `V ⟶ U`, `V ⟶ M_V`, `M_V ⟶ U/R` and the projection
`U ⟶ U/R` is Cartesian; this is Stacks 07S3 applied to the restriction, whose square on source
maps is Cartesian because `V` is invariant.

These are the charts out of which a scheme representing `U/R` is glued, and glueing them is
Stacks 07S6: when in addition every nonempty closed subset of `U` contains a point whose
`R`-equivalence class lies in an affine open, the invariant affine opens cover `U`, so the
charts cover `U/R` and the glued scheme represents it.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_schemeQuotient`: **Stacks 07S6**, the quotient
  scheme, its finite locally free surjection from `U`, the kernel-pair square and the
  representation of the fppf quotient sheaf.
* `AlgebraicGeometry.GroupoidScheme.exists_schemeQuotient_of_isFiniteLocallyFree_relation`: the
  same for an equivalence relation `t, s : R ⟶ U` rather than a groupoid scheme, under the
  stronger hypothesis that every finite set of points of `U` lies in an affine open.
* `AlgebraicGeometry.GroupoidScheme.exists_chart_of_isInvariantAffineOpen`: the chart attached
  to an invariant affine open, with its open immersion into `U`, its finite locally free
  projection, its representable open immersion into `U/R`, its size bound and its Cartesian
  square.
* `AlgebraicGeometry.Space.pointsYonedaIso_hom_comp` and
  `AlgebraicGeometry.Space.whiskerLeft_yonedaMap_comp`: naturality and multiplicativity of the
  comparison between restricted functors of points and represented presheaves.

## Implementation notes

The comparison isomorphism `AlgebraicGeometry.Space.pointsYonedaIso` identifies the restricted
functor of points of the image of a site object with the presheaf that object represents.  The
two sides are equal only up to an unfolding of the inclusion of the site into `S`-schemes, so
every composite in which both occur is type-correct only at default transparency, and `rw`
cannot see through it.  The comparison isomorphisms are therefore introduced with their types
written in terms of the `S`-schemes they are about rather than in terms of the site objects,
after which the rewriting is purely formal.

For the same reason the data of the restriction of the groupoid are taken as explicit
arguments of `AlgebraicGeometry.GroupoidScheme.exists_chart_aux` rather than produced inside
it: `AlgebraicGeometry.GroupoidScheme.restrict` is a choice from a large construction, and a
conclusion mentioning it is expensive to elaborate.

The charts are indexed by the invariant affine opens of `U` rather than by the points of `U`:
the cardinality of a set of opens of `U` is bounded by the size of `U`, whereas the cardinality
of the point set of `U` is not, and the size-restricted site asks of a covering family a bound
of the first kind.

## References

* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Groupoids Stacks.Morphisms

universe u v

namespace AlgebraicGeometry.Space

/-- An isomorphism of schemes over `S` induces an isomorphism of the functors of points
restricted along a functor presenting a site of `S`-schemes. -/
def pointsMapIso {C : Type v} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S)
    {X Y : Over S} (α : X ≅ Y) :
    Stacks.Groupoids.points F X ≅ Stacks.Groupoids.points F Y :=
  Functor.isoWhiskerLeft F.op (yoneda.mapIso α)

/-- The forward map of `AlgebraicGeometry.Space.pointsMapIso F α` is the whiskering along `F.op`
of the Yoneda image of `α.hom`. -/
@[simp]
theorem pointsMapIso_hom {C : Type v} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S)
    {X Y : Over S} (α : X ≅ Y) :
    (pointsMapIso F α).hom = F.op.whiskerLeft (yoneda.map α.hom) :=
  rfl

/-- Maps of restricted functors of points compose. -/
theorem whiskerLeft_yonedaMap_comp {C : Type v} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S)
    {X Y Z : Over S} (a : X ⟶ Y) (b : Y ⟶ Z) :
    F.op.whiskerLeft (yoneda.map a) ≫ F.op.whiskerLeft (yoneda.map b) =
      F.op.whiskerLeft (yoneda.map (a ≫ b)) := by
  rw [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp]

/-- The comparison isomorphisms of `AlgebraicGeometry.Space.pointsYonedaIso` are natural. -/
theorem pointsYonedaIso_hom_comp {C : Type v} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S)
    [F.Full] [F.Faithful] {X Y : C} (φ : X ⟶ Y) :
    F.op.whiskerLeft (yoneda.map (F.map φ)) ≫ (pointsYonedaIso F Y).hom =
      (pointsYonedaIso F X).hom ≫ yoneda.map φ := by
  have h := pointsYonedaIso_inv_comp F (F.map φ)
  rw [F.preimage_map] at h
  rw [← h]
  simp

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidScheme

/-- The object scheme of a groupoid scheme, regarded as an object of the big fppf category over
the base when it satisfies the size bound of the site. -/
abbrev objectsSite (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hU G.objects.hom

/-- The comparison between the restricted functor of points of the object scheme of a groupoid
scheme and the presheaf represented by that scheme as an object of the site. -/
noncomputable abbrev objectsPointsIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : GroupoidScheme S) (hU : B.Contains G.objects.left) :
    Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) G.objects ≅
      yoneda.obj (objectsSite B S hS G hU) :=
  Space.pointsYonedaIso (Over.post B.inclusion) (objectsSite B S hS G hU)

/-- The canonical map from the presheaf represented by the object scheme of a groupoid scheme,
as an object of the site, to the fppf quotient sheaf of the groupoid. -/
noncomputable abbrev yonedaToQuotientSheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left) :
    yoneda.obj (objectsSite B S hS G hU) ⟶
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (groupoidPreRelation G)).obj :=
  (objectsPointsIso B S hS G hU).inv ≫
    toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) (groupoidPreRelation G)

/-- `AlgebraicGeometry.GroupoidScheme.exists_chart_of_isInvariantAffineOpen` with the
restriction of the groupoid, its affine quotient and the open-immersion property of the induced
map of quotient sheaves taken as explicit arguments. -/
private theorem exists_chart_aux (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) [IsEquivalenceRelation G.target G.source]
    (hU : B.Contains G.objects.left) (V : G.objects.left.Opens)
    (g : Over.mk (V.ι ≫ G.objects.hom) ⟶ G.objects) (hg : g.left = V.ι)
    [IsOpenImmersion g.left] (hinv : IsInvariantSet G (Set.range g.left.base))
    (H : Restriction G g) {A : Type u} [CommRing A] {q : Spec (CommRingCat.of A) ⟶ S}
    (π : H.groupoid.objects ⟶ Over.mk q)
    (hVsize : B.Contains (V : Scheme.{u})) (hAsize : B.Contains (Spec (CommRingCat.of A)))
    (hsize : (Spec (CommRingCat.of A)).size ≤ G.objects.left.size)
    (hflfπ : IsFiniteLocallyFree π.left) (hsurjπ : Surjective π.left)
    (hpb : IsPullback H.groupoid.target H.groupoid.source π π)
    (h02WU : Space.IsOpenImmersion B S hS
      (restrictionQuotientMap (BigFppfOver.topology B S hS) (Over.post B.inclusion) G g H).hom) :
    ∃ (Vo Xo : BigFppfOver B S hS) (v : Vo ⟶ objectsSite B S hS G hU) (c : Vo ⟶ Xo)
      (f : yoneda.obj Xo ⟶ (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation G)).obj),
      ((BigFppfOver.toScheme B S hS).obj Xo).size ≤ G.objects.left.size ∧
        IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map v).base = (V : Set G.objects.left) ∧
        (openImmersionOver B S hS).presheaf f ∧
        IsFiniteLocallyFree ((Over.post B.inclusion).map c).left ∧
        Surjective ((Over.post B.inclusion).map c).left ∧
        IsPullback (yoneda.map c) (yoneda.map v) f
          (yonedaToQuotientSheaf B S hS G hU) := by
  classical
  have hrange : Set.range g.left.base = (V : Set G.objects.left) := by
    rw [hg]; exact V.range_ι
  have hEH : IsEquivalenceRelation (groupoidPreRelation H.groupoid).target
      (groupoidPreRelation H.groupoid).source := by
    simp only [groupoidPreRelation_target, groupoidPreRelation_source]
    infer_instance
  have hEG : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source := by
    simp only [groupoidPreRelation_target, groupoidPreRelation_source]
    infer_instance
  have hw : (groupoidPreRelation H.groupoid).target ≫ π =
      (groupoidPreRelation H.groupoid).source ≫ π := by
    simp only [groupoidPreRelation_target, groupoidPreRelation_source]
    exact hpb.w
  have hθ : IsIso (quotientSheafToPoints (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (groupoidPreRelation H.groupoid) π hw (isSheaf_points B S hS (Over.mk q))) :=
    isIso_quotientSheafToPoints_of_isPullback B S hS H.groupoid π hflfπ hsurjπ hpb hw
  set Vo : BigFppfOver B S hS := BigFppfOver.mk B S hS hVsize (V.ι ≫ G.objects.hom) with hVodef
  set Xo : BigFppfOver B S hS := BigFppfOver.mk B S hS hAsize q with hXodef
  set v : Vo ⟶ objectsSite B S hS G hU := (Over.post B.inclusion).preimage g with hvdef
  set c : Vo ⟶ Xo :=
    (Over.post B.inclusion).preimage (eqToHom H.objects_eq.symm ≫ π) with hcdef
  have hFv : (Over.post B.inclusion).map v = g := Functor.map_preimage _ _
  have hFc : (Over.post B.inclusion).map c = eqToHom H.objects_eq.symm ≫ π :=
    Functor.map_preimage _ _
  set PVo : Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion)
      (Over.mk (V.ι ≫ G.objects.hom)) ≅ yoneda.obj Vo :=
    Space.pointsYonedaIso (Over.post B.inclusion) Vo with hPVo
  set PXo : Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk q) ≅
      yoneda.obj Xo :=
    Space.pointsYonedaIso (Over.post B.inclusion) Xo with hPXo
  set PUo : Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) G.objects ≅
      yoneda.obj (objectsSite B S hS G hU) := objectsPointsIso B S hS G hU with hPUo
  have hnatv : PVo.inv ≫ (Over.post B.inclusion).op.whiskerLeft (yoneda.map g) ≫ PUo.hom =
      yoneda.map v :=
    Space.pointsYonedaIso_inv_comp (Over.post B.inclusion)
      (X := Vo) (Y := objectsSite B S hS G hU) g
  have hnatc : PVo.inv ≫ (Over.post B.inclusion).op.whiskerLeft
      (yoneda.map (eqToHom H.objects_eq.symm ≫ π)) ≫ PXo.hom = yoneda.map c :=
    Space.pointsYonedaIso_inv_comp (Over.post B.inclusion) (X := Vo) (Y := Xo)
      (eqToHom H.objects_eq.symm ≫ π)
  set eθ : (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (groupoidPreRelation H.groupoid)).obj ≅
      Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) (Over.mk q) :=
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso (asIso
      (quotientSheafToPoints (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (groupoidPreRelation H.groupoid) π hw
        (isSheaf_points B S hS (Over.mk q)))) with heθdef
  have key : toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (groupoidPreRelation H.groupoid) ≫ eθ.hom =
      (Over.post B.inclusion).op.whiskerLeft (yoneda.map π) := by
    rw [heθdef]
    exact toQuotientSheaf_comp_quotientSheafToPoints _ _ _ _ hw _
  set ρ := restrictionQuotientMap (BigFppfOver.topology B S hS) (Over.post B.inclusion) G g H
    with hρdef
  set f : yoneda.obj Xo ⟶ (quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (groupoidPreRelation G)).obj := PXo.inv ≫ eθ.inv ≫ ρ.hom
    with hfdef
  have htoS : (BigFppfOver.toScheme B S hS).map v = V.ι := by
    have h1 : (BigFppfOver.toScheme B S hS).map v = ((Over.post B.inclusion).map v).left := rfl
    rw [h1, hFv, hg]
  refine ⟨Vo, Xo, v, c, f, hsize, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htoS]
    exact (inferInstance : AlgebraicGeometry.IsOpenImmersion V.ι)
  · rw [htoS]; exact V.range_ι
  · rw [hfdef]
    exact MorphismProperty.RespectsIso.precomp _ PXo.inv _
      (MorphismProperty.RespectsIso.precomp _ eθ.inv _ h02WU)
  · have hisoe : IsIso (Over.Hom.left (eqToHom H.objects_eq.symm)) := by
      show IsIso ((Over.forget S).map (eqToHom H.objects_eq.symm))
      infer_instance
    rw [hFc, Over.comp_left]
    exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree.{u})
      (Over.Hom.left (eqToHom H.objects_eq.symm)) π.left hflfπ
  · have hisoe : IsIso (Over.Hom.left (eqToHom H.objects_eq.symm)) := by
      show IsIso ((Over.forget S).map (eqToHom H.objects_eq.symm))
      infer_instance
    have hresp : MorphismProperty.RespectsIso (@Surjective.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [hFc, Over.comp_left]
    exact MorphismProperty.RespectsIso.precomp (@Surjective.{u})
      (Over.Hom.left (eqToHom H.objects_eq.symm)) π.left hsurjπ
  · have hs : H.hom.mapArrows ≫ (groupoidPreRelation G).source =
        (groupoidPreRelation H.groupoid).source ≫ H.hom.mapObjects := by
      simpa [groupoidPreRelation, PreRelation.source] using H.hom.map_source
    have ht : H.hom.mapArrows ≫ (groupoidPreRelation G).target =
        (groupoidPreRelation H.groupoid).target ≫ H.hom.mapObjects := by
      simpa [groupoidPreRelation, PreRelation.target] using H.hom.map_target
    have hcart : IsPullback H.hom.mapArrows (groupoidPreRelation H.groupoid).source
        (groupoidPreRelation G).source H.hom.mapObjects := by
      simp only [groupoidPreRelation_source]
      rw [H.mapArrows_eq, H.source_eq, H.mapObjects_eq]
      refine (isPullback_restrictionArrowsToArrows_of_isInvariantSet G g hinv).of_iso
        (eqToIso H.arrows_eq.symm) (Iso.refl _) (eqToIso H.objects_eq.symm) (Iso.refl _)
        ?_ ?_ ?_ ?_
      all_goals simp
    have h07S3 : IsPullback (toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation H.groupoid))
        ((Over.post B.inclusion).op.whiskerLeft (yoneda.map H.hom.mapObjects)) ρ.hom
        (toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (groupoidPreRelation G)) :=
      isPullback_toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation H.groupoid) (groupoidPreRelation G)
        H.hom.mapArrows H.hom.mapObjects hs ht hcart
        (isSheaf_points B S hS H.groupoid.objects) (isSheaf_points B S hS G.objects)
    refine h07S3.of_iso
      (Space.pointsMapIso (Over.post B.inclusion) (eqToIso H.objects_eq) ≪≫ PVo)
      (eθ ≪≫ PXo) PUo (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.trans_hom, Space.pointsMapIso_hom, eqToIso.hom]
      rw [← Category.assoc, key, ← hnatc]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, Space.whiskerLeft_yonedaMap_comp]
      simp
    · rw [H.mapObjects_eq, ← hnatv]
      simp only [Iso.trans_hom, Space.pointsMapIso_hom, eqToIso.hom, Category.assoc,
        Iso.hom_inv_id_assoc]
      rw [← Category.assoc, Space.whiskerLeft_yonedaMap_comp]
    · simp [hfdef]
    · simp only [Iso.refl_hom, Category.comp_id]
      exact ((objectsPointsIso B S hS G hU).hom_inv_id_assoc
        (toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (groupoidPreRelation G))).symm

/-- **The chart of the fppf quotient sheaf attached to an invariant affine open.** Let a
groupoid scheme over `S` have finite locally free source and target maps, let its target and
source maps form an equivalence relation, let its object scheme `U` satisfy the size bound of
the site, and let `V` be an invariant affine open of `U`.  Then there are objects `Vo` and `Xo`
of the big fppf category over `S` — the open `V` itself and the quotient of the restriction of
the groupoid to it — together with an open immersion `v : Vo ⟶ U` with image `V`, a finite
locally free morphism `c : Vo ⟶ Xo`, and a representable open immersion `f` of the presheaf
represented by `Xo` into the quotient sheaf `U/R`, such that the square formed by `v`, `c`, `f`
and the projection of `U` onto `U/R` is Cartesian, and `Xo` is no larger than `U`.

The quotient of the restriction is the affine quotient of Stacks 03BM; that it is an open
subspace of `U/R` is Stacks 02WU; and the square is Cartesian by Stacks 07S3, whose hypothesis
on source maps holds because `V` is invariant. -/
theorem exists_chart_of_isInvariantAffineOpen (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source]
    (hU : B.Contains G.objects.left) (V : G.objects.left.Opens) (hVinv : IsInvariantOpen G V)
    (hVaff : IsAffineOpen V) :
    ∃ (Vo Xo : BigFppfOver B S hS) (v : Vo ⟶ objectsSite B S hS G hU) (c : Vo ⟶ Xo)
      (f : yoneda.obj Xo ⟶ (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation G)).obj),
      ((BigFppfOver.toScheme B S hS).obj Xo).size ≤ G.objects.left.size ∧
        IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map v).base = (V : Set G.objects.left) ∧
        (openImmersionOver B S hS).presheaf f ∧
        IsFiniteLocallyFree ((Over.post B.inclusion).map c).left ∧
        Surjective ((Over.post B.inclusion).map c).left ∧
        IsPullback (yoneda.map c) (yoneda.map v) f
          (yonedaToQuotientSheaf B S hS G hU) := by
  classical
  set g : Over.mk (V.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk V.ι rfl with hgdef
  have hg : g.left = V.ι := rfl
  have hoi : AlgebraicGeometry.IsOpenImmersion g.left :=
    (inferInstance : AlgebraicGeometry.IsOpenImmersion V.ι)
  have hinv : IsInvariantSet G (Set.range g.left.base) := by
    rw [hg, V.range_ι]; exact hVinv
  obtain ⟨A, _, q, π, hsizeA, hflfπ, hsurjπ, hpb⟩ :=
    exists_affineQuotient_of_isInvariantOpen G V hVinv hVaff g hg
  exact exists_chart_aux B S hS G hU V g hg hinv (restrict G g) π
    ((Scheme.size_coe_opens_le G.objects.left V).trans_lt hU)
    ((hsizeA.trans (Scheme.size_coe_opens_le G.objects.left V)).trans_lt hU)
    (hsizeA.trans (Scheme.size_coe_opens_le G.objects.left V)) hflfπ hsurjπ hpb
    (isOpenImmersion_restrictionQuotientMap_of_isInvariantSet B S hS G g hinv)

/-- The invariant affine opens of the object scheme of a groupoid scheme, as an index type.
This is the index type of the covering of the fppf quotient sheaf by its affine charts; the
cardinality of a set of opens of a scheme is bounded by the size of that scheme, which is the
bound a size-restricted site asks of a covering family. -/
abbrev invariantAffineIndex {S : Scheme.{u}} (G : GroupoidScheme S) : Type u :=
  {W : G.objects.left.affineOpens // IsInvariantOpen G (W : G.objects.left.Opens)}

/-- **Stacks 07S6.** Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` finite
locally free, with `(t, s)` an equivalence relation, and such that every nonempty closed subset
of `U` contains a point whose `R`-equivalence class lies in an affine open.  Then there is a
scheme `M` over `S`, no larger than `U`, and a finite locally free surjection `p : U ⟶ M`,
whose kernel pair is `(t, s)` and which represents the fppf quotient sheaf `U/R`.

The invariant affine opens cover `U` (Stacks 03JE), the quotient of the restriction of the
groupoid to each of them is affine (Stacks 03BM) and is an open subspace of `U/R`
(Stacks 02WU), and those open subspaces jointly cover `U/R` because `U` covers it; glueing
them (Stacks 01JJ) gives `M`.  Finite local freeness, surjectivity and the size bound transfer
from the charts to `p` because they are local on the target, and the kernel-pair square is the
identification of `R` with the kernel pair of the projection of `U` onto `U/R`. -/
@[stacks 07S6, sga "3 V 4.1" "(iv)"]
theorem exists_schemeQuotient (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source] (hU : B.Contains G.objects.left)
    (h3 : HasAffineOrbitInEveryClosed G) :
    ∃ (M : Over S) (p : G.objects ⟶ M)
      (hp : (groupoidPreRelation G).target ≫ p = (groupoidPreRelation G).source ≫ p)
      (hM : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
        (points (Over.post B.inclusion) M)),
      M.left.size ≤ G.objects.left.size ∧ IsFiniteLocallyFree p.left ∧ Surjective p.left ∧
        IsPullback G.target G.source p p ∧
        IsIso (quotientSheafToPoints (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (groupoidPreRelation G) p hp hM) := by
  classical
  -- the index set of charts: the invariant affine opens of the object scheme
  have hIne : Nonempty (invariantAffineIndex G) :=
    ⟨⟨⟨⊥, isAffineOpen_bot G.objects.left⟩, fun r hr => absurd hr (by simp)⟩⟩
  have hIle : Cardinal.mk (invariantAffineIndex G) ≤ G.objects.left.size :=
    (Cardinal.mk_subtype_le _).trans (Scheme.mk_affineOpens_le_size G.objects.left)
  have hIlt : Cardinal.mk (invariantAffineIndex G) < B.cutoff := hIle.trans_lt hU
  obtain ⟨V0, hV0aff, hV0inv, -, hV0top⟩ := exists_invariantAffineOpen_iSup_eq_top G h3
  have hVVtop : ⨆ i : invariantAffineIndex G, (i : G.objects.left.Opens) = ⊤ := by
    rw [eq_top_iff, ← hV0top]
    refine iSup_le fun x => ?_
    exact le_iSup (fun i : invariantAffineIndex G => (i : G.objects.left.Opens))
      ⟨⟨V0 x, hV0aff x⟩, hV0inv x⟩
  -- the charts
  choose Vo Xo v c f hsz hoi hrng hpo hflf hsrj hsq using
    fun i : invariantAffineIndex G =>
      exists_chart_of_isInvariantAffineOpen B S hS G hU (i : G.objects.left.Opens) i.2 i.1.2
  -- the charts cover the object scheme
  have hcovU : ∀ x : (BigFppfOver.toScheme B S hS).obj (objectsSite B S hS G hU),
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i)).base := by
    intro x
    have hx : x ∈ (⨆ i : invariantAffineIndex G, (i : G.objects.left.Opens)) := by
      rw [hVVtop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨i, by rw [hrng i]; exact hi⟩
  have hsieve : Sieve.ofArrows Vo v ∈ BigFppfOver.topology B S hS (objectsSite B S hS G hU) :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS v hoi hcovU
  -- joint local surjectivity of the chart maps
  have hu : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Limits.Sigma.desc fun i => yoneda.map (v i)) :=
    isLocallySurjective_coprodYonedaDesc (BigFppfOver.topology B S hS) Vo
      (objectsSite B S hS G hU) v hsieve
  have hqU : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (yonedaToQuotientSheaf B S hS G hU) := by
    have h1 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (objectsPointsIso B S hS G hU).inv := inferInstance
    have h2 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (groupoidPreRelation G)) :=
      toQuotientSheaf_isLocallySurjective _ _ _
    exact Presheaf.isLocallySurjective_comp _ _ _
  have hsurjf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Limits.Sigma.desc f) :=
    Presheaf.isLocallySurjective_sigmaDesc_of_fac (BigFppfOver.topology B S hS) f
      (fun i => yoneda.map (v i)) (fun i => yoneda.map (c i))
      (yonedaToQuotientSheaf B S hS G hU) hu hqU fun i => (hsq i).w
  -- glue
  obtain ⟨Y, e, gg, hfg, hggoi, hggcov⟩ :=
    exists_representing_cover_of_openCharts_of_size_le
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (groupoidPreRelation G)).property hpo hsurjf hIlt hU hsz
  set MO : invariantAffineIndex G → ((BigFppfOver.toScheme B S hS).obj Y).Opens :=
    fun i => Scheme.Hom.opensRange ((BigFppfOver.toScheme B S hS).map (gg i)) with hMOdef
  -- the arrow scheme is contained in the site
  have hfin : _root_.AlgebraicGeometry.IsFinite G.source.left :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation G.source.left).mp
      inferInstance).1
  have hRsize : B.Contains G.arrows.left :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact G.source.left).trans_lt hU
  set Ro : BigFppfOver B S hS := BigFppfOver.mk B S hS hRsize G.arrows.hom with hRodef
  set tO : Ro ⟶ objectsSite B S hS G hU := (Over.post B.inclusion).preimage G.target with htO
  set sO : Ro ⟶ objectsSite B S hS G hU := (Over.post B.inclusion).preimage G.source with hsO
  have hFt : (Over.post B.inclusion).map tO = G.target := Functor.map_preimage _ _
  have hFs : (Over.post B.inclusion).map sO = G.source := Functor.map_preimage _ _
  set PRo : Stacks.Groupoids.points (Over.post (X := B.obj hS) B.inclusion) G.arrows ≅
      yoneda.obj Ro := Space.pointsYonedaIso (Over.post B.inclusion) Ro with hPRo
  -- the projection onto the glued scheme
  set pO : objectsSite B S hS G hU ⟶ Y :=
    (yoneda (C := BigFppfOver B S hS)).preimage
      (yonedaToQuotientSheaf B S hS G hU ≫ e.hom) with hpOdef
  have hyp : yoneda.map pO = yonedaToQuotientSheaf B S hS G hU ≫ e.hom :=
    Functor.map_preimage _ _
  -- naturality of the comparison isomorphisms
  have hnatt : PRo.inv ≫ (Over.post B.inclusion).op.whiskerLeft (yoneda.map G.target) ≫
      (objectsPointsIso B S hS G hU).hom = yoneda.map tO :=
    Space.pointsYonedaIso_inv_comp (Over.post B.inclusion) (X := Ro)
      (Y := objectsSite B S hS G hU) G.target
  have hnats : PRo.inv ≫ (Over.post B.inclusion).op.whiskerLeft (yoneda.map G.source) ≫
      (objectsPointsIso B S hS G hU).hom = yoneda.map sO :=
    Space.pointsYonedaIso_inv_comp (Over.post B.inclusion) (X := Ro)
      (Y := objectsSite B S hS G hU) G.source
  -- the arrow scheme is the kernel pair of the projection
  have hEG : IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source := by
    simp only [groupoidPreRelation_target, groupoidPreRelation_source]
    infer_instance
  have hK : IsPullback
      (Stacks.Groupoids.targetMap (Over.post B.inclusion) (groupoidPreRelation G))
      (Stacks.Groupoids.sourceMap (Over.post B.inclusion) (groupoidPreRelation G))
      (toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (groupoidPreRelation G))
      (toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (groupoidPreRelation G)) :=
    isPullback_toQuotientSheaf_self (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (groupoidPreRelation G) (isSheaf_points B S hS G.arrows) (isSheaf_points B S hS G.objects)
  have hpbYon : IsPullback (yoneda.map tO) (yoneda.map sO) (yoneda.map pO) (yoneda.map pO) := by
    refine hK.of_iso PRo (objectsPointsIso B S hS G hU) (objectsPointsIso B S hS G hU) e
      ?_ ?_ ?_ ?_
    · rw [← hnatt]
      simp only [Stacks.Groupoids.targetMap, groupoidPreRelation_target,
        Iso.hom_inv_id_assoc]
    · rw [← hnats]
      simp only [Stacks.Groupoids.sourceMap, groupoidPreRelation_source,
        Iso.hom_inv_id_assoc]
    · rw [hyp]
      simp only [yonedaToQuotientSheaf, Category.assoc, Iso.hom_inv_id_assoc]
    · rw [hyp]
      simp only [yonedaToQuotientSheaf, Category.assoc, Iso.hom_inv_id_assoc]
  have hpbSite : IsPullback tO sO pO pO := IsPullback.of_map_of_faithful yoneda hpbYon
  have hpresv : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have hFtL : (BigFppfOver.toScheme B S hS).map tO = G.target.left :=
    congrArg Over.Hom.left hFt
  have hFsL : (BigFppfOver.toScheme B S hS).map sO = G.source.left :=
    congrArg Over.Hom.left hFs
  have hpbSch : IsPullback G.target.left G.source.left
      ((Over.post B.inclusion).map pO).left ((Over.post B.inclusion).map pO).left := by
    refine (hpbSite.map (BigFppfOver.toScheme B S hS)).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (hFtL.trans (Category.id_comp _).symm)
    · exact (Category.comp_id _).trans (hFsL.trans (Category.id_comp _).symm)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hpbOver : IsPullback G.target G.source ((Over.post B.inclusion).map pO)
      ((Over.post B.inclusion).map pO) := IsPullback.of_map_of_faithful (Over.forget S) hpbSch
  have hp : (groupoidPreRelation G).target ≫ (Over.post B.inclusion).map pO =
      (groupoidPreRelation G).source ≫ (Over.post B.inclusion).map pO := by
    simp only [groupoidPreRelation_target, groupoidPreRelation_source]
    exact hpbOver.w
  -- the chart squares in the site, and in schemes
  have hsqSite : ∀ i, IsPullback (c i) (v i) (gg i) pO := by
    intro i
    refine IsPullback.of_map_of_faithful yoneda ?_
    refine (hsq i).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
    · simp
    · simp
    · simpa using hfg i
    · simpa using hyp.symm
  have hsqSch : ∀ i, IsPullback ((BigFppfOver.toScheme B S hS).map (c i))
      ((BigFppfOver.toScheme B S hS).map (v i)) ((BigFppfOver.toScheme B S hS).map (gg i))
      ((Over.post B.inclusion).map pO).left :=
    fun i => (hsqSite i).map (BigFppfOver.toScheme B S hS)
  have hMcov : ⨆ i, MO i = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hggcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hflfp : IsFiniteLocallyFree ((Over.post B.inclusion).map pO).left := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top MO hMcov fun i => ?_
    have hoii : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (gg i)) :=
      hggoi i
    refine (MorphismProperty.arrow_mk_iso_iff (@IsFiniteLocallyFree.{u})
      (@morphismRestrictOpensRange _ _ _ ((Over.post B.inclusion).map pO).left
        ((BigFppfOver.toScheme B S hS).map (gg i)) hoii)).mpr ?_
    have h1 : IsFiniteLocallyFree ((hsqSch i).flip.isoPullback.inv ≫
        (BigFppfOver.toScheme B S hS).map (c i)) :=
      (MorphismProperty.cancel_left_of_respectsIso (@IsFiniteLocallyFree.{u}) _ _).mpr (hflf i)
    exact (hsqSch i).flip.isoPullback_inv_snd ▸ h1
  have hsurjp : Surjective ((Over.post B.inclusion).map pO).left := by
    have hresp : MorphismProperty.RespectsIso (@Surjective.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine IsZariskiLocalAtTarget.of_iSup_eq_top MO hMcov fun i => ?_
    have hoii : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (gg i)) :=
      hggoi i
    refine (MorphismProperty.arrow_mk_iso_iff (@Surjective.{u})
      (@morphismRestrictOpensRange _ _ _ ((Over.post B.inclusion).map pO).left
        ((BigFppfOver.toScheme B S hS).map (gg i)) hoii)).mpr ?_
    have h1 : Surjective ((hsqSch i).flip.isoPullback.inv ≫
        (BigFppfOver.toScheme B S hS).map (c i)) :=
      (MorphismProperty.cancel_left_of_respectsIso (@Surjective.{u}) _ _).mpr (hsrj i)
    exact (hsqSch i).flip.isoPullback_inv_snd ▸ h1
  refine ⟨(Over.post B.inclusion).obj Y, (Over.post B.inclusion).map pO, hp,
    isSheaf_points B S hS ((Over.post B.inclusion).obj Y), ?_, hflfp, hsurjp, hpbOver,
    isIso_quotientSheafToPoints_of_isPullback B S hS G ((Over.post B.inclusion).map pO)
      hflfp hsurjp hpbOver hp⟩
  have hoiGG : ∀ i, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (gg i)) := hggoi
  refine (Scheme.size_le_of_iSup_eq_top
    MO hMcov).trans (max_le hIle (ciSup_le' fun i => ?_))
  have hoii : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (gg i)) :=
    hoiGG i
  refine le_trans (le_of_eq ?_) (hsz i)
  exact (Scheme.size_congr
    (Scheme.Hom.isoOpensRange ((BigFppfOver.toScheme B S hS).map (gg i)))).symm

/-- **Stacks 07S6 for an equivalence relation.** Let `t, s : R ⟶ U` be finite locally free
morphisms of schemes over `S` forming an equivalence relation, let `U` satisfy the size bound
of the site, and assume every finite set of points of `U` lies in an affine open.  Then there
is a scheme `M` over `S`, no larger than `U`, and a finite locally free surjection `π : U ⟶ M`
whose kernel pair is `(t, s)`.

This is `AlgebraicGeometry.GroupoidScheme.exists_schemeQuotient` read for an equivalence
relation rather than for a groupoid scheme, the groupoid structure being the canonical
extension of Stacks 0233.  The hypothesis on finite sets of points is stronger than condition
(3) of Stacks 07S6 and implies it: the orbit of a point is the image of a fibre of `s`, which
is finite because `s` is, so every point has affine orbit. -/
theorem exists_schemeQuotient_of_isFiniteLocallyFree_relation (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {R U : Over S} (t s : R ⟶ U)
    (hflft : IsFiniteLocallyFree t.left) (hflfs : IsFiniteLocallyFree s.left)
    (hrel : IsEquivalenceRelation t s) (hUc : B.Contains U.left)
    (haff : ∀ E : Set U.left, E.Finite → ∃ O : U.left.Opens, IsAffineOpen O ∧ E ⊆ O) :
    ∃ (M : Over S) (π : U ⟶ M), M.left.size ≤ U.left.size ∧
      IsFiniteLocallyFree π.left ∧ Surjective π.left ∧ IsPullback t s π π := by
  classical
  have _ := hflft
  have _ := hflfs
  have _ := hrel
  set j : PreRelation R U := prod.lift t s with hj
  have hjt : j.target = t := by simp [hj, PreRelation.target]
  have hjs : j.source = s := by simp [hj, PreRelation.source]
  have _ : IsEquivalenceRelation j.target j.source := by rw [hjt, hjs]; infer_instance
  obtain ⟨G, hGext, -⟩ := existsUnique_groupoidScheme_of_isEquivalenceRelation j
  obtain ⟨ho, ha, hsrc, htgt⟩ := hGext
  have hoL : G.objects.left = U.left := congrArg Over.left ho
  have haL : G.arrows.left = R.left := congrArg Over.left ha
  have hsrcG : G.source = eqToHom ha ≫ s ≫ eqToHom ho.symm := by
    rw [← hjs, ← hsrc]; simp
  have htgtG : G.target = eqToHom ha ≫ t ≫ eqToHom ho.symm := by
    rw [← hjt, ← htgt]; simp
  have hsrcL : G.source.left = eqToHom haL ≫ s.left ≫ eqToHom hoL.symm := by
    rw [hsrcG]; simp [Over.eqToHom_left]
  have htgtL : G.target.left = eqToHom haL ≫ t.left ≫ eqToHom hoL.symm := by
    rw [htgtG]; simp [Over.eqToHom_left]
  have _ : IsFiniteLocallyFree G.source.left := by
    rw [hsrcL]
    exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree.{u}) _ _
      (MorphismProperty.RespectsIso.postcomp (@IsFiniteLocallyFree.{u}) _ _ hflfs)
  have _ : IsFiniteLocallyFree G.target.left := by
    rw [htgtL]
    exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree.{u}) _ _
      (MorphismProperty.RespectsIso.postcomp (@IsFiniteLocallyFree.{u}) _ _ hflft)
  have _ : IsEquivalenceRelation G.target G.source := by
    rw [hsrcG, htgtG]
    exact Space.isEquivalenceRelation_eqToHom_conj ha ho.symm t s
  have hUc' : B.Contains G.objects.left := by rw [hoL]; exact hUc
  -- condition (3) follows from finiteness of the orbits
  have hfinsrc : _root_.AlgebraicGeometry.IsFinite G.source.left :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation G.source.left).mp
      inferInstance).1
  have haff' : ∀ E : Set G.objects.left, E.Finite →
      ∃ O : G.objects.left.Opens, IsAffineOpen O ∧ E ⊆ O := by
    rw [hoL]; exact haff
  have h3 : HasAffineOrbitInEveryClosed G := by
    refine hasAffineOrbitInEveryClosed_of_forall fun x => ?_
    have hfib : (G.source.left.base ⁻¹' {x}).Finite :=
      G.source.left.finite_preimage_singleton x
    obtain ⟨O, hOaff, hOsub⟩ :=
      haff' (G.target.left.base '' (G.source.left.base ⁻¹' {x})) (hfib.image _)
    exact ⟨O, hOaff, fun r hr => hOsub ⟨r, hr, rfl⟩⟩
  obtain ⟨M, p, hp, hM, hsize, hflfp, hsurjp, hpb, -⟩ :=
    exists_schemeQuotient B S hS G hUc' h3
  refine ⟨M, eqToHom ho.symm ≫ p, ?_, ?_, ?_, ?_⟩
  · rw [← hoL]; exact hsize
  · rw [Over.comp_left, Over.eqToHom_left]
    exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree.{u}) _ _ hflfp
  · have hresp : MorphismProperty.RespectsIso (@Surjective.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [Over.comp_left, Over.eqToHom_left]
    exact MorphismProperty.RespectsIso.precomp (@Surjective.{u}) _ _ hsurjp
  · refine hpb.of_iso (eqToIso ha) (eqToIso ho) (eqToIso ho) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [htgtG]; simp
    · rw [hsrcG]; simp
    · simp
    · simp

end AlgebraicGeometry.GroupoidScheme

end
