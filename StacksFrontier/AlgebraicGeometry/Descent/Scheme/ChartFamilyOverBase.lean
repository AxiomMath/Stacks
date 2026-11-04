module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvariantOpenFromBase
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.RelativeOverBase

/-!
# Glueing the charts of a descent datum along an open cover of the base

Let `f : X ⟶ S` be a morphism of schemes, let `(V, φ)` be a descent datum relative to `X/S`
and let `S = ⋃ Sᵢ` be an open cover. The preimage `Vᵢ ⊆ V` of `Sᵢ` is an invariant open, so the
restricted datum `(Vᵢ, φ|)` makes sense; suppose each is descended by a scheme `Uᵢ ⟶ Sᵢ` and
that the `Uᵢ` are glued over `S` by transition isomorphisms satisfying the cocycle condition.
Then the glued scheme `U ⟶ S` descends `(V, φ)`, so the datum is effective.

No hypothesis on `f` is needed: the transition isomorphisms are part of the data, which is what
distinguishes this from `AlgebraicGeometry.DescentDatum.ChartFamily`, where they are produced
from the rigidity of a surjective flat quasi-compact morphism.

## Main definitions

* `AlgebraicGeometry.DescentDatum.baseOpens` and
  `AlgebraicGeometry.DescentDatum.restrictBaseOpens`: the part of `V` lying over an open of the
  base, and the restriction of the datum to it.
* `AlgebraicGeometry.DescentDatum.BaseChartFamily`: a relative glueing datum over an open cover
  of `S` whose pieces descend the restrictions of the datum.
* `AlgebraicGeometry.Scheme.RelativeGlueData.toGlueDataOverBase`: a relative glueing datum,
  read as a glueing datum over the base.
* `AlgebraicGeometry.DescentDatum.BaseChartFamily.toGluedChartFamily`: the family, presented as
  an `AlgebraicGeometry.DescentDatum.GluedChartFamily`.

## Main results

* `AlgebraicGeometry.DescentDatum.BaseChartFamily.isOpenCover`: the parts of `V` lying over the
  members of the cover of the base cover `V`.
* `AlgebraicGeometry.DescentDatum.isEffective_of_baseChartFamily`: **a descent datum with a
  family of charts over an open cover of the base is effective.**

## Implementation notes

The glueing datum is an `AlgebraicGeometry.Scheme.RelativeGlueData`, in which the overlaps are
the preimages of the members of the cover of the base rather than free parameters.

The members of the cover of `V` and the local projections are repackaged as
`AlgebraicGeometry.DescentDatum.BaseChartFamily.opens` and
`AlgebraicGeometry.DescentDatum.BaseChartFamily.chartProj` before anything is proved about
them. The restriction of a datum to an invariant open is semireducible, so a goal mentioning
the scheme of a restriction is type-correct only after unfolding it; naming the open and the
projection keeps the rewrites in such goals from having to abstract over that unfolding.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- A relative gluing datum, read as a gluing datum over the base: the overlaps are the
preimages of the members of the cover of the base. -/
@[implicit_reducible]
def Scheme.RelativeGlueData.toGlueDataOverBase {S : Scheme.{u}}
    (G : Scheme.RelativeGlueData S) : Scheme.GlueDataOverBase S where
  J := G.J
  obj := G.obj
  proj := G.proj
  overlap := G.overlap
  overlap_self := G.overlap_self
  t := G.t
  t_over := G.t_over
  t_self := G.t_self
  t' := G.t'
  t'_fac := G.t'_fac
  cocycle := G.cocycle

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S}

attribute [local implicit_reducible] restrictOpen

/-- The part of the scheme of a descent datum lying over an open of the base. -/
abbrev baseOpens (D : DescentDatum f) (T : S.Opens) : D.over.left.Opens :=
  (D.over.hom ≫ f) ⁻¹ᵁ T

/-- The restriction of a descent datum to the part of its scheme lying over an open of the
base, which is an invariant open. -/
abbrev restrictBaseOpens (D : DescentDatum f) (T : S.Opens) : DescentDatum f :=
  D.restrictOpen (D.baseOpens T) (D.isTransitionInvariant_preimage_base T)

/-- **A family of charts for a descent datum over an open cover of the base.** A relative
glueing datum over `S` together with, for each member `Sᵢ` of its cover, a projection of the
part of `V` lying over `Sᵢ` onto the `i`-th piece which exhibits that part as the fibre product
of the piece with `X` over `S`, equalises the two legs of the gluing isomorphism, and agrees
with the other projections inside the glued scheme. -/
structure BaseChartFamily (D : DescentDatum f) where
  /-- The glueing datum over the base: an open cover of `S`, a scheme over each member, and
  transition isomorphisms satisfying the cocycle condition. -/
  glue : Scheme.RelativeGlueData S
  /-- The projection of the part of `V` lying over the `i`-th member of the cover onto the
  `i`-th piece. -/
  proj : ∀ i, (D.baseOpens (glue.base i)).toScheme ⟶ glue.obj i
  /-- The `i`-th projection exhibits the part of `V` lying over the `i`-th member of the cover
  as the fibre product of the `i`-th piece with `X` over `S`. -/
  isPullback : ∀ i, IsPullback ((D.baseOpens (glue.base i)).ι ≫ D.over.hom) (proj i) f
    (glue.proj i)
  /-- The `i`-th projection equalises the gluing isomorphism of the restricted datum followed
  by the projection of `X ×_S Vᵢ` to `Vᵢ` and the projection of `Vᵢ ×_S X` to `Vᵢ`. -/
  proj_invariant : ∀ i, (D.restrictBaseOpens (glue.base i)).transitionPullbackIso.hom ≫
      pullback.snd f ((D.restrictBaseOpens (glue.base i)).over.hom ≫ f) ≫ proj i =
    pullback.fst ((D.restrictBaseOpens (glue.base i)).over.hom ≫ f) f ≫ proj i
  /-- The projections agree on the intersection of two members of the cover of `V` after
  passing to the glued scheme. -/
  proj_comp_ι : ∀ i j, D.over.left.homOfLE
        (inf_le_left : D.baseOpens (glue.base i) ⊓ D.baseOpens (glue.base j) ≤
          D.baseOpens (glue.base i)) ≫ proj i ≫ glue.ι i =
      D.over.left.homOfLE
        (inf_le_right : D.baseOpens (glue.base i) ⊓ D.baseOpens (glue.base j) ≤
          D.baseOpens (glue.base j)) ≫ proj j ≫ glue.ι j

namespace BaseChartFamily

variable {D : DescentDatum f} (C : D.BaseChartFamily)

/-- The part of `V` lying over the `i`-th member of the cover of the base. -/
def opens (i : C.glue.J) : D.over.left.Opens := D.baseOpens (C.glue.base i)

/-- The `i`-th member of the family is the preimage of the `i`-th member of the cover of the
base. -/
lemma opens_eq (i : C.glue.J) : C.opens i = (D.over.hom ≫ f) ⁻¹ᵁ C.glue.base i := rfl

/-- Each member of the family is an invariant open, being the preimage of an open of the
base. -/
lemma invariant (i : C.glue.J) : D.IsTransitionInvariant (C.opens i) :=
  D.isTransitionInvariant_preimage_base (C.glue.base i)

/-- The projection of the `i`-th member of the family onto the `i`-th piece. -/
def chartProj (i : C.glue.J) : (C.opens i).toScheme ⟶ C.glue.obj i := C.proj i

/-- The `i`-th projection exhibits the `i`-th member of the family as the fibre product of the
`i`-th piece with `X` over `S`. -/
lemma isPullback_chartProj (i : C.glue.J) :
    IsPullback ((C.opens i).ι ≫ D.over.hom) (C.chartProj i) f (C.glue.proj i) :=
  C.isPullback i

/-- The `i`-th projection equalises the two legs of the gluing isomorphism of the restriction
of the datum to the `i`-th member of the family. -/
lemma chartProj_invariant (i : C.glue.J) :
    (D.restrictOpen (C.opens i) (C.invariant i)).transitionPullbackIso.hom ≫
        pullback.snd f ((D.restrictOpen (C.opens i) (C.invariant i)).over.hom ≫ f) ≫
          C.chartProj i =
      pullback.fst ((D.restrictOpen (C.opens i) (C.invariant i)).over.hom ≫ f) f ≫
        C.chartProj i :=
  C.proj_invariant i

/-- The projections agree on the intersection of two members of the family after passing to the
glued scheme. -/
lemma homOfLE_comp_chartProj_comp_ι (i j : C.glue.J) :
    D.over.left.homOfLE (inf_le_left : C.opens i ⊓ C.opens j ≤ C.opens i) ≫
        C.chartProj i ≫ C.glue.ι i =
      D.over.left.homOfLE (inf_le_right : C.opens i ⊓ C.opens j ≤ C.opens j) ≫
        C.chartProj j ≫ C.glue.ι j :=
  C.proj_comp_ι i j

/-- The members of the family cover `V`. -/
lemma isOpenCover : TopologicalSpace.IsOpenCover C.opens :=
  TopologicalSpace.IsOpenCover.mk (D.iSup_preimage_base C.glue.base C.glue.iSup_base)

end BaseChartFamily

/-- **A family of charts over an open cover of the base is a family of charts glued over the
base.** The glueing datum over the base is the relative glueing datum read as one, the members
of the cover of `V` are the parts lying over the members of the cover of the base, and the
projections are the given ones. -/
def BaseChartFamily.toGluedChartFamily {D : DescentDatum f} (C : D.BaseChartFamily) :
    D.GluedChartFamily where
  glue := C.glue.toGlueDataOverBase
  opens := C.opens
  isOpenCover := C.isOpenCover
  invariant := C.invariant
  proj := C.chartProj
  isPullback := C.isPullback_chartProj
  proj_invariant := C.chartProj_invariant
  proj_comp_ι := C.homOfLE_comp_chartProj_comp_ι
  proj_preimage_overlap i j := by
    change C.chartProj i ⁻¹ᵁ (C.glue.proj i ⁻¹ᵁ C.glue.base j) = _
    rw [← Scheme.Hom.comp_preimage, ← (C.isPullback_chartProj i).w, Category.assoc,
      Scheme.Hom.comp_preimage]
    rfl

/-- **A descent datum with a family of charts over an open cover of the base is effective.**
Let `f : X ⟶ S` be a morphism of schemes and `(V, φ)` a descent datum relative to `X/S`. If
there is an open cover `S = ⋃ Sᵢ` and schemes `Uᵢ ⟶ Sᵢ` descending the restrictions of `(V, φ)`
to the preimages of the `Sᵢ`, glued over `S` compatibly with those descriptions, then `(V, φ)`
is effective. -/
theorem isEffective_of_baseChartFamily {D : DescentDatum f} (C : D.BaseChartFamily) :
    DescentData.IsEffective D :=
  C.toGluedChartFamily.descended.isEffective

end DescentDatum

end AlgebraicGeometry

end

end
