module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedAtChart
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingLiftedFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack

/-!
# The fibre over a field-valued point is unramified at a point of an étale chart

The chart construction of **Stacks 06N3** ends by feeding **Stacks 06N2** the hypothesis that the
fibre `F = U ×_𝒳 Spec k` is unramified over `Spec k` near the sliced point. What the construction
produces is a statement about a morphism of **schemes**: an affine étale chart `V` of `F` and a
point `v` of `V` at which the morphism of schemes `V ⟶ Spec k` is unramified in the sense of
**Stacks 02G4** — this is
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSliceSeparablePoint`, read
at the slice.

This file lifts that statement one level, to the morphism of **algebraic spaces**
`Fsp ⟶ Spec k` — the structure 1-morphism of the fibre read through an algebraic space `Fsp`
representing it, `AlgebraicGeometry.Stack.fibreSpaceStructureMorphism`. The conclusion is
`AlgebraicGeometry.Space.IsUnramifiedAt` (**Stacks 03ZH**, part (2)) at the point of `|Fsp|`
below `v`, which by definition hands back an **open subspace of `Fsp`** containing that point on
which `Fsp ⟶ Spec k` is unramified.

## Main results

* `AlgebraicGeometry.Stack.isUnramifiedAt_fibreSpaceStructureMorphism_of_unramifiedAt`: the lift
  itself.
* `AlgebraicGeometry.Stack.exists_isOpenSubspace_isUnramified_fibreSpace_of_unramifiedAt`: the
  open subspace of `Fsp` it produces, stated outright.
* `AlgebraicGeometry.Stack.exists_openSubstack_mem_pointSet_of_isOpenSubspace`: that open
  subspace of `Fsp` read as an **open substack of the 2-fibre product**, across the equivalence
  `eF`, with the point it contains carried along.

## How it is proved

The target of the structure morphism is the presheaf represented by the site object on `Spec k`,
so the square of étale charts the criterion needs has the **identity** for its target chart, and
the given étale chart of `Fsp` for its source chart; the morphism of charts is then the
structure morphism of the chart over `Spec k` itself. The criterion is
`AlgebraicGeometry.Space.isUnramifiedAt_chartPoint_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedAtChart`: unramifiedness at a point of an
algebraic space is tested on any one commuting square of étale charts over it, because
unramifiedness of morphisms of schemes is étale local on the source and target (**Stacks 04R3**).

Nothing about the 2-fibre product is used: the statement is about an arbitrary étale chart of
`Fsp` whose structure morphism over `Spec k` factors the structure morphism of the fibre, which
is what an étale chart of the fibre is.

## The open substack, and where the unramifiedness clause is proved

**Stacks 06N2** consumes `AlgebraicGeometry.Stack.FibreIsUnramifiedNear`, which asks for an
`AlgebraicGeometry.Stack.OpenSubstack` of the 2-fibre product
`AlgebraicGeometry.Stack.fibreOverFieldPoint` containing the point, on which the *stack-level*
unramifiedness of **Stacks 0CIT** holds. Of the two things that asks for, the **open substack**
is produced here: the point set of the open subspace of `Fsp` is open in `|Fsp|` by part (1) of
**Stacks 03BZ**, its image in `|F|` is open because the comparison of point spaces attached to a
representing algebraic space is a homeomorphism
(`AlgebraicGeometry.Stack.isOpenMap_spacePointMap_representing`), and an open set of points is
the point set of an open substack by the surjectivity half of **Stacks 06FJ**
(`AlgebraicGeometry.Stack.pointsWithinOpenSubstack`). That is
`AlgebraicGeometry.Stack.exists_openSubstack_mem_pointSet_of_isOpenSubspace` below, and the
membership clause of `FibreIsUnramifiedNear` comes with it.

The unramifiedness clause — that `AlgebraicGeometry.Stack.IsUnramified` holds of
`V.inclusion ≫ fibreStructureMorphism` for an open substack `V` containing the point — is proved
in `StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedNearSubstack`, as
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt`, which produces the whole of
`AlgebraicGeometry.Stack.FibreIsUnramifiedNear` at the hypotheses of
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isUnramified_fibreSpace_of_unramifiedAt` above. Its
open substack is **not** the one produced here: the only route the library offers to the
stack-level unramifiedness is
`AlgebraicGeometry.Stack.isUnramified_of_hasRelativeProperty_unramified` followed by
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, which needs the
representing datum of the open substack itself, and the open substack obtained here from the
surjectivity half of Stacks 06FJ carries none. There the open substack is cut out by the
*essential image* of `S_W ⟶ S_{Fsp} ⟶ F`, so that **Stacks 0506** supplies the comparison with
`S_W` that the representing datum, the identification of the structure 1-morphisms and the
point-set membership are all read through.

Invariance of `AlgebraicGeometry.Stack.IsUnramified` under an equivalence of the source with no
representability hypothesis is not needed for that, and is still open, where
`AlgebraicGeometry.Stack.IsDM` (`...isDM_of_equivalence`), `AlgebraicStacks.IsFlat`,
`AlgebraicStacks.IsSmooth` and `AlgebraicGeometry.Stack.HasRelativeProperty`
(`...hasRelativeProperty_of_equivalences`) have it outright: the étale-smooth diagram test
quantifies over the 2-fibre products of the cospan `(b, f)`, and an equivalence of the source
changes the *source* of the second leg of that cospan, which
`CategoryTheory.Bicategory.TwoCommSq.reindexSnd` — the reindexing that carries the
2-isomorphism case — does not do; the comparison `𝒰' ×_𝒴 V ≃ 𝒰 ×_𝒴 V` would have to be built.
See the module documentation of
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem`.

No `@[stacks]` attribute is claimed: this is a step of the chart construction of **Stacks 06N3**,
whose registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

variable (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

include hFsp in
/-- **The fibre is unramified over `Spec k` at a point of an étale chart at which the chart is.**
Let `Fsp` represent the fibre `F = U ×_𝒳 Spec k` of a 1-morphism `f : U ⟶ 𝒳` over a field-valued
point `g : Spec k ⟶ 𝒳`, let `N` be an étale chart of `Fsp` whose structure morphism `q` over
`Spec k` factors the structure morphism of `F`, and let `v` be a point of the scheme underlying
`N` at which the morphism of schemes `q` is unramified. Then the morphism of algebraic spaces
`Fsp ⟶ Spec k` is unramified, in the sense of **Stacks 03ZH**, part (2), at the point of `|Fsp|`
below `v`.

This is the passage from the scheme-level unramifiedness the chart construction of
**Stacks 06N3** produces — the slice over `Spec k` at the sliced point, which is
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field` — to a
statement about the fibre as an algebraic space. The target of the structure morphism is a
represented presheaf, so the square of étale charts that
`AlgebraicGeometry.Space.isUnramifiedAt_chartPoint_iff` tests the condition on has the identity
for its target chart and `N` for its source chart, and the morphism of charts in it is `q`. -/
theorem isUnramifiedAt_fibreSpaceStructureMorphism_of_unramifiedAt
    (N : Space.SmallEtale B S hS Fsp)
    (q : (Space.SmallEtale.toOver B S hS Fsp).obj N ⟶ fieldPointObject B S hS k hk toBase)
    (hsq : N.obj.hom ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF =
      yoneda.map q)
    (v : Space.chartScheme N)
    (hv : UnramifiedAt ((BigFppfOver.toScheme B S hS).map q) v) :
    Space.IsUnramifiedAt B S hS
      (fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF)
      (Space.chartPointsMap N v) :=
  (Space.isUnramifiedAt_chartPoint_iff B S hS hFsp
    (isAlgebraicSpace_yoneda B S hS (fieldPointObject B S hS k hk toBase))
    (fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF)
    _ _ N.obj.hom (𝟙 _) q N.property
    (Space.presheaf_etale_of_iso B S hS (Iso.refl _))
    (by rw [hsq, Category.comp_id]) v).2 hv

include hFsp in
/-- **The open subspace of the fibre on which it is unramified over `Spec k`.** The same
hypotheses as
`AlgebraicGeometry.Stack.isUnramifiedAt_fibreSpaceStructureMorphism_of_unramifiedAt`, with the
conclusion spelled out: an open subspace of `Fsp` containing the point below `v` whose structure
morphism to `Spec k` is unramified in the sense of **Stacks 03ZH**, part (1).

Unramifiedness at a point *is* the existence of such an open subspace, so this is the previous
lemma followed by `AlgebraicGeometry.Space.IsUnramifiedAt.exists_mem_range_pointsMap`. It is the
form that the open substack of `AlgebraicGeometry.Stack.FibreIsUnramifiedNear` has to be built
out of. -/
theorem exists_isOpenSubspace_isUnramified_fibreSpace_of_unramifiedAt
    (N : Space.SmallEtale B S hS Fsp)
    (q : (Space.SmallEtale.toOver B S hS Fsp).obj N ⟶ fieldPointObject B S hS k hk toBase)
    (hsq : N.obj.hom ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF =
      yoneda.map q)
    (v : Space.chartScheme N)
    (hv : UnramifiedAt ((BigFppfOver.toScheme B S hS).map q) v) :
    ∃ W : Subfunctor Fsp, Space.IsOpenSubspace B S hS W ∧
      Space.IsUnramified B S hS
          (W.ι ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF) ∧
        Space.chartPointsMap N v ∈
          Set.range (Space.pointsMap B S hS W.toFunctor W.ι) :=
  (isUnramifiedAt_fibreSpaceStructureMorphism_of_unramifiedAt B S hS 𝒳 U hU k hk toBase f g
    Fsp hFsp eF N q hsq v hv).exists_mem_range_pointsMap

section OpenSubstack

attribute [local instance] AlgebraicGeometry.Stack.pointTopology
attribute [local instance] AlgebraicGeometry.Space.pointTopology

/-- **An open subspace of a representing algebraic space of the fibre is an open substack of the
fibre.** The 2-fibre product `F = U ×_𝒳 Spec k` is represented by the algebraic space `Fsp`
through `eF`; an open subspace `W` of `Fsp` then cuts out an open substack of `F` whose point set
is the image of the point set of `W`, and a point of `|Fsp|` lying in `W` has its image in that
open substack.

This is the open substack that `AlgebraicGeometry.Stack.FibreIsUnramifiedNear` asks for, together
with its membership clause; only the unramifiedness clause is still owed, for which see the
module documentation.

The point set of `W` is open in `|Fsp|` by part (1) of **Stacks 03BZ**
(`AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion`), its image is open because
the comparison of point spaces attached to a representing algebraic space is an open map
(`AlgebraicGeometry.Stack.isOpenMap_spacePointMap_representing`, the open half of
`...isHomeomorph_spacePointMap_representing`), and an open set of points is the point set of an
open substack by the surjectivity half of **Stacks 06FJ**,
`AlgebraicGeometry.Stack.exists_openSubstack_pointSet_eq`. -/
theorem exists_openSubstack_mem_pointSet_of_isOpenSubspace
    (W : Subfunctor Fsp) (hW : Space.IsOpenSubspace B S hS W)
    (z : Space.points B S hS Fsp)
    (hz : z ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι)) :
    ∃ V : OpenSubstack (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g),
      spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
          (representingEquivalence B S hS Fsp
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor z ∈
        V.pointSet B S hS ∧
      V.pointSet B S hS =
        spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
            (representingEquivalence B S hS Fsp
              (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor ''
          Set.range (Space.pointsMap B S hS W.toFunctor W.ι) := by
  obtain ⟨V, hV⟩ := exists_openSubstack_pointSet_eq B S hS
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _
    (isOpenMap_spacePointMap_representing B S hS Fsp
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF _
      (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hW.2))
  exact ⟨V, hV ▸ Set.mem_image_of_mem _ hz, hV⟩

end OpenSubstack

end AlgebraicGeometry.Stack

end
