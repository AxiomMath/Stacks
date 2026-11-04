module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreUnramifiedRegularSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# The slicing sequence of Stacks 06N3 off the space-level hypotheses

`AlgebraicGeometry.Space.exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt`
produces the slicing sequence of the chart construction of **Stacks 06N3** in the étale local
ring `𝒪_{F, z̄}` from two hypotheses about one étale-chart square — unramifiedness of the
underlying morphism of schemes `V ⟶ U` at the point `v` below the geometric point, and
regularity of the ordinary local ring `𝒪_{V, v}`. What the chart construction has in hand is
instead the two *space-level* statements those come from: unramifiedness of the projection
`F ⟶ U` of the source's cartesian diagram (**Stacks 03ZH**, part (1)), which the monomorphy of
the residual gerbe supplies, and regularity of `F` itself (**Stacks 06M1**), `F` being smooth
over a field. This file performs the two reductions, so that the sequence can be read off the
hypotheses the construction produces.

## Main results

* `isRegularLocalRing_chartLocalRing`: the local ring of any small étale neighbourhood of a
  geometric point of a regular algebraic space is a regular local ring.
* `unramified_chartMap_of_isUnramified`: the morphism of schemes in an étale-chart square over an
  unramified morphism of algebraic spaces is unramified — the defining property of
  `AlgebraicGeometry.Space.IsUnramified`, read at the square the slicing sequence is produced on.
* `exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_isUnramified`: **the slicing
  sequence of Stacks 06N3 off the space-level hypotheses.**

## Implementation notes

Regularity of an algebraic space is `AlgebraicGeometry.Space.HasEtaleLocalProperty` at
`AlgebraicGeometry.IsRegular`, which is the form **Stacks 06M1** delivers. Passing from the atlas
on which it is asserted to the chart of a prescribed small étale neighbourhood is
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale` (**Stacks 03E8**), the chart of a small
étale neighbourhood being an étale chart by definition; the local ring is then regular by
`AlgebraicGeometry.isRegular_iff_regular_stalks` (**Stacks 02IT**).

Local finite type of the chart morphism, which
`...exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt` asks for as an
instance, is not a separate hypothesis: an unramified morphism of schemes is locally of finite
type (**Stacks 02G4**).

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The local ring of a chart of a regular algebraic space is regular.** Regularity of an
algebraic space is asserted on one surjective étale atlas; the chart of a small étale
neighbourhood of a geometric point is an étale scheme over the space, so **Stacks 03E8** carries
regularity to it, and **Stacks 02IT** reads it on the local ring at the point of the
neighbourhood.

This is the regularity of `𝒪_{V, v}` that the chart construction of **Stacks 06N3** gets from
**Stacks 06M1** at the fibre `F = U ×_𝒳 Spec k`, which is smooth over a field. -/
theorem isRegularLocalRing_chartLocalRing {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hreg : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsRegular X))
    {z : GeometricPoint B S hS F} (N : SmallEtaleNeighborhood z) :
    IsRegularLocalRing (chartLocalRing B S hS F N) :=
  ((isRegular_iff_regular_stalks (chartScheme N.chart)).mp
    ((exists_atlas_iff_forall_etale B S hS F (fun X : Scheme.{u} => IsRegular X) hF).mp hreg
      N.chart.obj.left N.chart.obj.hom N.chart.property)).2 (chartPoint B S hS F N)

/-- **Stacks 03ZH, part (1) read at one square.** The morphism of schemes in a commuting square
of étale charts over an unramified morphism of algebraic spaces is unramified. This is what
`AlgebraicGeometry.Space.IsUnramified` says, at the square on which the slicing sequence of
**Stacks 06N3** is produced: the chart of a small étale neighbourhood of a geometric point of the
fibre, over an étale chart of the smooth chart of the stack. -/
theorem unramified_chartMap_of_isUnramified {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ξ : F ⟶ G}
    (hξ : IsUnramified B S hS ξ) (Vch : SmallEtale B S hS F) (Uch : SmallEtale B S hS G)
    (gVU : Vch.obj.left ⟶ Uch.obj.left)
    (hsq : Vch.obj.hom ≫ ξ = yoneda.map gVU ≫ Uch.obj.hom) :
    Unramified ((BigFppfOver.toScheme B S hS).map gVU) :=
  hξ Vch.obj.left Uch.obj.left Vch.obj.hom Uch.obj.hom gVU Vch.property Uch.property hsq.symm

/-- **The slicing sequence of Stacks 06N3 in the étale local ring, off the space-level
hypotheses.** Let `ξ : F ⟶ X` be an **unramified** morphism of algebraic spaces with `F`
**regular**, let `z` be a geometric point of `F`, and let a small étale neighbourhood `N` of `z`
map to an étale chart `Uch` of `X` over `ξ`. Then there are `d = (𝔪_v).spanFinrank` elements of
the maximal ideal of `𝒪_{U, u}` whose images in the étale local ring `𝒪_{F, z̄}` form a regular
sequence **generating** the maximal ideal of `𝒪_{F, z̄}`.

This is
`AlgebraicGeometry.Space.exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt`
with its two hypotheses on the chart square traded for the two hypotheses on the algebraic
spaces that the chart construction of **Stacks 06N3** produces: unramifiedness of the projection
`F = U ×_𝒳 Spec k ⟶ U`, which the monomorphy of the residual gerbe of the finite type point
supplies, and regularity of `F`, which is **Stacks 06M1** at the smooth structure morphism
`F ⟶ Spec k`. -/
theorem exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_isUnramified
    {Xs Fs : AlgebraicSpaces B S hS} (ξ : Fs ⟶ Xs) (hξ : IsUnramified B S hS ξ.hom)
    (hreg : HasEtaleLocalProperty B S hS Fs.1 (fun X : Scheme.{u} => IsRegular X))
    {z : GeometricPoint B S hS Fs.1} (N : SmallEtaleNeighborhood z)
    (Uch : SmallEtale B S hS Xs.1) (gNU : N.chart.obj.left ⟶ Uch.obj.left)
    (hsq : N.chart.obj.hom ≫ ξ.hom = yoneda.map gNU ≫ Uch.obj.hom) :
    letI : IsLocalRing (etaleLocalRing B S hS Fs.1 z) :=
      isLocalRing_etaleLocalRing B S hS Fs.1 Fs.2 z
    ∃ t : Fin (maximalIdeal (chartLocalRing B S hS Fs.1 N)).spanFinrank →
        chartLocalRing B S hS Xs.1 (targetNeighborhood B S hS N Uch gNU hsq),
      (∀ i, t i ∈ maximalIdeal
        (chartLocalRing B S hS Xs.1 (targetNeighborhood B S hS N Uch gNU hsq))) ∧
        RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 z)
            (List.ofFn fun i => etaleLocalRingMap Fs.2 ξ.hom z
              (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2
                (targetNeighborhood B S hS N Uch gNU hsq) (t i))) ∧
          Ideal.ofList (List.ofFn fun i => etaleLocalRingMap Fs.2 ξ.hom z
              (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2
                (targetNeighborhood B S hS N Uch gNU hsq) (t i))) =
            maximalIdeal (etaleLocalRing B S hS Fs.1 z) := by
  have : Unramified ((BigFppfOver.toScheme B S hS).map gNU) :=
    unramified_chartMap_of_isUnramified B S hS hξ N.chart Uch gNU hsq
  exact exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt B S hS ξ N Uch
    gNU hsq (Unramified.unramifiedAt (chartPoint B S hS Fs.1 N))
    (isRegularLocalRing_chartLocalRing B S hS Fs.2 hreg N)

end AlgebraicGeometry.Space

end
