module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperBaseChange
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObject
public import StacksFrontier.Topology.Simplicial.ComponentInclusion

/-!
# The comparison functor from the simplicial Zariski site to the total site of `LC_qc/U`

Let `S` be a locally quasi-compact Zariski situation and let `U` be a simplicial object of its
quasi-compact site `LC_qc` of **Tag 09X2**. Write `|U|` for the underlying simplicial
topological space `U ⋙ siteToTop`.

The upper horizontal arrow of the diagram of **Tag 0DAF** is a morphism of topoi
`h : Sh((LC_qc/U)_total) ⟶ Sh(U_Zar)`. A morphism of topoi in that direction is presented by a
functor in the *same* direction between the underlying categories, by **Tag 00X1**; this file
constructs that functor, `Stacks.Topology.Simplicial.qcTotalComparisonFunctor`.

## The morphism of Tag 0DAF need not be a morphism of simplicial sites

The morphism `h` is not expressible as a morphism of simplicial sites, because
`CategoryTheory.SimplicialSite` demands a strict functor `SimplexCategory ⥤ Cat` while base
change `CategoryTheory.Over.pullback` is only pseudo-functorial, and
`CategoryTheory.SimplicialSiteMorphism` has exactly two constructors — `ofMorphismOfSites`
(case (A) to case (A)) and `ofCocontinuous` (case (B) to case (B)) — with no constructor mixing
the two cases. All of that is accurate.

It is, however, an obstruction to presenting `h` *as a `SimplicialSiteMorphism`*, not to `h`.
Tag 0DAF asks only for a commutative square of topoi, and a morphism of topoi between the two
total topoi needs no simplicial structure on the morphism at all: it needs one functor between
the two total categories. Both total categories are Grothendieck-type constructions over
`SimplexCategoryᵒᵖ`:

* `Stacks.Topology.Simplicial.SimplicialOpen |U|` of **Tag 09VL** has objects the pairs
  `(n, V)` with `V` an open of `|U|_n`, and a morphism `(n, V) ⟶ (m, W)` is a simplex map
  `α` with `V ≤ |U|(α)^{-1} W`;
* `(LC_qc/U)_total` is `Grothendieck (U ⋙ CategoryTheory.Over.mapFunctor _)`, whose objects
  are the pairs `(n, V/U_n)` and whose transition functors are `CategoryTheory.Over.map`,
  *postcomposition*, which is strictly functorial. This is case (B) of Situation 09WE, and for a
  site that is small it is `CategoryTheory.SimplicialOver.slices` on the nose, the total
  category of `CategoryTheory.SimplicialOver.situation`. The diagram is spelled out rather than
  taken from `SimplicialOver` because `slices` is pinned at `Cat.{u, u}` while `LC_qc` has
  objects in `Type (u + 1)` — the size gap of Tag 09X2 that its small model closes.

So the comparison is the degreewise open-subspace functor
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice` of each `U_n`, assembled over
the simplex direction. No comparison of base changes enters, because no base change enters: the
transitions on the target are `Over.map`, and a morphism of `SimplicialOpen` is exactly the
datum that the open `V` is carried into the open `W` by `|U|(α)`.

Functoriality is free rather than laborious, and for a reason worth recording: the structure
morphism of an open subspace is a monomorphism
(`Stacks.Topology.LocallyQuasiCompactZariskiSituation.mono_opensToSlice_hom`), so a morphism
over `U_m` *into* a comparison object is unique if it exists
(`…over_hom_opensToSlice_ext`). Every fibre morphism of this functor has such a target, so
`map_id` and `map_comp` hold by uniqueness and the pseudo-functoriality that obstructs the
simplicial-site route is never met. Existence is `…nonempty_over_hom_opensToSlice`, which is the
full faithfulness of the inclusion of `LC_qc` into `TopCat`.

This file constructs the functor of categories; continuity of this functor and exactness of the
induced `u_s`, the two clauses of Tag 00X1 which make it a morphism of topoi, are proved
elsewhere.

## Main definitions

* `Stacks.Topology.Simplicial.qcComparisonObj`: the open subspace of `U_n` attached to an open
  of `|U|_n`, as an object of `LC_qc/U_n`.
* `Stacks.Topology.Simplicial.qcTotalComparisonFunctor`: the functor
  `SimplicialOpen |U| ⥤ (LC_qc/U)_total` underlying the upper horizontal arrow of the diagram
  of Tag 0DAF.

## Main results

* `Stacks.Topology.Simplicial.qcTotalComparisonFunctor_obj_levelFunctor`: in each simplicial
  degree the functor is the open-subspace comparison of Tag 09X3.

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09WL](https://stacks.math.columbia.edu/tag/09WL)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace Stacks.Topology.Simplicial

open Stacks.Topology

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  (U : SimplicialObject S.category)

/-- The underlying simplicial topological space of a simplicial object of `LC_qc`. -/
abbrev qcSimplicialSpace : SimplicialObject TopCat.{u} :=
  U ⋙ S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop

/-- The object of `LC_qc/U_n` attached to an open subset of `|U|_n`: the open subspace, with its
inclusion. This is the value of the comparison functor of Tag 0DAF in one simplicial degree. -/
def qcComparisonObj (A : SimplicialOpen (qcSimplicialSpace S U)) : Over (U.obj A.degree) :=
  (S.opensToSlice (U.obj A.degree)).1.obj A.toOpens

/-- A morphism of simplicial opens carries the source open into the target open along the
transition map of the simplicial space, which is the hypothesis of
`nonempty_over_hom_opensToSlice` for the relocalized comparison object. -/
theorem qcComparison_mem {A B : SimplicialOpen (qcSimplicialSpace S U)}
    (g : SimplicialOpen.Hom A B) :
    ∀ p : ((Over.map (U.map g.base)).obj (qcComparisonObj S U A)).left.obj,
      (((Over.map (U.map g.base)).obj (qcComparisonObj S U A)).hom :
        ((Over.map (U.map g.base)).obj (qcComparisonObj S U A)).left.obj →
          (U.obj B.degree).obj) p ∈ B.toOpens :=
  fun p => g.le p.2

/-- The fibre morphism of the comparison functor in one simplicial degree: the restriction of
the transition map `|U|(α)` to the two opens. It exists because the inclusion of `LC_qc` into
`TopCat` is fully faithful, and it is unique because the inclusion of an open subspace is a
monomorphism. -/
def qcComparisonMap {A B : SimplicialOpen (qcSimplicialSpace S U)} (g : SimplicialOpen.Hom A B) :
    (Over.map (U.map g.base)).obj (qcComparisonObj S U A) ⟶ qcComparisonObj S U B :=
  (S.nonempty_over_hom_opensToSlice ((Over.map (U.map g.base)).obj (qcComparisonObj S U A))
    B.toOpens (qcComparison_mem S U g)).some

/-- **The comparison functor underlying the upper horizontal arrow of the diagram of
Tag 0DAF.** It sends an open `V` of `|U|_n` to the open subspace `V` of `U_n`, read as an object
of `LC_qc/U_n`, and a morphism of simplicial opens to the restriction of its transition map.

This is a functor of categories; continuity, and hence the morphism of topoi itself, is not
proved here. -/
def qcTotalComparisonFunctor :
    SimplicialOpen (qcSimplicialSpace S U) ⥤
      Grothendieck (U ⋙ Over.mapFunctor S.category) where
  obj A := { base := A.degree, fiber := qcComparisonObj S U A }
  map {_ _} g := { base := g.base, fiber := qcComparisonMap S U g }
  map_id _ := Grothendieck.ext _ _ rfl (S.over_hom_opensToSlice_ext _ _)
  map_comp _ _ := Grothendieck.ext _ _ rfl (S.over_hom_opensToSlice_ext _ _)

/-- The comparison functor sends a simplicial open to an object of its own simplicial degree. -/
@[simp]
theorem qcTotalComparisonFunctor_obj_base (A : SimplicialOpen (qcSimplicialSpace S U)) :
    ((qcTotalComparisonFunctor S U).obj A).base = A.degree := rfl

/-- The fibre of the comparison functor at a simplicial open `A` is `qcComparisonObj S U A`. -/
@[simp]
theorem qcTotalComparisonFunctor_obj_fiber (A : SimplicialOpen (qcSimplicialSpace S U)) :
    ((qcTotalComparisonFunctor S U).obj A).fiber = qcComparisonObj S U A := rfl

/-- The image of a morphism `g` under the comparison functor lies over the simplex map of `g`. -/
@[simp]
theorem qcTotalComparisonFunctor_map_base {A B : SimplicialOpen (qcSimplicialSpace S U)}
    (g : A ⟶ B) : ((qcTotalComparisonFunctor S U).map g).base = g.base := rfl

/-- The comparison functor lies over the simplex direction: it does not move simplicial
degrees. -/
theorem qcTotalComparisonFunctor_comp_forget :
    qcTotalComparisonFunctor S U ⋙ Grothendieck.forget _ =
      { obj := fun A => A.degree, map := fun g => g.base } := rfl

/-- **The comparison functor is the Tag 09X3 comparison in each simplicial degree.** The value
on an open `V` of `|U|_n`, included into the simplicial site in degree `n` by
`Stacks.Topology.Simplicial.levelFunctor`, is the open subspace `V` of `U_n` sitting in the
degree-`n` fibre of the total category.

This is what identifies the functor as the one Tag 0DAF describes rather than merely some
functor between the two total categories: the arrow it presents is degreewise the open-subspace
comparison whose topos-level inverse image is
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonInverseImage`, the first leg of
the bottom horizontal arrow `(h_{-1})^{-1}` of the same diagram. On morphisms there is nothing
to check: every fibre morphism of this functor has a comparison object as its target, and
`…over_hom_opensToSlice_ext` says there is at most one such morphism. -/
theorem qcTotalComparisonFunctor_obj_levelFunctor (n : SimplexCategoryᵒᵖ)
    (V : Opens ((qcSimplicialSpace S U).obj n)) :
    (qcTotalComparisonFunctor S U).obj ((levelFunctor (qcSimplicialSpace S U) n).obj V) =
      { base := n, fiber := (S.opensToSlice (U.obj n)).1.obj V } := rfl

end Stacks.Topology.Simplicial

end
