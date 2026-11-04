module

public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# At every point of an at-worst-nodal curve the local ring is regular or the point is a node

Let `k` be an algebraically closed field and `X` a reduced one-dimensional `k`-scheme, locally of
finite type, whose singularities are at worst nodal. Then at *every* point `x` of `X` — closed or
not — either `𝒪_{X,x}` is a regular local ring or `x` is a node.

The predicate `Stacks.Curves.HasAtWorstNodalSingularities` constrains only the closed points: it
says that each of them is either smooth over `k` or a node. Two things turn that into a statement
about all points.

At a closed point the smoothness alternative is converted into regularity of the local ring. Over
a perfect field the smooth locus of a scheme locally of finite type *is* the regular locus, which
is `AlgebraicGeometry.smoothAt_locus_eq_regular_locus`; an algebraically closed field is perfect.

At a point that is not closed the dimension hypothesis takes over, and the nodal hypothesis is not
used at all. The closure of such a point is an irreducible closed set which is not a single point,
so it already carries a strict specialization inside it; were it also strictly contained in an
irreducible component there would be a chain of three irreducible closed subsets of `X` and the
Krull dimension would be at least two. Hence the closure of `x` is an irreducible component, `x`
is its generic point, and on a reduced scheme the local ring at the generic point of a component
is a field — in particular a regular local ring.

## Main results

* `Stacks.Curves.isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities` —
  **at every point of an at-worst-nodal reduced one-dimensional curve over an algebraically
  closed field the local ring is regular or the point is a node.**

Along the way, and of independent use:

* `Stacks.Curves.closure_singleton_mem_irreducibleComponents_of_not_isClosed` — on a space of
  Krull dimension at most one a point which is not closed is the generic point of an irreducible
  component.
* `Stacks.Curves.isRegularLocalRing_stalk_of_smoothAt` — a point at which a scheme locally of
  finite type over a field is smooth has a regular local ring.

## References

* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology

universe u

namespace Stacks.Curves

/-- **On a space of Krull dimension at most one a point which is not closed is the generic point
of an irreducible component.** Any irreducible component containing the closure of `x` contains
it with equality: otherwise the closure of `x` sits strictly below that component and strictly
above the closure of a point specializing to `x`, which is a chain of three irreducible closed
subsets. -/
@[ega "II 7.4.3" "partial"]
public theorem closure_singleton_mem_irreducibleComponents_of_not_isClosed
    {T : Type u} [TopologicalSpace T] [T0Space T] (hdim : topologicalKrullDim T ≤ 1) {x : T}
    (hx : ¬ IsClosed ({x} : Set T)) :
    closure ({x} : Set T) ∈ irreducibleComponents T := by
  by_contra hmem
  refine hx (Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
    hdim isClosed_closure ?_ (subset_closure (Set.mem_singleton x)))
  intro C hC hCsub
  obtain ⟨C', hC', hsub'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set T)) isIrreducible_singleton.closure
  have hCC' : C = C' := hC.eq_of_le hC'.1 (hCsub.trans hsub')
  exact hmem (Set.Subset.antisymm (hCC' ▸ hsub') hCsub ▸ hC)

/-- **A smooth point has a regular local ring.** A scheme smooth over a field is regular
(`AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field`), and smoothness at a point
is smoothness of the restriction to an open neighbourhood of it, whose local ring there is the
local ring of the scheme. -/
@[sga "1 II 5.3" "more general"]
public theorem isRegularLocalRing_stalk_of_smoothAt (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x : X}
    (hsm : InfinitesimalLifting.SmoothAt f x) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hU⟩ := hsm
  have : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f (U := (⊤ : (Spec (.of k)).Opens)) (V := U) le_top]
    exact MorphismProperty.comp_mem @Smooth _ _ hU inferInstance
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ f) ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv
    (Scheme.Opens.stalkIso U ⟨x, hxU⟩).commRingCatIsoToRingEquiv

/-- **At every point of an at-worst-nodal curve the local ring is regular or the point is a
node.** At a closed point this is the dichotomy of
`Stacks.Curves.HasAtWorstNodalSingularities` with the smoothness alternative traded for
regularity of the local ring; at a point which is not closed the dimension hypothesis makes `x`
the generic point of an irreducible component, where reducedness makes the local ring a field. -/
public theorem isRegularLocalRing_stalk_or_isNode_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) ∨ Stacks.Curves.IsNode k X x := by
  by_cases hx : IsClosed ({x} : Set X)
  · rcases hnodal x hx with hsm | hnode
    · exact Or.inl (isRegularLocalRing_stalk_of_smoothAt k (X ↘ Spec (.of k)) hsm)
    · exact Or.inr hnode
  · exact Or.inl (mem_regularLocus_of_closure_mem_irreducibleComponents X x
      (closure_singleton_mem_irreducibleComponents_of_not_isClosed hdim.le hx))

end Stacks.Curves

end
