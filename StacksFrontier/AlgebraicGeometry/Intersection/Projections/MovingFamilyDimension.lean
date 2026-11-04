module

public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two dimension bounds for a moving family

A dimension count for a family of projections needs two inequalities, both of which are
general and neither of which is about projections.

The first is that the dimension of a topological space does not grow along a continuous closed
surjection: the image of such a map has dimension at most that of the source.

The second bounds the dimension of a scheme `X` over a field by the dimension of an
intermediate scheme `Y` plus the dimensions of the fibres of `X ⟶ Y`:

```
dim X ≤ dim Y + sup_x dim_x X_{f(x)}.
```

For a family parametrised by `Y`, the second inequality turns a bound on each member of the
family into a bound on the total space, and the first then transports that bound to the image
of the total space under a proper map.

## Main results

* `Topology.topologicalKrullDim_add_one_le_of_ne_univ`: in an irreducible Noetherian space a
  proper closed subset has dimension at least one less.

* `Topology.topologicalKrullDim_le_of_isClosedMap_of_surjective`: the dimension of the target
  of a continuous closed surjection is at most the dimension of its source.
* `AlgebraicGeometry.topologicalKrullDim_le_add_iSup_fiber`: the dimension of a scheme over a
  field factoring through another such scheme is at most the dimension of the intermediate
  scheme plus the supremum of the dimensions of the fibres.
* `AlgebraicGeometry.topologicalKrullDim_le_of_forall_fiber_le`: the same bound in the form a
  dimension count uses it, with the two suprema replaced by hypothesised bounds.

## Implementation notes

The first statement is **Stacks Tag 02JF**, which is already available in the generality of a
surjection along which specializations or generalizations lift
(`Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap`); a
closed map is a specializing map, so only the hypotheses have to be rearranged. The Noetherian
hypothesis one would need for the component-counting proof is therefore not imposed; what is
needed instead is that the target be sober, which every scheme is. The source needs no
hypothesis at all.

The second statement is the global form of **Stacks Tag 02JS**,
`AlgebraicGeometry.topologicalKrullDimAt_fiber_comp_le_add`, which compares the three
successive fibres of a composition `X ⟶ Y ⟶ S` at a point. Over a one-point base the fibre of
a morphism is its own source
(`AlgebraicGeometry.topologicalKrullDimAt_eq_fiber_of_subsingleton`), so two of the three local
dimensions appearing there are the local dimensions of `X` and of `Y`, leaving the fibre of
`f : X ⟶ Y` as the only fibre in the statement. Passing from local to global dimensions is the
supremum formula of **Stacks Tag 0B7I**, used only in the direction `≤`, which is why no
finiteness or irreducibility hypothesis is needed and why the inequality cannot be upgraded to
an equality: the two suprema are over the same index set `X`, but a point realising the
dimension of `Y` need not be the image of a point realising the dimension of a fibre.

The empty case needs no separate treatment: both sides are then `⊥`, the supremum over an empty
index type, since `⊥` is absorbing for the addition of `WithBot ℕ∞`.

## References

* [Stacks Project, Tag 02JF](https://stacks.math.columbia.edu/tag/02JF)
* [Stacks Project, Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
* [Stacks Project, Tag 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Topology

/-- **The image of a continuous closed surjection has no bigger dimension than its source.**
Specializations lift along a closed map, so this is the closed-map case of
`Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap`
(Stacks Tag 02JF). The target is assumed sober, which holds for every scheme; the source needs
no hypothesis. -/
@[ega "IV 5.4.1" "more general"]
theorem topologicalKrullDim_le_of_isClosedMap_of_surjective {Z W : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] [QuasiSober W] [T0Space W] {f : Z → W} (hcont : Continuous f)
    (hclosed : IsClosedMap f) (hsurj : Function.Surjective f) :
    topologicalKrullDim W ≤ topologicalKrullDim Z :=
  topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap f hcont hsurj
    (Or.inl hclosed.specializingMap)

/-- **In an irreducible Noetherian space a proper closed subset has dimension at least one
less.** A nonempty open subset of an irreducible space is dense, so a closed subset with
nonempty interior is everything; a proper closed subset is therefore nowhere dense, and
`IsNowhereDense.topologicalKrullDim_add_one_le` applies. -/
theorem topologicalKrullDim_add_one_le_of_ne_univ {X : Type*}
    [TopologicalSpace X] [NoetherianSpace X] [IrreducibleSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S ≠ Set.univ) :
    topologicalKrullDim S + 1 ≤ topologicalKrullDim X := by
  refine IsNowhereDense.topologicalKrullDim_add_one_le ?_ hS
  rw [IsNowhereDense, hS.closure_eq]
  by_contra hint
  have hopen : (interior S).Nonempty := Set.nonempty_iff_ne_empty.mpr hint
  have hdense : Dense (interior S) := by
    rw [dense_iff_inter_open]
    intro U hU hUne
    have h := (IrreducibleSpace.isIrreducible_univ X).2 U (interior S) hU isOpen_interior
      (by simpa using hUne) (by simpa using hopen)
    simpa using h
  refine hne (Set.eq_univ_of_univ_subset ?_)
  rw [← hS.closure_eq]
  exact hdense.closure_eq ▸ closure_mono interior_subset

end Topology

namespace AlgebraicGeometry

/-- The local form of the bound, over a one-point base: the local dimension of `X` at a point
is at most the local dimension there of the fibre of `f` through it, plus the local dimension
of `Y` at its image. Over a one-point base the outer two fibres of the composition
`X ⟶ Y ⟶ S` are `X` and `Y` themselves, so this is Stacks Tag 02JS. -/
private lemma topologicalKrullDimAt_le_add_of_subsingleton {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) [Subsingleton S] [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X) :
    topologicalKrullDimAt X x ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) + topologicalKrullDimAt Y (f x) := by
  rw [topologicalKrullDimAt_eq_fiber_of_subsingleton (f ≫ g) x,
    topologicalKrullDimAt_eq_fiber_of_subsingleton g (f x)]
  exact topologicalKrullDimAt_fiber_comp_le_add f g x

/-- **The dimension of a scheme over a field is bounded by the dimension of an intermediate
scheme plus the dimensions of the fibres.** For `f : X ⟶ Y` and `g : Y ⟶ Spec k` locally of
finite type,

```
dim X ≤ dim Y + sup_x dim_x X_{f(x)},
```

the supremum being over the points `x` of `X` and `X_{f(x)}` the fibre of `f` through `x`. -/
@[ega "IV 10.6.1" "(iii), special case", sga "6 X 3.3" "special case"]
theorem topologicalKrullDim_le_add_iSup_fiber (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    topologicalKrullDim X ≤
      topologicalKrullDim Y + ⨆ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  exact (topologicalKrullDimAt_le_add_of_subsingleton f g x).trans
    ((le_of_eq (add_comm _ _)).trans
      (add_le_add (topologicalKrullDimAt_le_topologicalKrullDim (f x))
        (le_iSup (fun z : X => topologicalKrullDimAt (f.fiber (f z)) (f.asFiber z)) x)))

/-- **The dimension bound in the form a dimension count uses it.** If every fibre of
`f : X ⟶ Y` has dimension at most `d` at every point of `X`, and `Y` has dimension at most `e`,
then `X` has dimension at most `e + d`. Both morphisms are assumed locally of finite type over
the base field; no flatness is needed, the bound being an inequality. -/
theorem topologicalKrullDim_le_of_forall_fiber_le (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {d e : WithBot ℕ∞} (hY : topologicalKrullDim Y ≤ e)
    (hfib : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ d) :
    topologicalKrullDim X ≤ e + d :=
  (topologicalKrullDim_le_add_iSup_fiber k f g).trans (add_le_add hY (iSup_le hfib))

end AlgebraicGeometry

end
