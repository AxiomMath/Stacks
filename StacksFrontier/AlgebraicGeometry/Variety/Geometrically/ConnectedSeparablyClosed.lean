module

public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine
public import StacksFrontier.RingTheory.GeometricallyConnected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connected components after extending a separably closed field

Let `X` be a scheme over a separably closed field `k`. After any field extension `k'/k`, the
canonical morphism from the base change of `X` to `X` induces a bijection on connected
components. Consequently, geometric connectedness over `k` is equivalent to connectedness
of `X`.

## Main results

* `AlgebraicGeometry.baseChange_connectedComponents_bijective` gives the canonical bijection on
  connected components after a field extension.
* `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace` characterizes geometric
  connectedness over a separably closed field.

## Implementation notes

The base change along `k → k'` is the pullback against the corresponding morphism
`Spec k' ⟶ Spec k`, and the map to `X` is its first projection. Thus the first result
specifies the induced map on connected components rather than merely asserting that some
bijection exists. The second result states the final assertion of Tag 0363, that geometric
connectedness over a separably closed field is connectedness, as a separate equivalence.

## References

* [Stacks Project, Tag 0363](https://stacks.math.columbia.edu/tag/0363)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Over a separably closed field, the spectrum of any field extension is geometrically
connected. -/
private lemma geometricallyConnected_spec (k k' : Type u) [Field k] [IsSepClosed k]
    [Field k'] [Algebra k k'] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
  (geometricallyConnected_spec_iff k k').2
    ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum k k').2 inferInstance)

/-- **Stacks Project, Tag 0363.** Base change along any extension of a separably closed
field induces a bijection on the connected components of a scheme. -/
@[stacks 0363 "bijection on connected components",
  ega "III 4.3.4" "special case",
  ega "IV 4.4.1" "special case",
  ega "IV 4.5.15" "special case",
  ega "IV 4.5.21" "more general",
  ega "IV 4.5.6" "(i), special case", sga "3 VIA 4.1" "special case"]
public theorem baseChange_connectedComponents_bijective
    (k k' : Type u) [Field k] [IsSepClosed k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Function.Bijective
      (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).continuous.connectedComponentsMap := by
  let g : Spec (.of k') ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let : GeometricallyConnected g := geometricallyConnected_spec k k'
  simpa only [Function.Bijective, Function.Injective, Function.Surjective,
    Scheme.Hom.connectedComponentsHomeomorph_apply] using
    ((pullback.fst f g).connectedComponentsHomeomorph (pullback.fst f g).isOpenMap).bijective

/-- **Stacks Project, Tag 0363.** Over a separably closed field, a scheme is geometrically
connected if and only if its underlying topological space is connected. -/
@[stacks 0363 "geometric connectedness",
  ega "IV 4.4.4" "more general",
  ega "IV 8.4.5" "special case"]
public theorem geometricallyConnected_iff_connectedSpace
    (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔ ConnectedSpace X := by
  refine ⟨fun _ ↦ GeometricallyConnected.connectedSpace_of_subsingleton f, fun _ ↦ ?_⟩
  rw [AlgebraicGeometry.geometricallyConnected_iff,
    AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : GeometricallyConnected g := geometricallyConnected_spec k K
  exact GeometricallyConnected.connectedSpace (pullback.fst f g) (pullback.fst f g).isOpenMap

end AlgebraicGeometry
