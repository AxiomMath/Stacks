module

public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort

/-!
# The singular locus of a normal surface over a complete local base is finite

A normal Noetherian scheme of dimension at most two whose regular locus is open has a finite
singular locus: the singular locus is then closed, and on a normal scheme of dimension at most
two every singular point is closed, so the singular locus is a closed set of closed points in a
Noetherian space.

Openness of the regular locus is exactly what the J-2 condition provides, and a scheme locally
of finite type over a Noetherian complete local ring is J-2 by [Stacks, Tag 07R5]. That is the
form in which this is used: a stage of a chain of normalized blowups over the spectrum of a
complete local ring is proper over it, hence locally of finite type over it.

## Main results

* `AlgebraicGeometry.finite_singularLocus_of_isJ2`: a normal Noetherian scheme of dimension at
  most two which is J-2 has a finite singular locus.
* `AlgebraicGeometry.finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing`: the
  same for a normal Noetherian scheme of dimension at most two locally of finite type over a
  Noetherian complete local ring.

## Implementation notes

`AlgebraicGeometry.singularLocus` is by definition the complement of
`AlgebraicGeometry.regularLocus`, so openness of the latter is closedness of the former with no
further work. That every singular point of a normal locally Noetherian scheme of dimension at
most two is closed is `AlgebraicGeometry.isClosed_singleton_of_mem_singularLocus`: the local ring
at such a point has Krull dimension exactly two — at most two by the bound on the dimension of
the scheme and more than one because a normal scheme is regular in codimension one — so the point
has maximal coheight. Finiteness of a closed set all of whose points are closed on a Noetherian
scheme is `AlgebraicGeometry.finite_of_isClosed_of_forall_isClosed_singleton`.

The J-2 condition is taken in its scheme form `AlgebraicGeometry.Scheme.IsJ2`, which asserts
openness of the regular locus of every scheme locally of finite type over the given one;
openness for the scheme itself is the case of its own identity morphism.

Note that no Nagata or excellence hypothesis appears in the first result: openness of the regular
locus is the only thing needed, and it is strictly weaker. The second result is the usable
specialization, and it is the standing situation of Step 2 of [Stacks, Tag 0BGM], where the base
has already been replaced by its completion.

## References

* [Stacks Project, Tag 07R5](https://stacks.math.columbia.edu/tag/07R5)
* [Stacks Project, Tag 07R1](https://stacks.math.columbia.edu/tag/07R1)
* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A normal Noetherian scheme of dimension at most two which is J-2 has a finite singular
locus.** The J-2 condition makes the regular locus open, so the singular locus is closed; on a
normal scheme of dimension at most two every singular point is closed; and a closed set of closed
points on a Noetherian scheme is finite. -/
theorem finite_singularLocus_of_isJ2 (X : Scheme.{u}) [IsNoetherian X] [IsNormal X]
    (hdim : topologicalKrullDim X ≤ 2) (hJ2 : Scheme.IsJ2 X) : (singularLocus X).Finite := by
  have hopen : IsOpen (regularLocus X) := hJ2.isOpen_regularLocus (𝟙 X)
  exact finite_of_isClosed_of_forall_isClosed_singleton hopen.isClosed_compl
    fun x hx => isClosed_singleton_of_mem_singularLocus X hdim x hx

/-- **A normal Noetherian scheme of dimension at most two locally of finite type over a
Noetherian complete local ring has a finite singular locus.** Such a scheme is J-2 by
[Stacks, Tag 07R5]. -/
theorem finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing (R : Type u)
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (IsLocalRing.maximalIdeal R) R] {X : Scheme.{u}} [IsNoetherian X] [IsNormal X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X ≤ 2) :
    (singularLocus X).Finite :=
  finite_singularLocus_of_isJ2 X hdim
    (Scheme.isJ2_of_locallyOfFiniteType_over_completeLocalRing R f)

end AlgebraicGeometry

end
