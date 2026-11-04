module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus

/-!
# The isomorphism locus of a proper birational morphism at a codimension-zero point

Let `f : Y ⟶ X` be a proper birational morphism of schemes with `X` Noetherian and `Y` reduced,
and let `U ⊆ X` be the maximal open over which `f` is an isomorphism.  [Stacks, Tag 0BFP] lists
four kinds of point that `U` contains; item (1) is a point of codimension zero on `X`, and that
is what is proved here.

Item (2) is
`AlgebraicGeometry.mem_maximal_isomorphism_open_of_isDiscreteValuationRing` in
`StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusDVR`, and items (3)
and (4) are `AlgebraicGeometry.exists_isIso_restrict_of_finite_fiber_of_normal` and
`AlgebraicGeometry.mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal` in
`StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus`.

The source deduces item (1) from Morphisms, Lemma [Stacks, Tag 0BAJ]: a birational morphism is
an isomorphism over a dense open of its target, and a dense open contains every point of
codimension zero.

## Main results

* `AlgebraicGeometry.finite_irreducibleComponents_of_isBirational`: the source of a birational
  morphism has as many irreducible components as the target, so finitely many if the target has
  finitely many.
* `AlgebraicGeometry.exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian`:
  a separated birational morphism of finite type onto a Noetherian scheme is an isomorphism
  over a dense open of its target.
* `AlgebraicGeometry.exists_isIso_restrict_of_mem_genericPoints`: such a morphism is an
  isomorphism over a neighbourhood of every point of codimension zero.
* `AlgebraicGeometry.mem_maximal_isomorphism_open_of_mem_genericPoints`:
  **[Stacks, Tag 0BFP] item (1)** — the maximal open over which `f` is an isomorphism contains
  every point of codimension zero.

## Implementation notes

"`x` has codimension zero on `X`" is `x ∈ TopologicalSpace.genericPoints X`, that is,
`closure {x}` is an irreducible component of `X`: the codimension of a point is the codimension
of the irreducible closed subset it generates, and that is zero exactly when the subset is
maximal among irreducible closed subsets, i.e. is an irreducible component.

The hypothesis spellings of the registration are those of `BirationalIsomorphismLocus`,
verbatim: `[IsNoetherian X] [IsProper f] [IsReduced Y]` with `IsBirational f`, and "the maximal
open where `f` is an isomorphism" as `IsGreatest { V : X.Opens | IsIso (f ∣_ V) } U`.  The two
lemmas behind it ask only for what their proofs use, namely that `f` be separated and locally of
finite type.

Both hypotheses of [Stacks, Tag 0BAJ] on the irreducible components are available here: those of
`X` are finitely many because a Noetherian scheme is a Noetherian space, and those of `Y` are
then finitely many because a birational morphism bijects generic points.  Its disjunctive
hypotheses are met by separatedness and — since `X` is Noetherian and `f` is locally of finite
type — by `f` being locally of finite presentation; the reducedness of `Y` is not what makes
this half work, the reducedness in [Stacks, Tag 0BAJ] being that of the *target*.

## References

* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry

universe u

/-! ### Points of codimension zero -/

/-- The source of a birational morphism whose target has finitely many irreducible components
again has finitely many irreducible components: generic points of components biject across a
birational morphism, and in a scheme they correspond to the components. -/
public theorem finite_irreducibleComponents_of_isBirational {X Y : Scheme.{u}} (f : Y ⟶ X)
    [Finite (irreducibleComponents X)] (hf : IsBirational f) :
    Finite (irreducibleComponents Y) := by
  have hX : (genericPoints X).Finite := genericPoints.finite (Set.toFinite _)
  have himage : (f '' genericPoints Y).Finite := by
    rw [hf.bijOn.image_eq]
    exact hX
  have : Finite (genericPoints Y) :=
    (Set.Finite.of_finite_image himage hf.bijOn.injOn).to_subtype
  exact Finite.of_equiv _ (genericPoints.equiv (α := Y))

/-- A separated birational morphism locally of finite type onto a Noetherian scheme is an
isomorphism over a dense open subscheme of its target.

This is [Stacks, Tag 0BAJ] with its hypotheses discharged: a Noetherian scheme is a Noetherian
space, so it and — the morphism being birational — the source have finitely many irreducible
components, and a morphism locally of finite type onto a Noetherian scheme is locally of finite
presentation. -/
@[ega "I 6.5.5" "sufficiency in (ii)"]
public theorem exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsSeparated f] [LocallyOfFiniteType f]
    (hf : IsBirational f) :
    ∃ V : X.Opens, Dense (V : Set X) ∧ IsIso (f ∣_ V) := by
  have : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have : Finite (irreducibleComponents Y) := finite_irreducibleComponents_of_isBirational f hf
  exact exists_dense_open_isIso_morphismRestrict_of_isBirational f hf (Or.inr inferInstance)
    (Or.inr inferInstance)

/-- A separated birational morphism locally of finite type onto a Noetherian scheme is an
isomorphism over a neighbourhood of every point of codimension zero of its target: it is an
isomorphism over a dense open, and a dense open of a Noetherian space contains every generic
point of an irreducible component. -/
@[ega "I 6.5.5" "sufficiency in (ii)"]
public theorem exists_isIso_restrict_of_mem_genericPoints
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsSeparated f] [LocallyOfFiniteType f]
    (hf : IsBirational f) (x : X) (hx : x ∈ genericPoints X) :
    ∃ V : X.Opens, x ∈ V ∧ IsIso (f ∣_ V) := by
  obtain ⟨V, hVdense, hViso⟩ :=
    exists_dense_open_isIso_morphismRestrict_of_isBirational_of_isNoetherian f hf
  exact ⟨V, mem_of_mem_genericPoints_of_dense V hVdense hx, hViso⟩

/-- **Stacks Project, Tag 0BFP (codimension zero).**
Let `f : Y ⟶ X` be a proper birational morphism, where `X` is Noetherian and `Y` is reduced. The
maximal open over which `f` is an isomorphism contains every point of codimension zero on `X`,
that is, every generic point of an irreducible component of `X`. -/
@[stacks 0BFP "item (1): a point of codimension zero, a generic point of a component"]
public theorem mem_maximal_isomorphism_open_of_mem_genericPoints
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (U : X.Opens)
    (hU : IsGreatest { V : X.Opens | IsIso (f ∣_ V) } U) (x : X)
    (hx : x ∈ genericPoints X) :
    x ∈ U :=
  mem_maximal_isomorphism_open_of_exists_isIso_restrict f U hU x
    (exists_isIso_restrict_of_mem_genericPoints f hf x hx)

end AlgebraicGeometry

end
