module

public import StacksFrontier.CategoryTheory.Bicategory.Functor.Cat.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism

/-!
# Descent for small étale sheaves along a family of algebraic spaces étale over `X`

Let `X` be an algebraic space and let `U i` be a family of algebraic spaces étale over `X`
whose structure morphisms are jointly surjective on points. Tag 04TS at the
spaces-étale site of `X`
(`AlgebraicGeometry.Space.SpacesEtale.isEquivalence_toDescentData_spacesEtale`) says that
sheaves on the *slice* of that site at its final object are descent data for the family, the
descent data living in the sheaf categories of the *slices* at the `U i`. This file moves the
descent data into the sheaf categories of the *members themselves*, first for their
spaces-étale sites and then for their small étale sites.

Both steps are the same construction applied twice:
`CategoryTheory.Pseudofunctor.transport` carries a pseudofunctor to `Cat` along a family of
equivalences of its fibres and comes with a canonical strong transformation, and
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_transport_iff` transports effective
descent along it. The two families of equivalences are already available: the site
equivalence of `AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall` for the first step,
and the comparison of topoi `AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`
(Tag 03G1) for the second.

The index type of the family is then freed: a family indexed by an arbitrary type contains a
jointly surjective subfamily indexed by the points of `X`, which is a type in `Type (u + 1)`,
so the covering lemma stated for that universe suffices. Specialising the result to the family
underlying an étale covering of algebraic spaces gives Tag 0GFS.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.spacesEtaleSheafSystem`, the pseudofunctor on the
  spaces-étale site of `X` whose fibre over `U` is the category of sheaves on the
  spaces-étale site of `U`;
* `AlgebraicGeometry.Space.SpacesEtale.smallEtaleSheafSystem`, the same with the small étale
  site of `U` as fibre.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isEquivalence_toDescentData_spacesEtaleSheafSystem` and
  `AlgebraicGeometry.Space.SpacesEtale.isEquivalence_toDescentData_smallEtaleSheafSystem`:
  effective descent for those two systems along a jointly surjective family.
* `AlgebraicGeometry.Space.SpacesEtale.ofArrows_toFinal_mem_topology_of_jointlySurjective` and
  `isEquivalence_toDescentData_smallEtaleSheafSystem_of_jointlySurjective` in the same
  namespace: the same covering lemma and the same effective descent for a family indexed by a
  type in an arbitrary universe.
* `isEquivalence_toDescentData_smallEtaleSheafSystem_of_isEtaleCovering`, again in that
  namespace: **Stacks 0GFS**, effective descent for small étale sheaves along an étale covering
  of algebraic spaces.

## Implementation notes

The descent data of Tag 0GFS live in the small étale sheaf categories of the members of the
covering, not on the slices of the spaces-étale site of `X`; that is why the two files this one
builds on withhold the tag, registering only instances of Tag 04TS, and why the final statement
here carries it. Its domain is the small étale topos of `X` itself: the fibre of
`AlgebraicGeometry.Space.SpacesEtale.smallEtaleSheafSystem` over the final object of the
spaces-étale site of `X` is `Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))` on the nose.

The base category is the spaces-étale site of `X`, whose morphisms are étale, and this is no
restriction on Tag 0GFS: the members of an étale covering of `X` are by definition algebraic
spaces with an *étale* morphism to `X`, hence are objects of that site, which is what
`AlgebraicGeometry.Space.etaleObject` records. The covering condition of Tag 041E is joint
surjectivity on points of the structure morphisms, which is exactly the hypothesis of the
descent statements above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe t u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS}

/-- The pseudofunctor on the spaces-étale site of `X` whose fibre over `U` is the category of
sheaves of sets on the spaces-étale site of `U`. It is the transport of
`CategoryTheory.GrothendieckTopology.pseudofunctorOver` along the site equivalences of
`AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall`. -/
noncomputable def spacesEtaleSheafSystem :
    Pseudofunctor (LocallyDiscrete (SpacesEtale B S hS X)ᵒᵖ) Cat :=
  Pseudofunctor.transport
    ((topology B S hS X).pseudofunctorOver (Type (u + 1)))
    (fun a => Cat.of (Sheaf (topology B S hS (unop a.as).obj.left) (Type (u + 1))))
    (fun a => sheafOverEquivSmall B S hS (unop a.as) (Type (u + 1)))

/-- **Effective descent for spaces-étale sheaves of the members.** For a family of objects of
the spaces-étale site of `X` whose structure morphisms are jointly surjective on points,
sheaves of sets on the slice at the final object are equivalent to descent data for the
family, the descent data being taken in the sheaf categories of the spaces-étale sites of the
members. -/
theorem isEquivalence_toDescentData_spacesEtaleSheafSystem {I : Type (u + 1)}
    (U : I → SpacesEtale B S hS X)
    (hsurj : (⋃ i, Set.range (pointsMap B S hS ((U i).obj.left).1 ((U i).obj.hom).hom))
      = Set.univ) :
    ((spacesEtaleSheafSystem B S hS (X := X)).toDescentData
      (fun i => toFinal B S hS (U i))).IsEquivalence :=
  (Pseudofunctor.isEquivalence_toDescentData_transport_iff _ _ _ _).mp
    (isEquivalence_toDescentData_spacesEtale B S hS U hsurj)

/-- The pseudofunctor on the spaces-étale site of `X` whose fibre over `U` is the category of
sheaves of sets on the *small étale* site of `U`. It is
`AlgebraicGeometry.Space.SpacesEtale.spacesEtaleSheafSystem` transported along the comparison
of topoi of Tag 03G1. -/
noncomputable def smallEtaleSheafSystem
    [∀ (U : SpacesEtale B S hS X) (Z : _),
      HasLimitsOfShape
        (StructuredArrow Z (Space.comparisonFunctor B S hS U.obj.left).op) (Type (u + 1))] :
    Pseudofunctor (LocallyDiscrete (SpacesEtale B S hS X)ᵒᵖ) Cat :=
  Pseudofunctor.transport (spacesEtaleSheafSystem B S hS (X := X))
    (fun a => Cat.of (Sheaf (SmallEtale.topology B S hS ((unop a.as).obj.left).1)
      (Type (u + 1))))
    (fun a => ((Space.comparisonFunctor B S hS (unop a.as).obj.left).sheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B S hS ((unop a.as).obj.left).1)
      (topology B S hS (unop a.as).obj.left)).asEquivalence)

/-- **Effective descent for small étale sheaves of the members.** For a family of objects of
the spaces-étale site of `X` whose structure morphisms are jointly surjective on points,
sheaves of sets on the slice at the final object are equivalent to descent data for the
family, the descent data being taken in the sheaf categories of the small étale sites of the
members. This is the content of Stacks 0GFS for an index type in `Type (u + 1)`; the attribute
is carried by `isEquivalence_toDescentData_smallEtaleSheafSystem_of_isEtaleCovering` below,
which has an arbitrary index type and reads the hypothesis as an étale covering. -/
theorem isEquivalence_toDescentData_smallEtaleSheafSystem
    [∀ (U : SpacesEtale B S hS X) (Z : _),
      HasLimitsOfShape
        (StructuredArrow Z (Space.comparisonFunctor B S hS U.obj.left).op) (Type (u + 1))]
    {I : Type (u + 1)} (U : I → SpacesEtale B S hS X)
    (hsurj : (⋃ i, Set.range (pointsMap B S hS ((U i).obj.left).1 ((U i).obj.hom).hom))
      = Set.univ) :
    ((smallEtaleSheafSystem B S hS (X := X)).toDescentData
      (fun i => toFinal B S hS (U i))).IsEquivalence :=
  (Pseudofunctor.isEquivalence_toDescentData_transport_iff _ _ _ _).mp
    (isEquivalence_toDescentData_spacesEtaleSheafSystem B S hS U hsurj)

/-! ### Families indexed by an arbitrary type, and étale coverings -/

/-- A family of objects of the spaces-étale site of `X` whose structure morphisms are jointly
surjective on points generates a covering sieve of the final object, for an index type in any
universe: choosing for every point of `X` an index whose member hits it gives a jointly
surjective subfamily indexed by the points of `X`, a type in `Type (u + 1)`, and the sieve it
generates is contained in the sieve of the whole family. -/
theorem ofArrows_toFinal_mem_topology_of_jointlySurjective {I : Type t}
    (U : I → SpacesEtale B S hS X)
    (hsurj : (⋃ i, Set.range (pointsMap B S hS ((U i).obj.left).1 ((U i).obj.hom).hom))
      = Set.univ) :
    Sieve.ofArrows U (fun i => toFinal B S hS (U i))
      ∈ topology B S hS X (final B S hS X) := by
  classical
  have h : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS ((U i).obj.left).1,
      pointsMap B S hS ((U i).obj.left).1 ((U i).obj.hom).hom y = x :=
    Set.iUnion_eq_univ_iff.1 hsurj
  choose σ y hy using h
  refine (topology B S hS X).superset_covering ?_
    (ofArrows_toFinal_mem_topology B S hS (fun x : points B S hS X.1 => U (σ x))
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, y x, hy x⟩))
  rw [Sieve.generate_le_iff]
  rintro W _ ⟨x⟩
  exact Sieve.ofArrows_mk _ _ (σ x)

/-- **Effective descent for small étale sheaves of the members, at an arbitrary index type.**
For a family of objects of the spaces-étale site of `X`, indexed by a type in any universe,
whose structure morphisms are jointly surjective on points, sheaves of sets on the small étale
site of `X` are equivalent to descent data for the family, the descent data being taken in the
sheaf categories of the small étale sites of the members. -/
theorem isEquivalence_toDescentData_smallEtaleSheafSystem_of_jointlySurjective
    [∀ (U : SpacesEtale B S hS X) (Z : _),
      HasLimitsOfShape
        (StructuredArrow Z (Space.comparisonFunctor B S hS U.obj.left).op) (Type (u + 1))]
    {I : Type t} (U : I → SpacesEtale B S hS X)
    (hsurj : (⋃ i, Set.range (pointsMap B S hS ((U i).obj.left).1 ((U i).obj.hom).hom))
      = Set.univ) :
    ((smallEtaleSheafSystem B S hS (X := X)).toDescentData
      (fun i => toFinal B S hS (U i))).IsEquivalence :=
  (Pseudofunctor.isEquivalence_toDescentData_transport_iff _ _ _ _).mp
    ((Pseudofunctor.isEquivalence_toDescentData_transport_iff _ _ _ _).mp
      (GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver
        (topology B S hS X) (Type (u + 1)) _
        (ofArrows_toFinal_mem_topology_of_jointlySurjective B S hS U hsurj)))

/-- **Stacks 0GFS.** Let `X` be an algebraic space over a scheme `S` and let
`{g i : Y i ⟶ X}` be an étale covering of algebraic spaces. Then sheaves of sets on the small
étale site of `X` are equivalent, via the functor taking a sheaf to its canonical descent
datum, to descent data for étale sheaves with respect to that covering: a sheaf on the small
étale site of each `Y i`, together with transition isomorphisms over the overlaps satisfying
the cocycle condition. -/
@[stacks 0GFS]
theorem isEquivalence_toDescentData_smallEtaleSheafSystem_of_isEtaleCovering
    [∀ (U : SpacesEtale B S hS X) (Z : _),
      HasLimitsOfShape
        (StructuredArrow Z (Space.comparisonFunctor B S hS U.obj.left).op) (Type (u + 1))]
    {I : Type t} (Y : I → AlgebraicSpaces B S hS) (g : ∀ i, Y i ⟶ X)
    (hg : IsEtaleCovering B S hS (fun i => (Y i).1) (fun i => (g i).hom)) :
    ((smallEtaleSheafSystem B S hS (X := X)).toDescentData
      (fun i => toFinal B S hS (etaleObject B S hS (g i) (hg.etale i)))).IsEquivalence :=
  isEquivalence_toDescentData_smallEtaleSheafSystem_of_jointlySurjective B S hS
    (fun i => etaleObject B S hS (g i) (hg.etale i)) hg.jointly_surjective

end AlgebraicGeometry.Space.SpacesEtale

end
