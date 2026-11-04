module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension

/-!
# The reduced closed subscheme on a closed subset, and its dimension

A closed subset `S` of a scheme `X` carries the reduced induced closed subscheme
`(Scheme.IdealSheafData.vanishingIdeal ⟨S, hS⟩).subscheme`, whose inclusion is a closed immersion
with image `S`. This file records the two facts a dimension count needs: the image is `S`, and the
dimension of the subscheme is the dimension of `S` as a subspace. Both are immediate from the
inclusion being a closed embedding, and are stated for an arbitrary scheme so that they serve both
`𝐏(V)` and the products of the Moving Lemma.

## Main results

* `AlgebraicGeometry.range_vanishingIdeal_subschemeι`: the image of the inclusion is `S`.
* `AlgebraicGeometry.irreducibleSpace_vanishingIdeal_subscheme`: for irreducible `S` the
  subscheme is irreducible.
* `AlgebraicGeometry.topologicalKrullDim_vanishingIdeal_subscheme`: its dimension is that of `S`.
* `AlgebraicGeometry.locallyOfFiniteType_vanishingIdeal_subschemeι_comp`: it is of finite type
  over whatever base the ambient scheme is of finite type over.

## Implementation notes

`AlgebraicGeometry.ProjectiveSpaceOfModule.closedSubschemeOf` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus` is this construction
named for the special case `X = 𝐏(V)`; these lemmas are stated for an arbitrary `X` because the
Moving Lemma needs them for the product `ℓ ×_k 𝐏(V)` as well, and no second definition is
introduced — the subscheme is always written out as the subscheme of the vanishing ideal.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (S : Set X) (hS : IsClosed S)

/-- **The image of the inclusion of the reduced closed subscheme on `S` is `S`.** -/
public theorem range_vanishingIdeal_subschemeι :
    Set.range (Scheme.IdealSheafData.vanishingIdeal (⟨S, hS⟩ : Closeds X)).subschemeι.base = S :=
  ((Scheme.IdealSheafData.vanishingIdeal (⟨S, hS⟩ : Closeds X)).range_subschemeι).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- The reduced closed subscheme on `S` is homeomorphic to `S`, via its closed immersion. -/
private def vanishingIdealSubschemeHomeomorph :
    (Scheme.IdealSheafData.vanishingIdeal (⟨S, hS⟩ : Closeds X)).subscheme ≃ₜ S :=
  ((Scheme.IdealSheafData.vanishingIdeal
    (⟨S, hS⟩ : Closeds X)).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr (range_vanishingIdeal_subschemeι S hS))

/-- **The reduced closed subscheme on an irreducible closed subset is irreducible**, being
homeomorphic to the subset along its closed immersion. -/
public theorem irreducibleSpace_vanishingIdeal_subscheme (hSirr : IsIrreducible S) :
    IrreducibleSpace
      (Scheme.IdealSheafData.vanishingIdeal (⟨S, hS⟩ : Closeds X)).subscheme :=
  (vanishingIdealSubschemeHomeomorph S hS).irreducibleSpace_iff.mpr
    (Subtype.irreducibleSpace hSirr)

/-- **The dimension of the reduced closed subscheme on `S` is the dimension of `S`.** -/
public theorem topologicalKrullDim_vanishingIdeal_subscheme :
    topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (⟨S, hS⟩ : Closeds X)).subscheme =
      topologicalKrullDim S :=
  IsHomeomorph.topologicalKrullDim_eq _ (vanishingIdealSubschemeHomeomorph S hS).isHomeomorph

/-- The reduced closed subscheme on `S` is of finite type over any base the ambient scheme is of
finite type over. -/
public instance locallyOfFiniteType_vanishingIdeal_subschemeι_comp {Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal (⟨S, hS⟩ : Closeds X)).subschemeι ≫ f) :=
  inferInstance

end AlgebraicGeometry

end
