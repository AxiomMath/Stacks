module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionLocalStructure
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.SepClosedComponents

/-!
# An irreducible component of a nodal curve is geometrically reduced, and has `h⁰ = 1`

Let `k` be a field and let `X` be a proper one-dimensional equidimensional `k`-curve with at worst
nodal singularities. Let `Z ⊆ X` be an irreducible component, taken with its *reduced* induced
closed subscheme structure, that is as `(Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Z))
.subscheme`. Then `Z` is again a curve of the same kind: reduced by construction, irreducible
hence equidimensional, of dimension one because every component of a one-dimensional
equidimensional curve is one-dimensional, and nodal by [Stacks, Tag 0E38] (1). So [Stacks,
Tag 0E37] applies to it and `Z` is geometrically reduced over `k`.

Over a *separably closed* `k` this computes the degree of `Z`: a proper geometrically reduced
scheme over a separably closed field has `dim_k Γ = #π₀` ([Stacks, Tag 0BUG]), and an irreducible
space has exactly one connected component.

## Main results

* `Stacks.Curves.geometricallyReduced_vanishingIdeal_component`: an irreducible component of such
  a curve, with its reduced induced structure, is geometrically reduced over `k`.
* `Stacks.Curves.finrank_structureSheafCohomology_zero_vanishingIdeal_component_eq_one`: over a
  separably closed field such a component has `h⁰(Z, 𝒪_Z) = 1`.

## Implementation notes

The component is an element of `irreducibleComponents X`, so it is a closed subset of `X`, and
`TopologicalSpace.Closeds.closure Z` is the same closed set repackaged as an element of
`TopologicalSpace.Closeds X`; `IsClosed.closure_eq` is what identifies the two. The reduced
induced structure then has `Z` as its underlying set
(`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_vanishingIdeal`) and is reduced
(`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`), which are the two
inputs [Stacks, Tag 0E38] (1) asks of a closed subcurve beyond its dimension.

The dimension of the subscheme is obtained from the dimension of `Z` as a subset of `X`
(`Stacks.Curves.topologicalKrullDim_irreducibleComponent_eq_one`) by transporting along the
homeomorphism of the subscheme with the range of its closed immersion, which is `Z`.

Properness of `X` is used twice: it supplies the `LocallyOfFiniteType` hypothesis of
[Stacks, Tag 0E37] and [Stacks, Tag 0E38], and it makes the component proper over `k` — a closed
immersion followed by a proper morphism — which is what [Stacks, Tag 0BUG] needs for the degree
computation. It is not needed for geometric reducedness beyond finite type.

## References

* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The reduced induced subscheme on an irreducible component has that component as its range. -/
private theorem range_subschemeι_vanishingIdeal_component {Z : Set X}
    (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    Set.range (vanishingIdeal (Closeds.closure Z)).subschemeι.base = Z := by
  simp [(isClosed_of_mem_irreducibleComponents Z hZ).closure_eq]

/-- The reduced induced subscheme on an irreducible component is an irreducible space. -/
private theorem irreducibleSpace_vanishingIdeal_component {Z : Set X}
    (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    IrreducibleSpace (vanishingIdeal (Closeds.closure Z)).subscheme :=
  irreducibleSpace_subscheme X _ (by rw [range_subschemeι_vanishingIdeal_component hZ]; exact hZ.1)

/-- **An irreducible component of a proper one-dimensional equidimensional nodal curve over a
field, taken with its reduced induced closed subscheme structure, is geometrically reduced over
that field.**

The component is reduced by construction and irreducible, hence equidimensional, and it is
one-dimensional because every irreducible component of a one-dimensional equidimensional curve
is. So it is itself a nodal curve by [Stacks, Tag 0E38] (1), and a one-dimensional
equidimensional nodal curve over a field is geometrically reduced by [Stacks, Tag 0E37]. -/
theorem geometricallyReduced_vanishingIdeal_component [IsProper (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    {Z : Set X} (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    GeometricallyReduced ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫
      (X ↘ Spec (.of k))) := by
  set I : X.IdealSheafData := vanishingIdeal (Closeds.closure Z) with hI
  have hrange : Set.range I.subschemeι.base = Z := range_subschemeι_vanishingIdeal_component hZ
  let : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ (X ↘ Spec (.of k))⟩
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ (X ↘ Spec (.of k))))
  have : IrreducibleSpace I.subscheme := irreducibleSpace_vanishingIdeal_component hZ
  have hIeq : Equidimensional I.subscheme := .of_preirreducibleSpace I.subscheme
  have hIdim : topologicalKrullDim I.subscheme = 1 := by
    have hemb : Topology.IsEmbedding I.subschemeι.base := IsPreimmersion.isEmbedding I.subschemeι
    have e : I.subscheme ≃ₜ Z := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
    rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
    exact topologicalKrullDim_irreducibleComponent_eq_one (X ↘ Spec (.of k)) hX_equidimensional
      hX_dimension Z hZ
  have hInodal : HasAtWorstNodalSingularities k I.subscheme :=
    hasAtWorstNodalSingularities_subscheme hX_equidimensional hX_dimension hX_nodal I hIeq hIdim
  exact geometricallyReduced_of_hasAtWorstNodalSingularities k I.subscheme hIeq hIdim hInodal

/-- **Over a separably closed field, an irreducible component of a proper one-dimensional
equidimensional nodal curve, taken with its reduced induced closed subscheme structure, has
`h⁰(Z, 𝒪_Z) = 1`.**

The component is proper over `k` and geometrically reduced
(`Stacks.Curves.geometricallyReduced_vanishingIdeal_component`), so `h⁰` counts its connected
components by [Stacks, Tag 0BUG]; the component is irreducible, hence connected and nonempty, so
there is exactly one. -/
theorem finrank_structureSheafCohomology_zero_vanishingIdeal_component_eq_one [IsSepClosed k]
    [IsProper (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    {Z : Set X} (hZ : Z ∈ irreducibleComponents (X : Type u)) :
    Module.finrank k (structureSheafCohomology ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫
      (X ↘ Spec (.of k))) 0) = 1 := by
  set I : X.IdealSheafData := vanishingIdeal (Closeds.closure Z) with hI
  have hrange : Set.range I.subschemeι.base = Z := range_subschemeι_vanishingIdeal_component hZ
  have : IrreducibleSpace I.subscheme := irreducibleSpace_vanishingIdeal_component hZ
  have : GeometricallyReduced (I.subschemeι ≫ (X ↘ Spec (.of k))) :=
    geometricallyReduced_vanishingIdeal_component hX_equidimensional hX_dimension hX_nodal hZ
  have : IsProper (I.subschemeι ≫ (X ↘ Spec (.of k))) := inferInstance
  open Stacks.AlgebraicGeometry.ProperSectionsGeom in
  rw [finrank_structureSheafCohomology_zero_eq_card_connectedComponents k
    (I.subschemeι ≫ (X ↘ Spec (.of k)))]
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

end Stacks.Curves

end
