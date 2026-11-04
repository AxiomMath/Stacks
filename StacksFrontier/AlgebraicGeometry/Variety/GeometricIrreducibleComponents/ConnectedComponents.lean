module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Irreducible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# Geometrically irreducible components give geometrically connected components

Any topological space with finitely many irreducible components has finitely many connected
components, because every point lies in an irreducible component and an irreducible set is
connected. If the space is a scheme over a field and its irreducible components are
geometrically irreducible, then each connected component is geometrically connected: it contains
an irreducible component, which is geometrically connected and maps into it over the base field.

## Main results

* `TopologicalSpace.finite_connectedComponents_of_finite_irreducibleComponents` gives finiteness
  of the connected components.
* `AlgebraicGeometry.geometricallyConnected_connectedComponent` gives each connected component
  its open subscheme structure and geometric connectedness.

## Implementation notes

Finiteness of connected components is stated for arbitrary topological spaces. For the geometric
assertion, an irreducible component is endowed with its reduced induced closed subscheme
structure, defined by its vanishing ideal. A connected component is represented by its open
subscheme; its underlying subset is the fibre of the connected-components quotient map.

## References

* [Stacks Project, Tag 054S](https://stacks.math.columbia.edu/tag/054S)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace

/-- Every point lies in an irreducible component contained in its connected component. -/
private theorem exists_mem_irreducibleComponents_subset_connectedComponent
    {X : Type*} [TopologicalSpace X] (x : X) :
    ∃ Z ∈ irreducibleComponents X, Z ⊆ connectedComponent x := by
  obtain ⟨Z, hZ, hxZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible ({x} : Set X) isIrreducible_singleton
  exact ⟨Z, hZ, hZ.1.isConnected.subset_connectedComponent (hxZ (by simp))⟩

/-- **Stacks Project, Tag 054S.** Finitely many irreducible components imply finitely many
connected components. -/
@[stacks 054S "finiteness of connected components"]
public theorem finite_connectedComponents_of_finite_irreducibleComponents
    {X : Type*} [TopologicalSpace X] (hX : (irreducibleComponents X).Finite) :
    Finite (ConnectedComponents X) := by
  let f : ↥(irreducibleComponents X) → ConnectedComponents X := fun Z =>
    ConnectedComponents.mk (Classical.choose Z.2.1.nonempty)
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨Z, hZ, hZc⟩ := exists_mem_irreducibleComponents_subset_connectedComponent x
    exact ⟨⟨Z, hZ⟩, ConnectedComponents.coe_eq_coe'.2 (hZc (Classical.choose_spec hZ.1.nonempty))⟩
  have := hX.to_subtype
  exact Finite.of_surjective f hf

end TopologicalSpace

namespace AlgebraicGeometry

/-- A geometrically irreducible morphism is geometrically connected. -/
theorem geometricallyConnected_of_geometricallyIrreducible
    {T Y : Scheme} (g : T ⟶ Y) [GeometricallyIrreducible g] :
    GeometricallyConnected g :=
  ⟨fun _ _ y Z fst snd h ↦ @IrreducibleSpace.connectedSpace Z _
    ((inferInstance : GeometricallyIrreducible g).geometrically_irreducibleSpace y fst snd h)⟩

/-- **A geometrically irreducible morphism is geometrically connected**: every base change of it
to a field is irreducible, hence connected. -/
alias GeometricallyIrreducible.geometricallyConnected := geometricallyConnected_of_geometricallyIrreducible

/-- **Stacks Project, Tag 054S.** If each of the finitely many irreducible components of a
scheme over a field is geometrically irreducible, each connected component has an open
subscheme structure that is geometrically connected over that field. -/
@[stacks 054S "geometric connectedness of connected components", ega "IV 4.5.13.1" "(ii)"]
public theorem geometricallyConnected_connectedComponent
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (hX : (irreducibleComponents X).Finite)
    (hgeom : ∀ Z : irreducibleComponents X,
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal (X := X)
            ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫ f))
    (c : ConnectedComponents X) :
    ∃ U : X.Opens,
      (U : Set X) = (ConnectedComponents.mk : X → ConnectedComponents X) ⁻¹' {c} ∧
        GeometricallyConnected (U.ι ≫ f) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have : Finite (ConnectedComponents X) :=
    TopologicalSpace.finite_connectedComponents_of_finite_irreducibleComponents hX
  let U : X.Opens := ⟨connectedComponent x,
    (TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents x).2⟩
  have hU : (U : Set X) = (ConnectedComponents.mk : X → ConnectedComponents X) ⁻¹'
      {ConnectedComponents.mk x} := by
    simpa [U] using (connectedComponents_preimage_singleton (x := x)).symm
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp (by
    simpa [U] using (isConnected_connectedComponent (x := x)))
  obtain ⟨Z, hZ, hZc⟩ := exists_mem_irreducibleComponents_subset_connectedComponent x
  let T : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  have hrange : Set.range T.subschemeι ⊆ Set.range U.ι := by
    rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.Opens.range_ι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let g : T.subscheme ⟶ U := IsOpenImmersion.lift U.ι T.subschemeι hrange
  have hfac : g ≫ U.ι = T.subschemeι := IsOpenImmersion.lift_fac ..
  have : GeometricallyIrreducible (T.subschemeι ≫ f) := hgeom ⟨Z, hZ⟩
  have : GeometricallyConnected (g ≫ U.ι ≫ f) := by
    rw [← Category.assoc, hfac]
    exact geometricallyConnected_of_geometricallyIrreducible _
  exact ⟨U, by simp [hU], geometricallyConnected_of_comp_of_connectedSpace k g (U.ι ≫ f)⟩

end AlgebraicGeometry
