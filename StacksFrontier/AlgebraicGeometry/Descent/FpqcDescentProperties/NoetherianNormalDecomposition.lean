module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct

/-!
# A connected Noetherian normal scheme is irreducible

A connected Noetherian normal scheme is irreducible.

## Main results

* `AlgebraicGeometry.irreducibleSpace_of_isNormal_of_connectedSpace`: a connected Noetherian
  normal scheme is irreducible.

## Implementation notes

The decomposition of a normal Noetherian scheme into a finite disjoint union of normal integral
schemes is `AlgebraicGeometry.isNormal_iff_exists_iso_finite_coproduct_integral_normal`, in
`StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct`, where the tag it realises is carried.

For the irreducibility corollary the coproduct is connected, so exactly one summand occurs and
the coproduct is homeomorphic to that single integral piece.

## References

* [Stacks Project, Tag 033M](https://stacks.math.columbia.edu/tag/033M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A connected coproduct of a family of nonempty irreducible schemes is irreducible: only one
summand can occur. -/
public theorem irreducibleSpace_coproduct_of_connectedSpace {ι : Type u} (Y : ι → Scheme.{u})
    [∀ i, IsIntegral (Y i)] [ConnectedSpace (∐ Y : Scheme.{u})] :
    IrreducibleSpace (∐ Y : Scheme.{u}) := by
  let : ConnectedSpace (Σ i, Y i) := (sigmaMk Y).connectedSpace_iff.mpr inferInstance
  obtain ⟨i, t, -, heq⟩ := Sigma.isConnected_iff.mp
    (isConnected_univ : IsConnected (Set.univ : Set (Σ i, Y i)))
  have hi : ∀ j : ι, j = i := fun j ↦ by
    obtain ⟨y, -, hxy⟩ : (⟨j, Nonempty.some inferInstance⟩ : Σ i, Y i) ∈ Sigma.mk i '' t :=
      heq ▸ Set.mem_univ _
    exact congrArg Sigma.fst hxy.symm
  have hrange : Set.range (fun x : Y i ↦ (⟨i, x⟩ : Σ j, Y j)) = Set.univ := by
    ext ⟨j, x⟩
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    cases hi j
    exact ⟨x, rfl⟩
  have hsig : IrreducibleSpace (Σ i, Y i) :=
    (irreducibleSpace_def _).mpr (by
      simpa [hrange] using (IrreducibleSpace.isIrreducible_univ (Y i)).image
        (fun x : Y i ↦ (⟨i, x⟩ : Σ j, Y j)) (continuous_sigmaMk (i := i)).continuousOn)
  exact (sigmaMk Y).irreducibleSpace_iff.mp hsig

/-- A connected Noetherian normal scheme is irreducible: by Tag 033M it is a finite disjoint
union of integral schemes, and connectedness leaves only one of them. -/
public theorem irreducibleSpace_of_isNormal_of_connectedSpace (X : Scheme.{u}) [IsNoetherian X]
    [ConnectedSpace X] (hX : IsNormal X) : IrreducibleSpace X := by
  obtain ⟨ι, -, Y, -, hintegralY, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal X).mp hX
  let : ∀ i, IsIntegral (Y i) := hintegralY
  let : ConnectedSpace (∐ Y : Scheme.{u}) := e.hom.homeomorph.connectedSpace_iff.mp inferInstance
  let : IrreducibleSpace (∐ Y : Scheme.{u}) := irreducibleSpace_coproduct_of_connectedSpace Y
  exact e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

end AlgebraicGeometry

end
