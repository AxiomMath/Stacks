module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyClosedPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyGraph
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySection

/-!
# The family `C'` of the Moving Lemma, as a closed subset of `ℓ × 𝐏(V)`

Tag 0B1T takes for `C'` the image of `ℓ × C` under the family of projective transformations. The
graph of that family inside `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` is
`AlgebraicGeometry.ProjectiveSpaceOfModule.movingGraph`, a closed subset, and the projection
forgetting the source point is proper, so the image of the part of the graph lying over `C` is a
closed subset of `ℓ ×_k 𝐏(V)`. That image is `C'`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingFamilySet`: the family `C'` as a subset of
  `ℓ ×_k 𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_movingFamilySet`: `C'` is closed, the
  projection forgetting the source point being proper.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_movingFamilySet_iff`: a point of `ℓ × 𝐏(V)`
  lies on `C'` exactly when it is the image of a point of the graph whose source point lies in
  `C`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_movingFibre_movingFamilySet_iff`: the same, read
  on the fibre over a closed point of the line.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.closure_image_ambLine_movingFamilySet`: **clause (1)
  of Tag 0B1T**, that `C'` is dominant over the line, granted that its fibre over every closed
  point of the line is nonempty.

## Implementation notes

`C'` is a *subset*, carrying the reduced induced structure of the project's convention for a
closed subvariety (`TopologicalSpace.IrreducibleCloseds`, as in
`StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs`); irreducibility and the
identification of its fibres are established separately, from the characterisation of the closed
points of the graph.

The image is taken of the intersection of the graph with the preimage of `C` under the projection
to the *source* point, so no product `ℓ ×_k C` is formed: the preimage of a closed subset is
closed, which is all the properness argument needs.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- **The family `C'` of Tag 0B1T**: the image in `ℓ ×_k 𝐏(V)` of the part of the graph of the
family of projective transformations whose source point lies in `C`. -/
public def movingFamilySet {ι : Type*} [Fintype ι] (b : Module.Basis ι k (lineSpace k V L))
    (C : Set (projectiveSpaceOfModule k V)) : Set (movingAmbient k V L) :=
  (prAmbient k V L).base ''
    (movingGraph k V L b ∩ (prSource k V L).base ⁻¹' C)

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- A point of `ℓ × 𝐏(V)` lies on `C'` exactly when it is the image of a point of the graph whose
source point lies in `C`. -/
public theorem mem_movingFamilySet_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (C : Set (projectiveSpaceOfModule k V))
    (z : movingAmbient k V L) :
    z ∈ movingFamilySet k V L b C ↔
      ∃ t : movingProd k V L, t ∈ movingGraph k V L b ∧
        (prSource k V L).base t ∈ C ∧ (prAmbient k V L).base t = z := by
  constructor
  · rintro ⟨t, ⟨ht, htC⟩, rfl⟩
    exact ⟨t, ht, htC, rfl⟩
  · rintro ⟨t, ht, htC, rfl⟩
    exact ⟨t, ⟨ht, htC⟩, rfl⟩

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] in
/-- **`C'` is closed.** The graph is closed, the preimage of a closed `C` is closed, and the
projection forgetting the source point is proper, hence a closed map. -/
public theorem isClosed_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) :
    IsClosed (movingFamilySet k V L b C) :=
  isClosed_image_prAmbient k V L
    ((isClosed_movingGraph k V L b).inter (hC.preimage (prSource k V L).continuous))

omit [Nontrivial V] in
/-- The fibre of `C'` over a closed point of the line, read through the section at that point. -/
public theorem mem_movingFibre_movingFamilySet_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (C : Set (projectiveSpaceOfModule k V))
    (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) :
    y ∈ movingFibre k V L lam hlam (movingFamilySet k V L b C) ↔
      ∃ t : movingProd k V L, t ∈ movingGraph k V L b ∧
        (prSource k V L).base t ∈ C ∧
        (prAmbient k V L).base t = (lineSection k V L lam hlam).base y := by
  rw [mem_movingFibre_iff, mem_movingFamilySet_iff]

omit [IsAlgClosed k] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- `C'` lies in the image of the projection to the line, so every point of it has a line
coordinate. -/
public theorem ambLine_image_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (C : Set (projectiveSpaceOfModule k V)) :
    (ambLine k V L).base '' movingFamilySet k V L b C =
      (prLine k V L).base '' (movingGraph k V L b ∩ (prSource k V L).base ⁻¹' C) := by
  rw [movingFamilySet, ← Set.image_comp]
  rfl

omit [Nontrivial V] in
/-- **Clause (1) of Tag 0B1T: the family is dominant over the line.** If the fibre of `C'` over
every closed point of the line is nonempty then the image of `C'` in the line is dense, the
closed points of the line being dense in it. -/
public theorem closure_image_ambLine_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) (C : Set (projectiveSpaceOfModule k V))
    (h : ∀ (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _)),
      (movingFibre k V L lam hlam (movingFamilySet k V L b C)).Nonempty) :
    closure ((ambLine k V L).base '' movingFamilySet k V L b C) = Set.univ :=
  closure_eq_univ_of_closedPoints_subset fun lam hlam =>
    mem_image_ambLine_of_movingFibre_nonempty k V L lam (mem_closedPoints_iff.mp hlam)
      (h lam (mem_closedPoints_iff.mp hlam))

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
