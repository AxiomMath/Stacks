module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProduct

/-!
# The fibre of `ℓ × 𝐏(V)` over a closed point of the line, as a section

Over an algebraically closed field a closed point `λ` of the line `ℓ` is a `k`-point, that is a
morphism `Spec k ⟶ ℓ` splitting the structure morphism
(`AlgebraicGeometry.pointOfClosedPoint`). Base changing it along `𝐏(V) ⟶ Spec k` gives a section

`σ_λ : 𝐏(V) ⟶ ℓ ×_k 𝐏(V)`

of the second projection whose image is the fibre of the first projection over `λ`. A closed
subset of `ℓ ×_k 𝐏(V)` therefore has a well-defined *fibre over `λ`*, namely its preimage under
`σ_λ`, a closed subset of `𝐏(V)`; and this is the reading of the fibres `C'₀` and `C'_∞` in Tag
0B1T.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineSection`: the section `σ_λ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingFibre`: the fibre of a subset of `ℓ × 𝐏(V)`
  over a closed point of the line, that is its preimage under `σ_λ`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineSection_comp_ambPoint`: `σ_λ` is a section of
  the projection to `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.ambLine_lineSection`: it lands in the fibre over
  `λ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.injective_lineSection`: `σ_λ` is injective on
  points, the projection to `𝐏(V)` undoing it.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_movingFibre`: the fibre of a closed subset
  is closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_image_ambLine_of_movingFibre_nonempty`: a closed
  point of the line with nonempty fibre is in the image of the projection to the line.

## Implementation notes

The section is `CategoryTheory.Limits.pullback.lift` of the constant morphism to `λ` and the
identity, so the two equations `lineSection_comp_ambLine` and `lineSection_comp_ambPoint` hold by
`CategoryTheory.Limits.pullback.lift_fst` and `CategoryTheory.Limits.pullback.lift_snd`, and
injectivity on points follows from the second of them.

The fibre is taken as a preimage rather than as the set of points of `ℓ × 𝐏(V)` above `λ`: the
preimage is what the clauses of Tag 0B1T are stated with, is closed as soon as the subset is,
and needs no identification of the scheme-theoretic fibre with `𝐏(V)`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]

section AbstractLine

variable (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k V]
  [FiniteDimensional k W] [Nontrivial W] [Nontrivial V]

/-- **The fibre of `𝐏(W) ×_k 𝐏(V)` over a closed point `λ` of `𝐏(W)`, as a section of the
projection to `𝐏(V)`**: the base change along `𝐏(V) ⟶ Spec k` of the `k`-point of `𝐏(W)` that
`λ` is. -/
public def lineProductSection (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) :
    projectiveSpaceOfModule k V ⟶ lineProduct k V W :=
  pullback.lift
    (projectiveSpaceOfModuleToSpec k V ≫
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k W) lam hlam)
    (𝟙 _)
    (by rw [Category.assoc, pointOfClosedPoint_comp, Category.comp_id, Category.id_comp])

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The section composed with the projection to `𝐏(W)` is the constant morphism at `λ`. -/
@[reassoc (attr := simp)]
public theorem lineProductSection_comp_lineProductLine (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) :
    lineProductSection k V W lam hlam ≫ lineProductLine k V W =
      projectiveSpaceOfModuleToSpec k V ≫
        pointOfClosedPoint (projectiveSpaceOfModuleToSpec k W) lam hlam :=
  pullback.lift_fst _ _ _

omit [FiniteDimensional k V] [Nontrivial V] in
/-- **The section is a section of the projection to `𝐏(V)`.** -/
@[reassoc (attr := simp)]
public theorem lineProductSection_comp_lineProductPoint (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) :
    lineProductSection k V W lam hlam ≫ lineProductPoint k V W = 𝟙 _ :=
  pullback.lift_snd _ _ _

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The projection to `𝐏(V)` undoes the section on points. -/
public theorem lineProductPoint_lineProductSection (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) (y : projectiveSpaceOfModule k V) :
    (lineProductPoint k V W).base ((lineProductSection k V W lam hlam).base y) = y :=
  by rw [← Scheme.Hom.comp_apply, lineProductSection_comp_lineProductPoint]; rfl

omit [FiniteDimensional k V] [Nontrivial V] in
/-- **The section lands in the fibre over `λ`.** -/
public theorem lineProductLine_lineProductSection (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) (y : projectiveSpaceOfModule k V) :
    (lineProductLine k V W).base ((lineProductSection k V W lam hlam).base y) = lam := by
  rw [← Scheme.Hom.comp_apply, lineProductSection_comp_lineProductLine]
  simp

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The section is injective on points, the projection to `𝐏(V)` undoing it. -/
public theorem injective_lineProductSection (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) :
    Function.Injective (lineProductSection k V W lam hlam).base := fun y y' hyy => by
  rw [← lineProductPoint_lineProductSection k V W lam hlam y,
    ← lineProductPoint_lineProductSection k V W lam hlam y', hyy]

/-- **The fibre of a subset of `𝐏(W) × 𝐏(V)` over a closed point of `𝐏(W)`**: its preimage under
the section at that point, a subset of `𝐏(V)`. -/
public def lineProductFibre (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) (S : Set (lineProduct k V W)) :
    Set (projectiveSpaceOfModule k V) :=
  (lineProductSection k V W lam hlam).base ⁻¹' S

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The fibre of a closed subset is closed. -/
public theorem isClosed_lineProductFibre (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) {S : Set (lineProduct k V W)} (hS : IsClosed S) :
    IsClosed (lineProductFibre k V W lam hlam S) :=
  hS.preimage (lineProductSection k V W lam hlam).continuous

omit [FiniteDimensional k V] [Nontrivial V] in
/-- A point of `𝐏(V)` lies in the fibre of `S` over `λ` exactly when the corresponding point of
`𝐏(W) × 𝐏(V)` lies in `S`. -/
public theorem mem_lineProductFibre_iff (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) (S : Set (lineProduct k V W))
    (y : projectiveSpaceOfModule k V) :
    y ∈ lineProductFibre k V W lam hlam S ↔
      (lineProductSection k V W lam hlam).base y ∈ S := Iff.rfl

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The fibre of the whole ambient product is the whole of `𝐏(V)`. -/
public theorem lineProductFibre_univ (lam : projectiveSpaceOfModule k W)
    (hlam : IsClosed ({lam} : Set _)) :
    lineProductFibre k V W lam hlam Set.univ = Set.univ :=
  Set.preimage_univ

omit [FiniteDimensional k V] [Nontrivial V] in
/-- **A closed point of `𝐏(W)` with nonempty fibre lies in the image of the projection.** -/
public theorem mem_image_lineProductLine_of_lineProductFibre_nonempty
    (lam : projectiveSpaceOfModule k W) (hlam : IsClosed ({lam} : Set _))
    {S : Set (lineProduct k V W)} (h : (lineProductFibre k V W lam hlam S).Nonempty) :
    lam ∈ (lineProductLine k V W).base '' S := by
  obtain ⟨y, hy⟩ := h
  exact ⟨(lineProductSection k V W lam hlam).base y, hy,
    lineProductLine_lineProductSection k V W lam hlam y⟩

end AbstractLine

variable (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- **The fibre of `ℓ ×_k 𝐏(V)` over a closed point `λ` of the line, as a section of the
projection to `𝐏(V)`**: the section of
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineProductSection` at the corank-two quotient. -/
public def lineSection (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _)) :
    projectiveSpaceOfModule k V ⟶ movingAmbient k V L :=
  lineProductSection k V (lineSpace k V L) lam hlam

omit [Nontrivial V] in
/-- The section composed with the projection to the line is the constant morphism at `λ`. -/
@[reassoc (attr := simp)]
public theorem lineSection_comp_ambLine (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    lineSection k V L lam hlam ≫ ambLine k V L =
      projectiveSpaceOfModuleToSpec k V ≫
        pointOfClosedPoint (movingLineToSpec k V L) lam hlam :=
  lineProductSection_comp_lineProductLine k V (lineSpace k V L) lam hlam

omit [Nontrivial V] in
/-- **The section is a section of the projection to `𝐏(V)`.** -/
@[reassoc (attr := simp)]
public theorem lineSection_comp_ambPoint (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    lineSection k V L lam hlam ≫ ambPoint k V L = 𝟙 _ :=
  lineProductSection_comp_lineProductPoint k V (lineSpace k V L) lam hlam

omit [Nontrivial V] in
/-- The projection to `𝐏(V)` undoes the section on points. -/
public theorem ambPoint_lineSection (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) :
    (ambPoint k V L).base ((lineSection k V L lam hlam).base y) = y :=
  lineProductPoint_lineProductSection k V (lineSpace k V L) lam hlam y

omit [Nontrivial V] in
/-- **The section lands in the fibre over `λ`.** -/
public theorem ambLine_lineSection (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (y : projectiveSpaceOfModule k V) :
    (ambLine k V L).base ((lineSection k V L lam hlam).base y) = lam :=
  lineProductLine_lineProductSection k V (lineSpace k V L) lam hlam y

omit [Nontrivial V] in
/-- The section is injective on points, the projection to `𝐏(V)` undoing it. -/
public theorem injective_lineSection (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    Function.Injective (lineSection k V L lam hlam).base :=
  injective_lineProductSection k V (lineSpace k V L) lam hlam

/-- **The fibre of a subset of `ℓ × 𝐏(V)` over a closed point of the line**: its preimage under
the section at that point, a subset of `𝐏(V)`. -/
public def movingFibre (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (S : Set (movingAmbient k V L)) : Set (projectiveSpaceOfModule k V) :=
  lineProductFibre k V (lineSpace k V L) lam hlam S

omit [Nontrivial V] in
/-- The fibre of a closed subset is closed. -/
public theorem isClosed_movingFibre (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    {S : Set (movingAmbient k V L)} (hS : IsClosed S) :
    IsClosed (movingFibre k V L lam hlam S) :=
  isClosed_lineProductFibre k V (lineSpace k V L) lam hlam hS

omit [Nontrivial V] in
/-- A point of `𝐏(V)` lies in the fibre of `S` over `λ` exactly when the corresponding point of
`ℓ × 𝐏(V)` lies in `S`. -/
public theorem mem_movingFibre_iff (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (S : Set (movingAmbient k V L)) (y : projectiveSpaceOfModule k V) :
    y ∈ movingFibre k V L lam hlam S ↔ (lineSection k V L lam hlam).base y ∈ S := Iff.rfl

omit [Nontrivial V] in
/-- **A closed point of the line with nonempty fibre lies in the image of the projection.** -/
public theorem mem_image_ambLine_of_movingFibre_nonempty (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) {S : Set (movingAmbient k V L)}
    (h : (movingFibre k V L lam hlam S).Nonempty) :
    lam ∈ (ambLine k V L).base '' S :=
  mem_image_lineProductLine_of_lineProductFibre_nonempty k V (lineSpace k V L) lam hlam h

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
