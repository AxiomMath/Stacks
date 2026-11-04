module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyConstant
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySection

/-!
# The section at a closed point of the line is a homeomorphism onto the fibre

The section `σ_λ : 𝐏(V) ⟶ ℓ ×_k 𝐏(V)` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySection` is the base change
along `𝐏(V) ⟶ Spec k` of the `k`-point `τ_λ : Spec k ⟶ ℓ` that a closed point `λ` of the line is.
That square being cartesian, the image of `σ_λ` is exactly the fibre
`(ℓ ×_k 𝐏(V) ⟶ ℓ)⁻¹(λ)`: the image of a projection of a fibre product of schemes is the preimage
of the image of the opposite leg (`AlgebraicGeometry.range_pullback_fst_base`), and the image of
`τ_λ` is the single point `λ`.

Since the other projection `ℓ ×_k 𝐏(V) ⟶ 𝐏(V)` is a continuous left inverse of `σ_λ`, this makes
`σ_λ` a homeomorphism of `𝐏(V)` onto that fibre. So the fibre `σ_λ⁻¹(S)` of a subset `S` of
`ℓ × 𝐏(V)`, which is how Tag 0B1T reads the fibres `C'₀` and `C'_∞`, is homeomorphic to the
honest slice `S ∩ (ℓ ×_k 𝐏(V) ⟶ ℓ)⁻¹(λ)` and in particular has the same dimension.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.fibreHomeomorph`: the homeomorphism of `𝐏(V)` onto
  the fibre of the projection to the line over `λ`, given by `σ_λ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingFibreHomeomorph`: its restriction, a
  homeomorphism of `σ_λ⁻¹(S)` onto `S ∩ (ℓ ×_k 𝐏(V) ⟶ ℓ)⁻¹(λ)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_lineSection`: the section is the base
  change of the `k`-point `λ` along the structure morphism of `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_lineSection`: its image is the fibre of the
  projection to the line over `λ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isHomeomorph_lineSection`: it is a homeomorphism
  onto that fibre.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.image_movingFibre`: the fibre of `S` over `λ`, read
  back in `ℓ × 𝐏(V)`, is the slice of `S` over `λ`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_movingFibre`: the fibre of `S`
  over `λ` has the dimension of that slice.

## Implementation notes

The cartesian square is obtained by pasting rather than by a computation: the square with
horizontal maps `σ_λ` and `ℓ ×_k 𝐏(V) ⟶ 𝐏(V)` and vertical maps the two projections to the line
has horizontal composites the identities — of `𝐏(V)` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineSection_comp_ambPoint` and of `Spec k` by
`AlgebraicGeometry.pointOfClosedPoint_comp` — so the composite square is cartesian, the right
square is the defining one of the fibre product, and `CategoryTheory.IsPullback.of_right` peels
it off.

The key point-set consequence, extracted as
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineSection_ambPoint_of_ambLine_eq`, is that `σ_λ`
undoes the projection to `𝐏(V)` *on the fibre over `λ`*; it is what makes both restrictions of
`σ_λ` below bijective, the global statement `σ_λ ∘ pr = id` being false.

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

/-- **The section at a closed point of the line is the base change of that point.** The square
with top the section `σ_λ`, left the structure morphism of `𝐏(V)`, right the projection to the
line and bottom the `k`-point `τ_λ` of the line is cartesian. -/
public theorem isPullback_lineSection (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    IsPullback (lineSection k V L lam hlam) (projectiveSpaceOfModuleToSpec k V)
      (ambLine k V L) (pointOfClosedPoint (movingLineToSpec k V L) lam hlam) := by
  have hbig : IsPullback (lineSection k V L lam hlam ≫ ambPoint k V L)
      (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)
      (pointOfClosedPoint (movingLineToSpec k V L) lam hlam ≫ movingLineToSpec k V L) := by
    rw [lineSection_comp_ambPoint, pointOfClosedPoint_comp]
    exact IsPullback.of_id_fst
  exact IsPullback.of_right (h₁₂ := ambPoint k V L) hbig
    (lineSection_comp_ambLine k V L lam hlam)
    (IsPullback.of_hasPullback (movingLineToSpec k V L)
      (projectiveSpaceOfModuleToSpec k V)).flip

omit [Nontrivial V] in
/-- The image of the `k`-point of the line at a closed point `λ` is the singleton `{λ}`: every
point of `Spec k` is sent to `λ`, and `Spec k` is nonempty. -/
public theorem range_pointOfClosedPoint_movingLine (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    Set.range (pointOfClosedPoint (movingLineToSpec k V L) lam hlam).base =
      ({lam} : Set (movingLine k V L)) := by
  have : Nonempty ↥(Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
  exact Set.range_eq_singleton fun a =>
    pointOfClosedPoint_apply (movingLineToSpec k V L) lam hlam a

/-- **The image of the section at `λ` is the fibre of the projection to the line over `λ`.** -/
public theorem range_lineSection (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _)) :
    Set.range (lineSection k V L lam hlam).base = (ambLine k V L).base ⁻¹' {lam} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ambLine_lineSection k V L lam hlam y
  · intro hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (pullback.fst (ambLine k V L)
        (pointOfClosedPoint (movingLineToSpec k V L) lam hlam)).base := by
      rwa [range_pullback_fst_base, range_pointOfClosedPoint_movingLine]
    exact ⟨_, (congrArg (fun m : pullback (ambLine k V L)
      (pointOfClosedPoint (movingLineToSpec k V L) lam hlam) ⟶ movingAmbient k V L =>
        m.base z) (isPullback_lineSection k V L lam hlam).isoPullback_inv_fst).trans hz⟩

/-- **The section at `λ` undoes the projection to `𝐏(V)` on the fibre over `λ`.** The composite
`σ_λ ∘ pr` is not the identity of `ℓ × 𝐏(V)`, but it is on the points above `λ`, those being
exactly the image of `σ_λ`. -/
public theorem lineSection_ambPoint_of_ambLine_eq (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) {x : movingAmbient k V L}
    (hx : (ambLine k V L).base x = lam) :
    (lineSection k V L lam hlam).base ((ambPoint k V L).base x) = x := by
  obtain ⟨y, rfl⟩ : x ∈ Set.range (lineSection k V L lam hlam).base := by
    rwa [range_lineSection]
  rw [ambPoint_lineSection]

/-- **The section at `λ` as a homeomorphism of `𝐏(V)` onto the fibre of the projection to the
line over `λ`**, the projection to `𝐏(V)` being its inverse. -/
public def fibreHomeomorph (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _)) :
    projectiveSpaceOfModule k V ≃ₜ ↥((ambLine k V L).base ⁻¹' {lam}) where
  toFun y := ⟨(lineSection k V L lam hlam).base y, ambLine_lineSection k V L lam hlam y⟩
  invFun z := (ambPoint k V L).base z.1
  left_inv y := ambPoint_lineSection k V L lam hlam y
  right_inv z := Subtype.ext (lineSection_ambPoint_of_ambLine_eq k V L lam hlam z.2)
  continuous_toFun := (lineSection k V L lam hlam).continuous.subtype_mk _
  continuous_invFun := (ambPoint k V L).continuous.comp continuous_subtype_val

/-- **The section at `λ` is a homeomorphism onto the fibre over `λ`.** -/
public theorem isHomeomorph_lineSection (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    IsHomeomorph (fun y : projectiveSpaceOfModule k V =>
      (⟨(lineSection k V L lam hlam).base y, ambLine_lineSection k V L lam hlam y⟩ :
        ↥((ambLine k V L).base ⁻¹' {lam}))) :=
  (fibreHomeomorph k V L lam hlam).isHomeomorph

/-- **The fibre of `S` over `λ`, read back in `ℓ × 𝐏(V)`, is the slice of `S` over `λ`.** -/
public theorem image_movingFibre (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (S : Set (movingAmbient k V L)) :
    (lineSection k V L lam hlam).base '' movingFibre k V L lam hlam S =
      S ∩ (ambLine k V L).base ⁻¹' {lam} := by
  have h : movingFibre k V L lam hlam S = (lineSection k V L lam hlam).base ⁻¹' S := rfl
  rw [h, Set.image_preimage_eq_inter_range, range_lineSection]

/-- The projection to `𝐏(V)` carries the slice of `S` over `λ` into the fibre of `S` over `λ`,
the section at `λ` undoing it there. -/
public theorem ambPoint_mem_movingFibre (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) {S : Set (movingAmbient k V L)}
    {x : movingAmbient k V L} (hx : x ∈ S ∩ (ambLine k V L).base ⁻¹' {lam}) :
    (ambPoint k V L).base x ∈ movingFibre k V L lam hlam S := by
  rw [mem_movingFibre_iff, lineSection_ambPoint_of_ambLine_eq k V L lam hlam hx.2]
  exact hx.1

/-- **The fibre of `S` over `λ` is homeomorphic to the slice of `S` over `λ`**, by the
restriction of the section at `λ`. -/
public def movingFibreHomeomorph (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set _))
    (S : Set (movingAmbient k V L)) :
    ↥(movingFibre k V L lam hlam S) ≃ₜ ↥(S ∩ (ambLine k V L).base ⁻¹' {lam}) where
  toFun y := ⟨(lineSection k V L lam hlam).base y.1,
    y.2, ambLine_lineSection k V L lam hlam y.1⟩
  invFun z := ⟨(ambPoint k V L).base z.1, ambPoint_mem_movingFibre k V L lam hlam z.2⟩
  left_inv y := Subtype.ext (ambPoint_lineSection k V L lam hlam y.1)
  right_inv z := Subtype.ext (lineSection_ambPoint_of_ambLine_eq k V L lam hlam z.2.2)
  continuous_toFun :=
    ((lineSection k V L lam hlam).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((ambPoint k V L).continuous.comp continuous_subtype_val).subtype_mk _

/-- **The fibre of `S` over `λ` has the dimension of the slice of `S` over `λ`.** -/
public theorem topologicalKrullDim_movingFibre (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) (S : Set (movingAmbient k V L)) :
    topologicalKrullDim ↥(movingFibre k V L lam hlam S) =
      topologicalKrullDim ↥(S ∩ (ambLine k V L).base ⁻¹' {lam}) :=
  IsHomeomorph.topologicalKrullDim_eq _ (movingFibreHomeomorph k V L lam hlam S).isHomeomorph

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
