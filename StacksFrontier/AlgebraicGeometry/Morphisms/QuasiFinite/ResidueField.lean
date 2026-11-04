module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed points of a fibre and residue field extensions

Whether a point is closed in its scheme-theoretic fibre is a property of the residue field
extension it induces. Algebraicity of that extension already forces the point to be closed in
its fibre, and closedness in the fibre then propagates to closedness in the source whenever the
image point is closed in the target. For a morphism locally of finite type the implication
reverses and sharpens: a point is closed in its fibre exactly when its residue field is *finite*
over the residue field of its image.

## Main results

* `AlgebraicGeometry.isClosed_asFiber_of_isAlgebraic_residueField`: a point with an algebraic
  residue field extension is closed in its fibre.
* `AlgebraicGeometry.isClosed_of_isAlgebraic_residueField`: such a point is closed in the source
  when its image is closed in the target.
* `AlgebraicGeometry.isClosed_asFiber_iff_finite_residueField`: for a morphism locally of finite
  type, closedness in the fibre is equivalent to finiteness of the residue field extension.

## Implementation notes

The point of the scheme-theoretic fibre determined by `x` is `Scheme.Hom.asFiber x`. In every
statement the algebra structure on `κ(x)` is the canonical one induced by
`Scheme.Hom.residueFieldMap`, supplied by a `letI` inside the statement so that the hypothesis
and the conclusion speak about the same instance.

Algebraicity gives closedness because the induced map from the spectrum of `κ(x)` into the fibre
is integral, hence closed, on each affine chart; finiteness in the converse direction comes from
the fibre being Jacobson, where a finite-type algebra over a field with a closed point is
finite.

## References

* [Stacks Project, Tag 01TE](https://stacks.math.columbia.edu/tag/01TE)
* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A point whose residue field is algebraic over that of its image is closed in its fibre. -/
@[stacks 01TE "part (1)"]
public theorem isClosed_asFiber_of_isAlgebraic_residueField (f : X ⟶ S) (x : X)
    (h : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x)) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  let _ := (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x) := h
  let Z := f.fiber (f x)
  let y : Z := f.asFiber x
  rw [(show TopologicalSpace.IsOpenCover (fun U : Z.affineOpens ↦ U.1) from
    iSup_affineOpens_eq_top Z).isClosed_iff_coe_preimage]
  intro U
  by_cases hy : y ∈ U.1
  · let l : Spec (X.residueField x) ⟶ U.1.toScheme :=
      IsOpenImmersion.lift U.1.ι (f.asFiberHom x) (by
        rintro _ ⟨z, rfl⟩
        exact ⟨⟨y, hy⟩, (f.asFiberHom_apply x z).symm⟩)
    have : IsIntegralHom (l ≫ U.1.ι ≫ f.fiberToSpecResidueField (f x)) := by
      show IsIntegralHom ((l ≫ U.1.ι) ≫ f.fiberToSpecResidueField (f x))
      rw [show l ≫ U.1.ι = f.asFiberHom x from IsOpenImmersion.lift_fac _ _ _,
        f.asFiberHom_fiberToSpecResidueField]
      exact IsIntegralHom.SpecMap_iff.mpr (Algebra.isIntegral_def.mp inferInstance)
    have : IsIntegralHom l :=
      IsIntegralHom.of_comp l (U.1.ι ≫ f.fiberToSpecResidueField (f x))
    have hl : l default = (⟨y, hy⟩ : U.1) :=
      Subtype.ext ((congrArg (fun q : Spec (X.residueField x) ⟶ Z ↦ q default)
        (IsOpenImmersion.lift_fac U.1.ι (f.asFiberHom x) _)).trans (f.asFiberHom_apply x default))
    rw [show Subtype.val ⁻¹' ({y} : Set Z) = ({⟨y, hy⟩} : Set U.1) by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩]
    rw [← hl, ← Set.range_unique]
    exact l.isClosedMap.isClosed_range
  · rw [show Subtype.val ⁻¹' ({y} : Set Z) = (∅ : Set U.1) by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hz => hy (hz ▸ z.property), False.elim⟩]
    exact isClosed_empty

/-- If the image of a point is closed and its residue field extension is algebraic, then the
point is closed. -/
@[stacks 01TE "part (2)", ega "I 6.4.2" "sufficiency"]
public theorem isClosed_of_isAlgebraic_residueField (f : X ⟶ S) (x : X)
    (h : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x))
    (hs : IsClosed ({f x} : Set S)) : IsClosed ({x} : Set X) := by
  simpa [Set.image_image] using
    (hs.preimage f.continuous).isClosedEmbedding_subtypeVal.isClosedMap _
      ((f.fiberHomeo (f x)).isClosed_image.mpr
        (isClosed_asFiber_of_isAlgebraic_residueField f x h))

/-- A point of a fibre of a locally finite type morphism is closed exactly when its residue
field is finite over the residue field of its image. -/
@[stacks 01TF]
public theorem isClosed_asFiber_iff_finite_residueField (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) ↔
      letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (S.residueField (f x)) (X.residueField x) := by
  refine ⟨fun hclosed ↦ ?_, fun _ ↦ isClosed_asFiber_of_isAlgebraic_residueField f x
    (by infer_instance)⟩
  have : IsClosedImmersion (f.asFiberHom x) :=
    IsClosedImmersion.of_isPreimmersion _
      (by simpa only [Scheme.Hom.range_asFiberHom] using hclosed)
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  have : RingHom.FiniteType (f.residueFieldMap x).hom :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp (by
      rw [← Scheme.Hom.asFiberHom_fiberToSpecResidueField]; infer_instance)
  algebraize [(f.residueFieldMap x).hom]
  exact finite_of_finite_type_of_isJacobsonRing _ _

end AlgebraicGeometry
