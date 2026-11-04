module

public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula

/-!
# Dimension of a fibre at a point

For a morphism locally of finite type, the dimension of a scheme-theoretic fibre at a point is
the Krull dimension of the local ring of the fibre there plus the transcendence degree of the
residue field extension at that point.

This is the dimension formula for a scheme over a field
(`AlgebraicGeometry.topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk`), applied to the fibre
over `f x` viewed as a `κ(f x)`-scheme through `Scheme.Hom.fiberToSpecResidueField`, combined
with the identification of the residue field of the fibre at `f.asFiber x` with `κ(x)` given by
`AlgebraicGeometry.Scheme.Hom.trdeg_residueField_fiber`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg`: the
  dimension formula for a scheme-theoretic fibre at a point.

## Implementation notes

The point `x` in the fibre over `f x` is represented by `Scheme.Hom.asFiber`. The residue-field
extension is the canonical one induced by `Scheme.Hom.residueFieldMap`. Since transcendence
degree is cardinal-valued while both dimensions take values in `WithBot ℕ∞`, it is compared
through `Cardinal.toENat`.

## References

* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 02FX.** For a morphism locally of finite type, the dimension of the
fibre at a point is the dimension of the local ring of the fibre there plus the transcendence
degree of the residue-field extension. -/
@[stacks 02FX]
theorem topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) +
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
          WithBot ℕ∞) := by
  let k := S.residueField (f x)
  let g : f.fiber (f x) ⟶ Spec (.of k) := f.fiberToSpecResidueField (f x)
  let _ : LocallyOfFiniteType g := by
    show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  have h := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k (f.fiber (f x)) g (f.asFiber x)
  rw [f.trdeg_residueField_fiber x] at h
  rw [h, add_comm]

end AlgebraicGeometry

end
