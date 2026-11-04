module

public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat with smooth fibres implies smooth

[Stacks, Tag 01V8]: a morphism of schemes `f : X ⟶ S` which is flat, locally of finite
presentation and has smooth fibres `X_s` is smooth. Mathlib proves exactly this statement as
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`, the fibre `X_s` being
`f.fiber s` over `Spec κ(s)` with structure morphism `f.fiberToSpecResidueField s`; it is
registered here at the tag.

## References

* [Stacks Project, Tag 01V8](https://stacks.math.columbia.edu/tag/01V8)
-/

add_to_stacks 01V8 AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "1 II 2.1" "sufficiency, global form"
  AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "1 II 2.2" "sufficiency with Y=S"
  AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "3 VIB 3.10" "partial" AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "3 VIB 4.4" "more general" AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "3 VIB 8.4" "(ii)" AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "3 VIII 2.1" "partial" AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "3 XI 1.2" "(i)" AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_sga "3 XV 1.1" "partial" AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_ega "IV 17.5.1" "b)⇒a), global form"
  AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
add_to_ega "IV 17.8.2" "special case" AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField
