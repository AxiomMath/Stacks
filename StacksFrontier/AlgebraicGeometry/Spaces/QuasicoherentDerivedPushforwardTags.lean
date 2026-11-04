module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image on `D_QCoh` of algebraic spaces, as Stacks tags

For a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, the derived
direct image `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with the right adjoints `DQ` of the
inclusions `D_QCoh ⊆ D`, when these exist (Stacks 0CR5), and with direct sums (Stacks 08FB);
it carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` (Stacks 08FA, part (1)). These are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction`,
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums` and
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage`; this file records the
tags.

## References

* [Stacks Project, Tag 0CR5](https://stacks.math.columbia.edu/tag/0CR5)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
-/

@[expose] public section

add_to_stacks 0CR5 AlgebraicGeometry.Space.quasicoherentDerivedPushforwardCompCoheratorIso

add_to_stacks 08FB AlgebraicGeometry.Space.preservesCoproducts_quasicoherentDerivedPushforward

add_to_stacks 08FA "part (1)" AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj

end
