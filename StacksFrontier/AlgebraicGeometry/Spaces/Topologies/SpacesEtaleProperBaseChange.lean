module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforwardUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DG2: the proper base change theorem for algebraic spaces

For a cartesian square of algebraic spaces with `f` proper and every abelian torsion sheaf `F` on
`Y_étale`, the base change map `g⁻¹ R f_* F ⟶ R f'_* (g')⁻¹ F` is an isomorphism. The statement
is `isIso_spacesEtaleDerivedBaseChange_app_singleFunctor_of_isProper`, in the namespace
`AlgebraicGeometry.BigEtaleSpaceSite`.
-/

add_to_stacks 0DG2 "proper base change for algebraic spaces: g⁻¹ R f_* F ≅ R f'_* (g')⁻¹ F for f \
  proper and F an abelian torsion sheaf"
AlgebraicGeometry.BigEtaleSpaceSite.isIso_spacesEtaleDerivedBaseChange_app_singleFunctor_of_isProper
