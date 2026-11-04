module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleTorsionDerivedPushforwardUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DG3: proper base change for bounded below complexes on algebraic spaces

For a cartesian square of algebraic spaces with `f` proper and every bounded below complex `E` of
abelian sheaves on `Y_étale` with torsion cohomology sheaves, the base change map
`g⁻¹ R f_* E ⟶ R f'_* (g')⁻¹ E` is an isomorphism. The statement is
`AlgebraicGeometry.BigEtaleSpaceSite.isIso_spacesEtaleDerivedBaseChange_app_of_isProper`.
-/

add_to_stacks 0DG3 "proper base change for algebraic spaces: g⁻¹ R f_* E ≅ R f'_* (g')⁻¹ E for f \
  proper and E bounded below with torsion cohomology sheaves"
  AlgebraicGeometry.BigEtaleSpaceSite.isIso_spacesEtaleDerivedBaseChange_app_of_isProper
