module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullbackAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullbackColimit

/-!
# Stacks registrations of the colimit formula for the pro-étale inverse image

The formula `ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i)` of Stacks 099S, for `Y = lim Y_i` a cofiltered limit of
quasi-compact and quasi-separated objects of `X_proétale` with affine transition morphisms, is
proved in `Spaces/ProetaleEtaleSheafPullbackColimit` (sheaves of sets, and the final form with
stages in `X_étale`) and `Spaces/ProetaleEtaleSheafPullbackAbelian` (abelian sheaves). This
module registers those declarations with the tag.
-/

@[expose] public section

add_to_stacks 099S "the displayed formula ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i); `Y = lim Y_i` is the limit of \
  the underlying schemes, as in the source"
  AlgebraicGeometry.Scheme.proetaleInverseImageIsColimit

add_to_stacks 099S "the final statement ε⁻¹ℱ(Y) = colim ℱ(Y_i) for stages Y_i in X_étale, the maps \
  being the unit ℱ ⟶ ε_*ε⁻¹ℱ followed by restriction"
  AlgebraicGeometry.Scheme.proetaleInverseImageIsColimitOfEtale

add_to_stacks 099S "the displayed formula for abelian sheaves, for an arbitrary left adjoint ε⁻¹ \
  of ε_*; `Y = lim Y_i` is the limit of the underlying schemes"
  AlgebraicGeometry.Scheme.proetaleInverseImageIsColimitAddCommGrp

end
