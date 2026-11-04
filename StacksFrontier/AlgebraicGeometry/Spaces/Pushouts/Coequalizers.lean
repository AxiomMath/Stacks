module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# A proper modification of an algebraic space away from a closed subspace

The coequalizer construction that glues an algebraic space back together from a proper
modification starts from the following data: a locally Noetherian algebraic space `X` over a
scheme `S`, a closed immersion `i : Z ⟶ X`, the complementary open subspace `U` of `X`, and a
proper morphism `f : X' ⟶ X` which restricts to an isomorphism over `U`. This module records
that data as one structure.

## Main definitions

* `AlgebraicGeometry.Space.CoequalizerGlueSituation`: the proper-modification situation, with
  the closed subspace, its complementary open subspace and the proper morphism.

## Implementation notes

The closed part is given as an algebraic space `Z` together with a closed immersion into `X`,
while the complementary open part is a subfunctor `U` of `X`; complementarity is the equality of
the two corresponding subsets of the space of points, so no quotient or ideal-sheaf datum is
needed. "Isomorphism over `U`" is invertibility of `pullback.snd f U.ι`, the base change of `f`
along the inclusion of `U`. Local Noetherianity is
`AlgebraicGeometry.Space.HasEtaleLocalProperty` for `AlgebraicGeometry.IsLocallyNoetherian`,
that is, the existence of a surjective étale atlas by a locally Noetherian scheme.

## References

* [Stacks Project, Tag 0AGH](https://stacks.math.columbia.edu/tag/0AGH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0AGH.** The standing situation for the coequalizer construction: a locally
Noetherian algebraic space `X` over `S`, a closed immersion `i : Z ⟶ X` with complementary open
subspace `U`, and a proper morphism `f : X' ⟶ X` which is an isomorphism over `U`. -/
@[stacks 0AGH]
structure CoequalizerGlueSituation where
  /-- The ambient big fppf site. -/
  B : BigFppfSite.{u}
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The base scheme belongs to the site. -/
  hS : B.Contains S
  /-- The target algebraic space. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `X` is an algebraic space. -/
  hX : IsAlgebraicSpace B S hS X
  /-- `X` is locally Noetherian. -/
  locallyNoetherian :
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)
  /-- The closed algebraic subspace. -/
  Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `Z` is an algebraic space. -/
  hZ : IsAlgebraicSpace B S hS Z
  /-- The closed immersion. -/
  i : Z ⟶ X
  /-- The immersion `Z ⟶ X` is closed. -/
  hi : IsClosedImmersion B S hS i
  /-- The complementary open subspace. -/
  U : Subfunctor X
  /-- `U` is an open algebraic subspace. -/
  hU : IsOpenSubspace B S hS U
  /-- On points, `U` is exactly the complement of `Z`. -/
  U_compl_Z : Set.range (pointsMap B S hS U.toFunctor U.ι) =
    (Set.range (pointsMap B S hS Z i))ᶜ
  /-- The space from which the proper morphism starts. -/
  X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `X'` is an algebraic space. -/
  hX' : IsAlgebraicSpace B S hS X'
  /-- The modification map. -/
  f : X' ⟶ X
  /-- The map `X' ⟶ X` is proper. -/
  hf : IsProper B S hS f
  /-- Over the complementary open, `f` is an isomorphism. -/
  f_iso_over_U : IsIso (pullback.snd f U.ι)

end AlgebraicGeometry.Space

end
