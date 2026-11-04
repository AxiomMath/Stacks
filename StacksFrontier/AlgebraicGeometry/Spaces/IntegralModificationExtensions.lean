module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralModification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalDenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.BirationalDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Additions to `IntegralModification`

Declarations this development adds alongside
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralModification`, kept in their own module so that the
base file is unchanged: 1 declaration(s) that the base file does not have, with the section
variables, namespaces and options they are stated in.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A modification of an integral algebraic space is an alteration (Stacks 0ADA): source and
target are integral, the morphism is proper, it is dominant because it is birational, and by
Stacks 0AD9 it is an isomorphism — hence a finite morphism — over a nonempty open subspace of
its target. This is the reduction of case (1) of Stacks 0AYJ to case (2). -/
theorem IsIntegralModification.isAlteration {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hX' : IsAlgebraicSpace B S hS X'} {hX : IsAlgebraicSpace B S hS X}
    {hXint : IsIntegralSpace B S hS X} {f : X' ⟶ X}
    (hf : IsIntegralModification B S hS hX' hX hXint f) :
    IsAlteration B S hS f := by
  have hX'int : IsIntegralSpace B S hS X' := hf.isIntegralSpace B S hS
  obtain ⟨U, hU, hUne, hiso⟩ := hf.exists_isIso_fromPreimage B S hS
  exact ⟨hX, hXint, hX', hX'int, hf.isProper B S hS,
    isDominant_of_isBirational B S hS hX' hX hX'int.isDecentSpace hXint.isDecentSpace
      (hX'int.finite_irreducibleComponents B S hS X')
      (hXint.finite_irreducibleComponents B S hS X) (hf.isBirational B S hS),
    U, hU, hUne, isFinite_of_isIso B S hS (U.fromPreimage f)⟩

end AlgebraicGeometry.Space

end
