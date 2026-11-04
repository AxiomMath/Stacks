module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardUnitLaws

/-!
# Pseudofunctoriality of the direct image of modules on the small étale site

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the direct
image `f_*` of `𝒪`-modules on the small étale sites together with the comparison
`f_* ∘ g_* ≅ (f ≫ g)_*`.  Pseudofunctoriality of that assignment is
`AlgebraicGeometry.Space.ModulePushforwardCoherence`, and
`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` reduces it to the single datum of an
isomorphism `(𝟙 X)_* ≅ 𝟭`, which is `AlgebraicGeometry.Space.modulePushforwardIdIso`.  So the
structure is inhabited with no hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardCoherence`: the pseudofunctoriality data of the
  direct image of `𝒪`-modules along a morphism of algebraic spaces, with no hypothesis.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Pseudofunctoriality of the direct image of `𝒪`-modules of Stacks 03LU, with no
hypothesis.**  The identity datum is
`AlgebraicGeometry.Space.modulePushforwardIdIso`, and
`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` supplies the associativity coherence
and the two unit laws from it. -/
@[stacks 03LU "the pseudofunctoriality of the direct image, assembled: the identity \
comparison together with the associativity and the two unit laws of the composition \
comparison, as one datum with no hypothesis"]
noncomputable def modulePushforwardCoherence : ModulePushforwardCoherence B S hS :=
  modulePushforwardCoherenceOfIdIso B S hS fun X ↦ modulePushforwardIdIso B S hS X

end AlgebraicGeometry.Space

end
