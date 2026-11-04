module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapFlatTargetSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The fibre of a map of quasi-coherent modules over a point of the affine base

In the situation of Stacks 0CWA — an affine base `S = Spec R`, an algebraic space `X` over `S`
and a map `u : F ⟶ G` of quasi-coherent `𝒪_X`-modules with `G` flat over `S` — the lemmas of
the section *Making a map zero* speak of the pullback `u_s` of `u` to the fibre `X_s` over a
point `s ∈ S`. This file supplies that vocabulary: the fibre, the projection from it, and the
proposition that the pulled-back map vanishes.

The fibre is the base change of `X` along `Spec κ(s) ⟶ S`, which is the base change of the
situation of Stacks 083F at the test scheme `Spec κ(s)`; so `u_s` is literally the
`AlgebraicGeometry.Space.ModuleMapSituation.baseChangeHom` of that situation at that test
scheme, taken for the pullback of modules `AlgebraicGeometry.Space.modulePullback` of Stacks
03LU. Nothing here is a chartwise approximation of the source's condition.

## Main definitions

* `AlgebraicGeometry.Space.specResidueFieldOver`: `Spec κ(s)` as an object of the big fppf site
  over the base.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreTest`: the same, read as a test
  scheme over the base for the situation of Stacks 083F.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.fibreSpace` and `.fibreProjection`: the
  fibre `X_s` and its projection to `X`.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.FibreMapEqZero`: the assertion
  `u_s = 0`.

## Main results

There are no results beyond the definitions; this file only supplies vocabulary.

## Implementation notes

`Spec κ(s)` belongs to the site by
`AlgebraicGeometry.BigFppfSite.residueField_spec_contains`, and the map to the base needed to
make it an object of the site over `S` is `AlgebraicGeometry.Scheme.fromSpecResidueField`
itself.

The target algebraic space of the situation of Stacks 083F attached to Stacks 0CWA is the final
algebraic space over `S`, so a test scheme over it carries no extra datum: its structure
morphism is the unique one, taken from
`AlgebraicGeometry.Space.terminalSpace_isTerminal`.

The pullback of modules used is the one of Stacks 03LU, assembled into a
`AlgebraicGeometry.Space.ModulePullbackSystem` by
`AlgebraicGeometry.Space.modulePullbackSystem`. It lives only at the module universe of the
structure rings, which is the universe at which Stacks 0CWA is stated, so there is no universe
mismatch to accommodate.

## References

* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `Spec κ(s)`, for a point `s` of the base, as an object of the big fppf site over the base;
its structure morphism is `AlgebraicGeometry.Scheme.fromSpecResidueField`. -/
def specResidueFieldOver (s : S) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (B.residueField_spec_contains hS s) (S.fromSpecResidueField s)

namespace ModuleMapFlatTargetSituation

variable [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS)

/-- `Spec κ(s)`, for a point `s` of the base, read as a test scheme over the target algebraic
space of the situation of Stacks 083F attached to the situation of Stacks 0CWA. That target is
the final algebraic space over the base, so the structure morphism is the unique one. -/
def fibreTest (s : S) : (D.toModuleMapSituation B S hS).SchemesOver :=
  CostructuredArrow.mk
    ((terminalSpace_isTerminal B S hS).from
      ((schemeSpaceFunctor B S hS).obj (specResidueFieldOver B S hS s)))

/-- The fibre `X_s` of the algebraic space of the situation over a point `s` of the base: the
base change of `X` along `Spec κ(s) ⟶ S`. -/
def fibreSpace (s : S) : AlgebraicSpaces B S hS :=
  (D.toModuleMapSituation B S hS).baseChangeSpace (D.fibreTest B S hS s)

/-- The projection `X_s ⟶ X` from the fibre over a point of the base. -/
def fibreProjection (s : S) : D.fibreSpace B S hS s ⟶ D.X :=
  (D.toModuleMapSituation B S hS).baseChangeProjection (D.fibreTest B S hS s)

/-- **`u_s = 0`.** The pullback of the map of modules of the situation to the fibre over a point
`s` of the base is the zero morphism. -/
def FibreMapEqZero (s : S) : Prop :=
  (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
    (D.fibreTest B S hS s)

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end
