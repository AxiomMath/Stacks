module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Localization
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of sheaves of sets on the small pro-étale site

A weakly étale morphism `j : U ⟶ X` induces restriction from sheaves of sets on the small
pro-étale site of `X` to those on the small pro-étale site of `U`. This restriction has a
left adjoint, extension by zero.

## Main definitions

* `AlgebraicGeometry.ProEtale.Sets.proetaleRestriction` is restriction of sheaves of sets
  along the postcomposition functor of small pro-étale sites.
* `AlgebraicGeometry.ProEtale.Sets.extensionByZero` is the left adjoint of restriction.

## Main results

* `AlgebraicGeometry.ProEtale.Sets.extensionByZeroAdjunction` is the defining adjunction.

## Implementation notes

Restriction is precomposition with the canonical postcomposition functor
`AlgebraicGeometry.ProEtale.proetalePostcompose`, not with an arbitrary equivalent functor.
Extension by zero is sheafification of left Kan extension along its opposite. Its adjunction
is stated explicitly so downstream fully-faithfulness results can use the unit and counit
directly. The coefficient universe may be any universe containing the site.

## References

* [Stacks Project, Tag 09AE](https://stacks.math.columbia.edu/tag/09AE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ProEtale.Sets

/-- Restriction of sheaves of sets along a weakly étale morphism. -/
abbrev proetaleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)) := by
  letI := proetalePostcompose_isContinuous j
  exact (proetalePostcompose j).sheafPushforwardContinuous (Type (max (u + 1) v))
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- Extension by zero of sheaves of sets along a weakly étale morphism. -/
@[implicit_reducible, stacks 09AE "extension_by_zero_sets"]
def extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    Sheaf (Scheme.ProEt.topology U) (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)) := by
  letI := proetalePostcompose_isContinuous j
  exact Functor.sheafPullbackConstruction.sheafPullback
    (proetalePostcompose j) (Type (max (u + 1) v))
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- Extension by zero is left adjoint to restriction. -/
@[stacks 09AE "extension_by_zero_sets"]
def extensionByZeroAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    extensionByZero.{u, v} j ⊣ proetaleRestriction.{u, v} j := by
  letI := proetalePostcompose_isContinuous j
  exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proetalePostcompose j) (Type (max (u + 1) v))
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

end AlgebraicGeometry.ProEtale.Sets

end
