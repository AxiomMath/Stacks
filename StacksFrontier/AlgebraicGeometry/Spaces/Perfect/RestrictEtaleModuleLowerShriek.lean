module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of the extension by zero along an étale morphism of algebraic spaces

Let `j : U ⟶ X` and `j_V : V ⟶ X` be étale morphisms of algebraic spaces over a scheme `S`
contained in a big fppf site `B`, let `W = V ×_X U` and let `j_W : W ⟶ V` and `p : W ⟶ U` be the
two projections. For the extension by zero `AlgebraicGeometry.Space.etaleModuleLowerShriek`, the
canonical base-change map

`j_{W!}(E|_W) ⟶ (j_!E)|_V`

is an isomorphism, for a sheaf of `𝒪_U`-modules and for an object `E` of the unbounded derived
category `D(𝒪_U)`; that is, `(j_!E)|_V = j_{W!}(E|_W)` (Stacks 08HA).

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `restrictEtaleModuleLowerShriekIso` is the isomorphism `j_{W!}(-|_W) ≅ (j_!-)|_V` of functors on
  sheaves of `𝒪_U`-modules.
* `derivedRestrictEtaleModuleLowerShriekMap` is the base-change map on unbounded derived
  categories, and `derivedRestrictEtaleModuleLowerShriekIso` the resulting isomorphism of functors
  on `D(𝒪_U)`.

## Main results

* `isIso_restrictEtaleModuleLowerShriekMap`: **Stacks 08HA on modules**.
* `isIso_derivedRestrictEtaleModuleLowerShriekMap`: **Stacks 08HA**.

## Implementation notes

Both `j_!` and `j_{W!}` are `etaleModuleLowerShriek`, the left adjoint of restriction of modules
along an étale morphism, with its adjunction `etaleModuleLowerShriekAdjunction`; it is exact
(Stacks 03DJ, `preservesFiniteLimits_etaleModuleLowerShriek` together with the preservation of
finite colimits by a left adjoint), so it induces a functor on derived categories. The base-change
map of sheaves of modules is `restrictExtensionByZeroMap` evaluated at those two adjunctions; it is
the conjugate of the cartesian comparison of direct images of Stacks 03LX around the square, and
its invertibility is `isIso_restrictExtensionByZeroMap`.

On derived categories the statement is made for an arbitrary choice of derived category of each of
the four categories of modules, `[HasDerivedCategory _]`. The derived base-change map is the map of
sheaves of modules lifted through the localizations, read through the identification
`CategoryTheory.Functor.mapDerivedCategoryComp` of the derived functor of a composite of exact
functors with the composite of their derived functors.

## References

* [Stacks Project, Tag 08HA](https://stacks.math.columbia.edu/tag/08HA)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ w₄ u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {U X V W : AlgebraicSpaces B S hS} {j : U ⟶ X} {jV : V ⟶ X} {jW : W ⟶ V} {p : W ⟶ U}
  (sq : IsPullback jW p jV j) (hj : IsEtale B S hS j.hom) (hjV : IsEtale B S hS jV.hom)

/-- **Stacks 08HA**, on sheaves of modules. Let `j : U ⟶ X` and `j_V : V ⟶ X` be étale morphisms of
algebraic spaces, let `W = V ×_X U` with projections `j_W : W ⟶ V` and `p : W ⟶ U`, and let `F` be
a sheaf of `𝒪_U`-modules. Then the canonical map `j_{W!}(F|_W) ⟶ (j_!F)|_V` is an isomorphism, that
is, `(j_!F)|_V = j_{W!}(F|_W)`, where `j_!` and `j_{W!}` are the extensions by zero
`AlgebraicGeometry.Space.etaleModuleLowerShriek`. -/
@[stacks 08HA "on modules, for the constructed extension by zero"]
theorem isIso_restrictEtaleModuleLowerShriekMap :
    IsIso (restrictExtensionByZeroMap B S hS sq hj hjV
      (etaleModuleLowerShriekAdjunction B S hS j hj)
      (etaleModuleLowerShriekAdjunction B S hS jW
        (isEtale_of_isPullback B S hS p jW j jV sq.flip hj))) :=
  isIso_restrictExtensionByZeroMap B S hS sq hj hjV _ _

/-- The isomorphism `j_{W!}(-|_W) ≅ (j_!-)|_V` of functors on sheaves of `𝒪_U`-modules of
Stacks 08HA, for the extensions by zero `AlgebraicGeometry.Space.etaleModuleLowerShriek`: the
canonical base-change map, which is invertible by
`AlgebraicGeometry.Space.isIso_restrictEtaleModuleLowerShriekMap`. -/
noncomputable def restrictEtaleModuleLowerShriekIso :
    etaleModulePullback.{u, u} B S hS p (isEtale_of_isPullback B S hS jW p jV j sq hjV) ⋙
        etaleModuleLowerShriek B S hS jW (isEtale_of_isPullback B S hS p jW j jV sq.flip hj) ≅
      etaleModuleLowerShriek B S hS j hj ⋙ etaleModulePullback.{u, u} B S hS jV hjV :=
  have := isIso_restrictEtaleModuleLowerShriekMap B S hS sq hj hjV
  asIso (restrictExtensionByZeroMap B S hS sq hj hjV
    (etaleModuleLowerShriekAdjunction B S hS j hj)
    (etaleModuleLowerShriekAdjunction B S hS jW
      (isEtale_of_isPullback B S hS p jW j jV sq.flip hj)))

section Derived

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable [HasDerivedCategory.{w₁} (Modules.{u, u} B S hS U.1 U.2)]
  [HasDerivedCategory.{w₂} (Modules.{u, u} B S hS X.1 X.2)]
  [HasDerivedCategory.{w₃} (Modules.{u, u} B S hS V.1 V.2)]
  [HasDerivedCategory.{w₄} (Modules.{u, u} B S hS W.1 W.2)]

/-- The canonical base-change map `j_{W!}(E|_W) ⟶ (j_!E)|_V` on unbounded derived categories of
modules, for the extensions by zero `AlgebraicGeometry.Space.etaleModuleLowerShriek` and any choice
of the four derived categories: the map of sheaves of modules lifted through the localizations
defining the derived categories, read through the identification of the derived functor of a
composite with the composite of the derived functors. -/
noncomputable def derivedRestrictEtaleModuleLowerShriekMap :
    (etaleModulePullback.{u, u} B S hS p
            (isEtale_of_isPullback B S hS jW p jV j sq hjV)).mapDerivedCategory ⋙
          (etaleModuleLowerShriek B S hS jW
            (isEtale_of_isPullback B S hS p jW j jV sq.flip hj)).mapDerivedCategory ⟶
      (etaleModuleLowerShriek B S hS j hj).mapDerivedCategory ⋙
        (etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory :=
  (Functor.mapDerivedCategoryComp _ _).inv ≫
    NatTrans.mapDerivedCategory (restrictExtensionByZeroMap B S hS sq hj hjV
      (etaleModuleLowerShriekAdjunction B S hS j hj)
      (etaleModuleLowerShriekAdjunction B S hS jW
        (isEtale_of_isPullback B S hS p jW j jV sq.flip hj))) ≫
      (Functor.mapDerivedCategoryComp _ _).hom

/-- **Stacks 08HA.** Let `j : U ⟶ X` and `j_V : V ⟶ X` be étale morphisms of algebraic spaces, let
`W = V ×_X U` with projections `j_W : W ⟶ V` and `p : W ⟶ U`, and let `E` be an object of the
unbounded derived category of `𝒪_U`-modules. Then the canonical map `j_{W!}(E|_W) ⟶ (j_!E)|_V` is
an isomorphism, that is, `(j_!E)|_V = j_{W!}(E|_W)`, where `j_!` and `j_{W!}` are the derived
functors of the exact extensions by zero `AlgebraicGeometry.Space.etaleModuleLowerShriek`. -/
@[stacks 08HA "for the constructed extension by zero, on any model of the derived categories"]
theorem isIso_derivedRestrictEtaleModuleLowerShriekMap :
    IsIso (derivedRestrictEtaleModuleLowerShriekMap B S hS sq hj hjV) := by
  have := isIso_restrictEtaleModuleLowerShriekMap B S hS sq hj hjV
  unfold derivedRestrictEtaleModuleLowerShriekMap
  infer_instance

/-- The isomorphism `j_{W!}(-|_W) ≅ (j_!-)|_V` of functors on unbounded derived categories of
Stacks 08HA, for the derived extensions by zero of
`AlgebraicGeometry.Space.etaleModuleLowerShriek`: the canonical base-change map, which is
invertible by `AlgebraicGeometry.Space.isIso_derivedRestrictEtaleModuleLowerShriekMap`. -/
noncomputable def derivedRestrictEtaleModuleLowerShriekIso :
    (etaleModulePullback.{u, u} B S hS p
            (isEtale_of_isPullback B S hS jW p jV j sq hjV)).mapDerivedCategory ⋙
          (etaleModuleLowerShriek B S hS jW
            (isEtale_of_isPullback B S hS p jW j jV sq.flip hj)).mapDerivedCategory ≅
      (etaleModuleLowerShriek B S hS j hj).mapDerivedCategory ⋙
        (etaleModulePullback.{u, u} B S hS jV hjV).mapDerivedCategory :=
  have := isIso_derivedRestrictEtaleModuleLowerShriekMap B S hS sq hj hjV
  asIso (derivedRestrictEtaleModuleLowerShriekMap B S hS sq hj hjV)

end Derived

end AlgebraicGeometry.Space

end
