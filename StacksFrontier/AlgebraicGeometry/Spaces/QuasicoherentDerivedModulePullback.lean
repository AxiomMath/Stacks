module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackQuasicoherent
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback of algebraic spaces preserves `D_QCoh`

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`.  **Stacks 08F4** asserts that
the derived pullback `Lf^*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`.  This file states it, for the
derived pullback `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, together with the
restricted functor `Lf^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedModulePullback`: the restricted functor of
  **Stacks 08F4**
  (`AlgebraicGeometry.Space.derivedQuasicoherent_smallEtaleDerivedModulePullback`), and
  `AlgebraicGeometry.Space.quasicoherentDerivedModulePullbackCompιIso` its compatibility with the
  inclusions.

## References

* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

section General

open Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {B S hS}

/-- **Stacks 08F4, as a functor.**  The derived pullback along a morphism `f : Y ⟶ X` of
algebraic spaces restricts to a functor `Lf^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. -/
noncomputable def quasicoherentDerivedModulePullback (f : Y ⟶ X) :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ smallEtaleDerivedModulePullback B S hS f)
    fun K => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f K.obj K.property

/-- The restriction of `Lf^*` to the quasi-coherent derived categories is compatible with their
inclusions into the unbounded derived categories. -/
noncomputable def quasicoherentDerivedModulePullbackCompιIso (f : Y ⟶ X) :
    quasicoherentDerivedModulePullback f ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ smallEtaleDerivedModulePullback B S hS f :=
  ObjectProperty.liftCompιIso _ _ _

end General

end AlgebraicGeometry.Space

end
