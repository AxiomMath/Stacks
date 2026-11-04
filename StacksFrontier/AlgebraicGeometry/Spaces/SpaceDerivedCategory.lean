module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage

/-!
# The derived category of `𝒪_X`-modules on an algebraic space, at the standard model

For an algebraic space `X` over a scheme `S` of a big fppf site `B`, this module names the
unbounded derived category `D(𝒪_X)` of the `𝒪_X`-modules on the small étale site of `X`, at the
module universe `u` of the structure rings, **at the standard model**
`CategoryTheory.HasDerivedCategory.standard` (morphisms in `Type (u + 1)`), together with its
localization, cohomology and single-degree functors and the subcategory `D_QCoh(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.spaceHasDerivedCategory X`: the standard model, as a term.
* `AlgebraicGeometry.Space.spaceDerivedCategory X`: `D(𝒪_X)` at that model.
* `AlgebraicGeometry.Space.spaceDerivedQ`, `…spaceDerivedHomology`, `…spaceDerivedSingle`: the
  localization functor, the cohomology functors and the single-degree functors at that model.
* `AlgebraicGeometry.Space.spaceQuasicoherentProp X`: `D_QCoh(𝒪_X)` as a property of the objects
  of `spaceDerivedCategory X`, with its triangulated structure
  `AlgebraicGeometry.Space.isTriangulated_spaceQuasicoherentProp`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The standard model of the derived category of the `𝒪_X`-modules of an algebraic space, as a
term (no instance is declared). -/
abbrev spaceHasDerivedCategory (X : AlgebraicSpaces B S hS) :
    @HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS X.1 X.2) _
      (modulesAbelianSmallEtale B S hS X.1 X.2) :=
  @HasDerivedCategory.standard _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)

/-- `D(𝒪_X)`: the unbounded derived category of `𝒪_X`-modules on the small étale site of an
algebraic space, at the standard model. -/
abbrev spaceDerivedCategory (X : AlgebraicSpaces B S hS) :=
  @DerivedCategory (Modules.{u, u} B S hS X.1 X.2) _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X)

/-- The localization functor `C(𝒪_X) ⥤ D(𝒪_X)` at the standard model. -/
abbrev spaceDerivedQ (X : AlgebraicSpaces B S hS) :
    CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ ⥤ spaceDerivedCategory B S hS X :=
  @DerivedCategory.Q _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X)

/-- The cohomology sheaf functor `Hⁿ : D(𝒪_X) ⥤ Mod(𝒪_X)` at the standard model. -/
abbrev spaceDerivedHomology (X : AlgebraicSpaces B S hS) (n : ℤ) :
    spaceDerivedCategory B S hS X ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  @DerivedCategory.homologyFunctor _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X) n

/-- The functor `Mod(𝒪_X) ⥤ D(𝒪_X)` placing a module in degree `n`, at the standard model. -/
abbrev spaceDerivedSingle (X : AlgebraicSpaces B S hS) (n : ℤ) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ spaceDerivedCategory B S hS X :=
  @DerivedCategory.singleFunctor _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X) n

/-- `D_QCoh(𝒪_X)`, as a property of the objects of `spaceDerivedCategory X`: every cohomology sheaf
is quasi-coherent (Stacks 071X). -/
abbrev spaceQuasicoherentProp (X : AlgebraicSpaces B S hS) :
    ObjectProperty (spaceDerivedCategory B S hS X) :=
  @DerivedCategoryB.derivedCategoryB _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-! ### The triangulated structure of `spaceDerivedCategory` -/

/-- The shift functors of `D(𝒪_X)` are additive. -/
instance additive_shiftFunctor_spaceDerivedCategory (X : AlgebraicSpaces B S hS) (n : ℤ) :
    (shiftFunctor (spaceDerivedCategory B S hS X) n).Additive :=
  @DerivedCategory.instAdditiveShiftFunctorInt _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X) n

/-- `D(𝒪_X)` is pretriangulated. -/
instance pretriangulated_spaceDerivedCategory (X : AlgebraicSpaces B S hS) :
    Pretriangulated (spaceDerivedCategory B S hS X) :=
  @DerivedCategory.instPretriangulated _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X)

/-- `D(𝒪_X)` is triangulated. -/
instance isTriangulated_spaceDerivedCategory (X : AlgebraicSpaces B S hS) :
    IsTriangulated (spaceDerivedCategory B S hS X) :=
  @DerivedCategory.instIsTriangulated _ _ (modulesAbelianSmallEtale B S hS X.1 X.2)
    (spaceHasDerivedCategory B S hS X)

/-- `D_QCoh(𝒪_X)` is closed under isomorphisms in `D(𝒪_X)`. -/
instance isClosedUnderIsomorphisms_spaceQuasicoherentProp (X : AlgebraicSpaces B S hS) :
    (spaceQuasicoherentProp B S hS X).IsClosedUnderIsomorphisms :=
  ⟨fun e h n => SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((spaceDerivedHomology B S hS X n).mapIso e) (h n)⟩

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`: quasi-coherence is a weak Serre
class. -/
instance isTriangulated_spaceQuasicoherentProp (X : AlgebraicSpaces B S hS) :
    (spaceQuasicoherentProp B S hS X).IsTriangulated :=
  @DerivedCategoryB.derivedCategoryB_isTriangulated _ _
    (modulesAbelianSmallEtale B S hS X.1 X.2) (spaceHasDerivedCategory B S hS X) _
    (@WeakSerre.isWeakSerre_of_isWeakSerreClass _ _ (modulesAbelianSmallEtale B S hS X.1 X.2) _
      (quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS X.1 X.2))

end AlgebraicGeometry.Space

end
