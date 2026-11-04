module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedDualComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.CategoryTheory.Monoidal.BifunctorIntegerPowersMap

/-!
# Products of integer tensor powers of perfect objects commute with derived pullback

Let `f : X ⟶ Y` be a morphism of algebraic spaces and let `E_1, …, E_r` be perfect objects of
`D(𝒪_Y)`.  For every `n ∈ ℤ^{⊕ r}`,

`Lf^*(E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}) ≅ (Lf^*E_1)^{⊗ n_1} ⊗ ⋯ ⊗ (Lf^*E_r)^{⊗ n_r}`.

Indeed `Lf^*` commutes with the derived tensor product (Stacks 07A4), carries `𝒪_Y` to `𝒪_X`,
and commutes with the derived dual of a perfect object (Stacks 08I3, 08JJ).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackDerivedTensorPowerProductIso`: the
  isomorphism above.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackDerivedTensorPowerIso`: its case
  `r = 1`, `Lf^*(E^{⊗ n}) ≅ (Lf^*E)^{⊗ n}`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- `Lf^*` carries the structure sheaf in degree zero to the structure sheaf in degree zero, at
the spelling of the unit of the integer tensor powers. -/
def smallEtaleDerivedModulePullbackDerivedStructureSheafIso (f : X ⟶ Y) :
    (smallEtaleDerivedModulePullback B S hS f).obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)))) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) :=
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).app
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))).symm ≪≫
    smallEtaleDerivedModulePullbackUnitIso f ≪≫
    (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).app
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))

/-- **Products of integer tensor powers of perfect objects commute with derived pullback**: for
`f : X ⟶ Y` and perfect `E_1, …, E_r ∈ D(𝒪_Y)`,
`Lf^*(E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}) ≅ (Lf^*E_1)^{⊗ n_1} ⊗ ⋯ ⊗ (Lf^*E_r)^{⊗ n_r}`. -/
def smallEtaleDerivedModulePullbackDerivedTensorPowerProductIso (f : X ⟶ Y) {r : ℕ}
    (E : Fin r → DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : ∀ j, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect (E j)) (n : Fin r → ℤ) :
    (smallEtaleDerivedModulePullback B S hS f).obj (derivedTensorPowerProduct B S hS Y.1 Y.2 E n) ≅
      derivedTensorPowerProduct B S hS X.1 X.2
        (fun j => (smallEtaleDerivedModulePullback B S hS f).obj (E j)) n :=
  Functor.multiTensorPowMapIso (smallEtaleDerivedModulePullback B S hS f)
    (fun A A' => (smallEtaleDerivedPullbackTensorIso f).app (A, A'))
    (smallEtaleDerivedModulePullbackDerivedStructureSheafIso f) E
    (fun j => derivedDual B S hS Y.1 Y.2 (E j))
    (fun j => derivedDual B S hS X.1 X.2 ((smallEtaleDerivedModulePullback B S hS f).obj (E j)))
    (fun j => smallEtaleDerivedModulePullbackDerivedDualIso f (E j) (hE j)) n

/-- **Integer tensor powers of a perfect object commute with derived pullback**:
`Lf^*(E^{⊗ n}) ≅ (Lf^*E)^{⊗ n}` for `E ∈ D(𝒪_Y)` perfect and `n ∈ ℤ`. -/
def smallEtaleDerivedModulePullbackDerivedTensorPowerIso (f : X ⟶ Y)
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hE : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect E) (n : ℤ) :
    (smallEtaleDerivedModulePullback B S hS f).obj (derivedTensorPower B S hS Y.1 Y.2 E n) ≅
      derivedTensorPower B S hS X.1 X.2 ((smallEtaleDerivedModulePullback B S hS f).obj E) n :=
  Functor.intTensorPowMapIso (smallEtaleDerivedModulePullback B S hS f)
    (fun A A' => (smallEtaleDerivedPullbackTensorIso f).app (A, A'))
    (smallEtaleDerivedModulePullbackDerivedStructureSheafIso f) E (derivedDual B S hS Y.1 Y.2 E)
    (derivedDual B S hS X.1 X.2 ((smallEtaleDerivedModulePullback B S hS f).obj E))
    (smallEtaleDerivedModulePullbackDerivedDualIso f E hE) n

end AlgebraicGeometry.Space

end
