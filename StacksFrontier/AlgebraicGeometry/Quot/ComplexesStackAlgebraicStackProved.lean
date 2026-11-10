module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityCechDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentProved
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackSmallerBaseComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceGrothendieck

/-!
# Stacks 0DLN for `Complexes_{X/Y}`, with Stacks 0DIQ and the Čech case of Stacks 0DLA proved

Stacks 0DIQ, the derived Grothendieck existence theorem, is
`AlgebraicGeometry.Space.DerivedExistenceSystem.exists_isPseudoCoherent_stageDerivedPullback_iso`
(`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/DerivedExistenceGrothendieck.lean`), stated
for the systems of Situation 0DIK. The change of base of
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackDerivedExistenceBridge.lean`
(`ComplexesSituation.SpecLimitTower.exists_restriction_of_derivedExistence`,
with the comparison over a smaller base
`AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`) turns it into Stacks
0DIQ at `X_T ⟶ T` for a tower `T_n ≅ Spec R_n` with limit `T ≅ Spec (lim R_n)`: the form of the
hypothesis `h0DIQ` of
`ComplexesSituation.isAlgebraicStack_complexes_of_cechDescent_of_derivedExistence`.
The Čech case of Stacks 0DLA is
`AlgebraicGeometry.Space.ComplexesSituation.cechDescent_proved`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.exists_restriction_proved`: Stacks
  0DIQ at `X_T ⟶ T`.
* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_cechDescent`:
  Stacks 0DLN, granted the Čech case of Stacks 0DLA.
* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_proved`: **Stacks 0DLN**,
  with no hypothesis beyond its statement.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u z

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space.ComplexesSituation

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory complexesCategory

variable {B : BigFppfSite.{u}}

/-- **Stacks 0DIQ at `X_T ⟶ T`.** Let `D` be Situation 0DLE over `S` and `L` a tower
`T_n ≅ Spec R_n` with limit `T ≅ Spec (lim R_n)`. For pseudo-coherent `K_n` on `X_{T_n}` with
isomorphisms `φ_n : L(X_{T_n} ⟶ X_{T_{n+1}})^* K_{n+1} ⟶ K_n` there is a pseudo-coherent `E` on
`X_T` with isomorphisms `ψ_n : L(X_{T_n} ⟶ X_T)^* E ⟶ K_n` compatible with the `φ_n`.

This is
`AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.exists_restriction_of_derivedExistence`
with the comparison over a smaller base
`AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison` and Stacks 0DIQ for
Situation 0DIK given by
`Space.DerivedExistenceSystem.exists_isPseudoCoherent_stageDerivedPullback_iso`. -/
theorem SpecLimitTower.exists_restriction_proved {S : Scheme.{u}} {hS : B.Contains S}
    {D : ComplexesSituation B S hS} {level : ℕ → SchemesOver D.Y}
    {transition : ∀ n, level n ⟶ level (n + 1)} (L : D.SpecLimitTower level transition)
    (K : ∀ n, derivedModules B S hS (D.space (level n)))
    (hK : ∀ n, (smallEtaleRingedSite B S hS (D.space (level n)).1
      (D.space (level n)).2).IsPseudoCoherent (K n))
    (φ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
      (D.relativeMap (transition n))).obj (K (n + 1)) ⟶ K n) (hφ : ∀ n, IsIso (φ n)) :
    ∃ (E : derivedModules B S hS (D.space L.T)),
      (smallEtaleRingedSite B S hS (D.space L.T).1 (D.space L.T).2).IsPseudoCoherent E ∧
      ∃ ψ : ∀ n, ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (L.toLimit n))).obj E ⟶ K n, (∀ n, IsIso (ψ n)) ∧
        ∀ n, Functor.fibreComp (D.compComparison (transition n) (L.toLimit (n + 1))) (φ n)
            (ψ (n + 1)) =
          (D.relativeMapComparison (L.transition_toLimit n)).hom.app E ≫ ψ n :=
  L.exists_restriction_of_derivedExistence (smallerBaseDerivedComparison B S hS)
    (fun DS => DS.exists_isPseudoCoherent_stageDerivedPullback_iso) K hK φ hφ

/-- **Stacks 0DLN, granted Stacks 0DLA** (unregistered). In Situation 0DLE over `S`
(`f : X ⟶ Y` proper, flat and of finite presentation), `Complexes_{X/Y}` is an algebraic stack
over `S`, given `h0DLA`, the Čech case of Stacks 0DLA (proved as
`AlgebraicGeometry.Space.ComplexesSituation.cechDescent_proved`).

This is
`ComplexesSituation.isAlgebraicStack_complexes_of_cechDescent_of_derivedExistence`
with Stacks 0DIQ given by
`AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.exists_restriction_proved`. -/
theorem isAlgebraicStack_complexes_of_cechDescent
    (h0DLA : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      D.CechDescent)
    {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_cechDescent_of_derivedExistence h0DLA
    (fun _ _ _ _ _ _ _ L K hK φ hφ => L.exists_restriction_proved K hK φ hφ) hS D

/-- **Stacks 0DLN: `Complexes_{X/Y}` is an algebraic stack.** In Situation 0DLE over `S`
(`f : X ⟶ Y` proper, flat and of finite presentation), `Complexes_{X/Y}` is an algebraic stack
over `S`.

This is
`ComplexesSituation.isAlgebraicStack_complexes_of_cechDescent_of_derivedExistence`
with Stacks 0DLA, Čech case, given by
`AlgebraicGeometry.Space.ComplexesSituation.cechDescent_proved` and Stacks 0DIQ given by
`AlgebraicGeometry.Space.ComplexesSituation.SpecLimitTower.exists_restriction_proved`. -/
@[stacks 0DLN]
theorem isAlgebraicStack_complexes_proved {S : Scheme.{u}} (hS : B.Contains S)
    (D : ComplexesSituation B S hS) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D) :=
  isAlgebraicStack_complexes_of_cechDescent cechDescent_proved hS D

end AlgebraicGeometry.Space.ComplexesSituation

end
