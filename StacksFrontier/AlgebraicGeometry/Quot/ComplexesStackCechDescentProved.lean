module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentProof
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtaleAugmentationTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtaleVertex
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentStrictPairRealization
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackProved
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleHypercoverDescentTransfer
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleSystemRealizesUnconditional

/-!
# Stacks 0DLA (Čech case) and Stacks 0DLH for `Complexes_{X/Y}`

The four pieces of the proof of the Čech case of Stacks 0DLA
(`AlgebraicGeometry.Space.ComplexesSituation.CechDescent`) are proved:

* P-core, Stacks 0D9T without flatness:
  `CategoryTheory.SimplicialSiteSituation.cartesianModuleSystemRealizes_unconditional`;
* P-0DHF, Stacks 0DLA on the spaces-étale sites, in the namespace `AlgebraicGeometry.Space`:
  `SimplicialSpacesEtaleSite.spacesEtaleHypercoverDescentOfRealization_of_strict`, with its four
  inputs on the strict components;
* P-univ, the passage to the small étale sites:
  `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDescentComparison` and
  `AlgebraicGeometry.Space.smallEtaleHypercoverDescentOfSpacesEtale`;
* P-cech, the Čech case: `AlgebraicGeometry.Space.cechDescentOfSmallEtaleHypercoverDescent`.

`AlgebraicGeometry.Space.ComplexesSituation.cechDescent_of_pieces` assembles them.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.cechDescent_proved`: Stacks 0DLA, Čech case, for
  every `Complexes` situation, in the shape of the hypothesis `h0DLA`.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor_isStackInGroupoids_proved`:
  **Stacks 0DLH**, `Complexes_{X/Y}` is a stack in groupoids over `(Sch/S)_fppf`.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

open AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}}

attribute [local instance] complexesCategory instModulesHasDerivedCategory

/-- **Stacks 0DLA, Čech case.** For every scheme `S` of the site and every `Complexes` situation
`D` over `S`, a Čech covering datum of `Complexes_{X/Y}` whose members have no negative
self-extensions on the fibres glues (`AlgebraicGeometry.Space.ComplexesSituation.CechDescent`). -/
theorem cechDescent_proved :
    ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS), D.CechDescent :=
  fun {S} hS D => cechDescent_of_pieces
    (fun C O => C.cartesianModuleSystemRealizes_unconditional O)
    (spacesEtaleHypercoverDescentOfRealization_of_strict B S hS
      (fun X => strictPairRealization X) (strictAugmentationTransitionCoherent B S hS)
      (strictCartesianQuasicoherent B S hS) (spacesEtaleVertexQuasicoherent B S hS))
    (smallEtaleSpacesEtaleDescentComparison B S hS)
    (smallEtaleHypercoverDescentOfSpacesEtale B S hS)
    (cechDescentOfSmallEtaleHypercoverDescent (B := B) (S := S) (hS := hS)) D

/-- In a `Complexes` situation `D` over `S`, the category `Complexes_{X/Y}` fibred in groupoids
over `(Sch/S)_fppf` is a stack in groupoids. -/
@[stacks 0DLH]
theorem complexesFunctor_isStackInGroupoids_proved {S : Scheme.{u}} {hS : B.Contains S}
    (D : ComplexesSituation B S hS) :
    (complexesFunctor D).IsStackInGroupoids.{u + 1} (BigFppfOver.topology B S hS) :=
  D.complexesFunctor_isStackInGroupoids_of_cechDescent (cechDescent_proved hS D)

end AlgebraicGeometry.Space.ComplexesSituation

end
