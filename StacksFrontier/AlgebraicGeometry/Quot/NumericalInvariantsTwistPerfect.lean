module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleModulePerfect
public import StacksFrontier.AlgebraicGeometry.Quot.InvertibleTwistPower

/-!
# The twists `L^{⊗ n}` of an invertible module on an algebraic space are perfect

Let `F` be an algebraic space and `L` an invertible `𝒪_F`-module.  Every integer tensor power
`L^{⊗ n}` (Stacks 01CU) is again invertible
(`AlgebraicGeometry.Space.isInvertible_invertibleTensorPower`), so by Stacks 0B8N (b) it is
étale locally a direct summand of a finite free module, and `L^{⊗ n}[0]` is a perfect object of
`D(𝒪_F)` in the sense of Stacks 08G5.  This is the perfectness of the family `n ↦ L^{⊗ n}`
which Stacks 0DNF uses to see the substack `Coh^{P, L}_{X/B}` as a case of Situation 0DNC.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.ofHilbertPolynomial`: the standing data of
  Situation 0DNC with `I = ℤ`, `E n = L^{⊗ n}` and prescribed invariants `P`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_invertibleTwistObject`: `L^{⊗ n}[0]` is a perfect object
  of `D(𝒪_F)`.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The twists `L^{⊗ n}[0]` of an invertible module on an algebraic space are perfect objects
of `D(𝒪_F)`** (Stacks 08G5). -/
theorem isPerfect_invertibleTwistObject (L : Modules.{u, u} B S hS F hF)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property L]
    (n : ℤ) :
    (smallEtaleRingedSite B S hS F hF).IsPerfect (invertibleTwistObject B S hS F hF L n) :=
  RingedSite.isPerfect_singleFunctor_of_isInvertible_general _ _
    (hL := isInvertible_invertibleTensorPower B S hS F hF L n) 0

/-- **The standing data of Situation 0DNC for coherent sheaves with fixed Hilbert polynomial**
(Stacks 0DNF): over a separated morphism `f : X ⟶ B` of finite presentation, an invertible
`𝒪_X`-module `L` and `P : ℤ → ℤ`, the index set `ℤ`, the perfect objects `n ↦ L^{⊗ n}` of
`D(𝒪_X)` and the prescribed invariants `P`. -/
def NumericalSituation.ofHilbertPolynomial (D : CoherentSituation B S hS)
    (separated : IsSeparated B S hS D.f.hom)
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) : NumericalSituation.{u, 0, u} B S hS D :=
  NumericalSituation.ofInvertibleTwists B S hS D separated L
    (isPerfect_invertibleTwistObject B S hS D.X.1 D.X.2 L) P

end AlgebraicGeometry.Space

end
