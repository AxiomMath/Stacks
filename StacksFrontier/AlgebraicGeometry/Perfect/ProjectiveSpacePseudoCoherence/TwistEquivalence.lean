module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMultiplication
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity

/-!
# Twisting by `𝒪(d)` is an autoequivalence of `D(𝒪_{ℙⁿ_S})`

Let `S` be a scheme and `𝒪(d)` the twists of the structure sheaf of `ℙⁿ_S`. In the derived
category of `𝒪_{ℙⁿ_S}`-modules, `𝒪(a)[0] ⊗^𝐋 𝒪(b)[0] ≅ 𝒪(a + b)[0]`, so `𝒪(d)[0]` is an
invertible object of the monoidal derived category, and `- ⊗^𝐋 𝒪(d)[0]` is an autoequivalence.

## Main results

* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.twistTensorTwistIso`:
  `𝒪(a)[0] ⊗^𝐋 𝒪(b)[0] ≅ 𝒪(a + b)[0]`.
* `AlgebraicGeometry.ProjectiveSpacePseudoCoherence.twistEquivalence`: the autoequivalence
  `- ⊗^𝐋 𝒪(d)[0]` of `D(𝒪_{ℙⁿ_S})`, whose functor is the derived tensor bifunctor
  `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` with `𝒪(d)[0]` in the right
  variable.

## Implementation notes

The monoidal structure is `Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal` at the
canonical derived tensor product, whose tensor bifunctor and unit are the derived tensor
product and the structure sheaf in degree zero on the nose; the inverse of `𝒪(d)[0]` is
`𝒪(-d)[0]`, and `CategoryTheory.MonoidalCategory.HasInverse.tensorRightEquivalence` produces the
equivalence. The derived categories are the standard model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherence

attribute [local instance 100000] HasDerivedCategory.standard

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistOverMulIso twistZeroIsoUnit)

variable (n : ℕ) (S : Scheme.{u})

/-- The twist `𝒪(d)` of `ℙⁿ_S` placed in degree zero. -/
abbrev twistObj (d : ℤ) : DerivedCategory (projectiveSpaceOver n S).Modules :=
  (DerivedCategory.singleFunctor _ 0).obj (twistOver n S d)

/-- The monoidal structure on `D(𝒪_{ℙⁿ_S})` given by the derived tensor product. -/
abbrev derivedMonoidal : MonoidalCategory (DerivedCategory (projectiveSpaceOver n S).Modules) :=
  Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal (projectiveSpaceOver n S).sheaf
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (projectiveSpaceOver n S).sheaf)

/-- **`𝒪(a)[j] ⊗^𝐋 𝒪(b)[0] ≅ 𝒪(a + b)[j]`.** -/
def singleTwistTensorIso (j a b : ℤ) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (projectiveSpaceOver n S).sheaf).obj
        ((DerivedCategory.singleFunctor _ j).obj (twistOver n S a))).obj (twistObj n S b) ≅
      (DerivedCategory.singleFunctor _ j).obj (twistOver n S (a + b)) :=
  Stacks.Chow.derivedTwistQIso (CochainComplex.singleFunctor _ j |>.obj (twistOver n S a))
      (twistOver n S b) ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex (Stacks.Chow.twistFunctor (twistOver n S b))
        (ComplexShape.up ℤ) j).app (twistOver n S a)) ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) j).mapIso (twistOverMulIso n S a b))

/-- **`𝒪(a)[0] ⊗^𝐋 𝒪(b)[0] ≅ 𝒪(a + b)[0]`.** -/
def twistTensorTwistIso (a b : ℤ) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (projectiveSpaceOver n S).sheaf).obj (twistObj n S a)).obj (twistObj n S b) ≅
      twistObj n S (a + b) :=
  singleTwistTensorIso n S 0 a b

/-- `𝒪(0)[0]` is the unit of the monoidal derived category. -/
def twistObjZeroIso : twistObj n S 0 ≅
    (letI := derivedMonoidal n S; 𝟙_ (DerivedCategory (projectiveSpaceOver n S).Modules)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso (twistZeroIsoUnit n S)

/-- `𝒪(d)[0]` is invertible, with inverse `𝒪(-d)[0]`. -/
def twistHasInverse (d : ℤ) :
    letI := derivedMonoidal n S
    HasInverse (twistObj n S d) :=
  letI := derivedMonoidal n S
  { inv := twistObj n S (-d)
    isoLeft := twistTensorTwistIso n S d (-d) ≪≫
      eqToIso (congrArg (twistObj n S) (by ring)) ≪≫ twistObjZeroIso n S
    isoRight := twistTensorTwistIso n S (-d) d ≪≫
      eqToIso (congrArg (twistObj n S) (by ring)) ≪≫ twistObjZeroIso n S }

/-- **`- ⊗^𝐋 𝒪(d)[0]` is an autoequivalence of `D(𝒪_{ℙⁿ_S})`.** -/
def twistEquivalence (d : ℤ) :
    DerivedCategory (projectiveSpaceOver n S).Modules ≌
      DerivedCategory (projectiveSpaceOver n S).Modules :=
  letI := derivedMonoidal n S
  (twistHasInverse n S d).tensorRightEquivalence

/-- The functor of `twistEquivalence n S d` is the derived tensor product `- ⊗^𝐋 𝒪(d)[0]`. -/
theorem twistEquivalence_functor (d : ℤ) :
    (twistEquivalence n S d).functor =
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (projectiveSpaceOver n S).sheaf).flip.obj (twistObj n S d) :=
  rfl

end AlgebraicGeometry.ProjectiveSpacePseudoCoherence

end
