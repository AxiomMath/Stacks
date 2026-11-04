module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.GradedAlgebraSheafIso
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.NonnegTruncationFunctorial
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.GradedTwistMultiplicativity
public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentUnit

/-!
# Situation 01QH's comparison as an isomorphism of algebra sheaves

`Stacks.SectionRingProjIso.gradedTwistComparisonOfIsAmple` is Situation [Stacks, Tag 01QH]'s
comparison

`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n)) ≅ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}`

as an isomorphism of sheaves of `ℤ`-graded `𝒪_X`-algebras, with no hypothesis beyond ampleness.
Both left-hand entries of [Stacks, Tag 0EKG]'s diagram are relative spectra of the twist
*algebras*, and the relative spectrum of [Stacks, Tag 01LM] consumes a
`Stacks.RelativeSpec.AlgebraSheaf` — a sheaf of commutative rings over the structure sheaf, not a
sheaf of graded algebras. **This file reads the comparison between the algebra sheaves.**

## The two steps

The comparison arrives from the recognition theorem as a
`SheafOfModules.GradedAlgebra.Hom`, which carries no `map_one`, and the realization
`Stacks.RelativeSpec.gradedAlgebraSheafMap` consumes a
`SheafOfModules.GradedAlgebra.UnitalHom`. The unit is
`Stacks.AlgebraicGeometry.GradedLaurentRecognition.oneHom_comp_gradedIso_app_zero`, in the global
form `oneHom ≫ app 0 = oneHom`, and
`SheafOfModules.GradedAlgebra.UnitalHom.ofOneHomComp` converts that into the global-sections form
the constructor asks for. That is `gradedTwistUnitalComparison`.

Both algebras then need commutative homogeneous multiplication. For the source that is
`Stacks.SectionRingProjIso.heq_pbTwistGradedAlgebra_mul_comm`; for the target it is
`Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm`, which already holds for the Laurent
algebra of any invertible module and applies here with no transport,
`…RelativeProjQcohSheaf.laurent` being a reducible abbreviation for `…TensorPower.laurentAlgebra`.
Feeding the unital comparison and the two commutativity data to
`Stacks.RelativeSpec.gradedAlgebraSheafIso` gives the isomorphism of algebra sheaves.

## Main definitions

* `Stacks.SectionRingProjIso.laurentAlgebraSheaf`: **`⨁_{n ∈ ℤ} 𝓛^{⊗ n}` as a sheaf of
  commutative `𝒪_X`-algebras**, the form in which a relative spectrum over `X` can be taken of
  it.
* `Stacks.SectionRingProjIso.gradedTwistUnitalComparison`: **Situation 01QH's comparison as a
  *unital* homomorphism of sheaves of graded algebras.**
* `Stacks.SectionRingProjIso.pbTwistAlgebraSheafIsoLaurent`: **`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n))` and
  `⨁_{n ∈ ℤ} 𝓛^{⊗ n}` are isomorphic as sheaves of commutative `𝒪_X`-algebras**, which is the
  substitution [Stacks, Tag 0EKI]'s diagram clause makes in the integer-graded left-hand entry of
  [Stacks, Tag 0EKG]'s diagram.

## References

* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.RingedSpace
open Stacks.Ample (IsInvertibleModule)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (laurent isSheafStruct)

universe u

namespace Stacks.SectionRingProjIso

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

/-! ### The target as a sheaf of commutative algebras -/

/-- **`⨁_{n ∈ ℤ} 𝓛^{⊗ n}` as a sheaf of commutative `𝒪_X`-algebras**, which is the form in which
a relative spectrum over `X` can be taken of it.

This is the ungraded realization `Stacks.RelativeSpec.gradedAlgebraSheaf` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent`, whose commutativity input is
`Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm` — the Laurent algebra of an
invertible module has commutative homogeneous multiplication for every such module, so nothing
about `𝓛` beyond invertibility enters. It is the right-hand side of the substitution
[Stacks, Tag 0EKI]'s diagram clause makes in the integer-graded left-hand entry of
[Stacks, Tag 0EKG]'s diagram. -/
def laurentAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  Stacks.RelativeSpec.gradedAlgebraSheaf X (laurent L)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm X.toRingedSpace.presheaf
      (isSheafStruct X) L)

/-! ### The comparison as a unital homomorphism -/

/-- **Situation [Stacks, Tag 01QH]'s comparison as a *unital* homomorphism of sheaves of graded
algebras.**

`Stacks.SectionRingProjIso.gradedTwistComparisonOfIsAmple` is an isomorphism in the category of
sheaves of graded algebras, whose morphisms are the `SheafOfModules.GradedAlgebra.Hom` — degreewise
and multiplicative, with no unit condition. Unit preservation is the separate statement
`Stacks.AlgebraicGeometry.GradedLaurentRecognition.oneHom_comp_gradedIso_app_zero`, in the global
form `oneHom ≫ app 0 = oneHom`, and
`SheafOfModules.GradedAlgebra.UnitalHom.ofOneHomComp` turns that into the global-sections form the
constructor `…UnitalHom.ofHom` asks for. -/
def gradedTwistUnitalComparison :
    letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
    SheafOfModules.GradedAlgebra.UnitalHom (pbTwistGradedAlgebra L hL) (laurent L) :=
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  SheafOfModules.GradedAlgebra.UnitalHom.ofOneHomComp
    (A := pbTwistGradedAlgebra L hL) (B := laurent L)
    (gradedTwistComparisonOfIsAmple L hL).hom
    (Stacks.AlgebraicGeometry.GradedLaurentRecognition.oneHom_comp_gradedIso_app_zero _ _ _ _ _)

/-- The degreewise components of the unital comparison are those of the graded comparison;
`SheafOfModules.GradedAlgebra.UnitalHom.ofOneHomComp` changes no component. -/
theorem gradedTwistUnitalComparison_app (n : ℤ) :
    letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
    (gradedTwistUnitalComparison L hL).app n = (gradedTwistComparisonOfIsAmple L hL).hom.app n :=
  rfl

/-- **The unital comparison is an isomorphism in every degree**, being the degreewise component
of an isomorphism of sheaves of graded algebras
(`Stacks.AlgebraicGeometry.ProjRepresentsF1.gradedAlgebraIsoApp`). -/
theorem isIso_gradedTwistUnitalComparison_app (n : ℤ) :
    letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
    IsIso ((gradedTwistUnitalComparison L hL).app n) :=
  (Stacks.AlgebraicGeometry.ProjRepresentsF1.gradedAlgebraIsoApp
    (gradedTwistComparisonOfIsAmple L hL) n).isIso_hom

/-! ### The comparison of the algebra sheaves -/

/-- **`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n))` and `⨁_{n ∈ ℤ} 𝓛^{⊗ n}` are isomorphic as sheaves of
commutative `𝒪_X`-algebras**, for `𝓛` an ample invertible `𝒪_X`-module, `A = Γ_*(X, 𝓛)` and `r`
the canonical morphism of [Stacks, Tag 01PZ].

This is Situation [Stacks, Tag 01QH]'s comparison read between the algebra sheaves: the unital
comparison `gradedTwistUnitalComparison`, which is an isomorphism in every degree, carried through
the `Iso` form `Stacks.RelativeSpec.gradedAlgebraSheafIso` of
`Stacks.RelativeSpec.gradedAlgebraSheafMap`. It is the substitution [Stacks, Tag 0EKI]'s diagram
clause makes in the integer-graded left-hand entry of [Stacks, Tag 0EKG]'s diagram, at the
algebra-sheaf spelling. -/
def pbTwistAlgebraSheafIsoLaurent :
    pbTwistAlgebraSheaf L hL ≅ laurentAlgebraSheaf L :=
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  haveI : ∀ n : ℤ, IsIso ((gradedTwistUnitalComparison L hL).app n) :=
    isIso_gradedTwistUnitalComparison_app L hL
  Stacks.RelativeSpec.gradedAlgebraSheafIso X (heq_pbTwistGradedAlgebra_mul_comm L hL)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm X.toRingedSpace.presheaf
      (isSheafStruct X) L)
    (gradedTwistUnitalComparison L hL)

/-! ### The nonnegative halves -/

/-- **`⨁_{m ≥ 0} 𝓛^{⊗ m}` as a sheaf of commutative `𝒪_X`-algebras**, the nonnegative truncation
of `laurentAlgebraSheaf`'s graded algebra. This is the right-hand side of the substitution
[Stacks, Tag 0EKI]'s diagram clause makes in the nonnegatively graded left-hand entry `L` of
[Stacks, Tag 0EKG]'s diagram. -/
def nonnegLaurentAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  Stacks.RelativeSpec.gradedAlgebraSheaf X
    (Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation (laurent L))
    (Stacks.AlgebraicGeometry.NonnegTruncation.isCommutative_nonnegTruncation (laurent L)
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm X.toRingedSpace.presheaf
        (isSheafStruct X) L))

/-- **`r^*(⨁_{m ≥ 0} 𝒪_{Proj A}(m))` as a sheaf of commutative `𝒪_X`-algebras**, the nonnegative
truncation of `Stacks.SectionRingProjIso.pbTwistAlgebraSheaf`'s graded algebra.

By `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra_eq_nonnegTruncation` the truncation
of the integral twist algebra *is* the nonnegative twist algebra, so this is the pullback along
`r` of [Stacks, Tag 0EKG]'s nonnegatively graded left-hand entry, read degreewise. -/
def pbNonnegTwistAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  Stacks.RelativeSpec.gradedAlgebraSheaf X
    (Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation (pbTwistGradedAlgebra L hL))
    (Stacks.AlgebraicGeometry.NonnegTruncation.isCommutative_nonnegTruncation
      (pbTwistGradedAlgebra L hL) (heq_pbTwistGradedAlgebra_mul_comm L hL))

/-- **`r^*(⨁_{m ≥ 0} 𝒪_{Proj A}(m))` and `⨁_{m ≥ 0} 𝓛^{⊗ m}` are isomorphic as sheaves of
commutative `𝒪_X`-algebras**, for `𝓛` an ample invertible `𝒪_X`-module, `A = Γ_*(X, 𝓛)` and `r`
the canonical morphism of [Stacks, Tag 01PZ].

This is `pbTwistAlgebraSheafIsoLaurent` in nonnegative degrees: the unital comparison
`gradedTwistUnitalComparison`, truncated by
`Stacks.AlgebraicGeometry.NonnegTruncation.unitalHom` and still an isomorphism in every degree,
carried through `Stacks.RelativeSpec.gradedAlgebraSheafIso`. It is the substitution
[Stacks, Tag 0EKI]'s diagram clause makes in the nonnegatively graded left-hand entry `L` of
[Stacks, Tag 0EKG]'s diagram, at the algebra-sheaf spelling. -/
def pbNonnegTwistAlgebraSheafIsoNonnegLaurent :
    pbNonnegTwistAlgebraSheaf L hL ≅ nonnegLaurentAlgebraSheaf L :=
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncationAlgebraSheafIso
    (pbTwistGradedAlgebra L hL) (laurent L) (heq_pbTwistGradedAlgebra_mul_comm L hL)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm X.toRingedSpace.presheaf
      (isSheafStruct X) L)
    (gradedTwistUnitalComparison L hL) (isIso_gradedTwistUnitalComparison_app L hL)

end Monoidal

end Stacks.SectionRingProjIso

end
