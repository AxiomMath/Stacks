module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistAlgebraMulSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedCommutative
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.GradedTwistAlgebra
public import StacksFrontier.AlgebraicGeometry.SectionRingVeroneseChart.DegreeOne
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Situation 01QH as an isomorphism of graded algebras, with no hypothesis left

`Stacks.SectionRingProjIso.gradedTwistComparison` is Situation [Stacks, Tag 01QH]'s comparison

`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n)) ≅ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}`

as an isomorphism of sheaves of `ℤ`-graded `𝒪_X`-algebras, carrying one hypothesis: that the twist
multiplications of `Proj A` become isomorphisms after pullback along the canonical morphism `r` of
[Stacks, Tag 01PZ]. **This file discharges it**, so that the graded comparison is unconditional
for every ample invertible module.

## Main results

* `Stacks.SectionRingProjIso.isIso_pullback_mulSheaf_integerTwistAlgebra`: **the twist
  multiplications of `Proj A` become isomorphisms after pullback along `r`** — the hypothesis
  `hmul` of `Stacks.SectionRingProjIso.gradedTwistComparison`.
* `Stacks.SectionRingProjIso.gradedTwistComparisonOfIsAmple`: **Situation 01QH's comparison as an
  isomorphism of sheaves of `ℤ`-graded `𝒪_X`-algebras, out of ampleness alone.**

## The route, and why it costs nothing

`r` factors through [Stacks, Tag 01MU]'s open `W₁` — that is the first claim of [Stacks, Tag
01QI], `Stacks.SectionRingProjGoodOpen.projHomOfIsAmple_preimage_whereInvertible`, packaged as
`Stacks.SectionRingVeroneseChart.goodLift` with
`Stacks.SectionRingVeroneseChart.goodLift_comp_ι` — and on `W₁` the multiplication of
`⨁_{m ∈ ℤ} 𝒪_{Proj A}(m)` is an isomorphism, which is
`Stacks.AlgebraicGeometry.ProjConeTwist.isIso_pullbackGoodOpen_mulSheaf_integerTwistAlgebra`.
Pullback is multiplicative (`RingedSpaceModuleAdjunction.modulePullbackComp`) and a functor
carries isomorphisms to isomorphisms, so the pullback along `r` factors through the pullback along
`W₁ ⟶ Proj A` and the claim follows.

The delicate point is neither of those steps but the identification of the graded algebra's
multiplication with the canonical twist multiplication: stated naively, it exhausts the heartbeat
allowance in `whnf`, because the two sides live at two different tensor products of sheaves of
modules. That identification is
`Stacks.AlgebraicGeometry.ProjConeTwist.mulSheaf_integerTwistAlgebra`, routed through the
tensor-bifunctor ascription `Stacks.AlgebraicGeometry.TwistTensor.twistMul` so that the equation
has one spelling of the tensor product on both sides; see that file for details.

## References

* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.Ample (IsInvertibleModule)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.GoodOpenIntTwist (goodOpen)
open Stacks.AlgebraicGeometry.ProjConeTwist (integerTwistAlgebra
  isIso_pullbackGoodOpen_mulSheaf_integerTwistAlgebra)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (laurent isSheafStruct)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingVeroneseChart (goodLift goodLift_comp_ι)

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

/-! ### The canonical morphism, factored through `W₁`, at the ringed-space level -/

/-- `Stacks.SectionRingVeroneseChart.goodLift_comp_ι` at the spelling the pullback functor on
sheaves of modules takes: the factoring of the canonical morphism of [Stacks, Tag 01PZ] through
[Stacks, Tag 01MU]'s open `W₁`, as morphisms of ringed spaces. -/
theorem shHom_goodLift_comp_ι :
    (goodLift L hL).toLRSHom.toShHom ≫ (goodOpen (grading L)).ι.toLRSHom.toShHom =
      (projHomOfIsAmple L hL).toLRSHom.toShHom :=
  congrArg (fun φ : X ⟶ AlgebraicGeometry.Proj (grading L) => φ.toLRSHom.toShHom)
    (goodLift_comp_ι L hL)

/-- **`r^* = (goodLift)^* ∘ (W₁ ⟶ Proj A)^*` on sheaves of modules.** The canonical morphism of
[Stacks, Tag 01PZ] is the lift through [Stacks, Tag 01MU]'s open `W₁` followed by the open
immersion, and pullback is multiplicative
(`RingedSpaceModuleAdjunction.modulePullbackComp`). -/
def pullbackProjHomIsoComp :
    modulePullback (projHomOfIsAmple L hL).toLRSHom.toShHom ≅
      modulePullback (goodOpen (grading L)).ι.toLRSHom.toShHom ⋙
        modulePullback (goodLift L hL).toLRSHom.toShHom :=
  eqToIso (congrArg modulePullback (shHom_goodLift_comp_ι L hL).symm) ≪≫
    modulePullbackComp (goodLift L hL).toLRSHom.toShHom (goodOpen (grading L)).ι.toLRSHom.toShHom

/-! ### The hypothesis of the graded comparison, discharged -/

/-- **The twist multiplications of `Proj A` become isomorphisms after pullback along the canonical
morphism `r` of [Stacks, Tag 01PZ]**, for `A = Γ_*(X, 𝓛)` the section ring of an ample invertible
module — in every pair of integer degrees.

This is the hypothesis `hmul` of `Stacks.SectionRingProjIso.gradedTwistComparison`. On `W₁` the
multiplication is an isomorphism
(`Stacks.AlgebraicGeometry.ProjConeTwist.isIso_pullbackGoodOpen_mulSheaf_integerTwistAlgebra`),
`r` factors through `W₁` by the first claim of [Stacks, Tag 01QI], and `pullbackProjHomIsoComp`
splits the pullback along `r` accordingly; a functor carries isomorphisms to isomorphisms. -/
theorem isIso_pullback_mulSheaf_integerTwistAlgebra (i j : ℤ) :
    IsIso ((pullbackFunctor (projHomOfIsAmple L hL).toLRSHom.toShHom).map
      (SheafOfModules.GradedAlgebra.mulSheaf (integerTwistAlgebra (grading L)) i j)) := by
  have := isIso_pullbackGoodOpen_mulSheaf_integerTwistAlgebra (grading L) i j
  exact (NatIso.isIso_map_iff (pullbackProjHomIsoComp L hL) _).mpr
    (Functor.map_isIso (modulePullback _) _)

/-! ### Situation 01QH's comparison, unconditionally -/

/-- **Situation [Stacks, Tag 01QH]'s comparison as an isomorphism of sheaves of `ℤ`-graded
`𝒪_X`-algebras, out of ampleness alone**:

`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n)) ≅ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}`,

for `𝓛` an ample invertible `𝒪_X`-module, `A = Γ_*(X, 𝓛)` and `r` the canonical morphism of
[Stacks, Tag 01PZ].

This is `Stacks.SectionRingProjIso.gradedTwistComparison` with its one hypothesis supplied by
`isIso_pullback_mulSheaf_integerTwistAlgebra`. Multiplicativity is not assumed anywhere: the
recognition theorem `Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso` proves it from
invertibility of the multiplications and of the degree-zero piece together with the degree-one
identification. -/
@[ega "II 8.8.1" "special case"]
def gradedTwistComparisonOfIsAmple :
    letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
    pbTwistGradedAlgebra L hL ≅ laurent L :=
  gradedTwistComparison L hL (isIso_pullback_mulSheaf_integerTwistAlgebra L hL)

/-! ### The source as a sheaf of commutative algebras -/

/-- **The multiplication of `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n))` is commutative on homogeneous local
sections.**

The two sides lie in the pieces of the degrees `i + j` and `j + i`, which agree only
propositionally, so the equality is heterogeneous — this is the shape
`Stacks.RelativeSpec.gradedAlgebraSheaf` consumes. It is
`Stacks.AlgebraicGeometry.ProjConeTwist.heq_twistMul_comm`, the commutativity of the integral
twist algebra of `Proj A`, carried through the pullback by
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm_of_comm`. -/
theorem heq_pbTwistGradedAlgebra_mul_comm (i j : ℤ) (W : (Opens ↥X)ᵒᵖ)
    (a : ((pbTwistGradedAlgebra L hL).piece i).val.obj W)
    (b : ((pbTwistGradedAlgebra L hL).piece j).val.obj W) :
    HEq (((pbTwistGradedAlgebra L hL).mul i j).app W a b)
      (((pbTwistGradedAlgebra L hL).mul j i).app W b a) :=
  Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm_of_comm
    (projHomOfIsAmple L hL).toLRSHom.toShHom (integerTwistAlgebra (grading L))
    (Stacks.AlgebraicGeometry.ProjConeTwist.heq_twistMul_comm (grading L)) i j W a b

/-- **`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n))` as a sheaf of commutative `𝒪_X`-algebras**, which is the
form in which a relative spectrum over `X` can be taken of it.

This is the ungraded realization `Stacks.RelativeSpec.gradedAlgebraSheaf` of
`Stacks.SectionRingProjIso.pbTwistGradedAlgebra`, whose commutativity input is
`heq_pbTwistGradedAlgebra_mul_comm`. It is the left-hand entry of [Stacks, Tag 0EKG]'s diagram
for `A = Γ_*(X, 𝓛)`, pulled back along the canonical morphism of [Stacks, Tag 01PZ] from
`Proj A` to `X`, at the algebra-sheaf spelling. -/
def pbTwistAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf X :=
  Stacks.RelativeSpec.gradedAlgebraSheaf X (pbTwistGradedAlgebra L hL)
    (heq_pbTwistGradedAlgebra_mul_comm L hL)

end Monoidal

end Stacks.SectionRingProjIso

end
