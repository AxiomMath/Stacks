module

public import StacksFrontier.AlgebraicGeometry.Spaces.GradedPullHomOfMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistGlued
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistGradedAlgebra

/-!
# The map `θ` of Stacks 085F as a homomorphism of graded algebras

For a map `ψ : 𝒜 ⟶ ℬ` of quasi-coherent graded `𝒪_X`-algebras on an algebraic space `X`, with
`P = Proj_X(𝒜)`, `Q = Proj_X(ℬ)`, the open `U(ψ) ⊆ Q`, `r_ψ : U(ψ) ⟶ P` and `ι : U(ψ) ⟶ Q`, the
glued maps `θ_d : r_ψ^*𝒪_P(d) ⟶ ι^*𝒪_Q(d)` assemble into one map of `ℤ`-graded
`𝒪_{U(ψ)}`-algebras
`θ : r_ψ^*(⨁_{d ∈ ℤ} 𝒪_P(d)) ⟶ ι^*(⨁_{d ∈ ℤ} 𝒪_Q(d))`
between the inverse images (Stacks 0FQX) of the graded algebras of twists of Stacks 084D, once the
`θ_d` carry the inverse image along `r_ψ` of the multiplication of the twists of `P` to the
inverse image along `ι` of the multiplication of the twists of `Q`, both read through Stacks 03EL.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraHomOfMul`: the map `θ` of graded
  algebras, with degree-`d` component `θ_d`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraHomOfMul_app`: its degree-`d`
  component is the glued map `θ_d`.
* `AlgebraicGeometry.Space.RelativeProjSituation.eq_twistAlgebraHomOfMul`: it is the only map of
  graded algebras with these components.

## References

* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

namespace RelativeProjSituation

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

section Generic

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- The multiplication of `⨁_{n ∈ ℤ} 𝒪_P(n)`, read out of the tensor product of `𝒪_P`-modules, is
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraMul`. -/
theorem modulesTensorObjIso_hom_comp_mulSheaf_twistGradedAlgebra (i j : ℤ) :
    haveI := SmallEtale.instHasSheafify s.site s.base s.containsBase s.relativeProjFunctor
      AddCommGrpCat.{u}
    haveI := SmallEtale.instWEqualsLocallyBijective s.site s.base s.containsBase
      s.relativeProjFunctor AddCommGrpCat.{u}
    (modulesTensorObjIso s.site s.base s.containsBase s.relativeProjFunctor
        s.isAlgebraicSpace_relativeProjFunctor (s.twistModule Px i).obj
        (s.twistModule Px j).obj).hom ≫
      SheafOfModules.GradedAlgebra.mulSheaf.{u, u + 1, u, u}
        (J := SmallEtale.topology s.site s.base s.containsBase s.relativeProjFunctor)
        (s.twistGradedAlgebra Px) i j = s.twistAlgebraMul Px i j :=
  (congrArg (fun φ => (modulesTensorObjIso s.site s.base s.containsBase s.relativeProjFunctor
        s.isAlgebraicSpace_relativeProjFunctor (s.twistModule Px i).obj
        (s.twistModule Px j).obj).hom ≫ φ) (s.mulSheaf_twistGradedAlgebra Px i j)).trans
    (Iso.hom_inv_id_assoc _ _)

end Generic

section Map

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
  (Px : Presentation B S hS X.1 X.2)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝒢" => relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- **Stacks 085F, the map `θ` of `ℤ`-graded `𝒪_{U(ψ)}`-algebras**
`θ : r_ψ^*(⨁_{d ∈ ℤ} 𝒪_P(d)) ⟶ ι^*(⨁_{d ∈ ℤ} 𝒪_Q(d))`, between the inverse images (Stacks 0FQX)
along `r_ψ : U(ψ) ⟶ P` and `ι : U(ψ) ⟶ Q` of the graded algebras of twists of Stacks 084D, whose
degree-`d` component is the glued map `θ_d`; `hmul` says that the `θ_d` carry the inverse image
along `r_ψ` of the multiplication `𝒪_P(i) ⊗ 𝒪_P(j) ⟶ 𝒪_P(i + j)` to the inverse image along `ι`
of the multiplication of the twists of `Q`, both read through Stacks 03EL
(`AlgebraicGeometry.Space.PullMulCompat`). -/
def twistAlgebraHomOfMul
    (hmul : PullMulCompat (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (fun n => ((𝔰₁).twistModule Px n).obj) (fun n => ((𝔰₂).twistModule Px n).obj)
      (fun n => twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)
      (fun i j => (𝔰₁).twistAlgebraMul Px i j) (fun i j => (𝔰₂).twistAlgebraMul Px i j)) :
    SheafOfModules.GradedAlgebra.Hom
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
        (Y := smallEtaleRingedTopos B S hS (projSpace₁ h₁c h₁n h₁q h₁k))
        (smallEtaleRingedToposHom B S hS
          (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
        ((𝔰₁).twistGradedAlgebra Px))
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
        (Y := smallEtaleRingedTopos B S hS (projSpace₂ h₂c h₂n h₂q h₂k))
        (smallEtaleRingedToposHom B S hS
          (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
        ((𝔰₂).twistGradedAlgebra Px)) :=
  gradedPullHomOfMul (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
    (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) ((𝔰₁).twistGradedAlgebra Px)
    ((𝔰₂).twistGradedAlgebra Px) (fun n => twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)
    (fun i j => (𝔰₁).twistAlgebraMul Px i j) (fun i j => (𝔰₂).twistAlgebraMul Px i j)
    (fun i j => (𝔰₁).modulesTensorObjIso_hom_comp_mulSheaf_twistGradedAlgebra Px i j)
    (fun i j => (𝔰₂).modulesTensorObjIso_hom_comp_mulSheaf_twistGradedAlgebra Px i j) hmul

/-- The degree-`d` component of the map `θ` of graded algebras of Stacks 085F is the glued map
`θ_d`. -/
theorem twistAlgebraHomOfMul_app
    (hmul : PullMulCompat (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (fun n => ((𝔰₁).twistModule Px n).obj) (fun n => ((𝔰₂).twistModule Px n).obj)
      (fun n => twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)
      (fun i j => (𝔰₁).twistAlgebraMul Px i j) (fun i j => (𝔰₂).twistAlgebraMul Px i j)) (n : ℤ) :
    gradedPullHomApp (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
        (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) ((𝔰₁).twistGradedAlgebra Px)
        ((𝔰₂).twistGradedAlgebra Px)
        (twistAlgebraHomOfMul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px hmul) n =
      twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n :=
  gradedPullHomApp_gradedPullHomOfMul (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
    (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) ((𝔰₁).twistGradedAlgebra Px)
    ((𝔰₂).twistGradedAlgebra Px) (fun n => twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)
    (fun i j => (𝔰₁).twistAlgebraMul Px i j) (fun i j => (𝔰₂).twistAlgebraMul Px i j)
    (fun i j => (𝔰₁).modulesTensorObjIso_hom_comp_mulSheaf_twistGradedAlgebra Px i j)
    (fun i j => (𝔰₂).modulesTensorObjIso_hom_comp_mulSheaf_twistGradedAlgebra Px i j) hmul n

/-- **The map `θ` of graded algebras of Stacks 085F is unique**: a map of graded algebras
`r_ψ^*(⨁_d 𝒪_P(d)) ⟶ ι^*(⨁_d 𝒪_Q(d))` whose degree-`d` components are the glued maps `θ_d` is
`AlgebraicGeometry.Space.RelativeProjSituation.twistAlgebraHomOfMul`. -/
theorem eq_twistAlgebraHomOfMul
    (hmul : PullMulCompat (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
      (fun n => ((𝔰₁).twistModule Px n).obj) (fun n => ((𝔰₂).twistModule Px n).obj)
      (fun n => twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)
      (fun i j => (𝔰₁).twistAlgebraMul Px i j) (fun i j => (𝔰₂).twistAlgebraMul Px i j))
    (θ : SheafOfModules.GradedAlgebra.Hom
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
        (Y := smallEtaleRingedTopos B S hS (projSpace₁ h₁c h₁n h₁q h₁k))
        (smallEtaleRingedToposHom B S hS
          (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
        ((𝔰₁).twistGradedAlgebra Px))
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
        (Y := smallEtaleRingedTopos B S hS (projSpace₂ h₂c h₂n h₂q h₂k))
        (smallEtaleRingedToposHom B S hS
          (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
        ((𝔰₂).twistGradedAlgebra Px)))
    (hθ : ∀ n : ℤ, gradedPullHomApp (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ)
        (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) ((𝔰₁).twistGradedAlgebra Px)
        ((𝔰₂).twistGradedAlgebra Px) θ n = twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n) :
    θ = twistAlgebraHomOfMul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px hmul :=
  SheafOfModules.GradedAlgebra.Hom.ext hθ

end Map

end RelativeProjSituation

end AlgebraicGeometry.Space

end
