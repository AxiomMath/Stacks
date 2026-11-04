module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistMapMul

/-!
# The triple `(U(ψ), r_ψ, θ)` of Stacks 085F

For a map `ψ : 𝒜 ⟶ ℬ` of quasi-coherent graded `𝒪_X`-algebras on an algebraic space `X`, with
`P = Proj_X(𝒜)` and `Q = Proj_X(ℬ)`, this file states Stacks 085F in one declaration: the open
subspace `U(ψ) ⊆ Q`, the morphism `r_ψ : U(ψ) ⟶ P` over `X` and the map of `ℤ`-graded
`𝒪_{U(ψ)}`-algebras `θ : r_ψ^*(⨁_d 𝒪_P(d)) ⟶ ⨁_d 𝒪_Q(d)|_{U(ψ)}`, their description over the
scheme points of `X` by the triple of Tag 07ZG, and the uniqueness of the three.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapTriple_spec`: Stacks 085F.
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

namespace RelativeProjSituation

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

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
local notation "𝔥" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ
local notation "𝒢" => relativeMapSpace h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- **Stacks 085F.** Let `ψ : 𝒜 ⟶ ℬ` be a map of quasi-coherent graded `𝒪_X`-algebras on an
algebraic space `X`, `P = Proj_X(𝒜)`, `Q = Proj_X(ℬ)`, and `X = U/R` a presentation. Then:
1. `U(ψ) ⊆ Q` is an open subspace, and `r_ψ : U(ψ) ⟶ P` is a morphism over `X`;
2. `θ : r_ψ^*(⨁_d 𝒪_P(d)) ⟶ ι^*(⨁_d 𝒪_Q(d))` is a map of `ℤ`-graded `𝒪_{U(ψ)}`-algebras
   whose degree-`d` component is the glued map `θ_d`, which is, on `U(ψ) ×_X U`, the component
   `θ_d` of Tag 07ZG for `ψ|_U`;
3. over every scheme point `f : T ⟶ X`, `U(ψ) ×_X T` is `U(ψ|_T)` of Tag 07ZG and `r_ψ` there
   is `r_{ψ|_T}`;
4. these properties determine `U(ψ)`, `r_ψ`, the `θ_d` and `θ`. -/
@[stacks 085F "the triple (U(ψ), r_ψ, θ) with θ a map of graded algebras, its description by the \
triple of Tag 07ZG over the scheme points of X, and its uniqueness"]
theorem relativeMapTriple_spec :
    IsOpenSubspace B S hS (𝔥).relativeMapSubfunctor ∧
    (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).hom ≫ (𝔰₁).relativeProjπ =
      (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).hom ≫ (𝔰₂).relativeProjπ ∧
    (∀ n : ℤ, type_of% (twistAlgebraHomOfMul_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px
      (twistMap_mul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px) n)) ∧
    (∀ n : ℤ, type_of% (isDescendedChartHom_twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)) ∧
    (∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) {T' : BigFppfOver B S hS}
      (r : T' ⟶ T) (v : yoneda.obj T' ⟶ (𝔰₂).relativeProjFunctor)
      (hv : v ≫ (𝔰₂).relativeProjπ = yoneda.map r ≫ f),
      type_of% ((𝔥).mem_relativeMapSubfunctor_iff T f r v hv)) ∧
    (∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) {T' : BigFppfOver B S hS}
      (r : T' ⟶ T) (v : yoneda.obj T' ⟶ (𝔰₂).relativeProjFunctor)
      (hv : v ≫ (𝔰₂).relativeProjπ = yoneda.map r ≫ f)
      (hd : IsDefinedOn (𝔰₁).relativeProjPoints (𝔰₂).relativeProjPoints (𝔥).hom T f r v hv)
      (hx : yonedaEquiv v ∈ (𝔥).relativeMapSubfunctor.obj (op T')),
      type_of% ((𝔥).app_relativeMapSpaceHom T f r v hv hd hx)) ∧
    (∀ G : Subfunctor (𝔰₂).relativeProjFunctor,
      type_of% ((𝔥).relativeMapSubfunctor_unique G)) ∧
    (∀ k : (𝔥).relativeMapSubfunctor.toFunctor ⟶ (𝔰₁).relativeProjFunctor,
      type_of% ((𝔥).relativeMapSpaceHom_unique k)) ∧
    (∀ (n : ℤ) (χ : type_of% (twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n)),
      type_of% (eq_twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n (χ := χ))) ∧
    (∀ θ' : SheafOfModules.GradedAlgebra.Hom
        ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
          (Y := smallEtaleRingedTopos B S hS (projSpace₁ h₁c h₁n h₁q h₁k))
          (smallEtaleRingedToposHom B S hS
            (relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
          ((𝔰₁).twistGradedAlgebra Px))
        ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒢)
          (Y := smallEtaleRingedTopos B S hS (projSpace₂ h₂c h₂n h₂q h₂k))
          (smallEtaleRingedToposHom B S hS
            (relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ))).obj
          ((𝔰₂).twistGradedAlgebra Px)),
      type_of% (eq_twistAlgebraHomOfMul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px
        (twistMap_mul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px) θ')) :=
  ⟨isOpenSubspace_homPoints_relativeMapSubfunctor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ,
    relativeMapSpaceMor_comp_π h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ,
    fun n => twistAlgebraHomOfMul_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px
      (twistMap_mul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px) n,
    fun n => isDescendedChartHom_twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n,
    fun T f _ r v hv => (𝔥).mem_relativeMapSubfunctor_iff T f r v hv,
    fun T f _ r v hv hd hx => (𝔥).app_relativeMapSpaceHom T f r v hv hd hx,
    fun G => (𝔥).relativeMapSubfunctor_unique G,
    fun k => (𝔥).relativeMapSpaceHom_unique k,
    fun n χ => eq_twistMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px n (χ := χ),
    fun θ' => eq_twistAlgebraHomOfMul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px
      (twistMap_mul h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px) θ'⟩

end RelativeProjSituation

end AlgebraicGeometry.Space

end
