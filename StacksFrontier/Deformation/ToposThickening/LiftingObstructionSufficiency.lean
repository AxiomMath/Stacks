module

public import StacksFrontier.Deformation.ToposThickening.LiftingObstructionPushout
public import StacksFrontier.Deformation.ToposThickening.LiftFromPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Step 3 of the proof of Stacks 08UG/08U8 at the source's own presentation

`StacksFrontier/Deformation/ToposThickening/LiftFromPresentation.lean` carries out Step 3 of the
proof of [Stacks Project, Tag 08U8] for an *arbitrary* presentation of the front thickened
structure sheaf: a locally surjective `a : ℛ ⟶ 𝒪_{X'₁}`, a homomorphism `b : ℛ ⟶ 𝒪_{X'₂}`, a
derivation `δ` of `ℛ` into `𝒢₂` along `b`, and three compatibilities give a
`Deformation.ToposThickening.FirstOrderLiftDiagram.Lift`.

This file instantiates it at the source's own presentation `ℛ = 𝒪_{B'₁}[ℰ]` with the two algebra
maps `a` and `b` of Step 1 and `δ = θ ∘ d` for a factorization `θ` of the obstruction
homomorphism `ξ`, which closes Step 3 and so makes the morphisms filling the source's diagram
exactly the factorizations of `ξ` through the degree `0` term of `NL(α)`.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram.twistDerivation`: `θ ∘ d`, as a
  `Deformation.ToposThickening.SectionwiseDerivation` of the back layer along `b`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftOfFactorization`: **the morphism
  `X'₂ ⟶ X'₁` attached to a factorization of `ξ`**, which is Step 3.

## Main results

* `Deformation.ToposThickening.FirstOrderLiftDiagram.twist_backAlgebra_thickIdeal`: the hypothesis
  `hideal` — on the ideal `ℐ'` of the presentation the twist `b + θ ∘ d` takes the value
  `ν ∘ a`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.nonempty_lift_iff_exists_factorization`:
  **Steps 2 and 3 together** — a morphism filling the source's diagram compatibly with `ν` exists
  if and only if `ξ` factors through the degree `0` term of `NL(α)`. This is the content that
  `AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff` used to assume as its
  hypothesis `e`.

## Implementation notes

**The four hypotheses of `liftOfTwist`, and where each comes from.**

* Local surjectivity of `a = frontAlgebra D` is `isLocallySurjective_frontAlgebra`
  (`LiftingObstructionPushout.lean`), through local surjectivity of the first projection
  `ℰ ⟶ 𝒪_{X'₁}`. It is *not* `isLocallySurjective_pairAlpha`, which is about the reduced
  `𝒪_{X₁}` and gives local surjectivity of `thickenedPresentation` instead.
* `hc` is `coefficientMap_comp_frontAlgebra` and `hred` is
  `reduction_backAlgebra_eq_g_reduction_frontAlgebra`, both read off the construction of `a` and
  `b` in Step 1.
* `hbase` is `twist_backAlgebra_coefficientMap`: the twist agrees with `b` on the coefficients
  because the derivation `θ ∘ d` kills them, and `b` on the coefficients is `gB'` followed by
  the structure map of the back layer.
* `hideal` is `twist_backAlgebra_thickIdeal`, and it is the only one with content. It rests on
  `tensorDerivation_d_baseChange_thickIdeal`
  (`LiftingObstructionFactorization.lean`): `d ≫ θ = ξ` says exactly that `θ ∘ d` takes the
  value `ν(a(x)) - b(x)` on a local section `x` of `ℐ'`, so the twist takes the value
  `b(x) + (ν(a(x)) - b(x)) = ν(a(x))`. The sign is `liftFactorization`'s and not
  `liftDegreeZeroHom`'s; with the other normalisation the twist would be `b - θ ∘ d`.

**`θ ∘ d` is a derivation along `b`, not along `a`.** The degree `0` term of `NL(α)` is a module
over the *reduced* structure sheaf `𝒪_{X₁}`, and the Leibniz rule the twist needs — that of a
`SectionwiseDerivation` whose scalar map is `b` followed by `𝒪_{X'₂} ⟶ 𝒪_{X₂}` — wants its
scalars through `𝒪_{X'₂} ⟶ 𝒪_{X₂}` applied to `b`. Those agree because `b` reduces to `α`
followed by `g` (`reduction_backAlgebra_apply`), which is exactly the module structure
`baseChangeDerivationFun_mul` already produces. No comparison of
`Ω_{𝒪_{B'₁}[ℰ]/𝒪_{B'₁}}` with `Ω_{𝒪_{B₁}[ℰ]/𝒪_{B₁}}` is needed here either.

**The extra instance.** `[J.HasSheafCompose (forget CommRingCat)]` is assumed in addition to the
instances a `FirstOrderLiftDiagram` already carries. It is what `LiftFromPresentation.lean`
needs for the universe-unrestricted sheaf condition on sections, used to compare the two sides of
`kernel_comm` on the image sieve of the only locally surjective `a`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.FreeAlgebra
open Stacks.Sites.Conormal

universe v u w

namespace Deformation.ToposThickening.FirstOrderLiftDiagram

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.HasSheafCompose (forget CommRingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)
  (θ : reducedDegreeZero D ⟶ pushedIdeal D)

/-! ### `θ ∘ d` as a derivation of `𝒪_{B'₁}[ℰ]` into `𝒢₂` along `b` -/

/-- **The derivation `θ ∘ d` of `𝒪_{B'₁}[ℰ]` into `𝒢₂` along `b`.** Its value on a local
section is the value of the derivation `θ` corresponds to, taken after the reduction of
coefficients; the Leibniz rule is the one `baseChangeDerivationFun_mul` proves, whose scalars
act through the presentation followed by `g` and so through the reduction of `b`. -/
def twistDerivation :
    SectionwiseDerivation (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)) D.back.G
      (backAlgebra D ≫ D.back.reduction) where
  toFun U x := baseChangeDerivationFun D (tensorDerivation D θ) U x
  map_add' U x y := baseChangeDerivationFun_add D (tensorDerivation D θ) U x y
  naturality h x := baseChangeDerivationFun_map D (tensorDerivation D θ) h x
  leibniz U x y := by
    simp only [sheafHom_comp_apply]
    rw [reduction_backAlgebra_apply, reduction_backAlgebra_apply]
    exact baseChangeDerivationFun_mul D (tensorDerivation D θ) U x y

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})] in
/-- The value of `twistDerivation D θ` on a local section `x` is the derivation
`tensorDerivation D θ` applied to the image of `x` under `algebraBaseChange D`. -/
@[simp] theorem twistDerivation_toFun (U : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj U) :
    (twistDerivation D θ).toFun U x =
      (tensorDerivation D θ).d ((algebraBaseChange D).hom.app U x) := rfl

/-! ### The three compatibilities -/

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})] in
/-- **`hbase`: the twist agrees with `gB'` followed by the structure map of the back layer on
the coefficients.** The derivation `θ ∘ d` kills the coefficients of the free algebra sheaf, so
the twist is `b` there, and `b` on the coefficients is the comparison of thickened bases
followed by the structure map of the back layer. -/
theorem twist_backAlgebra_coefficientMap (U : Cᵒᵖ) (t : D.front.OB'.obj.obj U) :
    (D.back.twist (backAlgebra D) (twistDerivation D θ)).hom.app U
        ((freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom.app U t) =
      D.back.f'.hom.app U (D.gB'.hom.app U t) := by
  rw [LiftSquare.twist_apply,
    show (twistDerivation D θ).toFun U
        ((freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom.app U t) = 0 from
      baseChangeDerivationFun_coefficientMap D (tensorDerivation D θ) U t,
    D.back.incl_zero, add_zero]
  exact congrArg (fun k : D.front.OB' ⟶ D.back.O' => k.hom.app U t)
    (coefficientMap_comp_backAlgebra D)

omit [J.HasSheafCompose (forget CommRingCat.{max u v w})] in
/-- **`hideal`: on the ideal `ℐ'` of the presentation the twist `b + θ ∘ d` takes the value
`ν ∘ a`.** This is the content of Step 3. A local section `x` of `𝒪_{B'₁}[ℰ]` carried by `a`
into the ideal `𝒢₁` lies in `ℐ'` and has `a|_{ℐ'}(x)` the section of `𝒢₁` it was carried to; on
`ℐ'` the derivation `θ ∘ d` takes the value `ν(a(x)) - b(x)` because `d ≫ θ = ξ` and `ξ` is
pinned as the difference of the two restriction data of Step 1; and `b(x)` is the image of
`b|_{ℐ'}(x)`. The two `b`-terms cancel. -/
theorem twist_backAlgebra_thickIdeal
    (hθ : reducedDifferential D ≫ θ = obstructionConormalHom D)
    (U : Cᵒᵖ) (m : D.front.G.val.obj U)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj U)
    (hx : (frontAlgebra D).hom.app U x = D.front.incl m) :
    (D.back.twist (backAlgebra D) (twistDerivation D θ)).hom.app U x =
      D.back.incl (D.nuSection m) := by
  have hmem := mem_thickIdeal_of_frontAlgebra_eq_incl D U m x hx
  have hval : (twistDerivation D θ).toFun U x =
      D.nuSection m - backIdealSection D U ⟨x, hmem⟩ := by
    refine (tensorDerivation_d_baseChange_thickIdeal D θ hθ U ⟨x, hmem⟩).trans ?_
    rw [frontIdealSection_of_frontAlgebra_eq_incl D U m x hx]
  rw [LiftSquare.twist_apply, hval,
    show (backAlgebra D).hom.app U x = D.back.incl (backIdealSection D U ⟨x, hmem⟩) from
      (incl_backIdealSection D U ⟨x, hmem⟩).symm,
    ← D.back.incl_add]
  exact congrArg D.back.incl (by abel)

/-! ### Step 3 -/

/-- **Step 3 of the proof of [Stacks Project, Tag 08U8]: a factorization of `ξ` through the
degree `0` term of `NL(α)` produces a morphism `X'₂ ⟶ X'₁` fitting into the source's diagram
compatibly with `ν`.** The source twists `b` by `θ ∘ d` and descends along the presentation `a`,
which is possible because the twist agrees with `ν ∘ a` on the ideal of the presentation
(`twist_backAlgebra_thickIdeal`) and `𝒪_{X'₁}` is generated by `𝒪_{B'₁}[ℰ]` locally
(`isLocallySurjective_frontAlgebra`). -/
def liftOfFactorization (hθ : reducedDifferential D ≫ θ = obstructionConormalHom D) : Lift D :=
  liftOfTwist D (frontAlgebra D) (backAlgebra D) (twistDerivation D θ)
    (freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D))
    (twist_backAlgebra_thickIdeal D θ hθ)
    (coefficientMap_comp_frontAlgebra D)
    (reduction_backAlgebra_eq_g_reduction_frontAlgebra D)
    (twist_backAlgebra_coefficientMap D θ)

/-- The morphism built by Step 3 restricts along the presentation to the twist `b + θ ∘ d`,
which is what pins it down. -/
theorem frontAlgebra_comp_liftOfFactorization
    (hθ : reducedDifferential D ≫ θ = obstructionConormalHom D) :
    frontAlgebra D ≫ (liftOfFactorization D θ hθ).hom =
      D.back.twist (backAlgebra D) (twistDerivation D θ) :=
  liftOfTwist_comp D _ _ _ _ _ _ _ _

/-- **Steps 2 and 3 of the proof of [Stacks Project, Tag 08U8], together.** A morphism
`X'₂ ⟶ X'₁` fitting into the source's diagram compatibly with `ν` exists if and only if the
obstruction homomorphism `ξ` of Step 1 factors through the degree `0` term of `NL(α)`.

Step 2 (`reducedDifferential_comp_liftFactorization`) is the forward direction and Step 3
(`liftOfFactorization`) the backward one. This is exactly the content that clause (1) of the
source needs, and that
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff` would otherwise have to
assume. -/
theorem nonempty_lift_iff_exists_factorization :
    Nonempty (Lift D) ↔
      ∃ θ : reducedDegreeZero D ⟶ pushedIdeal D,
        reducedDifferential D ≫ θ = obstructionConormalHom D := by
  constructor
  · rintro ⟨p⟩
    exact ⟨liftFactorization D p, reducedDifferential_comp_liftFactorization D p⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨liftOfFactorization D θ hθ⟩

end Deformation.ToposThickening.FirstOrderLiftDiagram

end
