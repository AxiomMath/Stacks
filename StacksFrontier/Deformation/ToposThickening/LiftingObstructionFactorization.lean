module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Deformation.ToposThickening.LiftingObstructionNecessity
import StacksCore.Tactic.StacksAttribute

/-!
# Step 2 of the proof of Stacks 08UG/08U8: a lift factors the obstruction homomorphism

Step 1 (`StacksFrontier/Deformation/ToposThickening/LiftingObstructionPresentation.lean`) attaches
to a `Deformation.ToposThickening.FirstOrderLiftDiagram` the sheaf of sets `ℰ`, the two algebra
maps `a` and `b` out of `𝒪_{B'₁}[ℰ]`, and the obstruction homomorphism `ξ : ℐ/ℐ² ⟶ g_*𝒢₂`,
pinned by `conormalDescentMap_comp_obstructionConormalHom`. The first half of Step 2
(`StacksFrontier/Deformation/ToposThickening/LiftingObstructionNecessity.lean`) attaches to a lift
`φ` the morphism `θ : NL(α)₀ ⟶ g_*𝒢₂` prescribed on the generator `[x]` by `x₂ - φ(x₁)`.

This file closes Step 2: that `θ` factors `ξ` through the degree `0` term, `d ≫ θ = ±ξ`.

The route is the source's own, with the two reductions kept apart. The source reads `φ` as the
derivation `f' ↦ b(f') - φ(a(f'))` of `𝒪_{B'₁}[ℰ]` over `𝒪_{B'₁}`; that is `liftDerivation`,
built here as an honest `PresheafOfModules.Derivation'`. Its Leibniz rule is the square-zero
cancellation `a · incl m = incl (ā · m)` of the back layer, and it kills the coefficients
because a lift is under the comparison `gB'` of thickened bases. The morphism `θ` also gives a
derivation, of the *reduced* algebra `𝒪_{B₁}[ℰ]`, since the degree `0` term corepresents them
(`Deformation.ToposThickening.FirstOrderLiftDiagram.degreeZeroHomEquivDerivation`); pulled back
along the reduction of coefficients `𝒪_{B'₁}[ℰ] ⟶ 𝒪_{B₁}[ℰ]` that is `baseChangeDerivation`. The
two agree, because a derivation of a free algebra sheaf is determined by its values on the
variables (`Stacks.SheafOfModules.derivation_ext_of_polynomialVariable`) and both take the value
`x₂ - φ(x₁)` on the variable `[x]`. **No descent of derivations is needed:** prescribing on the
generators does not see which of the two coefficient sheaves is used, which is why no comparison
of `Ω_{𝒪_{B'₁}[ℰ]/𝒪_{B'₁}}` with `Ω_{𝒪_{B₁}[ℰ]/𝒪_{B₁}}` appears anywhere.

Evaluating the agreement on a local section of `ℐ'`, and using that `ℐ'/(ℐ')² ↠ ℐ/ℐ²` carries
`ξ` to the difference cocycle of Step 1 in exactly one way, then identifies `d ≫ θ` with `ξ` up
to sign.

## Implementation notes

**The sign.** The source's two halves normalise `ξ` oppositely: its Step 1 describes `ξ` as
`f ↦ ν(a(f')) - b(f')`, the order `frontRestriction - backRestriction` that Step 1 formalises,
while its Step 2 forms the derivation `b - φ ∘ a`, whose restriction to `ℐ'` is
`backRestriction - frontRestriction`. So the `θ` of `liftDegreeZeroHom`, which follows the
Step 2 prose, factors `-ξ` (`reducedDifferential_comp_liftDegreeZeroHom`), and it is its
negative `liftFactorization` that factors `ξ` itself
(`reducedDifferential_comp_liftFactorization`). The latter is the normalisation the source's
Step 3 consumes, since that step builds `b + θ ∘ d` and needs
`θ ∘ d|_{ℐ'} = ν ∘ a|_{ℐ'} - b|_{ℐ'}`.

**Spellings.** Every statement comparing a morphism out of `ℐ'/(ℐ')²` with a
`conormalDifference` is made against an *ascribed* abbreviation (`conormalDifferenceCocycle` of
Step 1, `reducedDifferential` here) rather than against the `conormalDifference` term written
out. The reason is cost, not taste: `pushedIdeal D` is a sheaf of modules over
`Stacks.commRingSheafToRingSheaf D.front.O` while the conormal API is stated over
`underlyingRingSheafOfSite D.front.O`, and although the two are definitionally equal, unifying
the `Preadditive` instances they carry exhausts the heartbeat budget when it has to happen
inside a composite. Ascribing pays it once, at the abbreviation. For the same reason the final
proof folds the sign of `liftFactorization` into its one `conormal_hom_ext` argument instead of
relating two `conormalDifference`s by a separate antisymmetry lemma.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftDerivation`: the derivation `b - φ ∘ a` of
  `𝒪_{B'₁}[ℰ]` over `𝒪_{B'₁}` attached to a lift.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.tensorDerivation`: the derivation of
  `𝒪_{B₁}[ℰ]` corresponding to a morphism out of the degree `0` term of `NL(α)`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.baseChangeDerivation`: the pullback of a
  derivation of `𝒪_{B₁}[ℰ]` along the reduction of coefficients.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.reducedDifferential`: the differential
  `d : ℐ/ℐ² ⟶ NL(α)₀`, the left hand map of the conormal sequence of the reduced presentation.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftFactorization`: the factorization of
  `ξ` through the degree `0` term of `NL(α)` prescribed by a lift.

## Main results

* `Deformation.ToposThickening.FirstOrderLiftDiagram.liftDerivation_eq`: the derivation of a
  lift is the pullback of the derivation of the morphism it prescribes.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.reducedDifferential_comp_liftFactorization`:
  `d ≫ liftFactorization = ξ`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.reducedDifferential_comp_liftDegreeZeroHom`:
  the source's own form of the same statement, `d ≫ θ = -ξ`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.tensorDerivation_d_baseChange_thickIdeal`:
  **the input of Step 3** — for any `θ` with `d ≫ θ = ξ`, the derivation `θ` induces on
  `𝒪_{B'₁}[ℰ]` takes on a local section of `ℐ'` the value `ν(a(x)) - b(x)`. The chain of Step 2
  is run with `θ` free in `tensorDerivation_d_baseChange_eq_apply_conormalClass`, of which
  `liftDerivation_eq` is the instance at `θ = liftDegreeZeroHom`.
* `reduction_backAlgebra_eq_g_reduction_frontAlgebra`, `coefficientMap_comp_frontAlgebra`,
  `coefficientMap_comp_backAlgebra`, `mem_thickIdeal_of_frontAlgebra_eq_incl` and
  `frontIdealSection_of_frontAlgebra_eq_incl`: the remaining compatibilities Step 3 checks at the
  source's own polynomial presentation.

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
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)

/-! ### The derivation `b - φ ∘ a` of `𝒪_{B'₁}[ℰ]` attached to a lift -/

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The difference `b(x) - φ(a(x))` is killed by the reduction of the back layer, so it is the
image of exactly one local section of `𝒢₂`. -/
theorem existsUnique_liftAlgebraSection (p : Lift D) (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    ∃! m : D.back.G.val.obj X,
      D.back.incl m = (backAlgebra D).hom.app X x -
        p.hom.hom.app X ((frontAlgebra D).hom.app X x) := by
  refine D.back.kernelUniversal X _ ?_
  rw [map_sub, reduction_backAlgebra_apply, p.reduction_app _ _, reduction_frontAlgebra_apply,
    sub_self]

/-- The local section `b(x) - φ(a(x))` of `𝒢₂`. -/
def liftAlgebraSection (p : Lift D) (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) : D.back.G.val.obj X :=
  (existsUnique_liftAlgebraSection D p X x).choose

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The defining equation of `liftAlgebraSection`. -/
theorem incl_liftAlgebraSection (p : Lift D) (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    D.back.incl (liftAlgebraSection D p X x) = (backAlgebra D).hom.app X x -
      p.hom.hom.app X ((frontAlgebra D).hom.app X x) :=
  (existsUnique_liftAlgebraSection D p X x).choose_spec.1

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- `liftAlgebraSection` is additive. -/
theorem liftAlgebraSection_add (p : Lift D) (X : Cᵒᵖ)
    (x y : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    liftAlgebraSection D p X (x + y) =
      liftAlgebraSection D p X x + liftAlgebraSection D p X y := by
  refine D.back.incl_injective ?_
  rw [incl_liftAlgebraSection, D.back.incl_add, incl_liftAlgebraSection,
    incl_liftAlgebraSection, map_add, map_add, map_add]
  abel

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- `liftAlgebraSection` sends `0` to `0`. -/
theorem liftAlgebraSection_zero (p : Lift D) (X : Cᵒᵖ) :
    liftAlgebraSection D p X 0 = 0 := by
  refine D.back.incl_injective ?_
  rw [incl_liftAlgebraSection, D.back.incl_zero, map_zero, map_zero, map_zero, sub_zero]

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- `liftAlgebraSection` is compatible with the restriction maps of the site. -/
theorem liftAlgebraSection_map (p : Lift D) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    liftAlgebraSection D p Y
        ((freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.map f x) =
      D.back.G.val.map f (liftAlgebraSection D p X x) := by
  refine D.back.incl_injective ?_
  rw [incl_liftAlgebraSection, D.back.incl_naturality, incl_liftAlgebraSection, map_sub,
    sheafHom_naturality_apply J (backAlgebra D) f x,
    sheafHom_naturality_apply J (frontAlgebra D) f x,
    sheafHom_naturality_apply J p.hom f ((frontAlgebra D).hom.app X x)]

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **The Leibniz rule for `b - φ ∘ a`.** The scalars act on `𝒢₂` through the presentation
followed by the comparison `g`, which is the module structure of `g_*𝒢₂`. -/
theorem liftAlgebraSection_mul (p : Lift D) (X : Cᵒᵖ)
    (x y : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    liftAlgebraSection D p X (x * y) =
      toRingSection J (D.g.hom.app X ((thickenedPresentation D).hom.app X x)) •
          liftAlgebraSection D p X y +
        toRingSection J (D.g.hom.app X ((thickenedPresentation D).hom.app X y)) •
          liftAlgebraSection D p X x := by
  refine D.back.incl_injective ?_
  rw [incl_liftAlgebraSection, D.back.incl_add, map_mul, map_mul, map_mul,
    ← reduction_backAlgebra_apply, ← D.back.mul_incl, incl_liftAlgebraSection]
  rw [show D.g.hom.app X ((thickenedPresentation D).hom.app X y) =
      D.back.reduction.hom.app X (p.hom.hom.app X ((frontAlgebra D).hom.app X y)) by
    rw [p.reduction_app _ _, reduction_frontAlgebra_apply]]
  rw [← D.back.mul_incl, incl_liftAlgebraSection]
  ring

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **The derivation `b - φ ∘ a` vanishes on the coefficients.** The two algebra maps agree on
`𝒪_{B'₁}` because a lift is under the comparison `gB'` of thickened bases. -/
theorem liftAlgebraSection_coefficientMap (p : Lift D) (X : Cᵒᵖ)
    (j : D.front.OB'.obj.obj X) :
    liftAlgebraSection D p X
      ((freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom.app X j) = 0 := by
  have ha := frontAlgebra_app_coefficientMap D X j
  have hb := backAlgebra_app_coefficientMap D X j
  refine D.back.incl_injective ?_
  rw [incl_liftAlgebraSection, D.back.incl_zero, ha, hb, p.base_app _ _, sub_self]

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **The value of `b - φ ∘ a` on a variable** is the value `x₂ - φ(x₁)` of Step 2. -/
theorem liftAlgebraSection_variable (p : Lift D) (X : Cᵒᵖ) (x : D.PairSection X) :
    liftAlgebraSection D p X
        ((freeAlgebraSheafVariable J D.front.OB' (pairPresheaf D)).app X x) =
      liftPairSection D p X x := by
  have ha : (frontAlgebra D).hom.app X
      ((freeAlgebraSheafVariable J D.front.OB' (pairPresheaf D)).app X x) = x.1.1 :=
    congrArg (fun k : pairPresheaf D ⟶ underlyingPresheaf J D.front.O' => k.app X x)
      (freeAlgebraSheafVariable_comp_desc J D.front.OB' D.front.O' (pairPresheaf D)
        D.front.f' (pairFst D))
  have hb : (backAlgebra D).hom.app X
      ((freeAlgebraSheafVariable J D.front.OB' (pairPresheaf D)).app X x) = x.1.2 :=
    congrArg (fun k : pairPresheaf D ⟶ underlyingPresheaf J D.back.O' => k.app X x)
      (freeAlgebraSheafVariable_comp_desc J D.front.OB' D.back.O' (pairPresheaf D)
        (D.gB' ≫ D.back.f') (pairSnd D))
  refine D.back.incl_injective ?_
  rw [incl_liftAlgebraSection, incl_liftPairSection, ha, hb]

/-! ### The two derivations of `𝒪_{B'₁}[ℰ]` -/

/-- `g_*𝒢₂` as a sheaf of modules over `𝒪_{B'₁}[ℰ]`, the scalars acting through the
presentation with thickened coefficients. This is the module both derivations of Step 2 take
their values in. -/
abbrev thickModule : SheafOfModules.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (freeAlgebraSheaf J D.front.OB' (pairPresheaf D))) :=
  (SheafOfModules.pushforward (underlyingRingHomForPullback J
    (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)) D.front.O
    (thickenedPresentation D))).obj (pushedIdeal D)

/-- **The derivation `b - φ ∘ a` of `𝒪_{B'₁}[ℰ]` over `𝒪_{B'₁}` attached to a lift**, which is
the derivation the source's Step 2 reads a morphism filling the diagram as. -/
def liftDerivation (p : Lift D) :
    PresheafOfModulesOfCommRing.Derivation' (thickModule D).val
      (freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom where
  d {X} := AddMonoidHom.mk' (fun x => liftAlgebraSection D p X x) (liftAlgebraSection_add D p X)
  d_mul {X} x y := liftAlgebraSection_mul D p X x y
  d_map {_X _Y} f x := liftAlgebraSection_map D p f x
  d_app {X} j := liftAlgebraSection_coefficientMap D p X j

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The derivation of a lift takes a local section `x` to `liftAlgebraSection D p X x`. -/
@[simp] theorem liftDerivation_d (p : Lift D) (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    (liftDerivation D p).d x = liftAlgebraSection D p X x := rfl

/-- The reduction `𝒪_{B'₁}[ℰ] ⟶ 𝒪_{B₁}[ℰ]` of coefficients, along which the derivation of a
lift descends. -/
abbrev algebraBaseChange : freeAlgebraSheaf J D.front.OB' (pairPresheaf D) ⟶
    freeAlgebraSheaf J D.front.OB (pairPresheaf D) :=
  baseChange J D.front.baseReduction (pairPresheaf D)

/-- `g_*𝒢₂` as a sheaf of modules over `𝒪_{B₁}[ℰ]`, the scalars acting through the reduced
presentation: the module the derivations corresponding to morphisms out of `NL(α)₀` take their
values in. -/
abbrev reducedModule : SheafOfModules.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (freeAlgebraSheaf J D.front.OB (pairPresheaf D))) :=
  (SheafOfModules.pushforward (underlyingRingHomForPullback J
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
    (reducedPresentation D))).obj (pushedIdeal D)

/-- The derivation of `𝒪_{B₁}[ℰ]` over `𝒪_{B₁}` corresponding to a morphism out of the degree
`0` term of `NL(α)`: the degree `0` term corepresents the derivations. -/
def tensorDerivation (θ : reducedDegreeZero D ⟶ pushedIdeal D) :
    PresheafOfModulesOfCommRing.Derivation' (reducedModule D).val
      (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D)).hom :=
  degreeZeroHomEquivDerivation D (pushedIdeal D) θ

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The derivation corresponding to `θ` takes a local section `y` to the value of `θ` on
`1 ⊗ d y`. -/
theorem tensorDerivation_d (θ : reducedDegreeZero D ⟶ pushedIdeal D) (X : Cᵒᵖ)
    (y : (freeAlgebraSheaf J D.front.OB (pairPresheaf D)).obj.obj X) :
    (tensorDerivation D θ).d y = θ.val.app X (reducedTensorDifferential D X y) :=
  degreeZeroHomEquivDerivation_d D (pushedIdeal D) θ X y

section BaseChangeDerivation

variable (Θ : PresheafOfModulesOfCommRing.Derivation' (reducedModule D).val
  (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D)).hom)

/-- The value of the pullback along the reduction of coefficients of a derivation of
`𝒪_{B₁}[ℰ]`. -/
def baseChangeDerivationFun (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) : D.back.G.val.obj X :=
  Θ.d ((algebraBaseChange D).hom.app X x)

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- `baseChangeDerivationFun` is additive. -/
theorem baseChangeDerivationFun_add (X : Cᵒᵖ)
    (x y : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    baseChangeDerivationFun D Θ X (x + y) =
      baseChangeDerivationFun D Θ X x + baseChangeDerivationFun D Θ X y :=
  (congrArg (fun t => Θ.d t) (map_add ((algebraBaseChange D).hom.app X).hom x y)).trans
    (map_add Θ.d _ _)

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- `baseChangeDerivationFun` commutes with restriction along a morphism `f : X ⟶ Y`. -/
theorem baseChangeDerivationFun_map {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    baseChangeDerivationFun D Θ Y
        ((freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.map f x) =
      D.back.G.val.map f (baseChangeDerivationFun D Θ X x) :=
  (congrArg (fun t => Θ.d t)
    (sheafHom_naturality_apply J (algebraBaseChange D) f x)).trans (Θ.d_map f _)

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- `baseChangeDerivationFun` vanishes on the image of the coefficients `𝒪_{B'₁}`. -/
theorem baseChangeDerivationFun_coefficientMap (X : Cᵒᵖ) (j : D.front.OB'.obj.obj X) :
    baseChangeDerivationFun D Θ X
      ((freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom.app X j) = 0 :=
  (congrArg (fun t => Θ.d t)
    (congrArg (fun k : D.front.OB' ⟶ freeAlgebraSheaf J D.front.OB (pairPresheaf D) =>
        k.hom.app X j)
      (freeAlgebraSheafCoefficientMap_comp_baseChange J D.front.baseReduction
        (pairPresheaf D)))).trans (Θ.d_app _)

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The Leibniz rule for `baseChangeDerivationFun`, the scalars acting through the thickened
presentation. -/
theorem baseChangeDerivationFun_mul (X : Cᵒᵖ)
    (x y : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    baseChangeDerivationFun D Θ X (x * y) =
      toRingSection J (D.g.hom.app X ((thickenedPresentation D).hom.app X x)) •
          baseChangeDerivationFun D Θ X y +
        toRingSection J (D.g.hom.app X ((thickenedPresentation D).hom.app X y)) •
          baseChangeDerivationFun D Θ X x := by
  rw [restrictedPresentation_app_apply J D.front.baseReduction (pairPresheaf D) D.front.f
      (pairAlpha D) X x,
    restrictedPresentation_app_apply J D.front.baseReduction (pairPresheaf D) D.front.f
      (pairAlpha D) X y]
  exact (congrArg (fun t => Θ.d t) (map_mul ((algebraBaseChange D).hom.app X).hom x y)).trans
    (Θ.d_mul _ _)

/-- **The pullback of a derivation of `𝒪_{B₁}[ℰ]` along the reduction of coefficients.** No
descent of derivations is involved: a derivation of the reduced algebra precomposed with the
reduction of coefficients is a derivation of the thickened one, because that reduction is a
homomorphism of algebras carrying `𝒪_{B'₁}` into `𝒪_{B₁}`. -/
def baseChangeDerivation :
    PresheafOfModulesOfCommRing.Derivation' (thickModule D).val
      (freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom where
  d {X} := AddMonoidHom.mk' (fun x => baseChangeDerivationFun D Θ X x)
    (baseChangeDerivationFun_add D Θ X)
  d_mul {X} x y := baseChangeDerivationFun_mul D Θ X x y
  d_map {_X _Y} f x := baseChangeDerivationFun_map D Θ f x
  d_app {X} j := baseChangeDerivationFun_coefficientMap D Θ X j

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The pullback of `Θ` takes a local section `x` to the value of `Θ` on its reduction. -/
@[simp] theorem baseChangeDerivation_d (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    (baseChangeDerivation D Θ).d x = Θ.d ((algebraBaseChange D).hom.app X x) := rfl

end BaseChangeDerivation

/-! ### The two derivations agree -/

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The reduction of coefficients is the identity on the variables, in the form the agreement of
the two derivations on the generators needs. -/
theorem algebraBaseChange_variable (X : Cᵒᵖ) (x : D.PairSection X) :
    (algebraBaseChange D).hom.app X
        ((freeAlgebraSheafVariable J D.front.OB' (pairPresheaf D)).app X x) =
      (freeAlgebraSheafVariable J D.front.OB (pairPresheaf D)).app X x :=
  congrArg
    (fun k : pairPresheaf D ⟶
        underlyingPresheaf J (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) => k.app X x)
    (freeAlgebraSheafVariable_comp_baseChange J D.front.baseReduction (pairPresheaf D))

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **The derivation of a lift is the pullback of the derivation of the prescribed morphism out
of `NL(α)₀`.** Both are derivations of `𝒪_{B'₁}[ℰ]` over `𝒪_{B'₁}`, and a derivation of a free
algebra sheaf is determined by its values on the variables; on the variable `[x]` both take the
value `x₂ - φ(x₁)`, by `liftAlgebraSection_variable` and by `liftDegreeZeroHom_generator`. This
is the step at which the thickened data discharges itself against the reduced one: prescribing
on the generators does not see which of the two coefficient sheaves is used. -/
theorem liftDerivation_eq (p : Lift D) :
    liftDerivation D p =
      baseChangeDerivation D (tensorDerivation D (liftDegreeZeroHom D p)) := by
  have hsurj : Presheaf.IsLocallySurjective J ((toSheafification J CommRingCat.{max u v w}).app
      (polynomialPresheaf J D.front.OB' (pairPresheaf D))) :=
    (J.W_toSheafify _).isLocallySurjective
  refine Stacks.SheafOfModules.derivation_ext_of_polynomialVariable J D.front.OB'
    (pairPresheaf D) ((toSheafification J CommRingCat.{max u v w}).app
      (polynomialPresheaf J D.front.OB' (pairPresheaf D))) rfl (thickModule D) _ _
    (fun X e => ?_)
  have h2 : (tensorDerivation D (liftDegreeZeroHom D p)).d
      ((freeAlgebraSheafVariable J D.front.OB (pairPresheaf D)).app X e) =
      liftPairSection D p X e :=
    (tensorDerivation_d D (liftDegreeZeroHom D p) X _).trans
      (liftDegreeZeroHom_generator D p X e)
  exact (liftAlgebraSection_variable D p X e).trans
    ((congrArg (fun t => (tensorDerivation D (liftDegreeZeroHom D p)).d t)
      (algebraBaseChange_variable D X e)).trans h2).symm

/-! ### The factorization of `ξ` -/

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **The value of the derivation `b - φ ∘ a` on a local section of `ℐ'`.** It is the difference
of the two restriction data of Step 1, in the order `b|_{ℐ'} - ν ∘ a|_{ℐ'}`: the compatibility of
a lift with `ν` is what turns `φ(a(x))` into `ν(a(x))`. -/
theorem liftAlgebraSection_thickIdeal (p : Lift D) (X : Cᵒᵖ) (x : D.thickIdeal X) :
    liftAlgebraSection D p X x.1 =
      backIdealSection D X x - D.nuSection (frontIdealSection D X x) := by
  refine D.back.incl_injective ?_
  rw [incl_liftAlgebraSection, D.back.incl_sub, incl_backIdealSection,
    show p.hom.hom.app X ((frontAlgebra D).hom.app X x.1) =
        D.back.incl (D.nuSection (frontIdealSection D X x)) by
      rw [← incl_frontIdealSection, p.kernel_comm]]

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The two restriction data of Step 1 are `ν ∘ a|_{ℐ'}` and `b|_{ℐ'}` by definition. -/
theorem frontRestriction_sub_backRestriction_app (X : Cᵒᵖ) (x : D.thickIdeal X) :
    (frontRestriction D).app X x - (backRestriction D).app X x =
      D.nuSection (frontIdealSection D X x) - backIdealSection D X x := rfl

/-- The differential `d : ℐ/ℐ² ⟶ NL(α)₀` of the source's Step 2, the left hand map of the
conormal sequence of the reduced presentation of Step 1. -/
abbrev reducedDifferential : reducedConormal D ⟶ reducedDegreeZero D :=
  (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, max u v w} J
    D.front.OB D.front.O D.front.f (pairPresheaf D) (pairAlpha D)).f

/-- **The factorization of `ξ` through the degree `0` term of `NL(α)` prescribed by a lift.** On
the generator `[x]` attached to a local section `x = (x₁, x₂)` of `ℰ` it takes the value
`φ(x₁) - x₂`.

The sign is the source's own, and the two halves of its proof normalise `ξ` oppositely: its
Step 1 describes `ξ` as `f ↦ ν(a(f')) - b(f')`, while its Step 2 forms the derivation
`b - φ ∘ a`, whose restriction to `ℐ'` is `b|_{ℐ'} - ν ∘ a|_{ℐ'}`. This is the normalisation
that factors `ξ` itself, hence the one the source's Step 3 — which builds `b + θ ∘ d` —
consumes. -/
def liftFactorization (p : Lift D) : reducedDegreeZero D ⟶ pushedIdeal D :=
  -liftDegreeZeroHom D p

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- `liftFactorization D p` is the negative of `liftDegreeZeroHom D p`. -/
theorem liftFactorization_eq_neg (p : Lift D) :
    liftFactorization D p = -liftDegreeZeroHom D p := rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The value of `liftFactorization D p` on a local section is the negative of the value of
`liftDegreeZeroHom D p`. -/
theorem liftFactorization_app (p : Lift D) (X : Cᵒᵖ)
    (t : (reducedDegreeZero D).val.obj X) :
    (liftFactorization D p).val.app X t = -((liftDegreeZeroHom D p).val.app X t) := rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **The morphism prescribed by a lift factors the difference cocycle of Step 1.** Pulled back
along `ℐ'/(ℐ')² ↠ ℐ/ℐ²` the composite `d ≫ liftFactorization` is the difference cocycle
`ν ∘ a|_{ℐ'} - b|_{ℐ'}`: the conormal class of a local section `x` of `ℐ'` goes to the class of
its image in `ℐ`, then to `1 ⊗ d x̄`, where `liftDegreeZeroHom` takes the value of its
derivation, which `liftDerivation_eq` identifies with `b(x) - φ(a(x))`; the sign of
`liftFactorization` turns that into `ν(a(x)) - b(x)`. -/
theorem conormalDescentMap_comp_reducedDifferential_comp_liftFactorization (p : Lift D) :
    conormalDescentMap D ≫ reducedDifferential D ≫ liftFactorization D p =
      conormalDifferenceCocycle D := by
  refine conormal_hom_ext.{v, u, max u v w, max u v w} (thickenedPresentation D)
    (pushedIdeal D) (fun X x => ?_)
  have hA := presentationConormalMap_conormalClass.{v, u, max u v w, max u v w} J
    D.front.baseReduction (pairPresheaf D) D.front.f (pairAlpha D) X x
  have hB := conormalSequence_f_class.{v, u, max u v w, max u v w} J D.front.OB
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
    (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D)) (reducedPresentation D) X
    ⟨(algebraBaseChange D).hom.app X x.1,
      baseChange_mem_basePresentationIdeal J D.front.baseReduction (pairPresheaf D) D.front.f
        (pairAlpha D) X x⟩
  have hC := (tensorDerivation_d D (liftDegreeZeroHom D p) X
    ((algebraBaseChange D).hom.app X x.1)).symm
  have hD := congrArg (fun Θ => Θ.d (X := X) x.1) (liftDerivation_eq D p)
  have hE := liftAlgebraSection_thickIdeal D p X x
  have hR := conormalDifference_toAssociatedModule.{v, u, max u v w, max u v w}
    (thickenedPresentation D) (pushedIdeal D) (frontRestriction D) (backRestriction D) X x
  have chain := (congrArg (fun t => (liftDegreeZeroHom D p).val.app X
      ((reducedDifferential D).val.app X t)) hA).trans
    ((congrArg (fun t => (liftDegreeZeroHom D p).val.app X t) hB).trans
      (hC.trans (hD.symm.trans hE)))
  refine Eq.trans ((liftFactorization_app D p X _).trans (congrArg Neg.neg chain)) ?_
  refine Eq.trans (neg_sub _ _) ?_
  exact ((frontRestriction_sub_backRestriction_app D X x).trans
    (congrArg₂ (· - ·) rfl rfl)).symm.trans hR.symm

/-- **Step 2 of the proof of [Stacks Project, Tag 08U8] is complete:** a morphism filling the
source's diagram compatibly with `ν` prescribes a factorization of the obstruction homomorphism
`ξ` of Step 1 through the degree `0` term of `NL(α)`. Together with Step 3 this is the content
carried by the hypothesis `e` of
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff`. -/
theorem reducedDifferential_comp_liftFactorization (p : Lift D) :
    reducedDifferential D ≫ liftFactorization D p = obstructionConormalHom D :=
  (existsUnique_obstructionConormalHom D).choose_spec.2 _
    (conormalDescentMap_comp_reducedDifferential_comp_liftFactorization D p)

/-- The source's own Step 2 statement, with its own sign: the morphism prescribed on the
generators by `x₂ - φ(x₁)` factors `-ξ`. -/
theorem reducedDifferential_comp_liftDegreeZeroHom (p : Lift D) :
    reducedDifferential D ≫ liftDegreeZeroHom D p = -obstructionConormalHom D := by
  have h := reducedDifferential_comp_liftFactorization D p
  rw [liftFactorization_eq_neg, Preadditive.comp_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-! ### The input of Step 3: a factorization of `ξ`, evaluated on `ℐ'` -/

section Sufficiency

variable (θ : reducedDegreeZero D ⟶ pushedIdeal D)

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **The chain of Step 2, with the morphism out of the degree `0` term left free.** The
derivation `θ` induces on `𝒪_{B'₁}[ℰ]` takes on a local section `x` of `ℐ'` the value of
`d ≫ θ` on the conormal class of `x`: the class of `x` in `ℐ'/(ℐ')²` goes to the class of its
image in `ℐ/ℐ²`, then `d` carries that to `1 ⊗ d x̄`, where `θ` takes the value of its own
derivation. Nothing about a lift enters; `liftDerivation_eq` is the instance of this at
`θ = liftDegreeZeroHom`. -/
theorem tensorDerivation_d_baseChange_eq_apply_conormalClass (X : Cᵒᵖ) (x : D.thickIdeal X) :
    (tensorDerivation D θ).d ((algebraBaseChange D).hom.app X x.1) =
      (conormalDescentMap D ≫ reducedDifferential D ≫ θ).val.app X
        (conormalClass.{v, u, max u v w, max u v w} J D.front.OB'
          (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)) D.front.O
          (freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D))
          (thickenedPresentation D) X x) := by
  have hA := presentationConormalMap_conormalClass.{v, u, max u v w, max u v w} J
    D.front.baseReduction (pairPresheaf D) D.front.f (pairAlpha D) X x
  have hB := conormalSequence_f_class.{v, u, max u v w, max u v w} J D.front.OB
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O
    (freeAlgebraSheafCoefficientMap J D.front.OB (pairPresheaf D)) (reducedPresentation D) X
    ⟨(algebraBaseChange D).hom.app X x.1,
      baseChange_mem_basePresentationIdeal J D.front.baseReduction (pairPresheaf D) D.front.f
        (pairAlpha D) X x⟩
  have hC := (tensorDerivation_d D θ X ((algebraBaseChange D).hom.app X x.1)).symm
  exact (((congrArg (fun t => θ.val.app X ((reducedDifferential D).val.app X t)) hA).trans
    (congrArg (fun t => θ.val.app X t) hB)).trans hC).symm

/-- **The input of Step 3 of the proof of [Stacks Project, Tag 08U8].** If `θ` factors the
obstruction homomorphism `ξ` of Step 1 through the degree `0` term of `NL(α)`, then the
derivation it induces on `𝒪_{B'₁}[ℰ]` takes on a local section `x` of `ℐ'` exactly the value
`ν(a(x)) - b(x)`.

This is the sentence Step 3 needs in order to twist `b` into an algebra map agreeing with
`ν ∘ a|_{ℐ'}` on `ℐ'`: the twist `b + θ ∘ d` sends `x` to
`b(x) + (ν(a(x)) - b(x)) = ν(a(x))`. The normalisation is `liftFactorization`'s, not
`liftDegreeZeroHom`'s — the source's two halves spell `ξ` with opposite signs, and it is this
one that makes the twist work. -/
theorem tensorDerivation_d_baseChange_thickIdeal
    (hθ : reducedDifferential D ≫ θ = obstructionConormalHom D) (X : Cᵒᵖ)
    (x : D.thickIdeal X) :
    (tensorDerivation D θ).d ((algebraBaseChange D).hom.app X x.1) =
      D.nuSection (frontIdealSection D X x) - backIdealSection D X x := by
  have hfac : conormalDescentMap D ≫ reducedDifferential D ≫ θ =
      conormalDifferenceCocycle D := by
    rw [hθ]
    exact conormalDescentMap_comp_obstructionConormalHom D
  have hval := congrArg (fun k : conormalSheaf.{v, u, max u v w, max u v w} J
      (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)) D.front.O
      (thickenedPresentation D) ⟶ pushedIdeal D =>
    k.val.app X (conormalClass.{v, u, max u v w, max u v w} J D.front.OB'
      (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)) D.front.O
      (freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D))
      (thickenedPresentation D) X x)) hfac
  have hR := conormalDifference_toAssociatedModule.{v, u, max u v w, max u v w}
    (thickenedPresentation D) (pushedIdeal D) (frontRestriction D) (backRestriction D) X x
  exact ((tensorDerivation_d_baseChange_eq_apply_conormalClass D θ X x).trans hval).trans hR

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **`hred` for the source's own presentation:** `b` reduces to `α` followed by `g`, and `a`
reduces to `α`, so `b` is over `g ∘ (reduction ∘ a)`. -/
theorem reduction_backAlgebra_eq_g_reduction_frontAlgebra (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    D.back.reduction.hom.app X ((backAlgebra D).hom.app X x) =
      D.g.hom.app X (D.front.reduction.hom.app X ((frontAlgebra D).hom.app X x)) := by
  rw [reduction_backAlgebra_apply, reduction_frontAlgebra_apply]

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **`hc` for the source's own presentation:** the coefficient map followed by `a` is the
structure map of the front thickened square. -/
theorem coefficientMap_comp_frontAlgebra :
    freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D) ≫ frontAlgebra D =
      D.front.f' :=
  freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.front.O' (pairPresheaf D)
    D.front.f' (pairFst D)

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The coefficient map followed by `b` is the comparison of thickened bases followed by the
structure map of the back thickened square: the half of `hbase` that does not involve the
derivation. -/
theorem coefficientMap_comp_backAlgebra :
    freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D) ≫ backAlgebra D =
      D.gB' ≫ D.back.f' :=
  freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.back.O' (pairPresheaf D)
    (D.gB' ≫ D.back.f') (pairSnd D)

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **A local section of `𝒪_{B'₁}[ℰ]` carried by `a` into the ideal `𝒢₁` lies in `ℐ'`.** This is
the hypothesis of `hideal`, half turned into what Step 3 uses. -/
theorem mem_thickIdeal_of_frontAlgebra_eq_incl (X : Cᵒᵖ) (m : D.front.G.val.obj X)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X)
    (hx : (frontAlgebra D).hom.app X x = D.front.incl m) :
    x ∈ D.thickIdeal X :=
  RingHom.mem_ker.mpr (by
    rw [← reduction_frontAlgebra_apply, hx, D.front.reduction_incl])

omit [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **And `a|_{ℐ'}` then recovers the section of `𝒢₁` it was carried to**, by injectivity of the
ideal inclusion. This is the other half of the hypothesis of `hideal`. -/
theorem frontIdealSection_of_frontAlgebra_eq_incl (X : Cᵒᵖ) (m : D.front.G.val.obj X)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X)
    (hx : (frontAlgebra D).hom.app X x = D.front.incl m) :
    frontIdealSection D X ⟨x, mem_thickIdeal_of_frontAlgebra_eq_incl D X m x hx⟩ = m :=
  D.front.incl_injective ((incl_frontIdealSection D X _).trans hx)

end Sufficiency

end Deformation.ToposThickening.FirstOrderLiftDiagram

end
