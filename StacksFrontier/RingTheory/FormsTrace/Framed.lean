module

public import StacksFrontier.RingTheory.FormsTrace.Comparison
public import StacksFrontier.RingTheory.FormsTrace.UniversalComparison

/-!
# Trace maps on forms of framed finite syntomic algebras

A *frame* of a finite free `A`-algebra `B` of rank `d ≥ 1` is a basis `e` of `B` over `A` with
`e 0 = 1`, together with a syntomic-good element `g` of the universal ring `A_d` whose image under
the classifying map of `e` is a unit of `A` (`Stacks.FormsTrace.ChartFrame`). A frame presents
`B/A` as a base change of the universal chart: with `R = N_g[x_a : a ∈ A]`, the evaluation
`R → A` (`x_a ↦ a`, and the chart `N_g → A` on coefficients) is surjective, and `B` is the base
change along it of the base change `B_R` of the universal family to `R`.

Given a family `Θ_R` on the forms of `B_R` with property (1) of Stacks, Lemma 0FLB, it is
automatically linear over the forms of `R` (the discriminant is a nice element, Tag 0FLC), so it
descends along `R → A` (`Stacks.FormsTrace.descendForms`) to the *framed trace* `Θ_A` on the forms
of `B`.

## Main definitions

* `Stacks.FormsTrace.ChartFrame`: a frame of `B/A`.
* `Stacks.FormsTrace.ChartFrame.eval`, `Stacks.FormsTrace.ChartFrame.carrierMap`: the maps
  `R → A` and `B_R → B` of the presentation, and the algebra structures
  `Stacks.FormsTrace.ChartFrame.algebraChart`, `Stacks.FormsTrace.ChartFrame.algebraCarrier`,
  `Stacks.FormsTrace.ChartFrame.algebraChartTarget` making it a pushout square.
* `Stacks.FormsTrace.ChartFrame.framedTrace`: the descended trace maps.

## Main results

* `Stacks.FormsTrace.ChartFrame.eval_surjective`, `Stacks.FormsTrace.ChartFrame.isPushout`.
* `Stacks.FormsTrace.ChartFrame.framedTrace_formsMap`: `Θ_A(η|_B) = Θ_R(η)|_A`.
* `Stacks.FormsTrace.ChartFrame.isFormsTrace_framedTrace`,
  `Stacks.FormsTrace.ChartFrame.isWedgeLinear_framedTrace`,
  `Stacks.FormsTrace.ChartFrame.commutesWithD_framedTrace`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FL4](https://stacks.math.columbia.edu/tag/0FL4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra
open scoped TensorProduct nonZeroDivisors

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

/-- **A frame** of a finite free `A`-algebra `B` of rank `d`: a basis `e` with first vector `1`
and a syntomic-good `g ∈ A_d` whose image under the classifying map of `e` is a unit. -/
structure ChartFrame (d : ℕ) [NeZero d] (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] where
  /-- The basis. -/
  basis : Module.Basis (Fin d) A B
  /-- Its first vector is `1`. -/
  basis_zero : basis 0 = 1
  /-- The syntomic-good element of the universal ring. -/
  g : universalRing d
  /-- `g` is syntomic-good. -/
  good : IsSyntomicGood.{u} d g
  /-- The image of `g` under the classifying map of the basis is a unit. -/
  isUnit : IsUnit ((ofBasis basis basis_zero).classify g)

namespace ChartFrame

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (f : ChartFrame d A B)

/-- The chart ring `R = N_g[x_a : a ∈ A]` of the presentation of a frame. -/
abbrev Chart : Type u := universalChartRing A f.g

/-- The base change `B_R` of the universal family to the chart ring. -/
abbrev ChartAlgebra : Type u := Carrier (tableOfHom (universalChartClassify A f.g))

/-- The chart `N_g → A` of the frame. -/
def chartMap : universalChartBase.{u} f.g →+* A := chartOfBasis f.basis f.basis_zero f.isUnit

/-- **The evaluation** `R = N_g[x_a] → A`: `x_a ↦ a`, and the chart of the frame on `N_g`. -/
def eval : f.Chart →+* A := MvPolynomial.eval₂Hom f.chartMap id

/-- The evaluation sends the variable `x_a` to `a`. -/
theorem eval_X (a : A) : f.eval (MvPolynomial.X a : MvPolynomial A (universalChartBase.{u} f.g)) =
    a :=
  MvPolynomial.eval₂_X _ _ a

/-- The evaluation restricts to the chart on `N_g`. -/
theorem eval_algebraMap (n : universalChartBase.{u} f.g) :
    f.eval (algebraMap (universalChartBase.{u} f.g) f.Chart n) = f.chartMap n :=
  MvPolynomial.eval₂_C _ _ n

/-- **The evaluation is surjective.** -/
theorem eval_surjective : Function.Surjective f.eval := fun a =>
  ⟨MvPolynomial.X a, f.eval_X a⟩

/-- The evaluation, composed with the classifying map of the chart, is the classifying map of the
basis. -/
theorem eval_comp_classify :
    f.eval.comp (universalChartClassify A f.g) = (ofBasis f.basis f.basis_zero).classify := by
  refine RingHom.ext fun x => ?_
  change f.eval (algebraMap _ f.Chart (universalChartBaseClassify.{u} f.g x)) = _
  rw [eval_algebraMap, chartMap, ← RingHom.comp_apply, chartOfBasis_comp]

/-- The base change along the evaluation of the table of the chart is the table of the basis. -/
theorem map_table : FiniteFreeAlgebra.map f.eval (tableOfHom (universalChartClassify A f.g)) =
    ofBasis f.basis f.basis_zero := by
  rw [map_tableOfHom, eval_comp_classify, tableOfHom_classify]

/-- **The map `B_R → B`** of the presentation: `x ↦ ∑ₖ ψ(x k) • e k`. -/
def carrierMap : f.ChartAlgebra →+* B :=
  carrierLift f.eval _ f.basis f.basis_zero f.map_table

/-- The `R`-algebra structure on `A` given by the evaluation. -/
abbrev algebraChart : Algebra f.Chart A := f.eval.toAlgebra

/-- The `B_R`-algebra structure on `B` given by `Stacks.FormsTrace.ChartFrame.carrierMap`. -/
abbrev algebraCarrier : Algebra f.ChartAlgebra B := f.carrierMap.toAlgebra

/-- The `R`-algebra structure on `B` through `A`. -/
abbrev algebraChartTarget : Algebra f.Chart B := ((algebraMap A B).comp f.eval).toAlgebra

/-- The tower `R → A → B`. -/
theorem isScalarTower_chart :
    letI := f.algebraChart
    letI := f.algebraChartTarget
    IsScalarTower f.Chart A B :=
  let := f.algebraChart
  let := f.algebraChartTarget
  IsScalarTower.of_algebraMap_eq' rfl

/-- `B_R → B` is compatible with the structure maps. -/
theorem carrierMap_algebraMap (r : f.Chart) :
    f.carrierMap (algebraMap f.Chart f.ChartAlgebra r) = algebraMap A B (f.eval r) :=
  carrierLift_algebraMap _ _ _ _ _ r

/-- The tower `R → B_R → B`. -/
theorem isScalarTower_carrier :
    letI := f.algebraCarrier
    letI := f.algebraChartTarget
    IsScalarTower f.Chart f.ChartAlgebra B :=
  let := f.algebraCarrier
  let := f.algebraChartTarget
  IsScalarTower.of_algebraMap_eq fun r => (f.carrierMap_algebraMap r).symm

/-- **The presentation of a frame is a pushout**: `B` is the base change along the evaluation
`R → A` of `B_R`. -/
theorem isPushout :
    letI := f.algebraChart
    letI := f.algebraCarrier
    letI := f.algebraChartTarget
    haveI := f.isScalarTower_chart
    haveI := f.isScalarTower_carrier
    Algebra.IsPushout f.Chart f.ChartAlgebra A B := by
  let := f.algebraChart
  let := f.algebraCarrier
  let := f.algebraChartTarget
  have := f.isScalarTower_chart
  have := f.isScalarTower_carrier
  exact isPushout_of_bases_one (Carrier.basis _) f.basis fun x => carrierLift_apply _ _ _ _ _ x

/-- The discriminant of the chart is a nice element for `B_R/R`. -/
theorem nice : IsNiceElement f.Chart f.ChartAlgebra
    (Algebra.discr f.Chart (Carrier.basis (tableOfHom (universalChartClassify A f.g)))) :=
  discr_universalChartRing_nice A f.good

/-- **The framed trace** `Θ_A : Ω^p_B → Ω^p_A` of a frame and a family `Θ_R` on the forms of the
chart with property (1) of Stacks, Lemma 0FLB: the descent of `Θ_R` along the evaluation. -/
def framedTrace (Θ : ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart]
      ⋀[f.Chart]^p Ω[f.Chart⁄ℤ]) (hΘ : IsFormsTrace f.Chart f.ChartAlgebra Θ) :
    ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ] :=
  letI := f.algebraChart
  letI := f.algebraCarrier
  letI := f.algebraChartTarget
  haveI := f.isScalarTower_chart
  haveI := f.isScalarTower_carrier
  haveI := f.isPushout
  descendForms f.Chart f.ChartAlgebra A B f.eval_surjective Θ
    (hΘ.isWedgeLinear_of_isNiceElement f.nice)

variable {f}

/-- The four properties of the framed trace, proved once in the pushout context. -/
private theorem framedTrace_spec
    {Θ : ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart]
      ⋀[f.Chart]^p Ω[f.Chart⁄ℤ]} (hΘ : IsFormsTrace f.Chart f.ChartAlgebra Θ) :
    (letI := f.algebraChart
    letI := f.algebraCarrier
    ∀ (p : ℕ) (η : ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ]),
      f.framedTrace Θ hΘ p (formsMap f.ChartAlgebra B p η) = formsMap f.Chart A p (Θ p η)) ∧
    (∀ [Module.Finite A B] [Module.Projective A B], IsFormsTrace A B (f.framedTrace Θ hΘ)) ∧
    IsWedgeLinear A B (f.framedTrace Θ hΘ) ∧
    (CommutesWithD f.Chart f.ChartAlgebra Θ → CommutesWithD A B (f.framedTrace Θ hΘ)) := by
  let := f.algebraChart
  let := f.algebraCarrier
  let := f.algebraChartTarget
  have := f.isScalarTower_chart
  have := f.isScalarTower_carrier
  have := f.isPushout
  exact ⟨descendForms_formsMap _ _ _, isFormsTrace_descendForms _ _ _ hΘ,
    isWedgeLinear_descendForms _ _ _, commutesWithD_descendForms _ _ _⟩

/-- **The defining property of the framed trace**: `Θ_A(η|_B) = Θ_R(η)|_A`. -/
theorem framedTrace_formsMap
    {Θ : ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart]
      ⋀[f.Chart]^p Ω[f.Chart⁄ℤ]} (hΘ : IsFormsTrace f.Chart f.ChartAlgebra Θ) (p : ℕ)
    (η : ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ]) :
    letI := f.algebraChart
    letI := f.algebraCarrier
    f.framedTrace Θ hΘ p (formsMap f.ChartAlgebra B p η) = formsMap f.Chart A p (Θ p η) :=
  (framedTrace_spec hΘ).1 p η

/-- **The framed trace has property (1) of Stacks, Lemma 0FLB.** -/
theorem isFormsTrace_framedTrace [Module.Finite A B] [Module.Projective A B]
    {Θ : ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart]
      ⋀[f.Chart]^p Ω[f.Chart⁄ℤ]} (hΘ : IsFormsTrace f.Chart f.ChartAlgebra Θ) :
    IsFormsTrace A B (f.framedTrace Θ hΘ) :=
  (framedTrace_spec hΘ).2.1

/-- **The framed trace has property (2) of Stacks, Proposition 0FLC.** -/
theorem isWedgeLinear_framedTrace
    {Θ : ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart]
      ⋀[f.Chart]^p Ω[f.Chart⁄ℤ]} (hΘ : IsFormsTrace f.Chart f.ChartAlgebra Θ) :
    IsWedgeLinear A B (f.framedTrace Θ hΘ) :=
  (framedTrace_spec hΘ).2.2.1

/-- **The framed trace commutes with the de Rham differentials** if `Θ_R` does. -/
theorem commutesWithD_framedTrace
    {Θ : ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart]
      ⋀[f.Chart]^p Ω[f.Chart⁄ℤ]} (hΘ : IsFormsTrace f.Chart f.ChartAlgebra Θ)
    (hd : CommutesWithD f.Chart f.ChartAlgebra Θ) :
    CommutesWithD A B (f.framedTrace Θ hΘ) :=
  (framedTrace_spec hΘ).2.2.2 hd

end ChartFrame

end Stacks.FormsTrace

end
