module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness is preserved by localizing the base

Let `R → Sₘ` be a smooth ring map, let `M ⊆ R` be a multiplicative subset and let `Rₘ` be a
localization of `R` at `M`. Assume that `Sₘ` is an `Rₘ`-algebra compatibly with its `R`-algebra
structure; for `M` the powers of an element `f ∈ R` this says exactly that `f` maps to an
invertible element of `Sₘ`. Then `Sₘ` is smooth over `Rₘ`: this is the second assertion of
Stacks 00T3.

## Main results

* `Stacks.Smooth.LocalizedBase.solution`: Lemma 00T3, second assertion — an algebra smooth over `R`
  which is an algebra over a localization `Rₘ` of `R` is smooth over `Rₘ`.

## References

* [StacksProject 00T3](https://stacks.math.columbia.edu/tag/00T3)
  (`algebra-lemma-localize-smooth`), in the section "Smooth ring maps".
-/

@[expose] public section

namespace Stacks.Smooth.LocalizedBase

section

variable {R Rₘ Sₘ : Type*} [CommRing R] [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ]
  [Algebra R Sₘ] [Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ] (M : Submonoid R) [IsLocalization M Rₘ]

include M in
/-- If `Sₘ` is an algebra over a localization `Rₘ` of `R` at `M`, compatibly with its `R`-algebra
structure, then `R → Rₘ`, `R → Sₘ`, `Rₘ → Sₘ` is a pushout square: `Sₘ` is its own base change
`Rₘ ⊗[R] Sₘ` along `R → Rₘ`. -/
private theorem isPushout_localization_base : Algebra.IsPushout R Rₘ Sₘ Sₘ :=
  have : IsLocalization (Algebra.algebraMapSubmonoid Sₘ M) Sₘ :=
    IsLocalization.of_le_isUnit <| by
      rintro _ ⟨m, hm, rfl⟩
      rw [IsUnit.mem_submonoid_iff, IsScalarTower.algebraMap_apply R Rₘ Sₘ]
      exact (IsLocalization.map_units Rₘ (⟨m, hm⟩ : M)).map _
  (Algebra.isPushout_of_isLocalization M Rₘ Sₘ Sₘ).symm

include M in
/-- Localizing the base preserves finite presentation: if `Sₘ` is of finite presentation over `R`
and an algebra over a localization `Rₘ` of `R` at `M`, compatibly with its `R`-algebra structure,
then it is of finite presentation over `Rₘ`. -/
@[sga "1 VIII 3.6" "special case"]
private theorem finitePresentation_localization_base [Algebra.FinitePresentation R Sₘ] :
    Algebra.FinitePresentation Rₘ Sₘ :=
  have := isPushout_localization_base (Rₘ := Rₘ) (Sₘ := Sₘ) M
  .equiv (Algebra.IsPushout.equiv R Rₘ Sₘ Sₘ)

end

/-- **Smoothness is preserved by localizing the base** (Stacks 00T3, second assertion). Let `M` be
a multiplicative subset of `R` and `Rₘ` a localization of `R` at `M`. Let `Sₘ` be an `R`-algebra
which is smooth over `R` and which is an `Rₘ`-algebra compatibly with its `R`-algebra structure —
for `M` the powers of `f ∈ R` this last condition says that `f` maps to an invertible element of
`Sₘ`. Then `Sₘ` is smooth over `Rₘ`. -/
public theorem solution {R Rₘ Sₘ : Type*} [CommRing R] [CommRing Rₘ]
    [CommRing Sₘ] [Algebra R Rₘ] [Algebra R Sₘ] [Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]
    (M : Submonoid R) [IsLocalization M Rₘ] [Algebra.Smooth R Sₘ] :
    Algebra.Smooth Rₘ Sₘ where
  formallySmooth := Algebra.FormallySmooth.localization_base M
  finitePresentation := finitePresentation_localization_base M

end Stacks.Smooth.LocalizedBase

/-!
# Smoothness is preserved by localizing the target at an element and by localizing the base

Let `R → S` be a smooth ring map, that is, `S` is of finite presentation over `R` and formally
smooth over `R`. Smoothness survives both localizations:

* localizing the target at the powers of an element `g : S` keeps it smooth over `R`, because
  `S → S_g` is itself smooth and smoothness is stable under composition;
* localizing the base keeps it smooth: if `M ⊆ R` is a multiplicative subset whose image in an
  `R`-algebra `Sₘ` consists of units — equivalently, if `Sₘ` is an algebra over a localization
  `Rₘ` of `R` at `M`, compatibly with `R` — then `Sₘ` is smooth over `Rₘ`, because formal
  smoothness descends along `R → Rₘ` and the square `R → Rₘ`, `Sₘ = Sₘ` is a pushout, so that
  `Sₘ ≃ Rₘ ⊗[R] Sₘ` is of finite presentation over `Rₘ`.

Here `Algebra.Smooth R S` is formal smoothness together with finite presentation. The hypothesis
that an element `f ∈ R` maps to an invertible element of the target is expressed by the pair
`[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]`, for an arbitrary localization `Rₘ` of `R` at an
arbitrary submonoid `M`.

## Main results

* `Algebra.Smooth.localization_away`: a localization of the target away from an element is smooth
  over the base.
* `Algebra.Smooth.localization_base`: an algebra smooth over `R` which is an algebra over a
  localization `Rₘ` of `R` is smooth over `Rₘ`.

## References

* [StacksProject 00T3](https://stacks.math.columbia.edu/tag/00T3)
-/

@[expose] public section

/-- Let `R → S` be a smooth ring map and let `S'` be a localization of `S` away from an element
`g : S`. Then `S'` is smooth over `R`. -/
@[stacks 00T3 "First assertion: any localization `S_g` is smooth over `R`. `Algebra.Smooth` is
Definition 00T2 (Mathlib's formal smoothness is the cotangent condition, plus finite presentation).
The localization is an abstract `IsLocalization.Away g S'`. See the module docstring."]
public theorem Algebra.Smooth.localization_away {R S S' : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [Algebra.Smooth R S] (g : S) [IsLocalization.Away g S'] :
    Algebra.Smooth R S' :=
  have : Algebra.Smooth S S' := Algebra.Smooth.of_isLocalization_Away g
  Algebra.Smooth.comp R S S'

/-- Let `M` be a multiplicative subset of `R` and `Rₘ` a localization of `R` at `M`. Let `Sₘ` be
an `R`-algebra which is smooth over `R` and which is an `Rₘ`-algebra compatibly with its
`R`-algebra structure — for `M` the powers of `f ∈ R` this last condition says that `f` maps to an
invertible element of `Sₘ`. Then `Sₘ` is smooth over `Rₘ`. -/
@[stacks 00T3 "Second assertion: if `f ∈ R` maps to an invertible element of `S` then `R_f → S`
is smooth. Stated as the `Algebra.Smooth` analogue of `Algebra.FormallySmooth.localization_base`:
the base is localized at an arbitrary submonoid `M`, and the hypothesis on `f` is the pair
`[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]`. `Algebra.Smooth` is Definition 00T2 (Mathlib's
formal smoothness is the cotangent condition, plus finite presentation). See the module docstring."]
public theorem Algebra.Smooth.localization_base {R Rₘ Sₘ : Type*} [CommRing R] [CommRing Rₘ]
    [CommRing Sₘ] [Algebra R Rₘ] [Algebra R Sₘ] [Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]
    (M : Submonoid R) [IsLocalization M Rₘ] [Algebra.Smooth R Sₘ] :
    Algebra.Smooth Rₘ Sₘ :=
  Stacks.Smooth.LocalizedBase.solution (R := R) M

end
