module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
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

/-!
# Projective dimension from a single Ext group, over enough projectives

Let `X` be an object of an abelian category `C` with enough projectives and let `n : ℕ`. If the
single group `Extⁿ(X, Y)` vanishes for every object `Y`, then `X` has projective dimension `< n`.

Projective dimension is Mathlib's `HasProjectiveDimensionLT`, defined by the vanishing of Ext,
rather than the minimal length of a finite resolution by projectives.

## Main results

* `Stacks.Abelian.ExtVanishingDimension.solution`,
  `CategoryTheory.hasProjectiveDimensionLT_of_enoughProjectives`: in an abelian category with
  enough projectives, `Extⁿ(X, Y) = 0` for every object `Y` implies that `X` has projective
  dimension `< n`.

## References

* [StacksProject 065R](https://stacks.math.columbia.edu/tag/065R)
-/

@[expose] public section

universe w v u

open CategoryTheory Abelian Limits

namespace Stacks.Abelian.ExtVanishingDimension

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Along a short exact sequence `S`, the group `Extⁱ(S.X₁, Y)` is squeezed between `Extⁱ(S.X₂, Y)`
and `Ext^(i+1)(S.X₃, Y)`: if those two vanish, so does it. -/
private lemma subsingleton_ext_X₁ {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (i : ℕ)
    (h₂ : Subsingleton (Ext.{w} S.X₂ Y i)) (h₃ : Subsingleton (Ext.{w} S.X₃ Y (i + 1))) :
    Subsingleton (Ext.{w} S.X₁ Y i) :=
  subsingleton_of_forall_eq 0 fun x₁ ↦ by
    obtain ⟨x₂, rfl⟩ :=
      Ext.contravariant_sequence_exact₁ hS Y x₁ (add_comm 1 i) (Subsingleton.elim _ _)
    simp [Subsingleton.elim x₂ 0]

/-- An object whose group of self-extensions in degree `0` vanishes is a zero object: that group is
`Hom(X, X)`, so the identity of `X` is zero. -/
private lemma isZero_of_subsingleton_ext_zero (X : C) (h : Subsingleton (Ext.{w} X X 0)) :
    IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact Ext.homEquiv₀.symm.injective (Subsingleton.elim _ _)

end

end Stacks.Abelian.ExtVanishingDimension

open CategoryTheory Abelian

@[expose] public section

/-- Let `X` be an object of an abelian category with enough projectives and let `n : ℕ`. If the
single group `Extⁿ(X, Y)` vanishes for every object `Y`, then `X` has projective dimension `< n`. -/
@[stacks 065R "The implication `(3) ⇒ (1)`, proved the source's way: in an abelian category with
enough projectives, indexed by `HasProjectiveDimensionLT X n`, so that the source's `R`-modules of
projective dimension `≤ n` are the case `C = ModuleCat.{v} R` at `n + 1`. The converse `(1) ⇒ (2)`
and, at a single degree, `(2) ⇒ (3)` are `hasProjectiveDimensionLT_iff`; the sibling under enough
injectives is `hasProjectiveDimensionLT_of_enoughInjectives`. Projective dimension is Ext-measured
here rather than defined by a finite projective resolution (Definition 00O4, Lemma 0CXC); see the
module docstring."]
public theorem CategoryTheory.hasProjectiveDimensionLT_of_enoughProjectives {C : Type u}
    [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughProjectives C] (X : C) (n : ℕ)
    (hX : ∀ Y : C, Subsingleton (Ext.{w} X Y n)) : HasProjectiveDimensionLT X n := by
  induction n generalizing X with
  | zero =>
    exact (Stacks.Abelian.ExtVanishingDimension.isZero_of_subsingleton_ext_zero X
      (hX X)).hasProjectiveDimensionLT_zero
  | succ m ih =>
    obtain _ | m := m
    · exact projective_iff_hasProjectiveDimensionLT_one.1
        (projective_iff_subsingleton_ext_one.2 fun {Y} ↦ hX Y)
    · obtain ⟨p⟩ := EnoughProjectives.presentation (C := C) X
      have hS : (ShortComplex.mk _ _ (kernel.condition p.f)).ShortExact :=
        { exact := ShortComplex.exact_kernel p.f }
      exact (hS.hasProjectiveDimensionLT_X₃_iff m p.projective).mpr
        (ih _ fun Y ↦ Stacks.Abelian.ExtVanishingDimension.subsingleton_ext_X₁ hS Y (m + 1)
          (Ext.subsingleton_of_projective _ Y m) (hX Y))

end

namespace Stacks.Abelian.ExtVanishingDimension

@[expose] public section

/-- In an abelian category with enough projectives, an object `X` such that `Extⁿ(X, Y)` vanishes
for every object `Y` has projective dimension `< n`. -/
public alias solution := CategoryTheory.hasProjectiveDimensionLT_of_enoughProjectives

end

end Stacks.Abelian.ExtVanishingDimension
