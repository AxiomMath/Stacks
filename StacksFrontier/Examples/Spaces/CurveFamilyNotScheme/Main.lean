module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyCurveFamily
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A family of curves whose total space is not a scheme

This file states and proves [Stacks, Tag 0D5E]: there is a field `k` and a family of curves
`X ⟶ A¹_k` (Stacks 0D4Z) whose total space `X` is not a scheme. The field is `k = ℂ`.

The construction (Stacks, Section 0D5D) is assembled in the neighbouring files: the cubic
surface `Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` in `ℙ²_{k[t]}`, a point `y` of the central
fibre `Y₀` with property (2), the blowup `Z` of `Y` at `y` with exceptional curve `E` and strict
transform `C` of `Y₀`, Artin's contraction `X` of `C` (Stacks 0GIB) — a family of curves over
`A¹_k` — and the proof that `X` is not a scheme
(`Stacks.Examples.CurveFamilyNotScheme.exists_curveFamily_cubicContraction`).

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.exists_curveFamily_total_not_scheme`: Stacks 0D5E.

## Implementation notes

The statement also quantifies over the big fppf site `B` and the proof that it contains
`Spec ℤ`. This is not an extra freedom of the source: the source's big fppf site is absolute,
while this library's is a size-bounded category of schemes (see
`StacksFrontier/AlgebraicGeometry/Quot/CurveFamilies.lean`), and a family of curves, being an object
of a category over such a site, can only be stated relative to one. The base of the family is the
affine line `Spec ℂ[t]` itself, up to isomorphism, and its total space is not the algebraic space
of any scheme of the site, which is the source's "`X` is not a scheme".

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Stacks.Examples.CurveFamilyNotScheme

/-- The complex numbers are uncountable. -/
instance uncountable_complex : Uncountable ℂ :=
  ⟨fun h => not_countable_complex (Set.countable_univ_iff.mpr h)⟩

/-- **A family of curves whose total space is not a scheme** ([Stacks, Tag 0D5E]). There are a
field `k` and a family of curves `F` (Stacks 0D4Z: a flat, proper morphism of finite
presentation of relative dimension at most one, from an algebraic space over `Spec ℤ` to a
scheme) in a big fppf site, whose base is the affine line `A¹_k = Spec k[t]` and whose total space
is not isomorphic to the algebraic space of any scheme.

The construction is that of Stacks, Section 0D5D, with `k = ℂ`: `Y ⊆ ℙ²_{k[t]}` is the cubic
surface `T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0`, `y` a point of the central fibre `Y₀` with
property (2), `Z` the blowup of `Y` at `y` and `C ⊆ Z` the strict transform of `Y₀`; the total
space of `F` is Artin's contraction of `C` (Stacks 0GIB), read over `Spec ℤ`. -/
@[stacks 0D5E "with k = ℂ: a family of curves over A¹_ℂ in the sense of Tag 0D4Z, Artin's \
contraction of the strict transform of the central fibre of the blown-up cubic surface, whose \
total space is not isomorphic to the algebraic space of any scheme"]
theorem exists_curveFamily_total_not_scheme :
    ∃ (k : Type) (_ : Field k) (B : BigFppfSite.{0}) (hZ : B.Contains integerBase)
      (F : AlgebraicGeometry.CurveFamily B hZ),
      Nonempty (F.base.left.obj ≅ Spec (CommRingCat.of (Polynomial k))) ∧
        ¬ ∃ V : BigFppfOver B integerBase hZ, Nonempty (F.total ≅ schemeSpace V) := by
  have h3 : ringChar ℂ ≠ 3 := by
    rw [ringChar.eq_zero]
    norm_num
  obtain ⟨F, hb, hF⟩ := exists_curveFamily_cubicContraction ℂ h3
  refine ⟨ℂ, inferInstance, cubicSite ℂ h3, cubicSite_contains_integerBase ℂ h3, F, ?_, hF⟩
  rw [hb]
  exact ⟨Iso.refl _⟩

end Stacks.Examples.CurveFamilyNotScheme

end
