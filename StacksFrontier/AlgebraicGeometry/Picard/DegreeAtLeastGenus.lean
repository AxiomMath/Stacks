module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective
public import StacksCore.Tactic.StacksAttribute

/-!
# Effective divisors of degree at least the genus

Let `X` be an integral scheme, proper of dimension at most one over a field `k`, whose only
global regular functions are the constants, and let `g` be its genus. An invertible
`𝒪_X`-module `ℒ` of degree at least `g` is `𝒪_X(D)` for an effective Cartier divisor `D` finite
locally free over `k` of rank `deg ℒ`.

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_eq_finrank_globalSections_zeroScheme`: the degree of
  an invertible module with a nonzero section is the dimension of the functions on its zero
  scheme.
* `AlgebraicGeometry.exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree`: the
  divisor of a module of degree at least the genus.

## Implementation notes

The divisor is the zero scheme of a nonzero global section of `ℒ`, which exists by
`AlgebraicGeometry.exists_section_ne_zero_of_genus_le_invertibleCurveDegree`.

## References

* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

variable [IsProper f] (hdim : topologicalKrullDim X ≤ 1)

/-- **The degree of an invertible module with a nonzero global section is the dimension of the
ring of functions on the zero scheme of that section**, here the subscheme of `D`. -/
theorem invertibleCurveDegree_eq_finrank_globalSections_zeroScheme [IsIntegral X]
    (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) (D : X.IdealSheafData)
    (hD : zeroScheme X L (s.eval (op ⊤)) = D) :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    @invertibleCurveDegree k _ X f _ hdim L hL =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) := by
  subst hD
  rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k f hdim L s hs
      (forall_finiteDimensional_cohomologyOverField_unit k f),
    finrank_cohomologyOverField_eq_of_iso k _
      (nonempty_pullback_zeroScheme_iso_unit k f hdim L s hs).some 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]

/-- **An invertible module of degree at least the genus is the module of an effective Cartier
divisor.** Let `X` be an integral curve, proper over a field `k` and of dimension at most one,
whose only global regular functions are the constants, and let `g` be its genus. Every invertible
`𝒪_X`-module of degree `d ≥ g` is `𝒪_X(D)` for an effective Cartier divisor `D` on `X` that is
finite locally free of rank `d` over `k`. On `k`-points, this is the surjectivity of `γ_d` in
[Stacks, Tag 0BA0] (5). -/
theorem exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree [IsIntegral X]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : (genus f : ℤ) ≤ @invertibleCurveDegree k _ X f _ hdim L hL) :
    ∃ (D : X.IdealSheafData) (d : ℕ), Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      Nonempty (L ≅ Stacks.Divisors.invertibleSheaf' D) ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) d ∧
      (d : ℤ) = @invertibleCurveDegree k _ X f _ hdim L hL := by
  obtain ⟨s, hs⟩ := exists_section_ne_zero_of_genus_le_invertibleCurveDegree k f hdim L hdeg
  have hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  set D := zeroScheme X L (s.eval (op ⊤))
  let _ : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    isEffectiveCartierDivisor_zeroScheme_of_ne_zero L (s.eval (op ⊤)) hs
  exact ⟨D, Module.finrank k Γ(D.subscheme, ⊤), hcart,
    ⟨invertibleSheafIsoZeroSchemeOfIsRegularSection L s
      ((isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).1 hcart)⟩,
    isFiniteLocallyFreeOfRank_divisorSubscheme k f hdim D,
    (invertibleCurveDegree_eq_finrank_globalSections_zeroScheme k f hdim L s hs D rfl).symm⟩

end AlgebraicGeometry

end
