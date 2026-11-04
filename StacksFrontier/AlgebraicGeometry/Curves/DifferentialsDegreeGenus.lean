module

public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitzGenus
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafSmoothCurve

/-!
# The differentials of a smooth proper curve, and the Riemann–Hurwitz formula

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`.
[Stacks, Tag 0C1A] says that `dim_k H⁰(X, Ω_{X/k}) = g` and `deg(Ω_{X/k}) = 2g - 2`, and
[Stacks, Tag 0C1D] deduces the Riemann–Hurwitz formula
`2g_X - 2 = (2g_Y - 2) deg(f) + deg(R)` for a morphism `f : X ⟶ Y` of such curves satisfying the
equivalent conditions of [Stacks, Tag 0C1C], `R` being the divisor cut out by the different.

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two`:
  **Tag 0C1A, second equality**, `deg(Ω_{X/k}) = 2g - 2`, with the degree of an invertible module.
  The first equality, `dim_k H⁰(X, Ω_{X/k}) = g`, is
  `AlgebraicGeometry.finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus`.
* `AlgebraicGeometry.two_mul_genus_sub_two_eq_degreeOver_mul_add_of_exists_etale`: **Tag 0C1D**,
  with condition (4) of Tag 0C1C (`f` étale on a nonempty open). The form with condition (1) is
  `AlgebraicGeometry.two_mul_genus_sub_two_eq_degreeOver_mul_add`.

## Implementation notes

The proof of Tag 0C1A is the source's: `Ω_{X/k} ≅ ω_X` by clause (6) of [Stacks, Tag 0BS2]
(`Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials`, `X` being smooth
of relative dimension one), and for the dualizing sheaf `dim_k H⁰(X, ω_X) = g` (equation 0BY8 and
clause (5) of Tag 0BS2) and `deg(ω_X) = 2g - 2` (the computation of [Stacks, Tag 0C19] for the
Gorenstein curve `X`) are
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_genus` and
`AlgebraicGeometry.invertibleCurveDegree_dualizingSheafOverField_of_isInvertible`. Both quantities
are invariant under isomorphism.

For Tag 0C1D the condition of Tag 0C1C used is (4), that `f` is étale on a nonempty open; `R` is
the closed subscheme of the Kähler different, an effective Cartier divisor
(`AlgebraicGeometry.isEffectiveCartierDivisor_kaehlerDifferent_of_exists_etale_comp_ι`), of
degree `dim_k Γ(R, 𝒪_R)`, and `deg(f)` is `AlgebraicGeometry.degreeOver f`. The computation
`deg(Ω_{X/k}) = deg(f) deg(Ω_{Y/k}) + deg(R)` is
`AlgebraicGeometry.invertibleCurveDegree_relativeDifferentials_eq_degreeOver_mul_add`
(Tags 0BWJ, 0AYX, 0AYZ), and Tag 0C1A for `X` and `Y` finishes it.

## References

* [Stacks Project, Tag 0C1A](https://stacks.math.columbia.edu/tag/0C1A)
* [Stacks Project, Tag 0C1D](https://stacks.math.columbia.edu/tag/0C1D)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Differentials

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
  [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- **Stacks Project, Tag 0C1A, second equality.** Let `X` be a smooth proper curve over a field
`k` with `H⁰(X, 𝒪_X) = k`, of genus `g`. Then `deg(Ω_{X/k}) = 2g - 2`: `Ω_{X/k} ≅ ω_X` by
Tag 0BS2 (6), and `deg(ω_X) = 2g - 2` (Tag 0C19 for the Gorenstein curve `X`). -/
@[stacks 0C1A "`deg(Ω_{X/k}) = 2g - 2`"]
theorem invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two :
    invertibleCurveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
        (Scheme.Hom.relativeDifferentials f) = 2 * genus f - 2 := by
  have := smoothOfRelativeDimension_one_of_isCurve _ f
  have := isInvertible_dualizingSheafOverField_of_isCurve f
  rw [invertibleCurveDegree_eq_of_iso k f _
    (Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials f).some.symm]
  exact invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k f _

end Differentials

section RiemannHurwitz

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k))
  (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsCurve k pY] [Smooth pX] [Smooth pY]
  [IsProper pX] [IsProper pY] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop)]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop)] (f : X ⟶ Y)

/-- **Stacks Project, Tag 0C1D (Riemann–Hurwitz).** Let `f : X ⟶ Y` be a morphism of smooth
proper curves over a field `k` satisfying the equivalent conditions of Tag 0C1C (here (4): `f` is
étale on a nonempty open), with `k = H⁰(Y, 𝒪_Y) = H⁰(X, 𝒪_X)`, and let `X`, `Y` have genus
`g_X`, `g_Y`. Then

`2g_X - 2 = (2g_Y - 2) deg(f) + deg(R)`,

where `R ⊆ X` is the effective Cartier divisor cut out by the different of `f`, of degree
`dim_k Γ(R, 𝒪_R)`, and `deg(f) = [k(X) : k(Y)]`. -/
@[stacks 0C1D]
theorem two_mul_genus_sub_two_eq_degreeOver_mul_add_of_exists_etale (hf : f ≫ pY = pX)
    (hgen : ∃ U : X.Opens, Nonempty U ∧ Etale (U.ι ≫ f)) :
    letI : LocallyOfFiniteType f := locallyOfFiniteType_of_isCurve_comp k pX pY f hf
    letI : IsDominant f := isDominant_of_exists_etale_comp_ι pX pY f hf hgen
    letI : Algebra k Γ((Stacks.Discriminant.kaehlerDifferent f).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((Stacks.Discriminant.kaehlerDifferent f).subschemeι ≫ pX).appTop).hom.toAlgebra
    2 * (genus pX : ℤ) - 2 =
      (2 * (genus pY : ℤ) - 2) * (degreeOver f : ℤ) +
        (Module.finrank k Γ((Stacks.Discriminant.kaehlerDifferent f).subscheme, ⊤) : ℤ) :=
  two_mul_genus_sub_two_eq_of_invertibleCurveDegree_relativeDifferentials pX pY f hf hgen
    (invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two pX)
    (invertibleCurveDegree_relativeDifferentials_eq_two_mul_genus_sub_two pY)

end RiemannHurwitz

end AlgebraicGeometry

end
