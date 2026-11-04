module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Refutation

/-!
# The components of the special fibre in the equality case of the genus bound

[Stacks, Tag 0CEE] describes the irreducible components of the special fibre `X_k` of a regular
proper model when equality holds in [Stacks, Tag 0CEA]. Its part (2) asserts that every
component `C` not through the chosen smooth rational point has `κ = H⁰(C, 𝒪_C)` separable over
`k`. That clause is false: `Stacks.Models.InseparableModel.situation` is a regular proper model of
`ℙ¹_K` over `R = 𝔽₂(t)⟦π⟧` where equality holds and a component is `ℙ¹_κ` with `κ = k(√t)`.

`Stacks.Models.RegularProperModelSituation.smooth_and_not_forall_isSeparable_of_genus_equality`
is the conjunction of the corrected statement, in the namespace `Stacks.Models`,
`RegularProperModelSituation.smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction`
— part (1) in full, and part (2) with separability exactly for the components of positive genus,
where the source's argument proves it — and of the refutation of the separability clause in
general.

## Main results

* `Stacks.Models.RegularProperModelSituation.smooth_and_not_forall_isSeparable_of_genus_equality`
  — the corrected form of [Stacks, Tag 0CEE] together with the refutation of its separability
  clause.

## References

* [Stacks Project, Tag 0CEE](https://stacks.math.columbia.edu/tag/0CEE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The corrected form of [Stacks, Tag 0CEE], together with the refutation of its separability
clause.** In the situation of [Stacks, Tag 0C61] let `x` be a `k`-rational point of `X_k` at which
`X_k ⟶ Spec(k)` is smooth, and suppose equality holds in [Stacks, Tag 0CEA]:
`dim_k H¹((X_k)_red, 𝒪) = g_top + g_geom(X_k/k)`. Then

1. `x` lies on a unique irreducible component of `X_k`, and that component is a smooth,
   H-projective, geometrically irreducible curve over `k`;
2. every other irreducible component `C` has `κ = H⁰(C, 𝒪_C)` finite over `k`, has a `κ`-rational
   point and is smooth over `κ`; and `κ/k` is separable as soon as `H¹(C, 𝒪_C) ≠ 0`.

The source asserts in (2) that `κ/k` is always separable. The second conjunct shows that this
fails: there is a situation of [Stacks, Tag 0C61], with a smooth `k`-rational point and equality
in [Stacks, Tag 0CEA], with a component `C` not through the point such that `H⁰(C, 𝒪_C)` is not
separable over `k`. The model is `Stacks.Models.InseparableModel.situation`: over
`R = 𝔽₂(t)⟦π⟧` it is the blow-up of `ℙ¹_R` at the closed point `X₁² = t X₀²` of the special
fibre, written as the divisor `π X₀² V = (X₁² - t X₀²) U` of `ℙ¹_R × ℙ¹_R`. Its special fibre is
`C₁ + E` with `C₁ ≅ ℙ¹_k` and `E ≅ ℙ¹_κ`, `κ = k(√t)` purely inseparable of degree two, meeting
transversally in one `κ`-point; a section of the model gives a smooth `k`-rational point on
`C₁ \ E`, `dim_k H¹((X_k)_red, 𝒪) = 0`, so equality holds, and `H⁰(E, 𝒪_E) = κ`.

Where the source's argument breaks: equality in `[κ_i : k] g_i ≥ [κ_i : k]_s g_i ≥ g_geom(C_i/k)`
gives `[κ_i : k] = [κ_i : k]_s` only when `g_i > 0`; for `g_i = 0`, as for `E`, it says nothing
about `κ_i/k`. Every other assertion of the tag survives, with the proof recorded at
`smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction`, which is the statement
registered as [Stacks, Tag 0CEE]. -/
theorem smooth_and_not_forall_isSeparable_of_genus_equality
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (heq : (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1)) :
    ((∃! Z : irreducibleComponents S.specialFiber, x ∈ Z.1) ∧
    (∀ Z : irreducibleComponents S.specialFiber, x ∈ Z.1 →
      Smooth (S.specialFiberComponentToSpec Z) ∧
        Stacks.HProjective.IsHProjective (S.specialFiberComponentToSpec Z) ∧
        GeometricallyIrreducible (S.specialFiberComponentToSpec Z) ∧
        IsCurve S.k (S.specialFiberComponentToSpec Z)) ∧
    (∀ Z : irreducibleComponents S.specialFiber, x ∉ Z.1 →
      letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
        (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
      letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
      FiniteDimensional S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) ∧
        (genus (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ ≠ 0 →
          Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)) ∧
        (∃ c : (S.specialFiberComponentIdeal Z).subscheme,
          IsRationalPoint (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ c) ∧
        Smooth (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ)) ∧
    ¬ ∀ (S' : RegularProperModelSituation.{0}) (x' : S'.specialFiber)
      (_hx' : IsRationalPoint S'.specialFiberToSpec x')
      (_hsm' : InfinitesimalLifting.SmoothAt S'.specialFiberToSpec x')
      (n' : ℕ) (e' : Fin n' ≃ irreducibleComponents S'.specialFiber)
      (_heq' : (S'.associatedNumericalType n' e').topologicalGenus +
          (geometricGenus S'.k S'.specialFiberToSpec : ℤ) =
        Module.finrank S'.k (cohomologyOverField S'.k
          (S'.specialFiber.reductionι ≫ S'.specialFiberToSpec)
          (SheafOfModules.unit S'.specialFiber.reduction.ringCatSheaf) 1))
      (Z : irreducibleComponents S'.specialFiber), x' ∉ Z.1 →
        letI : Field Γ((S'.specialFiberComponentIdeal Z).subscheme, ⊤) :=
          (S'.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
        letI : Algebra S'.k Γ((S'.specialFiberComponentIdeal Z).subscheme, ⊤) :=
          ((Scheme.ΓSpecIso (.of S'.k)).inv ≫
            (S'.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
        Algebra.IsSeparable S'.k Γ((S'.specialFiberComponentIdeal Z).subscheme, ⊤) :=
  ⟨S.smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction x hx hsm n e heq,
    not_forall_isSeparable_of_genus_equality⟩

end Stacks.Models.RegularProperModelSituation
