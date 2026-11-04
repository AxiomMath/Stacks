module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.Basic

/-!
# Covers that are étale locally standard tamely ramified

Let `X` be a scheme, `U ⊆ X` an open subscheme and `f : Y ⟶ U` a morphism. We say that
`Y ⟶ X` is *étale locally on `X` a finite disjoint union of standard tamely ramified morphisms*
if every point `x` of `X` has an affine étale neighbourhood `g : Spec A ⟶ X` such that

* `A` is Noetherian and `g⁻¹(U)` is the basic open `Spec A_φ` of a nonzerodivisor `φ ∈ A` with
  `A / φA` reduced, and
* the base change of `f` to `Spec A_φ` is, over `Spec A_φ`, a finite disjoint union of the standard
  tamely ramified covers `Spec (A[x]/(x^{eᵢ} - φ))_φ ⟶ Spec A_φ` of [Stacks, Tag 0EYF], with every
  `eᵢ ≥ 1` invertible in `A`.

This is the conclusion of Abhyankar's lemma for a regular divisor, [Stacks, Tag 0EYG], and the
standing description of the cover used by its consequences [Stacks, Tag 0EYH] (the normalization
of `X` in `Y`), [Stacks, Tag 0EYI] (lifting points over discrete valuation rings) and
[Stacks, Tag 0EYJ] (extending Galois covers of the generic fibre).

## Main definitions

* `Stacks.FundamentalGroup.IsEtaleLocallyStandardTamelyRamified U f`: the property above.

## Main results

* `Stacks.FundamentalGroup.IsEtaleLocallyStandardTamelyRamified.of_iso`: the property only depends
  on `f` up to isomorphism of schemes over `U`.

## Implementation notes

The standard morphism of [Stacks, Tag 0EYF] attached to `(A, φ, e)` is
`AlgebraicGeometry.standardTamelyRamifiedCover A φ e : Spec (C_φ) ⟶ Spec (A_φ)`, where
`C = AlgebraicGeometry.standardTamelyRamifiedAlgebra A φ e = A[x]/(x^e - φ)`. The hypotheses of the
example on `(A, φ, e)` — `A` Noetherian, `φ` a nonzerodivisor, `A / φA` reduced, `e ≥ 1`
invertible in `A` — are part of the property.

The identification of `g⁻¹(U)` with `Spec A_φ` is recorded as a morphism
`gU : Spec A_φ ⟶ U` together with the fact that the square
```
Spec A_φ --gU--> U
    |            |
Spec A  --g-->   X
```
is cartesian. The base change of `f` is then `pullback f gU ⟶ Spec A_φ`, and the disjoint union
is the coproduct of the standard covers indexed by `Fin n`, compared with it over `Spec A_φ`.
Indexing by `Fin n` costs nothing, since the index set is finite, and lets the exponents be a
plain function `e : Fin n → ℕ`.

## References

* [Stacks Project, Example 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
* [Stacks Project, Lemma 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-- **Étale locally a finite disjoint union of standard tamely ramified morphisms.** Let
`U ⊆ X` be an open subscheme and `f : Y ⟶ U`. Then `Y ⟶ X` is étale locally on `X` a finite
disjoint union of standard tamely ramified morphisms ([Stacks, Example 0EYF]) if every point
`x : X` is in the image of an étale morphism `g : Spec A ⟶ X` with the following properties:
`A` is a Noetherian ring, there is a nonzerodivisor `φ ∈ A` with `A / φA` reduced and a
morphism `gU : Spec A_φ ⟶ U` exhibiting `Spec A_φ` as the inverse image `g⁻¹(U)` (the square
with `U.ι` and `g` is cartesian), and there are exponents `e : Fin n → ℕ`, each `eᵢ ≥ 1` and
invertible in `A`, with an isomorphism over `Spec A_φ` between the base change
`Y ×_U Spec A_φ` and the disjoint union `∐ᵢ Spec (A[x]/(x^{eᵢ} - φ))_φ` of the standard covers.

This is the conclusion of [Stacks, Tag 0EYG], used by [Stacks, Tags 0EYH, 0EYI, 0EYJ]. -/
def IsEtaleLocallyStandardTamelyRamified {X Y : Scheme.{u}} (U : X.Opens) (f : Y ⟶ U) :
    Prop :=
  ∀ x : X, ∃ (A : CommRingCat.{u}) (g : Spec A ⟶ X) (_ : Etale g) (a : Spec A), g a = x ∧
    ∃ φ : A, IsNoetherianRing A ∧ φ ∈ nonZeroDivisors A ∧
      _root_.IsReduced (A ⧸ Ideal.span {φ}) ∧
      ∃ gU : Spec (.of (Localization.Away φ)) ⟶ U,
        IsPullback gU (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away φ))))
          U.ι g ∧
        ∃ (n : ℕ) (e : Fin n → ℕ), (∀ i, 0 < e i ∧ IsUnit (e i : A)) ∧
          ∃ ι : pullback f gU ≅ ∐ fun i ↦ Spec (.of (Localization.Away
              (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ))),
            ι.hom ≫ Sigma.desc (fun i ↦ standardTamelyRamifiedCover A φ (e i)) =
              pullback.snd f gU

/-- Being étale locally a finite disjoint union of standard tamely ramified morphisms only
depends on the cover up to isomorphism over `U`: if `e : Y' ≅ Y` with `e.hom ≫ f = f'` and `f`
has the property, then so does `f'`. -/
theorem IsEtaleLocallyStandardTamelyRamified.of_iso {X Y Y' : Scheme.{u}} {U : X.Opens}
    {f : Y ⟶ U} {f' : Y' ⟶ U} (e : Y' ≅ Y) (he : e.hom ≫ f = f')
    (h : IsEtaleLocallyStandardTamelyRamified U f) :
    IsEtaleLocallyStandardTamelyRamified U f' := by
  intro x
  obtain ⟨A, g, hg, a, hga, φ, hA, hφ, hred, gU, hpb, n, e', he', ι, hι⟩ := h x
  subst he
  let m : pullback (e.hom ≫ f) gU ⟶ pullback f gU :=
    pullback.map (e.hom ≫ f) gU f gU e.hom (𝟙 _) (𝟙 _) (by simp) (by simp)
  refine ⟨A, g, hg, a, hga, φ, hA, hφ, hred, gU, hpb, n, e', he', asIso m ≪≫ ι, ?_⟩
  rw [Iso.trans_hom, asIso_hom, Category.assoc, hι]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end Stacks.FundamentalGroup
