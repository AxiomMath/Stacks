module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison

/-!
# The pullback on derived sections along a derived adjunction

Let `f ⊣ g` be an adjunction between abelian categories with `f` preserving homology, so that it
descends to the derived adjunction `Rf ⊣ Rg` on bounded below derived categories
(`CategoryTheory.Adjunction.rightDerivedFunctorPlus`). Let `Δ₀` and `Δ` be left exact "sections"
functors on the two sides with `g ⋙ Δ₀ ≅ Δ`, and suppose that `g` preserves injective objects.
Then `RΔ ≅ Rg ⋙ RΔ₀` (the Leray factorization of Stacks 015M), and the unit `K ⟶ Rg(Rf K)` of
the derived adjunction yields the *pullback on derived sections*

```
RΔ₀(K) ⟶ RΔ₀(Rg(Rf K)) ≅ RΔ(Rf K),
```

natural in `K ∈ D⁺`. It is invertible at every `K` at which the derived unit is invertible.

This is the formal argument of Cohomology on Sites, Remark 08J6, by which cohomological descent
`K ≅ Ra_*a⁻¹K` gives `RΓ(X, K) = RΓ(U, a⁻¹K)`.

## Main definitions

* `CategoryTheory.Adjunction.rightDerivedFunctorPlusSectionsPullback`: the pullback
  `RΔ₀ ⟶ Rf ⋙ RΔ`.

## Main results

* `CategoryTheory.Adjunction.isIso_rightDerivedFunctorPlusSectionsPullback_app`: it is invertible
  at `K` when the unit of `Rf ⊣ Rg` is invertible at `K`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {D₀ D 𝒜 : Type*} [Category* D₀] [Category* D] [Category* 𝒜]
  [Abelian D₀] [Abelian D] [Abelian 𝒜]
  [HasDerivedCategory D₀] [HasDerivedCategory D] [HasDerivedCategory 𝒜]
  [EnoughInjectives D₀] [EnoughInjectives D]
  {f : D₀ ⥤ D} {g : D ⥤ D₀} [f.Additive] [g.Additive] [f.PreservesHomology] (adj : f ⊣ g)
  (Δ₀ : D₀ ⥤ 𝒜) (Δ : D ⥤ 𝒜) [Δ₀.Additive] [Δ.Additive] [PreservesFiniteLimits Δ₀]
  [g.PreservesInjectiveObjects] (e : g ⋙ Δ₀ ≅ Δ)

/-- **The pullback on derived sections** `RΔ₀ ⟶ Rf ⋙ RΔ` along an adjunction `f ⊣ g` with `f`
preserving homology and `g` preserving injectives, given `g ⋙ Δ₀ ≅ Δ`: `RΔ₀` of the unit of the
derived adjunction `Rf ⊣ Rg`, followed by the inverse of the Leray factorization
`RΔ ≅ Rg ⋙ RΔ₀`. -/
def rightDerivedFunctorPlusSectionsPullback :
    Δ₀.rightDerivedFunctorPlus ⟶ f.rightDerivedFunctorPlus ⋙ Δ.rightDerivedFunctorPlus :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight adj.rightDerivedFunctorPlus.unit Δ₀.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft f.rightDerivedFunctorPlus
      (Stacks.LerayPullbackComparison.lerayIso Δ₀ Δ e).inv

/-- The pullback on derived sections at `K` is `RΔ₀` of the derived unit at `K` followed by the
inverse of the Leray factorization at `Rf K`. -/
theorem rightDerivedFunctorPlusSectionsPullback_app (K : DerivedCategory.Plus D₀) :
    (adj.rightDerivedFunctorPlusSectionsPullback Δ₀ Δ e).app K =
      Δ₀.rightDerivedFunctorPlus.map (adj.rightDerivedFunctorPlus.unit.app K) ≫
        (Stacks.LerayPullbackComparison.lerayIso Δ₀ Δ e).inv.app
          (f.rightDerivedFunctorPlus.obj K) := by
  simp [rightDerivedFunctorPlusSectionsPullback]

/-- **The pullback on derived sections is invertible wherever the derived unit is**: if
`K ⟶ Rg(Rf K)` is an isomorphism, then `RΔ₀(K) ≅ RΔ(Rf K)`. -/
theorem isIso_rightDerivedFunctorPlusSectionsPullback_app (K : DerivedCategory.Plus D₀)
    [IsIso (adj.rightDerivedFunctorPlus.unit.app K)] :
    IsIso ((adj.rightDerivedFunctorPlusSectionsPullback Δ₀ Δ e).app K) := by
  rw [rightDerivedFunctorPlusSectionsPullback_app]
  infer_instance

end CategoryTheory.Adjunction

end
