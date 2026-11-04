module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# Zero schemes of iteratively pulled-back sections

Let `q₁ : A ⟶ B` and `q₂ : B ⟶ T` be morphisms of schemes, let `L` be an invertible module on `T`
and let `s` be a global section of `L`. There are two ways to read the zero scheme of `s` pulled
back to `A`: pull `s` back along `q₁ ≫ q₂` in one step, or pull it back along `q₂` and then along
`q₁`. The two invertible modules involved,

  `(q₁ ≫ q₂)^* L`   and   `q₁^* q₂^* L`,

are only *isomorphic* — the comparison is `Scheme.Modules.pullbackComp`, and the corresponding
identification of global sections is `AlgebraicGeometry.pullbackGlobalSections_comp_hom` — so
nothing forces the two zero schemes to be given by the same term. This file shows that they are
nevertheless **equal** as quasi-coherent ideal sheaves on `A`.

## Main results

* `Stacks.Divisors.zeroScheme_pullback_comp` — `Z(q₁^* q₂^* s) = Z((q₁ ≫ q₂)^* s)` as ideal
  sheaves on `A`.

## Implementation notes

The proof does not compare the two invertible modules at all, and in particular does not use
`Scheme.Modules.pullbackComp`. Stacks 0B6Y — `Stacks.Divisors.zeroScheme_pullback` — says that the
zero scheme of a pulled-back section is the scheme-theoretic inverse image of the zero scheme.
Applying it three times rewrites both sides as inverse images of the one zero scheme `Z(s)` on
`T`, namely as `(Z(s).comap q₂).comap q₁` and `Z(s).comap (q₁ ≫ q₂)`, and those agree by
functoriality of `Scheme.IdealSheafData.comap`. The isomorphism of invertible modules therefore
never has to be carried, which is what makes the statement an equality rather than an
isomorphism of subschemes.

This is what lets the Gysin condition of Stacks 0B76 be checked for a *composite* `f ≫ g` of
morphisms: the inner class is capped against the divisor pulled back to a test scheme over the
middle object, the outer class against that divisor pulled back once more, and the condition being
verified speaks about the section pulled back along the composite. Without the identity below
those are three unrelated zero schemes.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- The zero scheme of a section pulled back in two steps is the zero scheme of the section
pulled back along the composite: `Z(q₁^* q₂^* s) = Z((q₁ ≫ q₂)^* s)` as quasi-coherent ideal
sheaves on `A`.

Both sides are the scheme-theoretic inverse image of `Z(s)` along `q₁ ≫ q₂` by Stacks 0B6Y, so
the isomorphism `q₁^* q₂^* L ≅ (q₁ ≫ q₂)^* L` of invertible modules never enters; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Composition`. -/
theorem zeroScheme_pullback_comp {A B T : Scheme.{u}} (q₁ : A ⟶ B) (q₂ : B ⟶ T) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    zeroScheme A ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q₂ L s)) =
      zeroScheme A ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (q₁ ≫ q₂) L s) := by
  rw [zeroScheme_pullback q₁ ((Scheme.Modules.pullback q₂).obj L)
      (AlgebraicGeometry.pullbackGlobalSections q₂ L s),
    zeroScheme_pullback q₂ L s, zeroScheme_pullback (q₁ ≫ q₂) L s,
    Scheme.IdealSheafData.comap_comp]

end Stacks.Divisors

end

end
