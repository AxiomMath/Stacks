module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusSingleTriangleHomology

/-!
# Killing a quotient through a factorisation of its image

Let `F, G : D⁺(C) ⥤ D⁺(C)` be triangulated functors such that `X ↦ Hⁿ(GF(X[0]))` is
concentrated in degree `n` and reflects zero objects on a class `P` of objects stable under
subobjects and quotients (so that it is faithful on `P`,
`Stacks.DerivedCategoryPlus.eq_zero_of_homology_map_map_singleFunctor_map_eq_zero`). For an
epimorphism `β : A ⟶ B` with `A ∈ P` and `ψ : B ⟶ B`, if `F((β ≫ ψ)[0])` factors through an
object `Z` with `Hⁿ(G Z) = 0`, then `ψ = 0`.

This is the formal lemma (E2) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), with
`F = G = Φ`, `n = 2` and `ψ = ℓᵉ • 𝟙`.

## Main results

* `Stacks.DerivedCategoryPlus.eq_zero_of_map_singleFunctor_map_epi_comp_factors`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  (F G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C) [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- **(E2, abstract form)** For an epimorphism `β : A ⟶ B` with `A ∈ P` and `ψ : B ⟶ B` such
that `F((β ≫ ψ)[0])` factors through `Z` with `Hⁿ(G Z) = 0`, `ψ = 0`. -/
lemma eq_zero_of_map_singleFunctor_map_epi_comp_factors (P : C → Prop)
    (hPmono : ∀ {A B : C} (ι : A ⟶ B) [Mono ι], P B → P A)
    (hPepi : ∀ {A B : C} (π : A ⟶ B) [Epi π], P A → P B) (n : ℤ)
    (hconc : ∀ X : C, P X → ∀ i : ℤ, i ≠ n → IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj
      ((F ⋙ G).obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))))
    (hrefl : ∀ X : C, P X → IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
      ((F ⋙ G).obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) → IsZero X)
    {A B : C} (β : A ⟶ B) [Epi β] (ψ : B ⟶ B) (hA : P A) {Z : DerivedCategory.Plus C}
    (a : F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A) ⟶ Z)
    (b : Z ⟶ F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj B))
    (hab : F.map ((DerivedCategory.Plus.singleFunctor C 0).map (β ≫ ψ)) = a ≫ b)
    (hZ : IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj (G.obj Z))) : ψ = 0 := by
  have h0 := eq_zero_of_homology_map_map_singleFunctor_map_eq_zero F G P hPmono hPepi n hconc
    hrefl (β ≫ ψ) hA (hPepi β hA) (by
      rw [Functor.comp_map, hab, G.map_comp, Functor.map_comp]
      rw [hZ.eq_of_tgt ((DerivedCategory.Plus.homologyFunctor C n).map (G.map a)) 0,
        Limits.zero_comp])
  rw [← cancel_epi β, h0, Limits.comp_zero]

end Stacks.DerivedCategoryPlus
