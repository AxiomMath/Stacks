module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact

/-!
# Vanishing of the cohomology of a derived limit

Let `A` be an abelian category with exact countable products and let `K` be a derived limit of
an inverse system `(Kₙ)` in `D(A)`. The Milnor short exact sequence (Stacks 07KY)

`0 ⟶ R¹lim Hʳ⁻¹(Kₙ) ⟶ Hʳ(K) ⟶ lim Hʳ(Kₙ) ⟶ 0`

shows that `Hʳ(K) = 0` as soon as every `Hʳ(Kₙ)` vanishes and the Milnor difference
`1 - shift` of the system `n ↦ Hʳ⁻¹(Kₙ)` is an epimorphism, `R¹lim` being its cokernel.

Epimorphy of the Milnor difference, that is the vanishing of `R¹lim`, can be checked after a
functor preserving the product and reflecting epimorphisms, such as an equivalence.

## Main results

* `Stacks.InverseSystem.epi_milnorDifference_of_epi_map`: the transport along a functor.
* `DerivedCategory.isZero_homology_of_isDerivedLimit`: the vanishing criterion.

## References

* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace Stacks.InverseSystem

/-- **Surjectivity of the Milnor difference descends along a functor** that preserves the product
of the tower and reflects epimorphisms: the functor carries the Milnor difference of a tower to
that of the image tower, up to the comparison isomorphism of the products. -/
theorem epi_milnorDifference_of_epi_map {D D' : Type*} [Category* D] [Category* D']
    [Preadditive D] [Preadditive D'] (G : D ⥤ D') [G.Additive] [G.ReflectsEpimorphisms]
    (X : ℕ → D) (f : ∀ n, X (n + 1) ⟶ X n) [HasProduct X] [HasProduct fun n => G.obj (X n)]
    [PreservesLimit (Discrete.functor X) G]
    (h : Epi (milnorDifference (fun n => G.obj (X n)) (fun n => G.map (f n)))) :
    Epi (milnorDifference X f) := by
  have hcomm : G.map (milnorDifference X f) ≫ piComparison G X =
      piComparison G X ≫ milnorDifference (fun n => G.obj (X n)) (fun n => G.map (f n)) := by
    refine Pi.hom_ext _ _ fun n => ?_
    simp only [Category.assoc, milnorDifference_π, piComparison_comp_π, ← G.map_comp,
      Preadditive.comp_sub, G.map_sub, piComparison_comp_π_assoc]
  have : Epi (G.map (milnorDifference X f) ≫ piComparison G X) := by
    rw [hcomm]
    exact epi_comp _ _
  have : Epi (G.map (milnorDifference X f)) := by
    have e : G.map (milnorDifference X f) =
        (G.map (milnorDifference X f) ≫ piComparison G X) ≫ inv (piComparison G X) := by
      simp
    rw [e]
    exact epi_comp _ _
  exact G.epi_of_epi_map this

end Stacks.InverseSystem

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]

/-- **The cohomology of a derived limit vanishes where that of the system does and `R¹lim`
vanishes one degree lower.** If `K` is a derived limit of `F : ℕᵒᵖ ⥤ D(A)`, every `Hʳ(Fₙ)`
vanishes and the Milnor difference of the system `n ↦ Hʳ⁻¹(Fₙ)` is an epimorphism, then
`Hʳ(K) = 0`. -/
theorem isZero_homology_of_isDerivedLimit (F : ℕᵒᵖ ⥤ DerivedCategory A)
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] (K : DerivedCategory A) (hK : IsDerivedLimit F K)
    (r : ℤ)
    (h₁ : Epi (Stacks.InverseSystem.milnorDifference
      (fun n : ℕ => (homologyFunctor A (r - 1)).obj (F.obj ⟨n⟩))
      (fun n : ℕ => (homologyFunctor A (r - 1)).map (F.map (homOfLE (Nat.le_succ n)).op))))
    (h₂ : ∀ n : ℕ, IsZero ((homologyFunctor A r).obj (F.obj ⟨n⟩))) :
    IsZero ((homologyFunctor A r).obj K) := by
  obtain ⟨_, _, _, hr⟩ := isDerivedLimit_homology_shortExact F K hK
  obtain ⟨_, _, _, _, _, _, _, hSE⟩ := hr r
  exact isZero_X₂_of_shortExact hSE (@isZero_cokernel_of_epi _ _ _ _ _ _ h₁ _)
    (isZero_limit_of_forall_isZero _ fun n => h₂ n.unop)

end DerivedCategory
