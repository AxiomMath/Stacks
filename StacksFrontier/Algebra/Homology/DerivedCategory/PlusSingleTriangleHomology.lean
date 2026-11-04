module

public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Homology of the image of a short exact sequence under two triangulated functors

Let `C` be an abelian category and `F, G : D⁺(C) ⥤ D⁺(C)` triangulated functors. For a short
exact sequence `0 → X₁ → X₂ → X₃ → 0` in `C`, the triangle `X₁[0] → X₂[0] → X₃[0] → X₁[1]` is
distinguished, hence so is its image under `G ∘ F`, and the long exact cohomology sequence of
that triangle gives:

* `Hⁿ(GF(X₁[0])) → Hⁿ(GF(X₂[0]))` is a monomorphism if `Hⁿ⁻¹(GF(X₃[0])) = 0`;
* `Hⁿ(GF(X₂[0])) → Hⁿ(GF(X₃[0]))` is an epimorphism if `Hⁿ⁺¹(GF(X₁[0])) = 0`.

Consequently, if `X ↦ Hⁿ(GF(X[0]))` is concentrated in degree `n` and reflects zero objects on a
class of objects stable under subobjects and quotients, it is faithful on that class.

These are stated for two functors (rather than for their composite) so that they apply to a
composite of two copies of one concrete functor without unfolding it.

## Main results

* `Stacks.DerivedCategoryPlus.mono_homology_map_map_singleFunctor_map`
* `Stacks.DerivedCategoryPlus.epi_homology_map_map_singleFunctor_map`
* `Stacks.DerivedCategoryPlus.eq_zero_of_homology_map_map_singleFunctor_map_eq_zero`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  (F G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C) [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]

/-- The image under `G ∘ F` of the triangle of a short exact sequence is distinguished. -/
lemma map_map_singleTrianglePlus_distinguished {S : ShortComplex C} (hS : S.ShortExact) :
    G.mapTriangle.obj (F.mapTriangle.obj
      (Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
        ((DerivedCategory.Plus.singleFunctor C 0).map S.g)
        (Stacks.DerivedIndexing.singleδPlus hS))) ∈ distTriang (DerivedCategory.Plus C) :=
  G.map_distinguished _
    (F.map_distinguished _ (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS))

/-- **`Hⁿ¹(GF(-[0]))` preserves the monomorphism of a short exact sequence** when
`Hⁿ⁰(GF(X₃[0])) = 0`, `n₀ + 1 = n₁`. -/
lemma mono_homology_map_map_singleFunctor_map {S : ShortComplex C} (hS : S.ShortExact)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hz : IsZero ((DerivedCategory.Plus.homologyFunctor C n₀).obj
      (G.obj (F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₃))))) :
    Mono ((DerivedCategory.Plus.homologyFunctor C n₁).map
      (G.map (F.map ((DerivedCategory.Plus.singleFunctor C 0).map S.f)))) :=
  ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _
    (map_map_singleTrianglePlus_distinguished F G hS) n₀ n₁ h).2 (hz.eq_of_src _ _)

/-- **`Hⁿ⁰(GF(-[0]))` preserves the epimorphism of a short exact sequence** when
`Hⁿ¹(GF(X₁[0])) = 0`, `n₀ + 1 = n₁`. -/
lemma epi_homology_map_map_singleFunctor_map {S : ShortComplex C} (hS : S.ShortExact)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hz : IsZero ((DerivedCategory.Plus.homologyFunctor C n₁).obj
      (G.obj (F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))))) :
    Epi ((DerivedCategory.Plus.homologyFunctor C n₀).map
      (G.map (F.map ((DerivedCategory.Plus.singleFunctor C 0).map S.g)))) :=
  ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _
    (map_map_singleTrianglePlus_distinguished F G hS) n₀ n₁ h).2 (hz.eq_of_tgt _ _)

/-- **`X ↦ Hⁿ(GF(X[0]))` is faithful on a class `P` of objects** stable under subobjects and
quotients, on which `GF(X[0])` has cohomology only in degree `n` and `Hⁿ(GF(X[0])) = 0` only
for `X = 0`: it is exact on `P`, so it kills the image of a morphism it kills. -/
lemma eq_zero_of_homology_map_map_singleFunctor_map_eq_zero (P : C → Prop)
    (hPmono : ∀ {A B : C} (ι : A ⟶ B) [Mono ι], P B → P A)
    (hPepi : ∀ {A B : C} (π : A ⟶ B) [Epi π], P A → P B) (n : ℤ)
    (hconc : ∀ X : C, P X → ∀ i : ℤ, i ≠ n → IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj
      ((F ⋙ G).obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))))
    (hrefl : ∀ X : C, P X → IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
      ((F ⋙ G).obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) → IsZero X)
    {A B : C} (f : A ⟶ B) (hA : P A) (hB : P B)
    (hf : (DerivedCategory.Plus.homologyFunctor C n).map
      ((F ⋙ G).map ((DerivedCategory.Plus.singleFunctor C 0).map f)) = 0) : f = 0 := by
  let T := DerivedCategory.Plus.singleFunctor C 0 ⋙ F ⋙ G ⋙
    DerivedCategory.Plus.homologyFunctor C n
  let π := Abelian.factorThruImage f
  let ι := Abelian.image.ι f
  have hfac : π ≫ ι = f := Abelian.image.fac f
  let S₁ := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (S₁.exact_of_f_is_kernel (kernelIsKernel π)) inferInstance
      inferInstance
  let S₂ := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS₂ : S₂.ShortExact :=
    ShortComplex.ShortExact.mk' (S₂.exact_of_g_is_cokernel (cokernelIsCokernel ι)) inferInstance
      inferInstance
  have : Mono (T.map ι) := mono_homology_map_map_singleFunctor_map F G hS₂ (n - 1) n
    (by omega) (hconc _ (hPepi (cokernel.π ι) hB) _ (by omega))
  have : Epi (T.map π) := epi_homology_map_map_singleFunctor_map F G hS₁ n (n + 1)
    rfl (hconc _ (hPmono (kernel.ι π) hA) _ (by omega))
  have hπ : T.map π = 0 := by
    rw [← cancel_mono (T.map ι), Limits.zero_comp, ← T.map_comp, hfac]
    exact hf
  have hIz : IsZero (Abelian.image f) := hrefl _ (hPmono ι hB) (IsZero.of_epi_eq_zero _ hπ)
  rw [← hfac, hIz.eq_of_src ι 0, Limits.comp_zero]

/-- **(E1, abstract form) A morphism `φ : A ⟶ A` with `F((φ ≫ α)[0]) = 0`, for
a monomorphism `α : A ⟶ B` in the class `P` of
`Stacks.DerivedCategoryPlus.eq_zero_of_homology_map_map_singleFunctor_map_eq_zero`, is zero.** -/
lemma eq_zero_of_homology_map_map_singleFunctor_map_comp_mono_eq_zero (P : C → Prop)
    (hPmono : ∀ {A B : C} (ι : A ⟶ B) [Mono ι], P B → P A)
    (hPepi : ∀ {A B : C} (π : A ⟶ B) [Epi π], P A → P B) (n : ℤ)
    (hconc : ∀ X : C, P X → ∀ i : ℤ, i ≠ n → IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj
      ((F ⋙ G).obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))))
    (hrefl : ∀ X : C, P X → IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
      ((F ⋙ G).obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) → IsZero X)
    {A B : C} (α : A ⟶ B) [Mono α] (φ : A ⟶ A) (hB : P B)
    (hf : F.map ((DerivedCategory.Plus.singleFunctor C 0).map (φ ≫ α)) = 0) : φ = 0 := by
  rw [← cancel_mono α, Limits.zero_comp]
  exact eq_zero_of_homology_map_map_singleFunctor_map_eq_zero F G P hPmono hPepi n hconc
    hrefl (φ ≫ α) (hPmono α hB) hB
    (by rw [Functor.comp_map, hf, Functor.map_zero, Functor.map_zero])

end Stacks.DerivedCategoryPlus
