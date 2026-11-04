module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangle

/-!
# The ends of the long exact sequence of `Φ` at a two-degree triangle

Let `C` be an abelian category, `Φ : D⁺(C) ⥤ D⁺(C)` a triangulated functor and
`G[-1] ⟶ Y ⟶ N[-2] ⟶ G[-1][1]` a distinguished triangle in `D⁺(C)`. If `H⁻¹(Φ(N[0])) = 0` and
`H³(Φ Y) = 0`, the long exact cohomology sequence of the image triangle in degrees `2` and `3`
gives a monomorphism `H¹(Φ(G[0])) ⟶ H²(Φ Y)` and an epimorphism `H⁰(Φ(N[0])) ⟶ H²(Φ(G[0]))`.

For `Φ` the Fourier transform, `Y = Φ(F[0])` with `F` lisse, `G = H¹(Φ F)` and `N = H²(Φ F)`
punctual, this is the sequence `0 → H¹(Φ G) → F' → H⁰(Φ N) → H²(Φ G) → 0` of the step (a) of the
single-level argument for the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), `F' = H²(ΦΦ F)`.

## Main results

* `Stacks.DerivedCategoryPlus.mono_homology_two_map_mor₁_of_distTriang`.
* `Stacks.DerivedCategoryPlus.epi_homologySequenceδ_two_of_distTriang`.
* `Stacks.DerivedCategoryPlus.exists_mono_epi_homology_map_singleFunctor_of_distTriang`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C) [Φ.CommShift ℤ] [Φ.IsTriangulated]

/-- **`H²(Φ(G[-1])) ⟶ H²(Φ Y)` is a monomorphism** for a distinguished triangle
`G[-1] ⟶ Y ⟶ N[-2] ⟶ G[-1][1]` with `H⁻¹(Φ(N[0])) = 0`: the preceding term of the long exact
sequence is `H¹(Φ(N[-2])) = H⁻¹(Φ(N[0]))`. -/
theorem mono_homology_two_map_mor₁_of_distTriang {G N : C}
    {Y : DerivedCategory.Plus C} (f : (DerivedCategory.Plus.singleFunctor C 1).obj G ⟶ Y)
    (g : Y ⟶ (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N)
    (h : (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N ⟶
      ((DerivedCategory.Plus.singleFunctor C 1).obj G)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory.Plus C))
    (hN : IsZero ((DerivedCategory.Plus.homologyFunctor C (-1)).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N)))) :
    Mono ((DerivedCategory.Plus.homologyFunctor C 2).map (Φ.map f)) := by
  have hT' := Φ.map_distinguished _ hT
  obtain ⟨e₃⟩ := nonempty_homology_map_singleFunctor_iso Φ (1 + 1) 1 (-1) (by omega) N
  have h₃ : IsZero ((DerivedCategory.Plus.homologyFunctor C 1).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N))) := hN.of_iso e₃
  exact ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT'
    1 2 (by omega)).2 (h₃.eq_of_src _ _)

/-- **The connecting map `H²(Φ(N[-2])) ⟶ H³(Φ(G[-1]))` is an epimorphism** for a distinguished
triangle `G[-1] ⟶ Y ⟶ N[-2] ⟶ G[-1][1]` with `H³(Φ Y) = 0`. -/
theorem epi_homologySequenceδ_two_of_distTriang {G N : C}
    {Y : DerivedCategory.Plus C} (f : (DerivedCategory.Plus.singleFunctor C 1).obj G ⟶ Y)
    (g : Y ⟶ (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N)
    (h : (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N ⟶
      ((DerivedCategory.Plus.singleFunctor C 1).obj G)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory.Plus C))
    (hY : IsZero ((DerivedCategory.Plus.homologyFunctor C 3).obj (Φ.obj Y))) :
    Epi ((DerivedCategory.Plus.homologyFunctor C 0).homologySequenceδ
      (Φ.mapTriangle.obj (Triangle.mk f g h)) 2 3 rfl) := by
  have hT' := Φ.map_distinguished _ hT
  exact ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_exact₁ _ hT' 2 3
    rfl).epi_f (hY.eq_of_tgt _ _)

/-- **`0 ⟶ H¹(Φ(G[0])) ⟶ H²(Φ Y)` and `H⁰(Φ(N[0])) ⟶ H²(Φ(G[0])) ⟶ 0`** for a distinguished
triangle `G[-1] ⟶ Y ⟶ N[-2] ⟶ G[-1][1]` with `H⁻¹(Φ(N[0])) = 0` and `H³(Φ Y) = 0`, `Φ`
triangulated: the two ends of the long exact cohomology sequence of the image triangle in
degrees `2` and `3`. -/
theorem exists_mono_epi_homology_map_singleFunctor_of_distTriang {G N : C}
    {Y : DerivedCategory.Plus C} (f : (DerivedCategory.Plus.singleFunctor C 1).obj G ⟶ Y)
    (g : Y ⟶ (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N)
    (h : (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N ⟶
      ((DerivedCategory.Plus.singleFunctor C 1).obj G)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory.Plus C))
    (hN : IsZero ((DerivedCategory.Plus.homologyFunctor C (-1)).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N))))
    (hY : IsZero ((DerivedCategory.Plus.homologyFunctor C 3).obj (Φ.obj Y))) :
    (∃ m : (DerivedCategory.Plus.homologyFunctor C 1).obj
        (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj G)) ⟶
        (DerivedCategory.Plus.homologyFunctor C 2).obj (Φ.obj Y), Mono m) ∧
      ∃ p : (DerivedCategory.Plus.homologyFunctor C 0).obj
          (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N)) ⟶
        (DerivedCategory.Plus.homologyFunctor C 2).obj
          (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj G)), Epi p := by
  have := mono_homology_two_map_mor₁_of_distTriang Φ f g h hT hN
  have hδ := epi_homologySequenceδ_two_of_distTriang Φ f g h hT hY
  obtain ⟨e₁⟩ := nonempty_homology_map_singleFunctor_iso Φ 1 2 1 (by omega) G
  obtain ⟨e₁'⟩ := nonempty_homology_map_singleFunctor_iso Φ 1 3 2 (by omega) G
  obtain ⟨e₃⟩ := nonempty_homology_map_singleFunctor_iso Φ (1 + 1) 2 0 (by omega) N
  exact ⟨⟨e₁.inv ≫ (DerivedCategory.Plus.homologyFunctor C 2).map (Φ.map f), inferInstance⟩,
    ⟨e₃.inv ≫ (DerivedCategory.Plus.homologyFunctor C 0).homologySequenceδ
      (Φ.mapTriangle.obj (Triangle.mk f g h)) 2 3 rfl ≫ e₁'.hom,
      epi_comp' (IsIso.epi_of_iso e₃.inv) (epi_comp' hδ (IsIso.epi_of_iso e₁'.hom))⟩⟩

end Stacks.DerivedCategoryPlus

end
