module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangleSequence

/-!
# The middle of the long exact sequence of `Φ` at a two-degree triangle

Let `C` be an abelian category, `Φ : D⁺(C) ⥤ D⁺(C)` a triangulated functor and
`G[-1] ⟶ Y ⟶ N[-2] ⟶ G[-1][1]` a distinguished triangle in `D⁺(C)` with `H⁻¹(Φ(N[0])) = 0` and
`H³(Φ Y) = 0`. The long exact cohomology sequence of the image triangle gives an exact sequence

`0 ⟶ H¹(Φ(G[0])) ⟶ H²(Φ Y) ⟶ H⁰(Φ(N[0])) ⟶ H²(Φ(G[0])) ⟶ 0`,

so there is a morphism `u : H²(Φ Y) ⟶ H⁰(Φ(N[0]))` with `H¹(Φ(G[0])) ≅ ker u` and
`H²(Φ(G[0])) ≅ coker u`.

For `Φ` the Fourier transform, `Y = Φ(F[0])` with `F` lisse, `G = H¹(Φ F)` and `N = H²(Φ F)`,
this exhibits `H¹(Φ G)` and `H²(Φ G)` as the kernel and the cokernel of a map
`H²(ΦΦ F) ⟶ H⁰(Φ N)` (step (a) of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.DerivedCategoryPlus.exists_kernel_cokernel_iso_homology_map_singleFunctor_of_distTriang`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C) [Φ.CommShift ℤ] [Φ.IsTriangulated]

/-- **`H¹(Φ(G[0]))` and `H²(Φ(G[0]))` are the kernel and the cokernel of a morphism
`H²(Φ Y) ⟶ H⁰(Φ(N[0]))`**, for a distinguished triangle `G[-1] ⟶ Y ⟶ N[-2] ⟶ G[-1][1]` with
`H⁻¹(Φ(N[0])) = 0` and `H³(Φ Y) = 0`, `Φ` triangulated: the long exact cohomology sequence of
the image triangle is `0 ⟶ H²(Φ(G[-1])) ⟶ H²(Φ Y) ⟶ H²(Φ(N[-2])) ⟶ H³(Φ(G[-1])) ⟶ 0`. -/
theorem exists_kernel_cokernel_iso_homology_map_singleFunctor_of_distTriang {G N : C}
    {Y : DerivedCategory.Plus C} (f : (DerivedCategory.Plus.singleFunctor C 1).obj G ⟶ Y)
    (g : Y ⟶ (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N)
    (h : (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N ⟶
      ((DerivedCategory.Plus.singleFunctor C 1).obj G)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory.Plus C))
    (hN : IsZero ((DerivedCategory.Plus.homologyFunctor C (-1)).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N))))
    (hY : IsZero ((DerivedCategory.Plus.homologyFunctor C 3).obj (Φ.obj Y))) :
    ∃ u : (DerivedCategory.Plus.homologyFunctor C 2).obj (Φ.obj Y) ⟶
        (DerivedCategory.Plus.homologyFunctor C 0).obj
          (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N)),
      Nonempty ((DerivedCategory.Plus.homologyFunctor C 1).obj
          (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj G)) ≅ kernel u) ∧
        Nonempty ((DerivedCategory.Plus.homologyFunctor C 2).obj
          (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj G)) ≅ cokernel u) := by
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let T := Triangle.mk f g h
  have hT' := Φ.map_distinguished _ hT
  have : Mono ((H.shift (2 : ℤ)).map ((Φ.mapTriangle.obj T).mor₁)) :=
    mono_homology_two_map_mor₁_of_distTriang Φ f g h hT hN
  have : Epi (H.homologySequenceδ (Φ.mapTriangle.obj T) 2 3 rfl) :=
    epi_homologySequenceδ_two_of_distTriang Φ f g h hT hY
  let u' := (H.shift (2 : ℤ)).map ((Φ.mapTriangle.obj T).mor₂)
  let eK : (H.shift (2 : ℤ)).obj (Φ.obj ((DerivedCategory.Plus.singleFunctor C 1).obj G)) ≅
      kernel u' :=
    IsLimit.conePointUniqueUpToIso (H.homologySequence_exact₂ _ hT' 2).fIsKernel (limit.isLimit _)
  let eC : (H.shift (3 : ℤ)).obj (Φ.obj ((DerivedCategory.Plus.singleFunctor C 1).obj G)) ≅
      cokernel u' :=
    IsColimit.coconePointUniqueUpToIso (H.homologySequence_exact₃ _ hT' 2 3 rfl).gIsCokernel
      (colimit.isColimit _)
  obtain ⟨e₁⟩ := nonempty_homology_map_singleFunctor_iso Φ 1 2 1 (by omega) G
  obtain ⟨e₂⟩ := nonempty_homology_map_singleFunctor_iso Φ 1 3 2 (by omega) G
  obtain ⟨e₃⟩ := nonempty_homology_map_singleFunctor_iso Φ (1 + 1) 2 0 (by omega) N
  let e₃' : (H.shift (2 : ℤ)).obj (Φ.obj ((DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N)) ≅
      (DerivedCategory.Plus.homologyFunctor C 0).obj
        (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N)) := e₃
  have i₃ : IsIso e₃'.hom := ⟨⟨e₃'.inv, e₃'.hom_inv_id, e₃'.inv_hom_id⟩⟩
  exact ⟨u' ≫ e₃'.hom, ⟨e₁.symm ≪≫ eK ≪≫
      (@kernelCompMono C _ _ _ _ _ u' e₃'.hom _ (@IsIso.mono_of_iso _ _ _ _ _ i₃)).symm⟩,
    ⟨e₂.symm ≪≫ eC ≪≫ (@cokernelCompIsIso C _ _ _ _ _ u' e₃'.hom _ i₃).symm⟩⟩

end Stacks.DerivedCategoryPlus

end
