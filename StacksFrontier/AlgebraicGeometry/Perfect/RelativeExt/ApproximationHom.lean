module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Morphisms out of an approximation

Let `𝒜` be an abelian category and `p : P ⟶ E` a morphism of `D(𝒜)` which induces isomorphisms
on cohomology in degrees `> m` and a surjection in degree `m` (an approximation of `E` from `m`,
in the sense of [Stacks, Tag 08EM]). Then for every `Y` in `D^{≥ b}(𝒜)` and every `i` with
`i + m < b`, precomposition with `p`,

`Hom(E, Y[i]) ⟶ Hom(P, Y[i])`,

is bijective: the cone `C` of `p` lies in `D^{≤ m - 1}`, so `Hom(C, Y[i])` and `Hom(C[-1], Y[i])`
vanish ([Stacks, Tag 06XS]).

## Main results

* `DerivedCategory.isLE_cone_of_approximatesFrom`: the cone of `p` is `≤ m - 1`.
* `DerivedCategory.bijective_precomp_of_approximatesFrom`: the bijectivity.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The cone of an approximation from `m` is `≤ m - 1`.** -/
theorem isLE_cone_of_approximatesFrom (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (m : ℤ)
    (h : ∀ i : ℤ, m < i → IsIso ((homologyFunctor C i).map T.mor₁))
    (he : Epi ((homologyFunctor C m).map T.mor₁)) : T.obj₃.IsLE (m - 1) := by
  rw [isLE_iff]
  intro j hj
  have hepi : Epi ((homologyFunctor C j).map T.mor₁) := by
    rcases eq_or_lt_of_le (show m ≤ j by omega) with rfl | hmj
    · exact he
    · have := h j hmj
      infer_instance
  have := h (j + 1) (by omega)
  have h₂ : (homologyFunctor C j).map T.mor₂ = 0 :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT j).1 hepi
  have hδ : HomologySequence.δ T j (j + 1) (by omega) = 0 :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT j (j + 1) (by omega)).1 inferInstance
  have : Epi ((homologyFunctor C j).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT j (j + 1) (by omega)).2 hδ
  exact IsZero.of_epi_eq_zero _ h₂

/-- **Morphisms out of an approximation.** If `p : P ⟶ E` induces isomorphisms on cohomology in
degrees `> m` and a surjection in degree `m`, then for `Y` in `D^{≥ b}` and `i + m < b`,
precomposition with `p` is a bijection `Hom(E, Y[i]) ⟶ Hom(P, Y[i])`. -/
theorem bijective_precomp_of_approximatesFrom {P E : DerivedCategory C} (p : P ⟶ E) (m : ℤ)
    (h : ∀ i : ℤ, m < i → IsIso ((homologyFunctor C i).map p))
    (he : Epi ((homologyFunctor C m).map p)) (Y : DerivedCategory C) (b : ℤ) [Y.IsGE b]
    (i : ℤ) (hi : i + m < b) :
    Function.Bijective (fun x : E ⟶ Y⟦i⟧ => p ≫ x) := by
  obtain ⟨Cn, g, δ, hT⟩ := distinguished_cocone_triangle p
  have hC : Cn.IsLE (m - 1) :=
    isLE_cone_of_approximatesFrom (Triangle.mk p g δ) hT m h he
  have hY : (Y⟦i⟧).IsGE (b - i) := TStructure.t.isGE_shift Y b i (b - i) (by omega)
  refine ⟨fun x₁ x₂ hx => ?_, fun z => ?_⟩
  · have h0 : p ≫ (x₁ - x₂) = 0 := by
      rw [Preadditive.comp_sub, sub_eq_zero]
      exact hx
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ (Triangle.mk p g δ) hT (x₁ - x₂) h0
    have : TStructure.t.IsLE (Triangle.mk p g δ).obj₃ (m - 1) := hC
    have hy0 : y = 0 := TStructure.t.zero y (m - 1) (b - i) (by omega)
    rwa [hy0, comp_zero, sub_eq_zero] at hy
  · have hC' : (Cn⟦(-1 : ℤ)⟧).IsLE m := TStructure.t.isLE_shift Cn (m - 1) (-1) m (by omega)
    have : TStructure.t.IsLE (Triangle.mk p g δ).invRotate.obj₁ m := hC'
    have hz : (Triangle.mk p g δ).invRotate.mor₁ ≫ z = 0 :=
      TStructure.t.zero _ m (b - i) (by omega)
    obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) z hz
    exact ⟨x, hx.symm⟩

end DerivedCategory

end
