module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoFieldExtra

/-!
# Morphisms into an injective object placed in degree zero

Let `𝒜` be an abelian category and `I` an injective object of `𝒜`. For every object `M` of the
unbounded derived category `D(𝒜)`, taking cohomology in degree zero is a bijection
`Hom_{D(𝒜)}(M, I[0]) → Hom_𝒜(H⁰(M), I)`.

The proof uses the truncation triangle `τ_{≤ 0} M ⟶ M ⟶ τ_{≥ 1} M ⟶`: an object in degrees
`≥ 1` has no nonzero morphism into `I[0]` because `I` is injective, so restriction to `τ_{≤ 0} M`
is bijective, and on `τ_{≤ 0} M` the statement is
`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE`.

## Main results

* `DerivedCategory.map_eq_zero_of_isGE_of_injective_single_anyModel` — `Hom(Z, I[a]) = 0` for `Z`
  in degrees `≥ b > a`.
* `DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_injective` — the bijection
  `Hom_{D(𝒜)}(M, I[0]) → Hom_𝒜(H⁰(M), H⁰(I[0]))`.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Triangulated DerivedCategory.TStructure

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- For a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶` with `T₁` in degrees `≤ 0` and `T₃` in
degrees `≥ 1`, taking `H⁰` is a bijection `Hom(T₂, I[0]) → Hom(H⁰(T₂), H⁰(I[0]))`. -/
private theorem bijective_homologyFunctor_map_of_triangle (I : C) [Injective I]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) [T.obj₁.IsLE 0]
    [T.obj₃.IsGE 1] :
    Function.Bijective
      (fun g : T.obj₂ ⟶ (singleFunctor C 0).obj I ↦ (homologyFunctor C 0).map g) := by
  have : (T.obj₃⟦(-1 : ℤ)⟧).IsGE 2 := t.isGE_shift T.obj₃ 1 (-1) 2
  -- the map `T₁ ⟶ T₂` is an isomorphism on `H⁰`
  have : IsIso ((homologyFunctor C 0).map T.mor₁) := by
    have : Epi ((homologyFunctor C 0).map T.mor₁) :=
      (HomologySequence.epi_homologyMap_mor₁_iff T hT 0).2
        ((isZero_of_isGE T.obj₃ 1 0 (by omega)).eq_of_tgt _ _)
    have : Mono ((homologyFunctor C 0).map T.mor₁) :=
      (HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0 (by omega)).2
        ((isZero_of_isGE T.obj₃ 1 (-1) (by omega)).eq_of_src _ _)
    exact isIso_of_mono_of_epi _
  -- restriction along `T₁ ⟶ T₂` is bijective
  have hres : Function.Bijective
      (fun g : T.obj₂ ⟶ (singleFunctor C 0).obj I ↦ T.mor₁ ≫ g) := by
    refine ⟨fun g₁ g₂ hg ↦ ?_, fun g' ↦ ?_⟩
    · have hg' : T.mor₁ ≫ (g₁ - g₂) = 0 := by
        rw [Preadditive.comp_sub]
        exact sub_eq_zero.2 hg
      obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ T hT (g₁ - g₂) hg'
      rw [map_eq_zero_of_isGE_of_injective_single_anyModel 0 1 (by omega) h, comp_zero] at hh
      exact sub_eq_zero.1 hh
    · obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) g'
        (map_eq_zero_of_isGE_of_injective_single_anyModel
          (X := T.obj₃⟦(-1 : ℤ)⟧) 0 2 (by omega) _)
      exact ⟨g, hg.symm⟩
  have key : (fun g : T.obj₂ ⟶ (singleFunctor C 0).obj I ↦ (homologyFunctor C 0).map g) =
      (fun k : (homologyFunctor C 0).obj T.obj₁ ⟶
          (homologyFunctor C 0).obj ((singleFunctor C 0).obj I) ↦
            inv ((homologyFunctor C 0).map T.mor₁) ≫ k) ∘
        (fun g' : T.obj₁ ⟶ (singleFunctor C 0).obj I ↦ (homologyFunctor C 0).map g') ∘
        (fun g : T.obj₂ ⟶ (singleFunctor C 0).obj I ↦ T.mor₁ ≫ g) := by
    funext g
    simp
  have hinv : Function.Bijective (fun k : (homologyFunctor C 0).obj T.obj₁ ⟶
      (homologyFunctor C 0).obj ((singleFunctor C 0).obj I) ↦
        inv ((homologyFunctor C 0).map T.mor₁) ≫ k) :=
    ⟨fun k₁ k₂ h ↦ (cancel_epi _).1 h, fun k ↦ ⟨(homologyFunctor C 0).map T.mor₁ ≫ k, by simp⟩⟩
  rw [key]
  exact (hinv.comp
    (bijective_homologyFunctor_map_of_isLE_of_isGE T.obj₁ ((singleFunctor C 0).obj I) 0)).comp
      hres

/-- **Morphisms into an injective object in degree zero are read off `H⁰`.** For an injective
object `I` of `𝒜` and any object `M` of `D(𝒜)`, the map
`Hom_{D(𝒜)}(M, I[0]) → Hom_𝒜(H⁰(M), H⁰(I[0]))` is bijective. -/
theorem bijective_homologyFunctor_map_singleFunctor_of_injective (I : C) [Injective I]
    (M : DerivedCategory C) :
    Function.Bijective (fun g : M ⟶ (singleFunctor C 0).obj I ↦ (homologyFunctor C 0).map g) := by
  have : ((t.triangleLTGE 1).obj M).obj₁.IsLE 0 := t.isLE_truncLT_obj M 1 0
  have : ((t.triangleLTGE 1).obj M).obj₃.IsGE 1 :=
    inferInstanceAs (t.IsGE ((t.truncGE 1).obj M) 1)
  exact bijective_homologyFunctor_map_of_triangle I _ (t.triangleLTGE_distinguished 1 M)

end DerivedCategory
