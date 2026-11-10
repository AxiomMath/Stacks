module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusSingleTriangleHomology

/-!
# Objects of `D⁺` with cohomology in two adjacent degrees, and a triangulated functor on them

Let `C` be an abelian category. An object `X` of `D⁺(C)` with cohomology only in degrees `a` and
`a + 1` sits in a distinguished triangle

`M[-a] ⟶ X ⟶ N[-a-1] ⟶ M[-a][1]`, `M ≅ Hᵃ(X)`, `N ≅ Hᵃ⁺¹(X)`,

the truncation triangle `τ_{≤a} X ⟶ X ⟶ τ_{>a} X` of the canonical t-structure. For a
triangulated functor `Φ : D⁺(C) ⥤ D⁺(C)`, the cohomology of `Φ` at a shifted single object is that
at the unshifted one, shifted: `Hᵇ(Φ(M[-a])) ≅ Hᶜ(Φ(M[0]))` for `c + a = b`.

Applying `Φ` to the triangle of `X` with `a = 1` gives, from the long exact cohomology sequence,
`H⁰(Φ(H¹(X)[0])) = 0` as soon as `H¹(Φ X) = 0` and `H⁻²(Φ(H²(X)[0])) = 0`. This is the step (a)
of the single-level argument for the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), for `X = Φ(F[0])`, `Φ` the Fourier
transform and `F` lisse: `ΦΦF` lives in degree `2`, so the Fourier transform of `G = H¹(Φ F)` has
no `H⁰`.

## Main results

* `Stacks.DerivedCategoryPlus.exists_distTriang_singleFunctor_of_isGE_of_isLE`.
* `Stacks.DerivedCategoryPlus.nonempty_homology_map_singleFunctor_iso`.
* `Stacks.DerivedCategoryPlus.isZero_homology_zero_map_singleFunctor_of_distTriang`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- `Hᵃ(M[-a]) ≅ M` in `D⁺(C)`. -/
noncomputable def homologySingleFunctorIso (a : ℤ) (M : C) :
    (DerivedCategory.Plus.homologyFunctor C a).obj
      ((DerivedCategory.Plus.singleFunctor C a).obj M) ≅ M :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso C a).app M

/-- **An object of `D⁺(C)` with cohomology in degrees `a` and `a + 1` only is an extension of
`Hᵃ⁺¹(X)[-a-1]` by `Hᵃ(X)[-a]`**: the truncation triangle `τ_{≤a} X ⟶ X ⟶ τ_{>a} X`, both of
whose outer vertices have cohomology in a single degree. -/
theorem exists_distTriang_singleFunctor_of_isGE_of_isLE (X : DerivedCategory.Plus C) (a : ℤ)
    [X.IsGE a] [X.IsLE (a + 1)] :
    ∃ (M N : C) (f : (DerivedCategory.Plus.singleFunctor C a).obj M ⟶ X)
      (g : X ⟶ (DerivedCategory.Plus.singleFunctor C (a + 1)).obj N)
      (h : (DerivedCategory.Plus.singleFunctor C (a + 1)).obj N ⟶
        ((DerivedCategory.Plus.singleFunctor C a).obj M)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (DerivedCategory.Plus C) ∧
        Nonempty (M ≅ (DerivedCategory.Plus.homologyFunctor C a).obj X) ∧
        Nonempty (N ≅ (DerivedCategory.Plus.homologyFunctor C (a + 1)).obj X) := by
  let t := DerivedCategory.Plus.TStructure.t (C := C)
  let T := (t.triangleLEGT a).obj X
  have hT : T ∈ distTriang _ := t.triangleLEGT_distinguished a X
  have : t.IsGE T.obj₁ a := inferInstanceAs (t.IsGE ((t.truncLE a).obj X) a)
  have : t.IsLE T.obj₁ a := inferInstanceAs (t.IsLE ((t.truncLE a).obj X) a)
  have : t.IsGE T.obj₃ (a + 1) := inferInstanceAs (t.IsGE ((t.truncGT a).obj X) (a + 1))
  have : t.IsLE T.obj₃ (a + 1) := inferInstanceAs (t.IsLE ((t.truncGT a).obj X) (a + 1))
  obtain ⟨M, ⟨e₁⟩⟩ := DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₁ a
  obtain ⟨N, ⟨e₃⟩⟩ :=
    DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ (a + 1)
  have hI₁ := DerivedCategory.Plus.isIso_homologyMap_truncLEι_app X a a le_rfl
  have hI₃ := DerivedCategory.Plus.isIso_homologyMap_truncGTπ_app X (a + 1) a (by omega)
  refine ⟨M, N, e₁.inv ≫ T.mor₁, T.mor₂ ≫ e₃.hom, e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧', ?_,
    ⟨(homologySingleFunctorIso a M).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor C a).mapIso e₁.symm ≪≫
      @asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor C a).map
        ((DerivedCategory.Plus.TStructure.t.truncLEι a).app X)) hI₁⟩,
    ⟨(homologySingleFunctorIso (a + 1) N).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor C (a + 1)).mapIso e₃.symm ≪≫
      (@asIso _ _ _ _ ((DerivedCategory.Plus.homologyFunctor C (a + 1)).map
        ((DerivedCategory.Plus.TStructure.t.truncGTπ a).app X)) hI₃).symm⟩⟩
  refine isomorphic_distinguished T hT _ ?_
  refine Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm ?_ ?_ ?_
  · exact Category.comp_id _
  · change (T.mor₂ ≫ e₃.hom) ≫ e₃.inv = 𝟙 X ≫ T.mor₂
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp _).symm
  · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Iso.symm_hom,
      Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]

variable (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C) [Φ.CommShift ℤ]

/-- **`Hᵇ(Φ(M[-a])) ≅ Hᶜ(Φ(M[0]))` for `c + a = b`**, for a functor `Φ` commuting with the
shift: `M[-a] = M[0][-a]`, `Φ(K[-a]) ≅ Φ(K)[-a]` and `Hᵇ(L[-a]) = Hᶜ(L)`. -/
theorem nonempty_homology_map_singleFunctor_iso (a b c : ℤ) (h : c + a = b) (M : C) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor C b).obj
        (Φ.obj ((DerivedCategory.Plus.singleFunctor C a).obj M)) ≅
      (DerivedCategory.Plus.homologyFunctor C c).obj
        (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M))) := by
  let e₁ : (DerivedCategory.Plus.singleFunctor C a).obj M ≅
      ((DerivedCategory.Plus.singleFunctor C 0).obj M)⟦-a⟧ :=
    (((DerivedCategory.Plus.singleFunctors C).shiftIso (-a) a 0 (by omega)).app M).symm
  let e₂ := Φ.mapIso e₁ ≪≫ (Φ.commShiftIso (-a)).app _
  exact ⟨(DerivedCategory.Plus.homologyFunctor C b).mapIso e₂ ≪≫
    ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso (-a) b c (by omega)).app _⟩

variable [Φ.IsTriangulated]

/-- **`H⁰(Φ(G[0])) = 0`** for a distinguished triangle `G[-1] ⟶ Y ⟶ N[-2] ⟶ G[-1][1]` with
`H¹(Φ Y) = 0` and `H⁻²(Φ(N[0])) = 0`, `Φ` triangulated: in the long exact cohomology sequence of
the image triangle, `H¹(Φ(G[-1])) = H⁰(Φ(G[0]))` sits between `H⁰(Φ(N[-2])) = H⁻²(Φ(N[0]))` and
`H¹(Φ Y)`. -/
theorem isZero_homology_zero_map_singleFunctor_of_distTriang {G N : C}
    {Y : DerivedCategory.Plus C} (f : (DerivedCategory.Plus.singleFunctor C 1).obj G ⟶ Y)
    (g : Y ⟶ (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N)
    (h : (DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N ⟶
      ((DerivedCategory.Plus.singleFunctor C 1).obj G)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory.Plus C))
    (hY : IsZero ((DerivedCategory.Plus.homologyFunctor C 1).obj (Φ.obj Y)))
    (hN : IsZero ((DerivedCategory.Plus.homologyFunctor C (-2)).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj N)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor C 0).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 0).obj G))) := by
  have hT' := Φ.map_distinguished _ hT
  have hex := (DerivedCategory.Plus.homologyFunctor C 0).homologySequence_exact₁ _ hT' 0 1
    (by omega)
  obtain ⟨e₃⟩ := nonempty_homology_map_singleFunctor_iso Φ (1 + 1) 0 (-2) (by omega) N
  obtain ⟨e₁⟩ := nonempty_homology_map_singleFunctor_iso Φ 1 1 0 (by omega) G
  have h₃ : IsZero ((DerivedCategory.Plus.homologyFunctor C 0).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C (1 + 1)).obj N))) := hN.of_iso e₃
  have h₁ : IsZero ((DerivedCategory.Plus.homologyFunctor C 1).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor C 1).obj G))) :=
    hex.isZero_X₂ (h₃.eq_of_src _ _) (hY.eq_of_tgt _ _)
  exact h₁.of_iso e₁.symm

end Stacks.DerivedCategoryPlus

end
