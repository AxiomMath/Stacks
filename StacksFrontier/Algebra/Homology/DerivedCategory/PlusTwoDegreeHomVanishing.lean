module

public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomEqualDegree
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Morphisms between objects of `D⁺` with cohomology in degrees `1` and `2`

Let `C` be an abelian category and `X, Y` objects of `D⁺(C)` with cohomology in degrees `1` and
`2` only. A morphism `u : X ⟶ Y` with `H¹(u) = 0` is zero as soon as
`Hom(H²(X)[-2], H¹(Y)[-1]) = 0` and `Hom(H²(X), H²(Y)) = 0`: `u` vanishes on the truncation
`H¹(X)[-1] ⟶ X` (a morphism from `D^{≤ 1}` to `D^{≥ 1}` is read on `H¹`), so it factors through
`X ⟶ H²(X)[-2]`; the factor `H²(X)[-2] ⟶ Y` vanishes after `Y ⟶ H²(Y)[-2]`, hence factors through
`H¹(Y)[-1] ⟶ Y`, and vanishes.

This is the formal core of the mechanism `ℓᵉ K(S) = 0 ⇒ ℓᵉ Φ(α) = 0` in the single-level argument
for the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.DerivedCategoryPlus.singleFunctor_hom_eq_zero_of_subsingleton_ext`: a morphism
  `A[-m] ⟶ B[-k]` of `D⁺(C)` vanishes when `Ext^{m-k}(A, B) = 0`.
* `Stacks.DerivedCategoryPlus.eq_zero_of_singleFunctor_one_comp_eq_zero`.
* `Stacks.DerivedCategoryPlus.eq_zero_of_homology_one_map_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' v u

namespace Stacks.DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **A morphism `A[-m] ⟶ B[-k]` of `D⁺(C)` vanishes when `Ext^p(A, B) = 0`, `p + k = m`**: after
shifting by `m`, it is a class of `Ext^p(A, B)` (`CategoryTheory.Abelian.Ext.homEquiv`). -/
theorem singleFunctor_hom_eq_zero_of_subsingleton_ext [HasExt.{w'} C] (A B : C) (m k : ℤ) (p : ℕ)
    (hp : (p : ℤ) + k = m) (h : Subsingleton (Abelian.Ext.{w'} A B p))
    (f : (DerivedCategory.Plus.singleFunctor C m).obj A ⟶
      (DerivedCategory.Plus.singleFunctor C k).obj B) : f = 0 := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_zero]
  refine (shiftFunctor (DerivedCategory C) m).map_injective ?_
  rw [Functor.map_zero]
  let e₁ := ((DerivedCategory.singleFunctors C).shiftIso m 0 m (by omega)).app A
  let e₂ := ((DerivedCategory.singleFunctors C).shiftIso m (k - m) k (by omega)).app B ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (p : ℤ) (k - m) 0 (by omega)).app B).symm
  let g : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A)
      ((DerivedCategory.singleFunctor C 0).obj B) (p : ℤ) :=
    e₁.inv ≫ (shiftFunctor (DerivedCategory C) m).map (DerivedCategory.Plus.ι.map f) ≫ e₂.hom
  have hg : g = 0 := by
    simpa [Abelian.Ext.hom] using congrArg (fun z : Abelian.Ext.{w'} A B p => z.hom)
      (Subsingleton.elim (Abelian.Ext.homEquiv.symm g) 0)
  have h' : (shiftFunctor (DerivedCategory C) m).map (DerivedCategory.Plus.ι.map f) =
      e₁.hom ≫ g ≫ e₂.inv := by
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
    exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂.hom_inv_id).trans
      (Category.comp_id _))).symm
  rw [h', hg, zero_comp, comp_zero]
  rfl

/-- **A morphism `M[-1] ⟶ Y` with `Y ∈ D^{≥ 1}` vanishing on `H¹` is zero**: the equal-degree case
of the orthogonality of the canonical t-structure, read in `D(C)`. -/
theorem eq_zero_of_singleFunctor_one_comp_eq_zero {M : C} {Y : DerivedCategory.Plus C} [Y.IsGE 1]
    (f : (DerivedCategory.Plus.singleFunctor C 1).obj M ⟶ Y)
    (hf : (DerivedCategory.Plus.homologyFunctor C 1).map f = 0) : f = 0 := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_zero]
  exact DerivedCategory.eq_zero_of_isLE_of_isGE_of_homologyFunctor_map_eq_zero 1 _ hf

/-- A morphism vanishes if its conjugate by isomorphisms lies in a family of zero morphisms. -/
private theorem eq_zero_of_iso_comp_comp_iso_eq_zero {D : Type*} [Category D]
    [Limits.HasZeroMorphisms D] {A A' B B' : D} (e : A' ≅ A) (e' : B ≅ B')
    (h : ∀ g : A' ⟶ B', g = 0) (φ : A ⟶ B) : φ = 0 := by
  rw [← cancel_epi e.hom, ← cancel_mono e'.hom, comp_zero, zero_comp]
  exact h _

/-- **A morphism `u : X ⟶ Y` of `D⁺(C)` between objects with cohomology in degrees `1` and `2` is
zero if `H¹(u) = 0`, `Hom(H²(X)[-2], H¹(Y)[-1]) = 0` and `Hom(H²(X), H²(Y)) = 0`.** -/
theorem eq_zero_of_homology_one_map_eq_zero {X Y : DerivedCategory.Plus C} [X.IsGE 1] [X.IsLE 2]
    [Y.IsGE 1] [Y.IsLE 2] (u : X ⟶ Y) (hu : (DerivedCategory.Plus.homologyFunctor C 1).map u = 0)
    (h₁ : ∀ g : (DerivedCategory.Plus.singleFunctor C 2).obj
        ((DerivedCategory.Plus.homologyFunctor C 2).obj X) ⟶
      (DerivedCategory.Plus.singleFunctor C 1).obj
        ((DerivedCategory.Plus.homologyFunctor C 1).obj Y),
      g = 0)
    (h₂ : ∀ g : (DerivedCategory.Plus.homologyFunctor C 2).obj X ⟶
      (DerivedCategory.Plus.homologyFunctor C 2).obj Y, g = 0) : u = 0 := by
  have : X.IsLE (1 + 1) := ‹X.IsLE 2›
  have : Y.IsLE (1 + 1) := ‹Y.IsLE 2›
  obtain ⟨M, N, f, g, k, hT, -, ⟨eN⟩⟩ :=
    exists_distTriang_singleFunctor_of_isGE_of_isLE X 1
  obtain ⟨M', N', f', g', k', hT', ⟨eM'⟩, ⟨eN'⟩⟩ :=
    exists_distTriang_singleFunctor_of_isGE_of_isLE Y 1
  -- `u` vanishes on `M[-1] ⟶ X`
  have hfu : f ≫ u = 0 := eq_zero_of_singleFunctor_one_comp_eq_zero (f ≫ u) <| by
    rw [Functor.map_comp, hu, comp_zero]
  obtain ⟨w, hw⟩ := Triangle.yoneda_exact₂ _ hT u hfu
  -- the factor `N[-2] ⟶ Y` vanishes on `Y ⟶ N'[-2]`
  have hwg : w ≫ g' = 0 := by
    obtain ⟨φ, hφ⟩ := (DerivedCategory.Plus.singleFunctor C (1 + 1)).map_surjective (w ≫ g')
    have hφ0 : φ = 0 := eq_zero_of_iso_comp_comp_iso_eq_zero eN.symm eN' h₂ φ
    rw [← hφ, hφ0, Functor.map_zero]
  obtain ⟨w', hw'⟩ := Triangle.coyoneda_exact₂ _ hT' w hwg
  have hw'0 : w' = 0 := eq_zero_of_iso_comp_comp_iso_eq_zero
    ((DerivedCategory.Plus.singleFunctor C 2).mapIso eN.symm)
    ((DerivedCategory.Plus.singleFunctor C 1).mapIso eM') h₁ w'
  rw [hw, hw', hw'0, zero_comp, comp_zero]

end Stacks.DerivedCategoryPlus

end
