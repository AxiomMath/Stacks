module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Morphisms in the derived category along maps which are isomorphisms on part of the cohomology

Let `v : M ⟶ M'` be a morphism of `D(C)` which is an isomorphism on cohomology in degrees `≤ m`.
Its cone lies in `D^{≥ m}`, so composing with `v` is a bijection `Hom(O, M) ≃ Hom(O, M')` for
every `O` in `D^{≤ k}` with `k < m`.  Dually, if `c : G ⟶ L` is an isomorphism on cohomology in
degrees `> m`, its cone lies in `D^{≤ m}`, and precomposing with `c` is a bijection
`Hom(L, B) ≃ Hom(G, B)` for every `B` in `D^{≥ n}` with `m + 1 < n`.

## Main results

* `DerivedCategory.bijective_comp_of_isIso_homologyMap_le`: composing with a map which is an
  isomorphism on cohomology in low degrees.
* `DerivedCategory.bijective_comp_shift_of_isIso_homologyMap_le`: the same after the shift
  by `-1`.
* `DerivedCategory.bijective_precomp_of_isIso_homologyMap_gt`: precomposing with a map which is
  an isomorphism on cohomology in high degrees.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The cohomology of the third vertex of a distinguished triangle vanishes in degree `i` if
the first map is an isomorphism on cohomology in degrees `i` and `i + 1`. -/
private theorem isZero_homology_obj₃_of_isIso_homologyMap_mor₁ {T : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang (DerivedCategory C)) (i : ℤ)
    (h₁ : IsIso ((homologyFunctor C i).map T.mor₁))
    (h₂ : IsIso ((homologyFunctor C (i + 1)).map T.mor₁)) :
    IsZero ((homologyFunctor C i).obj T.obj₃) :=
  (HomologySequence.exact₃ _ hT i (i + 1) rfl).isZero_X₂
    ((HomologySequence.epi_homologyMap_mor₁_iff _ hT i).1 inferInstance)
    ((HomologySequence.mono_homologyMap_mor₁_iff _ hT i (i + 1) rfl).1 inferInstance)

/-- **Composing with a map which is an isomorphism on cohomology in degrees `≤ m`** is a
bijection on morphisms out of an object of `D^{≤ k}`, `k < m`. -/
theorem bijective_comp_of_isIso_homologyMap_le {M M' : DerivedCategory C} (v : M ⟶ M') (m : ℤ)
    (hv : ∀ i : ℤ, i ≤ m → IsIso ((homologyFunctor C i).map v)) (O : DerivedCategory C) (k : ℤ)
    [O.IsLE k] (hk : k < m) :
    Function.Bijective (fun x : O ⟶ M => x ≫ v) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle v
  -- The cone lies in degrees `≥ m`; this is the base's
  -- `Stacks.Cohomology.BoxKunneth.isGE_obj₃_of_isIso_homologyMap_mor₁`
  -- (`StacksDraft.DeRham.RelativeKunnethTruncation`), inlined to keep its imports out.
  have hZ : Z.IsGE m := by
    rw [isGE_iff]
    intro i hi
    exact isZero_homology_obj₃_of_isIso_homologyMap_mor₁ hT i (hv i (by omega))
      (hv (i + 1) (by omega))
  have : (Z⟦(-1 : ℤ)⟧).IsGE (m + 1) := TStructure.t.isGE_shift Z m (-1) (m + 1)
  refine ⟨fun x x' hxx ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero]
    have h0 : (x - x') ≫ v = 0 := by
      rw [Preadditive.sub_comp]
      exact sub_eq_zero.2 hxx
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) (x - x') h0
    have hy0 := TStructure.t.zero_of_isLE_of_isGE y k (m + 1) (by omega) inferInstance this
    exact hy.trans ((congrArg (· ≫ _) hy0).trans zero_comp)
  · obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ hT y
      (TStructure.t.zero_of_isLE_of_isGE _ k m hk inferInstance hZ)
    exact ⟨x, hx.symm⟩

/-- **Composing with the shift by `-1` of a map which is an isomorphism on cohomology in
degrees `≤ m`** is a bijection on morphisms out of an object of `D^{≤ k}`, `k < m + 1`. -/
theorem bijective_comp_shift_of_isIso_homologyMap_le {M M' : DerivedCategory C} (v : M ⟶ M')
    (m : ℤ) (hv : ∀ i : ℤ, i ≤ m → IsIso ((homologyFunctor C i).map v)) (O : DerivedCategory C)
    (k : ℤ) [O.IsLE k] (hk : k < m + 1) :
    Function.Bijective (fun x : O ⟶ M⟦(-1 : ℤ)⟧ => x ≫ v⟦(-1 : ℤ)⟧') :=
  bijective_comp_of_isIso_homologyMap_le (v⟦(-1 : ℤ)⟧') (m + 1)
    (fun i hi => (NatIso.isIso_map_iff
      ((homologyFunctor C 0).shiftIso (-1 : ℤ) i (i - 1) (by omega)) v).2 (hv (i - 1) (by omega)))
    O k hk

/-- **Precomposing with a map which is an isomorphism on cohomology in degrees `> m`** is a
bijection on morphisms into an object of `D^{≥ n}`, `m + 1 < n`. -/
theorem bijective_precomp_of_isIso_homologyMap_gt {G L : DerivedCategory C} (c : G ⟶ L) (m : ℤ)
    (hc : ∀ i : ℤ, m < i → IsIso ((homologyFunctor C i).map c)) (B : DerivedCategory C) (n : ℤ)
    [B.IsGE n] (hn : m + 1 < n) :
    Function.Bijective (fun x : L ⟶ B => c ≫ x) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle c
  -- The cone lies in degrees `≤ m`; this is the base's
  -- `DerivedCategory.isLE_obj₃_of_isIso_homologyMap_mor₁`
  -- (`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualBounds`), inlined to keep its
  -- imports out.
  have hZ : Z.IsLE m := by
    rw [isLE_iff]
    intro i hi
    exact isZero_homology_obj₃_of_isIso_homologyMap_mor₁ hT i (hc i hi) (hc (i + 1) (by omega))
  have : (Z⟦(-1 : ℤ)⟧).IsLE (m + 1) := TStructure.t.isLE_shift Z m (-1) (m + 1)
  refine ⟨fun x x' hxx ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero]
    have h0 : c ≫ (x - x') = 0 := by
      rw [Preadditive.comp_sub]
      exact sub_eq_zero.2 hxx
    obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ _ hT (x - x') h0
    have hy0 := TStructure.t.zero_of_isLE_of_isGE y m n (by omega) hZ inferInstance
    exact hy.trans ((congrArg (_ ≫ ·) hy0).trans comp_zero)
  · obtain ⟨x, hx⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) y
      (TStructure.t.zero_of_isLE_of_isGE _ (m + 1) n hn this inferInstance)
    exact ⟨x, hx.symm⟩

end DerivedCategory
