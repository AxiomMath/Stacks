module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Complex

/-!
# Čech cohomology of a finite direct sum of presheaves

Let `P : Lᵒᵖ ⥤ ModuleCat k` be a presheaf of modules on a complete lattice which is the direct sum
of finitely many presheaves `F i`, exhibited by morphisms `ι_i : F i ⟶ P` and `π_i : P ⟶ F i`
with `π_j ∘ ι_i = δ_{ij}` and `∑_i ι_i ∘ π_i = id`. Then, for any family `U`, the Čech cohomology
of `P` is the product of the Čech cohomologies of the `F i`, through the maps induced by the
`π_i`, with inverse induced by the `ι_i`.

## Main results

* `Stacks.HodgeWeil.cechMap_add`, `Stacks.HodgeWeil.cechMap_comp`, `Stacks.HodgeWeil.cechMap_id`:
  the map on Čech cohomology induced by a morphism of presheaves is additive and functorial.
* `Stacks.HodgeWeil.cechSumEquiv`: `Ȟ^n(U, P) ≅ ∏_i Ȟ^n(U, F i)`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.HodgeWeil

open Stacks.CechKunneth

variable {k : Type u} [CommRing k] {L : Type u} [CompleteLattice L] {κ : Type u} (U : κ → L)

section Functoriality

variable {P P' P'' : Lᵒᵖ ⥤ ModuleCat.{u} k}

/-- The map on Čech cohomology induced by a sum of morphisms of presheaves is the sum of the
maps. -/
theorem cechMap_add (f g : P ⟶ P') (n : ℕ) : Hmap U (f + g) n = Hmap U f n + Hmap U g n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
  rw [LinearMap.add_apply, Hmap_Hmk, Hmap_Hmk, Hmap_Hmk, ← Hmk_add]
  exact Hmk_congr _ _ (funext fun s => rfl) _ _

/-- The map on Čech cohomology induced by the zero morphism is zero. -/
theorem cechMap_zero (n : ℕ) : Hmap U (0 : P ⟶ P') n = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
  rw [Hmap_Hmk, LinearMap.zero_apply, ← Hmk_zero P' U n]
  exact Hmk_congr _ _ (funext fun s => rfl) _ _

/-- The map on Čech cohomology induced by a finite sum of morphisms is the sum of the maps. -/
theorem cechMap_sum {ι : Type*} (s : Finset ι) (f : ι → (P ⟶ P')) (n : ℕ) :
    Hmap U (∑ i ∈ s, f i) n = ∑ i ∈ s, Hmap U (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cechMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cechMap_add, ih]

/-- The map on Čech cohomology induced by a composite is the composite of the maps. -/
theorem cechMap_comp (f : P ⟶ P') (g : P' ⟶ P'') (n : ℕ) :
    Hmap U (f ≫ g) n = Hmap U g n ∘ₗ Hmap U f n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
  rfl

/-- The map on Čech cohomology induced by the identity is the identity. -/
theorem cechMap_id (n : ℕ) : Hmap U (𝟙 P) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
  rfl

end Functoriality

section Sum

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {F : ι → Lᵒᵖ ⥤ ModuleCat.{u} k}
  {P : Lᵒᵖ ⥤ ModuleCat.{u} k} (inc : ∀ i, F i ⟶ P) (proj : ∀ i, P ⟶ F i)

/-- **The Čech cohomology of a finite direct sum of presheaves is the product of the Čech
cohomologies of the summands**, through the maps induced by the projections. -/
def cechSumEquiv (hinc : ∀ i, inc i ≫ proj i = 𝟙 (F i))
    (hne : ∀ i j, i ≠ j → inc i ≫ proj j = 0) (hsum : ∑ i, proj i ≫ inc i = 𝟙 P) (n : ℕ) :
    H P U n ≃ₗ[k] ∀ i, H (F i) U n where
  toFun x i := Hmap U (proj i) n x
  map_add' x y := funext fun i => map_add _ x y
  map_smul' c x := funext fun i => map_smul _ c x
  invFun y := ∑ i, Hmap U (inc i) n (y i)
  left_inv x := by
    have h := congrArg (fun φ => Hmap U φ n x) hsum
    simp only [cechMap_sum, cechMap_comp, cechMap_id, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h
  right_inv y := by
    funext j
    change Hmap U (proj j) n (∑ i, Hmap U (inc i) n (y i)) = y j
    rw [map_sum, Finset.sum_eq_single j]
    · rw [← LinearMap.comp_apply, ← cechMap_comp, hinc, cechMap_id, LinearMap.id_apply]
    · intro i _ hij
      rw [← LinearMap.comp_apply, ← cechMap_comp, hne i j hij, cechMap_zero, LinearMap.zero_apply]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

variable (hinc : ∀ i, inc i ≫ proj i = 𝟙 (F i)) (hne : ∀ i j, i ≠ j → inc i ≫ proj j = 0)
  (hsum : ∑ i, proj i ≫ inc i = 𝟙 P)

omit [DecidableEq ι] in
/-- The `i`-th component of `cechSumEquiv` is the map induced by the projection `π_i`. -/
theorem cechSumEquiv_apply (n : ℕ) (x : H P U n) (i : ι) :
    cechSumEquiv U inc proj hinc hne hsum n x i = Hmap U (proj i) n x :=
  rfl

omit [DecidableEq ι] in
/-- The inverse of `cechSumEquiv` sends a family of classes to the sum of their images under the
maps induced by the inclusions `ι_i`. -/
theorem cechSumEquiv_symm_apply (n : ℕ) (y : ∀ i, H (F i) U n) :
    (cechSumEquiv U inc proj hinc hne hsum n).symm y = ∑ i, Hmap U (inc i) n (y i) :=
  rfl

end Sum

end Stacks.HodgeWeil

end
