module

public import StacksFrontier.CategoryTheory.Triangulated.HomologicalDualityPairing
public import StacksFrontier.Algebra.Homology.DerivedCategory.TopDegreeTest

/-!
# Yoneda duality in `Ext` as duality for a homological functor on `D⁺`

Let `𝒜` be an abelian category, `O`, `D`, `F` objects, `N` a natural number and
`t : Ext^N(O, D) → B` a trace. The Yoneda pairing `Ext^i(O, F) × Ext^j(F, D) → B`
(`CategoryTheory.Abelian.Ext.IsDualityPerfect`) is the pairing of the homological functor
`H = Hom_{D⁺}(O[0], -)` on `D⁺(𝒜)` (`Stacks.HomologicalDuality.IsPerfect`) at `F[0]`, with
dualizing object `D[0]` and the trace `τ` on `Hom(O[0], D[0][N])` corresponding to `t`
(`Stacks.TopTruncationExt.extPlus` identifies `Ext^m(X, Y)` with `Hom(X[0], Y[0][m])`, compatibly
with composition). The degrees differ: `IsPerfect` asks for all integers `i + j = N`, and the
pairing vanishes on both sides outside `0 ≤ i, j`, except for `Ext^q(O, F)` and `Ext^q(F, D)` with
`q > N`. So:

* duality at `F[0]` for `H` gives duality at `F` in `Ext`
  (`Stacks.HomologicalDuality.isDualityPerfect_of_isPerfect_coyoneda`);
* duality at `F` in `Ext`, together with `Ext^q(O, F) = 0` and `Ext^q(F, D) = 0` for `q > N`,
  gives duality at `F[0]` for `H`
  (`Stacks.HomologicalDuality.isPerfect_coyoneda_of_isDualityPerfect`).

This is how Poincaré duality for sheaves (in `Ext`) enters the five lemma for complexes in the
proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.HomologicalDuality.isDualityPerfect_of_isPerfect_coyoneda`.
* `Stacks.HomologicalDuality.isPerfect_coyoneda_of_isDualityPerfect`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w

namespace Stacks.HomologicalDuality

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] [HasExt.{w} 𝒜]

open Stacks.TopTruncationExt

/-- The map `extPlus : Ext^m(X, Y) → Hom(X[0], Y[0][m])` is injective. -/
theorem extPlus_injective (X Y : 𝒜) (m : ℕ) :
    Function.Injective (extPlus : Ext.{w} X Y m → _) := by
  intro e₁ e₂ h
  apply Ext.ext
  rw [← extPlus_map_ι e₁, ← extPlus_map_ι e₂, h]

/-- The map `extPlus` is additive. -/
theorem extPlus_add {X Y : 𝒜} {m : ℕ} (e₁ e₂ : Ext.{w} X Y m) :
    extPlus (e₁ + e₂) = extPlus e₁ + extPlus e₂ := by
  apply map_ι_injective
  dsimp only
  rw [ShiftedHom.map_add, extPlus_map_ι, extPlus_map_ι, extPlus_map_ι, Ext.add_hom]
  rfl

/-- `extPlus` as an additive map. -/
def extPlusHom (X Y : 𝒜) (m : ℕ) :
    Ext.{w} X Y m →+ ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X ⟶
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj Y)⟦(m : ℤ)⟧) where
  toFun := extPlus
  map_zero' := by
    rw [← sub_self (0 : Ext.{w} X Y m), ← add_left_inj (extPlus (0 : Ext.{w} X Y m)),
      ← extPlus_add]
    simp
  map_add' := extPlus_add

/-- The map `extPlus : Ext^m(X, Y) → Hom(X[0], Y[0][m])` is bijective. -/
theorem extPlus_bijective (X Y : 𝒜) (m : ℕ) :
    Function.Bijective (extPlus : Ext.{w} X Y m → _) :=
  ⟨extPlus_injective X Y m, extPlus_surjective X Y m⟩

omit [HasExt 𝒜] in
/-- Morphisms `X[0] ⟶ Y[0][n]` of `D⁺(𝒜)` vanish for `n < 0`. -/
theorem subsingleton_hom_single_shift_of_neg (X Y : 𝒜) {n : ℤ} (hn : n < 0) :
    Subsingleton ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X ⟶
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj Y)⟦n⟧) := by
  refine ⟨fun f g => ?_⟩
  have hz : ∀ φ : (DerivedCategory.Plus.singleFunctor 𝒜 0).obj X ⟶
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj Y)⟦n⟧, φ = 0 := by
    intro φ
    apply DerivedCategory.Plus.ι.map_injective
    rw [Functor.map_zero]
    apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso n).hom.app _)).1
    rw [zero_comp]
    have : DerivedCategory.TStructure.t.IsLE
        (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X)) 0 :=
      inferInstanceAs
        (DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor 𝒜 0).obj X) 0)
    have : DerivedCategory.TStructure.t.IsGE
        (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj Y)) 0 :=
      inferInstanceAs
        (DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor 𝒜 0).obj Y) 0)
    have hge := DerivedCategory.TStructure.t.isGE_shift
      (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj Y)) 0 n (-n)
      (by omega)
    have : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.Plus.ι ⋙
        shiftFunctor (DerivedCategory 𝒜) n).obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj Y))
        (-n) := hge
    exact DerivedCategory.TStructure.t.zero _ 0 (-n) (by omega)
  rw [hz f, hz g]

/-- A map between groups with at most one element, the source nonempty, is bijective. -/
lemma bijective_of_subsingleton {X Y : Type*} [Subsingleton X] [Subsingleton Y] (f : X → Y)
    (x : X) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨x, Subsingleton.elim _ _⟩⟩

variable (O D : 𝒜) (N : ℕ) {B : Type*} [AddCommGroup B] (t : Ext.{w} O D N →+ B)
  (τ : ((preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj O))).obj
    (((DerivedCategory.Plus.singleFunctor 𝒜 0).obj D)⟦(N : ℤ)⟧)) →+ B)
  (hτ : ∀ x : Ext.{w} O D N, τ (extPlus x) = t x)

include hτ in
/-- The two pairings agree under `extPlus`. -/
lemma pairing_coyoneda_extPlus (F : 𝒜) {i j : ℕ} (h : i + j = N) (x : Ext.{w} O F i)
    (y : Ext.{w} F D j) :
    pairing (preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj O)))
        ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj D) (N : ℤ) τ
        ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F) (i : ℤ) (j : ℤ) (by omega)
        (extPlus x) (extPlus y) = Ext.dualityPairing O D N t F h x y := by
  simp only [Ext.dualityPairing_apply]
  rw [← hτ, extPlus_comp x y h]
  rfl

include hτ in
/-- **Duality for `Hom_{D⁺}(O[0], -)` at `F[0]` gives Yoneda duality at `F`.** -/
theorem isDualityPerfect_of_isPerfect_coyoneda (F : 𝒜)
    (hF : IsPerfect (preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj O)))
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj D) (N : ℤ) τ
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F)) :
    Ext.IsDualityPerfect O D N t F := by
  intro i j h
  exact (bijective_iff_of_comp _ _ extPlus (extPlus_bijective O F i) (extPlusHom F D j)
    (extPlus_bijective F D j) (fun x y => pairing_coyoneda_extPlus O D N t τ hτ F h x y)).2
    (hF i j (by omega))

include hτ in
/-- **Yoneda duality at `F` gives duality for `Hom_{D⁺}(O[0], -)` at `F[0]`**, when
`Ext^q(O, F) = 0` and `Ext^q(F, D) = 0` for `q > N`. -/
theorem isPerfect_coyoneda_of_isDualityPerfect (F : 𝒜) (hF : Ext.IsDualityPerfect O D N t F)
    (hO : ∀ q : ℕ, N < q → Subsingleton (Ext.{w} O F q))
    (hD : ∀ q : ℕ, N < q → Subsingleton (Ext.{w} F D q)) :
    IsPerfect (preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj O)))
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj D) (N : ℤ) τ
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F) := by
  intro i j h
  rcases lt_or_ge i 0 with hi | hi
  · obtain ⟨j', rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
    have := subsingleton_hom_single_shift_of_neg O F hi
    have : Subsingleton ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F ⟶
        ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj D)⟦(j' : ℤ)⟧) := by
      have := hD j' (by omega)
      exact (extPlus_surjective F D j').subsingleton
    exact bijective_of_subsingleton (X := (DerivedCategory.Plus.singleFunctor 𝒜 0).obj O ⟶
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F)⟦i⟧) _ 0
  rcases lt_or_ge j 0 with hj | hj
  · obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have := subsingleton_hom_single_shift_of_neg F D hj
    have : Subsingleton ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj O ⟶
        ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F)⟦(i' : ℤ)⟧) := by
      have := hO i' (by omega)
      exact (extPlus_surjective O F i').subsingleton
    exact bijective_of_subsingleton (X := (DerivedCategory.Plus.singleFunctor 𝒜 0).obj O ⟶
      ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj F)⟦(i' : ℤ)⟧) _ 0
  obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
  obtain ⟨j', rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have h' : i' + j' = N := by omega
  exact (bijective_iff_of_comp _ _ extPlus (extPlus_bijective O F i') (extPlusHom F D j')
    (extPlus_bijective F D j') (fun x y => pairing_coyoneda_extPlus O D N t τ hτ F h' x y)).1
    (hF i' j' h')

end Stacks.HomologicalDuality

end
