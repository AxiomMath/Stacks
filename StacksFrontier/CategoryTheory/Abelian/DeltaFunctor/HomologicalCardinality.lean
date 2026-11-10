module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalConstructions
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # Vanishing of `Hₙ₊₁(g)` by counting, for a homological δ-functor with values in modules

Let `H` be a homological δ-functor with values in `R`-modules and `0 → X₁ → X₂ → X₃ → 0` a short
exact sequence. The long exact sequence `Hₙ₊₁(X₂) → Hₙ₊₁(X₃) → Hₙ(X₁) → Hₙ(X₂)` shows that the
connecting map identifies `Hₙ₊₁(X₃)/im Hₙ₊₁(g)` with the kernel of `Hₙ(f)`. Hence, if `Hₙ₊₁(X₃)`
is finite with at most as many elements as that kernel, then `Hₙ₊₁(g) = 0`.

## Main results

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.map_g_eq_zero_of_natCard_le`: `Hₙ₊₁(g) = 0`
  when `Hₙ₊₁(X₃)` is finite with at most as many elements as the kernel of `Hₙ(f)`.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.natCard_ker_map_f_eq_of_map_g_eq_zero`: the
  kernel of `Hₙ(f)` has as many elements as `Hₙ₊₁(X₃)` when `Hₙ₊₁(g) = 0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w w'

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

variable {A : Type u} [Category.{v} A] [Preadditive A] {R : Type w} [Ring R]
  (H : HomologicalDeltaFunctor A (ModuleCat.{w'} R))

/-- The connecting map followed by `Hₙ(f)` is zero, elementwise. -/
private theorem map_f_δ_apply {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) (y) :
    ((H.functor n).map S.f).hom ((H.δ hS n).hom y) = 0 := by
  rw [← ModuleCat.comp_apply, H.δ_map_f hS n]
  rfl

/-- **`Hₙ₊₁(g) = 0` by counting.** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if
`Hₙ₊₁(X₃)` is finite with at most as many elements as the kernel of `Hₙ(f)`, then
`Hₙ₊₁(g) = 0`. -/
theorem map_g_eq_zero_of_natCard_le {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    [Finite ((H.functor (n + 1)).obj S.X₃)]
    (hcard : Nat.card ((H.functor (n + 1)).obj S.X₃) ≤
      Nat.card (LinearMap.ker ((H.functor n).map S.f).hom)) :
    (H.functor (n + 1)).map S.g = 0 := by
  set δ := (H.δ hS n).hom
  have h₂ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (H.exact_δ₂ hS n)
  have hrange : LinearMap.range δ = LinearMap.ker ((H.functor n).map S.f).hom := by
    refine le_antisymm ?_ h₂
    rintro _ ⟨y, rfl⟩
    exact map_f_δ_apply H hS n y
  have hsplit : Nat.card ((H.functor (n + 1)).obj S.X₃) =
      Nat.card δ.toAddMonoidHom.ker * Nat.card δ.toAddMonoidHom.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup δ.toAddMonoidHom.ker, mul_comm,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ.toAddMonoidHom).toEquiv]
  have hr : Nat.card δ.toAddMonoidHom.range =
      Nat.card (LinearMap.ker ((H.functor n).map S.f).hom) := by
    rw [← hrange]
    rfl
  have : Finite δ.toAddMonoidHom.range :=
    Finite.of_surjective (fun y ↦ (⟨δ y, y, rfl⟩ : δ.toAddMonoidHom.range))
      (fun ⟨_, y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩)
  have hpos : 0 < Nat.card δ.toAddMonoidHom.range := Nat.card_pos
  have hker : Nat.card δ.toAddMonoidHom.ker ≤ 1 := by
    rw [hsplit, hr] at hcard
    rw [hr] at hpos
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul_right (Nat.card (LinearMap.ker ((H.functor n).map S.f).hom)) hlt
    lia
  have : Finite δ.toAddMonoidHom.ker := Subtype.finite
  ext x
  have hx : ((H.functor (n + 1)).map S.g).hom x ∈ δ.toAddMonoidHom.ker := by
    change (H.δ hS n).hom (((H.functor (n + 1)).map S.g).hom x) = 0
    rw [← ModuleCat.comp_apply, H.map_g_δ hS n]
    rfl
  exact congrArg Subtype.val ((Finite.card_le_one_iff_subsingleton.1 hker).elim ⟨_, hx⟩ 0)

/-- **`#ker Hₙ(f) = #Hₙ₊₁(X₃)` when `Hₙ₊₁(g) = 0`**: the connecting map is then an isomorphism of
`Hₙ₊₁(X₃)` onto the kernel of `Hₙ(f)`. -/
theorem natCard_ker_map_f_eq_of_map_g_eq_zero {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (hg : (H.functor (n + 1)).map S.g = 0) :
    Nat.card (LinearMap.ker ((H.functor n).map S.f).hom) =
      Nat.card ((H.functor (n + 1)).obj S.X₃) := by
  have h₁ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (H.exact_δ₁ hS n)
  have h₂ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (H.exact_δ₂ hS n)
  have hmap := map_f_δ_apply H hS n
  have hinj : Function.Injective (H.δ hS n).hom := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := h₁ hy
    change ((H.functor (n + 1)).map S.g).hom x ∈ ⊥
    rw [hg]
    exact Submodule.zero_mem _
  refine (Nat.card_congr (Equiv.ofBijective (fun y ↦ (⟨(H.δ hS n).hom y, hmap y⟩ :
    LinearMap.ker ((H.functor n).map S.f).hom)) ⟨fun a b h ↦ hinj (congrArg Subtype.val h),
      fun ⟨z, hz⟩ ↦ ?_⟩)).symm
  obtain ⟨y, hy⟩ := h₂ hz
  exact ⟨y, Subtype.ext hy⟩

end Stacks.CategoryHomology.HomologicalDeltaFunctor
