module

public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Compatible families into an inverse system with zero derived limit

Let `D` be a pre-triangulated category and let `F : ℕᵒᵖ ⥤ D` be an inverse system with a derived
limit `K`. A compatible family of maps `pₙ : X ⟶ Fₙ`, that is one with `pₙ₊₁ ≫ fₙ₊₁ = pₙ`, is a
map into `∏ Fₙ` killed by the difference map, so it factors through `K ⟶ ∏ Fₙ`. In particular,
if `K = 0` then every compatible family vanishes.

Applied to the family `F₀ ⟶ Fₙ` of inverses of the transition maps of a tower whose transition
maps into `F₀` are isomorphisms, this says that such a tower with zero derived limit is zero. This
is the form in which the last step of the proof of Proposition 0GZK uses that a tower which is
constant with value `Mₜ` and has derived limit `0` forces `Mₜ = 0`.

## Main results

* `CategoryTheory.Pretriangulated.IsDerivedLimit.eq_zero_of_isZero`: a compatible family of maps
  into an inverse system with zero derived limit vanishes.
* `CategoryTheory.Pretriangulated.IsDerivedLimit.isZero_obj_zero_of_isZero`: an inverse system
  with zero derived limit whose transition maps into the zeroth term are isomorphisms has zero
  zeroth term.

## References

* [Stacks, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A compatible family of maps into an inverse system with zero derived limit vanishes.**
The family is a map into `∏ Fₙ` killed by the difference map, so it factors through the derived
limit, which is zero. -/
theorem IsDerivedLimit.eq_zero_of_isZero {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    {K : D} (hK : IsDerivedLimit F K) (hz : IsZero K) {X : D} (p : ∀ n : ℕ, X ⟶ F.obj ⟨n⟩)
    (hp : ∀ n : ℕ, p (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = p n) (n : ℕ) :
    p n = 0 := by
  obtain ⟨q, δ, hT⟩ := hK
  have h0 : Pi.lift p ≫ (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) = 0 := by
    refine Pi.hom_ext _ _ fun m => ?_
    simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub, Pi.lift_π_assoc, hp, sub_self,
      zero_comp]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ hT (Pi.lift p) h0
  have hzero : Pi.lift p = 0 := by
    rw [hg, hz.eq_of_tgt g 0, zero_comp]
  simpa only [Pi.lift_π, zero_comp] using hzero =≫ Pi.π (fun n : ℕ => F.obj ⟨n⟩) n

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- The transition map into the zeroth term of an inverse system indexed by `ℕ` factors through
the previous one. -/
theorem map_homOfLE_zero_succ (F : ℕᵒᵖ ⥤ D) (k : ℕ) :
    F.map (homOfLE (Nat.zero_le (k + 1))).op =
      F.map (homOfLE (Nat.le_succ k)).op ≫ F.map (homOfLE (Nat.zero_le k)).op := by
  rw [← F.map_comp]
  rfl

/-- **An inverse system with zero derived limit whose transition maps into the zeroth term are
isomorphisms has zero zeroth term.** The inverses of those transition maps form a compatible
family out of the zeroth term whose zeroth member is the identity. -/
theorem IsDerivedLimit.isZero_obj_zero_of_isZero {F : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] {K : D} (hK : IsDerivedLimit F K) (hz : IsZero K)
    (hF : ∀ k : ℕ, IsIso (F.map (homOfLE (Nat.zero_le k)).op)) : IsZero (F.obj ⟨0⟩) := by
  let p : ∀ k : ℕ, F.obj ⟨0⟩ ⟶ F.obj ⟨k⟩ := fun k => inv (F.map (homOfLE (Nat.zero_le k)).op)
  have hp : ∀ k : ℕ, p (k + 1) ≫ F.map (homOfLE (Nat.le_succ k)).op = p k := by
    intro k
    simp only [p]
    rw [IsIso.inv_comp_eq, map_homOfLE_zero_succ F k, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hid : p 0 = 𝟙 _ := by simp [p]
  rw [IsZero.iff_id_eq_zero, ← hid]
  exact hK.eq_zero_of_isZero hz p hp 0

end CategoryTheory.Pretriangulated
