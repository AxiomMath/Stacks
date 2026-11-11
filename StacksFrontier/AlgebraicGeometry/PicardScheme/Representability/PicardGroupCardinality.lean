module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSmallEncoding
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# The Picard group of a scheme of bounded size has bounded cardinality

Let `Y` be a scheme and let `κ` be a strong limit cardinal with `size(Y) < κ`. Then the Picard
group `Pic(Y)` of [Stacks, Tag 01CX] has fewer than `κ` elements.

## Main results

* `Stacks.Picard.injective_code_picardRepresentative`: the code of
  `Stacks.PresheafOfModules.code` separates the classes of `Pic(Y)`.
* `Stacks.Picard.mk_code_structureSheaf_lt`: the type of codes of the structure sheaf of `Y` has
  fewer than `κ` elements.
* `Stacks.Picard.mk_ofScheme_lt`: `#Pic(Y) < κ`.

## References

* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal Opposite AlgebraicGeometry

universe u

namespace Stacks.Picard

open Stacks.RingedSpace (structureIsSheaf)

/-- **Codes separate Picard classes.** Two classes of `Pic(Y)` whose chosen representatives have
the same code are equal. -/
theorem injective_code_picardRepresentative (Y : Scheme.{u}) :
    Function.Injective (fun x : ofScheme Y =>
      Stacks.PresheafOfModules.code (picardRepresentative Y.toRingedSpace x).obj.val) := by
  intro x y h
  have := (picardRepresentative Y.toRingedSpace x).property
  have := (picardRepresentative Y.toRingedSpace y).property
  rw [← classOf_picardRepresentative Y.toRingedSpace x,
    ← classOf_picardRepresentative Y.toRingedSpace y]
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
    ⟨Stacks.SheafOfModules.isoOfCodeEq (structureIsSheaf Y.toRingedSpace)
      (picardRepresentative Y.toRingedSpace x).obj (picardRepresentative Y.toRingedSpace y).obj h⟩

/-- **The codes of the structure sheaf of `Y` number fewer than `κ`**, for `κ > ℵ₀` a strong limit
cardinal above `size(Y)`. -/
theorem mk_code_structureSheaf_lt (Y : Scheme.{u}) {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : κ.IsStrongPrelimit) (hY : Y.size < κ) :
    #(Stacks.PresheafOfModules.Code
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
        (structureIsSheaf Y.toRingedSpace)).obj) < κ := by
  set R := (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
    (structureIsSheaf Y.toRingedSpace)).obj with hR
  have hO : #(Y.Opens)ᵒᵖ < κ := by
    rw [← mk_congr (Opposite.equivToOpposite (α := Y.Opens))]
    have hinj : Function.Injective (fun U : Y.Opens => (U : Set Y)) := SetLike.coe_injective
    refine (mk_le_of_injective hinj).trans_lt ?_
    rw [mk_set]
    exact hsl (Y.mk_le_two_pow_size.trans_lt (hsl hY))
  set c₀ : Cardinal.{u} := (2 ^ Y.size) ^ ℵ₀ with hc₀
  have hc₀κ : c₀ < κ := power_aleph0_lt_of_isStrongPrelimit hκ hsl (hsl hY)
  have hseq : ∀ W : (Y.Opens)ᵒᵖ, #(ℕ → R.obj W) ≤ c₀ := by
    intro W
    rw [mk_arrow, lift_uzero, mk_nat, lift_aleph0]
    exact power_le_power_right (Y.mk_sections_le_two_pow_size W.unop)
  set c₁ : Cardinal.{u} := ⨆ U : (Y.Opens)ᵒᵖ,
    #(Set (∀ p : Σ W : (Y.Opens)ᵒᵖ, (U ⟶ W), ℕ → R.obj p.1)) with hc₁
  have hsig : ∀ U : (Y.Opens)ᵒᵖ, #(Σ W : (Y.Opens)ᵒᵖ, (U ⟶ W)) ≤ #(Y.Opens)ᵒᵖ := by
    intro U
    have hinj : Function.Injective (fun p : Σ W : (Y.Opens)ᵒᵖ, (U ⟶ W) => p.1) := by
      rintro ⟨W, a⟩ ⟨W', b⟩ (h : W = W')
      subst h
      exact congrArg _ (Subsingleton.elim a b)
    exact mk_le_of_injective hinj
  have hfam : ∀ U : (Y.Opens)ᵒᵖ,
      #(∀ p : Σ W : (Y.Opens)ᵒᵖ, (U ⟶ W), ℕ → R.obj p.1) ≤ c₀ ^ #(Y.Opens)ᵒᵖ := by
    intro U
    rw [mk_pi]
    refine (prod_le_prod _ (fun _ => c₀)
      (fun p : Σ W : (Y.Opens)ᵒᵖ, (U ⟶ W) => hseq p.1)).trans ?_
    rw [prod_const, lift_id, lift_id]
    exact power_le_power_left (power_ne_zero _ (power_ne_zero _ two_ne_zero)) (hsig U)
  have hc₁κ : c₁ ≤ 2 ^ (c₀ ^ #(Y.Opens)ᵒᵖ) := by
    refine ciSup_le' fun U => ?_
    rw [mk_set]
    exact power_le_power_left two_ne_zero (hfam U)
  have hc₁lt : c₁ < κ :=
    hc₁κ.trans_lt (hsl (power_lt_of_isStrongPrelimit hκ hsl hc₀κ hO))
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => c₁) (fun U => le_ciSup bddAbove_of_small U)).trans_lt ?_
  rw [prod_const, lift_id, lift_id]
  exact power_lt_of_isStrongPrelimit hκ hsl hc₁lt hO

/-- **The Picard group of a scheme of size below a strong limit cardinal `κ > ℵ₀` has fewer than
`κ` elements.** -/
theorem mk_ofScheme_lt (Y : Scheme.{u}) {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : κ.IsStrongPrelimit) (hY : Y.size < κ) :
    #(ofScheme Y) < lift.{u + 1} κ := by
  have h := lift_mk_le_lift_mk_of_injective (injective_code_picardRepresentative Y)
  rw [lift_id'.{u, u + 1}] at h
  exact h.trans_lt (lift_strictMono (mk_code_structureSheaf_lt Y hκ hsl hY))

end Stacks.Picard

end
