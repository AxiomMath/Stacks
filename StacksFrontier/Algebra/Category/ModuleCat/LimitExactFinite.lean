module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Inverse limits of exact sequences of towers with finite first term

Let `F → G → H` be maps of towers of `R`-modules (functors `ℕᵒᵖ ⥤ ModuleCat R`) which are exact
at every index, and assume every `F n` is finite.  Then `lim F → lim G → lim H` is exact.  This
is the step by which an exact sequence of torsion cohomology groups `Hⁱ_c(-, Fₙ)` — finite by the
finiteness theorem — passes to the ℓ-adic limit `Hⁱ_c(-, F) = limₙ Hⁱ_c(-, Fₙ)`, as in the
excision and Leray sequences of the reduction of Weil II to curves.

An element `y` of `lim G` killed by `lim H` has components `yₙ ∈ ker(Gₙ → Hₙ) = im(Fₙ → Gₙ)`; the
fibres of `Fₙ → Gₙ` over the `yₙ` form a tower of nonempty finite sets, which has a compatible
family by compactness (`nonempty_sections_of_finite_cofiltered_system`), and that family is a
preimage of `y` in `lim F`.

## Main results

* `ModuleCat.exact_limMap_of_finite`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R] {F G H : ℕᵒᵖ ⥤ ModuleCat.{v} R}

/-- The tower of fibres of `α : F ⟶ G` over the components of an element of `lim G`. -/
private def limMapFibreTower (α : F ⟶ G) (y : ToType (limit G)) : ℕᵒᵖ ⥤ Type v where
  obj n := {a : F.obj n // α.app n a = limit.π G n y}
  map {m n} φ := ↾(fun a => (⟨F.map φ a.1, by
    rw [NatTrans.naturality_apply α φ a.1, a.2]
    simp⟩ : {a : F.obj n // α.app n a = limit.π G n y}))
  map_id n := by ext a; simp
  map_comp φ ψ := by ext a; simp

private theorem limMapFibreTower_coe_map (α : F ⟶ G) (y : ToType (limit G)) {m n : ℕᵒᵖ}
    (φ : m ⟶ n) (a : (limMapFibreTower α y).obj m) :
    ((limMapFibreTower α y).map φ a).1 = F.map φ a.1 :=
  rfl

/-- **Inverse limits of exact sequences of towers with finite first term are exact.** -/
public theorem exact_limMap_of_finite (α : F ⟶ G) (β : G ⟶ H)
    (hex : ∀ n, Function.Exact (α.app n) (β.app n)) (hfin : ∀ n, Finite (F.obj n)) :
    Function.Exact (limMap α) (limMap β) := by
  intro y
  constructor
  · intro hy
    have : ∀ n, Finite ((limMapFibreTower α y).obj n) := fun _ => Subtype.finite
    have : ∀ n, Nonempty ((limMapFibreTower α y).obj n) := fun n =>
      let ⟨a, ha⟩ := (hex n _).1 (by simpa using congrArg (limit.π H n) hy)
      ⟨⟨a, ha⟩⟩
    obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (limMapFibreTower α y)
    let t : (F ⋙ forget (ModuleCat.{v} R)).sections :=
      ⟨fun n => (s n).1, fun {m n} φ =>
        (limMapFibreTower_coe_map α y φ (s m)).symm.trans (congrArg Subtype.val (hs φ))⟩
    let x : ToType (limit F) :=
      (Types.isLimitEquivSections (isLimitOfPreserves (forget (ModuleCat.{v} R))
        (limit.isLimit F))).symm t
    have hx : ∀ n, limit.π F n x = (s n).1 := fun n => by
      simpa using Types.isLimitEquivSections_symm_apply
        (isLimitOfPreserves (forget (ModuleCat.{v} R)) (limit.isLimit F)) t n
    refine ⟨x, Concrete.limit_ext G _ _ fun n => ?_⟩
    simpa [hx n] using (s n).2
  · rintro ⟨x, rfl⟩
    refine Concrete.limit_ext H _ _ fun n => ?_
    simp [(hex n).apply_apply_eq_zero]

end ModuleCat

end
