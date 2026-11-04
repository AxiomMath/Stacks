module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import StacksFrontier.CategoryTheory.Limits.SystemColimitLift

/-!
# Colimits of systems preserve monomorphisms

Let `(A, T_A)` and `(B, T_B)` be systems over a directed set satisfying the cocycle condition, in
the sense of `CategoryTheory.Limits.IsSystemColimit`, and let `f_i : A_i ⟶ B_i` be monomorphisms
compatible with the transition maps. If filtered colimits are exact in the ambient category, the
map induced between colimits of the two systems is a monomorphism. The systems are functors on
the filtered category `CategoryTheory.Limits.SystemLift I`, the family `f` is a natural
transformation between them, and the colimit functor of that filtered shape preserves
monomorphisms.

## Main definitions

* `CategoryTheory.Limits.IsSystemColimit.liftNatTrans` — a compatible family of maps of systems,
  as a natural transformation of the attached functors on `CategoryTheory.Limits.SystemLift I`.

## Main results

* `CategoryTheory.Limits.IsSystemColimit.mono_of_isSystemColimit` — colimits of systems preserve
  monomorphisms when the colimit functor of shape `CategoryTheory.Limits.SystemLift I` does.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits.IsSystemColimit

universe w v u

variable {I : Type w} [Preorder I] {𝒞 : Type u} [Category.{v} 𝒞]
  {A B : Iᵒᵖ → 𝒞} {TA : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i)}
  {TB : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (B j ⟶ B i)}
  (hTA : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), TA (a ≫ b) = TA b ≫ TA a)
  (hTB : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), TB (a ≫ b) = TB b ≫ TB a)
  (f : ∀ i, A i ⟶ B i) (hf : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), TA a ≫ f i = f j ≫ TB a)

/-- A family of maps of systems compatible with the transition maps, as a natural
transformation of the attached functors on `CategoryTheory.Limits.SystemLift I`. -/
def liftNatTrans : SystemLift.functor A TA hTA ⟶ SystemLift.functor B TB hTB where
  app x := f (Opposite.op x.idx)
  naturality x y g := by
    change SystemLift.map A TA (leOfHom g) ≫ f _ = f _ ≫ SystemLift.map B TB (leOfHom g)
    by_cases hlt : x.lvl < y.lvl
    · rw [SystemLift.map_of_lt A TA _ hlt, SystemLift.map_of_lt B TB _ hlt]
      exact hf _
    · obtain rfl := SystemLift.eq_of_le_of_not_lt (leOfHom g) hlt
      rw [SystemLift.map_self, SystemLift.map_self, Category.id_comp, Category.comp_id]

/-- The component of `liftNatTrans` at `x` is the map `f` at the index of `x`. -/
@[simp]
theorem liftNatTrans_app (x : SystemLift I) :
    (liftNatTrans hTA hTB f hf).app x = f (Opposite.op x.idx) :=
  rfl

include hTA hTB hf in
/-- **Monomorphisms of systems induce monomorphisms of colimits**, when the colimit functor of
shape `CategoryTheory.Limits.SystemLift I` preserves monomorphisms, for instance when filtered
colimits are exact. -/
theorem mono_of_isSystemColimit [IsDirected I (· ≤ ·)] [Nonempty I]
    [HasColimitsOfShape (SystemLift I) 𝒞]
    [(colim : (SystemLift I ⥤ 𝒞) ⥤ 𝒞).PreservesMonomorphisms]
    [∀ i, Mono (f i)] {𝒜 ℬ : 𝒞} {α : ∀ i, A i ⟶ 𝒜} {β : ∀ i, B i ⟶ ℬ}
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), TA a ≫ α i = α j)
    (hβ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), TB a ≫ β i = β j)
    (hA : IsSystemColimit A TA 𝒜 α) (hB : IsSystemColimit B TB ℬ β) (U : 𝒜 ⟶ ℬ)
    (hU : ∀ i, α i ≫ U = f i ≫ β i) : Mono U := by
  obtain ⟨cA⟩ := (SystemLift.isSystemColimit_iff hTA α hα).mp hA
  obtain ⟨cB⟩ := (SystemLift.isSystemColimit_iff hTB β hβ).mp hB
  have : ∀ x, Mono ((liftNatTrans hTA hTB f hf).app x) := fun x => inferInstanceAs (Mono (f _))
  have : Mono (liftNatTrans hTA hTB f hf) := NatTrans.mono_of_mono_app _
  exact colim.map_mono' (liftNatTrans hTA hTB f hf) cA cB U (fun x => hU _)

end CategoryTheory.Limits.IsSystemColimit
