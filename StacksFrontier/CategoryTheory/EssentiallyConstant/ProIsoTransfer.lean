module

public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Essential constancy along pro-isomorphisms of inverse sequences

An inverse sequence `X : ℕᵒᵖ ⥤ C` which is an essentially constant pro-object (Stacks 05PU(2),
`CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro`) stays so under every
pro-isomorphism `InverseSequence.ProIso X Y`: being essentially constant is a property of the
pro-object, and a pro-isomorphism in the explicit up-to-refinement form is an isomorphism of
pro-objects. The witness is transported directly: the cone on `X` with apex `P` becomes a cone
on `Y` by composing its projections with the forward maps, the splitting `s : X_i ⟶ P` becomes
`ψ_i ≫ s` on `Y_{β i}`, and cofinality is checked with the two zigzag identities of the
pro-isomorphism.

The file also records the pro-isomorphism between an inverse sequence and its shift
`n ↦ X_{n+1}`, in both directions.

## Main results

* `CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro.of_proIso` — essential
  constancy of an inverse sequence is invariant under pro-isomorphism.
* `InverseSequence.ProIso.shiftSucc` and `InverseSequence.ProIso.shiftSuccInv` — an inverse
  sequence is pro-isomorphic to its shift by one, in either direction.

## Implementation notes

The companion transfers asked for alongside these are already in the library:
`CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith.map` (postcomposition with a
functor), `CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro.of_iso` and
`CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro.comp` (natural isomorphisms
and functors), and `InverseSequence.ProIso.whiskerRight` (pro-isomorphisms under a functor).

## References

* [Stacks Project, Tag 05PU](https://stacks.math.columbia.edu/tag/05PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.EssentiallyConstantPro

open InverseSequence

variable {C : Type*} [Category C]

/-- **Essential constancy is invariant under pro-isomorphism.** If `X` is an essentially constant
pro-object and `X` is pro-isomorphic to `Y`, then `Y` is an essentially constant pro-object, with
the same value. -/
theorem IsEssentiallyConstantPro.of_proIso {X Y : ℕᵒᵖ ⥤ C} (e : ProIso X Y)
    (h : IsEssentiallyConstantPro X) : IsEssentiallyConstantPro Y := by
  obtain ⟨c, i, s, hs⟩ := h
  have hmap : ∀ {a b : ℕ} (hab : a ≤ b) (g : op b ⟶ op a), X.map g = tr X hab :=
    fun hab g => congrArg X.map (Subsingleton.elim _ _)
  have hmapY : ∀ {a b : ℕ} (hab : a ≤ b) (g : op b ⟶ op a), Y.map g = tr Y hab :=
    fun hab g => congrArg Y.map (Subsingleton.elim _ _)
  have hπ : ∀ {a b : ℕ} (hab : a ≤ b), c.π.app (op b) ≫ tr X hab = c.π.app (op a) := by
    intro a b hab
    exact c.w (homOfLE hab).op
  let c' : Cone Y :=
    { pt := c.pt
      π :=
        { app := fun m => c.π.app (op (e.α m.unop)) ≫ e.φ m.unop
          naturality := by
            rintro ⟨m⟩ ⟨m'⟩ g
            have hle : m' ≤ m := leOfHom g.unop
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.assoc]
            rw [hmapY hle g, ← e.φnat hle, ← Category.assoc, hπ] } }
  refine ⟨c', op (e.β i.unop), e.ψ i.unop ≫ s, ?_, ?_⟩
  · obtain ⟨i⟩ := i
    change (c.π.app (op (e.α (e.β i))) ≫ e.φ (e.β i)) ≫ e.ψ i ≫ s = 𝟙 c.pt
    rw [Category.assoc, ← Category.assoc (e.φ _), e.ψφ, ← Category.assoc, hπ]
    exact hs.retraction
  · rintro ⟨j⟩
    obtain ⟨⟨k₀⟩, σ, τ, hk⟩ := hs.cofinal (op (e.α j))
    obtain ⟨i⟩ := i
    have hik : i ≤ k₀ := leOfHom σ.unop
    have hjk : e.α j ≤ k₀ := leOfHom τ.unop
    have hβ : e.β i ≤ e.β k₀ := e.βmono hik
    have hjβ : j ≤ e.β k₀ := le_trans (e.αle j) (le_trans hjk (e.βle k₀))
    refine ⟨op (e.β k₀), (homOfLE hβ).op, (homOfLE hjβ).op, ?_⟩
    rw [hmap hik σ, hmap hjk τ] at hk
    change tr Y hjβ = tr Y hβ ≫ (e.ψ i ≫ s) ≫ c.π.app (op (e.α j)) ≫ e.φ j
    simp only [Category.assoc]
    rw [← Category.assoc (tr Y hβ) (e.ψ i), e.ψnat hik]
    simp only [Category.assoc]
    rw [← Category.assoc s, ← Category.assoc (tr X hik), ← hk, ← Category.assoc,
      ← e.ψnat hjk, Category.assoc, e.φψ, ProIso.tr_trans]

end CategoryTheory.EssentiallyConstantPro

namespace InverseSequence.ProIso

variable {D : Type*} [Category D]

/-- The shift `n ↦ n + 1` of the indices, as a functor of `ℕ`. -/
abbrev succFunctor : ℕ ⥤ ℕ := Monotone.functor (f := Nat.succ) fun _ _ h => Nat.succ_le_succ h

/-- **An inverse sequence is pro-isomorphic to its shift by one** `n ↦ X_{n+1}`: the forward
maps are identities and the backward maps are the transition maps `X_{m+1} ⟶ X_m`. -/
def shiftSucc (X : ℕᵒᵖ ⥤ D) : ProIso X (succFunctor.op ⋙ X) where
  α m := m + 1
  β m := m
  αmono _ _ h := Nat.succ_le_succ h
  βmono _ _ h := h
  αle m := Nat.le_succ m
  βle m := le_rfl
  φ m := 𝟙 _
  ψ m := tr X (Nat.le_succ m)
  φnat h := (Category.comp_id _).trans (Category.id_comp _).symm
  ψnat h := by
    change tr X (Nat.succ_le_succ h) ≫ tr X (Nat.le_succ _) = tr X (Nat.le_succ _) ≫ tr X h
    rw [tr_trans, tr_trans]
  ψφ m := by
    change 𝟙 _ ≫ tr X (Nat.le_succ m) = tr X _
    rw [Category.id_comp]
  φψ m := by
    change tr X (Nat.le_succ (m + 1)) ≫ 𝟙 _ = tr X (Nat.succ_le_succ (Nat.le_succ m))
    rw [Category.comp_id]

/-- **The shift by one of an inverse sequence is pro-isomorphic to it**, in the direction
opposite to `InverseSequence.ProIso.shiftSucc`: the forward maps are the transition maps and the
backward maps are identities. -/
def shiftSuccInv (X : ℕᵒᵖ ⥤ D) : ProIso (succFunctor.op ⋙ X) X where
  α m := m
  β m := m + 1
  αmono _ _ h := h
  βmono _ _ h := Nat.succ_le_succ h
  αle m := le_rfl
  βle m := Nat.le_succ m
  φ m := tr X (Nat.le_succ m)
  ψ m := 𝟙 _
  φnat h := by
    change tr X (Nat.succ_le_succ h) ≫ tr X (Nat.le_succ _) = tr X (Nat.le_succ _) ≫ tr X h
    rw [tr_trans, tr_trans]
  ψnat h := (Category.comp_id _).trans (Category.id_comp _).symm
  ψφ m := by
    change tr X (Nat.le_succ (m + 1)) ≫ 𝟙 _ = tr X (Nat.succ_le_succ (Nat.le_succ m))
    rw [Category.comp_id]
  φψ m := by
    change 𝟙 _ ≫ tr X (Nat.le_succ m) = tr X _
    rw [Category.id_comp]

end InverseSequence.ProIso

end
