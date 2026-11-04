module

public import Mathlib.CategoryTheory.CofilteredSystem

@[expose] public section

/-!
# Pro-isomorphism of inverse sequences

The transition maps `InverseSequence.tr` of an inverse system indexed by `ℕᵒᵖ` and the explicit
"up to refinement" pro-isomorphism structure `InverseSequence.ProIso`, used by the Artin--Rees
comparisons for the homology of an adic complex.
-/

/-! ### Support for tag 0H3D, replayed alongside the tag 0EGU material of this file

Pro-isomorphism of inverse sequences is stated below in the explicit up-to-refinement form of
tag 0H3D.  The conceptual library has no provider for that tag, so the two definitions it
supplies — the transition map of an inverse system and the pro-isomorphism structure itself —
are restated here as untagged support.  Tag 0H3D is not claimed here. -/

section

open CategoryTheory Opposite

namespace InverseSequence

/-- The transition map of an inverse system `X : ℕᵒᵖ ⥤ D` from level `m` down to level `n`
(`n ≤ m`). -/
noncomputable def tr {D : Type*} [Category D] (X : ℕᵒᵖ ⥤ D) {n m : ℕ} (h : n ≤ m) :
    X.obj (op m) ⟶ X.obj (op n) :=
  X.map (homOfLE h).op

/-- Two inverse systems indexed by `ℕᵒᵖ` are pro-isomorphic in the explicit "up to refinement"
form: order-preserving reindexings `α, β` with `m ≤ α m`, `m ≤ β m`, together with families of
morphisms `φ : X_{α m} → Y_m` and `ψ : Y_{β m} → X_m` that are compatible with the transition
maps (`φnat`, `ψnat`) and are mutually inverse up to refinement of the index (`ψφ`, `φψ`).
This is the standard notion of isomorphism in the category of pro-objects. -/
structure ProIso {D : Type*} [Category D] (X Y : ℕᵒᵖ ⥤ D) where
  /-- The reindexing carrying a level of `Y` to a level of `X`. -/
  α : ℕ → ℕ
  /-- The reindexing carrying a level of `X` to a level of `Y`. -/
  β : ℕ → ℕ
  /-- `α` is order preserving. -/
  αmono : Monotone α
  /-- `β` is order preserving. -/
  βmono : Monotone β
  /-- `α` refines the index. -/
  αle : ∀ m, m ≤ α m
  /-- `β` refines the index. -/
  βle : ∀ m, m ≤ β m
  /-- The forward morphisms, defined after refining along `α`. -/
  φ : ∀ m, X.obj (op (α m)) ⟶ Y.obj (op m)
  /-- The backward morphisms, defined after refining along `β`. -/
  ψ : ∀ m, Y.obj (op (β m)) ⟶ X.obj (op m)
  /-- The forward morphisms are compatible with the transition maps. -/
  φnat : ∀ {m m' : ℕ} (h : m ≤ m'), tr X (αmono h) ≫ φ m = φ m' ≫ tr Y h
  /-- The backward morphisms are compatible with the transition maps. -/
  ψnat : ∀ {m m' : ℕ} (h : m ≤ m'), tr Y (βmono h) ≫ ψ m = ψ m' ≫ tr X h
  /-- Backward after forward is a transition map of `X`. -/
  ψφ : ∀ m, φ (β m) ≫ ψ m = tr X (le_trans (βle m) (αle (β m)))
  /-- Forward after backward is a transition map of `Y`. -/
  φψ : ∀ m, ψ (α m) ≫ φ m = tr Y (le_trans (αle m) (βle (α m)))

/-- The transition map of an inverse system along a reflexive inequality is the identity. -/
theorem ProIso.tr_refl {D : Type*} [Category D] (X : ℕᵒᵖ ⥤ D) {n : ℕ} (h : n ≤ n) :
    tr X h = 𝟙 _ := by
  have e : (homOfLE h : n ⟶ n) = 𝟙 n := Subsingleton.elim _ _
  rw [tr, e, op_id, X.map_id]

/-- Transition maps of an inverse system compose: dropping from level `m` to level `n` and then
to level `k` is dropping from level `m` to level `k`. -/
theorem ProIso.tr_trans {D : Type*} [Category D] (X : ℕᵒᵖ ⥤ D) {k n m : ℕ} (h : k ≤ n)
    (h' : n ≤ m) : tr X h' ≫ tr X h = tr X (h.trans h') := by
  rw [tr, tr, tr, ← Functor.map_comp, ← op_comp, homOfLE_comp]

end InverseSequence

end

end
