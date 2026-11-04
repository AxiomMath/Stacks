module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PushedPairingFiveLemma

/-!
# Pushing pairings into a shifted target

Let `P` be push data for pairings (`CategoryTheory.Functor.PairingPushData`): functors `R₁`, `R₂`
and a natural cup product `μ : R₁K ⊗ R₂L ⟶ R(K ⊗ L)`. The pairing of [Stacks, Tag 0G8K] is
`Rf_*Ω^• ⊗^L Rf_*(Ω^•[2n]) ⟶ Rf_*(Ω^• ⊗^L Ω^•[2n]) ⟶ Rf_*(Ω^•[2n]) ⟶ 𝒪_S`: the second variable and
the target are shifted, inside `Rf_*`, by `2n`. This file packages that shift as new push data
`PairingPushData.shiftTarget P m`, with `R₂` and `R` precomposed with the shift by `m` and the
cup product followed by the commutation of `⊗` with the shift in its second variable, so that the
five lemma for pushed pairings applies to the unshifted pairings upstairs.

## Main definitions

* `CategoryTheory.Functor.PairingPushData.shiftTarget`

## Main results

* `CategoryTheory.Functor.PairingPushData.pushedPairing_shiftTarget`

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor.PairingPushData

variable {C₁ C₂ C D : Type*} [Category* C₁] [Category* C₂] [Category* C] [Category* D]
  [HasZeroObject C₁] [HasZeroObject C₂] [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂]
  {T : C₁ ⥤ C₂ ⥤ C} {T' : D ⥤ D ⥤ D} {R : C ⥤ D}
  [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive]

/-- **Push data into a shifted target**: `R₂` and `R` are precomposed with the shift by `m`, and
the cup product becomes `R₁K ⊗ R₂(L[m]) ⟶ R(K ⊗ L[m]) ⟶ R((K ⊗ L)[m])`, the second map being `R` of
the commutation of `⊗` with the shift in its second variable. Pushing a pairing `β` along it is
pushing `K ⊗ L[m] ⟶ (K ⊗ L)[m] ⟶ M[m]` along the given data
(`PairingPushData.pushedPairing_shiftTarget`). -/
@[simps R₁ R₂ μ]
noncomputable def shiftTarget (P : PairingPushData T T' R) (m : ℤ) :
    PairingPushData T T' (shiftFunctor C m ⋙ R) where
  R₁ := P.R₁
  R₂ := shiftFunctor C₂ m ⋙ P.R₂
  μ K L := P.μ K (L⟦m⟧) ≫ R.map (((T.obj K).commShiftIso m).hom.app L)
  μ_natural_left e L := by
    have h₁ := NatTrans.shift_app_comm (T.map e) m L
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ ⊢
    rw [P.μ_natural_left_assoc, ← R.map_comp, ← h₁, R.map_comp, Category.assoc]
  μ_natural_right K _ _ e := by
    have h₁ := ((T.obj K).commShiftIso m).hom.naturality e
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ ⊢
    rw [P.μ_natural_right_assoc, ← R.map_comp, h₁, R.map_comp, Category.assoc]
  exact₁₂ := P.exact₁₂
  exact₁₃ := P.exact₁₃
  exact₂₂ S hS Z N g hg := by
    have hS' : (Triangle.shiftFunctor C₂ m).obj S ∈ distTriang C₂ :=
      Triangle.shift_distinguished S hS m
    obtain ⟨k, hk⟩ : ∃ k : (T'.obj Z).obj (P.R₂.obj (S.obj₃⟦m⟧)) ⟶ N,
        g = (T'.obj Z).map (P.R₂.map (m.negOnePow • S.mor₂⟦m⟧')) ≫ k := P.exact₂₂ _ hS' Z g (by
      change (T'.obj Z).map (P.R₂.map (m.negOnePow • S.mor₁⟦m⟧')) ≫ g = 0
      change (T'.obj Z).map (P.R₂.map (S.mor₁⟦m⟧')) ≫ g = 0 at hg
      rw [map_units_smul, map_units_smul, Linear.units_smul_comp, hg, smul_zero])
    refine ⟨m.negOnePow • k, ?_⟩
    rw [hk, map_units_smul, map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
    rfl
  exact₂₃ S hS Z N g hg := by
    have hS' : (Triangle.shiftFunctor C₂ m).obj S ∈ distTriang C₂ :=
      Triangle.shift_distinguished S hS m
    obtain ⟨k, hk⟩ : ∃ k : (T'.obj Z).obj (P.R₂.obj ((S.obj₁⟦m⟧)⟦(1 : ℤ)⟧)) ⟶ N,
        g = (T'.obj Z).map (P.R₂.map (m.negOnePow • (S.mor₃⟦m⟧' ≫
          (shiftFunctorComm C₂ 1 m).hom.app S.obj₁))) ≫ k := P.exact₂₃ _ hS' Z g (by
      change (T'.obj Z).map (P.R₂.map (m.negOnePow • S.mor₂⟦m⟧')) ≫ g = 0
      change (T'.obj Z).map (P.R₂.map (S.mor₂⟦m⟧')) ≫ g = 0 at hg
      rw [map_units_smul, map_units_smul, Linear.units_smul_comp, hg, smul_zero])
    refine ⟨m.negOnePow • ((T'.obj Z).map
      (P.R₂.map ((shiftFunctorComm C₂ 1 m).hom.app S.obj₁)) ≫ k), ?_⟩
    rw [hk, map_units_smul, map_units_smul, Functor.map_comp, Functor.map_comp,
      Linear.units_smul_comp, Category.assoc, Linear.comp_units_smul]
    rfl

/-- Pushing a pairing into the shifted target is pushing its composite with the commutation of `⊗`
with the shift, followed by the shift of the pairing, along the given data. -/
theorem pushedPairing_shiftTarget (P : PairingPushData T T' R) (m : ℤ) {K : C₁} {L : C₂} {M : C}
    {N : D} (τ : R.obj (M⟦m⟧) ⟶ N) (β : (T.obj K).obj L ⟶ M) :
    (P.shiftTarget m).pushedPairing τ β =
      P.pushedPairing τ (((T.obj K).commShiftIso m).hom.app L ≫ β⟦m⟧') := by
  simp only [pushedPairing, shiftTarget_μ, Functor.comp_map, Functor.map_comp]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)

end CategoryTheory.Functor.PairingPushData
