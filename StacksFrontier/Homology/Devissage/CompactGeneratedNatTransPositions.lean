module

public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans

/-! # The remaining two positions of the five lemma for a transformation of exact functors

`StacksDraft.CompactDevissage.isIso_app_obj₃` says that a transformation `τ : F ⟶ G` of exact
functors compatible with the translation is invertible at the third vertex of a distinguished
triangle as soon as it is invertible at the first two. The dévissage of [Stacks, Tag 0FQE] asks
for all three positions, and the other two are deduced here by rotating the triangle: the inverse
rotation moves the second vertex into third position, and the rotation moves the shift of the
first vertex there.

## Main results

* `StacksDraft.CompactDevissage.isIso_app_obj₂`
* `StacksDraft.CompactDevissage.isIso_app_obj₁`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe u₁ u₂ v₁ v₂

namespace StacksDraft.CompactDevissage

open StacksDraft.NatTransDevissage

section FiveLemma

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D] [Limits.HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  {D' : Type u₂} [Category.{v₂} D'] [Preadditive D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D' n).Additive] [Pretriangulated D']
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]

/-- Invertibility of `τ` at the second vertex of a distinguished triangle, from the first and the
third: the inverse rotation moves the second vertex into third position. -/
theorem isIso_app_obj₂ (T : Pretriangulated.Triangle D)
    (hT : T ∈ Pretriangulated.distinguishedTriangles) (h₁ : IsIso (τ.app T.obj₁))
    (h₃ : IsIso (τ.app T.obj₃)) : IsIso (τ.app T.obj₂) :=
  isIso_app_obj₃ τ T.invRotate
    (Pretriangulated.inv_rot_of_distTriang T hT)
    (isIso_app_shift τ h₃ (-1)) h₁

/-- Invertibility of `τ` at the first vertex of a distinguished triangle, from the second and the
third: the rotation moves the shift of the first vertex into third position. -/
theorem isIso_app_obj₁ (T : Pretriangulated.Triangle D)
    (hT : T ∈ Pretriangulated.distinguishedTriangles) (h₂ : IsIso (τ.app T.obj₂))
    (h₃ : IsIso (τ.app T.obj₃)) : IsIso (τ.app T.obj₁) := by
  have h : IsIso (τ.app ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) :=
    isIso_app_obj₃ τ T.rotate
      (Pretriangulated.rot_of_distTriang T hT) h₂ h₃
  exact isIso_app_of_iso τ
    ((shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)).app T.obj₁)
    (isIso_app_shift τ h (-1))

end FiveLemma

end StacksDraft.CompactDevissage

end
