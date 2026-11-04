/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePowerTrace

/-!
# Restricting the classes of `C^2` along a constant section

For a point `c : C^0 ⟶ C` let `s_c = ι_0 : C^1 ⟶ C^2`, `x ↦ (c, x)`, be the section of the
second projection through `c`. This file computes the restrictions along `s_c` of the classes
`Δ` and `F₀ = {c₀} × C` of `C^2`:

* `Stacks.CurvePower.schemePullbackClass_insertPoint_diagClass`: `s_c^* Δ = [c]`;
* `Stacks.CurvePower.schemePullbackClass_insertPoint_fibreClass`: `s_c^* F₀ = 0`.

The first one uses the symmetry of the diagonal (`Stacks.CurvePower.comap_reindex_swap_diag`):
after swapping the two factors, `s_c` becomes the base change `𝟙 × c` of the point `c` of `C^1`,
along which the graph of the coordinate pulls back to the graph of `c`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.CurvePower

/-- **The ideal of a closed immersion is invariant under an automorphism fixing it**: if
`i ≫ e = i` for an isomorphism `e`, then `e^{-1}(ker i) = ker i`. -/
theorem ker_comap_of_comp_eq {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (e : Y ⟶ Y)
    [IsIso e] (h : i ≫ e = i) : i.ker.comap e = i.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i e]
  have w : i ≫ e = 𝟙 Z ≫ i := by rw [h, Category.id_comp]
  have hl : pullback.lift i (𝟙 Z) w ≫ pullback.snd e i = 𝟙 Z := pullback.lift_snd _ _ _
  have : IsIso (pullback.lift i (𝟙 Z) w ≫ pullback.snd e i) := by rw [hl]; infer_instance
  have : IsIso (pullback.lift i (𝟙 Z) w) := IsIso.of_isIso_comp_right _ (pullback.snd e i)
  rw [← Scheme.Hom.ker_comp_of_isIso (pullback.lift i (𝟙 Z) w) (pullback.fst e i),
    pullback.lift_fst]

variable {k : Type u} [Field k] [IsAlgClosed k] (C : Over (Spec (.of k))) [IsVariety k C.hom]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]

/-- The swap of the two factors of `C^2`. -/
abbrev swapTwo : power C 2 ⟶ power C 2 :=
  reindex C (Equiv.swap (0 : Fin 2) 1)

/-- The swap of the two factors of `C^2` is an isomorphism of schemes. -/
instance isIso_swapTwo_left : IsIso (swapTwo C).left :=
  isIso_reindex_perm_left C 2 (Equiv.swap (0 : Fin 2) 1)

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- The diagonal map `C^1 ⟶ C^2`, `x ↦ (x, x)`, is invariant under the swap of the factors. -/
theorem doubleFirst_comp_swapTwo : doubleFirst C 0 ≫ swapTwo C = doubleFirst C 0 := by
  refine hom_ext 2 fun i => ?_
  rw [Category.assoc, reindex_coord, doubleFirst, lift_coord, lift_coord]
  fin_cases i
  · rw [show (Equiv.swap (0 : Fin 2) 1) ((⟨0, by lia⟩ : Fin 2)) = (0 : Fin 1).succ from
      Equiv.swap_apply_left _ _, Fin.cons_succ]
    rfl
  · rw [show (Equiv.swap (0 : Fin 2) 1) ((⟨1, by lia⟩ : Fin 2)) = 0 from
      Equiv.swap_apply_right _ _, Fin.cons_zero]
    rfl

private theorem isClosedImmersion_pointGraph_one {k' : Type u} [Field k']
    (C' : Over (Spec (.of k'))) [IsVariety k' C'.hom] :
    IsClosedImmersion (Stacks.Hilbert.pointGraph C' (power C' 1) (coord C' 1 0)) :=
  Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C' (power C' 1) _

omit [IsAlgClosed k] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- **The diagonal of `C^2` is symmetric.** -/
theorem comap_reindex_swap_diag :
    (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0)).comap (swapTwo C).left =
      Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0) := by
  have := isClosedImmersion_pointGraph_one C
  refine ker_comap_of_comp_eq _ _ ?_
  have h1 : Stacks.Hilbert.pointGraph C (power C 1) (coord C 1 0) = (doubleFirst C 0).left := by
    rw [pointGraph_eq_lift]
  rw [h1, ← Over.comp_left, doubleFirst_comp_swapTwo]

variable (c : power C 0 ⟶ C)

/-- The point `c` of `C^1`. -/
abbrev pointOne : power C 0 ⟶ power C 1 :=
  lift 1 fun _ => c

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- **After the swap, the section through `c` is the base change of the point `c` of `C^1`.** -/
theorem insertPoint_comp_swapTwo :
    insertPoint C c 1 0 ≫ swapTwo C =
      CartesianMonoidalCategory.lift (fst C (power C 0)) (snd C (power C 0) ≫ pointOne C c) := by
  have h0 : insertPoint C c 1 0 ≫ swapTwo C ≫ coord C 2 0 = coord C 1 0 := by
    rw [reindex_coord, Equiv.swap_apply_left]
    exact insertPoint_coord_succAbove C c 1 0 0
  have h1 : insertPoint C c 1 0 ≫ swapTwo C ≫ coord C 2 1 = toPowerZero C 1 ≫ c := by
    rw [reindex_coord, Equiv.swap_apply_right]
    exact insertPoint_coord_self C c 1 0
  have hsnd : snd C (power C 0) = toPowerZero C 1 := toUnit_unique _ _
  refine hom_ext 2 fun i => ?_
  fin_cases i
  · show (insertPoint C c 1 0 ≫ swapTwo C) ≫ coord C 2 0 = _ ≫ coord C 2 0
    rw [Category.assoc, h0]
    show coord C 1 0 = CartesianMonoidalCategory.lift (fst C (power C 0))
      (snd C (power C 0) ≫ pointOne C c) ≫ fst C (power C 1)
    exact (lift_fst _ _).symm
  · show (insertPoint C c 1 0 ≫ swapTwo C) ≫ coord C 2 ((0 : Fin 1).succ) =
      _ ≫ coord C 2 ((0 : Fin 1).succ)
    rw [Category.assoc, show coord C 2 ((0 : Fin 1).succ) = coord C 2 1 from rfl, h1]
    show _ = CartesianMonoidalCategory.lift (fst C (power C 0))
      (snd C (power C 0) ≫ pointOne C c) ≫ snd C (power C 1) ≫ coord C 1 0
    refine Eq.trans ?_ (lift_snd_assoc (fst C (power C 0)) (snd C (power C 0) ≫ pointOne C c)
      (coord C 1 0)).symm
    rw [Category.assoc, lift_coord, hsnd]
    rfl

omit [IsAlgClosed k] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- The ideal of the diagonal of `C^2` pulls back along the section through `c` to the ideal of
the point `c` of `C^1`. -/
theorem comap_insertPoint_diag :
    (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0)).comap (insertPoint C c 1 0).left =
      Stacks.Hilbert.pointIdeal C (power C 0) c := by
  have := isClosedImmersion_pointGraph_one C
  have e := Scheme.IdealSheafData.comap_comp (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0))
    (insertPoint C c 1 0).left (swapTwo C).left
  rw [comap_reindex_swap_diag C] at e
  refine e.symm.trans ?_
  have e2 : (insertPoint C c 1 0).left ≫ (swapTwo C).left =
      Stacks.Hilbert.familyBaseChangeMap C (pointOne C c) := by
    rw [← Over.comp_left, insertPoint_comp_swapTwo, familyBaseChangeMap_eq]
  refine (congrArg (Scheme.IdealSheafData.comap
    (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0))) e2).trans ?_
  exact (Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap C (pointOne C c) (coord C 1 0)).trans
    (by rw [lift_coord])

omit [IsAlgClosed k] [IsProper C.hom] in
/-- **The diagonal restricts to the point `c` along the section through `c`**: `s_c^* Δ = [c]`. -/
theorem schemePullbackClass_insertPoint_diagClass :
    Stacks.Picard.schemePullbackClass (insertPoint C c 1 0).left (diagClass C) =
      pointClass C c := by
  have hD := comap_insertPoint_diag C c
  have : Stacks.Divisors.IsPullbackDefined (insertPoint C c 1 0).left
      (Stacks.Hilbert.pointIdeal C (power C 1) (coord C 1 0)) :=
    (congrArg Stacks.Divisors.IsEffectiveCartierDivisor hD).mpr
      (isEffectiveCartierDivisor_graph C 0 _)
  refine (@Stacks.Divisors.schemePullbackClass_picardClass _ _ _ _
    (isEffectiveCartierDivisor_graph C 1 _) this).trans ?_
  exact @picardClass_congr _ _ _ this (isEffectiveCartierDivisor_graph C 0 _) hD

omit [IsAlgClosed k] [IsProper C.hom] in
/-- **The fibre `{c₀} × C` restricts to zero along the section through `c`.** -/
theorem schemePullbackClass_insertPoint_fibreClass (c₀ : power C 0 ⟶ C) :
    Stacks.Picard.schemePullbackClass (insertPoint C c 1 0).left (fibreClass C c₀ 1) = 0 := by
  rw [← schemePullbackClass_firstProj_pointClass, Stacks.Picard.schemePullbackClass_comp,
    ← Over.comp_left]
  refine schemePullbackClass_eq_zero_of_factor C _ (pointOne C c) ?_ _
  refine hom_ext 1 fun i => ?_
  fin_cases i
  simp only [Category.assoc, reindex_coord, Fin.zero_eta, Fin.isValue, lift_coord]
  rw [insertPoint_coord_self]

end Stacks.CurvePower

end
