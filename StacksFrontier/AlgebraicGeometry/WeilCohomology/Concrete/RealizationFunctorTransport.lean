module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataIsoOfGraded
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of correspondences is invariant under isomorphisms of Weil data

Let `e : W ≅ W'` be an isomorphism of data (D0)–(D3) satisfying (A), (B), (C) which preserves the
cycle class maps and the trace maps (`Stacks.WeilCohomology.WeilData.IsIsomorphic`). The proof of
Stacks 0FHL lets a correspondence `c ∈ Corr⁰(X, Y)` act on cohomology by
`a ↦ pr₂,*(γ(c) ∪ pr₁^*a)` (`Stacks.WeilCohomology.WeilData.corrMap`). This file proves that the
isomorphisms `H^n(X) ≅ H'^n(X)` of `e` intertwine these actions
(`Stacks.WeilCohomology.WeilData.Iso.gradeEquiv_corrMap`): in coordinates of the Tate lines, `e`
scales cycle classes of codimension `i` by `κ^i` and traces in dimension `d` by `κ^d`
(`Stacks.WeilCohomology.WeilData.Iso.gradeEquiv_cycleClassCoord`,
`Stacks.WeilCohomology.WeilData.Iso.traceCoord_gradeEquiv`), and the two scalings cancel in
`pr₂,*(γ(c) ∪ pr₁^*a)`.

## Main results

* `Stacks.WeilCohomology.WeilData.Iso.traceProj_equiv`: `∫' ∘ e = κ^d ∫`.
* `Stacks.WeilCohomology.WeilData.Iso.gradeEquiv_blockAct`: `e ∘ pr₂,*(z ∪ pr₁^* -)` is
  `κ^{-d} pr₂,*(e(z) ∪ pr₁^* e(-))`.
* `Stacks.WeilCohomology.WeilData.Iso.equiv_corrClass`: `e(γ(c)) = κ^i γ'(c)`.
* `Stacks.WeilCohomology.WeilData.Iso.equiv_extendByZero`: `e` commutes with extension by zero.
* `Stacks.WeilCohomology.WeilData.Iso.gradeEquiv_corrMap`: `e` intertwines the actions of
  correspondences.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] {W W' : WeilData k F}

/-- On classes of degree `2d` of `X` of dimension `d`, the trace projection is the trace
coordinate. -/
theorem traceProj_eq_traceCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (x : W.grade X (2 * (d : ℤ))) :
    W.traceProj X d hX x = W.traceCoord X d hX x := by
  rw [W.traceProj_of_mem X d hX x.2, trace_eq_traceCoord, LinearEquiv.apply_symm_apply]

namespace Iso

variable (e : Iso W W')

/-- The scalar `κ`, the inverse of the ratio of the coordinates of the Tate lines. -/
abbrev κ : Fˣ := e.coordRatio⁻¹

/-- `e` maps classes of degree `n` to classes of degree `n`. -/
theorem equiv_mem_grade {X : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ} {x : W.H X}
    (hx : x ∈ W.grade X n) : e.equiv X x ∈ W'.grade X n :=
  e.gradeEquiv X n ⟨x, hx⟩ |>.2

/-- **`∫'_X ∘ e = κ^d ∫_X`** on the whole cohomology ring. -/
theorem traceProj_equiv (htr : e.PreservesTrace) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) (hX : IsNonemptyEquidimensional X d) (x : W.H X) :
    W'.traceProj X d hX (e.equiv X x) = ((e.κ ^ (d : ℤ) : Fˣ) : F) * W.traceProj X d hX x := by
  induction x using DirectSum.Decomposition.inductionOn (W.grade X) with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  | @homogeneous n x =>
    by_cases hn : n = 2 * (d : ℤ)
    · subst hn
      rw [traceProj_eq_traceCoord, ← coe_gradeEquiv,
        traceProj_eq_traceCoord X d hX (e.gradeEquiv X _ x), e.traceCoord_gradeEquiv htr]
    · rw [W.traceProj_of_mem_ne X d hX x.2 hn, W'.traceProj_of_mem_ne X d hX
        (e.equiv_mem_grade x.2) hn, mul_zero]

variable [CharZero F] {hA : W.PoincareDuality} {hB : W.Kunneth}
  {hC : W.CycleClassAxiom hA.perfectPairing} {hA' : W'.PoincareDuality} {hB' : W'.Kunneth}
  {hC' : W'.CycleClassAxiom hA'.perfectPairing}

omit [CharZero F] in
/-- **`e` and the action of a class**: `e(pr₂,*(z ∪ pr₁^*a)) = κ^{-d} pr₂,*(e(z) ∪ pr₁^* e(a))`
for `X` of dimension `d`. -/
theorem gradeEquiv_blockAct (htr : e.PreservesTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d d' : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y d')
    (z : W.H (prod X Y)) (i : ℤ) (a : W.grade X i) :
    e.gradeEquiv Y i (W.blockAct hA.perfectPairing hX hY z i a) =
      ((e.κ ^ (-(d : ℤ)) : Fˣ) : F) •
        W'.blockAct hA'.perfectPairing hX hY (e.equiv _ z) i (e.gradeEquiv X i a) := by
  refine eq_of_traceProj_mul_eq hA'.perfectPairing hY fun b' ↦ ?_
  obtain ⟨b, rfl⟩ := (e.gradeEquiv Y _).surjective b'
  have hL : W'.traceProj Y d' hY ((e.gradeEquiv Y i (W.blockAct hA.perfectPairing hX hY z i a) :
      W'.H Y) * (e.gradeEquiv Y _ b : W'.H Y)) = ((e.κ ^ (d' : ℤ) : Fˣ) : F) *
      W.traceProj (prod X Y) (d + d') (isNonemptyEquidimensional_prod hX hY)
        (z * W.pull (fst X Y) a * W.pull (snd X Y) b) := by
    rw [coe_gradeEquiv, coe_gradeEquiv, ← map_mul, traceProj_equiv e htr, blockAct_spec]
  have hR : W'.traceProj Y d' hY (((((e.κ ^ (-(d : ℤ)) : Fˣ) : F) •
      W'.blockAct hA'.perfectPairing hX hY (e.equiv _ z) i (e.gradeEquiv X i a) : W'.grade Y i) :
        W'.H Y) * (e.gradeEquiv Y _ b : W'.H Y)) = ((e.κ ^ (-(d : ℤ)) : Fˣ) : F) *
      (((e.κ ^ ((d + d' : ℕ) : ℤ) : Fˣ) : F) *
        W.traceProj (prod X Y) (d + d') (isNonemptyEquidimensional_prod hX hY)
          (z * W.pull (fst X Y) a * W.pull (snd X Y) b)) := by
    rw [SetLike.val_smul, smul_mul_assoc, map_smul, blockAct_spec, coe_gradeEquiv, coe_gradeEquiv,
      ← e.equiv_pull, ← e.equiv_pull, ← map_mul, ← map_mul, traceProj_equiv e htr, smul_eq_mul]
  rw [hL, hR, ← mul_assoc, ← Units.val_mul, ← zpow_add]
  congr 3
  push_cast
  ring

/-- **`e(γ(c)) = κ^i γ'(c)`** for the cycle class of a correspondence, read in codimension `i`. -/
theorem equiv_corrClass (hγ : e.PreservesCycleClass)
    (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (d r i : ℤ) (t : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom d r) :
    e.equiv (prod X Y) (W.corrClass X Y d r i t) =
      ((e.κ ^ i : Fˣ) : F) • W'.corrClass X Y d r i t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' h h' => rw [map_add, map_add, h, h', map_add, smul_add]
  | tmul q α =>
    rw [corrClass_tmul, corrClass_tmul, map_smul, smul_comm]
    congr 1
    show e.equiv _ ((W.cycleClassCoord (prod X Y) i _ : W.grade (prod X Y) (2 * i)) :
      W.H (prod X Y)) = _ • ((W'.cycleClassCoord (prod X Y) i _ : W'.grade (prod X Y) (2 * i)) :
        W'.H (prod X Y))
    rw [← coe_gradeEquiv, e.gradeEquiv_cycleClassCoord hγ, SetLike.val_smul]

/-- **`e` commutes with extension by zero.** -/
theorem equiv_extendByZero {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] (x : W.H V) :
    e.equiv X (extendByZero hA hB hC j x) = extendByZero hA' hB' hC' j (e.equiv V x) := by
  refine sub_eq_zero.1 (eq_zero_of_pull_eq_zero_of_pull_complι_eq_zero hA' hB' hC' j ?_ ?_)
  · rw [map_sub, ← e.equiv_pull, pull_extendByZero_self, pull_extendByZero_self, sub_self]
  · rw [map_sub, ← e.equiv_pull, (pull_extendByZero_and hA hB hC j x).2,
      (pull_extendByZero_and hA' hB' hC' j _).2, map_zero, sub_self]

/-- `e` commutes with extension by zero in each degree. -/
theorem gradeEquiv_extendDeg {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] (n : ℤ) (x : W.grade V n) :
    e.gradeEquiv X n (extendDeg hA hB hC j n x) = extendDeg hA' hB' hC' j n (e.gradeEquiv V n x) :=
  Subtype.ext (e.equiv_extendByZero (hA := hA) (hB := hB) (hC := hC) (hA' := hA') (hB' := hB')
    (hC' := hC') j x)

/-- **`e` intertwines the action of a block of a correspondence.** -/
theorem gradeEquiv_blockMap (hγ : e.PreservesCycleClass) (htr : e.PreservesTrace)
    (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d d' : ℕ) (r n : ℤ)
    (c : Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y d').obj.hom d' r)
    (a : W.grade X n) :
    e.gradeEquiv Y n (blockMap hA hB hC X Y d d' r n c a) =
      blockMap hA' hB' hC' X Y d d' r n c (e.gradeEquiv X n a) := by
  by_cases h : Nonempty (part X d).obj.left ∧ Nonempty (part Y d').obj.left
  · rw [blockMap_of_nonempty hA hB hC n h.1 h.2, blockMap_of_nonempty hA' hB' hC' n h.1 h.2]
    simp only [LinearMap.comp_apply]
    rw [gradeEquiv_extendDeg (hA' := hA') (hB' := hB') (hC' := hC'),
      e.gradeEquiv_blockAct (hA := hA) (hA' := hA') htr, ← gradeEquiv_pullDeg,
      e.equiv_corrClass hγ, blockAct_smul, LinearMap.smul_apply,
      map_smul, map_smul, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_smul]
  · rcases not_and_or.1 h with h | h
    · rw [blockMap_of_isEmpty_left hA hB hC n h, blockMap_of_isEmpty_left hA' hB' hC' n h]
      exact map_zero _
    · rw [blockMap_of_isEmpty_right hA hB hC n h, blockMap_of_isEmpty_right hA' hB' hC' n h]
      exact map_zero _

/-- **`e` intertwines the actions of correspondences** `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)`. -/
theorem gradeEquiv_corrMap (hγ : e.PreservesCycleClass) (htr : e.PreservesTrace)
    (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r n : ℤ) (c : Corr k X.obj.hom Y.obj.hom r)
    (a : W.grade X n) :
    e.gradeEquiv Y n (corrMap hA hB hC X Y r n c a) =
      corrMap hA' hB' hC' X Y r n c (e.gradeEquiv X n a) := by
  induction c using DirectSum.induction_on with
  | zero => simp
  | add c c' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | of d x =>
    rw [corrMap, corrMap, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | of d' c =>
      simp only [DirectSum.toAddMonoid_of, AddMonoidHom.coe_comp, Function.comp_apply]
      exact e.gradeEquiv_blockMap hγ htr X Y d d' r n (blockEquiv X Y d d' r c) a

end Iso

end Stacks.WeilCohomology.WeilData

end
