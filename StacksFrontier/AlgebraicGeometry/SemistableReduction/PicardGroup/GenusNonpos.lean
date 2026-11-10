module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contraction
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Minimal
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Contraction
public import Mathlib.GroupTheory.Archimedean

/-!
# The Picard group of a numerical type of nonpositive genus

A numerical type of genus at most zero has Picard group `ℤ`. The proof
contracts minus-one indices down to a single component, using that each
contraction is injective with 2-torsion cokernel.

## Main definitions

* `AlgebraicGeometry.NumericalType.relabelType`: the numerical type with its components
  relabelled along an equivalence, and `AlgebraicGeometry.NumericalType.relabelPicardEquiv`,
  the identification of Picard groups it induces.

## Main results

* `AlgebraicGeometry.NumericalType.picardGroup_addEquiv_int_of_genus_nonpos`.

## References

* [Stacks Project, Tag 0C7K](https://stacks.math.columbia.edu/tag/0C7K)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The numerical type obtained from `T` by relabelling its components along `e`: every datum of
the component `i` is the datum of the component `e.symm i` of `T`. -/
public abbrev relabelType (T : NumericalType) (e : Fin T.componentCount ≃ Fin T.componentCount) :
    NumericalType where
  componentCount := T.componentCount
  componentCount_pos := T.componentCount_pos
  multiplicity i := T.multiplicity (e.symm i)
  intersection i j := T.intersection (e.symm i) (e.symm j)
  weight i := T.weight (e.symm i)
  componentGenus i := T.componentGenus (e.symm i)
  multiplicity_pos i := T.multiplicity_pos (e.symm i)
  weight_pos i := T.weight_pos (e.symm i)
  componentGenus_nonneg i := T.componentGenus_nonneg (e.symm i)
  intersection_symm i j := T.intersection_symm _ _
  intersection_nonneg i j hij := T.intersection_nonneg _ _
    (fun heq => hij (e.symm.injective heq))
  connected := by
    intro h
    rcases h with ⟨I, hI, hne, hzero⟩
    apply T.connected
    refine ⟨e.symm '' I, ?_, ?_, ?_⟩
    · exact hI.image _
    · intro hfull
      apply hne
      apply Set.eq_univ_iff_forall.mpr
      intro j
      have hj : e.symm j ∈ e.symm '' I := hfull ▸ Set.mem_univ _
      obtain ⟨i, hi, heq⟩ := hj
      exact e.symm.injective heq ▸ hi
    · intro i hi j hj
      change ∃ i', i' ∈ I ∧ e.symm i' = i at hi
      rcases hi with ⟨i', hi', rfl⟩
      have hj' : e j ∉ I := fun hm => hj ⟨e j, hm, e.symm_apply_apply j⟩
      have hh := hzero i' hi' (e j) hj'
      change T.intersection (e.symm i') (e.symm (e j)) = 0 at hh
      simpa using hh
  intersection_mul_multiplicity i := by
    calc
      _ = ∑ j, T.intersection (e.symm i) j * T.multiplicity j :=
        Equiv.sum_comp e.symm _
      _ = 0 := T.intersection_mul_multiplicity (e.symm i)
  weight_dvd_intersection i j := T.weight_dvd_intersection (e.symm i) (e.symm j)

private theorem relabelType_equivalent (T : NumericalType)
    (e : Fin T.componentCount ≃ Fin T.componentCount) :
  Equivalent T (relabelType T e) := by
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i
    change T.multiplicity i = T.multiplicity (e.symm (e i))
    exact (congrArg T.multiplicity (e.symm_apply_apply i)).symm
  · intro i j
    change T.intersection i j = T.intersection (e.symm (e i)) (e.symm (e j))
    rw [e.symm_apply_apply, e.symm_apply_apply]
  · intro i
    change T.weight i = T.weight (e.symm (e i))
    exact (congrArg T.weight (e.symm_apply_apply i)).symm
  · intro i
    change T.componentGenus i = T.componentGenus (e.symm (e i))
    exact (congrArg T.componentGenus (e.symm_apply_apply i)).symm

/-- Relabelling the components of a numerical type leaves its genus unchanged. -/
public theorem genus_relabelType (T : NumericalType)
    (e : Fin T.componentCount ≃ Fin T.componentCount) :
    genus (relabelType T e) = genus T := by
  unfold genus
  change 1 + (∑ i, T.multiplicity (e.symm i) *
      (T.weight (e.symm i) * (T.componentGenus (e.symm i) - 1))) -
      (∑ i, T.multiplicity (e.symm i) * T.intersection (e.symm i) (e.symm i)) / 2 = _
  rw [Equiv.sum_comp e.symm (fun i => T.multiplicity i *
      (T.weight i * (T.componentGenus i - 1))),
    Equiv.sum_comp e.symm (fun i => T.multiplicity i * T.intersection i i)]

/-- Relabelling the components of a numerical type along `e`, read on the coordinates of the
free group on the components. -/
public def relabelCoordinates (T : NumericalType)
    (e : Fin T.componentCount ≃ Fin T.componentCount) :
    (Fin T.componentCount → ℤ) ≃ₗ[ℤ] (Fin T.componentCount → ℤ) where
  toFun x i := x (e i)
  invFun x i := x (e.symm i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

/-- Relabelling the components of a numerical type along `e` carries the relations defining the
Picard group to the relations defining the Picard group of the relabelled type, hence identifies
the two Picard groups. -/
public noncomputable def relabelPicardEquiv (T : NumericalType)
    (e : Fin T.componentCount ≃ Fin T.componentCount) :
    picardGroup (relabelType T e) ≃+ picardGroup T := by
  let r := relabelCoordinates T e
  have hcomm : r.toLinearMap.comp (picardRelationMap (relabelType T e)) =
      (picardRelationMap T).comp r.toLinearMap := by
    apply LinearMap.ext
    intro x
    funext j
    simp only [relabelType, relabelCoordinates, picardRelationMap,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, picardRelationMatrix,
      Equiv.symm_apply_apply, r]
    change (∑ i, T.intersection (e.symm i) j / T.weight j * x i) =
      ∑ i, T.intersection i j / T.weight j * x (e i)
    convert Equiv.sum_comp e.symm (fun i => T.intersection i j / T.weight j * x (e i)) using 1
    all_goals simp [mul_comm]
  have hrange : (LinearMap.range (picardRelationMap (relabelType T e))).map
      r.toLinearMap = LinearMap.range (picardRelationMap T) := by
    rw [← LinearMap.range_comp (picardRelationMap (relabelType T e)) r.toLinearMap, hcomm,
      LinearEquiv.range_comp r (picardRelationMap T)]
  exact (Submodule.Quotient.equiv
    (LinearMap.range (picardRelationMap (relabelType T e)))
    (LinearMap.range (picardRelationMap T)) r hrange).toAddEquiv

private theorem addSubgroupInt_equiv_int (K : AddSubgroup ℤ) (hK : K ≠ ⊥) :
    Nonempty (K ≃+ ℤ) := by
  obtain ⟨a, ha⟩ := AddSubgroup.isAddCyclic K
  have ha0 : (a : ℤ) ≠ 0 := by
    intro h0
    refine hK ((AddSubgroup.eq_bot_iff_forall K).2 fun x hx => ?_)
    obtain ⟨z, hz⟩ := ha ⟨x, hx⟩
    have := congrArg Subtype.val hz
    simp only [AddSubgroup.coe_zsmul, h0, smul_zero] at this
    exact this.symm
  let f : ℤ →+ K := zmultiplesHom K a
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, ha⟩
    have := congrArg Subtype.val hxy
    simp only [f, zmultiplesHom_apply, AddSubgroup.coe_zsmul, smul_eq_mul] at this
    exact mul_right_cancel₀ ha0 this
  exact ⟨(AddEquiv.ofBijective f hf).symm⟩

private theorem addGroup_equiv_int_of_injective_two_range
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hf : Function.Injective f)
    (htwo : ∀ y : H, 2 • y ∈ f.range) (e : H ≃+ ℤ) :
    Nonempty (G ≃+ ℤ) := by
  let g : G →+ ℤ := e.toAddMonoidHom.comp f
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (htwo (e.symm 1))
  have hgx : g x = 2 := by simp [g, hx]
  have hrange : g.range ≠ ⊥ := fun hbot => by
    have h0 : g x ∈ (⊥ : AddSubgroup ℤ) := hbot ▸ (⟨x, rfl⟩ : g x ∈ g.range)
    simp [hgx] at h0
  obtain ⟨φ⟩ := addSubgroupInt_equiv_int g.range hrange
  exact ⟨(AddMonoidHom.ofInjective (e.injective.comp hf)).trans φ⟩

private theorem picardGroup_equiv_int_of_componentCount_eq_one
    (T : NumericalType) (hn : T.componentCount = 1) :
    Nonempty (picardGroup T ≃+ ℤ) := by
  let : Unique (Fin T.componentCount) := {
    default := ⟨0, T.componentCount_pos⟩
    uniq i := Fin.ext (by have hi := i.isLt; omega)
  }
  have hzero (i j : Fin T.componentCount) : T.intersection i j = 0 := by
    obtain rfl : i = j := Subsingleton.elim _ _
    obtain rfl : i = default := Subsingleton.elim _ _
    have hs := T.intersection_mul_multiplicity default
    rw [Fintype.sum_unique] at hs
    exact (mul_eq_zero.mp hs).resolve_right (T.multiplicity_pos _).ne'
  have hrel : picardRelationMap T = 0 := by
    ext x j
    simp [picardRelationMap, picardRelationMatrix,
      Matrix.toLin'_apply, Matrix.mulVec, hzero]
  have hrange : LinearMap.range (picardRelationMap T) = ⊥ := by
    rw [hrel, LinearMap.range_zero]
  exact ⟨(Submodule.quotEquivOfEqBot _ hrange).trans
    (LinearEquiv.piUnique ℤ fun _ : Fin T.componentCount => ℤ)⟩

private theorem picardGroup_equiv_int_of_genus_nonpos_aux (n : ℕ) :
    ∀ (T : NumericalType), T.componentCount = n → genus T ≤ 0 →
      Nonempty (picardGroup T ≃+ ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T hcount hgen
    by_cases hn : n = 1
    · exact picardGroup_equiv_int_of_componentCount_eq_one T (hcount.trans hn)
    · have hnlarge : 1 < n := by have := T.componentCount_pos; omega
      have hnotmin : ¬IsMinimal T := fun hmin => by
        have := one_le_genus_of_isMinimal T hmin (by omega)
        omega
      obtain ⟨i, hi⟩ : ∃ i, IsMinusOneIndex T i := by simpa [IsMinimal] using hnotmin
      let e : Fin T.componentCount ≃ Fin T.componentCount :=
        Equiv.swap i (lastIndex T)
      have elast : e.symm (lastIndex T) = i := by
        simp [e, lastIndex]
      have hlast : IsMinusOneIndex (relabelType T e)
          (lastIndex (relabelType T e)) := by
        change T.componentGenus (e.symm (lastIndex T)) = 0 ∧
          T.intersection (e.symm (lastIndex T))
            (e.symm (lastIndex T)) =
              -T.weight (e.symm (lastIndex T))
        rw [elast]
        exact hi
      let c := contractLast (relabelType T e) hlast
      have hcount' : c.val.componentCount = n - 1 :=
        c.property.componentCount_eq.trans (by simp [hcount])
      have hgen' : genus c.val ≤ 0 := by rwa [c.property.genus_eq, genus_relabelType]
      obtain ⟨E⟩ := ih (n - 1) (by omega) c.val hcount' hgen'
      obtain ⟨F⟩ := addGroup_equiv_int_of_injective_two_range
        (contractPicardMap (relabelType T e) hlast)
        (contractPicardMap_injective (relabelType T e) hlast)
        (two_smul_mem_contractPicardMap_range (relabelType T e) hlast) E
      exact ⟨(relabelPicardEquiv T e).symm.trans F⟩

/-- A numerical type of nonpositive genus has infinite cyclic Picard group. -/
@[stacks 0C7K]
public theorem picardGroup_addEquiv_int_of_genus_nonpos (T : NumericalType)
    (hT : genus T ≤ 0) : Nonempty (picardGroup T ≃+ ℤ) :=
  picardGroup_equiv_int_of_genus_nonpos_aux T.componentCount T rfl hT

end AlgebraicGeometry.NumericalType
