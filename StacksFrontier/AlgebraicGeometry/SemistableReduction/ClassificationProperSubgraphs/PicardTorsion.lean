module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.CycleRank
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contraction
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.GenusBound
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Graph
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Contraction
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.GenusNonpos
public import StacksCore.Tactic.StacksAttribute

/-!
# Prime torsion in the Picard group of a numerical type

For a numerical type of genus at least two, the dimension of the `ℓ`-torsion of
its Picard group is bounded by the genus as soon as `ℓ` exceeds `768` times the
genus. For a minimal type the topological genus `1 - n + e` gives the sharper
bound, and that topological genus is itself at most the genus.

For a minimal type the bound is linear algebra: above `768 * g` the prime is
coprime to every multiplicity and to every intersection number, so the
`ℓ`-torsion of the cokernel of the intersection matrix is bounded by the cycle
rank of the incidence graph, which is the topological genus. The general case
reduces to the minimal one by contracting minus-one indices: contraction
preserves the genus, drops the number of components by one, and embeds the
Picard group, so an induction on the number of components applies.

## Main results

* `AlgebraicGeometry.NumericalType.finrank_picardGroup_torsionBy_le_genus`.
* `AlgebraicGeometry.NumericalType.finrank_picardGroup_torsionBy_le_topGenus_of_isMinimal`.
* `AlgebraicGeometry.NumericalType.topGenus_le_genus_of_isMinimal`.

## Implementation notes

The topological genus is written out as `1 - n + e`, where `e` is `edgeCount`,
the number of pairs of components with positive intersection number. The prime
torsion is `AddSubgroup.torsionBy` with its natural `ZMod ℓ`-module structure.
Contracting a minus-one index needs that index to be the last one, so the
numerical type is first relabelled by the transposition moving it there:
`AlgebraicGeometry.NumericalType.relabelType` and its effect on the genus and
on the Picard group, and `relabel_isMinimal_iff` for minimality.

## References

* [Stacks Project, Tag 0C9X](https://stacks.math.columbia.edu/tag/0C9X)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType


private theorem torsionBy_finite_type {H : Type*} [AddCommGroup H]
    [Module.Finite ℤ H] {n : ℕ} [Fact n.Prime] :
    Finite (AddSubgroup.torsionBy H (n : ℤ)) := by
  let P := AddSubgroup.torsionBy H (n : ℤ)
  have hP : P.FG := by
    simpa using Submodule.fg_toAddSubgroup
      (Submodule.FG.of_le_of_isNoetherian (le_top (a := AddSubgroup.toIntSubmodule P)))
  have ht : Module.IsTorsion ℤ P := by
    intro x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr ?_⟩, ?_⟩
    · exact_mod_cast (Fact.out : Nat.Prime n).ne_zero
    · change (n : ℤ) • x = 0
      norm_cast
      exact AddSubgroup.torsionBy.nsmul (n := n) x
  have : Module.Finite ℤ P :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg P).2 hP)
  exact Module.finite_of_fg_torsion P ht

private theorem torsionBy_finrank_mono_of_injective
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Module.Finite ℤ H]
    {n : ℕ} [Fact n.Prime] (f : G →+ H) (hf : Function.Injective f) :
    let : Module (ZMod n) (AddSubgroup.torsionBy G (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    let : Module (ZMod n) (AddSubgroup.torsionBy H (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod n) (AddSubgroup.torsionBy G (n : ℤ)) ≤
      Module.finrank (ZMod n) (AddSubgroup.torsionBy H (n : ℤ)) := by
  let : Module (ZMod n) (AddSubgroup.torsionBy G (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod n) (AddSubgroup.torsionBy H (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  have : Finite (AddSubgroup.torsionBy H (n : ℤ)) := torsionBy_finite_type
  have : Module.Finite (ZMod n) (AddSubgroup.torsionBy H (n : ℤ)) :=
    Module.Finite.of_finite
  let F : AddSubgroup.torsionBy G (n : ℤ) →+ AddSubgroup.torsionBy H (n : ℤ) :=
    (f.comp (AddSubgroup.subtype _)).codRestrict _ fun x =>
      AddSubgroup.torsionBy.nsmul_iff.mpr <| by
        rw [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, ← map_nsmul,
          AddSubgroup.torsionBy.nsmul_iff.mp x.2, map_zero]
  exact LinearMap.finrank_le_finrank_of_injective (f := AddMonoidHom.toZModLinearMap n F)
    fun x y hxy =>
      Subtype.ext (hf (congrArg (fun z : AddSubgroup.torsionBy H (n : ℤ) => (z : H)) hxy))

private theorem coprime_prime_int_of_pos_lt {p : ℕ} [Fact p.Prime]
    {z : ℤ} (hz : 0 < z) (hzp : z < (p : ℤ)) : IsCoprime (p : ℤ) z := by
  rw [Int.isCoprime_iff_nat_coprime]
  apply (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
  intro hdiv
  have hzabs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz.le
  have hlt : z.natAbs < p := by exact_mod_cast (hzabs ▸ hzp)
  have hle : p ≤ z.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt hz)) hdiv
  omega

private alias exists_positive_neighbor := AlgebraicGeometry.NumericalType.exists_neighbor

private theorem minimal_matrix_torsion_bound (T : NumericalType) (g : ℤ)
    (hg : 2 ≤ g) (hgenus : genus T = g) (hminimal : IsMinimal T)
    (hn : 1 < T.componentCount) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 768 * g < (ℓ : ℤ)) :
    let P := AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)
    let : Module (ZMod ℓ) P := AddSubgroup.torsionBy.zmodModule
    (Module.finrank (ZMod ℓ) P : ℤ) ≤
      (1 : ℤ) - T.componentCount + edgeCount T := by
  classical
  let A := intersectionMatrix T
  have hA : A.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [A, intersectionMatrix, T.intersection_symm]
  have hoff : ∀ i j, i ≠ j → 0 ≤ A i j := by
    intro i j hij
    simpa [A, intersectionMatrix] using
      T.intersection_nonneg j i hij.symm
  have hm : ∀ i, 0 < T.multiplicity i := T.multiplicity_pos
  have hAm : A.mulVec T.multiplicity = 0 := by
    ext i
    change ∑ j, A i j * T.multiplicity j = 0
    simpa [A, intersectionMatrix, T.intersection_symm] using
      T.intersection_mul_multiplicity i
  have hconnected : ∀ I : Set (Fin T.componentCount), I.Nonempty → I ≠ Set.univ →
      ¬ ∀ i ∈ I, ∀ j ∉ I, A i j = 0 := by
    intro I hI hIU hzero
    apply T.connected ⟨I, hI, hIU, ?_⟩
    intro i hi j hj
    simpa [A, intersectionMatrix, T.intersection_symm] using hzero i hi j hj
  have hℓA : ∀ i j, 0 < A i j → IsCoprime (ℓ : ℤ) (A i j) := by
    intro i j hij
    have hbound := multiplicity_mul_abs_intersection_le
      T g hg hgenus hminimal j i
    have hentry : 0 < T.intersection j i := by
      simpa [A, intersectionMatrix] using hij
    have hlt : T.intersection j i < (ℓ : ℤ) := by
      rw [abs_of_pos hentry] at hbound
      nlinarith [T.multiplicity_pos j, hbound, hℓ]
    simpa [A, intersectionMatrix] using
      coprime_prime_int_of_pos_lt hentry hlt
  have hℓm : ∀ i, IsCoprime (ℓ : ℤ) (T.multiplicity i) := by
    intro i
    obtain ⟨j, hij, hpos⟩ := exists_positive_neighbor T hn i
    have hbound := multiplicity_mul_abs_intersection_le
      T g hg hgenus hminimal i j
    have hlt : T.multiplicity i < (ℓ : ℤ) := by
      rw [abs_of_pos hpos] at hbound
      nlinarith [T.multiplicity_pos i, hbound, hℓ]
    exact coprime_prime_int_of_pos_lt (T.multiplicity_pos i) hlt
  have hmat := Matrix.finrank_torsionBy_matrixCokernel_le_cycleRank
    hA hoff hm hAm hconnected hℓA hℓm
  have hcount :
      ((Finset.univ.filter fun p : Fin T.componentCount × Fin T.componentCount =>
        p.1 < p.2 ∧ 0 < A p.1 p.2).card) = edgeCount T := by
    simp [A, edgeCount, T.intersection_symm]
  rw [hcount] at hmat
  have hrange : LinearMap.range (intersectionMap T) =
      LinearMap.range (intersectionMatrix T).mulVecLin := rfl
  let C := (Fin T.componentCount → ℤ) ⧸
    LinearMap.range (intersectionMatrix T).mulVecLin
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy C (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  obtain ⟨f, hf⟩ := picardGroup_embeds_intersectionCokernel T
  let e := Submodule.quotEquivOfEq
    (LinearMap.range (intersectionMap T))
    (LinearMap.range (intersectionMatrix T).mulVecLin) hrange
  let f' : picardGroup T →+ C := e.toAddEquiv.toAddMonoidHom.comp f
  have hmono := torsionBy_finrank_mono_of_injective (n := ℓ) f' (e.injective.comp hf)
  change (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) : ℤ) ≤ _
  have hnat : Module.finrank (ZMod ℓ)
      (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) ≤
      Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy C (ℓ : ℤ)) := by
    simpa using hmono
  have hnat' : Module.finrank (ZMod ℓ)
      (AddSubgroup.torsionBy C (ℓ : ℤ)) + T.componentCount ≤
      1 + edgeCount T := by
    simpa [C, A] using hmat
  omega

/-- A numerical type with at most one component has exactly one. -/
private theorem componentCount_eq_one_of_not_one_lt (T : NumericalType)
    (hn : ¬ 1 < T.componentCount) : T.componentCount = 1 := by
  have := T.componentCount_pos
  omega

/-- All intersection numbers of a one-component type vanish. -/
private theorem intersection_eq_zero_of_componentCount_eq_one (T : NumericalType)
    (hcount : T.componentCount = 1) (i j : Fin T.componentCount) : T.intersection i j = 0 := by
  have : Subsingleton (Fin T.componentCount) := by rw [hcount]; infer_instance
  rw [Subsingleton.elim i ⟨0, T.componentCount_pos⟩, Subsingleton.elim j ⟨0, T.componentCount_pos⟩]
  exact intersection_self_eq_zero_of_componentCount_eq_one T hcount

/-- A one-component type has no edges. -/
private theorem edgeCount_eq_zero_of_componentCount_eq_one (T : NumericalType)
    (hcount : T.componentCount = 1) : edgeCount T = 0 := by
  unfold edgeCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hlt : x.1.val < x.2.val := (Finset.mem_filter.mp hx).2.1
  have h₂ := x.2.isLt
  omega

private theorem picard_torsion_finrank_zero_of_count_one (T : NumericalType)
    (ℓ : ℕ) [Fact ℓ.Prime] (hcount : T.componentCount = 1) :
    let P := AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)
    let : Module (ZMod ℓ) P := AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) P = 0 := by
  classical
  have hall := intersection_eq_zero_of_componentCount_eq_one T hcount
  have hzero : intersectionMap T = 0 := by
    ext x i
    simp [intersectionMap, intersectionMatrix, hall]
  have hrange : LinearMap.range (intersectionMap T) = ⊥ := by
    simp [hzero]
  let e := (LinearMap.range (intersectionMap T)).quotEquivOfEqBot hrange
  obtain ⟨f, hf⟩ := picardGroup_embeds_intersectionCokernel T
  let f' : picardGroup T →+ (Fin T.componentCount → ℤ) :=
    e.toAddEquiv.toAddMonoidHom.comp f
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let Q := AddSubgroup.torsionBy (Fin T.componentCount → ℤ) (ℓ : ℤ)
  let : Module (ZMod ℓ) Q := AddSubgroup.torsionBy.zmodModule
  have hf' : Function.Injective f' := fun _ _ h => hf (e.injective h)
  have hmono := torsionBy_finrank_mono_of_injective (n := ℓ) f' hf'
  have hQ : Subsingleton Q := by
    have hℓne : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime ℓ).ne_zero
    have h0 (x : Q) (i : Fin T.componentCount) : x.val i = 0 := by
      have hmul : (ℓ : ℤ) * x.val i = 0 := by
        simpa [nsmul_eq_mul] using
          congrFun ((AddSubgroup.torsionBy.nsmul_iff (n := ℓ)).mp x.property) i
      exact (mul_eq_zero.mp hmul).resolve_left hℓne
    exact ⟨fun x y => Subtype.ext (funext fun i => (h0 x i).trans (h0 y i).symm)⟩
  have hQzero : Module.finrank (ZMod ℓ) Q = 0 :=
    Module.finrank_eq_zero_of_subsingleton (ZMod ℓ) Q
  have hnat : Module.finrank (ZMod ℓ)
      (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) ≤ 0 := by
    simpa [Q, hQzero] using hmono
  omega

private theorem relabel_isMinimal_iff (T : NumericalType)
    (e : Fin T.componentCount ≃ Fin T.componentCount) :
    IsMinimal (relabelType T e) ↔ IsMinimal T :=
  ⟨fun h ⟨i, hi⟩ => h ⟨e i, by simpa [relabelType] using hi.1,
      by simpa [relabelType] using hi.2⟩,
    fun h ⟨i, hi⟩ => h ⟨e.symm i, by simpa [relabelType] using hi.1,
      by simpa [relabelType] using hi.2⟩⟩

private theorem picard_torsion_bound_by_component_count (n : ℕ) :
    ∀ (T : NumericalType) (g : ℤ) (_hg : 2 ≤ g)
      (_hcount : T.componentCount = n) (_hgenus : genus T = g)
      (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : 768 * g < (ℓ : ℤ)),
      let P := AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)
      let : Module (ZMod ℓ) P := AddSubgroup.torsionBy.zmodModule
      (Module.finrank (ZMod ℓ) P : ℤ) ≤ g := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T g hg hcount hgenus ℓ inst hℓ
    let : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    by_cases hminimal : IsMinimal T
    · by_cases hn : 1 < T.componentCount
      · have hpic := minimal_matrix_torsion_bound T g hg hgenus hminimal hn ℓ hℓ
        have htop := one_sub_componentCount_add_edgeCount_le_genus_of_isMinimal
          T hminimal hn
        exact_mod_cast hpic.trans (by simpa [hgenus] using htop)
      · have hzero := picard_torsion_finrank_zero_of_count_one T ℓ
          (componentCount_eq_one_of_not_one_lt T hn)
        change Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) = 0 at hzero
        change (Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) : ℤ) ≤ g
        rw [hzero]
        omega
    · obtain ⟨i, hi⟩ : ∃ i, IsMinusOneIndex T i := by
        simpa [IsMinimal] using hminimal
      have hn : 1 < T.componentCount := by
        by_contra hnot
        rcases hi with ⟨hgi, hinter⟩
        have hdiag := intersection_eq_zero_of_componentCount_eq_one T
          (componentCount_eq_one_of_not_one_lt T hnot) i i
        have := T.weight_pos i
        omega
      let e : Fin T.componentCount ≃ Fin T.componentCount :=
        Equiv.swap i (lastIndex T)
      have he : e.symm (lastIndex T) = i := by simp [e]
      let T' := relabelType T e
      have hlastidx : lastIndex T' = lastIndex T := Fin.ext rfl
      have hlast : IsMinusOneIndex T' (lastIndex T') := by
        change T.componentGenus (e.symm (lastIndex T')) = 0 ∧
          T.intersection (e.symm (lastIndex T'))
            (e.symm (lastIndex T')) =
              -T.weight (e.symm (lastIndex T'))
        rw [hlastidx, he]
        exact hi
      have hgenus' : genus T' = g := by rw [genus_relabelType, hgenus]
      let K := (contractLast T' hlast).val
      have hKgenus : genus K = g := by
        rw [(contractLast T' hlast).property.genus_eq, hgenus']
      have hKcount : K.componentCount = T.componentCount - 1 := by
        rw [(contractLast T' hlast).property.componentCount_eq]
      have hKlt : K.componentCount < n := by omega
      let E := relabelPicardEquiv T e
      let f : picardGroup T →+ picardGroup K :=
        (contractPicardMap T' hlast).comp E.symm.toAddMonoidHom
      let : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup K) (ℓ : ℤ)) :=
        AddSubgroup.torsionBy.zmodModule
      have hf : Function.Injective f := fun _ _ hxy =>
        E.symm.injective (contractPicardMap_injective T' hlast hxy)
      have hmono := torsionBy_finrank_mono_of_injective (n := ℓ) f hf
      exact le_trans (by exact_mod_cast hmono) (ih K.componentCount hKlt K g hg rfl hKgenus ℓ hℓ)

/-- The prime torsion of the Picard group of a numerical type has dimension
at most its genus, provided the prime exceeds 768 times the genus. -/
@[stacks 0C9X "genus bound"]
public lemma finrank_picardGroup_torsionBy_le_genus
    (T : NumericalType) (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 768 * g < (ℓ : ℤ)) :
    let P := AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)
    let : Module (ZMod ℓ) P := AddSubgroup.torsionBy.zmodModule
    (Module.finrank (ZMod ℓ) P : ℤ) ≤ g :=
  picard_torsion_bound_by_component_count T.componentCount T g hg rfl hgenus ℓ hℓ

/-- For a minimal numerical type, the topological genus bounds the dimension
of the prime torsion of its Picard group. -/
@[stacks 0C9X "topological genus bound for minimal types"]
public lemma finrank_picardGroup_torsionBy_le_topGenus_of_isMinimal
    (T : NumericalType) (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (hminimal : IsMinimal T) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : 768 * g < (ℓ : ℤ)) :
    let P := AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)
    let : Module (ZMod ℓ) P := AddSubgroup.torsionBy.zmodModule
    (Module.finrank (ZMod ℓ) P : ℤ) ≤
      (1 : ℤ) - T.componentCount + edgeCount T := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy (picardGroup T) (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  by_cases hn : 1 < T.componentCount
  · exact minimal_matrix_torsion_bound T g hg hgenus hminimal hn ℓ hℓ
  · have hcount := componentCount_eq_one_of_not_one_lt T hn
    have htorsion := picard_torsion_finrank_zero_of_count_one T ℓ hcount
    have hedge := edgeCount_eq_zero_of_componentCount_eq_one T hcount
    simp [hcount, hedge, htorsion]

/-- The topological genus of a minimal numerical type of genus at least two
does not exceed its genus. -/
@[stacks 0C9X "topological genus at most genus"]
public lemma topGenus_le_genus_of_isMinimal
    (T : NumericalType) (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (hminimal : IsMinimal T) :
    (1 : ℤ) - T.componentCount + edgeCount T ≤ g := by
  by_cases hn : 1 < T.componentCount
  · simpa [hgenus] using one_sub_componentCount_add_edgeCount_le_genus_of_isMinimal T hminimal hn
  · have hcount := componentCount_eq_one_of_not_one_lt T hn
    have hedge := edgeCount_eq_zero_of_componentCount_eq_one T hcount
    rw [hcount, hedge]
    omega

end AlgebraicGeometry.NumericalType
