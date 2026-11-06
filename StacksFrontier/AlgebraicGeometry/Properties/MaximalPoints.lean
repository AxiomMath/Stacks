module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute

/-!
# Maximal points of a subset of a Noetherian scheme

For a subset `T` of a topological space, consider the points of `T` which admit no nontrivial
generalization in `T`. There are no nontrivial specializations between these maximal points;
on a Noetherian scheme every point of `T` is a specialization of one of them, and they have the
same closure as `T`. As a consequence, an infinite dense subset of a Noetherian scheme contains
a countable subset which is still dense.

## Main definitions

* `maximalPoints` is the set of points of a subset which have no nontrivial generalization in
  that subset.

## Main results

* `specialization_eq_of_mem_maximalPoints` gives the absence of nontrivial specializations
  between maximal points.
* `AlgebraicGeometry.exists_maximalPoint_specializes` says that every point of the subset is a
  specialization of a maximal point.
* `AlgebraicGeometry.closure_maximalPoints` identifies the closure of the maximal points with
  the closure of the original subset.
* `AlgebraicGeometry.exists_countable_dense_subset` produces a countable dense subset of a given
  infinite dense subset of a Noetherian scheme.

## Implementation notes

The definition and the first result are stated for an arbitrary topological space, since
Noetherianity is only needed for the existence assertion. Specialization is Mathlib's
`Specializes`, written `x ⤳ y`. The subset and density conditions for the countable-subset
result are stated on the underlying topological space of the scheme.

## References

* [Stacks Project, Tag 0G2F](https://stacks.math.columbia.edu/tag/0G2F)
* [Stacks Project, Tag 0G2R](https://stacks.math.columbia.edu/tag/0G2R)
-/

@[expose] public section

open AlgebraicGeometry Set

universe u

/-- The points of `T` which admit no nontrivial generalization belonging to `T`. -/
@[stacks 0G2R "the set of maximal points"]
def maximalPoints {X : Type u} [TopologicalSpace X] (T : Set X) : Set X :=
  {x | x ∈ T ∧ ∀ y ∈ T, y ⤳ x → y = x}

/-- There is no nontrivial specialization between maximal points of a subset. -/
@[stacks 0G2R "part (a)"]
theorem specialization_eq_of_mem_maximalPoints
    {X : Type u} [TopologicalSpace X] {T : Set X} {x y : X}
    (hx : x ∈ maximalPoints T) (hy : y ∈ maximalPoints T)
    (hxy : x ⤳ y) : x = y :=
  hy.2 x hx.1 hxy

namespace AlgebraicGeometry

/-- Every point of a subset of a Noetherian scheme is a specialization of a maximal point
of that subset. -/
@[stacks 0G2R "part (b)"]
theorem exists_maximalPoint_specializes
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) {x : X} (hx : x ∈ T) :
    ∃ y ∈ maximalPoints T, y ⤳ x := by
  obtain ⟨y, hy, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT
      (fun y : X => y ∈ T ∧ y ⤳ x)
      (fun y => ringKrullDim (X.presheaf.stalk y))
      ⟨x, hx, specializes_rfl⟩
  refine ⟨y, ⟨hy.1, ?_⟩, hy.2⟩
  intro z hzT hzy
  have hzx : z ⤳ x := hzy.trans hy.2
  by_cases hEq : z = y
  · exact hEq
  · have hlt : y < z := by
      exact ⟨Scheme.le_iff_specializes.2 hzy,
        fun hrev => hEq (hzy.antisymm (Scheme.le_iff_specializes.mp hrev)).eq⟩
    have hfinite : Order.coheight z < ⊤ := by
      have hdimz : ringKrullDim (X.presheaf.stalk z) < ⊤ := ringKrullDim_lt_top
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z] at hdimz
      change ((Order.coheight z : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) at hdimz
      exact WithBot.coe_lt_coe.mp hdimz
    have hdim : ringKrullDim (X.presheaf.stalk z) <
        ringKrullDim (X.presheaf.stalk y) := by
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z,
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight y]
      exact_mod_cast Order.coheight_strictAnti hlt hfinite
    exact False.elim ((not_lt_of_ge (hmin ⟨hzT, hzx⟩ hdim.le)) hdim)

/-- The maximal points of a subset of a Noetherian scheme have the same closure as the
subset. -/
@[stacks 0G2R "part (c)"]
theorem closure_maximalPoints
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) :
    closure (maximalPoints T) = closure T := by
  apply subset_antisymm
  · exact closure_mono (by rintro y ⟨hy, _⟩; exact hy)
  · refine closure_minimal ?_ isClosed_closure
    rintro x hx
    obtain ⟨y, hy, hyx⟩ := exists_maximalPoint_specializes X T hx
    exact closure_mono (singleton_subset_iff.mpr hy) hyx.mem_closure

variable {S : Scheme.{u}}

/-- Pulling a subset back to a subtype and pushing it forward recovers it. -/
private theorem image_preimage_subtype {X : Type*} {Y A : Set X} (hA : A ⊆ Y) :
    Subtype.val '' (Subtype.val ⁻¹' A : Set Y) = A := by
  rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hA]

/-- A point whose closure is the closure of a countable subset of `T` lying below it. -/
private def hasCountableDenseTrace (T : Set S) (x : S) : Prop :=
  ∃ E : Set S, E ⊆ closure ({x} : Set S) ∩ T ∧ E.Countable ∧
    closure E = closure ({x} : Set S)

/-- A choice of such a countable subset, empty when none exists. -/
private noncomputable def denseTrace (T : Set S) (x : S) : Set S := by
  classical
  exact if h : hasCountableDenseTrace T x then Classical.choose h else ∅

/-- The defining properties of `denseTrace` where it is chosen. -/
private theorem denseTrace_spec (T : Set S) (x : S)
    (h : hasCountableDenseTrace T x) :
    denseTrace T x ⊆ closure ({x} : Set S) ∩ T ∧
      (denseTrace T x).Countable ∧ closure (denseTrace T x) = closure ({x} : Set S) := by
  unfold denseTrace
  rw [dite_eq_left_of_eq_true (by simpa using h)]
  exact Classical.choose_spec h

/-- A countable union of dense traces is countable. -/
private theorem countable_union_denseTraces {T : Set S} {A : Set S}
    (hA : A.Countable) (hAP : A ⊆ {x | hasCountableDenseTrace T x}) :
    (⋃ x ∈ A, denseTrace T x).Countable :=
  hA.biUnion fun x hx => (denseTrace_spec T x (hAP hx)).2.1

/-- A union of dense traces over points having one is contained in `T`. -/
private theorem iUnion_denseTrace_subset {T : Set S} {A : Set S}
    (hAP : A ⊆ {x | hasCountableDenseTrace T x}) :
    (⋃ x ∈ A, denseTrace T x) ⊆ T := by
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨s, hsA, hsx⟩
  exact (denseTrace_spec T s (hAP hsA)).1 hsx |>.2

/-- A union of dense traces has the same closure as the set of points it is taken over. -/
private theorem closure_union_denseTraces {T : Set S} {A : Set S}
    (hAP : A ⊆ {x | hasCountableDenseTrace T x}) :
    closure (⋃ x ∈ A, denseTrace T x) = closure A := by
  apply le_antisymm
  · apply closure_minimal
    · intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨x, hxA, hyx⟩
      exact closure_mono (Set.singleton_subset_iff.mpr hxA)
        ((denseTrace_spec T x (hAP hxA)).1 hyx |>.1)
    · exact isClosed_closure
  · apply closure_minimal
    · intro x hx
      apply closure_mono _ ((denseTrace_spec T x (hAP hx)).2.2.symm ▸
        subset_closure (by simp : x ∈ ({x} : Set S)))
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨x, hx, hy⟩
    · exact isClosed_closure

/-- A generic point of an irreducible component of a Noetherian subspace has a countable
dense trace. -/
private theorem genericPoint_has_countable_trace {T : Set S} {Y : Set S}
    [TopologicalSpace.NoetherianSpace Y] {B : Set Y} (hB : Dense B)
    (hBc : B.Countable) (hBT : Subtype.val '' B ⊆ T)
    (g : {x : Y // x ∈ genericPoints Y}) : hasCountableDenseTrace T g.1.1 := by
  let C : Set Y := closure ({g.1} : Set Y)
  have hgC : C ∈ irreducibleComponents Y := g.2
  obtain ⟨U, hUopen, ⟨u, hu⟩, hUC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      C hgC
  let E : Set S := Subtype.val '' (B ∩ C)
  have hEsub : E ⊆ closure ({g.1.1} : Set S) ∩ T := by
    rintro z ⟨b, ⟨hbB, hbC⟩, rfl⟩
    refine ⟨?_, hBT ⟨b, hbB, rfl⟩⟩
    simpa using (closure_subtype).1 hbC
  refine ⟨E, hEsub, (hBc.mono Set.inter_subset_left).image Subtype.val, ?_⟩
  apply le_antisymm
  · exact closure_minimal (fun z hz => (hEsub hz).1) isClosed_closure
  · apply closure_minimal
    · have hgE : g.1.1 ∈ closure E := by
        rw [mem_closure_iff]
        intro O hO hgO
        have hgU : g.1 ∈ U := by
          have huC : u ∈ closure ({g.1} : Set Y) := hUC hu
          rw [mem_closure_iff] at huC
          obtain ⟨z, hzU, hzg⟩ := huC U hUopen hu
          have hzg' : z = g.1 := by simpa using hzg
          simpa [hzg'] using hzU
        let V : Set Y := Subtype.val ⁻¹' O
        let W : Set Y := U ∩ V
        obtain ⟨b, hbW, hbB⟩ := hB.inter_open_nonempty W
          (hUopen.inter (hO.preimage continuous_subtype_val)) ⟨g.1, hgU, hgO⟩
        exact ⟨b.1, hbW.2, b, ⟨hbB, hUC hbW.1⟩, rfl⟩
      exact Set.singleton_subset_iff.mpr hgE
    · exact isClosed_closure

/-- The maximal points for having a countable dense trace form a finite set. -/
private theorem maximal_denseTrace_finite (T : Set S) [IsNoetherian S] :
    (maximalPoints {x | hasCountableDenseTrace T x}).Finite := by
  classical
  let P : Set S := {x | hasCountableDenseTrace T x}
  let M : Set S := maximalPoints P
  by_contra hMfinite
  have hMinfinite : M.Infinite := hMfinite
  obtain ⟨A, hAM, hAcount, hAinf⟩ := hMinfinite.exists_subset_countable_infinite
  have hAP : A ⊆ P := fun x hx => (hAM hx).1
  let B : Set S := ⋃ x ∈ A, denseTrace T x
  have hBcount : B.Countable := countable_union_denseTraces hAcount hAP
  have hBT : B ⊆ T := iUnion_denseTrace_subset hAP
  have hBclosure : closure B = closure A := closure_union_denseTraces hAP
  let Y : Set S := closure A
  have hBY : B ⊆ Y := by
    intro x hx
    show x ∈ closure A
    rw [← hBclosure]
    exact subset_closure hx
  let AY : Set Y := Subtype.val ⁻¹' A
  have hAYimage : Subtype.val '' AY = A := image_preimage_subtype subset_closure
  have hAYinf : AY.Infinite := by
    apply Set.Infinite.of_image Subtype.val
    simpa [hAYimage] using hAinf
  let BY : Set Y := Subtype.val ⁻¹' B
  have hBYcount : BY.Countable := hBcount.preimage Subtype.val_injective
  have hBYimage : Subtype.val '' BY = B := image_preimage_subtype hBY
  have hBYdense : Dense BY := by
    rw [dense_iff_closure_eq]
    ext y
    simp [closure_subtype, hBYimage, hBclosure]
  let : QuasiSober Y := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  let : T0Space Y := inferInstance
  have hfiniteGeneric : (genericPoints Y).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hcover : AY ⊆ ⋃ g ∈ genericPoints Y, closure ({g} : Set Y) := by
    intro a _
    have haComp : a ∈ ⋃₀ irreducibleComponents Y := by
      rw [sUnion_irreducibleComponents]
      trivial
    rcases Set.mem_sUnion.mp haComp with ⟨C, hC, haC⟩
    let g : {x : Y // x ∈ genericPoints Y} :=
      ⟨genericPoints.ofComponent ⟨C, hC⟩, by simp⟩
    have hgen : closure ({g.1} : Set Y) = C :=
      (genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩).def
    refine Set.mem_iUnion₂.mpr ⟨g.1, g.2, ?_⟩
    rw [hgen]
    exact haC
  have hex : ∃ g : {x : Y // x ∈ genericPoints Y},
      (AY ∩ closure ({g.1} : Set Y)).Infinite := by
    by_contra hn
    have hfiniteFiber : ∀ g ∈ genericPoints Y,
        (AY ∩ closure ({g} : Set Y)).Finite := by
      intro g hg
      by_contra hnot
      exact hn ⟨⟨g, hg⟩, hnot⟩
    have hunionfinite : (⋃ g ∈ genericPoints Y, AY ∩ closure ({g} : Set Y)).Finite :=
      hfiniteGeneric.biUnion hfiniteFiber
    have hcover' : AY ⊆ ⋃ g ∈ genericPoints Y, AY ∩ closure ({g} : Set Y) := by
      intro a ha
      rcases Set.mem_iUnion₂.mp (hcover ha) with ⟨g, hg, hag⟩
      exact Set.mem_iUnion₂.mpr ⟨g, hg, ha, hag⟩
    exact hAYinf (hunionfinite.subset hcover')
  obtain ⟨g, hginf⟩ := hex
  have hgP : g.1.1 ∈ P := by
    show hasCountableDenseTrace T g.1.1
    exact genericPoint_has_countable_trace hBYdense hBYcount
      (by simpa [hBYimage] using hBT) g
  have hFsub : AY ∩ closure ({g.1} : Set Y) ⊆ {g.1} := by
    rintro a ⟨ha, hspec⟩
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact ((hAM (by simpa [AY] using ha)).2 g.1.1 hgP
      (specializes_iff_mem_closure.mpr
        (by simpa using (closure_subtype).1 hspec))).symm
  exact hginf ((Set.finite_singleton _).subset hFsub)

/-- An infinite dense subset of a Noetherian scheme contains a countable dense
subset. -/
@[stacks 0G2F]
theorem exists_countable_dense_subset (S : Scheme.{u}) [IsNoetherian S]
    (T : Set S) (_hT_infinite : T.Infinite) (hT_dense : Dense T) :
    ∃ E : Set S, E ⊆ T ∧ E.Countable ∧ Dense E := by
  classical
  let P : Set S := {x | hasCountableDenseTrace T x}
  have hTP : T ⊆ P := by
    intro x hx
    exact ⟨{x}, Set.singleton_subset_iff.mpr ⟨subset_closure rfl, hx⟩,
      Set.countable_singleton x, rfl⟩
  let M : Set S := maximalPoints P
  have hMfinite : M.Finite := maximal_denseTrace_finite T
  have hMP : M ⊆ P := fun x hx => hx.1
  let E : Set S := ⋃ x ∈ M, denseTrace T x
  refine ⟨E, iUnion_denseTrace_subset hMP, countable_union_denseTraces hMfinite.countable hMP, ?_⟩
  intro x
  rw [show closure E = closure M by simpa [E] using closure_union_denseTraces (T := T) hMP,
    show closure M = closure P by simpa [M] using closure_maximalPoints S P]
  exact closure_mono hTP (hT_dense x)

end AlgebraicGeometry

end
