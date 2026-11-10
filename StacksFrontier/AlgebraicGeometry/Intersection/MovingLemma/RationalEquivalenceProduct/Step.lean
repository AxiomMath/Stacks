module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepMove
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Induction

/-!
# Tag 0B1V: the inductive step

Let `X̄ ⊆ 𝐏^N` be a closed subvariety of dimension `n`, `Y ⊆ X̄` a nonsingular open subvariety,
`α = ∑ c_i ([W_{i,0}]_r - [W_{i,∞}]_r)` a rationally trivial `r`-cycle on `Y`, and `𝒯` the
irreducible components of the fibres `W_{i,0}`, `W_{i,∞}`. For a closed subvariety `Z ⊆ Y` of
dimension `s` meeting `α` properly but not every member of `𝒯`, the proof of Tag 0B1V writes
`[Z] = C · X̄ - ∑ m_j [Z_j]` with `α · (C · X̄)` rationally trivial and every `Z_j` of smaller
excess (Tags 0B0E, 0B1T, 0B1M and 0B60). This is the inductive step of
`torFormulaCycleIntersectionProduct_single_mem_ratCycles_of_induction`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

/-- `⊤ + n` is never bounded by a natural number. -/
private theorem not_top_add_natCast_le (n a : ℕ) :
    ¬ ((⊤ : ℕ∞) : WithBot ℕ∞) + (n : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_add, top_add, ← WithBot.coe_natCast,
    WithBot.coe_le_coe]
  simp

/-- A strict drop of a dimension lowers its excess by one. -/
theorem add_le_of_lt_of_add_le_succ {x y : WithBot ℕ∞} {n K : ℕ} (hxy : x < y)
    (hy : y + (n : WithBot ℕ∞) ≤ ((K + 1 : ℕ) : WithBot ℕ∞)) :
    x + (n : WithBot ℕ∞) ≤ (K : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    induction y using WithBot.recBotCoe with
    | bot => exact absurd hxy not_lt_bot
    | coe b =>
      induction b using ENat.recTopCoe with
      | top => exact absurd hy (not_top_add_natCast_le _ _)
      | coe b =>
        induction a using ENat.recTopCoe with
        | top => exact absurd hxy (by rw [WithBot.coe_lt_coe]; simp)
        | coe a =>
          have h1 : a < b := by exact_mod_cast hxy
          have h2 : b + n ≤ K + 1 := by exact_mod_cast hy
          exact_mod_cast (by omega : a + n ≤ K)

/-- Trading the dimension of the ambient space for that of the variety. -/
theorem add_le_of_add_le_of_add_eq {x : WithBot ℕ∞} {N n a b : ℕ}
    (h : x + (N : WithBot ℕ∞) ≤ (a : WithBot ℕ∞)) (hab : a + n = N + b) :
    x + (n : WithBot ℕ∞) ≤ (b : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp
  | coe t =>
    induction t using ENat.recTopCoe with
    | top => exact absurd h (not_top_add_natCast_le _ _)
    | coe t =>
      have h2 : t + N ≤ a := by exact_mod_cast h
      exact_mod_cast (by omega : t + n ≤ b)

section Step

variable (k : Type u) [Field k] [IsAlgClosed k] {Xb : Scheme.{u}} (N : ℕ)
  (iX : Xb ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k)) [IsClosedImmersion iX]
  [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))]
  {n : ℕ} (hn : topologicalKrullDim Xb = (n : WithBot ℕ∞))
  {Y : Scheme.{u}} (j₀ : Y ⟶ Xb) [IsOpenImmersion j₀] (hU : Set.range j₀.base ⊆ regularLocus Xb)
  (p : Y ⟶ Spec (.of k)) [IsVariety k p]
  (hp : j₀ ≫ iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = p) (hY : IsRegular Y)

include hn hU hp in
open scoped Classical in
/-- **Tag 0B1V, the inductive step.** For `α = ∑ c_i ([W_{i,0}]_r - [W_{i,∞}]_r)` on `Y` and a
closed subvariety `Z = closure {z}` of dimension `s` meeting `α` properly, of excess at most
`m + 1` but not `0` with respect to the components `𝒯` of the fibres `W_{i,0}`, `W_{i,∞}`, there
is a cycle `γ` (the restriction to `Y` of `C · X̄` for the cone `C` of Tag 0B0E) with
`α · γ` rationally trivial and `[Z] = γ - ∑ m_j [Z_j]` for closed subvarieties `Z_j` of
dimension `s` meeting `α` properly and of excess at most `m`. -/
theorem exists_step (r s : ℕ) {ι : Type*} [Fintype ι]
    (W : ι → (projectiveLineProduct p).IdealSheafData) [∀ i, IsIntegral (W i).subscheme]
    (hDim : ∀ i, ∀ ξ : genericPoints (W i).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p (W i)) ξ.1 = r + 1)
    (h₀ : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (infinitySection p))
    (c : ι → ℤ) :
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
    ∀ (m : ℕ) (z : Y), topologicalKrullDim (closure ({z} : Set Y)) = (s : WithBot ℕ∞) →
      AlgebraicCycle.IntersectProperly
        (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1))
        (Function.locallyFinsuppWithin.single z 1) →
      (∀ T ∈ fibreComponentSets k p W, topologicalKrullDim ↥(closure ({z} : Set Y) ∩ T) +
        (n : WithBot ℕ∞) ≤ ((s + r + (m + 1) : ℕ) : WithBot ℕ∞)) →
      ¬ (∀ T ∈ fibreComponentSets k p W, topologicalKrullDim ↥(closure ({z} : Set Y) ∩ T) +
        (n : WithBot ℕ∞) ≤ ((s + r : ℕ) : WithBot ℕ∞)) →
      ∃ (κ : Type u) (S : Finset κ) (w : κ → Y) (c' : κ → ℤ) (γ : AlgebraicCycle Y ℤ),
        Function.locallyFinsuppWithin.single z 1 =
          γ - ∑ j ∈ S, c' j • Function.locallyFinsuppWithin.single (w j) 1 ∧
        torFormulaCycleIntersectionProduct (fieldChowSituation k) p hY ((r : ℤ) + s - n)
          (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1)) γ ∈
          ratCycles (fieldChowSituation k) p ((r : ℤ) + s - n) ∧
        ∀ j ∈ S, topologicalKrullDim (closure ({w j} : Set Y)) = (s : WithBot ℕ∞) ∧
          AlgebraicCycle.IntersectProperly
            (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
              (zeroFiber p (W i)).subschemeι r).1 -
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
              (infinityFiber p (W i)).subschemeι r).1))
            (Function.locallyFinsuppWithin.single (w j) 1) ∧
          ∀ T ∈ fibreComponentSets k p W, topologicalKrullDim ↥(closure ({w j} : Set Y) ∩ T) +
            (n : WithBot ℕ∞) ≤ ((s + r + m : ℕ) : WithBot ℕ∞) := by
  intro m z hz hαz hm hnot
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isRegular hY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have hαmem : ∀ x : Y, (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
      (zeroFiber p (W i)).subschemeι r).1 -
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (infinityFiber p (W i)).subschemeι r).1)) x ≠ 0 →
      closure ({x} : Set Y) ∈ fibreComponentSets k p W ∧
        topologicalKrullDim (closure ({x} : Set Y)) = (r : WithBot ℕ∞) := fun x hx =>
    ⟨closure_mem_fibreComponentSets_of_ne_zero k p W c r hx,
      topologicalKrullDim_of_mem_fibreComponentSets hDim h₀ hInf
        (closure_mem_fibreComponentSets_of_ne_zero k p W c r hx)⟩
  generalize hαdef : (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
      (zeroFiber p (W i)).subschemeι r).1 -
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (infinityFiber p (W i)).subschemeι r).1)) = α at hαz hαmem ⊢
  -- `Y` has the dimension of `X̄`
  obtain ⟨y₁⟩ : Nonempty Y := ⟨z⟩
  have hdY : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
    have h := ProjectiveSpaceOfModule.topologicalKrullDim_closure_image_of_isOpenImmersion k
      (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) j₀ isClosed_univ
      (IrreducibleSpace.isIrreducible_univ Y)
    have hdense : closure (j₀.base '' (Set.univ : Set Y)) = Set.univ := by
      rw [Set.image_univ]
      exact (j₀.isOpenEmbedding.isOpen_range.dense ⟨_, Set.mem_range_self y₁⟩).closure_eq
    rw [hdense, topologicalKrullDim_univ, topologicalKrullDim_univ, hn] at h
    exact h.symm
  -- `Z` fails to meet some member of `𝒯` properly, so `r, s < n`
  obtain ⟨T₀, hT₀, hT₀n⟩ : ∃ T ∈ fibreComponentSets k p W,
      ¬ (topologicalKrullDim ↥(closure ({z} : Set Y) ∩ T) + (n : WithBot ℕ∞) ≤
        ((s + r : ℕ) : WithBot ℕ∞)) := by
    by_contra hno
    exact hnot fun T hT => by_contra fun h => hno ⟨T, hT, h⟩
  have hT₀d := topologicalKrullDim_of_mem_fibreComponentSets hDim h₀ hInf hT₀
  have hs : s < n := by
    by_contra hsn
    refine hT₀n (le_trans (add_le_add_left ((topologicalKrullDim_le_of_subset
      Set.inter_subset_right).trans hT₀d.le) _) ?_)
    rw [← Nat.cast_add]
    exact_mod_cast (by omega : r + n ≤ s + r)
  have hr : r < n := by
    by_contra hrn
    refine hT₀n (le_trans (add_le_add_left ((topologicalKrullDim_le_of_subset
      Set.inter_subset_left).trans hz.le) _) ?_)
    rw [← Nat.cast_add]
    exact_mod_cast (by omega : s + n ≤ s + r)
  -- the family `𝒯` as an indexed family of closed subvarieties
  have : Finite ↥(fibreComponentSets k p W) := (finite_fibreComponentSets W).to_subtype
  let T : ↥(fibreComponentSets k p W) → IrreducibleCloseds Y := fun A =>
    ⟨A.1, isIrreducible_of_mem_fibreComponentSets A.2, isClosed_of_mem_fibreComponentSets A.2⟩
  have hTd : ∀ i, topologicalKrullDim (T i : Set Y) = (r : WithBot ℕ∞) := fun i =>
    topologicalKrullDim_of_mem_fibreComponentSets hDim h₀ hInf i.2
  -- the cone of Tag 0B0E
  obtain ⟨C, S, mW, hdisp, hCprop, hrdC, hW, hcover⟩ :=
    exists_cone_data k N iX hn hs hr j₀ hU z hz T hTd
  -- the components of `α` meet `Z` and the `Z_j` properly
  have hαZ : ∀ x : Y, α x ≠ 0 → topologicalKrullDim ↥(closure ({x} : Set Y) ∩
      closure ({z} : Set Y)) + (n : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞) := by
    intro x hx
    refine (intersectProperly_closure_iff hdY (hαmem x hx).2 hz).mp ?_
    exact hαz ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
      (by rw [genericPoint_closure_singleton]; exact hx)
      (by rw [genericPoint_closure_singleton]; simp)
  have hαW : ∀ x : Y, α x ≠ 0 → ∀ V ∈ S, topologicalKrullDim ↥(closure ({x} : Set Y) ∩
      (V : Set Y)) + (n : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞) := by
    intro x hx V hV
    rcases ((hW V hV).2 ⟨_, (hαmem x hx).1⟩).1 with h | h
    · change topologicalKrullDim ↥((V : Set Y) ∩ closure {x}) ≤
        topologicalKrullDim ↥(closure ({z} : Set Y) ∩ closure {x}) at h
      rw [Set.inter_comm]
      refine le_trans (add_le_add_left h _) ?_
      rw [Set.inter_comm]
      exact hαZ x hx
    · change topologicalKrullDim ↥((V : Set Y) ∩ closure {x}) + (n : WithBot ℕ∞) ≤
        ((s + r : ℕ) : WithBot ℕ∞) at h
      rw [Set.inter_comm, Nat.add_comm]
      exact h
  refine ⟨IrreducibleCloseds Y, S, fun V => V.isIrreducible.genericPoint, mW,
    cycleComap j₀ j₀.isOpenEmbedding.injective (cycleComap iX iX.isClosedEmbedding.injective
      (torFormulaCycleIntersectionProduct (fieldChowSituation k)
        (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
        (isRegular_projectiveSpaceOfModule k _) (s : ℤ)
        (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint 1)
        (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) 1))), ?_, ?_, ?_⟩
  · rw [hdisp, add_sub_cancel_right]
  · -- `α · (C · X̄)|_Y` is rationally trivial
    have hPd : topologicalKrullDim (projectiveSpaceOfModule k (Fin (N + 1) → k)) =
        (N : WithBot ℕ∞) :=
      topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (Module.finrank_fin_fun k)
    by_cases hne : ∃ y₀ : Y, iX.base (j₀.base y₀) ∈ (C : Set (projectiveSpaceOfModule k _))
    swap
    · have hγ0 : cycleComap j₀ j₀.isOpenEmbedding.injective
          (cycleComap iX iX.isClosedEmbedding.injective
            (torFormulaCycleIntersectionProduct (fieldChowSituation k)
              (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
              (isRegular_projectiveSpaceOfModule k _) (s : ℤ)
              (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint 1)
              (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) 1))) = 0 := by
        refine Function.locallyFinsuppWithin.ext fun y => ?_
        rw [cycleComap_apply, cycleComap_apply]
        by_contra hy
        have hm := mem_inter_of_torFormula_single_single_ne_zero k
          (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
          (isRegular_projectiveSpaceOfModule k _) hPd (s : ℤ) _ _ _ hy
        rw [C.isIrreducible.closure_genericPoint C.isClosed'] at hm
        exact hne ⟨y, hm.1.1⟩
      rw [hγ0]
      change cycleIntersectionProduct _ _ 0 ∈ _
      rw [cycleIntersectionProduct_zero_right]
      exact AddSubgroup.zero_mem _
    obtain ⟨y₀, hy₀⟩ := hne
    -- the moving family of Tag 0B1T
    have hemb : Topology.IsEmbedding (j₀ ≫ iX).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp]
      exact iX.isClosedEmbedding.isEmbedding.comp j₀.isOpenEmbedding.isEmbedding
    have hXlc : IsLocallyClosed (Set.range (j₀ ≫ iX).base) := (j₀ ≫ iX).isLocallyClosed_range
    have hXirr : IsIrreducible (Set.range (j₀ ≫ iX).base) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ Y).image _ (j₀ ≫ iX).continuous.continuousOn
    have hdimXs : topologicalKrullDim ↥(Set.range (j₀ ≫ iX).base) = (n : WithBot ℕ∞) := by
      rw [← Set.image_univ, topologicalKrullDim_image_eq_of_isEmbedding hemb,
        topologicalKrullDim_univ, hdY]
    have hdR : topologicalKrullDim ↥(Set.range iX.base) = (n : WithBot ℕ∞) := by
      rw [← Set.image_univ, topologicalKrullDim_image_eq_of_isEmbedding
        iX.isClosedEmbedding.isEmbedding, topologicalKrullDim_univ, hn]
    have hCX : topologicalKrullDim ↥((C : Set (projectiveSpaceOfModule k (Fin (N + 1) → k))) ∩
          Set.range (j₀ ≫ iX).base) +
        topologicalKrullDim (projectiveSpaceOfModule k (Fin (N + 1) → k)) ≤
        topologicalKrullDim ↥(C : Set (projectiveSpaceOfModule k (Fin (N + 1) → k))) +
          topologicalKrullDim ↥(Set.range (j₀ ≫ iX).base) := by
      have h := intersectProperly_closure_of_single hCprop
      rw [AlgebraicGeometry.intersectProperly_iff] at h
      change topologicalKrullDim ↥(closure ({C.isIrreducible.genericPoint} :
          Set (projectiveSpaceOfModule k (Fin (N + 1) → k))) ∩
          closure {iX.base (genericPoint Xb)}) +
          topologicalKrullDim (projectiveSpaceOfModule k (Fin (N + 1) → k)) ≤
        topologicalKrullDim ↥(closure ({C.isIrreducible.genericPoint} :
          Set (projectiveSpaceOfModule k (Fin (N + 1) → k)))) +
          topologicalKrullDim ↥(closure {iX.base (genericPoint Xb)}) at h
      rw [C.isIrreducible.closure_genericPoint C.isClosed', ← range_eq_closure_singleton iX,
        hdR] at h
      rw [hdimXs]
      refine le_trans (add_le_add_left (topologicalKrullDim_le_of_subset
        (Set.inter_subset_inter_right _ ?_)) _) h
      rintro _ ⟨y, rfl⟩
      exact ⟨j₀.base y, rfl⟩
    let T' : ↥(fibreComponentSets k p W) → Set (projectiveSpaceOfModule k (Fin (N + 1) → k)) :=
      fun i => (j₀ ≫ iX).base '' (T i : Set Y)
    have hTX : ∀ i, T' i ⊆ Set.range (j₀ ≫ iX).base := fun i => Set.image_subset_range _ _
    have hTc : ∀ i, IsClosed {x : Set.range (j₀ ≫ iX).base | x.1 ∈ T' i} := by
      intro i
      let e := hemb.toHomeomorph
      have hset : {x : Set.range (j₀ ≫ iX).base | x.1 ∈ T' i} = e.symm ⁻¹' (T i : Set Y) := by
        ext x
        obtain ⟨y, rfl⟩ := e.surjective x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Homeomorph.symm_apply_apply]
        exact hemb.injective.mem_set_image
      rw [hset]
      exact (T i).isClosed.preimage e.symm.continuous
    have hTirr : ∀ i, IsIrreducible (T' i) := fun i =>
      (T i).isIrreducible.image _ (j₀ ≫ iX).continuous.continuousOn
    have hTd' : ∀ i, topologicalKrullDim ↥(T' i) = (r : WithBot ℕ∞) := fun i => by
      rw [topologicalKrullDim_image_eq_of_isEmbedding hemb]; exact hTd i
    obtain ⟨Cfam, -, hzero, hfam, hrdfam, hinf⟩ := exists_family_data k (Fin (N + 1) → k) N
      (Module.finrank_fin_fun k) C (Set.range (j₀ ≫ iX).base) hXlc hXirr hCX T' hTX hTc hTirr r
      hTd'
    -- Tag 0B1M: `(C · X̄)|_Y = ∑ b(e) [E_{e,0}]_s`
    obtain ⟨Se, b, hγeq, hE⟩ := exists_zeroFiber_presentation k
      (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) (isRegular_projectiveSpaceOfModule k _)
      hPd iX hn j₀ p hp hY C hCprop hrdC y₀ hy₀ Cfam hzero hfam hrdfam
    rw [hγeq]
    change cycleIntersectionProductRightHom (torFormulaSubvarietyProductTotal
      (fieldChowSituation k) p hY ((r : ℤ) + s - n)) α _ ∈ _
    rw [map_sum]
    refine AddSubgroup.sum_mem _ fun e he => ?_
    rw [map_zsmul]
    refine AddSubgroup.zsmul_mem _ ?_ _
    obtain ⟨hrel, h₀e, hzs, his⟩ := hE e he
    have := isIntegral_integralComponentAt e
    have hcn : (relativeDimension (fieldChowSituation k).dimensionFunction
        (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) C.isIrreducible.genericPoint).toNat +
          r + n = N + (s + r) := by
      have := relativeDimension_fieldChowSituation_nonneg k
        (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) C.isIrreducible.genericPoint
      omega
    rw [← hαdef]
    refine torFormulaCycleIntersectionProduct_zeroFiber_mem_ratCycles k p hY n r s hdY W hDim h₀
      hInf c (integralComponentAt e)
      (relativeDimension_familyBase_integralComponentAt_genericPoints (fieldChowSituation k) p e
        hrel) h₀e ?_ ?_
    · intro x hx
      rw [hαdef] at hx
      refine topologicalKrullDim_add_le_of_subset_sUnion
        (isClosed_closure.inter (zeroFiber p (integralComponentAt e)).support.isClosed)
        (𝒜 := insert (closure ({z} : Set Y)) ((fun V : IrreducibleCloseds Y => (V : Set Y)) '' S))
        ((Set.Finite.image _ S.finite_toSet).insert _) ?_ ?_ n (r + s) ?_
      · rintro A (rfl | ⟨V, -, rfl⟩)
        · exact isClosed_closure
        · exact V.isClosed
      · rintro y ⟨-, hy⟩
        rcases hcover y (hzs y hy) with h | ⟨V, hVS, hyV⟩
        · exact Set.mem_sUnion.mpr ⟨_, Set.mem_insert _ _, h⟩
        · exact Set.mem_sUnion.mpr ⟨V, Set.mem_insert_of_mem _ ⟨V, hVS, rfl⟩, hyV⟩
      · rintro A (rfl | ⟨V, hVS, rfl⟩)
        · exact le_trans (add_le_add_left (topologicalKrullDim_le_of_subset
            (by intro y hy; exact ⟨hy.1.1, hy.2⟩)) _) (hαZ x hx)
        · exact le_trans (add_le_add_left (topologicalKrullDim_le_of_subset
            (by intro y hy; exact ⟨hy.1.1, hy.2⟩)) _) (hαW x hx V hVS)
    · intro A hA
      have h1 : topologicalKrullDim ↥(((infinityFiber p (integralComponentAt e)).support :
          Set Y) ∩ A) ≤ topologicalKrullDim ↥((infinitySection
            (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))).base ⁻¹'
            (Cfam : Set _) ∩ T' ⟨A, hA⟩) := by
        rw [← topologicalKrullDim_image_eq_of_isEmbedding hemb]
        refine topologicalKrullDim_le_of_subset ?_
        rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨his y hy1, ⟨y, hy2, rfl⟩⟩
      exact add_le_of_add_le_of_add_eq (le_trans (add_le_add_left h1 _) (hinf ⟨A, hA⟩)) hcn
  · intro V hV
    have hgenV : closure ({V.isIrreducible.genericPoint} : Set Y) = (V : Set Y) :=
      V.isIrreducible.closure_genericPoint V.isClosed
    refine ⟨by rw [hgenV]; exact (hW V hV).1, ?_, ?_⟩
    · intro A B hA hB
      have hBV : B.isIrreducible.genericPoint = V.isIrreducible.genericPoint := by
        by_contra hne
        exact hB (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hne])
      have hA' : A = ⟨closure {A.isIrreducible.genericPoint}, isIrreducible_singleton.closure,
          isClosed_closure⟩ := by
        ext1; exact (A.isIrreducible.closure_genericPoint A.isClosed).symm
      have hB' : B = ⟨closure {V.isIrreducible.genericPoint}, isIrreducible_singleton.closure,
          isClosed_closure⟩ := by
        ext1; rw [← hBV]; exact (B.isIrreducible.closure_genericPoint B.isClosed).symm
      rw [hA', hB']
      refine (intersectProperly_closure_iff hdY (hαmem _ hA).2
        (by rw [hgenV]; exact (hW V hV).1)).mpr ?_
      rw [hgenV]
      exact hαW _ hA V hV
    · intro T' hT'
      rw [hgenV]
      by_cases hzT : topologicalKrullDim ↥(closure ({z} : Set Y) ∩ T') + (n : WithBot ℕ∞) ≤
          ((s + r : ℕ) : WithBot ℕ∞)
      · have hmono : ((s + r : ℕ) : WithBot ℕ∞) ≤ ((s + r + m : ℕ) : WithBot ℕ∞) := by
          exact_mod_cast (by omega : s + r ≤ s + r + m)
        rcases ((hW V hV).2 ⟨T', hT'⟩).1 with h | h
        · exact le_trans (add_le_add_left h _) (hzT.trans hmono)
        · exact le_trans h hmono
      · exact add_le_of_lt_of_add_le_succ (((hW V hV).2 ⟨T', hT'⟩).2 hzT) (hm T' hT')

end Step

end Stacks.Intersection.RationalEquivalenceProduct

end
