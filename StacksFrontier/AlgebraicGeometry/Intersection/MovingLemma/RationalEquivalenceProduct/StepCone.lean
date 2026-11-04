module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.ConeComponents
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.CycleDecomposition
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyConstantScheme
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.DimensionOfProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.ZeroFibreDegeneration
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectProperlyLinear

/-!
# Tag 0B1V: the cone of Tag 0B0E read on `X`

For a nonsingular closed subvariety `X ⊆ 𝐏(V)`, a closed subvariety `Z = closure {z}` of `X` of
dimension `s` and finitely many closed subvarieties `T_i` of dimension `r`, Tag 0B0E supplies a
closed subvariety `C ⊆ 𝐏(V)` meeting `X` properly with `C · X = [Z] + ∑ m_W [W]`. This file reads
the conclusion on `X` and adds what the positivity of intersection multiplicities gives: the
dimension count `dim C + dim X = dim 𝐏(V) + s`, and that every point of `C ∩ X` lies on `Z` or on
one of the `W`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

/-- The generic point of the closure of a point is the point. -/
theorem genericPoint_closure_eq {T : Type*} [TopologicalSpace T] [QuasiSober T] [T0Space T]
    (x : T) : (isIrreducible_singleton (x := x)).closure.genericPoint = x :=
  ((isIrreducible_singleton (x := x)).closure.isGenericPoint_genericPoint isClosed_closure).eq
    isGenericPoint_closure

/-- The image under a closed immersion of the closure of a point is the closure of the image. -/
theorem image_closure_singleton_eq {A B : Scheme.{u}} (i : A ⟶ B) [IsClosedImmersion i] (a : A) :
    i.base '' closure ({a} : Set A) = closure ({i.base a} : Set B) := by
  rw [← i.isClosedEmbedding.closure_image_eq, Set.image_singleton]

/-- A nonempty open subscheme of an irreducible scheme locally of finite type over a field has
the dimension of the ambient scheme. -/
theorem topologicalKrullDim_eq_of_isOpenImmersion (k : Type u) [Field k] {X Y : Scheme.{u}}
    (q : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q] [IrreducibleSpace X]
    (j₀ : Y ⟶ X) [IsOpenImmersion j₀] [Nonempty Y] :
    topologicalKrullDim Y = topologicalKrullDim X := by
  have : IrreducibleSpace Y := j₀.isOpenEmbedding.irreducibleSpace
  have h := topologicalKrullDim_closure_image_of_isOpenImmersion k q j₀ isClosed_univ
    (IrreducibleSpace.isIrreducible_univ Y)
  rw [Set.image_univ, (j₀.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).closure_eq,
    topologicalKrullDim_univ, topologicalKrullDim_univ] at h
  exact h.symm

/-- A point of projective space whose closure has dimension `m` has relative dimension `m`. -/
theorem relativeDimension_eq_of_topologicalKrullDim_closure (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) (w : projectiveSpaceOfModule k (Fin (N + 1) → k)) {m : ℕ}
    (h : topologicalKrullDim ↥(closure ({w} : Set (projectiveSpaceOfModule k (Fin (N + 1) → k)))) =
      (m : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) w = m := by
  rw [topologicalKrullDim_closure_eq
    (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))] at h
  have := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k
    (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) w
  have h' : m = (relativeDimension (fieldChowSituation k).dimensionFunction
      (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) w).toNat := by
    exact_mod_cast h.symm
  omega

/-- The generic point of `𝐏(V)`, `dim V = N + 1`, has relative dimension `N`. -/
theorem relativeDimension_genericPoint_projectiveSpaceOfModule (k : Type u) [Field k]
    [IsAlgClosed k] (N : ℕ) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
      (genericPoint (projectiveSpaceOfModule k (Fin (N + 1) → k))) = N :=
  relativeDimension_eq_of_topologicalKrullDim_closure k N _ (by
    rw [genericPoint_closure, topologicalKrullDim_univ]
    exact topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (Module.finrank_fin_fun k))

/-- The image of the generic point of an irreducible closed subscheme `X` of `𝐏(V)` has relative
dimension `dim X`. -/
theorem relativeDimension_image_genericPoint (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k)) [IsClosedImmersion iX]
    [IrreducibleSpace X] {n : ℕ} (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) (iX.base (genericPoint X)) = n :=
  relativeDimension_eq_of_topologicalKrullDim_closure k N _ (by
    rw [← image_closure_singleton_eq, genericPoint_closure,
      topologicalKrullDim_image_eq_of_isEmbedding iX.isClosedEmbedding.isEmbedding,
      topologicalKrullDim_univ, hn])

open scoped Classical in
/-- If two points of projective space intersect properly, every point of the intersection of their
closures satisfies the relative dimension bound of a proper intersection. -/
theorem relativeDimension_add_le_of_intersectProperly (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) {c x : projectiveSpaceOfModule k (Fin (N + 1) → k)}
    (hprop : AlgebraicCycle.IntersectProperly (Function.locallyFinsuppWithin.single c (1 : ℤ))
      (Function.locallyFinsuppWithin.single x (1 : ℤ))) :
    ∀ w ∈ closure ({c} : Set (projectiveSpaceOfModule k (Fin (N + 1) → k))) ∩
        closure ({x} : Set (projectiveSpaceOfModule k (Fin (N + 1) → k))),
      relativeDimension (fieldChowSituation k).dimensionFunction
          (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
          (genericPoint (projectiveSpaceOfModule k (Fin (N + 1) → k))) +
        relativeDimension (fieldChowSituation k).dimensionFunction
          (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) w ≤
      relativeDimension (fieldChowSituation k).dimensionFunction
          (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) c +
        relativeDimension (fieldChowSituation k).dimensionFunction
          (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) x := by
  intro w hw
  have hdP : topologicalKrullDim (projectiveSpaceOfModule k (Fin (N + 1) → k)) =
      (N : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (Module.finrank_fin_fun k)
  have hset := AlgebraicCycle.IntersectProperly.of_ne_zero hprop (x := c) (y := x)
    (by simp [Function.locallyFinsuppWithin.single_apply])
    (by simp [Function.locallyFinsuppWithin.single_apply])
  rw [AlgebraicGeometry.intersectProperly_iff] at hset
  change topologicalKrullDim ↥(closure ({c} : Set _) ∩ closure ({x} : Set _)) +
      topologicalKrullDim _ ≤
    topologicalKrullDim ↥(closure ({c} : Set _)) + topologicalKrullDim ↥(closure ({x} : Set _))
    at hset
  have hwle : topologicalKrullDim ↥(closure ({w} : Set (projectiveSpaceOfModule k
      (Fin (N + 1) → k)))) ≤ topologicalKrullDim ↥(closure ({c} : Set _) ∩ closure ({x} : Set _)) :=
    topologicalKrullDim_le_of_subset
      ((isClosed_closure.inter isClosed_closure).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hw))
  have h₂ := (add_le_add_left hwle _).trans hset
  have hcl := topologicalKrullDim_closure_eq (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
  rw [hcl, hcl, hcl, hdP] at h₂
  have h₃ : ((relativeDimension (fieldChowSituation k).dimensionFunction
      (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) w).toNat + N : ℕ) ≤
      (relativeDimension (fieldChowSituation k).dimensionFunction
        (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) c).toNat +
      (relativeDimension (fieldChowSituation k).dimensionFunction
        (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) x).toNat := by
    exact_mod_cast h₂
  have := relativeDimension_genericPoint_projectiveSpaceOfModule k N
  have hnn := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k
    (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
  have := hnn w
  have := hnn c
  have := hnn x
  omega

/-- Let `Y → X` be an open and `X → P` a closed immersion. If the image of `y : Y` in `P` is a
specialization of a point `p` in the range of `X → P`, then `p` is the image of a point `y'` of `Y`
and `y` is a specialization of `y'`. -/
theorem exists_eq_and_mem_closure_of_mem_closure {X Y P : Scheme.{u}} (iX : X ⟶ P)
    [IsClosedImmersion iX] (j₀ : Y ⟶ X) [IsOpenImmersion j₀] {y : Y} {p : P}
    (hp : p ∈ Set.range iX.base) (hy : iX.base (j₀.base y) ∈ closure ({p} : Set P)) :
    ∃ y', p = iX.base (j₀.base y') ∧ y ∈ closure ({y'} : Set Y) := by
  obtain ⟨x', rfl⟩ := hp
  rw [← image_closure_singleton_eq] at hy
  obtain ⟨x'', hx''cl, hx''⟩ := hy
  rw [iX.isClosedEmbedding.injective hx''] at hx''cl
  obtain ⟨y', rfl⟩ : x' ∈ Set.range j₀.base :=
    (specializes_iff_mem_closure.mpr hx''cl).mem_open j₀.isOpenEmbedding.isOpen_range
      (Set.mem_range_self y)
  refine ⟨y', rfl, ?_⟩
  rw [j₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
  exact hx''cl

/-- The closure of the image of the generic point under a closed immersion is the range. -/
private theorem closure_image_genericPoint_eq_range {X P : Scheme.{u}} (iX : X ⟶ P)
    [IsClosedImmersion iX] [IrreducibleSpace X] :
    closure ({iX.base (genericPoint X)} : Set P) = Set.range iX.base := by
  rw [← image_closure_singleton_eq, genericPoint_closure, Set.image_univ]

/-- The range of a closed immersion from an irreducible scheme is an irreducible closed subset
whose generic point is the image of the generic point. -/
theorem exists_irreducibleCloseds_eq_range {X P : Scheme.{u}} (iX : X ⟶ P) [IsClosedImmersion iX]
    [IrreducibleSpace X] :
    ∃ XC : IrreducibleCloseds P, (XC : Set P) = Set.range iX.base ∧
      XC.isIrreducible.genericPoint = iX.base (genericPoint X) := by
  let XC : IrreducibleCloseds P := ⟨Set.range iX.base, by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ iX.continuous.continuousOn,
    iX.isClosedEmbedding.isClosed_range⟩
  refine ⟨XC, rfl, (XC.isIrreducible.isGenericPoint_genericPoint XC.isClosed').eq ?_⟩
  rw [isGenericPoint_def, closure_image_genericPoint_eq_range]
  rfl

/-- If every point of `closure {c} ∩ X` specializes from a point of `closure {c} ∩ X` with
property `Q`, every point of the open `Y ⊆ X` lying in `closure {c}` specializes from a point of
`Y` whose image has property `Q`. -/
theorem exists_mem_closure_of_forall_mem_inter {X Y P : Scheme.{u}} (iX : X ⟶ P)
    [IsClosedImmersion iX] [IrreducibleSpace X] (j₀ : Y ⟶ X) [IsOpenImmersion j₀] {c : P}
    {Q : P → Prop}
    (hG : ∀ w ∈ closure ({c} : Set P) ∩ closure ({iX.base (genericPoint X)} : Set P),
      ∃ z ∈ closure ({c} : Set P) ∩ closure ({iX.base (genericPoint X)} : Set P),
        w ∈ closure ({z} : Set P) ∧ Q z)
    {y : Y} (hy : iX.base (j₀.base y) ∈ closure ({c} : Set P)) :
    ∃ y', y ∈ closure ({y'} : Set Y) ∧ Q (iX.base (j₀.base y')) := by
  obtain ⟨z', hz'inter, hwz', hQ⟩ := hG _ ⟨hy, by
    rw [closure_image_genericPoint_eq_range]
    exact Set.mem_range_self _⟩
  have hz'X := hz'inter.2
  rw [closure_image_genericPoint_eq_range] at hz'X
  obtain ⟨y', rfl, hyy'⟩ := exists_eq_and_mem_closure_of_mem_closure iX j₀ hz'X hwz'
  exact ⟨y', hyy', hQ⟩

open scoped Classical in
/-- At a point `y` that is none of the generic points of the `W`, the coefficient of
`[z] + ∑ m_W [W]` is `1` if `y = z` and `0` otherwise. -/
theorem single_add_sum_smul_single_apply_of_forall_ne {Y : Scheme.{u}} (z y : Y)
    (S : Finset (IrreducibleCloseds Y)) (m : IrreducibleCloseds Y → ℤ)
    (hy : ∀ W ∈ S, y ≠ W.isIrreducible.genericPoint) :
    (Function.locallyFinsuppWithin.single z (1 : ℤ) +
      ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single W.isIrreducible.genericPoint 1 :
        AlgebraicCycle Y ℤ) y = if y = z then 1 else 0 := by
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Finset.sum_eq_zero fun W hW => by
      rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
        Function.locallyFinsuppWithin.single_apply, ite_eq_right (hy W hW), smul_zero],
    Function.locallyFinsuppWithin.single_apply, add_zero]

open scoped Classical in
/-- A specialization of a point in the support of `[z] + ∑ m_W [W]` lies on `closure {z}` or on
one of the `W`. -/
theorem mem_closure_or_exists_mem_of_apply_ne_zero {Y : Scheme.{u}} (z : Y)
    (S : Finset (IrreducibleCloseds Y)) (m : IrreducibleCloseds Y → ℤ) {y y' : Y}
    (hyy' : y ∈ closure ({y'} : Set Y))
    (hy' : (Function.locallyFinsuppWithin.single z (1 : ℤ) +
      ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single W.isIrreducible.genericPoint 1 :
        AlgebraicCycle Y ℤ) y' ≠ 0) :
    y ∈ closure ({z} : Set Y) ∨ ∃ W ∈ S, y ∈ (W : Set Y) := by
  by_cases hy'z : y' = z
  · subst hy'z
    exact Or.inl hyy'
  by_cases hex : ∃ W ∈ S, y' = W.isIrreducible.genericPoint
  · obtain ⟨W, hW, hgen⟩ := hex
    refine Or.inr ⟨W, hW, ?_⟩
    rw [← W.isIrreducible.closure_genericPoint W.isClosed', ← hgen]
    exact hyy'
  · push Not at hex
    exact (hy' (by rw [single_add_sum_smul_single_apply_of_forall_ne z y' S m hex,
      ite_eq_right hy'z])).elim

open scoped Classical in
/-- **The cone of Tag 0B0E, read on an open subvariety `Y` of `X̄`.** -/
theorem exists_cone_data (k : Type u) [Field k] [IsAlgClosed k] {Xb : Scheme.{u}} (N : ℕ)
    (iX : Xb ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k)) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))]
    {n r s : ℕ} (hn : topologicalKrullDim Xb = (n : WithBot ℕ∞)) (hs : s < n) (hr : r < n)
    {Y : Scheme.{u}} (j₀ : Y ⟶ Xb) [IsOpenImmersion j₀]
    (hU : Set.range j₀.base ⊆ regularLocus Xb)
    (z : Y) (hz : topologicalKrullDim (closure ({z} : Set Y)) = (s : WithBot ℕ∞))
    {κ : Type*} [Finite κ] (T : κ → IrreducibleCloseds Y)
    (hTd : ∀ i, topologicalKrullDim (T i : Set Y) = (r : WithBot ℕ∞)) :
    ∃ (C : IrreducibleCloseds (projectiveSpaceOfModule k (Fin (N + 1) → k)))
      (S : Finset (IrreducibleCloseds Y)) (mW : IrreducibleCloseds Y → ℤ),
      cycleComap j₀ j₀.isOpenEmbedding.injective
          (cycleComap iX iX.isClosedEmbedding.injective
            (torFormulaCycleIntersectionProduct (fieldChowSituation k)
              (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
              (isRegular_projectiveSpaceOfModule k _) (s : ℤ)
              (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint 1)
              (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) 1))) =
        Function.locallyFinsuppWithin.single z 1 +
          ∑ W ∈ S, mW W • Function.locallyFinsuppWithin.single W.isIrreducible.genericPoint 1 ∧
      AlgebraicCycle.IntersectProperly
          (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint (1 : ℤ))
          (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) (1 : ℤ)) ∧
      relativeDimension (fieldChowSituation k).dimensionFunction
          (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) C.isIrreducible.genericPoint +
            (n : ℤ) = (N : ℤ) + s ∧
      (∀ W ∈ S, topologicalKrullDim (W : Set Y) = (s : WithBot ℕ∞) ∧
        ∀ i, (topologicalKrullDim ↥((W : Set Y) ∩ (T i : Set Y)) ≤
              topologicalKrullDim ↥(closure ({z} : Set Y) ∩ (T i : Set Y)) ∨
            topologicalKrullDim ↥((W : Set Y) ∩ (T i : Set Y)) + (n : WithBot ℕ∞) ≤
              ((s + r : ℕ) : WithBot ℕ∞)) ∧
          (¬ (topologicalKrullDim ↥(closure ({z} : Set Y) ∩ (T i : Set Y)) + (n : WithBot ℕ∞) ≤
              ((s + r : ℕ) : WithBot ℕ∞)) →
            topologicalKrullDim ↥((W : Set Y) ∩ (T i : Set Y)) <
              topologicalKrullDim ↥(closure ({z} : Set Y) ∩ (T i : Set Y)))) ∧
      ∀ y : Y, iX.base (j₀.base y) ∈ (C : Set _) →
        y ∈ closure ({z} : Set Y) ∨ ∃ W ∈ S, y ∈ (W : Set Y) := by
  have hV : Module.finrank k (Fin (N + 1) → k) = N + 1 := Module.finrank_fin_fun k
  have : Nonempty Y := ⟨z⟩
  obtain ⟨XC, hXC, hXgen⟩ := exists_irreducibleCloseds_eq_range iX
  obtain ⟨C, S, m, hprop, hdisp, -, hZS, -, hdimW, hleW, hltW⟩ :=
    exists_intersectProperly_cycleComap_torFormulaCycleIntersectionProduct_eq k
      (Fin (N + 1) → k) hV iX hn hs j₀ hU (IrreducibleCloseds.closureSingleton z) hz T
      (d' := fun _ => r) (fun _ => hr) hTd XC hXC
  rw [hXgen] at hprop hdisp
  rw [AlgebraicCycle.genericPoint_closureSingleton] at hdisp
  set Pd := torFormulaCycleIntersectionProduct (fieldChowSituation k)
      (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k))
      (isRegular_projectiveSpaceOfModule k _) (s : ℤ)
      (Function.locallyFinsuppWithin.single C.isIrreducible.genericPoint 1)
      (Function.locallyFinsuppWithin.single (iX.base (genericPoint Xb)) 1)
  have hWne : ∀ W ∈ S, W.isIrreducible.genericPoint ≠ z := fun W hW h =>
    hZS (by rwa [← h, AlgebraicCycle.closureSingleton_genericPoint])
  have hdispAt : ∀ y : Y, Pd (iX.base (j₀.base y)) =
      (Function.locallyFinsuppWithin.single z (1 : ℤ) +
        ∑ W ∈ S, m W • Function.locallyFinsuppWithin.single W.isIrreducible.genericPoint 1 :
          AlgebraicCycle Y ℤ) y :=
    fun y => congrArg (fun c : AlgebraicCycle Y ℤ => c y) hdisp
  have hcoef : Pd (iX.base (j₀.base z)) ≠ 0 := by
    rw [hdispAt, single_add_sum_smul_single_apply_of_forall_ne z z S m
      fun W hW => (hWne W hW).symm]
    simp
  have hdP := topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  obtain ⟨hz₀, hz₀s⟩ := Stacks.Intersection.mem_inter_of_torFormula_single_single_ne_zero k
    (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) (isRegular_projectiveSpaceOfModule k _)
    hdP (s : ℤ) _ _ _ hcoef
  obtain ⟨hG1, hG2⟩ := add_eq_and_forall_exists_apply_ne_zero
    (projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) (isRegular_projectiveSpaceOfModule k _)
    (s : ℤ) hcoef hz₀ hz₀s (relativeDimension_add_le_of_intersectProperly k N hprop) N hdP.le
  refine ⟨C, S, m, hdisp, hprop,
    by linarith [hG1, relativeDimension_image_genericPoint k N iX hn,
      relativeDimension_genericPoint_projectiveSpaceOfModule k N],
    fun W hW => ⟨hdimW W hW, fun i => ⟨?_, ?_⟩⟩, ?_⟩
  · exact (hleW W hW i).imp_right fun h => by rwa [Nat.cast_add]
  · intro hnp
    refine hltW W hW i fun hip => hnp ?_
    rw [AlgebraicGeometry.intersectProperly_iff] at hip
    change topologicalKrullDim ↥(closure ({z} : Set Y) ∩ (T i : Set Y)) + topologicalKrullDim Y ≤
      topologicalKrullDim ↥(closure ({z} : Set Y)) + topologicalKrullDim ↥(T i : Set Y) at hip
    rwa [topologicalKrullDim_eq_of_isOpenImmersion k
      (iX ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k)) j₀, hn, hz, hTd i,
      ← Nat.cast_add] at hip
  · intro y hy
    obtain ⟨y', hyy', -, hPz'⟩ := exists_mem_closure_of_forall_mem_inter iX j₀ hG2
      (by rwa [C.isIrreducible.closure_genericPoint C.isClosed'])
    exact mem_closure_or_exists_mem_of_apply_ne_zero z S m hyy' (by rwa [hdispAt] at hPz')

end Stacks.Intersection.RationalEquivalenceProduct

end
