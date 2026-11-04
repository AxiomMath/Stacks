module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepFibre
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepRestrict
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepFamily
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles

/-!
# Tag 0B1V: an open subscheme of the ambient space in which `X` is closed

The degeneration lemma Tag 0B1M is stated for a closed immersion `X ⟶ P` of nonsingular varieties.
In the inductive step of Tag 0B1V the variety `X` is an open subscheme of a closed subvariety of
`𝐏^N`, hence a closed subscheme of an open subscheme `U` of `𝐏^N`. This file collects the facts
about `U`, about the family `U × ℙ¹ ⊆ 𝐏^N × ℙ¹` and about cycles needed to apply Tag 0B1M there.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

section Opens

variable (k : Type u) [Field k] {P : Scheme.{u}} (s : P ⟶ Spec (.of k))

/-- **A nonempty open subscheme of a variety is a variety.** -/
theorem isVariety_opens_ι [IsVariety k s] (U : P.Opens) [Nonempty U] : IsVariety k (U.ι ≫ s) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian P := ⟨⟩
  exact { }

/-- **A nonempty open subscheme of a variety has the dimension of the variety.** -/
theorem topologicalKrullDim_opens [IsVariety k s] (U : P.Opens) [Nonempty U] :
    topologicalKrullDim U = topologicalKrullDim P := by
  have h := ProjectiveSpaceOfModule.topologicalKrullDim_closure_image_of_isOpenImmersion k s U.ι
    isClosed_univ
    (IrreducibleSpace.isIrreducible_univ U)
  have hdense : closure (U.ι.base '' (Set.univ : Set U)) = Set.univ := by
    rw [Set.image_univ]
    obtain ⟨x⟩ := ‹Nonempty U›
    exact (U.ι.isOpenEmbedding.isOpen_range.dense ⟨_, Set.mem_range_self x⟩).closure_eq
  rw [hdense, topologicalKrullDim_univ, topologicalKrullDim_univ] at h
  exact h.symm

end Opens

/-- **An open immersion of irreducible schemes preserves generic points.** -/
theorem genericPoint_image_of_isOpenImmersion {Y X : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (j : Y ⟶ X) [IsOpenImmersion j] :
    j.base (genericPoint Y) = genericPoint X := by
  have h := (genericPoint_spec Y).image j.continuous
  rw [Set.image_univ] at h
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  rw [(j.isOpenEmbedding.isOpen_range.dense ⟨_, Set.mem_range_self y⟩).closure_eq] at h
  exact h.eq (genericPoint_spec X)

/-- **An open set meeting the closure of a point contains that point.** -/
theorem mem_of_isOpen_of_mem_closure {T : Type*} [TopologicalSpace T] {U : Set T} (hU : IsOpen U)
    {x y : T} (hy : y ∈ closure ({x} : Set T)) (hyU : y ∈ U) : x ∈ U := by
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hy U hU hyU
  rw [Set.mem_singleton_iff.mp hz] at hzU
  exact hzU

/-- **Proper intersection of prime cycles from proper intersection of their closures.** -/
theorem intersectProperly_single_single_of_closure {Y : Scheme.{u}} [DecidableEq Y] {a b : Y}
    (h : AlgebraicGeometry.IntersectProperly
      ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    AlgebraicCycle.IntersectProperly (Function.locallyFinsuppWithin.single a (1 : ℤ))
      (Function.locallyFinsuppWithin.single b (1 : ℤ)) := by
  have key : ∀ (c : Y) (W : IrreducibleCloseds Y),
      Function.locallyFinsuppWithin.single c (1 : ℤ) W.isIrreducible.genericPoint ≠ 0 →
        W = ⟨closure {c}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    intro c W hW
    have hWc : W.isIrreducible.genericPoint = c := by
      by_contra hne
      exact hW (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hne])
    ext1
    change (W : Set Y) = closure {c}
    rw [← hWc, W.isIrreducible.closure_genericPoint W.isClosed]
  intro W V hW hV
  rw [key a W hW, key b V hV]
  exact h

section CycleComap

variable {Y X Z : Scheme.{u}}

/-- The inverse image of a prime cycle at an image point is the prime cycle. -/
theorem cycleComap_single [DecidableEq X] [DecidableEq Y] (f : Y ⟶ X)
    (hf : Function.Injective f.base) (y : Y) :
    cycleComap f hf (Function.locallyFinsuppWithin.single (f.base y) (1 : ℤ)) =
      Function.locallyFinsuppWithin.single y 1 := by
  refine Function.locallyFinsuppWithin.ext fun w => ?_
  rw [cycleComap_apply, Function.locallyFinsuppWithin.single_apply,
    Function.locallyFinsuppWithin.single_apply]
  by_cases hw : w = y
  · subst hw; simp
  · rw [ite_eq_right hw, ite_eq_right (fun h => hw (hf h))]

/-- Inverse images of cycles compose. -/
theorem cycleComap_cycleComap (g : Z ⟶ Y) (hg : Function.Injective g.base) (f : Y ⟶ X)
    (hf : Function.Injective f.base) (h : Z ⟶ X) (hh : Function.Injective h.base)
    (hgf : g ≫ f = h) (c : AlgebraicCycle X ℤ) :
    cycleComap g hg (cycleComap f hf c) = cycleComap h hh c := by
  subst hgf
  exact Function.locallyFinsuppWithin.ext fun _ => rfl

/-- The inverse image along a closed immersion of a pushforward is the original cycle. -/
theorem cycleComap_properPushforward (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (i : Y ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ sX = sY) (k : ℤ) (a : CycleGroup C sY k) :
    cycleComap i i.isClosedEmbedding.injective (properPushforward C sY sX i hi k a).1 = a.1 :=
  Function.locallyFinsuppWithin.ext fun y =>
    properPushforward_apply_image_of_isClosedImmersion C sY sX i hi k a y

end CycleComap

section Family

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)

/-- The morphism of families induced by an open immersion is an open immersion. -/
instance isOpenImmersion_familyBaseChange [IsOpenImmersion i] :
    IsOpenImmersion (familyBaseChange f i) :=
  MorphismProperty.of_isPullback (isPullback_familyBaseChange f i) inferInstance

/-- The zero section is compatible with the morphism induced on families. -/
theorem zeroSection_comp_familyBaseChange :
    zeroSection (i ≫ f) ≫ familyBaseChange f i = i ≫ zeroSection f :=
  constantSection_comp_familyBaseChange f i integralZeroSection

/-- The infinity section is compatible with the morphism induced on families. -/
theorem infinitySection_comp_familyBaseChange :
    infinitySection (i ≫ f) ≫ familyBaseChange f i = i ≫ infinitySection f :=
  constantSection_comp_familyBaseChange f i integralInfinitySection

/-- The zero fibre of the inverse image of a family is the inverse image of its zero fibre. -/
theorem zeroFiber_comap_familyBaseChange (Z : (projectiveLineProduct f).IdealSheafData) :
    zeroFiber (i ≫ f) (Z.comap (familyBaseChange f i)) = (zeroFiber f Z).comap i := by
  rw [zeroFiber, zeroFiber, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    zeroSection_comp_familyBaseChange]

end Family

section ZeroSectionSum

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [IsVariety k p]

open scoped Classical in
/-- **A cycle meeting `X × 0` properly has no component inside `X × 0`.** -/
theorem not_range_subset_zeroSection_of_intersectProperly {n : ℕ}
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) (m : ℤ)
    (β : CycleGroup (fieldChowSituation k)
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) (m + 1))
    (hβ : AlgebraicCycle.IntersectProperly β.1
      (Function.locallyFinsuppWithin.single ((zeroSection p).base (genericPoint X)) 1))
    (e : projectiveLineProduct p) (he : β.1 e ≠ 0) :
    ¬ Set.range (integralComponentAt e).subschemeι.base ⊆ Set.range (zeroSection p).base := by
  intro hsub
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt] at hsub
  have h := hβ ⟨closure {e}, isIrreducible_singleton.closure, isClosed_closure⟩
    ⟨closure {(zeroSection p).base (genericPoint X)}, isIrreducible_singleton.closure,
      isClosed_closure⟩ (by rw [genericPoint_closure_singleton]; exact he)
    (by rw [genericPoint_closure_singleton]; simp)
  rw [AlgebraicGeometry.intersectProperly_iff] at h
  change topologicalKrullDim ↥(closure ({e} : Set (projectiveLineProduct p)) ∩
      closure {(zeroSection p).base (genericPoint X)}) +
      topologicalKrullDim (projectiveLineProduct p) ≤
    topologicalKrullDim ↥(closure ({e} : Set (projectiveLineProduct p))) +
      topologicalKrullDim ↥(closure {(zeroSection p).base (genericPoint X)}) at h
  rw [closure_zeroSection_genericPoint, Set.inter_eq_left.mpr hsub,
    topologicalKrullDim_projectiveLineProduct, ← Set.image_univ,
    topologicalKrullDim_image_zeroSection, topologicalKrullDim_univ, hn,
    topologicalKrullDim_closure_singleton_eq k
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p)] at h
  have h' : ((relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) e).toNat +
        (n + 1) : ℕ) ≤ ((relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) e).toNat + n :
        ℕ) := by
    exact_mod_cast h
  omega

open scoped Classical in
/-- **`pr_*(β · X × 0) = ∑ β(e) [E_{e,0}]`.** For a `(m + 1)`-cycle `β` on `X × ℙ¹` with no
component inside `X × 0`, the pushforward to `X` of `β · X × 0` is the combination of the cycles
of the zero fibres of the components of `β` (Tag 0B07). -/
theorem exists_properPushforward_product_zeroSection_eq_sum
    (hQ : IsRegular (projectiveLineProduct p)) (m : ℤ)
    (β : CycleGroup (fieldChowSituation k)
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) (m + 1))
    (h₀ : ∀ e, β.1 e ≠ 0 →
      ¬ Set.range (integralComponentAt e).subschemeι.base ⊆ Set.range (zeroSection p).base)
    (A : CycleGroup (fieldChowSituation k)
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) m)
    (hA :
      haveI : IsLocallyNoetherian (projectiveLineProduct p) := isLocallyNoetherian_of_isRegular hQ
      A.1 = torFormulaCycleIntersectionProduct (fieldChowSituation k)
        (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) hQ m β.1
        (Function.locallyFinsuppWithin.single ((zeroSection p).base (genericPoint X)) 1)) :
    ∃ S : Finset (projectiveLineProduct p),
      (properPushforward (fieldChowSituation k)
          (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) p
          (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) rfl m A).1 =
        ∑ e ∈ S, β.1 e • (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
          (zeroFiber p (integralComponentAt e)).subschemeι m).1 ∧
      ∀ e ∈ S, β.1 e ≠ 0 := by
  have : IsLocallyNoetherian (projectiveLineProduct p) := isLocallyNoetherian_of_isRegular hQ
  have : IsVariety k (p ≫ eqToHom (rfl : (fieldChowSituation k).S = Spec (.of k))) := by
    simpa using ‹IsVariety k p›
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct k (fieldChowSituation k) rfl p
  have hfin := finite_support_of_compactSpace β.1
  refine ⟨hfin.toFinset, ?_, fun e he => hfin.mem_toFinset.mp he⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le_of_isVariety p
  have hsupp : ∀ x ∈ hfin.toFinset, β.1 x ≠ 0 := fun x hx => hfin.mem_toFinset.mp hx
  have hdimpt : ∀ x ∈ hfin.toFinset, relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) x = m + 1 :=
    fun x hx => (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k)
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) (m + 1)
      β.1).1 β.2 x (hsupp x hx)
  have hdec : A = ∑ x ∈ hfin.toFinset.attach, β.1 x.1 •
      (⟨torFormulaSubvarietyProductTotal (fieldChowSituation k)
          (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) hQ m x.1
          ((zeroSection p) (genericPoint X)),
        torFormulaSubvarietyProductTotal_zeroSection_mem_cyclesOfDimension (fieldChowSituation k)
          p hQ m x.1 (hdimpt x.1 x.2) (h₀ x.1 (hsupp x.1 x.2))⟩ :
        CycleGroup (fieldChowSituation k)
          (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) m) := by
    refine Subtype.ext ?_
    rw [hA]
    refine (torFormulaCycleIntersectionProduct_zeroSection_eq_sum (fieldChowSituation k) p hQ m
      β.1 hfin).trans ?_
    rw [← Finset.sum_attach hfin.toFinset (fun x => β.1 x • torFormulaSubvarietyProductTotal
      (fieldChowSituation k)
      (pullback.fst p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ p) hQ m x
      ((zeroSection p) (genericPoint X)))]
    simp
  rw [hdec, ← properPushforwardHom_apply, map_sum, AddSubgroup.val_finsetSum,
    ← Finset.sum_attach hfin.toFinset (fun e => β.1 e • (cycleAssociatedToClosedSubscheme
      (fieldChowSituation k) p (zeroFiber p (integralComponentAt e)).subschemeι m).1)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_zsmul, AddSubgroup.coe_zsmul, properPushforwardHom_apply,
    properPushforward_eq_zeroFiberCycle_of_coe_eq (fieldChowSituation k) p hQ m d x.1 hd
      (hdimpt x.1 x.2) (h₀ x.1 (hsupp x.1 x.2)) _ rfl]

end ZeroSectionSum

end Stacks.Intersection.RationalEquivalenceProduct

end
