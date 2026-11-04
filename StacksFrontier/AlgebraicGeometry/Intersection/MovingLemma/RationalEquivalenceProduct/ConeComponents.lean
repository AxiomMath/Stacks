module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Positivity
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.StalkDimensions
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaDeficient
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectionDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePointsBertini
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Every component of a proper intersection occurs in the intersection product

Let `P` be a nonsingular variety over an algebraically closed field and `V = closure {x}`,
`W = closure {y}` two closed subvarieties intersecting properly. If the intersection product
`V · W`, formed in the delta-dimension `s`, is nonzero at some point `z₀` of relative dimension
`s`, then every point of `V ∩ W` has relative dimension at most `s`, and at every point `z` of
`V ∩ W` of relative dimension `s` the product is nonzero. The second clause is the positivity of
intersection multiplicities, Tag 0B0V; the first follows from it, since at a point of
`V ∩ W` of largest relative dimension the multiplicity is positive, so some `Tor` sheaf is
supported there, and the `Tor` sheaves are supported in relative dimension at most `s` as soon as
the product is not the zero cycle.

These are the facts the proof of Tag 0B1V uses about the cone `C` of Tag 0B0E: the components of
`C ∩ X` are exactly the subvarieties occurring in `C · X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable {k : Type u} [Field k] [IsAlgClosed k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
  [IsVariety k sP] [IsLocallyNoetherian P] (hP : IsRegular P)

variable [DecidableEq P]

/-- The product of two prime cycles is the total Tor-formula product of the subvarieties. -/
private theorem torFormulaCycleIntersectionProduct_single_single {k : Type u} [Field k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [IsVariety k sP] [IsLocallyNoetherian P]
    (hP : IsRegular P) [DecidableEq P] (s : ℤ) (x y : P) :
    torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP s
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) =
      torFormulaSubvarietyProductTotal (fieldChowSituation k) sP hP s x y := by
  refine (cycleIntersectionProduct_single_single
    (torFormulaSubvarietyProductTotal (fieldChowSituation k) sP hP s) x y 1 1).trans ?_
  rw [one_mul, one_smul]

omit [IsAlgClosed k] in
/-- If the product of two prime cycles is nonzero somewhere, the `Tor` sheaves satisfy the
support bound in that delta-dimension. -/
theorem torSupportBound_of_apply_ne_zero (s : ℤ) {x y z₀ : P}
    (hcoef : torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP s
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) z₀ ≠ 0) :
    TorSupportBound (fieldChowSituation k) sP hP s x y := by
  refine Classical.byContradiction fun hb => hcoef ?_
  rw [torFormulaCycleIntersectionProduct_single_single sP hP s x y,
    torFormulaSubvarietyProductTotal_eq_zero (fieldChowSituation k) sP hP s hb,
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]

omit [IsAlgClosed k] [DecidableEq ↥P] in
/-- Under the support bound, every point of the support of a `Tor` sheaf has relative dimension
at most `s`. -/
theorem relativeDimension_le_of_mem_supp_torSheaf (s : ℤ) {x y : P}
    (hb : TorSupportBound (fieldChowSituation k) sP hP s x y) (i : ℕ) {w : P}
    (hw : w ∈ SheafOfModules.supp (torSheaf P (structureSheafAt x) (structureSheafAt y) i)) :
    relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤ s := by
  have := isCoherent_torSheaf_of_isRegular P hP (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
  have hmem : w ∈ Set.range (reducedSupport
      (torSheaf P (structureSheafAt x) (structureSheafAt y) i)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]
    exact hw
  obtain ⟨v, rfl⟩ := hmem
  exact relativeDimension_le_of_schemeDeltaDimension_le (fieldChowSituation k) sP _ (hb i) v

omit [IsLocallyNoetherian P] [DecidableEq ↥P] in
/-- A nonzero Tor-formula multiplicity at `w` puts `w` in the support of some `Tor` sheaf. -/
theorem exists_mem_supp_torSheaf_of_localIntersectionMultiplicity_ne_zero {x y w : P}
    (hwx : w ∈ closure ({x} : Set P)) (hwy : w ∈ closure ({y} : Set P))
    (he : (localIdealAt x w).localIntersectionMultiplicity
      (P.presheaf.stalk w ⧸ localIdealAt y w) ≠ 0) :
    ∃ i : ℕ, w ∈ SheafOfModules.supp (torSheaf P (structureSheafAt x) (structureSheafAt y) i) := by
  by_contra hno
  push Not at hno
  apply he
  rw [Ideal.localIntersectionMultiplicity]
  refine (tsum_congr fun i => ?_).trans tsum_zero
  have h := sheafMultiplicity_torSheaf_structureSheafAt x y i hwx hwy
  rw [sheafMultiplicity_eq_zero_of_notMem_supp _ (hno i)] at h
  have h' : (Module.length (P.presheaf.stalk w)
      (((Tor (ModuleCat.{u} (P.presheaf.stalk w)) i).obj
        (ModuleCat.of (P.presheaf.stalk w) (P.presheaf.stalk w ⧸ localIdealAt x w))).obj
        (ModuleCat.of (P.presheaf.stalk w)
          (P.presheaf.stalk w ⧸ localIdealAt y w)))).toNat = 0 := by
    exact_mod_cast h.symm
  rw [h']
  simp

variable [IrreducibleSpace P]

omit [IsLocallyNoetherian P] [DecidableEq ↥P] in
/-- The positivity at a point of `closure {x} ∩ closure {y}` where the relative dimension is
largest, under the numerical proper-intersection inequality. -/
theorem localIntersectionMultiplicity_pos_of_isMax (hP : IsRegular P) {x y z : P}
    (hzx : z ∈ closure ({x} : Set P)) (hzy : z ∈ closure ({y} : Set P))
    (hmax : ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
      relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP z)
    (hprop : relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P) +
          relativeDimension (fieldChowSituation k).dimensionFunction sP z ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP x +
          relativeDimension (fieldChowSituation k).dimensionFunction sP y) :
    0 < (localIdealAt x z).localIntersectionMultiplicity
      (P.presheaf.stalk z ⧸ localIdealAt y z) := by
  refine localIntersectionMultiplicity_localIdealAt_pos sP hP hzx hzy ?_ ?_
  · have h := Stacks.Intersection.ReductionToDiagonal.ringKrullDim_quotient_stalk_sup_eq_zero
      (fieldChowSituation k) sP
      (integralComponentAt x) (integralComponentAt y)
      (n := relativeDimension (fieldChowSituation k).dimensionFunction sP z) (z := z) ?_ rfl ?_
    · rwa [AlgebraicGeometry.IdealSheafData.stalk_sup] at h
    · rw [Scheme.IdealSheafData.support_sup]
      exact ⟨by rw [coe_support_integralComponentAt]; exact hzx,
        by rw [coe_support_integralComponentAt]; exact hzy⟩
    · intro w hw
      rw [Scheme.IdealSheafData.support_sup] at hw
      refine hmax w ⟨?_, ?_⟩
      · have := hw.1; rwa [coe_support_integralComponentAt] at this
      · have := hw.2; rwa [coe_support_integralComponentAt] at this
  · exact ringKrullDim_stalk_le_add_ringKrullDim_quotient_localIdealAt k sP hzx hzy hprop

/-- **The relative dimension on a proper intersection whose product is nonzero.** If `V · W` is
nonzero at some point in delta-dimension `s`, then every point of `V ∩ W` has relative dimension at
most `s`. -/
theorem relativeDimension_le_of_apply_ne_zero (s : ℤ) {x y z₀ : P}
    (hcoef : torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP s
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) z₀ ≠ 0)
    (hprop : ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
      relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P) +
          relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP x +
          relativeDimension (fieldChowSituation k).dimensionFunction sP y) :
    ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
      relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤ s := by
  have hb := torSupportBound_of_apply_ne_zero sP hP s hcoef
  -- the relative dimension on the intersection is bounded by that at `x`
  have hbdd : ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
      relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP x := by
    intro w hw
    obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
      (fieldChowSituation k).isUniversallyCatenary (fieldChowSituation k).dimensionFunction sP
    rcases eq_or_ne w x with heq | hne
    · rw [heq]
    · have hlt := d.strictAnti_specializes
        (by simpa [specializes_iff_mem_closure] using hw.1) (Ne.symm hne)
      rw [hd w, hd x] at hlt
      omega
  intro w₀ hw₀
  -- a point of largest relative dimension on the intersection
  obtain ⟨m, ⟨z, hz, rfl⟩, hm⟩ : ∃ m ∈ (relativeDimension (fieldChowSituation k).dimensionFunction
        sP '' (closure ({x} : Set P) ∩ closure ({y} : Set P))),
      ∀ m' ∈ (relativeDimension (fieldChowSituation k).dimensionFunction sP ''
        (closure ({x} : Set P) ∩ closure ({y} : Set P))), m' ≤ m := by
    refine ⟨_, Int.csSup_mem ⟨_, ⟨w₀, hw₀, rfl⟩⟩
      ⟨relativeDimension (fieldChowSituation k).dimensionFunction sP x, ?_⟩,
      fun m' hm' =>
        le_csSup ⟨relativeDimension (fieldChowSituation k).dimensionFunction sP x, ?_⟩ hm'⟩
    · rintro _ ⟨w, hw, rfl⟩; exact hbdd w hw
    · rintro _ ⟨w, hw, rfl⟩; exact hbdd w hw
  have hmax : ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
      relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP z :=
    fun w hw => hm _ ⟨w, hw, rfl⟩
  have hpos := localIntersectionMultiplicity_pos_of_isMax sP hP hz.1 hz.2 hmax (hprop z hz)
  obtain ⟨i, hi⟩ := exists_mem_supp_torSheaf_of_localIntersectionMultiplicity_ne_zero hz.1 hz.2
    hpos.ne'
  exact (hmax w₀ hw₀).trans (relativeDimension_le_of_mem_supp_torSheaf sP hP s hb i hi)

/-- **Every point of relative dimension `s` of a proper intersection occurs in the product.** If
`V · W` is nonzero at some point in delta-dimension `s`, then it is nonzero at every point of
`V ∩ W` of relative dimension `s`. -/
theorem apply_ne_zero_of_relativeDimension_eq (s : ℤ) {x y z₀ : P}
    (hcoef : torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP s
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) z₀ ≠ 0)
    (hprop : ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
      relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P) +
          relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP x +
          relativeDimension (fieldChowSituation k).dimensionFunction sP y)
    {z : P} (hz : z ∈ closure ({x} : Set P) ∩ closure ({y} : Set P))
    (hzs : relativeDimension (fieldChowSituation k).dimensionFunction sP z = s)
    (d : ℕ) (hd : topologicalKrullDim P ≤ (d : WithBot ℕ∞)) :
    torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP s
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) z ≠ 0 := by
  have hb := torSupportBound_of_apply_ne_zero sP hP s hcoef
  have hle := relativeDimension_le_of_apply_ne_zero sP hP s hcoef hprop
  have hpos := localIntersectionMultiplicity_pos_of_isMax sP hP hz.1 hz.2
    (fun w hw => (hle w hw).trans hzs.ge) (hprop z hz)
  have hlink := torSubvarietyProductOfBound_apply_eq_localIntersectionMultiplicity
    (fieldChowSituation k) sP hP s hb d hd hzs hz.1 hz.2
  rw [torFormulaCycleIntersectionProduct_single_single sP hP s x y,
    torFormulaSubvarietyProductTotal_eq_of_bound (fieldChowSituation k) sP hP s hb]
  intro h0
  refine hpos.ne' (hlink.symm.trans ?_)
  rw [h0, Int.cast_zero]

omit [IsAlgClosed k] [IsLocallyNoetherian P] [DecidableEq ↥P] [IrreducibleSpace ↥P] in
/-- The dimension of the closure of a point, as the natural number its relative dimension is. -/
theorem topologicalKrullDim_closure_eq (w : P) :
    topologicalKrullDim ↥(closure ({w} : Set P)) =
      (((relativeDimension (fieldChowSituation k).dimensionFunction sP w).toNat : ℕ) :
        WithBot ℕ∞) :=
  topologicalKrullDim_closure_eq_toNat_relativeDimension k sP w

omit [IsLocallyNoetherian P] [DecidableEq ↥P] in
/-- **Tag 0AZP at a point of the intersection.** Every point `w` of `closure {x} ∩ closure {y}`
specializes from a point `z` of the intersection with
`rd x + rd y ≤ rd η + rd z`, `η` the generic point of `P`: take `z` the generic point of an
irreducible component of the intersection containing `w`. -/
theorem exists_mem_inter_add_le (hP : IsRegular P) {x y w : P}
    (hw : w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P)) :
    ∃ z ∈ closure ({x} : Set P) ∩ closure ({y} : Set P), w ∈ closure ({z} : Set P) ∧
      relativeDimension (fieldChowSituation k).dimensionFunction sP x +
          relativeDimension (fieldChowSituation k).dimensionFunction sP y ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P) +
          relativeDimension (fieldChowSituation k).dimensionFunction sP z := by
  set I := integralComponentAt x with hI
  set J := integralComponentAt y with hJ
  have := isIntegral_integralComponentAt x
  have := isIntegral_integralComponentAt y
  have hF : ((I.support : Set P) ∩ (J.support : Set P)) =
      closure ({x} : Set P) ∩ closure ({y} : Set P) := by
    rw [hI, hJ, coe_support_integralComponentAt, coe_support_integralComponentAt]
  have hw' : w ∈ ((I.support : Set P) ∩ (J.support : Set P)) := hF ▸ hw
  obtain ⟨c, hc, hwc⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({(⟨w, hw'⟩ : ↥((I.support : Set P) ∩ (J.support : Set P)))} : Set _))
    isIrreducible_singleton.closure
  have hcl : IsClosed (Subtype.val '' c : Set P) :=
    (IsClosed.isClosedMap_subtype_val ((I.support.isClosed).inter J.support.isClosed)) c
      (isClosed_of_mem_irreducibleComponents c hc)
  have hirr : IsIrreducible (Subtype.val '' c : Set P) :=
    hc.1.image _ continuous_subtype_val.continuousOn
  set z := hirr.genericPoint with hzdef
  have hzD : closure ({z} : Set P) = Subtype.val '' c := hirr.closure_genericPoint hcl
  have hzF : z ∈ closure ({x} : Set P) ∩ closure ({y} : Set P) := by
    have : z ∈ (Subtype.val '' c : Set P) := hzD ▸ subset_closure rfl
    obtain ⟨⟨z', hz'⟩, -, rfl⟩ := this
    exact hF ▸ hz'
  refine ⟨z, hzF, ?_, ?_⟩
  · rw [hzD]
    exact ⟨⟨w, hw'⟩, hwc (subset_closure rfl), rfl⟩
  · have h0AZP :=
      Stacks.Intersection.add_topologicalKrullDim_le_add_topologicalKrullDim_of_irreducibleComponent
        sP hP I J c hc
    have hdc : topologicalKrullDim ↥c = topologicalKrullDim ↥(closure ({z} : Set P)) := by
      rw [hzD]
      exact (topologicalKrullDim_image_eq_of_isEmbedding Topology.IsEmbedding.subtypeVal c).symm
    have e : ∀ a : P, topologicalKrullDim (integralComponentAt a).subscheme =
        (((relativeDimension (fieldChowSituation k).dimensionFunction sP a).toNat : ℕ) :
          WithBot ℕ∞) := fun a => by
      rw [← topologicalKrullDim_support_eq, coe_support_integralComponentAt,
        topologicalKrullDim_closure_eq sP]
    have e3 : topologicalKrullDim ↥c =
        (((relativeDimension (fieldChowSituation k).dimensionFunction sP z).toNat : ℕ) :
          WithBot ℕ∞) := by
      rw [hdc, topologicalKrullDim_closure_eq sP]
    have e4 : topologicalKrullDim P =
        (((relativeDimension (fieldChowSituation k).dimensionFunction sP
          (genericPoint P)).toNat : ℕ) : WithBot ℕ∞) := by
      rw [← topologicalKrullDim_univ, ← genericPoint_closure P, topologicalKrullDim_closure_eq sP]
    rw [e x, e y, e3, e4] at h0AZP
    have h' : ((relativeDimension (fieldChowSituation k).dimensionFunction sP x).toNat +
        (relativeDimension (fieldChowSituation k).dimensionFunction sP y).toNat : ℕ) ≤
        (relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P)).toNat +
        (relativeDimension (fieldChowSituation k).dimensionFunction sP z).toNat := by
      exact_mod_cast h0AZP
    have := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k sP x
    have := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k sP y
    have := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k sP z
    have := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k sP (genericPoint P)
    omega

/-- **The dimension count and the components of a proper intersection with nonzero product.**
If `V · W`, formed in delta-dimension `s`, is nonzero at a point `z₀` of `V ∩ W` of relative
dimension `s`, and `V`, `W` intersect properly, then `dim P + s = dim V + dim W`, and every point
of `V ∩ W` lies in the closure of a point of `V ∩ W` of relative dimension `s` at which the product
is nonzero. -/
theorem add_eq_and_forall_exists_apply_ne_zero (s : ℤ) {x y z₀ : P}
    (hcoef : torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP s
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) z₀ ≠ 0)
    (hz₀ : z₀ ∈ closure ({x} : Set P) ∩ closure ({y} : Set P))
    (hz₀s : relativeDimension (fieldChowSituation k).dimensionFunction sP z₀ = s)
    (hprop : ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
      relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P) +
          relativeDimension (fieldChowSituation k).dimensionFunction sP w ≤
        relativeDimension (fieldChowSituation k).dimensionFunction sP x +
          relativeDimension (fieldChowSituation k).dimensionFunction sP y)
    (d : ℕ) (hd : topologicalKrullDim P ≤ (d : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P) + s =
        relativeDimension (fieldChowSituation k).dimensionFunction sP x +
          relativeDimension (fieldChowSituation k).dimensionFunction sP y ∧
      ∀ w ∈ closure ({x} : Set P) ∩ closure ({y} : Set P),
        ∃ z ∈ closure ({x} : Set P) ∩ closure ({y} : Set P), w ∈ closure ({z} : Set P) ∧
          relativeDimension (fieldChowSituation k).dimensionFunction sP z = s ∧
          torFormulaCycleIntersectionProduct (fieldChowSituation k) sP hP s
            (Function.locallyFinsuppWithin.single x (1 : ℤ))
            (Function.locallyFinsuppWithin.single y (1 : ℤ)) z ≠ 0 := by
  have hle := relativeDimension_le_of_apply_ne_zero sP hP s hcoef hprop
  have hG1 : relativeDimension (fieldChowSituation k).dimensionFunction sP (genericPoint P) + s =
      relativeDimension (fieldChowSituation k).dimensionFunction sP x +
        relativeDimension (fieldChowSituation k).dimensionFunction sP y := by
    obtain ⟨z, hz, -, hzle⟩ := exists_mem_inter_add_le sP hP hz₀
    have h1 := hprop z₀ hz₀
    have h2 := hle z hz
    omega
  refine ⟨hG1, fun w hw => ?_⟩
  obtain ⟨z, hz, hwz, hzle⟩ := exists_mem_inter_add_le sP hP hw
  have hzs : relativeDimension (fieldChowSituation k).dimensionFunction sP z = s := by
    have := hle z hz
    omega
  exact ⟨z, hz, hwz, hzs,
    apply_ne_zero_of_relativeDimension_eq sP hP s hcoef hprop hz hzs d hd⟩

end Stacks.Intersection.RationalEquivalenceProduct

end
