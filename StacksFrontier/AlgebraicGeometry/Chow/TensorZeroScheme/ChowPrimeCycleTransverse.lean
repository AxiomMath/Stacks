module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowDevissage

/-!
# Tag 0F98, the case `W ⊄ D`

[Stacks, Tag 0F98] closes its second case in one sentence: for an integral closed subscheme
`W ⊆ Y` of delta-dimension `k+1` not contained in the divisor `D = Z(s)`, "both `i₁^*p^*[W]` and
`p₁^*i^*[W]` are represented by the cycle associated to the scheme theoretic inverse image of `W`
in `D₁`". This file proves that, and in the strong form: the two cycles are *equal*, not merely
rationally equivalent.

On the left `p^*[W] = [p^{-1}W]` and then `i₁^*[p^{-1}W] = [p^{-1}W ∩ D₁]`; on the right
`i^*[W] = [W ∩ D]` and then `p₁^*[W ∩ D] = [p₁^{-1}(W ∩ D)]`. The square `i₁ ≫ p = p₁ ≫ i` of
[Stacks, Tag 0F97] identifies both with the fundamental cycle of `W.comap (i₁ ≫ p)`.

The condition `W ⊄ D` enters as two transversality hypotheses: `D ∩ W` is an effective Cartier
divisor on `W`, and `D₁ ∩ p^{-1}W` is an effective Cartier divisor on `p^{-1}W`.

## Main results

* `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le`: the flat pullback of
  the fundamental cycle of a closed subscheme is the fundamental cycle of its scheme-theoretic
  inverse image, at an arbitrary degree and an arbitrary base compatibility.
* `Stacks.Chow.gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme_of_section`: the
  Gysin cycle of a closed subscheme meeting a Cartier zero scheme properly is the fundamental cycle
  of the intersection, for the zero scheme of a global section.
* `Stacks.Chow.schemeDeltaDimension_comap_comm`: the delta-dimension of a scheme-theoretic
  intersection of two closed subschemes does not depend on which of the two it is read inside.
* `Stacks.Chow.TensorZeroScheme.leftRule_cycle_eq_rightRule_cycle_of_cartier`: **the case
  `W ⊄ D` of [Stacks, Tag 0F98]**: the two cycles are equal.

## References

* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Flat pullback of a fundamental cycle, in the `comap` presentation -/

/-- **The flat pullback of the fundamental cycle of a closed subscheme is the fundamental cycle of
its scheme-theoretic inverse image.** This is Stacks 02RE part (1), with the inverse image in
its `comap` presentation, at an arbitrary degree and an arbitrary base compatibility. -/
theorem flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (q : X' ⟶ X) [LocallyOfFiniteType q] [Flat q]
    (hbase : q ≫ sX = sX') (r : ℕ) (hq : AlgebraicGeometry.RelativeDimension q r)
    (I : X.IdealSheafData) (d : ℤ)
    (hI : schemeDeltaDimension C (I.subschemeι ≫ sX) ≤ (d : EInt)) :
    flatPullback C sX' sX q hbase r hq d
        (cycleAssociatedToClosedSubscheme C sX I.subschemeι d) =
      cycleAssociatedToClosedSubscheme C sX' (I.comap q).subschemeι (d + (r : ℤ)) := by
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun x' ↦ ?_
  rw [flatPullback_apply]
  exact (closedSubschemeCycleCoeff_comap C sX' sX q hbase r hq I d hI x').symm

/-! ### The Gysin cycle of a proper intersection, for a global section -/

/-- **Intersecting a closed subscheme properly with a Cartier zero scheme computes its Gysin
cycle**, for a global section `σ` of the invertible module and an element `t` of its sections
object whose value over `⊤` is `σ`. -/
theorem gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme_of_eval
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (t : L.sections) (σ : Γ(L, ⊤)) (hσ : t.eval (.op ⊤) = σ) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L σ).comap Z.subschemeι)) :
    (gysinRule C p k L σ (firstChernComponentClass C p k L)).extendCycleGroup
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C
        ((Stacks.Divisors.zeroScheme X L σ).subschemeι ≫ p)
        ((Z.comap (Stacks.Divisors.zeroScheme X L σ).subschemeι).subschemeι) k := by
  subst hσ
  exact gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme C p k L t Z hZ hDZ

/-- **Intersecting a closed subscheme properly with a Cartier zero scheme computes its Gysin
cycle**, for a global section of the invertible module. -/
theorem gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme_of_section
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L σ).comap Z.subschemeι)) :
    (gysinRule C p k L σ (firstChernComponentClass C p k L)).extendCycleGroup
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C
        ((Stacks.Divisors.zeroScheme X L σ).subschemeι ≫ p)
        ((Z.comap (Stacks.Divisors.zeroScheme X L σ).subschemeι).subschemeι) k :=
  gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme_of_eval C p k L
    (Stacks.Divisors.sectionsOfTop L σ) σ (Stacks.Divisors.sectionsOfTop_eval_top L σ) Z hZ hDZ

/-! ### The two orders of a scheme-theoretic intersection -/

/-- The image in the ambient scheme of the scheme-theoretic inverse image of a closed subscheme
along a morphism is the intersection of the image of that morphism with the support. -/
theorem range_comap_subschemeι_comp_eq_inter {A B : Scheme.{u}} (f : A ⟶ B)
    (I : B.IdealSheafData) :
    Set.range ((I.comap f).subschemeι ≫ f) = Set.range f ∩ (I.support : Set B) := by
  show Set.range (f ∘ (I.comap f).subschemeι) = _
  rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.support_comap]
  exact Set.image_preimage_eq_range_inter

/-- **The delta-dimension of a scheme-theoretic intersection of two closed subschemes does not
depend on which of the two it is read inside.** -/
theorem schemeDeltaDimension_comap_comm (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (I J : X.IdealSheafData) :
    schemeDeltaDimension C ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι ≫ p) =
      schemeDeltaDimension C ((I.comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ p) := by
  have hrange : Set.range ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι) =
      Set.range ((I.comap J.subschemeι).subschemeι ≫ J.subschemeι) := by
    rw [range_comap_subschemeι_comp_eq_inter, range_comap_subschemeι_comp_eq_inter,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.range_subschemeι]
    exact Set.inter_comm _ _
  have h := schemeDeltaDimension_eq_of_equal_ranges C p
    ((J.comap I.subschemeι).subschemeι ≫ I.subschemeι)
    ((I.comap J.subschemeι).subschemeι ≫ J.subschemeι) hrange
  exact (schemeDeltaDimension_congr C (Category.assoc _ I.subschemeι p).symm).trans
    (h.trans (schemeDeltaDimension_congr C (Category.assoc _ J.subschemeι p)))

end Stacks.Chow

namespace Stacks.Chow.TensorZeroScheme

variable (C : Stacks.Chow.ChowSituation.{u}) (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (k : ℤ)

include h₁ h₂ in
/-- **The case `W ⊄ D` of [Stacks, Tag 0F98].** For an integral closed subscheme `W ⊆ Y` of
delta-dimension `k+1` meeting the divisor `D = Z(s)` properly — in the sense that `D ∩ W` is an
effective Cartier divisor on `W` and `D₁ ∩ p^{-1}W` is one on `p^{-1}W` — the two cycles
`i₁^*p^*[W]` and `p₁^*i^*[W]` are **equal**, both being the fundamental cycle of the
scheme-theoretic inverse image of `W` in `D₁`. -/
theorem leftRule_cycle_eq_rightRule_cycle_of_cartier
    (W : Y.IdealSheafData) (hWint : IsIntegral W.subscheme)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor
      ((zeroIdeal Y L₁ L₂ s).comap W.subschemeι))
    (hD₁ : Stacks.Divisors.IsEffectiveCartierDivisor
      (R.normalize.D₁.comap (W.comap R.normalize.p).subschemeι)) :
    (leftRule C Y L₁ L₂ s R sY k).cycle W hWint hDim =
      (rightRule C Y L₁ L₂ s R sY k).cycle W hWint hDim := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible
      R.normalize.total.sheaf.obj
      R.normalize.total.ringCatSheaf.property
      ((Scheme.Modules.pullback R.normalize.p).obj L₁) :=
    Stacks.Divisors.pullback_isInvertible _ _
  have hWle : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) ≤ ((k + 1 : ℤ) : EInt) :=
    le_of_eq hDim
  have hpWle : Stacks.Chow.schemeDeltaDimension C
      ((W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) ≤
      ((k + 1 + 1 : ℤ) : EInt) :=
    Stacks.Chow.schemeDeltaDimension_comap_le_of_relativeDimension C
      (R.normalize.p ≫ sY) sY R.normalize.p rfl 1
      R.normalize.p_relativeDimension W (k + 1) hWle
  have hWD : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) ≤ (k : EInt) := by
    rw [← Stacks.Chow.schemeDeltaDimension_comap_comm C sY W (zeroIdeal Y L₁ L₂ s)]
    refine le_trans (Stacks.Chow.schemeDeltaDimension_isEffectiveCartierDivisor_le C
      (W.subschemeι ≫ sY) ((zeroIdeal Y L₁ L₂ s).comap W.subschemeι) hD) ?_
    rw [hDim, ← Stacks.Chow.coe_add_coe_eq_coe_add, show k + 1 + (-1 : ℤ) = k by lia]
  have hleft : (leftRule C Y L₁ L₂ s R sY k).cycle W hWint hDim =
      Stacks.Chow.cycleAssociatedToClosedSubscheme C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        (((W.comap R.normalize.p).comap R.normalize.D₁.subschemeι).subschemeι)
        (k + 1) := by
    show (gysinRuleBranch₁ C Y L₁ L₂ s R sY k).extendCycleGroup
        (Stacks.Chow.flatPullback C (R.normalize.p ≫ sY) sY R.normalize.p rfl 1
          R.normalize.p_relativeDimension (k + 1) _) = _
    rw [Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le C
      (R.normalize.p ≫ sY) sY R.normalize.p rfl 1 R.normalize.p_relativeDimension
      W (k + 1) hWle]
    exact Stacks.Chow.gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme_of_section C
      (R.normalize.p ≫ sY) (k + 1) ((Scheme.Modules.pullback R.normalize.p).obj L₁)
      R.normalize.s₁ (W.comap R.normalize.p) hpWle hD₁
  have hright : (rightRule C Y L₁ L₂ s R sY k).cycle W hWint hDim =
      Stacks.Chow.cycleAssociatedToClosedSubscheme C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        (((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁).subschemeι)
        (k + ((1 : ℕ) : ℤ)) := by
    show Stacks.Chow.flatPullback C (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
        (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
        ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
        ((gysinRuleZeroIdeal C Y L₁ L₂ s sY k).extendCycleGroup _) = _
    have hgys : (gysinRuleZeroIdeal C Y L₁ L₂ s sY k).extendCycleGroup
          (Stacks.Chow.cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)) =
        Stacks.Chow.cycleAssociatedToClosedSubscheme C
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
          ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι) k :=
      Stacks.Chow.gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme_of_section C
        sY k (Stacks.Divisors.tensorModules L₁ L₂) s W hWle hD
    rw [hgys]
    exact Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
      (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
      ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize))
      (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) k hWD
  have hideal : (W.comap R.normalize.p).comap R.normalize.D₁.subschemeι =
      (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁ := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      R.normalize.comm₁]
  rw [hleft, hright]
  exact congrArg (fun J : R.normalize.D₁.subscheme.IdealSheafData ↦
    Stacks.Chow.cycleAssociatedToClosedSubscheme C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) J.subschemeι (k + 1)) hideal

end Stacks.Chow.TensorZeroScheme

end
