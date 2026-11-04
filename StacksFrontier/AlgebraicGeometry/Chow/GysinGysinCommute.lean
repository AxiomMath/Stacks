module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinGysinSituation
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionDescentCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.CarrierAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.CompositeComponentRule
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentClassModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# Two Gysin maps commute, reduced to integral components

Let `(L, s)` and `(L', s')` be two invertible modules with global sections on a scheme `X`, with
zero schemes `i : D → X` and `i' : D' → X`. Restricting `(L', s')` to `D` presents the
intersection `D ∩ D'` as the zero scheme of a section of an invertible module on `D`, and
restricting `(L, s)` to `D'` presents it as the zero scheme of a section of an invertible module
on `D'`. By Stacks 0B6Y both are the scheme-theoretic intersection `D ⊔ D'`, so the two
presentations are isomorphic over `X`.

Stacks 0B73 asserts that the two iterated Gysin maps `A_{k+2}(X) → A_k(D ∩ D')` agree under that
identification. This file shows that they agree as soon as, for every integral closed subscheme
`W ⊆ X` of delta-dimension `k + 2`, the two iterated Gysin cycles of `W` differ by a cycle
rationally equivalent to zero, witnessed over `W`.

## Main definitions

* `Stacks.Chow.zeroSchemeRestrictModule`, `Stacks.Chow.restrictSectionToZeroScheme` — the
  restriction of an invertible module and of one of its global sections to the zero scheme of
  another pair.
* `Stacks.Chow.zeroSchemeInter` — the intersection of the two zero schemes, presented inside the
  first one.
* `Stacks.Chow.gysinGysinComponentCycle` — the iterated Gysin cycle of an integral component.
* `Stacks.Chow.GysinGysinCommutesOnComponents` — the per-component statement of Stacks 0B73.

## Main results

* `Stacks.Chow.exists_iso_zeroSchemeInter` — the two presentations of the intersection are
  isomorphic over the ambient scheme.
* `Stacks.Chow.rationallyEquivalent_properPushforward_extendCycleGroup_comp_of_components` — two
  towers of rules on integral components that agree on integral components agree on every cycle,
  modulo rational equivalence.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_cyclePullback` — the
  Gysin component cycle of an integral component is, inside the zero scheme, rationally
  equivalent to the inverse image of the divisor cycle of a prescribed generator.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub` — the same after
  the outer Gysin map has been applied, its carrier retained.
* `Stacks.Chow.range_zeroSchemeInter_subschemeι_comp` — the image of the intersection in the
  ambient scheme is the intersection of the two supports.
* `Stacks.Chow.gysinGysinCommutesOnComponents_of_properPushforward` — the per-component statement
  reduced to a comparison of cycles on the ambient scheme.
* `Stacks.Chow.gysinChowOfInvertible_comm_of_components` — Stacks 0B73, granted its
  per-component statement.

## References

* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
instance isInvertible_modulePullback_obj {X X' : Scheme.{u}} (f : X' ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  isInvertible_presheaf_modulePullback L f

section Setup

variable {X : Scheme.{u}} (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤))

/-- The restriction of the invertible module `L'` to the zero scheme of a section `s` of `L`. -/
abbrev zeroSchemeRestrictModule : (Stacks.Divisors.zeroScheme X L s).subscheme.Modules :=
  (Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L'

/-- The restriction of a global section `s'` of `L'` to the zero scheme of a section `s` of
`L`. -/
abbrev restrictSectionToZeroScheme : Γ(zeroSchemeRestrictModule L L' s, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (Stacks.Divisors.zeroScheme X L s).subschemeι L' s'

/-- **The intersection of the two zero schemes `Z(s)` and `Z(s')`, presented inside `Z(s)`**: the
zero scheme of the restriction of `s'` to `Z(s)`. -/
abbrev zeroSchemeInter : (Stacks.Divisors.zeroScheme X L s).subscheme.IdealSheafData :=
  Stacks.Divisors.zeroScheme (Stacks.Divisors.zeroScheme X L s).subscheme
    (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s')

/-- **Stacks 0B6Y for the intersection of two zero schemes.** The zero scheme of the restricted
section `s'|_{Z(s)}` is the inverse image of `Z(s')` under `Z(s) → X`. -/
theorem zeroSchemeInter_eq_comap :
    zeroSchemeInter L L' s s' =
      (Stacks.Divisors.zeroScheme X L' s').comap
        (Stacks.Divisors.zeroScheme X L s).subschemeι :=
  Stacks.Divisors.zeroScheme_pullback (Stacks.Divisors.zeroScheme X L s).subschemeι L' s'

/-- **The two presentations of the intersection of two zero schemes are isomorphic over the
ambient scheme.** -/
theorem exists_iso_zeroSchemeInter :
    ∃ e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme,
      e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L' s').subschemeι =
        (zeroSchemeInter L L' s s').subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι := by
  obtain ⟨e₁, he₁⟩ := Stacks.ChernCap42.exists_iso_comap_sup (Stacks.Divisors.zeroScheme X L s)
    (Stacks.Divisors.zeroScheme X L' s') (Stacks.Divisors.zeroScheme X L s).subschemeι
    (Iso.refl _) (by simp)
  obtain ⟨e₂, he₂⟩ := Stacks.ChernCap42.exists_iso_comap_sup (Stacks.Divisors.zeroScheme X L' s')
    (Stacks.Divisors.zeroScheme X L s) (Stacks.Divisors.zeroScheme X L' s').subschemeι
    (Iso.refl _) (by simp)
  rw [zeroSchemeInter_eq_comap L L' s s', zeroSchemeInter_eq_comap L' L s' s]
  refine ⟨e₁ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme (sup_comm _ _)) ≪≫ e₂.symm, ?_⟩
  have h₂ : e₂.inv ≫ ((Stacks.Divisors.zeroScheme X L s).comap
        (Stacks.Divisors.zeroScheme X L' s').subschemeι).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (Stacks.Divisors.zeroScheme X L' s' ⊔ Stacks.Divisors.zeroScheme X L s).subschemeι := by
    rw [← he₂, Iso.inv_hom_id_assoc]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc, h₂]
  have h₃ : (eqToIso (congrArg Scheme.IdealSheafData.subscheme
        (sup_comm (Stacks.Divisors.zeroScheme X L s)
          (Stacks.Divisors.zeroScheme X L' s')))).hom ≫
        (Stacks.Divisors.zeroScheme X L' s' ⊔ Stacks.Divisors.zeroScheme X L s).subschemeι =
      (Stacks.Divisors.zeroScheme X L s ⊔ Stacks.Divisors.zeroScheme X L' s').subschemeι := by
    rw [eqToIso.hom]
    exact Stacks.ChernCap42.subschemeι_eqToHom (sup_comm _ _)
  rw [h₃, he₁]

end Setup

/-! ### The Gysin component cycle, descended into the zero scheme -/

section Descent

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (j : Z ⟶ X) [IsClosedImmersion j]
  (hj : j ≫ sX = sZ) (m : ℤ)

/-- **A cycle vanishing off a closed subscheme is the pushforward of its own inverse image.** -/
theorem properPushforward_cyclePullbackAlongClosedImmersion_eq (c : CycleGroup C sX m)
    (hc : ∀ y : X, y ∉ Set.range j.base → c.1 y = 0) :
    properPushforward C sZ sX j hj m (cyclePullbackAlongClosedImmersion C sZ sX j hj m c) = c := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [properPushforward_cyclePullbackAlongClosedImmersion_apply]
  by_cases h : y ∈ Set.range j.base
  · exact Set.indicator_of_mem h c.1
  · rw [Set.indicator_of_notMem h, hc y h]

end Descent

section GysinDescent

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The divisor cycle of a generator on an integral component, pushed forward to the ambient
scheme, vanishes off the zero scheme.** -/
theorem properPushforward_chernCycleOfRestrictedStalk_apply_eq_zero_of_notMem (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt)) {m : L.presheaf.stalk ξ}
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s)
    (y : X) (hy : y ∉ Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base) :
    (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
        (integralComponentAt ξ).subschemeι rfl k
        (chernCycleOfRestrictedStalk C p k L (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim
          (genericPointOf_integralComponentAt ξ) m)).1 y = 0 := by
  rw [Scheme.IdealSheafData.range_subschemeι] at hy
  by_cases hr : y ∈ Set.range (integralComponentAt ξ).subschemeι.base
  · obtain ⟨w, rfl⟩ := hr
    rw [properPushforward_apply_image_of_isClosedImmersion]
    have hyW : (integralComponentAt ξ).subschemeι.base w ∈
        (((integralComponentAt ξ)).support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    by_cases h : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ
    · exact absurd ((le_integralComponentAt_iff_mem_support _ _).1
        (h.trans ((le_integralComponentAt_iff_mem_support _ _).2 hyW))) hy
    · obtain rfl := hmt h
      have hcyc := (val_chernCycleOfRestrictedStalk C p k L ξ hDim
          (L.presheaf.germ ⊤ ξ trivial s)).trans
        (weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_of_not_le C p L s ξ h k hDim)
      rw [show (chernCycleOfRestrictedStalk C p k L (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ)
            (L.presheaf.germ ⊤ ξ trivial s)).1 w = _ from congrFun (congrArg _ hcyc) w]
      by_contra hne
      have hmem := support_cycleAssociatedToClosedSubscheme_subset C
        ((integralComponentAt ξ).subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme X L s).comap
          (integralComponentAt ξ).subschemeι).subschemeι k hne
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap] at hmem
      exact hy (by simpa using hmem)
  · exact properPushforward_apply_of_notMem_range C ((integralComponentAt ξ).subschemeι ≫ p) p
      (integralComponentAt ξ).subschemeι rfl k _ hr

/-- **The Gysin component cycle of an integral component is, inside the zero scheme, rationally
equivalent to the inverse image of the divisor cycle of a prescribed generator.** The
difference is witnessed inside the inverse image of the intersection of the component with the
zero scheme. -/
theorem isRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_cyclePullback (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt)) {m : L.presheaf.stalk ξ} (hm : Stacks.Divisors.IsStalkBasis L ξ m)
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s) :
    IsRationallyEquivalentToZeroWithin C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (gysinComponentCycle C p k L s (firstChernComponentClass C p k L) (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim -
        cyclePullbackAlongClosedImmersion C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
            (integralComponentAt ξ).subschemeι rfl k
            (chernCycleOfRestrictedStalk C p k L (integralComponentAt ξ)
              (isIntegral_integralComponentAt ξ) hDim
              (genericPointOf_integralComponentAt ξ) m)))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹'
        (((integralComponentAt ξ).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L s).support : Set X))) := by
  refine isRationallyEquivalentToZeroWithin_of_properPushforward C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _
    (by rw [Scheme.IdealSheafData.range_subschemeι]; exact Set.inter_subset_right) ?_
  rw [properPushforward_sub, properPushforward_cyclePullbackAlongClosedImmersion_eq C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _
    (properPushforward_chernCycleOfRestrictedStalk_apply_eq_zero_of_notMem C p k L s ξ hDim hmt)]
  exact isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub C p L s k ξ
    hDim hm hmt

end GysinDescent

/-! ### Two towers of integral-component rules, assembled -/

section Assembly

variable (C : ChowSituation.{u}) {X Y Z Y' Z' : Scheme.{u}} (p : X ⟶ C.S)
  [LocallyOfFiniteType p] {q : Y ⟶ C.S} [LocallyOfFiniteType q] {r : Z ⟶ C.S}
  [LocallyOfFiniteType r] {q' : Y' ⟶ C.S} [LocallyOfFiniteType q'] {r' : Z' ⟶ C.S}
  [LocallyOfFiniteType r'] {g : Y ⟶ X} {h : Z ⟶ Y} {g' : Y' ⟶ X} {h' : Z' ⟶ Y'} (k : ℤ)

/-- The composite of two rules on integral components, applied to the cycle a rule attaches to
an integral closed subscheme `W`, is supported over `W`. -/
theorem support_zsmul_extendCycleGroup_cycle_subset
    (R₁ : IntegralComponentRule C p q g (k + 1)) (R₂ : IntegralComponentRule C q r h k)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)) (n : ℤ) :
    Function.support (n • R₂.extendCycleGroup (R₁.cycle W hW hDim)).1 ⊆
      h.base ⁻¹' (g.base ⁻¹' (W.support : Set X)) := by
  have hcl : IsClosed (g.base ⁻¹' (W.support : Set X)) := W.support.isClosed.preimage g.continuous
  have hsub := GysinChernCap.support_extendCycleGroup_subset C q r h R₂ hcl
    (R₁.cycle W hW hDim) (R₁.support_subset W hW hDim)
  intro z hz
  exact hsub fun h0 ↦ hz (by change n * _ = 0; rw [h0, mul_zero])

/-- The composite of two rules on integral components, applied to a cycle, is the finite sum of
the composites applied to its integral components. -/
private theorem extendCycleGroup_comp_apply_eq_finsum
    (R₁ : IntegralComponentRule C p q g (k + 1)) (R₂ : IntegralComponentRule C q r h k)
    (a : CycleGroup C p (k + 1 + 1)) (z : Z) :
    (R₂.extendCycleGroup (R₁.extendCycleGroup a)).1 z =
      ∑ᶠ x : cycleSupportIndex a, (a.1 x.1 • R₂.extendCycleGroup (R₁.cycle
        (integralComponentAt x.1) (isIntegral_integralComponentAt x.1)
        (schemeDeltaDimension_cycleSupportIndex a x))).1 z :=
  Eq.trans (R₁.extendCycleGroup_comp_of_presentation R₂
    (fun x : cycleSupportIndex a ↦ integralComponentAt x.1)
    (fun x ↦ isIntegral_integralComponentAt x.1) (schemeDeltaDimension_cycleSupportIndex a)
    (locallyFinite_support_integralComponentAt a) (fun x ↦ a.1 x.1) a
    (cycle_eq_finsum_primeCycles a) z) (finsum_congr fun _ ↦ rfl)

/-- **Two towers of Gysin-type rules agree as soon as they agree on integral components.** Let
`R₂ ∘ R₁` and `R₂' ∘ R₁'` be two composites of rules on integral components over the same `X`,
with a closed immersion `w` identifying the bottom of the first tower with the bottom of the
second compatibly with the maps to `X`. If for every integral closed subscheme `W ⊆ X` of
delta-dimension `k + 2` the two cycles attached to `W` differ by a rational equivalence witnessed
over `W`, then the two composites agree on every cycle, modulo rational equivalence. -/
theorem rationallyEquivalent_properPushforward_extendCycleGroup_comp_of_components
    (R₁ : IntegralComponentRule C p q g (k + 1)) (R₂ : IntegralComponentRule C q r h k)
    (R₁' : IntegralComponentRule C p q' g' (k + 1)) (R₂' : IntegralComponentRule C q' r' h' k)
    (w : Z ⟶ Z') [IsClosedImmersion w] (hw : w ≫ r' = r)
    (hbase : ∀ z : Z, g'.base (h'.base (w.base z)) = g.base (h.base z))
    (hcomp : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
      IsRationallyEquivalentToZeroWithin C r' k
        (properPushforward C r r' w hw k (R₂.extendCycleGroup (R₁.cycle W hW hDim)) -
          R₂'.extendCycleGroup (R₁'.cycle W hW hDim))
        (h'.base ⁻¹' (g'.base ⁻¹' (W.support : Set X))))
    (a : CycleGroup C p (k + 1 + 1)) :
    RationallyEquivalent C r' k
      (properPushforward C r r' w hw k (R₂.extendCycleGroup (R₁.extendCycleGroup a)))
      (R₂'.extendCycleGroup (R₁'.extendCycleGroup a)) := by
  have hW : ∀ x : cycleSupportIndex a, IsIntegral (integralComponentAt x.1).subscheme :=
    fun x ↦ isIntegral_integralComponentAt x.1
  have hDim : ∀ x : cycleSupportIndex a,
      schemeDeltaDimension C ((integralComponentAt x.1).subschemeι ≫ p) =
        ((k + 1 + 1 : ℤ) : EInt) := fun x ↦ schemeDeltaDimension_cycleSupportIndex a x
  have hLocal : LocallyFinite fun x : cycleSupportIndex a ↦
      ((integralComponentAt x.1).support : Set X) :=
    locallyFinite_support_integralComponentAt a
  have hTlocal : LocallyFinite fun x : cycleSupportIndex a ↦
      h'.base ⁻¹' (g'.base ⁻¹' ((integralComponentAt x.1).support : Set X)) :=
    GysinChernCap.locallyFinite_preimage
      (GysinChernCap.locallyFinite_preimage hLocal g'.continuous) h'.continuous
  have hv : ∀ x : cycleSupportIndex a, Function.support
      ((a.1 x.1 •
        R₂'.extendCycleGroup (R₁'.cycle (integralComponentAt x.1) (hW x) (hDim x)))).1 ⊆
      h'.base ⁻¹' (g'.base ⁻¹' ((integralComponentAt x.1).support : Set X)) := fun x ↦
    support_zsmul_extendCycleGroup_cycle_subset C p k R₁' R₂'
      (integralComponentAt x.1) (hW x) (hDim x) (a.1 x.1)
  have hu : ∀ x : cycleSupportIndex a, Function.support
      (properPushforward C r r' w hw k (a.1 x.1 •
        R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x)))).1 ⊆
      h'.base ⁻¹' (g'.base ⁻¹' ((integralComponentAt x.1).support : Set X)) := by
    intro x z' hz'
    by_cases hr : z' ∈ Set.range w.base
    · obtain ⟨z, rfl⟩ := hr
      rw [Function.mem_support, properPushforward_apply_image_of_isClosedImmersion] at hz'
      have hz := support_zsmul_extendCycleGroup_cycle_subset C p k R₁ R₂
        (integralComponentAt x.1) (hW x) (hDim x) (a.1 x.1) hz'
      simp only [Set.mem_preimage] at hz ⊢
      rw [hbase z]
      exact hz
    · exact absurd (properPushforward_apply_of_notMem_range C r r' w hw k _ hr) hz'
  have hA : ∀ z' : Z',
      (properPushforward C r r' w hw k (R₂.extendCycleGroup (R₁.extendCycleGroup a))).1 z' =
        ∑ᶠ x : cycleSupportIndex a, (properPushforward C r r' w hw k (a.1 x.1 •
          R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x)))).1 z' := by
    have hγ := extendCycleGroup_comp_apply_eq_finsum C p k R₁ R₂ a
    intro z'
    exact properPushforward_apply_finsum_of_isClosedImmersion C r r' w hw k
      (R₂.extendCycleGroup (R₁.extendCycleGroup a))
      (fun x : cycleSupportIndex a ↦ a.1 x.1 •
        R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x))) hγ z'
  have hB := extendCycleGroup_comp_apply_eq_finsum C p k R₁' R₂' a
  have hD : ∀ x : cycleSupportIndex a, IsRationallyEquivalentToZeroWithin C r' k
      (properPushforward C r r' w hw k (a.1 x.1 •
          R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x))) -
        a.1 x.1 • R₂'.extendCycleGroup (R₁'.cycle (integralComponentAt x.1) (hW x) (hDim x)))
      (h'.base ⁻¹' (g'.base ⁻¹' ((integralComponentAt x.1).support : Set X))) := by
    intro x
    refine isRationallyEquivalentToZeroWithin_zsmul C r' k
      (hcomp (integralComponentAt x.1) (hW x) (hDim x)) (a.1 x.1) fun z ↦ ?_
    have hzs : properPushforward C r r' w hw k
          (a.1 x.1 • R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x))) =
        a.1 x.1 • properPushforward C r r' w hw k
          (R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x))) :=
      map_zsmul (properPushforwardHom C r r' w hw k) _ _
    show (properPushforward C r r' w hw k (a.1 x.1 •
          R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x)))).1 z -
        (a.1 x.1 •
          R₂'.extendCycleGroup (R₁'.cycle (integralComponentAt x.1) (hW x) (hDim x))).1 z =
      a.1 x.1 * _
    rw [hzs]
    show a.1 x.1 * _ - a.1 x.1 * _ = a.1 x.1 * _
    rw [← mul_sub]
    rfl
  exact (mem_rationalEquivalences C r' k _).mpr
    (isRationallyEquivalentToZeroWithin_sub_of_finsum C r' k
      (fun x : cycleSupportIndex a ↦
        h'.base ⁻¹' (g'.base ⁻¹' ((integralComponentAt x.1).support : Set X)))
      hTlocal (properPushforward C r r' w hw k (R₂.extendCycleGroup (R₁.extendCycleGroup a)))
      (R₂'.extendCycleGroup (R₁'.extendCycleGroup a))
      (fun x : cycleSupportIndex a ↦ properPushforward C r r' w hw k (a.1 x.1 •
        R₂.extendCycleGroup (R₁.cycle (integralComponentAt x.1) (hW x) (hDim x))))
      (fun x : cycleSupportIndex a ↦ a.1 x.1 •
        R₂'.extendCycleGroup (R₁'.cycle (integralComponentAt x.1) (hW x) (hDim x)))
      hu hv hA hB hD).isRationallyEquivalentToZero

end Assembly

/-! ### The iterated Gysin map on an integral component -/

section Comm

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤))

/-- The Gysin integral-component rule of an invertible module with a global section: Stacks 02T8
at the first Chern class component rule of the module. -/
abbrev gysinRuleOfInvertible : IntegralComponentRule C p
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (Stacks.Divisors.zeroScheme X L s).subschemeι k :=
  gysinRule C p k L s (firstChernComponentClass C p k L)

/-- The Gysin integral-component rule of the restriction of `(L', s')` to the zero scheme of
`s`: the second of the two Gysin maps of Stacks 0B73, on integral components. -/
abbrev gysinRuleInter : IntegralComponentRule C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (zeroSchemeInter L L' s s').subschemeι k :=
  gysinRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
    (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s')
    (firstChernComponentClass C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (zeroSchemeRestrictModule L L' s))

/-- **The iterated Gysin cycle of an integral component**, in the presentation of the
intersection inside `Z(s)`: apply the Gysin rule of `(L, s)` to `W` and then the Gysin rule of
the restriction of `(L', s')` to `Z(s)`. -/
abbrev gysinGysinComponentCycle (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)) :
    CycleGroup C ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  (gysinRuleInter C p k L L' s s').extendCycleGroup
    ((gysinRuleOfInvertible C p (k + 1) L s).cycle W hW hDim)

/-- **The divisor cycle of a prescribed generator on an integral component, descended into
`Z(s)`.** The divisor `div_{L|W}(m|_W)` of a generator `m` of `L_ξ` on the integral component
`W = Z_ξ`, pushed forward to `X` and pulled back along `Z(s) ⟶ X`. -/
abbrev descendedComponentDivisorCycle (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt)) (m : L.presheaf.stalk ξ) :
    CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1) :=
  cyclePullbackAlongClosedImmersion C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
    (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
      (integralComponentAt ξ).subschemeι rfl (k + 1)
      (chernCycleOfRestrictedStalk C p (k + 1) L (integralComponentAt ξ)
        (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ) m))

/-- The iterated Gysin cycle of an integral component `W = Z_ξ` of delta-dimension `k + 2`
differs, inside the intersection, from the outer Gysin cycle of the descended divisor
`Stacks.Chow.descendedComponentDivisorCycle` by a cycle rationally equivalent to zero, witnessed
over `W ∩ Z(s)`. -/
theorem isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    {m : L.presheaf.stalk ξ} (hm : Stacks.Divisors.IsStalkBasis L ξ m)
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s) :
    IsRationallyEquivalentToZeroWithin C
      ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (gysinGysinComponentCycle C p k L L' s s' (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim -
        (gysinRuleInter C p k L L' s s').extendCycleGroup
          (descendedComponentDivisorCycle C p k L s ξ hDim m))
      ((zeroSchemeInter L L' s s').subschemeι.base ⁻¹'
        ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹'
          (((integralComponentAt ξ).support : Set X) ∩
            ((Stacks.Divisors.zeroScheme X L s).support : Set X)))) := by
  have h := isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
    (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s')
    (isRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_cyclePullback C p (k + 1) L s ξ
      hDim hm hmt)
  rwa [map_sub] at h

omit [LocallyOfFiniteType p] in
/-- The structure morphisms agree under an identification of the two presentations of the
intersection. -/
theorem iso_zeroSchemeInter_comp_structureMorphism
    (e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι) :
    e.hom ≫ ((zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) =
      (zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p := by
  simpa only [Category.assoc] using congrArg (· ≫ p) he

/-- The identification of the two presentations of the intersection is compatible with the maps
to the ambient scheme, on points. -/
theorem iso_zeroSchemeInter_base
    (e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι)
    (z : (zeroSchemeInter L L' s s').subscheme) :
    (Stacks.Divisors.zeroScheme X L' s').subschemeι.base
        ((zeroSchemeInter L' L s' s).subschemeι.base (e.hom.base z)) =
      (Stacks.Divisors.zeroScheme X L s).subschemeι.base
        ((zeroSchemeInter L L' s s').subschemeι.base z) := by
  show ((zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι).base (e.hom.base z) =
      ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι).base z
  rw [← he]
  rfl

/-- **The image of the intersection in the ambient scheme** is the intersection of the two
supports. -/
theorem range_zeroSchemeInter_subschemeι_comp :
    Set.range ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι).base =
      ((Stacks.Divisors.zeroScheme X L' s').support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X L s).support : Set X) := by
  have hA : Set.range (zeroSchemeInter L L' s s').subschemeι.base =
      (Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹'
        ((Stacks.Divisors.zeroScheme X L' s').support : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, zeroSchemeInter_eq_comap L L' s s',
      Scheme.IdealSheafData.support_comap]
    simp
  have hc : ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι).base =
      (Stacks.Divisors.zeroScheme X L s).subschemeι.base ∘
        (zeroSchemeInter L L' s s').subschemeι.base := rfl
  rw [hc, Set.range_comp, hA, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι]

/-- **The per-component statement of Stacks 0B73.** For every integral closed subscheme
`W ⊆ X` of delta-dimension `k + 2`, the two iterated Gysin cycles of `W` — the one taken through
`Z(s)` and transported to the second presentation of the intersection, and the one taken through
`Z(s')` — differ by a cycle rationally equivalent to zero, witnessed over `W`. -/
def GysinGysinCommutesOnComponents
    (e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι) : Prop :=
  ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
    IsRationallyEquivalentToZeroWithin C ((zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) k
      (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          ((zeroSchemeInter L' L s' s).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p)
          e.hom (iso_zeroSchemeInter_comp_structureMorphism C p L L' s s' e he) k
          (gysinGysinComponentCycle C p k L L' s s' W hW hDim) -
        gysinGysinComponentCycle C p k L' L s' s W hW hDim)
      ((zeroSchemeInter L' L s' s).subschemeι.base ⁻¹'
        ((Stacks.Divisors.zeroScheme X L' s').subschemeι.base ⁻¹' (W.support : Set X)))

/-- **The per-component statement of Stacks 0B73, reduced to the ambient scheme.** It is enough
to compare the two iterated Gysin cycles of `W` *after pushing both forward to `X`*, with the
rational equivalence carried over the intersection of `W` with the two divisors. -/
theorem gysinGysinCommutesOnComponents_of_properPushforward
    (e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (zeroSchemeInter L L' s s').subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι)
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
      IsRationallyEquivalentToZeroWithin C p k
        (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
              (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
            ((zeroSchemeInter L L' s s').subschemeι ≫
              (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
            (gysinGysinComponentCycle C p k L L' s s' W hW hDim) -
          properPushforward C ((zeroSchemeInter L' L s' s).subschemeι ≫
              (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) p
            ((zeroSchemeInter L' L s' s).subschemeι ≫
              (Stacks.Divisors.zeroScheme X L' s').subschemeι) (Category.assoc _ _ _) k
            (gysinGysinComponentCycle C p k L' L s' s W hW hDim))
        ((W.support : Set X) ∩
          (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
            ((Stacks.Divisors.zeroScheme X L' s').support : Set X)))) :
    GysinGysinCommutesOnComponents C p k L L' s s' e he := by
  intro W hW hDim
  set T : Set X := (W.support : Set X) ∩
    (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
      ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) with hTdef
  set β : CycleGroup C ((zeroSchemeInter L' L s' s).subschemeι ≫
      (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) k :=
    properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      ((zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) e.hom
      (iso_zeroSchemeInter_comp_structureMorphism C p L L' s s' e he) k
      (gysinGysinComponentCycle C p k L L' s s' W hW hDim) -
      gysinGysinComponentCycle C p k L' L s' s W hW hDim with hβdef
  have hsub : T ⊆ Set.range ((zeroSchemeInter L' L s' s).subschemeι ≫
      (Stacks.Divisors.zeroScheme X L' s').subschemeι).base := by
    rw [range_zeroSchemeInter_subschemeι_comp L' L s' s]
    exact fun x hx ↦ hx.2
  have hmain : IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((zeroSchemeInter L' L s' s).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) p
        ((zeroSchemeInter L' L s' s).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L' s').subschemeι) (Category.assoc _ _ _) k β) T := by
    rw [hβdef, properPushforward_sub, properPushforward_properPushforward C
      ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      ((zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) p e.hom
      ((zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι)
      (iso_zeroSchemeInter_comp_structureMorphism C p L L' s s' e he) (Category.assoc _ _ _) k,
      congrFun (properPushforward_congr C ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L' s').subschemeι)
        ((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι) he _ (Category.assoc _ _ _) k) _]
    exact h W hW hDim
  exact (isRationallyEquivalentToZeroWithin_of_properPushforward C
    ((zeroSchemeInter L' L s' s).subschemeι ≫
      (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) p
    ((zeroSchemeInter L' L s' s).subschemeι ≫
      (Stacks.Divisors.zeroScheme X L' s').subschemeι) (Category.assoc _ _ _) k β hsub
    hmain).mono fun z hz ↦ hz.1

/-- Pushforward along an isomorphism, on the class of a cycle. -/
theorem chowPushforwardOfIso_mk_coe {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) (m : ℤ)
    (c : CycleGroup C sA m) :
    chowPushforwardOfIso C sA sB f hf m (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (properPushforward C sA sB f hf m c) :=
  rfl

/-- The descended Gysin map of an invertible module, on the class of a cycle, is the class of the
coefficientwise extension of the Gysin integral-component rule. -/
theorem gysinChowOfInvertible_mk_eq_mk_extendCycleGroup (α : CycleGroup C p (k + 1)) :
    gysinChowOfInvertible C p k L s (QuotientAddGroup.mk α) =
      QuotientAddGroup.mk ((gysinRuleOfInvertible C p k L s).extendCycleGroup α) :=
  rfl

/-! ### The reduction of Stacks 0B73 to its per-component statement -/

/-- **Stacks 0B73, reduced to its per-component statement.** The two iterated Gysin maps
`A_{k+2}(X) → A_k(D ∩ D')` agree, in the two presentations of the intersection, as soon as they
agree on the integral closed subschemes of delta-dimension `k + 2`. -/
theorem gysinChowOfInvertible_comm_of_components
    (e : (zeroSchemeInter L L' s s').subscheme ≅ (zeroSchemeInter L' L s' s).subscheme)
    (he : e.hom ≫ (zeroSchemeInter L' L s' s).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L' s').subschemeι =
      (zeroSchemeInter L L' s s').subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι)
    (hcomp : GysinGysinCommutesOnComponents C p k L L' s s' e he)
    (α : chowGroup C p (k + 1 + 1)) :
    chowPushforwardOfIso C ((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((zeroSchemeInter L' L s' s).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p)
        e.hom (iso_zeroSchemeInter_comp_structureMorphism C p L L' s s' e he) k
        (gysinChowOfInvertible C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
          (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s')
          (gysinChowOfInvertible C p (k + 1) L s α)) =
      gysinChowOfInvertible C ((Stacks.Divisors.zeroScheme X L' s').subschemeι ≫ p) k
        (zeroSchemeRestrictModule L' L s') (restrictSectionToZeroScheme L' L s' s)
        (gysinChowOfInvertible C p (k + 1) L' s' α) := by
  induction α using QuotientAddGroup.induction_on with
  | H a =>
  rw [gysinChowOfInvertible_mk_eq_mk_extendCycleGroup,
    gysinChowOfInvertible_mk_eq_mk_extendCycleGroup,
    gysinChowOfInvertible_mk_eq_mk_extendCycleGroup,
    gysinChowOfInvertible_mk_eq_mk_extendCycleGroup, chowPushforwardOfIso_mk_coe]
  exact QuotientAddGroup.eq_iff_sub_mem.mpr
    (rationallyEquivalent_properPushforward_extendCycleGroup_comp_of_components C p k
      (gysinRuleOfInvertible C p (k + 1) L s) (gysinRuleInter C p k L L' s s')
      (gysinRuleOfInvertible C p (k + 1) L' s') (gysinRuleInter C p k L' L s' s)
      e.hom (iso_zeroSchemeInter_comp_structureMorphism C p L L' s s' e he)
      (iso_zeroSchemeInter_base L L' s s' e he) hcomp a)

end Comm

end Stacks.Chow

end
