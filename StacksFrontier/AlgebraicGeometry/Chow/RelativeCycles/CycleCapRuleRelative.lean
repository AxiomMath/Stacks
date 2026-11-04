module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleRigidity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleSourceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassProperCover
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HDescent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RelativeOpenCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0H6G: operations on cycles compatible with pushforward, pullback and Gysin maps

Let `(S, δ)` be as in Section 0H65, let `X ⟶ Y` be a morphism of schemes locally of finite type
over `S` and let `r ≥ 0`. Stacks 0H6G claims that a rule `c` which to every morphism
`g : Y' ⟶ Y` locally of finite type and every `e ∈ ℤ` associates an operation
`c ∩ - : Z_e(Y') ⟶ Z_{r+e}(X')`, compatible with proper pushforward, flat pullback, and Gysin
maps as in Lemma 0H6E, is `g ↦ g^*α ∩ -` for a relative `r`-cycle `α` on `X/Y`. This file proves
the claim: `Stacks.Chow.CompatibleCycleCapRule.exists_relativeCycle`.

The family `α` is `Stacks.Chow.CycleCapRule.genericFamily`, and `c ∩ - = g^*α ∩ -` is
`Stacks.Chow.CompatibleCycleCapRule.cap_eq_relativeCycleCap`. What remains is that `α` is a
relative cycle, `Stacks.Chow.CompatibleCycleCapRule.isRelativeCycle_genericFamily`:

* being a relative cycle is local on `X` (Lemma 0H51 and
  `Stacks.Chow.isRelativeCycle_of_openCover`) and restriction of the rule to an open of `X`
  restricts the family, so `X` may be assumed affine;
* a morphism from the spectrum of a discrete valuation ring to `Y` factors through an affine open
  `V` of the integral closed subscheme with generic point the image of the generic point, so it
  suffices that the base change `α_V` of `α` to `V` is a relative cycle;
* by the flattening argument of Lemma 0H59 there is a proper surjective `b : T ⟶ V`, `T`
  integral, and a relative cycle `β` on `X_T / T` agreeing with `b^*α_V` over the generic point
  of `T` (`Stacks.Chow.exists_isProper_cycleClassMap_genericPoint_eq_of_isIntegral`);
* the rule restricted to `T` minus the rule of `β` is a rule as in Stacks 0H6G whose family
  vanishes over the generic point of `T`, hence vanishes
  (`Stacks.Chow.CompatibleCycleCapRule.genericFamily_eq_zero_of_genericPoint`), so `b^*α_V = β`;
* a family whose base change along a proper surjective morphism is a relative cycle is one
  (Lemma 0H52).

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Lemma 0H52](https://stacks.math.columbia.edu/tag/0H52)
* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {p : X ⟶ Y} [LocallyOfFiniteType p] {r : ℕ}

/-- **The family of a rule restricted to an open of the source** is the restriction of the family.
-/
theorem CompatibleCycleCapRule.genericFamily_restrictSource (c : CompatibleCycleCapRule C sY p r)
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (c.restrictSource j).genericFamily =
      fun s ↦ fiberCycleRestrict p (j ≫ p) j rfl s r (c.genericFamily s) := by
  refine familyOfCycles_ext_familyCoeff (j ≫ p) (funext fun u ↦ ?_)
  rw [CycleCapRule.familyCoeff_genericFamily]
  have hfib : familyCoeff (j ≫ p) r
      (fun s ↦ fiberCycleRestrict p (j ≫ p) j rfl s r (c.genericFamily s)) u =
      familyCoeff p r c.genericFamily (j.base u) := by
    change ((fiberCycleRestrict p (j ≫ p) j rfl ((j ≫ p).base u) r
      (c.genericFamily ((j ≫ p).base u)) : FiberCycleGroup (j ≫ p) _ r) :
      AlgebraicCycle _ ℤ) ((j ≫ p).asFiber u) = _
    rw [fiberCycleRestrict_apply, ← familyCoeff_fiberι p r c.genericFamily]
    congr 1
    change (fiberRestrict p (j ≫ p) j rfl _ ≫ p.fiberι _) _ = _
    rw [fiberRestrict_fiberι, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]
  rw [hfib, CycleCapRule.familyCoeff_genericFamily]
  have := isIntegral_integralComponentAt ((j ≫ p).base u)
  obtain ⟨hz₁, -⟩ := (exists_pointClosure_lift (p := j ≫ p) u).choose_spec
  rw [CycleCapRule.genericCoeff, CompatibleCycleCapRule.restrictSource_toCycleCapRule,
    CycleCapRule.restrictSource_cap_apply]
  refine (c.toCycleCapRule.genericCoeff_eq rfl _ ?_).symm
  exact (congrArg (fun f : _ ⟶ X ↦ f.base (exists_pointClosure_lift (p := j ≫ p) u).choose)
    (sourceRestrictionMap_fst (p := p) j (integralComponentAt ((j ≫ p).base u)).subschemeι)).trans
    (congrArg j.base hz₁)

/-- An affine scheme locally of finite type over a locally Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType {V S : Scheme.{u}} [IsLocallyNoetherian S]
    [IsAffine V] (f : V ⟶ S) [LocallyOfFiniteType f] : IsNoetherian V :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  {}

/-- **The family of a rule over a Noetherian integral base is a relative cycle.** Here `X ⟶ Y` is
quasi-compact. By the flattening argument of Lemma 0H59 there is a proper surjective `b : T ⟶ Y`
with `T` integral and a relative cycle `β` on `X_T/T` agreeing with `b^*α` over the generic point
of `T`; the rule restricted to `T` minus the rule of `β` has a family vanishing over the generic
point, hence everywhere by rigidity, so `b^*α = β` is a relative cycle, and so is `α` by
Lemma 0H52. -/
theorem CompatibleCycleCapRule.isRelativeCycle_genericFamily_of_isIntegral [IsNoetherian Y]
    [IsIntegral Y] [QuasiCompact p] (c : CompatibleCycleCapRule C sY p r) :
    IsRelativeCycle p r c.genericFamily := by
  obtain ⟨T, b, hT, hTN, hb, hsurj, -, cc, hcc⟩ :=
    exists_isProper_cycleClassMap_genericPoint_eq_of_isIntegral p r c.genericFamily
  have : LocallyOfFinitePresentation b := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
    inferInstance
  set β := relativeCycleClassMap (r := r) (pullback.snd p b) cc with hβdef
  have hβ : IsRelativeCycle (pullback.snd p b) r β.1 := β.2
  set D := c.restrict b - relativeCycleCompatibleRule C (b ≫ sY) (pullback.snd p b) r β.1 hβ
    with hD
  have hfam : D.genericFamily = baseChangeFamily p b r c.genericFamily - β.1 := by
    change ((c.restrict b).toCycleCapRule -
      CycleCapRule.ofFamily C (b ≫ sY) (pullback.snd p b) r β.1).genericFamily = _
    rw [CycleCapRule.genericFamily_sub, CycleCapRule.genericFamily_ofFamily]
    exact congrArg (· - β.1) (c.genericFamily_restrict b)
  have hzero := D.genericFamily_eq_zero_of_genericPoint fun x hx ↦
    familyCoeff_eq_zero_of_apply_eq_zero _ _ (by rw [hfam, Pi.sub_apply, ← hcc, sub_self]) hx
  rw [hfam, sub_eq_zero] at hzero
  refine isRelativeCycle_of_isRelativeCycle_baseChangeFamily_of_isProper p b r c.genericFamily ?_
  rw [hzero]
  exact hβ

/-- **The family of a rule is a relative cycle, for `X ⟶ Y` quasi-compact.** A morphism from the
spectrum of a discrete valuation ring to `Y` factors through an affine open `V` of the integral
closed subscheme with generic point the image of the generic point; the family of the rule
restricted to `V` is the base change of the family, which is a relative cycle by
`Stacks.Chow.CompatibleCycleCapRule.isRelativeCycle_genericFamily_of_isIntegral`. -/
theorem CompatibleCycleCapRule.isRelativeCycle_genericFamily_of_quasiCompact [QuasiCompact p]
    (c : CompatibleCycleCapRule C sY p r) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    IsRelativeCycle p r c.genericFamily := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  intro R _ _ _ c₀
  -- the integral closed subscheme with generic point the image of the generic point
  set y := c₀.base (genericPoint (Spec (.of R))) with hy
  have := isIntegral_integralComponentAt y
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : Spec (.of R) ⟶ (integralComponentAt y).subscheme,
      c₁ ≫ (integralComponentAt y).subschemeι = c₀ := by
    refine (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support _ c₀).mpr ?_
    rintro _ ⟨t, rfl⟩
    rw [coe_support_integralComponentAt]
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes t).map c₀.base.hom.continuous)
  -- an affine open of it through which the morphism factors
  obtain ⟨V, hV, h0V⟩ := exists_isAffineOpen_mem (c₁.base (IsLocalRing.closedPoint R))
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Spec (.of R) ⟶ V.toScheme, c₂ ≫ V.ι = c₁ := by
    refine ⟨IsOpenImmersion.lift V.ι c₁ ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ((IsLocalRing.specializes_closedPoint t).map c₁.base.hom.continuous).mem_open V.2 h0V
  have : Nonempty V := ⟨⟨_, h0V⟩⟩
  have : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  have : IsAffine V := hV
  set v := V.ι ≫ (integralComponentAt y).subschemeι with hv
  have := isNoetherian_of_locallyOfFiniteType (v ≫ sY)
  have hrel := (c.restrict v).isRelativeCycle_genericFamily_of_isIntegral
  rw [CompatibleCycleCapRule.genericFamily_restrict] at hrel
  have key := (specializationCycle_baseChangeFamily_baseChangeFamily_iff p v r c.genericFamily R
    c₂).mp (hrel R c₂)
  have hc : c₂ ≫ v = c₀ := by rw [hv, ← Category.assoc, hc₂, hc₁]
  rw [← hc]
  exact key

/-- **The family of a rule of Stacks 0H6G is a relative cycle.** Being a relative cycle is local on
`X` (Lemma 0H51), and the restriction of the rule to an affine open of `X` has the restricted
family (`Stacks.Chow.CompatibleCycleCapRule.genericFamily_restrictSource`); over an affine open,
`X ⟶ Y` is quasi-compact. -/
theorem CompatibleCycleCapRule.isRelativeCycle_genericFamily
    (c : CompatibleCycleCapRule C sY p r) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    IsRelativeCycle p r c.genericFamily := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  refine isRelativeCycle_of_openCover p r c.genericFamily (fun i ↦ X.affineCover.f i ≫ p)
    X.affineCover.f (fun _ ↦ rfl) (fun x ↦ ⟨_, X.affineCover.covers x⟩) fun i ↦ ?_
  have := isNoetherian_of_locallyOfFiniteType ((X.affineCover.f i ≫ p) ≫ sY)
  have h := (c.restrictSource (X.affineCover.f i)).isRelativeCycle_genericFamily_of_quasiCompact
  rw [CompatibleCycleCapRule.genericFamily_restrictSource] at h
  exact h

/-- **Stacks Project, Tag 0H6G.** Let `(S, δ)` be as in Section 0H65, let `p : X ⟶ Y` be a morphism
of schemes locally of finite type over `S` and let `r ≥ 0`. Let `c` be a rule that to every
morphism `g : Y' ⟶ Y` locally of finite type and every `e ∈ ℤ` associates an operation
`c ∩ - : Z_e(Y') ⟶ Z_{r+e}(X')`, `X' = Y' ×_Y X`, compatible with proper pushforward, flat
pullback, and Gysin maps as in Lemma 0H6E (`Stacks.Chow.CompatibleCycleCapRule`). Then there is a
relative `r`-cycle `α` on `X/Y` such that `c ∩ - = g^*α ∩ -` for every such `g`, where `g^*α ∩ -`
is `Stacks.Chow.relativeCycleCap`. -/
@[stacks 0H6G]
theorem CompatibleCycleCapRule.exists_relativeCycle (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ)
    (c : CompatibleCycleCapRule C sY p r) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    ∃ α ∈ relativeCycles p r, ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y) [LocallyOfFiniteType g] (e : ℤ),
      c.cap g e = relativeCycleCap C sY p r α g e :=
  ⟨c.genericFamily, c.isRelativeCycle_genericFamily,
    fun g _ e ↦ AddMonoidHom.ext (c.cap_eq_relativeCycleCap g e)⟩

end Stacks.Chow

end
