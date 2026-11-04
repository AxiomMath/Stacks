module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleFamily
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# A rule of Stacks 0H6G is the operation of its family of cycles

Let `c` be a rule as in Stacks 0H6G and let `α` be its family of `r`-cycles on the fibres of
`X/Y` (`Stacks.Chow.CycleCapRule.genericFamily`). This file proves that `c ∩ - = g^*α ∩ -` on the
cycles of every test scheme `g : Y' ⟶ Y`.

The difference `d` of the two rules is compatible with proper pushforward and flat pullback, and
vanishes on `[Z_y]` for the integral closed subschemes `Z_y ⊆ Y`
(`Stacks.Chow.CycleCapRule.cap_integralComponentAt_eq`). Two steps propagate this:

* `d ∩ [T] = 0` for every integral test scheme `T`: away from the generic point of `T` because
  both rules have generic support, and over it by generic flatness — `T ⟶ Z_y`, `y` the image
  of the generic point, restricts to a flat morphism of some relative dimension between dense
  opens, along which `[T]` is the flat pullback of `[Z_y]`;
* `d ∩ β = 0` for every cycle `β`: restricted to an affine open, `β` is a finite sum of
  pushforwards of fundamental cycles of integral closed subschemes.

## Main results

* `Stacks.Chow.CycleCapRule.cap_eq_zero_of_cap_fundamentalCycle_eq_zero`
* `Stacks.Chow.CycleCapRule.cap_fundamentalCycle_eq_zero_of_hasGenericSupport`
* `Stacks.Chow.CompatibleCycleCapRule.cap_eq_relativeCycleCap`

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {p : X ⟶ Y} [LocallyOfFiniteType p] {r : ℕ}

/-- The restriction of the fundamental cycle of an integral scheme to a nonempty open subscheme
is the fundamental cycle of the open subscheme. -/
theorem cycleGroupRestrict_fundamentalCycle_val (C : ChowSituation.{u}) {T : Scheme.{u}}
    [IsIntegral T] (q : T ⟶ C.S) [LocallyOfFiniteType q] (V : T.Opens) [Nonempty V] {k : ℤ}
    (hk : schemeDeltaDimension C q = (k : EInt)) (q' : V.toScheme ⟶ C.S)
    [LocallyOfFiniteType q'] (hq : V.ι ≫ q = q') :
    (cycleGroupRestrict C q q' V.ι hq k (fundamentalCycle C q k)).1 =
      (fundamentalCycle C q' k).1 := by
  subst hq
  have : IsIntegral V := isIntegral_of_isOpenImmersion V.ι
  refine Function.locallyFinsuppWithin.ext fun v ↦ ?_
  rw [cycleGroupRestrict_apply, fundamentalCycle_apply_of_isIntegral C _ hk,
    fundamentalCycle_apply_of_isIntegral C _ (schemeDeltaDimension_opensι_comp C q V hk),
    ← genericPoint_eq_of_isOpenImmersion V.ι]
  by_cases h : v = genericPoint V
  · rw [ite_eq_left h, ite_eq_left (congrArg _ h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (V.ι.isOpenEmbedding.injective h'))]

/-- Every point of a scheme has an affine open neighbourhood. -/
theorem exists_isAffineOpen_mem {T : Scheme.{u}} (t : T) :
    ∃ V : T.Opens, IsAffineOpen V ∧ t ∈ V := by
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ t) isOpen_univ
  exact ⟨V, hV, htV⟩

omit [LocallyOfFiniteType p] in
/-- A point of `T ×_Y X` lying over an open subscheme `V ⊆ T` comes from `V ×_Y X`. -/
theorem mem_range_bivariantBaseChangeMap_opensι {T : Scheme.{u}} (g : T ⟶ Y) (V : T.Opens)
    (w : ↥(pullback p g)) (hw : (pullback.snd p g).base w ∈ V) :
    w ∈ Set.range (bivariantBaseChangeMap p g V.ι).base := by
  rw [range_fst_of_isPullback (isPullback_bivariantBaseChangeMap p g V.ι).flip]
  exact ⟨⟨_, hw⟩, rfl⟩

/-- The coefficient of `c ∩ β` at a point of `T ×_Y X` over an open `V ⊆ T` is a coefficient of
`c ∩ β|_V`. -/
private theorem CycleCapRule.exists_cap_cycleGroupRestrict_eq (d : CycleCapRule C sY p r)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (V : T.Opens) (e : ℤ)
    (β : CycleGroup C (g ≫ sY) e) (w : ↥(pullback p g)) (hw : (pullback.snd p g).base w ∈ V) :
    ∃ w', (d.cap (V.ι ≫ g) e (cycleGroupRestrict C (g ≫ sY) ((V.ι ≫ g) ≫ sY) V.ι
      (Category.assoc V.ι g sY).symm e β)).1 w' = (d.cap g e β).1 w := by
  obtain ⟨w', hw'⟩ := mem_range_bivariantBaseChangeMap_opensι g V w hw
  exact ⟨w', by rw [d.cap_cycleGroupRestrict_apply, hw']⟩

/-- **A rule vanishing on fundamental cycles of integral test schemes vanishes.** If a rule
compatible with proper pushforward and flat pullback kills `[T]` for every integral test scheme
`T`, it kills every cycle on every test scheme: restricted to an affine open, a cycle is a finite
sum of pushforwards of fundamental cycles of integral closed subschemes. -/
theorem CycleCapRule.cap_eq_zero_of_cap_fundamentalCycle_eq_zero (d : CycleCapRule C sY p r)
    (hd : ∀ {T : Scheme.{u}} [IsIntegral T] (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ),
      schemeDeltaDimension C (g ≫ sY) = (k : EInt) →
        d.cap g k (fundamentalCycle C (g ≫ sY) k) = 0)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ)
    (β : CycleGroup C (g ≫ sY) e) : d.cap g e β = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  obtain ⟨V, hV, htV⟩ := exists_isAffineOpen_mem ((pullback.snd p g).base w)
  obtain ⟨w', hw'⟩ := d.exists_cap_cycleGroupRestrict_eq g V e β w htV
  rw [← hw']
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  set β' := cycleGroupRestrict C (g ≫ sY) ((V.ι ≫ g) ≫ sY) V.ι (Category.assoc V.ι g sY).symm e
    β
  have hfin := finite_support_of_compactSpace C _ e β'
  have hzero : d.cap (V.ι ≫ g) e β' = 0 := by
    rw [eq_finsetSum_cycleAssociatedToIntegralComponentAt C _ e β' hfin, map_sum]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hdim : relativeDimension C.dimensionFunction ((V.ι ≫ g) ≫ sY) x = e :=
      (mem_cyclesOfDimension_iff_forall_point C _ e β'.1).mp β'.2 x (hfin.mem_toFinset.mp hx)
    have := isIntegral_integralComponentAt x
    have hk : schemeDeltaDimension C
        (((integralComponentAt x).subschemeι ≫ V.ι ≫ g) ≫ sY) = (e : EInt) := by
      rw [schemeDeltaDimension_congr C (Category.assoc _ _ _),
        schemeDeltaDimension_integralComponentAt, hdim]
    rw [map_zsmul, ← properPushforward_fundamentalCycle_of_isClosedImmersion C
      (((integralComponentAt x).subschemeι ≫ V.ι ≫ g) ≫ sY) ((V.ι ≫ g) ≫ sY)
      (integralComponentAt x).subschemeι (Category.assoc _ _ _).symm e,
      ← d.properPushforward_cap, hd _ e hk, properPushforward_zero, smul_zero]
  rw [hzero]
  rfl

attribute [local instance] isIntegral_integralComponentAt in
/-- A morphism from an integral scheme factors through the integral closed subscheme with generic
point the image of its generic point, sending generic point to generic point. -/
theorem exists_lift_integralComponentAt_genericPoint {T : Scheme.{u}} [IsIntegral T] (g : T ⟶ Y)
    [LocallyOfFiniteType g] {y : Y} (hy : g.base (genericPoint T) = y) :
    ∃ g' : T ⟶ (integralComponentAt y).subscheme, g' ≫ (integralComponentAt y).subschemeι = g ∧
      LocallyOfFiniteType g' ∧
        g'.base (genericPoint T) = genericPoint (integralComponentAt y).subscheme := by
  subst hy
  obtain ⟨g', hg'⟩ : ∃ g' : T ⟶ (integralComponentAt (g.base (genericPoint T))).subscheme,
      g' ≫ (integralComponentAt (g.base (genericPoint T))).subschemeι = g := by
    refine (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support _ g).mpr ?_
    rintro _ ⟨t, rfl⟩
    rw [coe_support_integralComponentAt]
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes t).map g.base.hom.continuous)
  have : LocallyOfFiniteType (g' ≫ (integralComponentAt (g.base (genericPoint T))).subschemeι) := by
    rw [hg']
    infer_instance
  refine ⟨g', hg', locallyOfFiniteType_of_comp g' (integralComponentAt _).subschemeι,
    (integralComponentAt (g.base (genericPoint T))).subschemeι.isClosedEmbedding.injective <|
      (congrArg (fun h : T ⟶ Y ↦ h.base (genericPoint T)) hg').trans
        (genericPointOf_integralComponentAt _).symm⟩

attribute [local instance] isIntegral_integralComponentAt in
/-- A rule killing `[Z_y]` kills the fundamental cycle of every nonempty open of `Z_y`. -/
theorem CycleCapRule.cap_opensι_integralComponentAt_fundamentalCycle_eq_zero
    (d : CycleCapRule C sY p r) (y : Y)
    (hZ : d.cap (integralComponentAt y).subschemeι (relativeDimension C.dimensionFunction sY y)
      (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _) = 0)
    (V : (integralComponentAt y).subscheme.Opens) [Nonempty V] {m : ℤ}
    (hm : relativeDimension C.dimensionFunction sY y = m) :
    d.cap (V.ι ≫ (integralComponentAt y).subschemeι) m
      (fundamentalCycle C ((V.ι ≫ (integralComponentAt y).subschemeι) ≫ sY) m) = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun v ↦ ?_)
  rw [d.cap_val_congr (V.ι ≫ (integralComponentAt y).subschemeι) rfl _
    (cycleGroupRestrict C ((integralComponentAt y).subschemeι ≫ sY)
      ((V.ι ≫ (integralComponentAt y).subschemeι) ≫ sY) V.ι (Category.assoc _ _ _).symm
      m (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) m))
    (cycleGroupRestrict_fundamentalCycle_val C _ V
      (by rw [schemeDeltaDimension_integralComponentAt C sY y, hm]) _ _).symm,
    d.cap_cycleGroupRestrict_apply, d.cap_val_congr (integralComponentAt y).subschemeι hm.symm _
      (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _) (by rw [hm]), hZ]
  rfl

/-- A rule killing the fundamental cycle of `T` kills that of every flat `T' ⟶ T` of some
relative dimension. -/
theorem CycleCapRule.cap_fundamentalCycle_eq_zero_of_flat (d : CycleCapRule C sY p r)
    {T T' : Scheme.{u}} (f : T ⟶ Y) [LocallyOfFiniteType f] (h : T' ⟶ T) [LocallyOfFiniteType h]
    [Flat h] (dd : ℕ) (hrel : AlgebraicGeometry.RelativeDimension h dd) (m k : ℤ)
    (hm : schemeDeltaDimension C (f ≫ sY) ≤ (m : EInt)) (hk : k = m + dd)
    (hf : d.cap f m (fundamentalCycle C (f ≫ sY) m) = 0) :
    d.cap (h ≫ f) k (fundamentalCycle C ((h ≫ f) ≫ sY) k) = 0 := by
  subst hk
  refine Subtype.ext ?_
  rw [d.cap_val_congr (h ≫ f) rfl _
      (flatPullback C ((h ≫ f) ≫ sY) (f ≫ sY) h (Category.assoc _ _ _).symm dd hrel m
        (fundamentalCycle C (f ≫ sY) m))
      (by rw [flatPullback_fundamentalCycle C _ _ h _ dd hrel m hm]),
    d.cap_flatPullback f h dd hrel m, hf, map_zero]
  rfl

/-- **Generic determination.** Let `d` be a rule compatible with proper pushforward and flat
pullback with generic support, killing `[Z_y]` for every integral closed subscheme `Z_y ⊆ Y`.
Then `d` kills `[T]` for every integral test scheme `T`.

Over the generic point of `T` the coefficients are computed after restricting to a dense open of
`T` flat of some relative dimension over a dense open of `Z_y`, `y` the image of the generic point
of `T` (generic flatness, Stacks 052A): there `[T]` is the flat pullback of `[Z_y]`. -/
theorem CycleCapRule.cap_fundamentalCycle_eq_zero_of_hasGenericSupport (d : CycleCapRule C sY p r)
    (hgen : d.HasGenericSupport)
    (hZ : ∀ y : Y, d.cap (integralComponentAt y).subschemeι
      (relativeDimension C.dimensionFunction sY y)
      (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _) = 0)
    {T : Scheme.{u}} [IsIntegral T] (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (hk : schemeDeltaDimension C (g ≫ sY) = (k : EInt)) :
    d.cap g k (fundamentalCycle C (g ≫ sY) k) = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  refine (em ((pullback.snd p g).base w = genericPoint T)).elim (fun hw ↦ ?_) (hgen g k hk w)
  set y := g.base (genericPoint T)
  have := isIntegral_integralComponentAt y
  have : IsLocallyNoetherian (integralComponentAt y).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt y).subschemeι ≫ sY)
  obtain ⟨g', hg', _, hdom⟩ := exists_lift_integralComponentAt_genericPoint g (y := y) rfl
  obtain ⟨U', V', hle, dd, hU', hflat, hrel⟩ :=
    AlgebraicGeometry.exists_nonempty_opens_flat_relativeDimension g' hdom
  have : Nonempty U' := ⟨⟨_, hU'.some_mem⟩⟩
  have hηU' : genericPoint T ∈ U' :=
    ((genericPoint_spec T).mem_open_set_iff U'.2).mpr (by simpa using hU')
  have : Nonempty V' := ⟨⟨g'.base (genericPoint T), hle hηU'⟩⟩
  set h := g'.resLE V' U' hle with hhdef
  have hpres : U'.ι ≫ g = h ≫ V'.ι ≫ (integralComponentAt y).subschemeι := by
    rw [← hg', ← Category.assoc, ← Category.assoc, hhdef, Scheme.Hom.resLE_comp_ι]
  have hkV : schemeDeltaDimension C ((V'.ι ≫ (integralComponentAt y).subschemeι) ≫ sY) =
      ((relativeDimension C.dimensionFunction sY y : ℤ) : EInt) := by
    simpa [Category.assoc] using
      schemeDeltaDimension_opensι_comp C _ V' (schemeDeltaDimension_integralComponentAt C sY y)
  have hkU : schemeDeltaDimension C ((h ≫ V'.ι ≫ (integralComponentAt y).subschemeι) ≫ sY) =
      (k : EInt) := by
    exact (schemeDeltaDimension_congr C (congrArg (· ≫ sY) hpres)).symm.trans
      ((schemeDeltaDimension_congr C (Category.assoc _ _ _)).trans
        (schemeDeltaDimension_opensι_comp C _ U' hk))
  have hadd := schemeDeltaDimension_eq_add_of_flat C
    ((h ≫ V'.ι ≫ (integralComponentAt y).subschemeι) ≫ sY)
    ((V'.ι ≫ (integralComponentAt y).subschemeι) ≫ sY) h (by simp) dd hrel hkV
  have hkd : relativeDimension C.dimensionFunction sY y = k - dd := by
    rw [hkU] at hadd
    have := WithBotTop.coe_injective hadd
    omega
  obtain ⟨w', hw'⟩ := d.exists_cap_cycleGroupRestrict_eq g U' k _ w (hw ▸ hηU')
  rw [← hw',
    d.cap_val_congr (U'.ι ≫ g) rfl _ (fundamentalCycle C ((U'.ι ≫ g) ≫ sY) k)
      (cycleGroupRestrict_fundamentalCycle_val C (g ≫ sY) U' hk _ _),
    d.cap_congr_hom hpres k _
      (fundamentalCycle C ((h ≫ V'.ι ≫ (integralComponentAt y).subschemeι) ≫ sY) k)
      (fundamentalCycle_val_congr C (by rw [hpres]) k),
    d.cap_fundamentalCycle_eq_zero_of_flat (V'.ι ≫ (integralComponentAt y).subschemeι) h dd hrel
      (k - dd) k (le_of_eq (by rw [hkV, hkd])) (by ring)
      (d.cap_opensι_integralComponentAt_fundamentalCycle_eq_zero y (hZ y) V' hkd)]
  rfl

/-- **A rule with generic support is the operation of its family.** A rule compatible with
proper pushforward and flat pullback, whose cycles `c ∩ [T]` live over the generic points of
integral test schemes `T`, is `g ↦ g^*α ∩ -` for its family `α`
(`Stacks.Chow.CycleCapRule.genericFamily`). -/
theorem CycleCapRule.cap_eq_relativeCycleCap_of_hasGenericSupport (c : CycleCapRule C sY p r)
    (hc : c.HasGenericSupport) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ)
    (β : CycleGroup C (g ≫ sY) e) :
    c.cap g e β = relativeCycleCap C sY p r c.genericFamily g e β := by
  have hd := (c - CycleCapRule.ofFamily C sY p r
      c.genericFamily).cap_eq_zero_of_cap_fundamentalCycle_eq_zero
    (fun g _ k hk ↦ CycleCapRule.cap_fundamentalCycle_eq_zero_of_hasGenericSupport _
      (hc.sub (CycleCapRule.hasGenericSupport_ofFamily _))
      (fun y ↦ by rw [CycleCapRule.sub_cap, AddMonoidHom.sub_apply,
        c.cap_integralComponentAt_eq hc y, sub_self]) g k hk) g e β
  rwa [CycleCapRule.sub_cap, AddMonoidHom.sub_apply, sub_eq_zero] at hd

/-- **Stacks 0H6G, the identity of operations.** A rule as in Stacks 0H6G is the operation
`g ↦ g^*α ∩ -` of its family of cycles on fibres. -/
theorem CompatibleCycleCapRule.cap_eq_relativeCycleCap (c : CompatibleCycleCapRule C sY p r)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ)
    (β : CycleGroup C (g ≫ sY) e) :
    c.cap g e β = relativeCycleCap C sY p r c.genericFamily g e β :=
  c.toCycleCapRule.cap_eq_relativeCycleCap_of_hasGenericSupport c.hasGenericSupport g e β

end Stacks.Chow

end
