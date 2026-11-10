module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionLocal

/-!
# Restricting a rule compatible with pushforward, pullback and Gysin maps to an open of the source

Let `c` be a rule as in Stacks 0H6G for a morphism `p : X ⟶ Y` locally of finite type over the
base: to every test scheme `g : T ⟶ Y` and every `e ∈ ℤ` it assigns an operation
`c ∩ - : Z_e(T) ⟶ Z_{r + e}(T ×_Y X)`, compatible with proper pushforward, flat pullback, and
Gysin maps. For an open immersion `j : U ⟶ X`, the base change `T ×_Y U ⟶ T ×_Y X` is an open
immersion, and restricting the cycles `c ∩ β` to it gives a rule of the same kind for
`j ≫ p : U ⟶ Y`. This is the restriction `c|_U` to an open subscheme of the source used in the
proof of Stacks 0H6G.

## Main definitions

* `Stacks.Chow.sourceRestrictionMap` — the open immersion `T ×_Y U ⟶ T ×_Y X`.
* `Stacks.Chow.CycleCapRule.restrictSource` — the restriction to `U ⊆ X` of a rule compatible
  with proper pushforward and flat pullback.
* `Stacks.Chow.CompatibleCycleCapRule.restrictSource` — the restriction to `U ⊆ X` of a rule as in
  Stacks 0H6G.

## Main results

* `Stacks.Chow.CycleCapRule.restrictSource_cap_apply` — the coefficients of the restricted rule
  are those of `c` at the image points in `T ×_Y X`.
* `Stacks.Chow.isPullback_sourceRestrictionMap_bivariantBaseChangeMap` — the comparison maps for
  two test schemes `T' ⟶ T` form a cartesian square with the maps of base changes.

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The comparison open immersion -/

section Map

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

/-- The comparison map `T ×_Y U ⟶ T ×_Y X` between the base changes of `j ≫ p` and of `p` along
a test scheme `g : T ⟶ Y`, induced by `j : U ⟶ X`. -/
def sourceRestrictionMap {U T : Scheme.{u}} (j : U ⟶ X) (g : T ⟶ Y) :
    pullback (j ≫ p) g ⟶ pullback p g :=
  pullback.map (j ≫ p) g p g j (𝟙 T) (𝟙 Y) (by simp) (by simp)

/-- The comparison map lies over `j : U ⟶ X`. -/
@[reassoc (attr := simp)]
theorem sourceRestrictionMap_fst {U T : Scheme.{u}} (j : U ⟶ X) (g : T ⟶ Y) :
    sourceRestrictionMap (p := p) j g ≫ pullback.fst p g = pullback.fst (j ≫ p) g ≫ j := by
  simp [sourceRestrictionMap]

/-- The comparison map lies over the test scheme. -/
@[reassoc (attr := simp)]
theorem sourceRestrictionMap_snd {U T : Scheme.{u}} (j : U ⟶ X) (g : T ⟶ Y) :
    sourceRestrictionMap (p := p) j g ≫ pullback.snd p g = pullback.snd (j ≫ p) g := by
  simp [sourceRestrictionMap]

/-- The comparison map `T ×_Y U ⟶ T ×_Y X` is the base change of `j : U ⟶ X` along the projection
`T ×_Y X ⟶ X`. -/
theorem isPullback_sourceRestrictionMap {U T : Scheme.{u}} (j : U ⟶ X) (g : T ⟶ Y) :
    IsPullback (pullback.fst (j ≫ p) g) (sourceRestrictionMap j g) j (pullback.fst p g) :=
  IsPullback.of_bot (by rw [sourceRestrictionMap_snd]; exact IsPullback.of_hasPullback (j ≫ p) g)
    (sourceRestrictionMap_fst j g).symm (IsPullback.of_hasPullback p g)

/-- The comparison map along an open immersion is an open immersion. -/
instance isOpenImmersion_sourceRestrictionMap {U T : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : T ⟶ Y) : IsOpenImmersion (sourceRestrictionMap (p := p) j g) :=
  MorphismProperty.of_isPullback (isPullback_sourceRestrictionMap j g)
    (P := @IsOpenImmersion) inferInstance

/-- The comparison map is a morphism over the base. -/
theorem sourceRestrictionMap_comp_structure {S U T : Scheme.{u}} (j : U ⟶ X) (g : T ⟶ Y)
    (sY : Y ⟶ S) :
    sourceRestrictionMap j g ≫ pullback.fst p g ≫ p ≫ sY =
      pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY := by
  simp

/-- The comparison maps commute with the maps of base changes induced by `h : T' ⟶ T`. -/
theorem sourceRestrictionMap_comp_bivariantBaseChangeMap {U T T' : Scheme.{u}} (j : U ⟶ X)
    (g : T ⟶ Y) (h : T' ⟶ T) :
    sourceRestrictionMap j (h ≫ g) ≫ bivariantBaseChangeMap p g h =
      bivariantBaseChangeMap (j ≫ p) g h ≫ sourceRestrictionMap j g := by
  apply pullback.hom_ext <;> simp

/-- The comparison maps for two test schemes `h : T' ⟶ T` and the maps of base changes induced by
`h` form a cartesian square. -/
theorem isPullback_sourceRestrictionMap_bivariantBaseChangeMap {U T T' : Scheme.{u}}
    (j : U ⟶ X) (g : T ⟶ Y) (h : T' ⟶ T) :
    IsPullback (sourceRestrictionMap j (h ≫ g)) (bivariantBaseChangeMap (j ≫ p) g h)
      (bivariantBaseChangeMap p g h) (sourceRestrictionMap j g) :=
  IsPullback.of_bot
    (by
      rw [bivariantBaseChangeMap_fst, bivariantBaseChangeMap_fst]
      exact (isPullback_sourceRestrictionMap j (h ≫ g)).flip)
    (sourceRestrictionMap_comp_bivariantBaseChangeMap j g h)
    (isPullback_sourceRestrictionMap j g).flip

end Map

section Rule

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {p : X ⟶ Y} [LocallyOfFiniteType p] {r : ℕ}

namespace CycleCapRule

variable (c : CycleCapRule C sY p r) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The operation of the restriction of a rule to an open `j : U ⟶ X` of the source on a test
scheme `g : T ⟶ Y`: the operation of the rule at `g`, restricted along the open immersion
`T ×_Y U ⟶ T ×_Y X`. -/
def restrictSourceCap {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ) :
    CycleGroup C (g ≫ sY) e →+
      CycleGroup C (pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY) ((r : ℤ) + e) :=
  (cycleGroupRestrict C (pullback.fst p g ≫ p ≫ sY) (pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY)
    (sourceRestrictionMap j g) (sourceRestrictionMap_comp_structure j g sY) ((r : ℤ) + e)).comp
    (c.cap g e)

/-- The coefficients of the restricted operation are those of the operation of the rule at the
image points. -/
theorem restrictSourceCap_apply {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ)
    (β : CycleGroup C (g ≫ sY) e) (z : ↥(pullback (j ≫ p) g)) :
    (c.restrictSourceCap j g e β).1 z = (c.cap g e β).1 ((sourceRestrictionMap j g).base z) :=
  rfl

/-- **Stacks 0H6B for the rule restricted to an open of the source.** -/
theorem properPushforward_restrictSourceCap {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (e : ℤ) (β : CycleGroup C ((h ≫ g) ≫ sY) e) :
    properPushforward C (pullback.fst (j ≫ p) (h ≫ g) ≫ (j ≫ p) ≫ sY)
        (pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY) (bivariantBaseChangeMap (j ≫ p) g h)
        (bivariantBaseChangeMap_comp_structure sY (j ≫ p) g h) ((r : ℤ) + e)
        (c.restrictSourceCap j (h ≫ g) e β) =
      c.restrictSourceCap j g e
        (properPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (Category.assoc h g sY).symm e β) := by
  change _ = cycleGroupRestrict C _ _ (sourceRestrictionMap j g)
    (sourceRestrictionMap_comp_structure j g sY) _
    (c.cap g e (properPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (Category.assoc h g sY).symm e β))
  rw [← c.properPushforward_cap g h e β]
  exact (cycleGroupRestrict_properPushforward C _ _ _ _ (bivariantBaseChangeMap p g h)
    (bivariantBaseChangeMap_comp_structure sY p g h) (sourceRestrictionMap j (h ≫ g))
    (sourceRestrictionMap_comp_structure j (h ≫ g) sY) (sourceRestrictionMap j g)
    (sourceRestrictionMap_comp_structure j g sY) (bivariantBaseChangeMap (j ≫ p) g h)
    (bivariantBaseChangeMap_comp_structure sY (j ≫ p) g h)
    (isPullback_sourceRestrictionMap_bivariantBaseChangeMap j g h) _ _).symm

/-- **Stacks 0H68 for the rule restricted to an open of the source.** -/
theorem restrictSourceCap_flatPullback {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension h d) (e : ℤ) (β : CycleGroup C (g ≫ sY) e) :
    letI : LocallyOfFiniteType (bivariantBaseChangeMap (j ≫ p) g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (j ≫ p) g h)
        (P := @LocallyOfFiniteType) inferInstance
    letI : Flat (bivariantBaseChangeMap (j ≫ p) g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (j ≫ p) g h)
        (P := @Flat) inferInstance
    (c.restrictSourceCap j (h ≫ g) (e + d)
        (flatPullback C ((h ≫ g) ≫ sY) (g ≫ sY) h (Category.assoc h g sY).symm d hd e β)).1 =
      (flatPullback C (pullback.fst (j ≫ p) (h ≫ g) ≫ (j ≫ p) ≫ sY)
        (pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY) (bivariantBaseChangeMap (j ≫ p) g h)
        (bivariantBaseChangeMap_comp_structure sY (j ≫ p) g h) d
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap (j ≫ p) g h) hd)
        ((r : ℤ) + e) (c.restrictSourceCap j g e β)).1 := by
  let : LocallyOfFiniteType (bivariantBaseChangeMap (j ≫ p) g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (j ≫ p) g h)
      (P := @LocallyOfFiniteType) inferInstance
  let : Flat (bivariantBaseChangeMap (j ≫ p) g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (j ≫ p) g h)
      (P := @Flat) inferInstance
  let : LocallyOfFiniteType (bivariantBaseChangeMap p g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g h)
      (P := @LocallyOfFiniteType) inferInstance
  let : Flat (bivariantBaseChangeMap p g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap p g h) (P := @Flat)
      inferInstance
  have hflat := c.cap_flatPullback g h d hd e β
  have key := cycleGroupRestrict_flatPullback C (pullback.fst p (h ≫ g) ≫ p ≫ sY)
    (pullback.fst p g ≫ p ≫ sY) (pullback.fst (j ≫ p) (h ≫ g) ≫ (j ≫ p) ≫ sY)
    (pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY) (bivariantBaseChangeMap p g h)
    (bivariantBaseChangeMap_comp_structure sY p g h) d
    (AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_bivariantBaseChangeMap p g h) hd)
    (sourceRestrictionMap j (h ≫ g)) (sourceRestrictionMap_comp_structure j (h ≫ g) sY)
    (sourceRestrictionMap j g) (sourceRestrictionMap_comp_structure j g sY)
    (bivariantBaseChangeMap (j ≫ p) g h) (bivariantBaseChangeMap_comp_structure sY (j ≫ p) g h)
    (sourceRestrictionMap_comp_bivariantBaseChangeMap j g h)
    (AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_bivariantBaseChangeMap (j ≫ p) g h) hd) ((r : ℤ) + e) (c.cap g e β)
  refine (Function.locallyFinsuppWithin.ext fun z ↦ ?_).trans (congrArg Subtype.val key)
  rw [restrictSourceCap_apply, cycleGroupRestrict_apply, hflat]

end CycleCapRule

/-- **The restriction of a rule to an open of the source.** For an open immersion `j : U ⟶ X`, a
rule compatible with proper pushforward and flat pullback for `p : X ⟶ Y` restricts to one for
`j ≫ p : U ⟶ Y`: on a test scheme `g : T ⟶ Y` it is the operation at `g`, restricted along the
open immersion `T ×_Y U ⟶ T ×_Y X`. -/
def CycleCapRule.restrictSource (c : CycleCapRule C sY p r) {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : CycleCapRule C sY (j ≫ p) r where
  cap g _ e := c.restrictSourceCap j g e
  properPushforward_cap g _ h _ e β := c.properPushforward_restrictSourceCap j g h e β
  cap_flatPullback g _ h _ _ d hd e β := c.restrictSourceCap_flatPullback j g h d hd e β

/-- The operations of the rule restricted to an open of the source. -/
theorem CycleCapRule.restrictSource_cap (c : CycleCapRule C sY p r) {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ) :
    (c.restrictSource j).cap g e = c.restrictSourceCap j g e :=
  rfl

/-- The coefficients of the rule restricted to an open `U ⊆ X` of the source on a test scheme
`g : T ⟶ Y` are those of the rule at `g`, at the image points of `T ×_Y U ⟶ T ×_Y X`. -/
theorem CycleCapRule.restrictSource_cap_apply (c : CycleCapRule C sY p r) {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (e : ℤ) (β : CycleGroup C (g ≫ sY) e) (z : ↥(pullback (j ≫ p) g)) :
    ((c.restrictSource j).cap g e β).1 z = (c.cap g e β).1 ((sourceRestrictionMap j g).base z) :=
  rfl

/-- **Stacks 0H6E for the rule restricted to an open of the source, read in `T ×_Y U`.** The
restriction of a rule as in Stacks 0H6G to an open of the source commutes with the composites
`i_* ∘ i^*` of the Gysin maps on cycles. -/
theorem CompatibleCycleCapRule.restrictSourceCap_gysinCycleMapPushforward
    (c : CompatibleCycleCapRule C sY p r) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (e : ℤ) (β : CycleGroup C (g ≫ sY) (e + 1)) :
    c.toCycleCapRule.restrictSourceCap j g e (gysinCycleMapPushforward C (g ≫ sY) e L s htriv β) =
      gysinCycleMapPushforward C (pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY) ((r : ℤ) + e)
        (bivariantPullbackModule (j ≫ p) g L) (bivariantPullbackSection (j ≫ p) g L s)
        (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
          (pullback.snd (j ≫ p) g) L s htriv)
        (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm
          (c.toCycleCapRule.restrictSourceCap j g (e + 1) β)) := by
  have hm := sourceRestrictionMap_comp_structure (p := p) j g sY
  have htriv' := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
    (pullback.snd p g) L s htriv
  have htrivU := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
    (sourceRestrictionMap j g) (bivariantPullbackModule p g L)
    (bivariantPullbackSection p g L s) htriv'
  have htrivU' := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
    (pullback.snd (j ≫ p) g) L s htriv
  have hZ : Stacks.Divisors.zeroScheme (pullback (j ≫ p) g)
        ((Scheme.Modules.pullback (sourceRestrictionMap j g)).obj (bivariantPullbackModule p g L))
        (pullbackGlobalSections (sourceRestrictionMap j g) _
          (bivariantPullbackSection p g L s)) =
      Stacks.Divisors.zeroScheme (pullback (j ≫ p) g) (bivariantPullbackModule (j ≫ p) g L)
        (bivariantPullbackSection (j ≫ p) g L s) := by
    rw [Stacks.Divisors.zeroScheme_pullback (sourceRestrictionMap j g),
      Stacks.Divisors.zeroScheme_pullback, Stacks.Divisors.zeroScheme_pullback,
      ← Scheme.IdealSheafData.comap_comp, sourceRestrictionMap_snd]
  have h1 : (c.toCycleCapRule.restrictSourceCap j g e
        (gysinCycleMapPushforward C (g ≫ sY) e L s htriv β)).1 =
      (cycleGroupRestrict C (pullback.fst p g ≫ p ≫ sY)
        (sourceRestrictionMap j g ≫ pullback.fst p g ≫ p ≫ sY) (sourceRestrictionMap j g) rfl
        ((r : ℤ) + e)
        (gysinCycleMapPushforward C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e)
          (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s) htriv'
          (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm (c.cap g (e + 1) β)))).1 := by
    refine Function.locallyFinsuppWithin.ext fun z ↦ ?_
    rw [CycleCapRule.restrictSourceCap_apply, cycleGroupRestrict_apply,
      c.cap_gysinCycleMapPushforward g L s htriv e β]
  have h2 := congrArg Subtype.val (cycleGroupRestrict_gysinCycleMapPushforward C
    (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e) (bivariantPullbackModule p g L)
    (bivariantPullbackSection p g L s) htriv' (sourceRestrictionMap j g) htrivU
    (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm (c.cap g (e + 1) β)))
  have h3 := gysinCycleMapPushforward_congr_zeroScheme C
    (sourceRestrictionMap j g ≫ pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e) hZ htrivU htrivU'
  have h4 := gysinCycleMapPushforward_congr C
    (sourceRestrictionMap j g ≫ pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + e)
    (bivariantPullbackModule (j ≫ p) g L) (bivariantPullbackSection (j ≫ p) g L s) htrivU'
    (pullback.fst (j ≫ p) g ≫ (j ≫ p) ≫ sY) hm
    (cycleGroupRestrict C (pullback.fst p g ≫ p ≫ sY)
      (sourceRestrictionMap j g ≫ pullback.fst p g ≫ p ≫ sY) (sourceRestrictionMap j g) rfl
      ((r : ℤ) + e + 1)
      (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm (c.cap g (e + 1) β)))
    (cycleGroupCongr C _ (add_assoc (r : ℤ) e 1).symm
      (c.toCycleCapRule.restrictSourceCap j g (e + 1) β))
    (Function.locallyFinsuppWithin.ext fun z ↦ by
      rw [cycleGroupRestrict_apply]
      exact (CycleCapRule.restrictSourceCap_apply c.toCycleCapRule j g (e + 1) β z).symm)
  rw [h3] at h2
  exact Subtype.ext (h1.trans (h2.trans h4))

/-- **The restriction of a rule as in Stacks 0H6G to an open of the source.** For an open
immersion `j : U ⟶ X`, a rule compatible with proper pushforward, flat pullback and Gysin maps for
`p : X ⟶ Y` restricts to one for `j ≫ p : U ⟶ Y`. -/
def CompatibleCycleCapRule.restrictSource (c : CompatibleCycleCapRule C sY p r) {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : CompatibleCycleCapRule C sY (j ≫ p) r where
  toCycleCapRule := c.toCycleCapRule.restrictSource j
  cap_gysin g _ L _ s htriv e β :=
    (c.toCycleCapRule.restrictSource j).cap_gysin_of_cap_gysinCycleMapPushforward g L s htriv e β
      (c.restrictSourceCap_gysinCycleMapPushforward j g L s htriv e β)

/-- The underlying rule of the restriction to an open of the source is the restriction of the
underlying rule. -/
@[simp]
theorem CompatibleCycleCapRule.restrictSource_toCycleCapRule
    (c : CompatibleCycleCapRule C sY p r) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (c.restrictSource j).toCycleCapRule = c.toCycleCapRule.restrictSource j :=
  rfl

end Rule

end Stacks.Chow

end
