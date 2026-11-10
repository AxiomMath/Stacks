module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleGeneric
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FamilyCoeff
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictedBaseChange
public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward

/-!
# The family of cycles on fibres of a rule of Stacks 0H6G

Let `c` be a rule as in Stacks 0H6G. For a point `y ∈ Y` let `Z_y ⊆ Y` be the integral closed
subscheme with generic point `y`. The cycle `c ∩ [Z_y]` on `Z_y ×_Y X` restricts over the generic
point of `Z_y` to an `r`-cycle on the fibre `X_y`; these cycles form the family of `r`-cycles on
the fibres of `X/Y` attached to `c`, `Stacks.Chow.CycleCapRule.genericFamily`. Its defining
property is that on every `Z_y` the rule and the operation `g ↦ g^*α ∩ -` of the family agree on
`[Z_y]`: over the generic point of `Z_y` by construction, and away from it because `c ∩ [Z_y]`
has no components there (Stacks 0H6G, `Stacks.Chow.CycleCapRule.HasGenericSupport`).

## Main definitions

* `Stacks.Chow.familyOfCoeff` — the family of cycles on fibres with a prescribed coefficient
  function on the total space.
* `Stacks.Chow.CycleCapRule.HasGenericSupport` — `c ∩ [T]` lives over the generic point of an
  integral test scheme `T`.
* `Stacks.Chow.CycleCapRule.genericFamily` — the family of cycles on fibres attached to a rule.

## Main results

* `Stacks.Chow.CycleCapRule.cap_pointClosure_eq` — on each `Z_y` the rule and the operation of
  its family agree on the fundamental cycle.

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Families of cycles with a prescribed coefficient function -/

section FamilyOfCoeff

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)

/-- The relative dimension of a point is that of its image plus the residue transcendence
degree. -/
theorem relativeDimension_eq_add_residueTrdeg {T : Scheme.{u}} (δ : DimensionFunction T)
    (q : S ⟶ T) (x : S) :
    relativeDimension δ q x = δ (q x) + ((residueTrdeg q x).toNat : ℤ) :=
  rfl

/-- **A family of cycles on fibres from its coefficients.** A function `φ` on `X` whose
restriction to each fibre has locally finite support, and which is nonzero only at points of
residue transcendence degree `r`, is the coefficient function of a family of `r`-cycles on the
fibres of `X/S`. -/
def familyOfCoeff (φ : X → ℤ) (hfin : ∀ s : S, LocallyFiniteSupport (φ ∘ f.fiberι s))
    (hdim : ∀ x : X, φ x ≠ 0 → residueTrdeg f x = r) : FamilyOfCycles f r := fun s ↦
  ⟨⟨φ ∘ f.fiberι s, fun _ _ ↦ trivial, fun z _ ↦ hfin s z⟩, by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro z hz
    rw [relativeDimension_eq_add_residueTrdeg, fieldChowSituation_dimensionFunction_eq_zero,
      residueTrdeg_fiberToSpecResidueField, hdim _ hz]
    simp⟩

/-- The coefficient function of the family with prescribed coefficients is the prescribed
function. -/
@[simp]
theorem familyCoeff_familyOfCoeff (φ : X → ℤ)
    (hfin : ∀ s : S, LocallyFiniteSupport (φ ∘ f.fiberι s))
    (hdim : ∀ x : X, φ x ≠ 0 → residueTrdeg f x = r) :
    familyCoeff f r (familyOfCoeff f r φ hfin hdim) = φ := by
  funext x
  exact congrArg φ (Scheme.Hom.fiberι_asFiber f x)

/-- Along a base change whose residue-field maps are isomorphisms, the coefficient function of
the base-changed family is that of the family, read through the projection to `X`. -/
theorem familyCoeff_baseChangeFamily_of_isIso {S' : Scheme.{u}} (g : S' ⟶ S)
    (α : FamilyOfCycles f r) (z : ↥(pullback f g))
    [IsIso (g.residueFieldMap ((pullback.snd f g).base z))] :
    familyCoeff (pullback.snd f g) r (baseChangeFamily f g r α) z =
      familyCoeff f r α ((pullback.fst f g).base z) := by
  change (baseChangeFamily f g r α ((pullback.snd f g).base z) : AlgebraicCycle _ ℤ)
      ((pullback.snd f g).asFiber z) = _
  rw [baseChangeFamily_apply_of_isIso_residueFieldMap, familyCoeff_restrictedFiberMap,
    Scheme.Hom.fiberι_asFiber]

end FamilyOfCoeff

/-! ### The family of a rule -/

section GenericFamily

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {p : X ⟶ Y} [LocallyOfFiniteType p] {r : ℕ}

/-- **The conclusion of Stacks 0H6G's key step**, as a property of a rule: for every integral test
scheme `T`, the cycle `c ∩ [T]` has no coefficient over a point of `T` other than its generic
point. -/
def CycleCapRule.HasGenericSupport (c : CycleCapRule C sY p r) : Prop :=
  ∀ {T : Scheme.{u}} [IsIntegral T] (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ),
    schemeDeltaDimension C (g ≫ sY) = (k : EInt) → ∀ w : ↥(pullback p g),
      (pullback.snd p g).base w ≠ genericPoint T →
        (c.cap g k (fundamentalCycle C (g ≫ sY) k)).1 w = 0

/-- A rule as in Stacks 0H6G has generic support. -/
theorem CompatibleCycleCapRule.hasGenericSupport (c : CompatibleCycleCapRule C sY p r) :
    c.toCycleCapRule.HasGenericSupport :=
  fun g _ _ hk w hw ↦ c.cap_fundamentalCycle_apply_eq_zero g hk w hw

/-- The rule `g ↦ g^*α ∩ -` of a family has generic support. -/
theorem CycleCapRule.hasGenericSupport_ofFamily (α : FamilyOfCycles p r) :
    (CycleCapRule.ofFamily C sY p r α).HasGenericSupport := by
  intro T _ g _ k hk w hw
  change (relativeCycleCap C sY p r α g k _).1 w = 0
  rw [relativeCycleCap_apply, capCoeff, fundamentalCycle_apply_of_isIntegral C _ hk,
    ite_eq_right hw, zero_mul]

/-- Generic support is preserved by differences. -/
theorem CycleCapRule.HasGenericSupport.sub {c₁ c₂ : CycleCapRule C sY p r}
    (h₁ : c₁.HasGenericSupport) (h₂ : c₂.HasGenericSupport) : (c₁ - c₂).HasGenericSupport := by
  intro T _ g _ k hk w hw
  change (c₁.cap g k _ - c₂.cap g k _).1 w = 0
  rw [AddSubgroup.coe_sub]
  change (c₁.cap g k _).1 w - (c₂.cap g k _).1 w = 0
  rw [h₁ g k hk w hw, h₂ g k hk w hw, sub_zero]

omit [LocallyOfFiniteType p] in
/-- The point of `Z ×_Y X`, where `Z` is the integral closed subscheme with generic point `p x`,
lying over `x` and over the generic point of `Z`. -/
theorem exists_pointClosure_lift (x : X) :
    haveI := isIntegral_integralComponentAt (p x)
    ∃ z : ↥(pullback p (integralComponentAt (p x)).subschemeι),
      (pullback.fst p _).base z = x ∧ (pullback.snd p _).base z = genericPoint _ :=
  have := isIntegral_integralComponentAt (p x)
  Scheme.Pullback.exists_preimage_pullback x _ (genericPointOf_integralComponentAt (p x)).symm

/-- The coefficient at `x ∈ X` of the family attached to a rule: the coefficient of
`c ∩ [Z]`, for `Z` the integral closed subscheme with generic point `p x`, at the point of
`Z ×_Y X` over `x` and over the generic point of `Z`. -/
def CycleCapRule.genericCoeff (c : CycleCapRule C sY p r) (x : X) : ℤ :=
  (c.cap (integralComponentAt (p x)).subschemeι (relativeDimension C.dimensionFunction sY (p x))
    (fundamentalCycle C ((integralComponentAt (p x)).subschemeι ≫ sY) _)).1
    (exists_pointClosure_lift x).choose

/-- The coefficient of the family attached to a rule may be read at any point lying over `x` and
the generic point of the integral closed subscheme with generic point `p x`. -/
theorem CycleCapRule.genericCoeff_eq (c : CycleCapRule C sY p r) {x : X} {y : Y} (h : p x = y)
    (z : ↥(pullback p (integralComponentAt y).subschemeι)) (hz : (pullback.fst p _).base z = x) :
    c.genericCoeff x = (c.cap (integralComponentAt y).subschemeι
      (relativeDimension C.dimensionFunction sY y)
      (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _)).1 z := by
  subst h
  rw [CycleCapRule.genericCoeff]
  congr 1
  apply (pullback.fst p (integralComponentAt (p x)).subschemeι).isClosedEmbedding.injective
  rw [(exists_pointClosure_lift x).choose_spec.1, hz]

/-- A point carrying a nonzero coefficient of the family attached to a rule has residue
transcendence degree `r`: the cycle `c ∩ [Z]` has delta-dimension `r` plus that of `Z`. -/
theorem CycleCapRule.residueTrdeg_eq_of_genericCoeff_ne_zero (c : CycleCapRule C sY p r) (x : X)
    (hx : c.genericCoeff x ≠ 0) : residueTrdeg p x = r := by
  have := isIntegral_integralComponentAt (p x)
  obtain ⟨hz₁, -⟩ := (exists_pointClosure_lift (p := p) x).choose_spec
  have hδ := relativeDimension_eq_of_cycleGroup_apply_ne_zero C _ _ _ hx
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction
    (pullback.fst p (integralComponentAt (p x)).subschemeι) (p ≫ sY), hz₁] at hδ
  obtain ⟨n, hn⟩ := exists_residueTrdeg_eq_natCast p x
  have hcomp := relativeDimension_comp_add_of_trdeg C.dimensionFunction p sY x n
    (by change (residueTrdeg p x).toNat = n; rw [hn]; simp)
  rw [hcomp] at hδ
  rw [hn]
  exact congrArg _ (by omega)

/-- The coefficient function of the family attached to a rule has locally finite support on each
fibre: on the fibre over `y` it is the coefficient function of `c ∩ [Z_y]` read through an
injective map to `Z_y ×_Y X` lying over the inclusion of the fibre. -/
theorem CycleCapRule.locallyFiniteSupport_genericCoeff (c : CycleCapRule C sY p r) (y : Y) :
    LocallyFiniteSupport (c.genericCoeff ∘ p.fiberι y) := by
  have := isIntegral_integralComponentAt y
  have hlift : ∀ z : p.fiber y, ∃ w : ↥(pullback p (integralComponentAt y).subschemeι),
      (pullback.fst p _).base w = p.fiberι y z ∧ (pullback.snd p _).base w = genericPoint _ :=
    fun z ↦ Scheme.Pullback.exists_preimage_pullback _ _
      (((p.fiberHomeo y z).2).trans (genericPointOf_integralComponentAt y).symm)
  choose L hL₁ hL₂ using hlift
  have hval : ∀ z, c.genericCoeff (p.fiberι y z) = (c.cap (integralComponentAt y).subschemeι
      (relativeDimension C.dimensionFunction sY y)
      (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _)).1 (L z) :=
    fun z ↦ c.genericCoeff_eq (p.fiberHomeo y z).2 (L z) (hL₁ z)
  have hinj : Function.Injective L := fun z₁ z₂ h ↦
    (p.fiberι y).isEmbedding.injective (by rw [← hL₁, ← hL₁, h])
  set γ := (c.cap (integralComponentAt y).subschemeι (relativeDimension C.dimensionFunction sY y)
    (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _)).1 with hγ
  intro z
  obtain ⟨N', hN', hfin⟩ := (Function.locallyFinsupp.locallyFiniteSupport γ :
    LocallyFiniteSupport (γ : _ → ℤ)) (L z)
  rw [(pullback.fst p
      (integralComponentAt y).subschemeι).isClosedEmbedding.isInducing.nhds_eq_comap,
    Filter.mem_comap, hL₁] at hN'
  obtain ⟨O, hO, hON'⟩ := hN'
  refine ⟨p.fiberι y ⁻¹' O, (p.fiberι y).continuous.continuousAt.preimage_mem_nhds hO, ?_⟩
  refine ((hfin.preimage hinj.injOn).subset) fun z' hz' ↦ ⟨hON' ?_, ?_⟩
  · change (pullback.fst p _).base (L z') ∈ O
    rw [hL₁]
    exact hz'.1
  · change γ (L z') ≠ 0
    rw [← hval]
    exact hz'.2

/-- **The family of cycles on fibres attached to a rule.** Its member over `y ∈ Y` is the
restriction of `c ∩ [Z_y]` to the fibre over the generic point of `Z_y`, read on `X_y`. -/
def CycleCapRule.genericFamily (c : CycleCapRule C sY p r) : FamilyOfCycles p r :=
  familyOfCoeff p r c.genericCoeff c.locallyFiniteSupport_genericCoeff
    c.residueTrdeg_eq_of_genericCoeff_ne_zero

/-- **The defining property of the family of a rule.** On the integral closed subscheme `Z_y`
with generic point `y`, the rule and the operation of its family agree on `[Z_y]`, as soon as the
rule has generic support. -/
theorem CycleCapRule.cap_integralComponentAt_eq (c : CycleCapRule C sY p r)
    (hc : c.HasGenericSupport) (y : Y) :
    c.cap (integralComponentAt y).subschemeι (relativeDimension C.dimensionFunction sY y)
        (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _) =
      (CycleCapRule.ofFamily C sY p r c.genericFamily).cap (integralComponentAt y).subschemeι
        (relativeDimension C.dimensionFunction sY y)
        (fundamentalCycle C ((integralComponentAt y).subschemeι ≫ sY) _) := by
  have := isIntegral_integralComponentAt y
  have hk := schemeDeltaDimension_integralComponentAt C sY y
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  change _ = (relativeCycleCap C sY p r c.genericFamily _ _ _).1 z
  rw [relativeCycleCap_apply, capCoeff, fundamentalCycle_apply_of_isIntegral C _ hk]
  split_ifs with hz
  · have := residueFieldMap_isIso_of_isClosedImmersion (integralComponentAt y).subschemeι
      ((pullback.snd p (integralComponentAt y).subschemeι).base z)
    have hfc := familyCoeff_baseChangeFamily_of_isIso p r (integralComponentAt y).subschemeι
      c.genericFamily z
    change _ = 1 * familyCoeff _ r _ z
    rw [one_mul, hfc, CycleCapRule.genericFamily, familyCoeff_familyOfCoeff]
    refine (c.genericCoeff_eq ?_ z rfl).symm
    change (pullback.fst p _ ≫ p).base z = y
    rw [pullback.condition, Scheme.Hom.comp_apply, hz]
    exact genericPointOf_integralComponentAt y
  · rw [zero_mul]
    exact hc _ _ hk z hz

end GenericFamily

end Stacks.Chow

end
