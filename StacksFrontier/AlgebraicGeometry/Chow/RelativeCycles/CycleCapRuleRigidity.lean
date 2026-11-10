module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleDetermination
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.MaximalDeltaComponent
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support

/-!
# Rigidity of the family of a rule of Stacks 0H6G

Let `c` be a rule as in Stacks 0H6G over an integral base `Y`. If its family of cycles on fibres
(`Stacks.Chow.CycleCapRule.genericFamily`) vanishes over the generic point of `Y`, it vanishes
everywhere. The proof descends along immediate specializations `y' ⤳ y` using the Gysin
compatibility for a function `φ` vanishing at `y` on an affine open of the closure of `y'`: the
coefficient of `[Z(φ)]` at `y` is nonzero, and the rule is the operation of its family
(`Stacks.Chow.CompatibleCycleCapRule.cap_eq_relativeCycleCap`), so the family vanishes over `y`.

This file also records how the family of a rule behaves under differences, for the operation of
a family, and under restriction of the rule along a test scheme.

## Main results

* `Stacks.Chow.CycleCapRule.genericFamily_sub`
* `Stacks.Chow.CycleCapRule.genericFamily_ofFamily`
* `Stacks.Chow.CompatibleCycleCapRule.genericFamily_restrict`
* `Stacks.Chow.CompatibleCycleCapRule.genericFamily_eq_zero_of_genericPoint`

## References

* [Stacks Project, Tag 0H6G](https://stacks.math.columbia.edu/tag/0H6G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Two families of cycles on fibres with the same coefficient function are equal. -/
theorem familyOfCycles_ext_familyCoeff {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℕ} {α β : FamilyOfCycles f r} (h : familyCoeff f r α = familyCoeff f r β) : α = β := by
  funext s
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  have := congrFun h (f.fiberι s z)
  rwa [familyCoeff_fiberι, familyCoeff_fiberι] at this

/-- The coefficient function of a family vanishes over a point whose member is zero. -/
theorem familyCoeff_eq_zero_of_apply_eq_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r : ℕ} (α : FamilyOfCycles f r) {s : S} (hs : α s = 0) {x : X}
    (hx : f x = s) : familyCoeff f r α x = 0 := by
  subst hx
  rw [familyCoeff, hs]
  rfl

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {p : X ⟶ Y} [LocallyOfFiniteType p] {r : ℕ}

/-- The coefficient function of the family of a rule. -/
theorem CycleCapRule.familyCoeff_genericFamily (c : CycleCapRule C sY p r) :
    familyCoeff p r c.genericFamily = c.genericCoeff :=
  familyCoeff_familyOfCoeff _ _ _ _ _

/-- The family of a difference of rules is the difference of the families. -/
theorem CycleCapRule.genericFamily_sub (c₁ c₂ : CycleCapRule C sY p r) :
    (c₁ - c₂).genericFamily = c₁.genericFamily - c₂.genericFamily := by
  refine familyOfCycles_ext_familyCoeff p (funext fun x ↦ ?_)
  rw [CycleCapRule.familyCoeff_genericFamily]
  change _ = (c₁.genericFamily (p x) - c₂.genericFamily (p x)).1 (p.asFiber x)
  rw [AddSubgroup.coe_sub]
  change _ = familyCoeff p r c₁.genericFamily x - familyCoeff p r c₂.genericFamily x
  rw [CycleCapRule.familyCoeff_genericFamily, CycleCapRule.familyCoeff_genericFamily]
  rfl

/-- The coefficients of `g^*α ∩ β` when the residue-field maps of `g` are isomorphisms. -/
private theorem relativeCycleCap_apply_of_isIso (α : FamilyOfCycles p r) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (β : CycleGroup C (g ≫ sY) k)
    (z : ↥(pullback p g)) [IsIso (g.residueFieldMap ((pullback.snd p g).base z))] :
    (relativeCycleCap C sY p r α g k β).1 z =
      β.1 ((pullback.snd p g).base z) * familyCoeff p r α ((pullback.fst p g).base z) := by
  rw [relativeCycleCap_apply, capCoeff, ← familyCoeff_baseChangeFamily_of_isIso]
  rfl

/-- The family of the operation `g ↦ g^*β ∩ -` of a family `β` is `β`. -/
theorem CycleCapRule.genericFamily_ofFamily (β : FamilyOfCycles p r) :
    (CycleCapRule.ofFamily C sY p r β).genericFamily = β := by
  refine familyOfCycles_ext_familyCoeff p (funext fun x ↦ ?_)
  rw [CycleCapRule.familyCoeff_genericFamily]
  have := isIntegral_integralComponentAt (p x)
  obtain ⟨hz₁, hz₂⟩ := (exists_pointClosure_lift (p := p) x).choose_spec
  have := residueFieldMap_isIso_of_isClosedImmersion (integralComponentAt (p x)).subschemeι
    ((pullback.snd p (integralComponentAt (p x)).subschemeι).base
      (exists_pointClosure_lift (p := p) x).choose)
  change (relativeCycleCap C sY p r β _ _ _).1 _ = _
  rw [relativeCycleCap_apply_of_isIso,
    fundamentalCycle_apply_of_isIntegral C _ (schemeDeltaDimension_integralComponentAt C sY _),
    ite_eq_left hz₂, one_mul, hz₁]

/-- Rules with the same operations have the same family. -/
theorem CycleCapRule.genericFamily_congr {c₁ c₂ : CycleCapRule C sY p r}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (e : ℤ)
      (β : CycleGroup C (g ≫ sY) e), (c₁.cap g e β).1 = (c₂.cap g e β).1) :
    c₁.genericFamily = c₂.genericFamily := by
  refine familyOfCycles_ext_familyCoeff p (funext fun x ↦ ?_)
  rw [CycleCapRule.familyCoeff_genericFamily, CycleCapRule.familyCoeff_genericFamily,
    CycleCapRule.genericCoeff, CycleCapRule.genericCoeff, h]

/-- **The family of a restricted rule is the base change of the family.** For a rule as in
Stacks 0H6G and a test scheme `w : T₀ ⟶ Y`, the family of the restriction of the rule to schemes
over `T₀` is the base change along `w` of the family of the rule. -/
theorem CompatibleCycleCapRule.genericFamily_restrict (c : CompatibleCycleCapRule C sY p r)
    {T₀ : Scheme.{u}} (w : T₀ ⟶ Y) [LocallyOfFiniteType w] :
    (c.restrict w).genericFamily = baseChangeFamily p w r c.genericFamily := by
  rw [← CycleCapRule.genericFamily_ofFamily (C := C) (sY := w ≫ sY)
    (baseChangeFamily p w r c.genericFamily)]
  refine CycleCapRule.genericFamily_congr fun h _ e β ↦ ?_
  refine Function.locallyFinsuppWithin.ext fun z ↦ ?_
  rw [CompatibleCycleCapRule.restrict_toCycleCapRule,
    CycleCapRule.restrict_cap_apply c.toCycleCapRule w h e β
      ((cycleGroupStructureCongr C (Category.assoc h w sY).symm e) β) rfl z,
    c.cap_eq_relativeCycleCap, relativeCycleCap_comp_apply]
  have hz : (pullbackLeftPullbackSndIso p w h).inv.base
      ((pullbackLeftPullbackSndIso p w h).hom.base z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [hz]
  rfl

/-- **Immediate generalizations exist.** On a scheme locally of finite type over the base, a point
with a proper generalization has one of delta-dimension exactly one more. -/
theorem exists_generalization_relativeDimension_eq_add_one (C : ChowSituation.{u})
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] {a t : T} (hat : a ⤳ t)
    (hne : a ≠ t) :
    ∃ t' : T, t' ⤳ t ∧ t' ≠ t ∧ relativeDimension C.dimensionFunction q t' =
      relativeDimension C.dimensionFunction q t + 1 := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction q
  set S : Set T := {t' | t' ⤳ t ∧ t' ≠ t} with hS
  obtain ⟨t', ht'S, hmin⟩ := (measure fun z : T ↦ (d z - d t).toNat).wf.has_min S ⟨a, hat, hne⟩
  refine ⟨t', ht'S.1, ht'S.2, ?_⟩
  rw [← hd, ← hd]
  refine d.step_immediate ⟨ht'S.1, ht'S.2, fun z h₁ h₂ ↦ ?_⟩
  by_contra hz
  push Not at hz
  have hzS : z ∈ S := ⟨h₂, hz.2⟩
  have hlt₁ := d.strictAnti_specializes h₁ (Ne.symm hz.1)
  have hlt₂ := d.strictAnti_specializes h₂ hz.2
  exact hmin z hzS (by
    change (d z - d t).toNat < (d t' - d t).toNat
    omega)

omit [LocallyOfFiniteType sY] in
/-- The relative dimension at a point of a scheme mapping to `Y` by an isomorphism followed by an
open immersion followed by a closed immersion is the relative dimension at its image. -/
theorem relativeDimension_iso_opens_closed {T V W : Scheme.{u}}
    (e : T ≅ V) (o : V ⟶ W) [IsOpenImmersion o] (i : W ⟶ Y) [IsClosedImmersion i]
    (z : T) :
    relativeDimension C.dimensionFunction ((e.hom ≫ o ≫ i) ≫ sY) z =
      relativeDimension C.dimensionFunction sY ((e.hom ≫ o ≫ i).base z) := by
  rw [Category.assoc, relativeDimension_comp_closedImmersion C.dimensionFunction e.hom,
    Category.assoc, relativeDimension_comp_isOpenImmersion,
    relativeDimension_comp_closedImmersion]
  rfl

attribute [local instance] isInvertible_unitModule

/-- **The rigidity step.** Let `c` be a rule as in Stacks 0H6G and let `t' ⤳ t` be a specialization
of points of `Y` with `δ(t') = δ(t) + 1`. If the family of `c` vanishes over `t'`, it vanishes
over `t`.

On an affine open `Spec R` of the closure of `t'` containing `t`, choose `φ ∈ R` nonzero vanishing
at `t`. The rule is the operation of its family, so `c ∩ [Spec R]` vanishes, and by the Gysin
compatibility so does `c ∩ [Z(φ)]`; its coefficient over `t` is the multiplicity of `t` in
`Z(φ)`, which is nonzero, times the coefficient of the family over `t`. -/
theorem CompatibleCycleCapRule.familyCoeff_eq_zero_of_specializes
    (c : CompatibleCycleCapRule C sY p r) {t t' : Y} (htt' : t' ⤳ t) (hne : t' ≠ t)
    (hδ : relativeDimension C.dimensionFunction sY t' =
      relativeDimension C.dimensionFunction sY t + 1)
    (ht' : ∀ x : X, p x = t' → familyCoeff p r c.genericFamily x = 0) (x₀ : X)
    (hx₀ : p x₀ = t) : familyCoeff p r c.genericFamily x₀ = 0 := by
  have := isIntegral_integralComponentAt t'
  -- the point `t` on the closure of `t'`, and an affine open around it
  obtain ⟨tl, htl⟩ : t ∈ Set.range (integralComponentAt t').subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact specializes_iff_mem_closure.mp htt'
  obtain ⟨V, hV, htV⟩ := exists_isAffineOpen_mem tl
  have : Nonempty V := ⟨⟨tl, htV⟩⟩
  set ΓV := Γ((integralComponentAt t').subscheme, V) with hΓV
  set e := hV.isoSpec with he
  set g' : Spec ΓV ⟶ Y :=
    e.inv ≫ V.ι ≫ (integralComponentAt t').subschemeι with hg'
  have : IsLocallyNoetherian (Spec ΓV) :=
    LocallyOfFiniteType.isLocallyNoetherian (g' ≫ sY)
  have : IsNoetherianRing ΓV :=
    isLocallyNoetherian_Spec.mp inferInstance
  have hgη : g'.base (genericPoint _) = t' := by
    rw [hg', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion e.inv, genericPoint_eq_of_isOpenImmersion V.ι]
    exact genericPointOf_integralComponentAt t'
  set th := e.hom.base ⟨tl, htV⟩ with hth
  have hgt : g'.base th = t := by
    rw [hg', hth, ← htl]
    change (e.hom ≫ e.inv ≫ V.ι ≫ (integralComponentAt t').subschemeι).base ⟨tl, htV⟩ = _
    rw [Iso.hom_inv_id_assoc]
    rfl
  have hrel : ∀ z, relativeDimension C.dimensionFunction (g' ≫ sY) z =
      relativeDimension C.dimensionFunction sY (g'.base z) :=
    relativeDimension_iso_opens_closed e.symm V.ι _
  have hk : schemeDeltaDimension C (g' ≫ sY) =
      ((relativeDimension C.dimensionFunction sY t + 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, hrel, hgη, hδ]
  -- a function vanishing at `t`
  have hthη : th ≠ genericPoint _ := fun h ↦ hne (by rw [← hgη, ← h, hgt])
  obtain ⟨φ, hφt, hφ0⟩ : ∃ φ : ΓV, φ ∈ th.asIdeal ∧
      φ ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h ↦ hthη ?_
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext h
  have hs0 := ΓSpecIso_inv_ne_zero hφ0
  have htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (Spec ΓV)
        (Scheme.unitModule (Spec ΓV))
        ((Scheme.ΓSpecIso ΓV).inv φ)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (Spec ΓV)
        (Scheme.unitModule (Spec ΓV))
        ((Scheme.ΓSpecIso ΓV).inv φ)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (Spec ΓV)
        (Scheme.unitModule (Spec ΓV))
        ((Scheme.ΓSpecIso ΓV).inv φ)).subschemeι).obj
          (Scheme.unitModule (Spec ΓV))) :=
    ⟨Scheme.Modules.pullbackUnitIso _⟩
  -- the residue fields along `g'`
  have hres : ∀ z, IsIso (g'.residueFieldMap z) := fun z ↦ by
    rw [hg', Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (IsIso.comp_isIso' (residueFieldMap_isIso_of_isClosedImmersion _ _)
      inferInstance) (residueFieldMap_isIso_of_isClosedImmersion _ _)
  -- the rule vanishes on `[Spec R]`
  have hzero : c.cap g' (relativeDimension C.dimensionFunction sY t + 1)
      (fundamentalCycle C (g' ≫ sY) (relativeDimension C.dimensionFunction sY t + 1)) = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [c.cap_eq_relativeCycleCap, relativeCycleCap_apply_of_isIso,
      fundamentalCycle_apply_of_isIntegral C _ hk]
    split_ifs with hz
    · refine mul_eq_zero_of_right _ (ht' _ ?_)
      change (pullback.fst p g' ≫ p).base z = t'
      rw [pullback.condition, Scheme.Hom.comp_apply, hz, hgη]
    · rw [zero_mul]
      rfl
  -- the Gysin compatibility
  have hG := c.cap_gysinCycleMapPushforward g'
    (Scheme.unitModule (Spec ΓV)) ((Scheme.ΓSpecIso ΓV).inv φ)
    htriv (relativeDimension C.dimensionFunction sY t)
    (fundamentalCycle C (g' ≫ sY) (relativeDimension C.dimensionFunction sY t + 1))
  rw [hzero, map_zero, map_zero,
    gysinCycleMapPushforward_fundamentalCycle C _ hk _ _ hs0 htriv] at hG
  -- read it at a point over `x₀` and `th`
  obtain ⟨z₀, hz₀₁, hz₀₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := g') x₀ th
    (hx₀.trans hgt.symm)
  have hval := congrArg (fun γ ↦ γ.1 z₀) hG
  simp only at hval
  rw [c.cap_eq_relativeCycleCap, relativeCycleCap_apply_of_isIso, hz₀₁, hz₀₂] at hval
  refine (mul_eq_zero.mp hval).resolve_left ?_
  -- the multiplicity of `th` in `Z(φ)` is nonzero
  have hco : Order.coheight th = 1 := by
    refine (relativeDimension_eq_sub_one_iff_coheight_eq_one C (g' ≫ sY) hk th).mp ?_
    rw [hrel, hgt]
    ring
  obtain ⟨ξ, hξ, hξδ⟩ := exists_genericPoints_of_coheight_one C (g' ≫ sY)
    (Stacks.Divisors.zeroScheme (Spec ΓV)
        (Scheme.unitModule (Spec ΓV)) ((Scheme.ΓSpecIso ΓV).inv φ)).subschemeι
    hk (Stacks.ChernCap42.genericPoint_notMem_range_subschemeι_zeroScheme _ _ hs0) hco
    (by rw [Scheme.IdealSheafData.range_subschemeι]
        exact mem_support_zeroScheme_unitModule_spec φ th hφt)
  rw [← hξ, cycleAssociatedToClosedSubscheme_apply C _ _ _ ξ (by rw [hξδ]; ring)]
  have : IsLocallyNoetherian (Stacks.Divisors.zeroScheme
      (Spec ΓV)
      (Scheme.unitModule (Spec ΓV))
      ((Scheme.ΓSpecIso ΓV).inv φ)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.IdealSheafData.subschemeι _ ≫ g' ≫ sY)
  exact_mod_cast componentMultiplicity_ne_zero _ ξ

/-- **Rigidity.** Let `c` be a rule as in Stacks 0H6G over an integral base `Y`. If its family
vanishes over the generic point of `Y`, it vanishes: by induction on the codimension, along
specializations raising the delta-dimension by one
(`Stacks.Chow.CompatibleCycleCapRule.familyCoeff_eq_zero_of_specializes`). -/
theorem CompatibleCycleCapRule.genericFamily_eq_zero_of_genericPoint [IsIntegral Y]
    (c : CompatibleCycleCapRule C sY p r)
    (h₀ : ∀ x : X, p x = genericPoint Y → familyCoeff p r c.genericFamily x = 0) :
    c.genericFamily = 0 := by
  have key : ∀ (n : ℕ) (t : Y), (relativeDimension C.dimensionFunction sY (genericPoint Y) -
      relativeDimension C.dimensionFunction sY t).toNat = n →
        ∀ x : X, p x = t → familyCoeff p r c.genericFamily x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t hn x hx
      by_cases ht : t = genericPoint Y
      · exact h₀ x (hx.trans ht)
      obtain ⟨t', htt', hne, hδ⟩ := exists_generalization_relativeDimension_eq_add_one C sY
        (genericPoint_specializes t) (Ne.symm ht)
      have hle := relativeDimension_le_of_specializes C sY (genericPoint_specializes t')
      exact c.familyCoeff_eq_zero_of_specializes htt' hne hδ
        (ih _ (by omega) t' rfl) x hx
  refine familyOfCycles_ext_familyCoeff p (funext fun x ↦ ?_)
  rw [key _ (p x) rfl x rfl]
  rfl

end Stacks.Chow

end
