module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# Support and localization properties of the Gysin map on cycles

Let `X` be locally of finite type over the base of a Chow situation, let `L` be an invertible
module on `X`, `s ∈ Γ(X, L)` and `D = Z(s)`, and assume `L|_D ≅ 𝒪_D`, so that the Gysin map on
cycles `i^* : Z_{k+1}(X) ⟶ Z_k(D)` of Stacks 0B6Z is defined. This file proves its vanishing on
cycles supported in `D`, its compatibility with open restriction, and its value on a closed
subscheme meeting `D` in an effective Cartier divisor.

## Main results

* `Stacks.Chow.gysinCycleMap_eq_zero_of_support_subset` — a cycle supported in `D` has zero
  image: each of its components lies in `D`.
* `Stacks.Chow.cycleGroupRestrict_gysinCycleMap` — the Gysin map commutes with restriction to an
  open subscheme `U ⊆ X`, the zero scheme on `U` being that of the restricted section.
* `Stacks.Chow.gysinCycleMap_cycleAssociatedToClosedSubscheme_of_isEffectiveCartierDivisor` —
  `i^*[Z] = [D ∩ Z]` when `D ∩ Z` is an effective Cartier divisor on `Z`.
* `Stacks.Chow.gysinCycleMapPushforward` — the composite `i_* ∘ i^*`, with its compatibility with
  proper pushforward (Stacks 0H6D) and with open restriction.

## References

* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 0H6D](https://stacks.math.columbia.edu/tag/0H6D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))

/-- The coefficients of the Gysin image of `β` are the locally finite sum of the Gysin images of
the components of `β`. -/
private theorem gysinCycleMap_apply_eq_finsum (β : CycleGroup C p (k + 1))
    (y : (Stacks.Divisors.zeroScheme X L s).subscheme) :
    (gysinCycleMap C p k L s htriv β).1 y = ∑ᶠ x : cycleSupportIndex β, β.1 x.1 *
      (gysinCycleMapComponent C p k L s (integralComponentAt x.1)
        (isIntegral_integralComponentAt x.1)
        (schemeDeltaDimension_cycleSupportIndex β x)).1 y :=
  isGysinCycleMap_gysinCycleMap C p k L s htriv
      (fun x : cycleSupportIndex β ↦ integralComponentAt x.1)
      (fun x ↦ isIntegral_integralComponentAt x.1)
      (fun x ↦ schemeDeltaDimension_cycleSupportIndex β x)
      (locallyFinite_support_integralComponentAt β) (fun x ↦ β.1 x.1) β
      (cycle_eq_finsum_primeCycles β) y

/-- A `(k+1)`-cycle supported in the zero scheme `D` has zero image under the Gysin map on
cycles. -/
theorem gysinCycleMap_eq_zero_of_support_subset (β : CycleGroup C p (k + 1))
    (hβ : Function.support β.1 ⊆ ((Stacks.Divisors.zeroScheme X L s).support : Set X)) :
    gysinCycleMap C p k L s htriv β = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [gysinCycleMap_apply_eq_finsum C p k L s htriv β y]
  refine finsum_eq_zero_of_forall_eq_zero fun x ↦ ?_
  rw [gysinCycleMapComponent_of_le C p k L s _ (isIntegral_integralComponentAt x.1)
    (schemeDeltaDimension_cycleSupportIndex β x)
    ((le_integralComponentAt_iff_mem_support _ x.1).2 (hβ x.2))]
  simp

/-- The morphism of zero schemes induced by an open immersion is an open immersion. -/
instance isOpenImmersion_zeroSchemePullbackMap {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsOpenImmersion (Stacks.Divisors.zeroSchemePullbackMap j L s) :=
  MorphismProperty.of_isPullback (Stacks.Divisors.isPullback_zeroSchemePullbackMap j L s)
    inferInstance

/-- **The Gysin map on cycles commutes with restriction to an open subscheme.** For an open
immersion `j : U ⟶ X`, restricting `i^* β` along the induced open immersion
`Z(j^* s) ⟶ Z(s)` of zero schemes (Stacks 0B6Y) gives the Gysin map of `(j^* L, j^* s)` applied
to the restriction of `β`. -/
theorem cycleGroupRestrict_gysinCycleMap {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (htrivU : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s)).subschemeι).obj ((Scheme.Modules.pullback j).obj L)))
    (β : CycleGroup C p (k + 1)) :
    cycleGroupRestrict C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
          (pullbackGlobalSections j L s)).subschemeι ≫ j ≫ p)
        (Stacks.Divisors.zeroSchemePullbackMap j L s)
        (Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism j L s p (j ≫ p) rfl) k
        (gysinCycleMap C p k L s htriv β) =
      gysinCycleMap C (j ≫ p) k ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s) htrivU
        (cycleGroupRestrict C p (j ≫ p) j rfl (k + 1) β) := by
  classical
  set D := Stacks.Divisors.zeroScheme X L s with hD
  set DU := Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
    (pullbackGlobalSections j L s) with hDU
  set q := Stacks.Divisors.zeroSchemePullbackMap j L s with hqdef
  set βU := cycleGroupRestrict C p (j ≫ p) j rfl (k + 1) β with hβU
  have hDUeq : DU = D.comap j := Stacks.Divisors.zeroScheme_pullback j L s
  have hqι : q ≫ D.subschemeι = DU.subschemeι ≫ j :=
    Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι j L s
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [cycleGroupRestrict_apply,
    gysinCycleMap_apply_eq_finsum C p k L s htriv β (q.base y),
    gysinCycleMap_apply_eq_finsum C (j ≫ p) k _ _ htrivU βU y]
  let φ : cycleSupportIndex βU → cycleSupportIndex β := fun x ↦ ⟨j.base x.1, x.2⟩
  have hφ : Function.Injective φ := fun a b h ↦
    Subtype.ext (j.isOpenEmbedding.injective (congrArg Subtype.val h))
  have hsupp : Function.support (fun x : cycleSupportIndex β ↦ β.1 x.1 *
      (gysinCycleMapComponent C p k L s (integralComponentAt x.1)
        (isIntegral_integralComponentAt x.1)
        (schemeDeltaDimension_cycleSupportIndex β x)).1 (q.base y)) ⊆ Set.range φ := by
    intro x hx
    have hne := right_ne_zero_of_mul hx
    have hmem := support_gysinCycleMapComponent_subset C p k L s (integralComponentAt x.1)
      (isIntegral_integralComponentAt x.1) (schemeDeltaDimension_cycleSupportIndex β x) hne
    have hpt : D.subschemeι.base (q.base y) = j.base (DU.subschemeι.base y) := by
      rw [← Scheme.Hom.comp_apply, hqι, Scheme.Hom.comp_apply]
    rw [Set.mem_preimage, coe_support_integralComponentAt, hpt] at hmem
    obtain ⟨w, hw⟩ : x.1 ∈ Set.range j.base :=
      (specializes_iff_mem_closure.mpr hmem).mem_open j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    exact ⟨⟨w, show β.1 (j.base w) ≠ 0 from hw ▸ x.2⟩, Subtype.ext hw⟩
  refine ((finsum_mem_univ _).symm.trans (finsum_mem_inter_support_eq' _ _ (Set.range φ)
    (fun x hx ↦ ⟨fun _ ↦ hsupp hx, fun _ ↦ trivial⟩))).trans ?_
  refine (finsum_mem_range hφ).trans (finsum_congr fun x ↦ ?_)
  show β.1 (j.base x.1) * _ = β.1 (j.base x.1) * _
  congr 1
  have hiff : D ≤ integralComponentAt (j.base x.1) ↔ DU ≤ integralComponentAt x.1 := by
    rw [le_integralComponentAt_iff_mem_support, le_integralComponentAt_iff_mem_support, hDUeq,
      Scheme.IdealSheafData.support_comap]
    rfl
  by_cases h : D ≤ integralComponentAt (j.base x.1)
  · rw [gysinCycleMapComponent_of_le C p k L s _ _ _ h,
      gysinCycleMapComponent_of_le C (j ≫ p) k _ _ _ _ _ (hiff.1 h)]
    rfl
  · rw [gysinCycleMapComponent_of_not_le C p k L s _ _ _ h,
      gysinCycleMapComponent_of_not_le C (j ≫ p) k _ _ _ _ _ (fun h' ↦ h (hiff.2 h'))]
    have hcomap : (integralComponentAt x.1).comap DU.subschemeι =
        ((integralComponentAt (j.base x.1)).comap D.subschemeι).comap q := by
      rw [← Scheme.IdealSheafData.comap_comp, hqι, Scheme.IdealSheafData.comap_comp,
        comap_integralComponentAt_of_isOpenImmersion]
    rw [hcomap, cycleAssociatedToClosedSubscheme_comap_of_isOpenImmersion C (D.subschemeι ≫ p)
      (DU.subschemeι ≫ j ≫ p) q
      (Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism j L s p (j ≫ p) rfl)]

/-- **The Gysin map on cycles of a closed subscheme meeting the divisor properly.** Let
`Z ⊆ X` be a closed subscheme of delta-dimension at most `k + 1` on which `D ∩ Z` is an effective
Cartier divisor. Then `i^*[Z]_{k+1} = [D ∩ Z]_k`. -/
theorem gysinCycleMap_cycleAssociatedToClosedSubscheme_of_isEffectiveCartierDivisor
    (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L s).comap Z.subschemeι)) :
    gysinCycleMap C p k L s htriv (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((Z.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k := by
  classical
  obtain ⟨s', rfl⟩ : ∃ s' : L.sections, s'.eval (.op ⊤) = s :=
    ⟨Stacks.PresheafOfModules.sectionOfTop L.val s,
      Stacks.PresheafOfModules.sectionOfTop_val_top L.val s⟩
  rw [← gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme C p k L s' Z hZ hDZ]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  show (gysinCycleMapRule C p k L _).toComponentRule.extend _ _ y =
    (gysinRule C p k L _ _).toComponentRule.extend _ _ y
  rw [ComponentRule.extend_apply, ComponentRule.extend_apply]
  refine finsum_congr fun x ↦ ?_
  by_cases hx : (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).1 x = 0
  · rw [hx, zero_mul, zero_mul]
  · congr 1
    have hxZ : x ∈ (Z.support : Set X) := by
      have h := support_cycleAssociatedToClosedSubscheme_subset C p Z.subschemeι (k + 1) hx
      rwa [Scheme.IdealSheafData.range_subschemeι] at h
    have hdim : relativeDimension C.dimensionFunction p x = k + 1 :=
      (mem_cyclesOfDimension_iff_forall_point C p (k + 1) _).1
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)).2 x hx
    have hnot : ¬ Stacks.Divisors.zeroScheme X L (s'.eval (.op ⊤)) ≤ integralComponentAt x :=
      fun hle ↦ not_mem_support_of_top_dimension_of_effectiveCartier C p k Z _ hZ hDZ x hxZ hdim
        ((le_integralComponentAt_iff_mem_support _ x).1 hle)
    exact congrArg (fun c : CycleGroup C _ k ↦ c.1 y)
      (gysinCycleMapRule_cycleAt_eq_gysinComponentCycleAt_of_not_le C p k L _
        (firstChernComponentClass C p k L) x hnot)

/-! ### The Gysin map followed by the pushforward to the ambient scheme -/

/-- The composite `i_* ∘ i^* : Z_{k+1}(X) ⟶ Z_k(X)` of the Gysin map on cycles of Stacks 0B6Z with
proper pushforward along the closed immersion `i : D ⟶ X` of the zero scheme. -/
def gysinCycleMapPushforward : CycleGroup C p (k + 1) →+ CycleGroup C p k :=
  (properPushforwardHom C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k).comp (gysinCycleMap C p k L s htriv)

/-- `i_* ∘ i^*` applied to a cycle `β` is the proper pushforward along `i` of the Gysin image of
`β`. -/
theorem gysinCycleMapPushforward_apply (β : CycleGroup C p (k + 1)) :
    gysinCycleMapPushforward C p k L s htriv β =
      properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k (gysinCycleMap C p k L s htriv β) :=
  rfl

/-- A cycle supported in the zero scheme is killed by `i_* ∘ i^*`. -/
theorem gysinCycleMapPushforward_eq_zero_of_support_subset (β : CycleGroup C p (k + 1))
    (hβ : Function.support β.1 ⊆ ((Stacks.Divisors.zeroScheme X L s).support : Set X)) :
    gysinCycleMapPushforward C p k L s htriv β = 0 := by
  rw [gysinCycleMapPushforward_apply, gysinCycleMap_eq_zero_of_support_subset C p k L s htriv β hβ,
    properPushforward_zero]

/-- **`i_* ∘ i^*` commutes with proper pushforward** (Stacks 0H6D read in `X`). For a proper
morphism `f : X' ⟶ X` over the base, `i_* i^* f_* β' = f_* i'_* (i')^* β'` where `i'` is the zero
scheme of the pulled-back section `f^* s`. -/
theorem gysinCycleMapPushforward_properPushforward {X' : Scheme.{u}} (p' : X' ⟶ C.S)
    [LocallyOfFiniteType p'] (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p')
    (β : CycleGroup C p' (k + 1)) :
    gysinCycleMapPushforward C p k L s htriv (properPushforward C p' p f hf (k + 1) β) =
      properPushforward C p' p f hf k
        (gysinCycleMapPushforward C p' k ((Scheme.Modules.pullback f).obj L)
          (pullbackGlobalSections f L s)
          (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections f L s htriv)
          β) := by
  rw [gysinCycleMapPushforward_apply, gysinCycleMapPushforward_apply,
    properPushforward_gysinCycleMap C p p' f hf k L s htriv β]
  have h1 := congrFun (properPushforward_comp C _ _ p (Stacks.Divisors.zeroSchemePullbackMap f L s)
    (Stacks.Divisors.zeroScheme X L s).subschemeι
    (Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) rfl k)
    (gysinCycleMap C p' k ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s)
      (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections f L s htriv) β)
  have h2 := congrFun (properPushforward_comp C _ p' p
    (Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback f).obj L)
      (pullbackGlobalSections f L s)).subschemeι f rfl hf k)
    (gysinCycleMap C p' k ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSections f L s)
      (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections f L s htriv) β)
  simp only [Function.comp_apply] at h1 h2
  rw [h1, h2]
  congr 1
  exact Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι f L s

/-- **`i_* ∘ i^*` commutes with restriction to an open subscheme.** -/
theorem cycleGroupRestrict_gysinCycleMapPushforward {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (htrivU : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme U ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s)).subschemeι).obj ((Scheme.Modules.pullback j).obj L)))
    (β : CycleGroup C p (k + 1)) :
    cycleGroupRestrict C p (j ≫ p) j rfl k (gysinCycleMapPushforward C p k L s htriv β) =
      gysinCycleMapPushforward C (j ≫ p) k ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L s) htrivU
        (cycleGroupRestrict C p (j ≫ p) j rfl (k + 1) β) := by
  rw [gysinCycleMapPushforward_apply, gysinCycleMapPushforward_apply,
    ← cycleGroupRestrict_gysinCycleMap C p k L s htriv j htrivU β]
  exact cycleGroupRestrict_properPushforward C _ p _ (j ≫ p)
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl
    (Stacks.Divisors.zeroSchemePullbackMap j L s)
    (Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism j L s p (j ≫ p) rfl) j rfl
    _ rfl (Stacks.Divisors.isPullback_zeroSchemePullbackMap j L s).flip k _

/-- **`i_* i^* [Z]_{k+1} = [D ∩ Z]_k`** for a closed subscheme `Z` of delta-dimension at most
`k + 1` meeting `D` in an effective Cartier divisor of `Z`, read as cycles on `X`. -/
theorem gysinCycleMapPushforward_cycleAssociatedToClosedSubscheme (Z : X.IdealSheafData)
    (hZ : schemeDeltaDimension C (Z.subschemeι ≫ p) ≤ ((k + 1 : ℤ) : EInt))
    (hDZ : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Divisors.zeroScheme X L s).comap Z.subschemeι)) :
    gysinCycleMapPushforward C p k L s htriv
        (cycleAssociatedToClosedSubscheme C p Z.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C p
        ((Z.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι) k := by
  rw [gysinCycleMapPushforward_apply,
    gysinCycleMap_cycleAssociatedToClosedSubscheme_of_isEffectiveCartierDivisor C p k L s htriv Z
      hZ hDZ]
  exact properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C _ p _ rfl
    _ k

/-- `i_* ∘ i^*` does not see how the structure morphism to the base is written: for two equal
structure morphisms, cycles with the same coefficients have images with the same coefficients. -/
theorem gysinCycleMapPushforward_congr (q : X ⟶ C.S) [LocallyOfFiniteType q] (hpq : p = q)
    (β : CycleGroup C p (k + 1)) (γ : CycleGroup C q (k + 1)) (h : β.1 = γ.1) :
    (gysinCycleMapPushforward C p k L s htriv β).1 =
      (gysinCycleMapPushforward C q k L s htriv γ).1 := by
  subst hpq
  rw [Subtype.ext h]

end Stacks.Chow

end
