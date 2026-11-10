module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupMapOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceDescentCanonical

/-!
# The diagram of Remark 0ER3 and the reduction of Stacks 0ER6 to one integral closed subspace

In Situation 0EDT let `f : X' ⟶ X` be a flat morphism of relative dimension `r` of good algebraic
spaces over `B` and let `(ℒ, s, i : E → X)` be as in Definition 0ER1. We construct the diagram of
Remark 0ER3 for the pulled-back pair `(f^*ℒ, f^*s)`

```
E' --i'--> X'
|          |
g          f
|          |
v          v
E  --i-->  X
```

with `E' = Z(f^*s)`, and reduce Stacks 0ER6, `(i')^* f^* α = g^* i^* α` in `CH_{k+r}(E')`, to a
statement about one integral closed subspace `W ⊆ X` at a time.

## Main definitions

* `AlgebraicGeometry.Space.gysinPullbackChernRule`: the component rule of the cap product
  `i'_* (i')^*` of Stacks 0EQJ on `X'`, the rule
  `AlgebraicGeometry.Space.sectionGysinChernRule` of the pulled-back pair `(f^*ℒ, f^*s)`.

## Main results

All declarations below are in the namespace `AlgebraicGeometry.Space`.

* `pullbackVanishingLocus_eq_preimage`: `E' = f^{-1}(E)` (Remark 0ER3).
* `isPullback_pullbackVanishingLocusProjection`: the square is cartesian.
* `isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection`: `g` is flat of relative
  dimension `r` (Stacks 0EPD, second assertion).
* `isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_firstChernCapCycleMap_sub`:
  Remark 0EQ8 for the commutator of `f^*` with a cap product, keeping track of the carriers.
* `chowClassCanonical_gysinCycleMap_flatPullbackMap_of_defect`: Stacks 0ER6 holds as soon as the
  defect at every `W ⊄ E` vanishes and the defect at every `W ⊆ E` is rationally equivalent to
  zero inside `f^{-1}(W)`.

## References

* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Diagram

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)

/-- **Remark 0ER3.** `Z(f^*s) = f^{-1}(Z(s))` for an invertible `ℒ`, as subfunctors of `X'`. -/
theorem pullbackVanishingLocus_eq_preimage (hL : IsInvertibleSheaf D p hp L) :
    (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 =
      (vanishingLocus D p hp L s).1.preimage f.hom :=
  (congrArg Subtype.val (pullbackDivisor_eq_vanishingLocus D p hp p' hp' f L s hL)).symm

/-- **Remark 0ER3.** The square is cartesian: `E' = X' ×_X E`. -/
theorem isPullback_pullbackVanishingLocusProjection (hL : IsInvertibleSheaf D p hp L) :
    IsPullback (pullbackVanishingLocusProjection D p hp p' hp' f L s hL)
      (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι (vanishingLocus D p hp L s).1.ι
      f.hom := by
  have h := congrArg Subtype.val (pullbackDivisor_eq_vanishingLocus D p hp p' hp' f L s hL)
  have hid : ∀ {A B : Subfunctor X'} (h₁ : A ≤ B) (h₂ : B ≤ A),
      Subfunctor.homOfLe h₁ ≫ Subfunctor.homOfLe h₂ = 𝟙 _ := fun h₁ h₂ => by
    rw [← cancel_mono (Subfunctor.ι _)]; simp
  let e : (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.toFunctor ≅
      (pullbackDivisor D p hp p' hp' f L s).1.toFunctor :=
    { hom := Subfunctor.homOfLe h.ge
      inv := Subfunctor.homOfLe h.le
      hom_inv_id := hid _ _
      inv_hom_id := hid _ _ }
  refine IsPullback.of_iso (pullbackDivisor_isPullback D p hp p' hp' f L s) e.symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change pullbackDivisorProjection D p hp p' hp' f L s ≫ 𝟙 _ =
      Subfunctor.homOfLe h.le ≫ Subfunctor.homOfLe h.ge ≫
        pullbackDivisorProjection D p hp p' hp' f L s
    rw [Category.comp_id, reassoc_of% (hid h.le h.ge)]
  · change (pullbackDivisor D p hp p' hp' f L s).1.ι ≫ 𝟙 _ =
      Subfunctor.homOfLe h.le ≫ (pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι
    rw [Category.comp_id, Subfunctor.homOfLe_ι]

/-- **Stacks 0EPD, second assertion, for the square of Remark 0ER3.** `g : E' ⟶ E` is flat of
relative dimension `r`. -/
theorem isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection (hfbase : f.hom ≫ p = p')
    (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (hL : IsInvertibleSheaf D p hp L) :
    IsFlat D.site D.base D.base_mem (pullbackVanishingLocusProjection D p hp p' hp' f L s hL) ∧
      HasRelativeDimension r D.site D.base D.base_mem
        (pullbackVanishingLocusProjection D p hp p' hp' f L s hL) :=
  (isFlat_and_hasRelativeDimension_of_isPullback D
    ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
    (isGood_vanishingLocus D p' hp' _ _) ((vanishingLocus D p hp L s).1.ι ≫ p)
    (isGood_vanishingLocus D p hp L s) p' hp' p hp
    (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase) hfbase
    (isPullback_pullbackVanishingLocusProjection D p hp p' hp' f L s hL) r hflat hr).2

end Diagram

section Carrier

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (k : ℤ)
    (chernY : FirstChernComponentCycleRule D sY k)
    (chernX : FirstChernComponentCycleRule D sX (k + (r : ℤ)))

/-- **Remark 0EQ8 for the commutator of flat pullback and cap product, with carriers.** If for
every integral closed subspace `W ⊆ Y` of δ-dimension `k + 1` occurring in `α` every integer
multiple of the defect at `W` is rationally equivalent to zero within a set `C W ⊆ f^{-1}(|W|)`,
then `f^*(c₁ ∩ α) - c₁ ∩ f^*α` is rationally equivalent to zero within `⋃ C W`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_firstChernCapCycleMap_sub
    (C : IntegralClosedSubspace D.site D.base D.base_mem Y →
      Set (points D.site D.base D.base_mem X))
    (hC : ∀ W, C W ⊆ pointsMap D.site D.base D.base_mem X f ⁻¹'
      subspacePointSet D.site D.base D.base_mem Y W.subspace)
    (α : CycleGroup D sY (k + 1))
    (hdefect : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (hW : deltaDimension D sY W = k + 1) (a : ℤ), α.1 W ≠ 0 →
      IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX (k + (r : ℤ))
        (a • flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX W hW) (C W)) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX (k + (r : ℤ))
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (firstChernCapCycleMap D sY hY k chernY α) -
        firstChernCapCycleMap D sX hX (k + (r : ℤ)) chernX
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
            α)) (⋃ W, C W) := by
  classical
  let J := {W : IntegralClosedSubspace D.site D.base D.base_mem Y // α.1 W ≠ 0}
  refine (isRationallyEquivalentToZeroWithinCanonical_finsum.{u + 1} D sX hX (k + (r : ℤ))
    (J := J)
    (fun j => α.1 j.1 • flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX j.1
      (α.2.2 j.1 j.2))
    (fun j => C j.1)
    (((locallyFinite_cycleSupport α).preimage_continuous
      (continuous_pointsMap D.site D.base D.base_mem f)).subset fun j => hC j.1)
    (fun j => hdefect j.1 (α.2.2 j.1 j.2) (α.1 j.1) j.2) fun T => ?_).mono
      (Set.iUnion_subset fun j => Set.subset_iUnion C j.1)
  rw [AddSubgroup.coe_sub, Pi.sub_apply, flatPullbackMap_firstChernCapCycleMap_sub_apply]
  have hj : ∀ j : J, ((α.1 j.1 • flatChernDefect D sX hX sY hY f hbase r hflat hr k chernY chernX
      j.1 (α.2.2 j.1 j.2) : CycleGroup D sX (k + (r : ℤ))) :
        IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) T =
      α.1 j.1 * flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k chernY chernX j.1 T :=
    fun j => by
      rw [AddSubgroup.coe_zsmul, Pi.smul_apply, flatChernDefect_apply, smul_eq_mul]
  rw [finsum_congr hj]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun W =>
      α.1 W * flatChernDefectCoeff D sX hX sY hY f hbase r hflat hr k chernY chernX W T)
    (fun W => α.1 W ≠ 0)).symm
  refine finsum_congr fun W => ?_
  by_cases hW : α.1 W = 0
  · rw [hW, zero_mul, finsum_eq_if, ite_eq_right (not_not.2 rfl)]
  · rw [finsum_eq_if, ite_eq_left hW]

end Carrier

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f.hom)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

/-- The component rule of the cap product `i'_* (i')^*` on `X'` for the pulled-back pair
`(f^*ℒ, f^*s)`. -/
abbrev gysinPullbackChernRule : FirstChernComponentCycleRule D p' (k + (r : ℤ)) :=
  sectionGysinChernRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
    (pullbackGlobalSection D p hp p' hp' f L s)
    (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) (k + (r : ℤ))

/-- **The reduction of Stacks 0ER6 to one integral closed subspace.** If the defect at every
integral closed subspace `W ⊄ E` of δ-dimension `k + 1` vanishes and every integer multiple of the
defect at every `W ⊆ E` is rationally equivalent to zero inside `f^{-1}(|W|)`, then
`(i')^* f^* α` and `g^* i^* α` have the same class in `CH_{k+r}(E')` for every `(k + 1)`-cycle
`α`. -/
theorem chowClassCanonical_gysinCycleMap_flatPullbackMap_of_defect
    (hnotle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1), ¬ W.subspace ≤ (vanishingLocus D p hp L s).1 →
      flatChernDefect D p' hp' p hp f.hom hfbase r hflat hr k
        (sectionGysinChernRule D p hp L s hL k) (gysinPullbackChernRule D p hp p' hp' f r L s hL k)
        W hW = 0)
    (hle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1), W.subspace ≤ (vanishingLocus D p hp L s).1 →
      ∀ a : ℤ, IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D p' hp' (k + (r : ℤ))
        (a • flatChernDefect D p' hp' p hp f.hom hfbase r hflat hr k
          (sectionGysinChernRule D p hp L s hL k)
          (gysinPullbackChernRule D p hp p' hp' f r L s hL k) W hW)
        (pointsMap D.site D.base D.base_mem X' f.hom ⁻¹'
          subspacePointSet D.site D.base D.base_mem X W.subspace))
    (α : CycleGroup D p (k + 1)) :
    chowClassCanonical.{u + 1} D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) (k + (r : ℤ))
        (gysinCycleMap D p' (pullbackSectionVanishingLocus D p hp p' hp' f L s)
          (isGood_vanishingLocus D p' hp' _ _) (k + (r : ℤ))
          (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s) (k + (r : ℤ))
            (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL))
          (flatPullbackMap D p' hp' p hp f.hom hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
            (by ring) α)) =
      chowClassCanonical.{u + 1} D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
        (isGood_vanishingLocus D p' hp' _ _) (k + (r : ℤ))
        (flatPullbackMap D ((pullbackSectionVanishingLocus D p hp p' hp' f L s).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _) ((vanishingLocus D p hp L s).1.ι ≫ p)
          (isGood_vanishingLocus D p hp L s)
          (pullbackVanishingLocusProjection D p hp p' hp' f L s hL)
          (pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase) r
          (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
            hfbase r hflat hr hL).1
          (isFlat_and_hasRelativeDimension_pullbackVanishingLocusProjection D p hp p' hp' f L s
            hfbase r hflat hr hL).2 k (k + (r : ℤ)) rfl
          (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
            (sectionGysinRule D p hp L s k hL) α)) := by
  classical
  set E := vanishingLocus D p hp L s
  set E' := pullbackSectionVanishingLocus D p hp p' hp' f L s
  have hE := isGood_vanishingLocus D p hp L s
  have hE' : D.IsGood (E'.1.ι ≫ p') := isGood_vanishingLocus D p' hp' _ _
  have hgb := pullbackVanishingLocusProjection_comp_structure D p hp p' hp' f L s hL hfbase
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  refine isRationallyEquivalentToZeroCanonical_of_withinCanonical_cycleGroupClosedPushforward
    D p' hp' E'.1 E'.2 (k + (r : ℤ)) ?_
  have hL' := isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL
  have hA := cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D p' hp'
    (pullbackSheaf D p hp p' hp' f L) (pullbackGlobalSection D p hp p' hp' f L s) hL'
    (k + (r : ℤ)) (restrictedDivisorCycle D p' hp' (pullbackSheaf D p hp p' hp' f L) (k + (r : ℤ))
      hL') (flatPullbackMap D p' hp' p hp f.hom hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
        (by ring) α)
  have h0 := flatPullback_properPushforward_unconditional D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE
    p' hp' p hp hgb rfl rfl hfbase r hflat hr
    (isPullback_pullbackVanishingLocusProjection D p hp p' hp' f L s hL)
    (isProper_of_isClosedImmersion D.site D.base D.base_mem E.2.1 hp.1 E.1.ι E.2.2) k
    (k + (r : ℤ)) rfl
    (gysinCycleMap D p E hE k (sectionGysinRule D p hp L s k hL) α)
  rw [properCyclePushforward_ι_eq_cycleGroupClosedPushforward D p hp E.1 E.2 k,
    properCyclePushforward_ι_eq_cycleGroupClosedPushforward D p' hp' E'.1 E'.2 (k + (r : ℤ))] at h0
  have hB := cycleClosedPushforward_gysinCycleMap_eq_firstChernCapCycleMap D p hp L s hL k
    (restrictedDivisorCycle D p hp L k hL) α
  rw [map_sub]
  let C : IntegralClosedSubspace D.site D.base D.base_mem X →
      Set (points D.site D.base D.base_mem X') := fun W =>
    if W.subspace ≤ E.1 then pointsMap D.site D.base D.base_mem X' f.hom ⁻¹'
      subspacePointSet D.site D.base D.base_mem X W.subspace else ∅
  have hC : ∀ W, C W ⊆ pointsMap D.site D.base D.base_mem X' f.hom ⁻¹'
      subspacePointSet D.site D.base D.base_mem X W.subspace := fun W => by
    by_cases h : W.subspace ≤ E.1 <;> simp [C, h]
  have hCE : (⋃ W, C W) ⊆ subspacePointSet D.site D.base D.base_mem X' E'.1 := by
    refine Set.iUnion_subset fun W => ?_
    by_cases h : W.subspace ≤ E.1
    · simp only [C, ite_eq_left h]
      rw [pullbackVanishingLocus_eq_preimage D p hp p' hp' f L s hL, subspacePointSet_preimage]
      exact Set.preimage_mono (subspacePointSet_mono_of_le D h)
    · simp only [C, ite_eq_right h, Set.empty_subset]
  have hcomm :=
    isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_firstChernCapCycleMap_sub
      D p' hp' p hp f.hom hfbase r hflat hr k (sectionGysinChernRule D p hp L s hL k)
      (gysinPullbackChernRule D p hp p' hp' f r L s hL k) C hC α fun W hW a _ => by
        by_cases h : W.subspace ≤ E.1
        · simp only [C, ite_eq_left h]
          exact hle W hW h a
        · simp only [C, ite_eq_right h]
          rw [hnotle W hW h, smul_zero]
          exact isRationallyEquivalentToZeroWithinCanonical_zero D p' hp' _ _
  convert (hcomm.neg).mono hCE using 1
  rw [neg_sub]
  congr 1
  rw [← h0]
  exact congrArg _ hB

end Main

end AlgebraicGeometry.Space

end
