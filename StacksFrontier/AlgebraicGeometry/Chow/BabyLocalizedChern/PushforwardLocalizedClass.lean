module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.CompositeCaps
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernGysinCommute
public import StacksCore.Tactic.StacksAttribute

/-!
# The pushforward of a localized class of a closed cover (Stacks 0F9I)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`i_j : X_j ⟶ X` (`j = 1, 2`) be closed immersions with `X = X₁ ∪ X₂` set theoretically. Let
`E ∈ D(𝒪_X)` be perfect with defined Chern classes and let `E₂ = E|_{X₂}`. If `E|_{X₁}` is zero,
respectively isomorphic to a finite locally free `𝒪_{X₁}`-module of rank `< p` sitting in
cohomological degree `0`, then `E₂|_{X₁ ∩ X₂}` is zero, respectively finite locally free of rank
`< p` in degree `0`, so the class `P'_p(E₂)`, respectively `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` of
Stacks 0F9H is defined, and **Stacks 0F9I** asserts

  `i_{2,*} ∘ P'_p(E₂) = P_p(E)`,   respectively   `i_{2,*} ∘ c'_p(E₂) = c_p(E)`

in `A^p(X ⟶ X) = A^p(X)`, with `i_{2,*} ∘ -` the proper pushforward of Stacks 0EPK.

## The argument

The source's computation: on a test scheme `X' ⟶ X` write `α' = i'_{1,*} α'_1 + i'_{2,*} α'_2`
(Stacks 0F94). Then `P_p(E) ∩ i'_{1,*} α'_1 = i'_{1,*}(P_p(E|_{X₁}) ∩ α'_1) = 0` and
`P_p(E) ∩ i'_{2,*} α'_2 = i'_{2,*}(P_p(E₂) ∩ α'_2) = i'_{2,*}(P'_p(E₂) ∩ α')`. This is
`Stacks.Chow.chowPush_closedCoverLocalizedClass_cap` for a class `κ_X ∈ A^p(X)` restricting to
`κ ∈ A^p(X₂)` and to `0 ∈ A^p(X₁)`; here it is read through the cap formula of Stacks 0EPK.

## Main results

* `Stacks.Chow.canonicalBivariantProperPushforward_closedCoverLocalizedClass` —
  `i_{2,*} ∘ κ' = κ_X` for the localized class `κ'` of the restriction `κ` of `κ_X` to `X₂`, when
  `κ_X` restricts to zero on `X₁`.
* `Stacks.Chow.pushforward_localizedPowerSumOfClosedCover` — **Stacks 0F9I** for `P'_p`.
* `Stacks.Chow.pushforward_localizedChernClassOfClosedCover` — **Stacks 0F9I** for `c'_p`.

## Implementation notes

`E₂` is the derived pullback `Li₂^* E`, and `E|_{X₁}` is `Li₁^* E`. The hypotheses of
Stacks 0F9H on `E₂` are derived from those of the lemma: the Chern classes of `E₂` are defined
because those of `E` are (Stacks 0GUE (5)), `E₂` is perfect, and `E₂|_{X₁ ∩ X₂}` is the pullback
of `E|_{X₁}` along `X₁ ∩ X₂ ⟶ X₁`. A class of `A^p(X)` is a bivariant class for `𝟙 X`; the class
`P'_p(E₂)` is a class for `i₂`, read as one for `i₂ ≫ 𝟙 X` by `Stacks.Chow.bivariantClassCongr`
before the pushforward along `i₂` is applied.

## References

* [Stacks Project, Tag 0F9I](https://stacks.math.columbia.edu/tag/0F9I)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The pushforward of a localized class -/

section Localized

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}

/-- **`i_{2,*} ∘ κ' = κ_X`.** Let `X = X₁ ∪ X₂` set theoretically, let `κ_X ∈ A^p(X)` restrict to
`κ ∈ A^p(X₂)` and to `0 ∈ A^p(X₁)`, and let `κ' ∈ A^p(X₂ ⟶ X)` be the localized class of `κ`
constructed in the proof of Stacks 0F9H. Then the proper pushforward `i_{2,*} ∘ κ'` of
Stacks 0EPK is `κ_X`. -/
theorem canonicalBivariantProperPushforward_closedCoverLocalizedClass
    (κX : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p)
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) (pullback.snd i₁ i₂)
      p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
    (hκX₂ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κX = κ)
    (hκX₁ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₁ p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κX = 0) :
    canonicalBivariantProperPushforward C (i₂ ≫ sX) sX sX i₂ (𝟙 X) rfl (Category.id_comp sX) p
        (bivariantClassCongr C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX
          (Category.comp_id i₂).symm rfl
          (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) p
          (closedCoverLocalizedClass C sX (i₁ ≫ sX) (i₂ ≫ sX) i₁ rfl i₂ rfl hcover κ hκ)) =
      κX := by
  refine BivariantClass.eq_of_idRule_eq C sX (gysinSystemOfInvertible C) _ _ fun g _ k α ↦ ?_
  rw [BivariantClass.idRule_apply]
  show chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) = _
  rw [chowPush_comp C _ _ _ _ _ _ (bivariantPushforwardBaseChange_snd i₂ (𝟙 X) g) _ _
      (pullbackSnd_comp_structureMorphism_eq C (i₂ ≫ sX) sX (i₂ ≫ 𝟙 X)
        (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) g),
    chowPush_snd_bivariantClassCongr C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX
      (Category.comp_id i₂).symm rfl]
  exact chowPush_closedCoverLocalizedClass_cap C sX i₁ i₂ hcover κX κ hκ hκX₂ hκX₁ g k α

end Localized

/-! ### Stacks 0F9I -/

section Statement

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
  {E : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E) (p : ℕ)

omit [IsClosedImmersion i₂] in
/-- `E₂ = E|_{X₂}` is perfect when `E` is. -/
theorem isPerfect_restriction
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E) :
    RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₂.toLRSHom.toShHom).obj E) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E perfect

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- If `E|_{X₁}` is zero, so is `E₂|_{X₁ ∩ X₂}` for `E₂ = E|_{X₂}`. -/
theorem isZero_restriction_intersection
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₂.toLRSHom.toShHom).obj E)) :=
  isZero_derivedPullback_of_comp_eq _ _ _ _ pullback.condition.symm E hzero

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- If `E|_{X₁}` is a finite locally free module of rank `< p` in degree `0`, so is
`E₂|_{X₁ ∩ X₂}` for `E₂ = E|_{X₂}`. -/
theorem exists_iso_single_restriction_intersection
    (hres : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          i₁.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor X₁.Modules 0).obj M)) :
    ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback i₂.toLRSHom.toShHom).obj
            E) ≅ (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M) :=
  exists_iso_single_derivedPullback_of_comp_eq _ _ _ _ pullback.condition.symm E hres

/-- **Stacks 0F9I, for the classes `P_p`.** Let `X` be locally of finite type over `S`, let
`i_j : X_j ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set theoretically, and let `E` be a
perfect object of `D(𝒪_X)` whose Chern classes are defined and whose restriction `E|_{X₁}` is
zero. Then `E₂ = E|_{X₂}` satisfies the hypotheses of Stacks 0F9H with `E₂|_{X₁ ∩ X₂}` zero, and

  `i_{2,*} ∘ P'_p(E₂) = P_p(E)`   in   `A^p(X)`,

where `P'_p(E₂) ∈ A^p(X₂ ⟶ X)` is the class of Stacks 0F9H
(`Stacks.Chow.localizedPowerSumOfClosedCover`), `i_{2,*} ∘ -` is the pushforward of
Stacks 0EPK and `P_p(E)` is the class of Definition 0F9E (2). -/
@[stacks 0F9I "the classes P'_p: i_{2,*} ∘ P'_p(E₂) = P_p(E) for E|_{X₁} zero"]
theorem pushforward_localizedPowerSumOfClosedCover
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      i₁.toLRSHom.toShHom).obj E)) :
    canonicalBivariantProperPushforward C (i₂ ≫ sX) sX sX i₂ (𝟙 X) rfl (Category.id_comp sX)
        (p : ℤ)
        (bivariantClassCongr C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX
          (Category.comp_id i₂).symm rfl
          (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) (p : ℤ)
          (localizedPowerSumOfClosedCover C sX i₁ i₂ hcover
            (hasDefinedChernClasses_derivedPullback i₂ hE) p
            (isPerfect_restriction i₂ perfect)
            (isZero_restriction_intersection i₁ i₂ hzero))) =
      perfectPowerSumComponent C sX hE p := by
  refine canonicalBivariantProperPushforward_closedCoverLocalizedClass C sX i₁ i₂ hcover _ _ _
    ?_ ?_
  · rw [← perfectPowerSumTotal_apply C sX hE p, ← TotalChowClass.res_rfl_apply,
      res_perfectPowerSumTotal_derivedPullback C sX i₂ rfl perfect hE
        (isPerfect_restriction i₂ perfect) (hasDefinedChernClasses_derivedPullback i₂ hE)]
    exact perfectPowerSumTotal_apply C (i₂ ≫ sX) _ p
  · exact chowCohomologyRestriction_perfectPowerSumComponent_eq_zero C sX perfect hE i₁ hzero p

/-- **Stacks 0F9I, for the Chern classes.** Let `X` be locally of finite type over `S`, let
`i_j : X_j ⟶ X` be closed immersions with `X = X₁ ∪ X₂` set theoretically, and let `E` be a
perfect object of `D(𝒪_X)` whose Chern classes are defined and whose restriction `E|_{X₁}` is
isomorphic to a finite locally free `𝒪_{X₁}`-module of rank `< p` sitting in cohomological
degree `0`. Then `E₂ = E|_{X₂}` satisfies the hypotheses of Stacks 0F9H with `E₂|_{X₁ ∩ X₂}`
finite locally free of rank `< p` in degree `0`, and

  `i_{2,*} ∘ c'_p(E₂) = c_p(E)`   in   `A^p(X)`,

where `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` is the class of Stacks 0F9H
(`Stacks.Chow.localizedChernClassOfClosedCover`), `i_{2,*} ∘ -` is the pushforward of
Stacks 0EPK and `c_p(E)` is the class of Definition 0F9E (2). -/
@[stacks 0F9I "the classes c'_p: i_{2,*} ∘ c'_p(E₂) = c_p(E) for E|_{X₁} finite locally free of \
rank < p in degree 0"]
theorem pushforward_localizedChernClassOfClosedCover
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E)
    (hres : ∃ M : X₁.Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          i₁.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor X₁.Modules 0).obj M)) :
    canonicalBivariantProperPushforward C (i₂ ≫ sX) sX sX i₂ (𝟙 X) rfl (Category.id_comp sX)
        (p : ℤ)
        (bivariantClassCongr C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX
          (Category.comp_id i₂).symm rfl
          (comp_comp_structureMorphism_eq rfl (Category.id_comp sX)) (p : ℤ)
          (localizedChernClassOfClosedCover C sX i₁ i₂ hcover
            (hasDefinedChernClasses_derivedPullback i₂ hE) p
            (exists_iso_single_restriction_intersection i₁ i₂ p hres))) =
      perfectChernClass C sX hE p := by
  refine canonicalBivariantProperPushforward_closedCoverLocalizedClass C sX i₁ i₂ hcover _ _ _
    ?_ ?_
  · rw [← TotalChowClass.res_rfl_apply,
      res_perfectChernClass_derivedPullback C sX i₂ hE
        (hasDefinedChernClasses_derivedPullback i₂ hE)]
  · obtain ⟨M, hM, ⟨e⟩⟩ := hres
    rw [← TotalChowClass.res_rfl_apply,
      res_perfectChernClass_derivedPullback C sX i₁ hE
        (hasDefinedChernClasses_derivedPullback i₁ hE)]
    exact perfectChernClass_apply_eq_zero_of_iso_single C _ _ M hM e

end Statement

end Stacks.Chow

end
