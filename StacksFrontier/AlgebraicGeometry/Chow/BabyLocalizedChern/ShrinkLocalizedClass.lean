module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChernShrink
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.LocalizedChernGysinCommute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedClassAtInfinity.Construction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardCanonical
public import StacksCore.Tactic.StacksAttribute

/-!
# Shrinking the localized classes of a closed cover (Stacks 0FAI)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let
`i_j : X_j ⟶ X` (`j = 1, 2`) be closed immersions with `X = X₁ ∪ X₂` set theoretically, and let
`E₂ ∈ D(𝒪_{X₂})` be a perfect object whose Chern classes are defined, with `E₂|_{X₁ ∩ X₂}` zero,
respectively finite locally free of rank `< p` in degree `0`, so that the class
`P'_p(E₂)`, respectively `c'_p(E₂) ∈ A^p(X₂ ⟶ X)` of Stacks 0F9H is defined.

**Stacks 0FAI.** Let `X₂' ⊂ X₂` and `X₁ ⊂ X₁' ⊂ X` be closed subschemes with
`X = X₁' ∪ X₂'` set theoretically, and assume `E₂|_{X₁' ∩ X₂}` is zero, respectively finite
locally free of rank `< p` in degree `0`. Then

  `(X₂' ⟶ X₂)_* ∘ P'_p(E₂|_{X₂'}) = P'_p(E₂)`,  resp.  `(X₂' ⟶ X₂)_* ∘ c'_p(E₂|_{X₂'}) = c'_p(E₂)`,

where `P'_p(E₂|_{X₂'})`, `c'_p(E₂|_{X₂'}) ∈ A^p(X₂' ⟶ X)` are the classes of Stacks 0F9H for
the cover `X = X₁' ∪ X₂'` and `(X₂' ⟶ X₂)_* ∘ -` is the proper pushforward of Stacks 0EPK.

## The argument

The source's proof is the characterization of Stacks 0F9H. The class `κ = P_p(E₂)`, resp.
`c_p(E₂)`, restricts to zero on `X₁' ∩ X₂`, so it has a localized class for the cover
`X = X₁' ∪ X₂`; by uniqueness (Stacks 0FAH, `Stacks.Chow.eq_of_isClosedCoverLocalizedClass`) that
class is `P'_p(E₂)`, resp. `c'_p(E₂)`. The class `κ' = P_p(E₂|_{X₂'})`, resp.
`c_p(E₂|_{X₂'})`, is the restriction of `κ` to `X₂'` (Stacks 0F9E, compatibility with pullback),
and the pushforward of its localized class along `X₂' ⟶ X₂` is the localized class of `κ`
(`Stacks.Chow.eq_of_isBivariantProperPushforward_of_isClosedCoverLocalizedClass`, which tests
both classes against fundamental classes of integral schemes, Stacks 02UC).

## Main results

* `Stacks.Chow.canonicalBivariantProperPushforward_eq_of_isClosedCoverLocalizedClass` — the
  pushforward along `X₂' ⟶ X₂` of the localized class of `κ'` for `X = X₁' ∪ X₂'` is the
  localized class of `κ` for `X = X₁' ∪ X₂`, whenever `κ'` operates as `κ` does.
* `Stacks.Chow.canonicalBivariantProperPushforward_localizedPowerSumOfClosedCover` —
  **Stacks 0FAI** for `P'_p`.
* `Stacks.Chow.canonicalBivariantProperPushforward_localizedChernClassOfClosedCover` —
  **Stacks 0FAI** for `c'_p`.

## Implementation notes

`X₂' ⊂ X₂` is a closed immersion `j : X₂' ⟶ X₂`, and `X₂'` is a closed subscheme of `X` through
`j ≫ i₂`; `E₂|_{X₂'}` is the derived pullback `Lj^*E₂`. The inclusion `X₁ ⊂ X₁'` of closed
subschemes of `X` is a factorization of `i₁` through `i₁' : X₁' ⟶ X`. The structure morphism of
`X₂'` carried by the class of Stacks 0F9H is `(j ≫ i₂) ≫ sX`, and the pushforward of Stacks 0EPK is
taken with the equality `j ≫ i₂ ≫ sX = (j ≫ i₂) ≫ sX`.

## References

* [Stacks Project, Tag 0FAI](https://stacks.math.columbia.edu/tag/0FAI)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FAH](https://stacks.math.columbia.edu/tag/0FAH)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow.GysinAtInfinity (isClosedCoverLocalizedClass_closedCoverLocalizedClass)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The pushforward of a localized class along a smaller second member -/

section General

variable (C : ChowSituation.{u}) {X X₁' X₂ X₂' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sX₁' : X₁' ⟶ C.S) [LocallyOfFiniteType sX₁'] (sX₂ : X₂ ⟶ C.S)
  [LocallyOfFiniteType sX₂] (sX₂' : X₂' ⟶ C.S) [LocallyOfFiniteType sX₂'] (i₁' : X₁' ⟶ X)
  [IsClosedImmersion i₁'] (hi₁' : i₁' ≫ sX = sX₁') (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂]
  (hi₂ : i₂ ≫ sX = sX₂) (j : X₂' ⟶ X₂) [IsClosedImmersion j] (hj : j ≫ sX₂ = sX₂') {p : ℤ}

/-- **The pushforward of a localized class along a smaller second member.** Let
`X = X₁' ∪ X₂'` set theoretically with `X₂' ⊂ X₂` closed, let `κ ∈ A^p(X₂)` and let
`κ' ∈ A^p(X₂')` operate on every test scheme `T ⟶ X₂'` as `κ` does on `T ⟶ X₂' ⟶ X₂`. If `c'`
is the localized class of `κ'` for the cover `X = X₁' ∪ X₂'` and `c` that of `κ` for the cover
`X = X₁' ∪ X₂`, both characterized as in Stacks 0F9H, then `(X₂' ⟶ X₂)_* ∘ c' = c`, the
pushforward being that of Stacks 0EPK. -/
theorem canonicalBivariantProperPushforward_eq_of_isClosedCoverLocalizedClass
    (hcover : Set.range i₁'.base ∪ Set.range (j ≫ i₂).base = Set.univ)
    {κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p}
    {κ' : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂' p}
    (hκ' : ∀ {T : Scheme.{u}} (t : T ⟶ X₂') [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sX₂') k) (β : chowGroup C ((t ≫ j) ≫ sX₂) k), α ≍ β →
      κ'.idRule C sX₂' (gysinSystemOfInvertible C) t k α ≍
        κ.idRule C sX₂ (gysinSystemOfInvertible C) (t ≫ j) k β)
    {c : BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p}
    {c' : BivariantClass C (gysinSystemOfInvertible C) sX₂' sX (j ≫ i₂)
      (comp_comp_structureMorphism_eq hj hi₂) p}
    (hc : IsClosedCoverLocalizedClass C (gysinSystemOfInvertible C) sX sX₁' sX₂ i₁' hi₁' i₂ hi₂
      p κ c)
    (hc' : IsClosedCoverLocalizedClass C (gysinSystemOfInvertible C) sX sX₁' sX₂' i₁' hi₁'
      (j ≫ i₂) (comp_comp_structureMorphism_eq hj hi₂) p κ' c') :
    canonicalBivariantProperPushforward C sX₂' sX₂ sX j i₂ hj hi₂ p c' = c := by
  subst hj
  have hres : κ' = chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ j p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ := by
    refine BivariantClass.eq_of_idRule_eq C (j ≫ sX₂) (gysinSystemOfInvertible C) _ _
      fun t _ k α ↦ eq_of_heq ?_
    exact (hκ' t k α α HEq.rfl).trans
      (BivariantClass.idRule_chowCohomologyRestriction_heq j κ t k α α HEq.rfl).symm
  subst hres
  exact eq_of_isBivariantProperPushforward_of_isClosedCoverLocalizedClass C
    (gysinSystemOfInvertible C) sX sX₁' sX₂ i₁' hi₁' i₂ hi₂ j p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) hcover hc hc' fun _ _ _ _ ↦ rfl

end General

/-! ### Stacks 0FAI -/

section Statement

variable (C : ChowSituation.{u}) {X X₁ X₁' X₂ X₂' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (i₁' : X₁' ⟶ X)
  [IsClosedImmersion i₁'] (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (j : X₂' ⟶ X₂)
  [IsClosedImmersion j]

omit [IsClosedImmersion i₁'] [IsClosedImmersion i₂] [IsClosedImmersion j] in
/-- The second member of a cover may be enlarged: if `X = X₁' ∪ X₂'` with `X₂' ⊂ X₂`, then
`X = X₁' ∪ X₂`. -/
theorem range_union_range_of_range_comp
    (hcover' : Set.range i₁'.base ∪ Set.range (j ≫ i₂).base = Set.univ) :
    Set.range i₁'.base ∪ Set.range i₂.base = Set.univ := by
  refine Set.univ_subset_iff.mp (hcover' ▸ Set.union_subset_union_right _ ?_)
  rintro _ ⟨y, rfl⟩
  exact ⟨j.base y, by simp⟩

/-- The morphism `X₁' ∩ X₂' ⟶ X₁' ∩ X₂` of scheme-theoretic intersections. -/
abbrev intersectionShrink : pullback i₁' (j ≫ i₂) ⟶ pullback i₁' i₂ :=
  pullback.lift (pullback.fst i₁' (j ≫ i₂)) (pullback.snd i₁' (j ≫ i₂) ≫ j)
    (by rw [pullback.condition, Category.assoc])

omit [IsClosedImmersion i₁'] [IsClosedImmersion i₂] [IsClosedImmersion j] in
/-- The restriction of `E₂|_{X₂'}` to `X₁' ∩ X₂'` is the pullback of the restriction of `E₂` to
`X₁' ∩ X₂`: the two composites `X₁' ∩ X₂' ⟶ X₂` agree. -/
theorem snd_comp_eq_intersectionShrink_comp_snd :
    pullback.snd i₁' (j ≫ i₂) ≫ j = intersectionShrink i₁' i₂ j ≫ pullback.snd i₁' i₂ :=
  (pullback.lift_snd _ _ _).symm

variable {E₂ : DerivedCategory X₂.Modules} (hE₂ : HasDefinedChernClasses E₂) (p : ℕ)

omit [IsClosedImmersion j] in
/-- `E₂|_{X₂'}` is perfect when `E₂` is. -/
theorem isPerfect_shrink
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂) :
    RingedSpace.IsPerfect.{u, u + 1} (X := X₂'.toRingedSpace)
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j.toLRSHom.toShHom).obj E₂) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E₂ perfect

omit [IsClosedImmersion i₁'] [IsClosedImmersion i₂] [IsClosedImmersion j] in
/-- If `E₂|_{X₁' ∩ X₂}` is zero, so is the restriction of `E₂|_{X₂'}` to `X₁' ∩ X₂'`. -/
theorem isZero_shrink
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁' i₂).toLRSHom.toShHom).obj E₂)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁' (j ≫ i₂)).toLRSHom.toShHom).obj
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j.toLRSHom.toShHom).obj E₂)) :=
  isZero_derivedPullback_of_comp_eq _ _ _ _ (snd_comp_eq_intersectionShrink_comp_snd i₁' i₂ j) E₂
    hzero'

omit [IsClosedImmersion i₁'] [IsClosedImmersion i₂] [IsClosedImmersion j] in
/-- If `E₂|_{X₁' ∩ X₂}` is finite locally free of rank `< p` in degree `0`, so is the
restriction of `E₂|_{X₂'}` to `X₁' ∩ X₂'`. -/
theorem exists_iso_single_shrink
    (hres' : ∃ M : (pullback i₁' i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁' i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁' i₂).Modules 0).obj M)) :
    ∃ M : (pullback i₁' (j ≫ i₂)).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁' (j ≫ i₂)).toLRSHom.toShHom).obj
          ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback j.toLRSHom.toShHom).obj
            E₂) ≅ (DerivedCategory.singleFunctor (pullback i₁' (j ≫ i₂)).Modules 0).obj M) :=
  exists_iso_single_derivedPullback_of_comp_eq _ _ _ _
    (snd_comp_eq_intersectionShrink_comp_snd i₁' i₂ j) E₂ hres'

/-- **Stacks 0FAI, for the classes `P_p`.** In the situation of Stacks 0F9H — closed immersions
`i_j : X_j ⟶ X` with `X = X₁ ∪ X₂` set theoretically, and `E₂ ∈ D(𝒪_{X₂})` perfect with
defined Chern classes and `E₂|_{X₁ ∩ X₂}` zero — let `X₂' ⊂ X₂` and `X₁ ⊂ X₁' ⊂ X` be closed
subschemes with `X = X₁' ∪ X₂'` set theoretically, and assume `E₂|_{X₁' ∩ X₂}` is zero. Then

  `(X₂' ⟶ X₂)_* ∘ P'_p(E₂|_{X₂'}) = P'_p(E₂)`   in   `A^p(X₂ ⟶ X)`,

where `P'_p(E₂|_{X₂'}) ∈ A^p(X₂' ⟶ X)` is the class of Stacks 0F9H for the cover
`X = X₁' ∪ X₂'` (`Stacks.Chow.localizedPowerSumOfClosedCover`), `P'_p(E₂)` the one for
`X = X₁ ∪ X₂`, and `(X₂' ⟶ X₂)_* ∘ -` the proper pushforward of Stacks 0EPK. -/
@[stacks 0FAI "the classes P'_p: (X₂' ⟶ X₂)_* ∘ P'_p(E₂|_{X₂'}) = P'_p(E₂) for E₂|_{X₁' ∩ X₂} \
zero"]
theorem canonicalBivariantProperPushforward_localizedPowerSumOfClosedCover
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hzero : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂))
    (_hX₁ : ∃ ι : X₁ ⟶ X₁', ι ≫ i₁' = i₁)
    (hcover' : Set.range i₁'.base ∪ Set.range (j ≫ i₂).base = Set.univ)
    (hzero' : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.snd i₁' i₂).toLRSHom.toShHom).obj E₂)) :
    canonicalBivariantProperPushforward C ((j ≫ i₂) ≫ sX) (i₂ ≫ sX) sX j i₂
        (Category.assoc j i₂ sX).symm rfl (p : ℤ)
        (localizedPowerSumOfClosedCover C sX i₁' (j ≫ i₂) hcover'
          (hasDefinedChernClasses_derivedPullback j hE₂) p (isPerfect_shrink j perfect)
          (isZero_shrink i₁' i₂ j hzero')) =
      localizedPowerSumOfClosedCover C sX i₁ i₂ hcover hE₂ p perfect hzero := by
  have hcover₂ := range_union_range_of_range_comp i₁' i₂ j hcover'
  have hκ := chowCohomologyRestriction_perfectPowerSumComponent_eq_zero C (i₂ ≫ sX) perfect hE₂
    (pullback.snd i₁' i₂) hzero' p
  have e : localizedPowerSumOfClosedCover C sX i₁ i₂ hcover hE₂ p perfect hzero =
      closedCoverLocalizedClass C sX (i₁' ≫ sX) (i₂ ≫ sX) i₁' rfl i₂ rfl hcover₂ _ hκ :=
    eq_of_isClosedCoverLocalizedClass C _ sX (i₁ ≫ sX) (i₁' ≫ sX) (i₂ ≫ sX) i₁ rfl i₁' rfl i₂
      rfl _ hcover hcover₂
      (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁ rfl i₂ rfl hcover _ _)
      (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl i₂ rfl hcover₂ _ hκ)
  rw [e]
  refine canonicalBivariantProperPushforward_eq_of_isClosedCoverLocalizedClass C sX (i₁' ≫ sX)
    (i₂ ≫ sX) ((j ≫ i₂) ≫ sX) i₁' rfl i₂ rfl j (Category.assoc j i₂ sX).symm hcover' ?_
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl i₂ rfl hcover₂ _ hκ)
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl (j ≫ i₂) rfl
      hcover' _ _)
  intro T t _ k α β hαβ
  rw [← perfectPowerSumTotal_apply C (i₂ ≫ sX) hE₂ p,
    ← perfectPowerSumTotal_apply C ((j ≫ i₂) ≫ sX) (hasDefinedChernClasses_derivedPullback j hE₂) p]
  exact idRule_heq_of_res_eq C (i₂ ≫ sX) j (Category.assoc j i₂ sX).symm
    (res_perfectPowerSumTotal_derivedPullback C (i₂ ≫ sX) j _ perfect hE₂
      (isPerfect_shrink j perfect) (hasDefinedChernClasses_derivedPullback j hE₂))
    p t k α β hαβ

/-- **Stacks 0FAI, for the Chern classes.** In the situation of Stacks 0F9H — closed immersions
`i_j : X_j ⟶ X` with `X = X₁ ∪ X₂` set theoretically, and `E₂ ∈ D(𝒪_{X₂})` perfect with
defined Chern classes and `E₂|_{X₁ ∩ X₂}` isomorphic to a finite locally free module of rank
`< p` in degree `0` — let `X₂' ⊂ X₂` and `X₁ ⊂ X₁' ⊂ X` be closed subschemes with
`X = X₁' ∪ X₂'` set theoretically, and assume `E₂|_{X₁' ∩ X₂}` is isomorphic to a finite locally
free module of rank `< p` placed in degree `0`. Then

  `(X₂' ⟶ X₂)_* ∘ c'_p(E₂|_{X₂'}) = c'_p(E₂)`   in   `A^p(X₂ ⟶ X)`,

where `c'_p(E₂|_{X₂'}) ∈ A^p(X₂' ⟶ X)` is the class of Stacks 0F9H for the cover
`X = X₁' ∪ X₂'` (`Stacks.Chow.localizedChernClassOfClosedCover`), `c'_p(E₂)` the one for
`X = X₁ ∪ X₂`, and `(X₂' ⟶ X₂)_* ∘ -` the proper pushforward of Stacks 0EPK. -/
@[stacks 0FAI "the classes c'_p: (X₂' ⟶ X₂)_* ∘ c'_p(E₂|_{X₂'}) = c'_p(E₂) for E₂|_{X₁' ∩ X₂} \
finite locally free of rank < p in degree 0"]
theorem canonicalBivariantProperPushforward_localizedChernClassOfClosedCover
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (_perfect : RingedSpace.IsPerfect.{u, u + 1} (X := X₂.toRingedSpace) E₂)
    (hres : ∃ M : (pullback i₁ i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁ i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁ i₂).Modules 0).obj M))
    (_hX₁ : ∃ ι : X₁ ⟶ X₁', ι ≫ i₁' = i₁)
    (hcover' : Set.range i₁'.base ∪ Set.range (j ≫ i₂).base = Set.univ)
    (hres' : ∃ M : (pullback i₁' i₂).Modules, IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (pullback.snd i₁' i₂).toLRSHom.toShHom).obj E₂ ≅
        (DerivedCategory.singleFunctor (pullback i₁' i₂).Modules 0).obj M)) :
    canonicalBivariantProperPushforward C ((j ≫ i₂) ≫ sX) (i₂ ≫ sX) sX j i₂
        (Category.assoc j i₂ sX).symm rfl (p : ℤ)
        (localizedChernClassOfClosedCover C sX i₁' (j ≫ i₂) hcover'
          (hasDefinedChernClasses_derivedPullback j hE₂) p
          (exists_iso_single_shrink i₁' i₂ j p hres')) =
      localizedChernClassOfClosedCover C sX i₁ i₂ hcover hE₂ p hres := by
  have hcover₂ := range_union_range_of_range_comp i₁' i₂ j hcover'
  have hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX)
      (pullback.snd i₁' i₂) (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (perfectChernClass C (i₂ ≫ sX) hE₂ p) = 0 := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hres'
    exact chowCohomologyRestriction_perfectChernClass_eq_zero C sX i₁' i₂ hE₂ p M hM e
  have e : localizedChernClassOfClosedCover C sX i₁ i₂ hcover hE₂ p hres =
      closedCoverLocalizedClass C sX (i₁' ≫ sX) (i₂ ≫ sX) i₁' rfl i₂ rfl hcover₂ _ hκ :=
    eq_of_isClosedCoverLocalizedClass C _ sX (i₁ ≫ sX) (i₁' ≫ sX) (i₂ ≫ sX) i₁ rfl i₁' rfl i₂
      rfl _ hcover hcover₂
      (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁ rfl i₂ rfl hcover _ _)
      (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl i₂ rfl hcover₂ _ hκ)
  rw [e]
  refine canonicalBivariantProperPushforward_eq_of_isClosedCoverLocalizedClass C sX (i₁' ≫ sX)
    (i₂ ≫ sX) ((j ≫ i₂) ≫ sX) i₁' rfl i₂ rfl j (Category.assoc j i₂ sX).symm hcover' ?_
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl i₂ rfl hcover₂ _ hκ)
    (isClosedCoverLocalizedClass_closedCoverLocalizedClass C sX _ _ i₁' rfl (j ≫ i₂) rfl
      hcover' _ _)
  intro T t _ k α β hαβ
  exact idRule_heq_of_res_eq C (i₂ ≫ sX) j (Category.assoc j i₂ sX).symm
    (res_perfectChernClass_derivedPullback_of_eq C (i₂ ≫ sX) j _ hE₂
      (hasDefinedChernClasses_derivedPullback j hE₂))
    p t k α β hαβ

end Statement

end Stacks.Chow

end
