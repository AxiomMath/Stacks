module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityGysinNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityPushforward

/-!
# The canonical class at infinity

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, and let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over the standard
affine chart `𝐀¹_X`. Stacks 0F9J constructs a bivariant class `C ∈ A⁰(W_∞ ⟶ X)` for the fibre at
infinity `W_∞ ⊆ W`: on a test scheme `T ⟶ X` locally of finite type, `C ∩ α = i_∞^* β` for any
class `β` on `W ×_X T` restricting to the flat pullback of `α` over `𝐀¹_X`; and it shows
`i_{∞,*}(C ∩ α) = i_{0,*} α`.

This file assembles that class from the cap operation `Stacks.Chow.gysinCapAtInfinity` and its
three naturality laws, and packages it with the pushforward identity as the inhabitant of
`Stacks.Chow.GysinAtInfinityData`.

## Main definitions

* `Stacks.Chow.gysinAtInfinityClass` — **Stacks 0F9J**: the bivariant class
  `C ∈ A⁰(W_∞ ⟶ X)`.
* `Stacks.Chow.gysinAtInfinityData` — **Stacks 0F9J**: the class together with the identity
  `i_{∞,*}(C ∩ α) = i_{0,*} α` on every test scheme.

## Main results

* `Stacks.Chow.gysinAtInfinityClass_cap` — the cap operation of the class is
  `Stacks.Chow.gysinCapAtInfinity`, read in the degree `k - 0` in which a class of degree `0` caps.

## Implementation notes

The cap operation of a bivariant class of degree `p` lands in degree `k - p`, while
`Stacks.Chow.gysinCapAtInfinity` lands in degree `k`; for `p = 0` the two are identified by
`Stacks.Chow.chowGroupDegreeEquiv`, and the three laws of Stacks 0B76 are transported along it.

The Gysin system is `Stacks.Chow.gysinSystemOfInvertible C`, whose Gysin maps are those of
Stacks 02TO; the Gysin law of the class is the case `Stacks.Chow.gysinCapOfLift_gysin` of
Stacks 0B73 for those maps.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- **Stacks 0F9J, the class at infinity.** The degree-zero bivariant class
`C ∈ A⁰(W_∞ ⟶ X)` whose cap operation on a test scheme `T ⟶ X` is `α ↦ i_∞^* β` for a lift `β`
of `α` to `W ×_X T` (`Stacks.Chow.gysinCapAtInfinity`). -/
@[stacks 0F9J "the canonical bivariant class C in A⁰(W_∞ ⟶ X)"]
def gysinAtInfinityClass :
    BivariantClass C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
      (modificationProjectionAtInfinity f b) rfl 0 where
  cap g _ k := (chowGroupDegreeEquiv C (modificationInfinityBaseChangeOver f b g)
    (sub_zero k).symm).toAddMonoidHom.comp (gysinCapAtInfinity C f b hA g k)
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
    refine (heq_of_eq (gysinCapOfLift_properChowPushforward C f b g h hA k h' sq.w.symm
      hfst α)).trans ?_
    exact properChowPushforward_heq_congr C _ _ h' _ (sub_zero k).symm _ _ _ _
      (chowGroupDegreeEquiv_heq C _ _ _).symm
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ r hr h' sq hfst k
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    intro α
    have hr' := AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    refine (heq_of_eq (gysinCapOfLift_flatPullbackChow C f b g h r hr hA k h' sq.w.symm hfst hr'
      α)).trans ?_
    exact flatPullbackChow_heq_congr C _ _ h' h' _ _ rfl rfl hr' hr' (sub_zero k).symm _ _ _ _
      (chowGroupDegreeEquiv_heq C _ _ _).symm
  cap_gysin := by
    intro T g _ L _ s k D L' s' E e he hbase α
    refine eq_of_heq ((properChowPushforward_heq_congr C _ _ e.hom hbase (sub_zero k) _
      (properPushforwardDescends C _ _ _ _ _) _ _ (chowGroupDegreeEquiv_heq C _ _ _)).trans ?_)
    refine (heq_of_eq (gysinCapOfLift_gysin C f b g L s hA k e he hbase α)).trans ?_
    exact gysinSystemOnChow_heq_congr _ _ _ _ (sub_zero k).symm _ _
      ((chowGroupDegreeEquiv_heq C _ _ _).symm.trans
        (eq_mp_chowGroup_heq C _ (by omega : k + 1 - 0 = k - 0 + 1) _).symm)

/-- The cap operation of the class at infinity is `Stacks.Chow.gysinCapAtInfinity`, transported to
the degree `k - 0` in which a class of degree `0` caps. -/
theorem gysinAtInfinityClass_cap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ f) k) :
    (gysinAtInfinityClass C f b hA).cap g k α =
      chowGroupDegreeEquiv C (modificationInfinityBaseChangeOver f b g) (sub_zero k).symm
        (gysinCapAtInfinity C f b hA g k α) :=
  rfl

/-- **Stacks 0F9J.** The class at infinity `C ∈ A⁰(W_∞ ⟶ X)` of `Stacks.Chow.gysinAtInfinityClass`
together with the identity `i_{∞,*}(C ∩ α) = i_{0,*} α` on every test scheme locally of finite
type over `X` (`Stacks.Chow.chowPushforward_gysinCapOfLift`). -/
@[stacks 0F9J "the class C in A⁰(W_∞ ⟶ X) with i_{∞,*}(C ∩ α) = i_{0,*} α, built from the cap \
operation i_∞^* of a lift and its three bivariance laws"]
def gysinAtInfinityData : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA where
  finiteTypeModification := inferInstance
  finiteTypeInfinity := inferInstance
  properModification := inferInstance
  properProjectionAtInfinity := inferInstance
  isIsoFibreAtZero := isIso_modificationFibreAtZeroProjection f b hA
  sectionAtZero_comp := modificationSectionAtZero_comp_projection f b hA
  properInclusionAtInfinity _ := inferInstance
  properSectionAtZero g :=
    haveI := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
    inferInstance
  bivariantClass := gysinAtInfinityClass C f b hA
  pushforward_formula := by
    intro T g _ k hfacInf hfacZero α
    have := isClosedImmersion_modificationSectionAtZeroBaseChange f b g hA
    have h := chowPushforward_gysinCapOfLift C f b g hA k α
    refine Eq.trans ?_ h
    refine congrArg (properChowPushforward C _ _ _ _ k hfacInf) (eq_of_heq ?_)
    exact (eq_mp_chowGroup_heq C _ (sub_zero k) _).trans (chowGroupDegreeEquiv_heq C _ _ _)

/-- The class of `Stacks.Chow.gysinAtInfinityData` is `Stacks.Chow.gysinAtInfinityClass`. -/
@[simp]
theorem gysinAtInfinityData_bivariantClass :
    (gysinAtInfinityData C f b hA).bivariantClass = gysinAtInfinityClass C f b hA :=
  rfl

end Stacks.Chow

end
