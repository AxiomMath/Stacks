module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationLocalization

/-!
# The product of two localizations supported on one closed subscheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let
`Z ⊆ X` be closed, with `E = W_∞ ×_X Z`. A class `a ∈ A^m(E ⟶ W_∞)` has the localization
`(E ⟶ Z)_* ∘ a ∘ C ∈ A^m(Z ⟶ X)`, with `C ∈ A⁰(W_∞ ⟶ X)` the class of Stacks 0F9J
(`Stacks.Chow.modificationLocalization`); by the construction of Stacks 0F9K the classes `c'_p(Q)`
and `P'_p(Q)` are such localizations.

This file proves, for two classes `e ∈ A^p(E ⟶ W_∞)` and `a ∈ A^m(E ⟶ W_∞)` with `a` preserving
the image of the Gysin map at infinity, that

  `res((E ⟶ Z)_* ∘ e ∘ C) ∘ ((E ⟶ Z)_* ∘ a ∘ C) = (E ⟶ Z)_* ∘ (res(e) ∘ a) ∘ C`

in `A^{p+m}(Z ⟶ X)`, where on both sides the product is the third multiplication
`(c, c') ↦ res(c) ∘ c'` of Stacks 0FA0 (`Stacks.Chow.supportedMul`). This is the form of
Stacks 0FE7 for two classes on the same closed subscheme; Stacks 0FE7 itself is stated for the
product of Stacks 0FE5 of classes on two closed subschemes, whose support is their intersection.

## Main results

* `Stacks.Chow.supportedMul_cap` — the third multiplication of Stacks 0FA0 on the test schemes.
* `Stacks.Chow.supportedMul_modificationLocalization` — the product of two localizations on `Z`
  is the localization of the product on `W_∞`.

## Implementation notes

The proof is that of Stacks 0FE7, on every test scheme `g : V ⟶ X`. With `β` a lift of `α` to
`W ×_X V` and `a ∩ i_∞^* β = i_∞^* β'` on `W_∞ ×_X (Z ×_X V)`, the second localization caps `α`
as the pushforward of `i_∞^* β'`, on which `C` caps as `i_∞^* β'` again by Stacks 0FAR; so both
sides are pushforwards of `e ∩ i_∞^* β'` to `Z ×_X V`, along morphisms which agree.

## References

* [Stacks Project, Tag 0FE7](https://stacks.math.columbia.edu/tag/0FE7)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Cap

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) {p q : ℤ}

/-- **The third multiplication of Stacks 0FA0 on the test schemes.** On a test scheme
`t : T ⟶ X`, the product `res(c) ∘ c'` of two classes supported on the closed subscheme `Z`
caps `α` as the iterated cap product `c ∩ (c' ∩ α)`, computed on the test scheme
`Z ×_X T ⟶ X` and pushed forward along `Z ×_X (Z ×_X T) ⟶ Z ×_X T`; the two sides lie in the
Chow groups of degrees `k - (p + q)` and `(k - q) - p`. -/
theorem supportedMul_cap
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi q) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (supportedMul C sZ sX i hi c c').cap t k α ≍
      chowPush C (pullback.fst i (pullback.fst i t ≫ i) ≫ sZ) (pullback.fst i t ≫ sZ)
        (pullback.snd i (pullback.fst i t ≫ i)) (by
          subst hi; exact pullbackSnd_comp_comp_structureMorphism C _ sX i rfl _) ((k - q) - p)
        (c.cap (pullback.fst i t ≫ i) (k - q)
          (chowGroupCongr C (by rw [Category.assoc, hi]) (k - q) (c'.cap t k α))) := by
  refine (supportedLeftComp_cap C sZ sX i hi _ c' t k α).trans ?_
  rw [BivariantClass.idRule_bivariantClassCongrBase,
    closedImmersionChowCohomologyRestriction_idRule, chowGroupCongr_chowGroupCongr,
    chowGroupCongr_chowPush]

end Cap

section Localization

variable (C : ChowSituation.{u}) {X W Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- **The product of two localizations on one closed subscheme** (Stacks 0FE7 for the third
multiplication of Stacks 0FA0). Let `Z ⊆ X` be closed, `E = W_∞ ×_X Z`, and let
`e ∈ A^p(E ⟶ W_∞)` and `a ∈ A^m(E ⟶ W_∞)`, where `a` preserves the image of the Gysin map at
infinity. Then the product `res((E ⟶ Z)_* ∘ e ∘ C) ∘ ((E ⟶ Z)_* ∘ a ∘ C)` of the two
localizations is the localization of the product `res(e) ∘ a` over `W_∞`. On a test scheme, with
`β` a lift of `α` and `a ∩ i_∞^* β = i_∞^* β'`, the second localization caps `α` as the
pushforward of `i_∞^* β'`, on which the class at infinity is `i_∞^* β'` again by Stacks 0FAR; so
both sides are pushforwards of `e ∩ i_∞^* β'`. -/
theorem supportedMul_modificationLocalization (z : Z ⟶ X) [IsClosedImmersion z] {p m : ℤ}
    (e : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl p)
    (a : BivariantClass C (gysinSystemOfInvertible C)
      (pullback.fst (modificationProjectionAtInfinity f b) z ≫
        modificationProjectionAtInfinity f b ≫ f)
      (modificationProjectionAtInfinity f b ≫ f)
      (pullback.fst (modificationProjectionAtInfinity f b) z) rfl m)
    (ha : PreservesInfinityGysinImage C f b z a) :
    supportedMul C (z ≫ f) f z rfl (modificationLocalization C f b hA z e)
        (modificationLocalization C f b hA z a) =
      modificationLocalization C f b hA z
        (supportedMul C (pullback.fst (modificationProjectionAtInfinity f b) z ≫
          modificationProjectionAtInfinity f b ≫ f) (modificationProjectionAtInfinity f b ≫ f)
          (pullback.fst (modificationProjectionAtInfinity f b) z) rfl e a) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {V} g _ k α ↦ ?_
  obtain ⟨β, hβ⟩ := exists_isModificationLift C f b hA g k α
  obtain ⟨β', hβ'⟩ := ha g k β
  -- the left side
  have hL := supportedMul_cap C (z ≫ f) f z rfl (modificationLocalization C f b hA z e)
    (modificationLocalization C f b hA z a) g k α
  rw [modificationLocalization_cap_eq_of_isModificationLift C f b hA z a g k α β hβ β' hβ',
    chowGroupCongr_chowPush _ _ _ _ _ (modificationInfinityBaseChange_snd_over f b _),
    modificationLocalization_cap, gysinAtInfinityClass_cap,
    gysinCapOfLift_chowPush_modificationInfinityGysin, BivariantClass.cap_chowGroupDegreeEquiv,
    chowGroupDegreeEquiv_chowGroupDegreeEquiv] at hL
  -- the right side
  rw [modificationLocalization_cap, gysinAtInfinityClass_cap,
    gysinCapAtInfinity_eq_of_isModificationLift C f b hA g k α β hβ,
    BivariantClass.cap_chowGroupDegreeEquiv, chowGroupDegreeEquiv_chowGroupDegreeEquiv]
  have hR := supportedMul_cap C _ _ _ rfl e a
    (pullback.fst (modificationProjectionAtInfinity f b) g) k
    (modificationInfinityGysin C f b g k β)
  have h1 := eq_chowPushforwardOfIso_inv_of_eq _ _
    (pullbackFstTestIso (modificationProjectionAtInfinity f b) z g)
    (pullbackFstTestIso_hom_comp_over z g)
    (by rw [Iso.inv_comp_eq, pullbackFstTestIso_hom_comp_over]) (k - m) hβ'
  have hm := pullbackFstTestIso_inv_fst_fst (modificationProjectionAtInfinity f b) z g
  rw [h1, chowGroupCongr_chowPushforwardOfIso_target C _ _ _ _
    (by rw [modificationInfinityBaseChangeOver, ← hm]; simp only [Category.assoc])] at hR
  have h2 := e.cap_properChowPushforward (properPushforwardDescends C)
    (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z)
        (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
          pullback.fst (modificationProjectionAtInfinity f b) z)
    (pullbackFstTestIso (modificationProjectionAtInfinity f b) z g).inv
    (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z g ≫ z)) hm
    (testBaseChangeMapOfEq _ _ _ _ hm) (testBaseChangeMapOfEq_fst _ _ _ _ hm)
    (testBaseChangeMapOfEq_snd _ _ _ _ hm) (k - m)
    (modificationInfinityGysin C f b (pullback.fst z g ≫ z) (k - m) β')
  have hR' := hR.trans (heq_of_eq (congrArg _ h2))
  refine eq_of_heq (hL.trans (HEq.trans ?_ (chowPush_heq C _ _
    (pullbackFstTestMap_comp_over _ g) rfl rfl (by ring)
    ((chowGroupDegreeEquiv_heq C _ _ _).trans hR')).symm))
  refine heq_of_eq ?_
  rw [chowGroupDegreeEquiv_self]
  have hsnd : (pullbackFstTestMap (modificationProjectionAtInfinity f b) z (pullback.fst z g ≫ z) ≫
      pullback.snd z (pullback.fst z g ≫ z)) ≫ pullback.snd z g =
      (testBaseChangeMapOfEq _ _ _ _ hm ≫
        pullback.snd (pullback.fst (modificationProjectionAtInfinity f b) z)
          (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z)
            (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
              pullback.fst (modificationProjectionAtInfinity f b) z) ≫
        pullbackFstTestMap (modificationProjectionAtInfinity f b) z g) ≫ pullback.snd z g := by
    simp only [Category.assoc, pullbackFstTestMap_snd, testBaseChangeMapOfEq_snd_assoc,
      pullbackFstTestIso_inv_snd_assoc, pullback.lift_snd]
  have key : pullbackFstTestMap (modificationProjectionAtInfinity f b) z (pullback.fst z g ≫ z) ≫
      pullback.snd z (pullback.fst z g ≫ z) =
      testBaseChangeMapOfEq _ _ _ _ hm ≫
        pullback.snd (pullback.fst (modificationProjectionAtInfinity f b) z)
          (pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z)
            (pullback.fst (modificationProjectionAtInfinity f b) g) ≫
              pullback.fst (modificationProjectionAtInfinity f b) z) ≫
        pullbackFstTestMap (modificationProjectionAtInfinity f b) z g := by
    refine pullback.hom_ext ((cancel_mono z).1 ?_) hsnd
    simpa only [Category.assoc, pullback.condition (f := z) (g := g)] using hsnd =≫ g
  have hover : (pullbackFstTestMap (modificationProjectionAtInfinity f b) z (pullback.fst z g ≫ z) ≫
      pullback.snd z (pullback.fst z g ≫ z)) ≫ pullback.fst z g ≫ z ≫ f =
      pullback.fst (pullback.fst (modificationProjectionAtInfinity f b) z)
          (pullback.fst (modificationProjectionAtInfinity f b) (pullback.fst z g ≫ z)) ≫
        pullback.fst (modificationProjectionAtInfinity f b) z ≫
          modificationProjectionAtInfinity f b ≫ f := by
    rw [Category.assoc, ← pullbackFstTestMap_comp_over z (pullback.fst z g ≫ z)]
    congr 1
    simpa only [Category.assoc] using
      (pullback.condition (f := z) (g := pullback.fst z g ≫ z) =≫ f).symm
  refine (chowPush_comp C _ _ _ _ _ _ rfl _ _ hover _ _).trans ?_
  refine (chowPush_congr C _ _ key _ (key ▸ hover) _ _).trans ?_
  exact (chowPush_comp_comp _ _ _ _ _ _ _ _ _ _ _ _ _).symm

end Localization

end Stacks.Chow

end
