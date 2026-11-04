module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ClosedCoverLocalizedClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyMultiplicative
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksCore.Tactic.StacksAttribute

/-!
# Shrinking the support of the localized class of a cover by two closed subschemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `i₂ : X₂ ⟶ X` be a closed immersion. **Stacks 0F9H**
attaches to a perfect object `E₂ ∈ D(𝒪_{X₂})` whose Chern classes are defined and whose
restriction to `X₁ ∩ X₂` vanishes, respectively is finite locally free of rank `< p` in degree
`0`, bivariant classes `P'_p(E₂)`, `c'_p(E₂) ∈ A^p(X₂ ⟶ X)`, characterized by

  `c'_p(E₂) ∩ i₂,*α₂ = c_p(E₂) ∩ α₂`  and  `c'_p(E₂) ∩ i₁,*α₁ = 0`

and similarly after any base change.

**Stacks 0FAI** says that the support may be shrunk: given closed subschemes `X₂' ⊂ X₂` and
`X₁ ⊂ X₁' ⊂ X` with `X = X₁' ∪ X₂'` set theoretically, and with `E₂|_{X₁' ∩ X₂}` zero
respectively finite locally free of rank `< p` in degree `0`,

  `(X₂' ⟶ X₂)_* ∘ P'_p(E₂|_{X₂'}) = P'_p(E₂)`,  resp.  `(X₂' ⟶ X₂)_* ∘ c'_p(E₂|_{X₂'}) = c'_p(E₂)`

in `A^p(X₂ ⟶ X)`, the composition being the proper pushforward of **Stacks 0EPK**.

## Main results

* `Stacks.Chow.eq_of_isBivariantProperPushforward_of_isClosedCoverLocalizedClass`: the proper
  pushforward along `X₂' ⟶ X₂` of the localized class of the cover `X = X₁' ∪ X₂'` is the
  localized class of the cover `X = X₁' ∪ X₂`.
* `Stacks.Chow.surjective_chowPushforwardOfIsClosedImmersion`: pushforward on Chow groups along a
  closed immersion surjective on points is surjective, with no reducedness assumption on the
  target.
* `Stacks.Chow.surjective_closedCoverPushforward`: every Chow class on a test scheme filled by the
  base-changed member of a closed cover is pushed forward from that member.
* `Stacks.Chow.properChowPushforward_congr_source`, `Stacks.Chow.toIdentityCapRule_congr_test`:
  proper pushforward and the identity cap rule commute with transport along an equality of
  structure morphisms.

## Implementation notes

The statement is about an arbitrary class `κ ∈ A^p(X₂)`, its restriction to `X₂'`, and arbitrary
bivariant classes with the characterizing property `Stacks.Chow.IsClosedCoverLocalizedClass` of
Stacks 0F9H, the pushed-forward class being any class with the characterizing property of
Stacks 0EPK. Both localized classes are taken with first member `X₁'`; the class `P'_p(E₂)` built
from `X₁` is the class for `X₁'` by Stacks 0FAH.

## References

* [Stacks Project, Tag 0FAI](https://stacks.math.columbia.edu/tag/0FAI)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0FAH](https://stacks.math.columbia.edu/tag/0FAH)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transports along an equality of structure morphisms -/

/-- Proper pushforward on Chow groups is unchanged by transporting its source along an equality
of structure morphisms. -/
theorem properChowPushforward_congr_source (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hsA : sA = sA')
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (w : A ⟶ B) [IsProper w] (hw : w ≫ sB = sA)
    (hw' : w ≫ sB = sA') (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB w hw k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB w hw' k)
    (α : chowGroup C sA k) :
    properChowPushforward C sA' sB w hw' k hfac' (chowGroupCongr C hsA k α) =
      properChowPushforward C sA sB w hw k hfac α := by
  subst hsA
  rfl

/-- The identity cap rule of a class for `𝟙 X` is unchanged by replacing its test morphism with
an equal one, the Chow classes being transported along the resulting equality of structure
morphisms. -/
theorem toIdentityCapRule_congr_test (C : ChowSituation.{u}) (G : GysinSystem C)
    {X T : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)
    (κ : chowCohomologyComponent C G sX p) {u v : T ⟶ X} [LocallyOfFiniteType u]
    [LocallyOfFiniteType v] (huv : u = v) (hs : u ≫ sX = v ≫ sX) (k : ℤ)
    (α : chowGroup C (u ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX p κ v k (chowGroupCongr C hs k α) =
      chowGroupCongr C hs (k - p) (BivariantClass.toIdentityCapRule C G sX p κ u k α) := by
  subst huv
  rfl

/-- Proper pushforward on Chow groups along a proper birational morphism onto an integral scheme
carries the fundamental class to the fundamental class. -/
theorem properChowPushforward_fundamentalChowClass_of_isBirational (C : ChowSituation.{u})
    {T T' : Scheme.{u}} (sT' : T' ⟶ C.S) [LocallyOfFiniteType sT'] (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] [IsIntegral T] (h : T' ⟶ T) [IsProper h] (hcomp : h ≫ sT = sT')
    (hbir : AlgebraicGeometry.IsBirational h) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sT' sT h hcomp k) :
    properChowPushforward C sT' sT h hcomp k hfac (fundamentalChowClass C sT' k) =
      fundamentalChowClass C sT k := by
  unfold fundamentalChowClass
  rw [properChowPushforward_mk,
    properPushforward_fundamentalCycle_of_isBirational C sT' sT h hcomp hbir k]

/-! ### Chow classes on a set-theoretically full closed subscheme -/

/-- Pushforward on Chow groups along a closed immersion that is surjective on points is
surjective, with no reducedness assumption on the target. -/
theorem surjective_chowPushforwardOfIsClosedImmersion (C : ChowSituation.{u})
    {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
    (hsurj : Function.Surjective i.base) (k : ℤ) :
    Function.Surjective (chowPushforwardOfIsClosedImmersion C sZ sX i hi k) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H α =>
    obtain ⟨β, hβ⟩ :=
      (properPushforward_bijective_of_surjective C sZ sX i hi k hsurj).2 α
    refine ⟨QuotientAddGroup.mk' (rationalEquivalences C sZ k) β, ?_⟩
    rw [chowPushforwardOfIsClosedImmersion_mk, hβ]
    rfl

/-- If the base change to a test scheme `T` of a member of a closed cover is surjective onto `T`,
then every Chow class on `T` is pushed forward from that base-changed member. -/
theorem surjective_closedCoverPushforward (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (hrange : Set.range (pullback.snd i g).base = Set.univ) (k : ℤ) :
    Function.Surjective (closedCoverPushforward C sX sZ i hi g k) :=
  surjective_chowPushforwardOfIsClosedImmersion C (pullback.fst i g ≫ sZ) (g ≫ sX)
    (pullback.snd i g) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi g)
    (Set.range_eq_univ.mp hrange) k

/-! ### Stacks 0FAI: shrinking the second member of the cover -/

section Shrink

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X₁' X₂ X₂' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sX₁' : X₁' ⟶ C.S) [LocallyOfFiniteType sX₁']
  (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂] (i₁' : X₁' ⟶ X) [IsClosedImmersion i₁']
  (hi₁' : i₁' ≫ sX = sX₁') (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ sX = sX₂)
  (j₂ : X₂' ⟶ X₂) [IsClosedImmersion j₂] (p : ℤ)

/-- A localized class of a closed cover caps the fundamental class of an integral test scheme, on
which the second member is surjective, to the cap of the underlying class with the fundamental
class of the base-changed second member. -/
private theorem cap_fundamentalChowClass_eq_toIdentityCapRule {Z : Scheme.{u}}
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {i : Z ⟶ X} [IsClosedImmersion i]
    {hi : i ≫ sX = sZ} {κ : chowCohomologyComponent C G sZ p} {c : BivariantClass C G sZ sX i hi p}
    (hc : IsClosedCoverLocalizedClass C G sX sX₁' sZ i₁' hi₁' i hi p κ c) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] [IsIntegral T]
    (hrange : Set.range (pullback.snd i g).base = Set.univ) (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ sX) k) =
      BivariantClass.toIdentityCapRule C G sZ p κ (pullback.fst i g) k
        (fundamentalChowClass C (pullback.fst i g ≫ sZ) k) := by
  conv_lhs => rw [← closedCoverPushforward_fundamentalChowClass C sX sZ i hi g hrange k]
  exact hc.2 g k _

/-- The proper pushforward of Stacks 0EPK along a closed immersion `j₂ : X₂' ⟶ X₂`, applied to the
localized class of Stacks 0F9H for the cover `X = X₁' ∪ X₂'` and for the restriction of
`κ ∈ A^p(X₂)` to `X₂'`, is the localized class of Stacks 0F9H for the cover `X = X₁' ∪ X₂` and
for `κ` itself. -/
theorem eq_of_isBivariantProperPushforward_of_isClosedCoverLocalizedClass
    (hgys : G.IsNaturalUnderBaseChangeIso)
    (hcover : Set.range i₁'.base ∪ Set.range (j₂ ≫ i₂).base = Set.univ)
    {κ : chowCohomologyComponent C G sX₂ p} {c d : BivariantClass C G sX₂ sX i₂ hi₂ p}
    {c' : BivariantClass C G (j₂ ≫ sX₂) sX (j₂ ≫ i₂)
      (comp_comp_structureMorphism_eq rfl hi₂) p}
    (hc : IsClosedCoverLocalizedClass C G sX sX₁' sX₂ i₁' hi₁' i₂ hi₂ p κ c)
    (hc' : IsClosedCoverLocalizedClass C G sX sX₁' (j₂ ≫ sX₂) i₁' hi₁' (j₂ ≫ i₂)
      (comp_comp_structureMorphism_eq rfl hi₂) p
      (chowCohomologyRestriction C G sX₂ j₂ p hgys κ) c')
    (hd : IsBivariantProperPushforward C G (j₂ ≫ sX₂) sX₂ sX j₂ i₂ rfl hi₂
      (properPushforwardDescends C) p c' d) :
    d = c := by
  rw [← sub_eq_zero, BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero]
  intro T g _ _ k
  rw [BivariantClass.sub_cap, sub_eq_zero]
  rcases range_pullbackSnd_eq_univ_or i₁' (j₂ ≫ i₂) g hcover with h₁ | h₂
  · have hT : closedCoverPushforward C sX sX₁' i₁' hi₁' g k
        (fundamentalChowClass C (pullback.fst i₁' g ≫ sX₁') k) =
          fundamentalChowClass C (g ≫ sX) k :=
      closedCoverPushforward_fundamentalChowClass C sX sX₁' i₁' hi₁' g h₁ k
    have hdz : d.cap g k (fundamentalChowClass C (g ≫ sX) k) = 0 := by
      rw [hd g k, bivariantProperPushforwardCap_apply, ← hT, hc'.1 g k _, map_zero]
    have hcz : c.cap g k (fundamentalChowClass C (g ≫ sX) k) = 0 := by
      rw [← hT]; exact hc.1 g k _
    rw [hdz, hcz]
  · have hmfst : bivariantPushforwardBaseChange j₂ i₂ g ≫ pullback.fst i₂ g =
        pullback.fst (j₂ ≫ i₂) g ≫ j₂ :=
      bivariantPushforwardBaseChange_fst j₂ i₂ g
    have hsub : Set.range (j₂ ≫ i₂).base ⊆ Set.range i₂.base := by
      rintro _ ⟨y, rfl⟩
      exact ⟨j₂.base y, by simp⟩
    have h₂' : Set.range (pullback.snd i₂ g).base = Set.univ := by
      refine Set.univ_subset_iff.mp ?_
      rw [← h₂, Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
      exact Set.preimage_mono hsub
    have hiso₂ : IsIso (pullback.snd i₂ g) :=
      isIso_pullbackSnd_of_range_eq_univ i₂ g h₂'
    have hiso₂' : IsIso (pullback.snd (j₂ ≫ i₂) g) :=
      isIso_pullbackSnd_of_range_eq_univ (j₂ ≫ i₂) g h₂
    have hmiso : IsIso (bivariantPushforwardBaseChange j₂ i₂ g) := by
      have he : bivariantPushforwardBaseChange j₂ i₂ g =
          pullback.snd (j₂ ≫ i₂) g ≫ CategoryTheory.inv (pullback.snd i₂ g) := by
        rw [← bivariantPushforwardBaseChange_snd j₂ i₂ g, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id]
      rw [he]
      infer_instance
    have : IsIntegral (pullback i₂ g) :=
      IsIntegral.of_isIso (CategoryTheory.inv (pullback.snd i₂ g))
    have hcv := cap_fundamentalChowClass_eq_toIdentityCapRule C G sX sX₁' i₁' hi₁' p hc g h₂' k
    have hc'v := (cap_fundamentalChowClass_eq_toIdentityCapRule C G sX sX₁' i₁' hi₁' p hc' g
      h₂ k).trans (chowCohomologyRestriction_toIdentityCapRule C G sX₂ j₂ hgys p κ
        (pullback.fst (j₂ ≫ i₂) g) k _)
    have hstruct : pullback.fst (j₂ ≫ i₂) g ≫ (j₂ ≫ sX₂) =
        (bivariantPushforwardBaseChange j₂ i₂ g ≫ pullback.fst i₂ g) ≫ sX₂ := by
      rw [hmfst, Category.assoc]
    have hnat := BivariantClass.toIdentityCapRule_properNaturality C G sX₂ p κ
      (pullback.fst i₂ g) (bivariantPushforwardBaseChange j₂ i₂ g) k
      (properPushforwardDescends C _ _ _ _ k)
      (properPushforwardDescends C _ _ _ _ (k - p))
      (chowGroupCongr C hstruct k
        (fundamentalChowClass C (pullback.fst (j₂ ≫ i₂) g ≫ (j₂ ≫ sX₂)) k))
    rw [chowGroupCongr_fundamentalChowClass C hstruct k,
      properChowPushforward_fundamentalChowClass_of_isBirational C
        ((bivariantPushforwardBaseChange j₂ i₂ g ≫ pullback.fst i₂ g) ≫ sX₂)
        (pullback.fst i₂ g ≫ sX₂) (bivariantPushforwardBaseChange j₂ i₂ g)
        (by simp [Category.assoc])
        (isBirational_of_isIso_of_isIntegral (bivariantPushforwardBaseChange j₂ i₂ g)) k
        (properPushforwardDescends C _ _ _ _ k)] at hnat
    have hkey : BivariantClass.toIdentityCapRule C G sX₂ p κ
          (bivariantPushforwardBaseChange j₂ i₂ g ≫ pullback.fst i₂ g) k
          (fundamentalChowClass C
            ((bivariantPushforwardBaseChange j₂ i₂ g ≫ pullback.fst i₂ g) ≫ sX₂) k) =
        chowGroupCongr C hstruct (k - p)
          (BivariantClass.toIdentityCapRule C G sX₂ p κ (pullback.fst (j₂ ≫ i₂) g ≫ j₂) k
            (fundamentalChowClass C (pullback.fst (j₂ ≫ i₂) g ≫ (j₂ ≫ sX₂)) k)) := by
      rw [← chowGroupCongr_fundamentalChowClass C hstruct k]
      exact toIdentityCapRule_congr_test C G sX₂ p κ hmfst.symm hstruct k _
    rw [hd g k, bivariantProperPushforwardCap_apply, hc'v, hcv, hnat, hkey]
    exact (properChowPushforward_congr_source C hstruct (pullback.fst i₂ g ≫ sX₂)
      (bivariantPushforwardBaseChange j₂ i₂ g)
      (bivariantPushforwardBaseChange_comp_structure (C := C) rfl i₂ g)
      (by simp [Category.assoc]) (k - p) (properPushforwardDescends C _ _ _ _ (k - p))
      (properPushforwardDescends C _ _ _ _ (k - p)) _).symm

end Shrink

end Stacks.Chow

end
