module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.CompositeCaps
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Retraction

/-!
# The class at infinity carries `x|_{X × {0}}` to `x|_{W_∞}`

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre at infinity
`i_∞ : W_∞ ⟶ W`, section at zero `i_0 : X ⟶ W`, and class `C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J.
For every Chow cohomology class `x ∈ A^p(W)` (Stacks 0B7E),

  `C ∘ x|_{X × {0}} = x|_{W_∞} ∘ C`   in   `A^p(W_∞ ⟶ X)`.

This is the identity behind Stacks 0FAV: there `x = c_p(Q)` is a Chern class of a perfect object
on `W`.

## The argument

On a test scheme `T ⟶ X`, let `α ∈ A_k(T)` and choose `β ∈ A_{k+1}(W ×_X T)` restricting over
`𝐀¹_X` to the flat pullback of `α`, so that `C ∩ α = i_∞^* β` (Stacks 0F9J). Put
`γ = x ∩ β`. Because `x` is bivariant, `x ∩ i_∞^* β = i_∞^* γ`, and

  `i_{∞,*} i_∞^* γ = x ∩ i_{∞,*} i_∞^* β = x ∩ i_{∞,*}(C ∩ α) = x ∩ i_{0,*} α
    = i_{0,*}(x|_{X × {0}} ∩ α)`,

using the pushforward identity of Stacks 0F9J. Pushing forward to `T`, of which `i_0` is a section,
gives `(W_∞ ⟶ X)_* i_∞^* γ = x|_{X × {0}} ∩ α`, and Stacks 0FAR then gives

  `C ∩ (x|_{X × {0}} ∩ α) = C ∩ (W_∞ ⟶ X)_* i_∞^* γ = i_∞^* γ = x ∩ i_∞^* β
    = x|_{W_∞} ∩ (C ∩ α)`.

## Main results

* `Stacks.Chow.GysinAtInfinity.commutesWithChowCohomologyClass_gysinAtInfinityClass` — the
  identity above, for classes `x₀ ∈ A^p(X)` and `x_∞ ∈ A^p(W_∞)` operating as `x` does on test
  schemes over `X` through `i_0` and over `W_∞` through `i_∞`.

## References

* [Stacks Project, Tag 0FAV](https://stacks.math.columbia.edu/tag/0FAV)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] {p : ℤ}
  (x : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p)

omit [LocallyOfFiniteType f] in
/-- Pushforward along an isomorphism is proper pushforward. -/
theorem chowPushforwardOfIso_eq_chowPush {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (w : A ⟶ B) [IsIso w]
    (hw : w ≫ sB = sA) (k : ℤ) :
    chowPushforwardOfIso C sA sB w hw k = chowPush C sA sB w hw k :=
  rfl

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- The base change of `i_∞` composed with the projection to `W` is the projection to `W_∞`
followed by `i_∞`, read on the zero-scheme model of `W_∞ ×_X T`. -/
theorem testInfinityIso_comp_fst_comp_inclusion :
    testInfinityIso C f b g ≫ pullback.fst (modificationProjectionAtInfinity f b) g ≫
        modificationInclusionAtInfinity f b =
      (testInfinityDivisor C f b g).subschemeι ≫ pullback.fst (modificationProjection f b) g := by
  rw [← modificationInfinityBaseChange_comp_fst, ← Category.assoc,
    testInfinityIso_comp_modificationInfinityBaseChange]

/-- The operation of `x` commutes with the Gysin map on the zero scheme of `i_∞`'s section. -/
private theorem idRule_onChow_infinity_heq (k : ℤ)
    (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)) :
    x.idRule C _ (gysinSystemOfInvertible C)
        ((testInfinityDivisor C f b g).subschemeι ≫ pullback.fst (modificationProjection f b) g) k
        (chowGroupCongr C (Category.assoc _ _ _).symm k
          ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
            (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
            (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
              (pullback.fst (modificationProjection f b) g)) k β)) ≍
      (gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
        (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
        (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) g)) (k - p)
        (Eq.mp (congrArg (chowGroup C (testStr C f (modificationProjection f b) g))
          (by omega : k + 1 - p = k - p + 1))
          (x.idRule C _ (gysinSystemOfInvertible C) (pullback.fst (modificationProjection f b) g)
            (k + 1) β)) :=
  (heq_of_eq (idRule_gysin_chowGroupCongr C _ x _ _ _ k β)).trans (chowGroupCongr_heq C _ _ _)

/-- **The Gysin map at infinity commutes with a Chow cohomology class.** For `x ∈ A^p(W)` and a
class `x_∞ ∈ A^p(W_∞)` operating as `x` on test schemes through `i_∞`,
`x_∞ ∩ i_∞^* β = i_∞^*(x ∩ β)` on `W_∞ ×_X T`. -/
theorem idRule_infinityGysin_heq
    (xInf : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f) p)
    (hInf : ∀ {V : Scheme.{u}} (v : V ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType v]
      (k : ℤ) (α : chowGroup C (v ≫ (modificationProjectionAtInfinity f b ≫ f)) k)
      (α' : chowGroup C ((v ≫ modificationInclusionAtInfinity f b) ≫
        (modificationProjection f b ≫ f)) k), α ≍ α' →
      xInf.idRule C _ (gysinSystemOfInvertible C) v k α ≍
        x.idRule C _ (gysinSystemOfInvertible C) (v ≫ modificationInclusionAtInfinity f b) k α')
    (k : ℤ) (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)) :
    xInf.idRule C _ (gysinSystemOfInvertible C)
        (pullback.fst (modificationProjectionAtInfinity f b) g) k (infinityGysin C f b g k β) ≍
      infinityGysin C f b g (k - p)
        (Eq.mp (congrArg (chowGroup C (testStr C f (modificationProjection f b) g))
          (by omega : k + 1 - p = k - p + 1))
          (x.idRule C _ (gysinSystemOfInvertible C) (pullback.fst (modificationProjection f b) g)
            (k + 1) β)) := by
  have hs : (testInfinityIso C f b g ≫ pullback.fst (modificationProjectionAtInfinity f b) g) ≫
      (modificationProjectionAtInfinity f b ≫ f) =
      (testInfinityDivisor C f b g).subschemeι ≫ testStr C f (modificationProjection f b) g := by
    rw [Category.assoc]
    exact testInfinityIso_comp_structure C f b g
  have hti : (testInfinityIso C f b g ≫ pullback.fst (modificationProjectionAtInfinity f b) g) ≫
      modificationInclusionAtInfinity f b =
      (testInfinityDivisor C f b g).subschemeι ≫ pullback.fst (modificationProjection f b) g := by
    rw [Category.assoc]
    exact testInfinityIso_comp_fst_comp_inclusion C f b g
  rw [infinityGysin_apply, infinityGysin_apply, chowPushforwardOfIso_eq_chowPush,
    chowPushforwardOfIso_eq_chowPush]
  refine (heq_of_eq (idRule_chowPush_of_eq C _ xInf
    (pullback.fst (modificationProjectionAtInfinity f b) g)
    (testInfinityIso C f b g ≫ pullback.fst (modificationProjectionAtInfinity f b) g)
    (testInfinityIso C f b g) rfl
    ((testInfinityDivisor C f b g).subschemeι ≫ testStr C f (modificationProjection f b) g)
    hs (testInfinityIso_comp_structure C f b g) k
    ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
      (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
      (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
        (pullback.fst (modificationProjection f b) g)) k β))).trans ?_
  refine properChowPushforward_heq_congr_base C (testInfinityIso C f b g) hs rfl _ _ rfl _ _ _ _ ?_
  refine (hInf _ k _ (chowGroupCongr C (by rw [hti, Category.assoc]) k _)
    ((chowGroupCongr_heq C _ k _).trans (chowGroupCongr_heq C _ k _).symm)).trans ?_
  refine (IdentityCapRule.heq_congr C _ (x.idRule C _ (gysinSystemOfInvertible C)) hti rfl
    ((chowGroupCongr_heq C _ k _).trans (chowGroupCongr_heq C (Category.assoc _ _ _).symm k
      ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
        (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
        (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) g)) k β)).symm)).trans ?_
  exact idRule_onChow_infinity_heq C f b g x k β

section Section

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The section at zero `i_0 : X ⟶ W` is a closed immersion. -/
instance isClosedImmersion_modificationSectionAtZero
    (h : IsIso (modificationFibreAtZeroProjection f b)) :
    IsClosedImmersion (modificationSectionAtZero f b h) := by
  unfold modificationSectionAtZero
  infer_instance

variable [IsIso (pullback.snd b (projectiveLineAffineChart f))]

/-- The base change `T ⟶ W ×_X T` of the section at zero. -/
abbrev zeroSectionTest : T ⟶ pullback (modificationProjection f b) g :=
  modificationSectionAtZeroBaseChange f b inferInstance (modificationSectionAtZero_comp f b) g

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- The base change `T ⟶ W ×_X T` of the section at zero, followed by the projection to `W`, is
`g` followed by the section at zero `i_0 : X ⟶ W`. -/
theorem zeroSectionTest_comp_fst :
    zeroSectionTest C f b g ≫ pullback.fst (modificationProjection f b) g =
      g ≫ modificationSectionAtZero f b inferInstance := by
  rw [zeroSectionTest, modificationSectionAtZeroBaseChange, pullback.lift_fst]

/-- **Stacks 0F9J, the pushforward identity, on the zero-scheme model.** For a lift `β` of
`α ∈ A_k(T)`, `i_{∞,*} i_∞^* β = i_{0,*} α` in `A_k(W ×_X T)`. -/
theorem chowPush_onChow_of_isLift {k : ℤ} {α : chowGroup C (g ≫ f) k}
    {β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)}
    (hβ : IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) g k α β) :
    chowPush C ((testInfinityDivisor C f b g).subschemeι ≫
        testStr C f (modificationProjection f b) g)
      (testStr C f (modificationProjection f b) g) (testInfinityDivisor C f b g).subschemeι
      rfl k
      ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
        (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
        (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) g)) k β) =
      chowPush C (g ≫ f) (testStr C f (modificationProjection f b) g) (zeroSectionTest C f b g)
        (modificationSectionAtZeroBaseChange_over f b g _ _) k α := by
  have hform := gysinAtInfinityClass_pushforward C f b inferInstance g k α
  rw [gysinAtInfinityClass_cap_eq_of_isLift C f b inferInstance g hβ,
    eqMp_chowGroupDegreeEquiv C _ (sub_zero k).symm (sub_zero k)] at hform
  refine Eq.trans ?_ hform
  rw [chowPushforwardOfIso_eq_chowPush]
  change _ = chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _)
  rw [chowPush_comp C _ _ _ _ _ _ rfl]
  · exact chowPush_congr C _ _ (testInfinityIso_comp_modificationInfinityBaseChange C f b g).symm
      _ _ _ _
  · rw [testInfinityIso_comp_modificationInfinityBaseChange]

/-- **The pushforward of `i_∞^*(x ∩ β)` to the test scheme.** For a lift `β` of `α ∈ A_k(T)`
and a class `x₀ ∈ A^p(X)` operating as `x ∈ A^p(W)` does through the section at zero,
`(W_∞ ⟶ X)_* i_∞^*(x ∩ β) = x₀ ∩ α`. -/
theorem properChowPushforward_infinityGysin_idRule
    (x0 : chowCohomologyComponent C (gysinSystemOfInvertible C) f p)
    (h0 : ∀ {V : Scheme.{u}} (v : V ⟶ X) [LocallyOfFiniteType v] (k : ℤ)
      (α : chowGroup C (v ≫ f) k)
      (α' : chowGroup C ((v ≫ modificationSectionAtZero f b inferInstance) ≫
        (modificationProjection f b ≫ f)) k), α ≍ α' →
      x0.idRule C f (gysinSystemOfInvertible C) v k α ≍
        x.idRule C _ (gysinSystemOfInvertible C)
          (v ≫ modificationSectionAtZero f b inferInstance) k α')
    {k : ℤ} {α : chowGroup C (g ≫ f) k}
    {β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)}
    (hβ : IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) g k α β) :
    properChowPushforward C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (modificationInfinityBaseChange_snd_over f b g) (k - p)
        (properPushforwardDescends C _ _ _ _ _)
        (infinityGysin C f b g (k - p)
          (Eq.mp (congrArg (chowGroup C (testStr C f (modificationProjection f b) g))
            (by omega : k + 1 - p = k - p + 1))
            (x.idRule C _ (gysinSystemOfInvertible C) (pullback.fst (modificationProjection f b) g)
              (k + 1) β))) =
      x0.idRule C f (gysinSystemOfInvertible C) g k α := by
  -- the Gysin image of `β` and of `x ∩ β`, on the zero-scheme model of `W_∞ ×_X T`
  have hD : (testInfinityDivisor C f b g).subschemeι ≫ pullback.snd (modificationProjection f b) g =
      testInfinityIso C f b g ≫ pullback.snd (modificationProjectionAtInfinity f b) g := by
    rw [← modificationInfinityBaseChange_comp_snd, ← Category.assoc,
      testInfinityIso_comp_modificationInfinityBaseChange]
  have hDs : (testInfinityDivisor C f b g).subschemeι ≫ testStr C f (modificationProjection f b) g =
      ((testInfinityDivisor C f b g).subschemeι ≫ pullback.fst (modificationProjection f b) g) ≫
        (modificationProjection f b ≫ f) := (Category.assoc _ _ _).symm
  -- step 1: push forward through `W ×_X T`
  have e1 : properChowPushforward C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (modificationInfinityBaseChange_snd_over f b g) (k - p)
        (properPushforwardDescends C _ _ _ _ _)
        (infinityGysin C f b g (k - p)
          (Eq.mp (congrArg (chowGroup C (testStr C f (modificationProjection f b) g))
            (by omega : k + 1 - p = k - p + 1))
            (x.idRule C _ (gysinSystemOfInvertible C) (pullback.fst (modificationProjection f b) g)
              (k + 1) β))) =
      chowPush C (testStr C f (modificationProjection f b) g) (g ≫ f)
        (pullback.snd (modificationProjection f b) g) (modificationBaseChange_snd_over f b g)
        (k - p)
        (chowPush C ((testInfinityDivisor C f b g).subschemeι ≫
            testStr C f (modificationProjection f b) g)
          (testStr C f (modificationProjection f b) g) (testInfinityDivisor C f b g).subschemeι
          rfl (k - p)
          ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
            (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
            (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
              (pullback.fst (modificationProjection f b) g)) (k - p)
            (Eq.mp (congrArg (chowGroup C (testStr C f (modificationProjection f b) g))
              (by omega : k + 1 - p = k - p + 1))
              (x.idRule C _ (gysinSystemOfInvertible C)
                (pullback.fst (modificationProjection f b) g) (k + 1) β)))) := by
    rw [infinityGysin_apply, chowPushforwardOfIso_eq_chowPush]
    change chowPush C _ _ _ _ _ (chowPush C _ _ _ _ _ _) = _
    rw [chowPush_comp C _ _ _ _ _ _ rfl, chowPush_comp C _ _ _ _ _ _ rfl]
    · exact chowPush_congr C _ _ hD.symm _ _ _ _
    all_goals first
      | (rw [Category.assoc, modificationBaseChange_snd_over])
      | (rw [Category.assoc, modificationInfinityBaseChange_snd_over];
         exact testInfinityIso_comp_structure C f b g)
  rw [e1]
  have hsec := zeroSectionTest_comp_fst C f b g
  -- steps 2 and 3: the Gysin map commutes with `x`, then Stacks 0F9J
  have e2 : chowPush C ((testInfinityDivisor C f b g).subschemeι ≫
        testStr C f (modificationProjection f b) g)
      (testStr C f (modificationProjection f b) g) (testInfinityDivisor C f b g).subschemeι
      rfl (k - p)
      ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
        (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
        (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) g)) (k - p)
        (Eq.mp (congrArg (chowGroup C (testStr C f (modificationProjection f b) g))
          (by omega : k + 1 - p = k - p + 1))
          (x.idRule C _ (gysinSystemOfInvertible C)
            (pullback.fst (modificationProjection f b) g) (k + 1) β))) =
      x.idRule C _ (gysinSystemOfInvertible C) (pullback.fst (modificationProjection f b) g) k
        (chowPush C (g ≫ f) (testStr C f (modificationProjection f b) g) (zeroSectionTest C f b g)
          (modificationSectionAtZeroBaseChange_over f b g _ _) k α) := by
    rw [← chowPush_onChow_of_isLift C f b g hβ, idRule_chowPush_of_eq C _ x
      (pullback.fst (modificationProjection f b) g)
      ((testInfinityDivisor C f b g).subschemeι ≫ pullback.fst (modificationProjection f b) g)
      (testInfinityDivisor C f b g).subschemeι rfl _ hDs.symm rfl k]
    refine eq_of_heq (properChowPushforward_heq_congr_base C _ hDs rfl _ _ rfl _ _ _ _ ?_)
    exact (idRule_onChow_infinity_heq C f b g x k β).symm
  rw [e2, idRule_chowPush_of_eq C _ x (pullback.fst (modificationProjection f b) g)
      (zeroSectionTest C f b g ≫ pullback.fst (modificationProjection f b) g)
      (zeroSectionTest C f b g) rfl (g ≫ f)
      (by rw [Category.assoc]; exact modificationSectionAtZeroBaseChange_over f b g _ _)
      (modificationSectionAtZeroBaseChange_over f b g _ _) k,
    chowPush_comp C _ _ _ (zeroSectionTest C f b g) (pullback.snd (modificationProjection f b) g)
      (𝟙 T) (modificationSectionAtZeroBaseChange_comp_snd f b g _ _) _ _
      (by rw [Category.id_comp, Category.assoc]
          exact (modificationSectionAtZeroBaseChange_over f b g _ _).symm),
    chowPush_id_eq_chowGroupCongr]
  have hh : g ≫ f = (g ≫ modificationSectionAtZero f b inferInstance) ≫
      (modificationProjection f b ≫ f) := by
    rw [Category.assoc, ← Category.assoc (modificationSectionAtZero f b inferInstance),
      modificationSectionAtZero_comp, Category.id_comp]
  refine eq_of_heq ((chowGroupCongr_heq C _ _ _).trans ?_)
  refine (IdentityCapRule.heq_congr C _ (x.idRule C _ (gysinSystemOfInvertible C)) hsec rfl
    ((chowGroupCongr_heq C _ k α).trans (chowGroupCongr_heq C hh k α).symm)).trans ?_
  exact (h0 g k α _ (chowGroupCongr_heq C hh k α).symm).symm

end Section

/-! ### The class at infinity carries `x|_{X × {0}}` to `x|_{W_∞}` -/

section Commute

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) {p : ℤ}

/-- **The class at infinity carries `x|_{X × {0}}` to `x|_{W_∞}`.** In the situation of
Stacks 0F9J, let `x ∈ A^p(W)` and let `x₀ ∈ A^p(X)`, `x_∞ ∈ A^p(W_∞)` operate as `x` does on test
schemes through the section at zero `i_0 : X ⟶ W` and the inclusion `i_∞ : W_∞ ⟶ W`
respectively. Then `C ∘ x₀ = x_∞ ∘ C` in `A^p(W_∞ ⟶ X)`, where `C ∈ A⁰(W_∞ ⟶ X)` is the class
at infinity. -/
theorem commutesWithChowCohomologyClass_gysinAtInfinityClass
    (x : chowCohomologyComponent C (gysinSystemOfInvertible C) (modificationProjection f b ≫ f) p)
    (x0 : chowCohomologyComponent C (gysinSystemOfInvertible C) f p)
    (xInf : chowCohomologyComponent C (gysinSystemOfInvertible C)
      (modificationProjectionAtInfinity f b ≫ f) p)
    (h0 : ∀ {V : Scheme.{u}} (v : V ⟶ X) [LocallyOfFiniteType v] (k : ℤ)
      (α : chowGroup C (v ≫ f) k)
      (α' : chowGroup C ((v ≫ modificationSectionAtZero f b
        (haveI := hA; inferInstance)) ≫ (modificationProjection f b ≫ f)) k), α ≍ α' →
      x0.idRule C f (gysinSystemOfInvertible C) v k α ≍
        x.idRule C _ (gysinSystemOfInvertible C)
          (v ≫ modificationSectionAtZero f b (haveI := hA; inferInstance)) k α')
    (hInf : ∀ {V : Scheme.{u}} (v : V ⟶ modificationFibreAtInfinity f b) [LocallyOfFiniteType v]
      (k : ℤ) (α : chowGroup C (v ≫ (modificationProjectionAtInfinity f b ≫ f)) k)
      (α' : chowGroup C ((v ≫ modificationInclusionAtInfinity f b) ≫
        (modificationProjection f b ≫ f)) k), α ≍ α' →
      xInf.idRule C _ (gysinSystemOfInvertible C) v k α ≍
        x.idRule C _ (gysinSystemOfInvertible C) (v ≫ modificationInclusionAtInfinity f b) k α') :
    CommutesWithChowCohomologyClass C (gysinSystemOfInvertible C) f
      (modificationProjectionAtInfinity f b) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p 0
      (gysinAtInfinityClass C f b hA) x0 xInf := by
  have := hA
  rw [commutesWithChowCohomologyClass_iff]
  refine BivariantClass.ext C _ _ f _ rfl _ fun g _ k α ↦ ?_
  refine eq_of_heq ((bivariantCompositeIdRightHom_cap_heq_idRule C _ f _ _ _ p 0 _ x0 g k α).trans
    (HEq.trans ?_ (bivariantCompositeIdLeftHom_cap_heq_idRule C _ f _ _ _ p 0 _ xInf g k α).symm))
  obtain ⟨β, hβ⟩ := exists_isLift C f (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) g k α
  rw [← properChowPushforward_infinityGysin_idRule C f b g x x0 h0 hβ,
    gysinAtInfinityClass_cap_properChowPushforward_infinityGysin C f b g hA (k - p),
    gysinAtInfinityClass_cap_eq_of_isLift C f b hA g hβ]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine HEq.trans ?_ (IdentityCapRule.heq_congr C _ (xInf.idRule C _ (gysinSystemOfInvertible C))
    rfl (sub_zero k).symm (chowGroupDegreeEquiv_heq C _ _ _).symm)
  exact (idRule_infinityGysin_heq C f b g x xInf hInf k β).symm

end Commute

end GysinAtInfinity

end Stacks.Chow

end
