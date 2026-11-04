module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Statement
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineOverComparison
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Unconditional
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksCore.Tactic.StacksAttribute

/-!
# The class at infinity retracts the Gysin map at infinity (Stacks 0FAR)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let `i_∞ : W_∞ ⟶ W` be the fibre at
infinity and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J. Stacks 0FAR asserts

  `C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*`

as maps `A_{k+1}(W) ⟶ A_k(W_∞)`, and, the class being bivariant, the same identity holds after any
base change by `T ⟶ X` locally of finite type.

The proof is the one of the source. Given `β ∈ A_{k+1}(W ×_X T)`, its restriction to
`b⁻¹(𝐀¹_X) ×_X T ≅ 𝐀¹_T` is the flat pullback of some `α ∈ A_k(T)` (Stacks 02TT for the affine
line, the step the source cites as Lemma 0B74), so `β` is a lift of `α` and `C ∩ α = i_∞^* β`.
By the pushforward identity of Stacks 0F9J, `i_{∞,*}(C ∩ α) = i_{0,*} α`, and pushing forward to
`T` along the projection, of which `i_0` is a section, gives `(W_∞ ⟶ X)_* i_∞^* β = α`. Hence
`C ∩ (W_∞ ⟶ X)_* i_∞^* β = C ∩ α = i_∞^* β`.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.infinityGysin` — the Gysin map
  `i_∞^* : A_{k+1}(W ×_X T) ⟶ A_k(W_∞ ×_X T)` of the fibre at infinity.

## Main results

* `Stacks.Chow.GysinAtInfinity.exists_isLift_of_chowGroup` — every class on `W ×_X T` is a lift.
* `Stacks.Chow.GysinAtInfinity.properChowPushforward_infinityGysin_of_isLift` —
  `(W_∞ ⟶ X)_* i_∞^* β = α` for a lift `β` of `α`.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_cap_properChowPushforward_infinityGysin` —
  Stacks 0FAR on the test schemes `W ×_X T`; the identity of bivariant classes is in
  `StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.RetractionClass`.

## References

* [Stacks Project, Tag 0FAR](https://stacks.math.columbia.edu/tag/0FAR)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The affine line `𝐀¹_S` of the Chow chapter is an affine-space bundle of rank one over `S`. -/
theorem isAffineSpaceBundle_affineLineOver (S : Scheme.{u}) :
    IsAffineSpaceBundle (pullback.fst (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) 1 :=
  isAffineSpaceBundle_of_isPullback
    (IsPullback.of_horiz_isIso
      ⟨by rw [affineLineOverIsoAffineLine_hom_over, Category.comp_id]⟩ :
      IsPullback (affineLineOverIsoAffineLine S).hom
        (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
        (𝔸(ULift.{u} (Fin 1); S) ↘ S) (𝟙 S))
    (isAffineSpaceBundle_affineSpaceOver S 1)

namespace GysinAtInfinity

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]

/-- The base change `W_∞ ×_X T ⟶ T` of the proper morphism `W_∞ ⟶ X` is proper. -/
instance isProper_pullbackSnd_modificationProjectionAtInfinity :
    IsProper (pullback.snd (modificationProjectionAtInfinity f b) g) :=
  MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ g) inferInstance

/-- The base change `W ×_X T ⟶ T` of the proper morphism `W ⟶ X` is proper. -/
instance isProper_pullbackSnd_modificationProjection :
    IsProper (pullback.snd (modificationProjection f b) g) :=
  MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ g) inferInstance

/-- The Gysin map `i_∞^* : A_{k+1}(W ×_X T) ⟶ A_k(W_∞ ×_X T)` of the fibre at infinity: the Gysin
homomorphism of the pulled-back canonical section of `𝒪(D_∞)`, read on `W_∞ ×_X T` through the
identification of its zero scheme with the base change of `W_∞`. -/
def infinityGysin (k : ℤ) :
    chowGroup C (testStr C f (modificationProjection f b) g) (k + 1) →+
      chowGroup C (modificationInfinityBaseChangeOver f b g) k :=
  (chowPushforwardOfIso C ((testInfinityDivisor C f b g).subschemeι ≫
      testStr C f (modificationProjection f b) g)
    (modificationInfinityBaseChangeOver f b g) (testInfinityIso C f b g)
    (testInfinityIso_comp_structure C f b g) k).comp
    ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
      (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
      (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
        (pullback.fst (modificationProjection f b) g)) k)

/-- The value of `infinityGysin` on `β` is the image of the Gysin homomorphism of the pulled-back
canonical section of `𝒪(D_∞)` applied to `β`, under the identification of its zero scheme with
`W_∞ ×_X T`. -/
theorem infinityGysin_apply (k : ℤ)
    (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)) :
    infinityGysin C f b g k β =
      chowPushforwardOfIso C ((testInfinityDivisor C f b g).subschemeι ≫
          testStr C f (modificationProjection f b) g)
        (modificationInfinityBaseChangeOver f b g) (testInfinityIso C f b g)
        (testInfinityIso_comp_structure C f b g) k
        ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
          (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
          (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
            (pullback.fst (modificationProjection f b) g)) k β) :=
  rfl

section Lift

variable [IsIso (pullback.snd b (projectiveLineAffineChart f))]

/-- **Every class is a lift.** The restriction of any `β ∈ A_{k+1}(W ×_X T)` to
`b⁻¹(𝐀¹_X) ×_X T ≅ 𝐀¹_T` is the flat pullback of a class on `T`: flat pullback along the affine
line is surjective (Stacks 02TT). -/
theorem exists_isLift_of_chowGroup (k : ℤ)
    (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)) :
    ∃ α, IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) g k α β := by
  have := isOpenImmersion_openBaseChange (modificationProjection f b) (chartInclusion f b) g
  obtain ⟨α, hα⟩ := flatPullbackChow_surjective_of_isAffineSpaceBundle_general C
    (openStr C f (modificationProjection f b) (chartInclusion f b) g) (g ≫ f)
    (pullback.snd (chartInclusion f b ≫ modificationProjection f b) g) rfl 1
    (relativeDimension_openSnd (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) g)
    (isAffineSpaceBundle_of_isPullback (isPullback_openTest f b g)
      (isAffineSpaceBundle_affineLineOver C.S)) k
    (chowGroupRestrict C (testStr C f (modificationProjection f b) g)
      (openStr C f (modificationProjection f b) (chartInclusion f b) g)
      (openBaseChange (modificationProjection f b) (chartInclusion f b) g)
      (openBaseChange_comp_testStr C f _ _ g) (k + 1) β)
  exact ⟨α, hα.symm⟩

/-- **The first step of the proof of Stacks 0FAR.** For a lift `β` of `α ∈ A_k(T)`, pushing
`i_∞^* β` forward along `W_∞ ×_X T ⟶ T` gives back `α`: by the pushforward identity of
Stacks 0F9J, `i_{∞,*} i_∞^* β = i_{∞,*}(C ∩ α) = i_{0,*} α`, and `i_0` is a section of the
projection `W ×_X T ⟶ T`. -/
theorem properChowPushforward_infinityGysin_of_isLift {k : ℤ} {α : chowGroup C (g ≫ f) k}
    {β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)}
    (hβ : IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) g k α β) :
    properChowPushforward C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
        (pullback.snd (modificationProjectionAtInfinity f b) g)
        (modificationInfinityBaseChange_snd_over f b g) k
        (properPushforwardDescends C _ _ _ _ _) (infinityGysin C f b g k β) = α := by
  have hform := gysinAtInfinityClass_pushforward C f b inferInstance g k α
  rw [gysinAtInfinityClass_cap_eq_of_isLift C f b inferInstance g hβ,
    eqMp_chowGroupDegreeEquiv C _ (sub_zero k).symm (sub_zero k)] at hform
  rw [properChowPushforward_comp_apply C (modificationInfinityBaseChangeOver f b g)
      (modificationBaseChangeOver f b g) (g ≫ f) (modificationInfinityBaseChange f b g)
      (pullback.snd (modificationProjection f b) g) _
      (modificationInfinityBaseChange_comp_snd f b g) (modificationInfinityBaseChange_over f b g)
      (modificationBaseChange_snd_over f b g) _ k (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
    infinityGysin_apply, hform,
    ← properChowPushforward_comp_apply C (g ≫ f) (modificationBaseChangeOver f b g) (g ≫ f)
      (modificationSectionAtZeroBaseChange f b inferInstance (modificationSectionAtZero_comp f b) g)
      (pullback.snd (modificationProjection f b) g) (𝟙 T)
      (modificationSectionAtZeroBaseChange_comp_snd f b g _ _)
      (modificationSectionAtZeroBaseChange_over f b g _ _)
      (modificationBaseChange_snd_over f b g) (Category.id_comp _) k
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _),
    properChowPushforward_id]
  rfl

end Lift

/-- **Stacks 0FAR on the test schemes `W ×_X T`.** Let `X` be locally of finite type over the
base of chapter 42, let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, let
`i_∞ : W_∞ ⟶ W` be the fibre at infinity and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J.
Then `C ∘ (W_∞ ⟶ X)_* ∘ i_∞^* = i_∞^*` as operations `A_{k+1}(W ×_X T) ⟶ A_k(W_∞ ×_X T)` for
every `g : T ⟶ X` locally of finite type, which for `g = 𝟙_X` is the identity of the source on
`W ×_X X = W`; this is the convention of Stacks 0F9J
(`Stacks.Chow.GysinAtInfinity.gysinAtInfinity`), where the cap of a bivariant class is defined
on test schemes over `X`. The class `C ∩ -` takes values in degree `k - 0`, identified with `k` by
`Stacks.Chow.chowGroupDegreeEquiv`. The identity of bivariant classes over `W`, valid on every
test scheme `W' ⟶ W`, is `Stacks.Chow.GysinAtInfinity.gysinAtInfinity_retraction`. -/
theorem gysinAtInfinityClass_cap_properChowPushforward_infinityGysin
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)) :
    (gysinAtInfinityClass C f b hA).cap g k
        (properChowPushforward C (modificationInfinityBaseChangeOver f b g) (g ≫ f)
          (pullback.snd (modificationProjectionAtInfinity f b) g)
          (modificationInfinityBaseChange_snd_over f b g) k
          (properPushforwardDescends C _ _ _ _ _) (infinityGysin C f b g k β)) =
      chowGroupDegreeEquiv C _ (sub_zero k).symm (infinityGysin C f b g k β) := by
  have := hA
  obtain ⟨α, hα⟩ := exists_isLift_of_chowGroup C f b g k β
  rw [properChowPushforward_infinityGysin_of_isLift C f b g hα,
    gysinAtInfinityClass_cap_eq_of_isLift C f b hA g hα, infinityGysin_apply]

end GysinAtInfinity

end Stacks.Chow

end
