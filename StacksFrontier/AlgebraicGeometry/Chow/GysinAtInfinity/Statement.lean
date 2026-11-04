module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Formula
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin class at infinity (Stacks 0F9J)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`b : W ⟶ 𝐏¹_X` be a proper morphism which is an isomorphism over `𝐀¹_X`. Write
`i_∞ : W_∞ ⟶ W` for the inverse image of the divisor `D_∞ ⊆ 𝐏¹_X` and `i_0 : X ⟶ W` for the
section at zero. Stacks 0F9J asserts that there is a canonical bivariant class
`C ∈ A⁰(W_∞ ⟶ X)` with `i_{∞,*}(C ∩ α) = i_{0,*} α` for `α ∈ A_k(X)`, and similarly after any
base change by `X' ⟶ X` locally of finite type.

The class is `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass`. It is canonical in the sense of
the source's construction: on every test scheme `T ⟶ X` it caps `α ∈ A_k(T)` to `i_∞^* β` for
*every* `β ∈ A_{k+1}(W ×_X T)` whose restriction to `b⁻¹(𝐀¹_X) ×_X T` is the flat pullback of
`α`, and this property determines it.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.IsGysinAtInfinityCap` — the construction of the source, as a
  property of a class in `A⁰(W_∞ ⟶ X)`: `C ∩ α = i_∞^* β` for every lift `β` of `α`.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityData` — the class with its pushforward identity,
  as an inhabitant of `Stacks.Chow.GysinAtInfinityData`.

## Main results

* `Stacks.Chow.GysinAtInfinity.gysinAtInfinity` — **Stacks 0F9J**: the class satisfies the
  construction of the source, it is the only class doing so, and
  `i_{∞,*}(C ∩ α) = i_{0,*} α` on every test scheme locally of finite type over `X`.

## Implementation notes

The construction is carried out in `StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Class`
for a divisor `Z(s) ⊆ W` with trivial normal bundle whose complement `U` is flat of relative
dimension one over `X`: lifts exist by Stacks 02RX, two lifts differ by a class pushed forward
from `Z(s)` (Stacks 02RX), and the Gysin map of `Z(s)` kills such classes (Remark 0B6Z, through
Stacks 0F95 and 02SP); the bivariance is a diagram chase using that lifts transform under proper
pushforward, flat pullback (Stacks 02RG, 02RD) and the Gysin map of a divisor on the test scheme
(Stacks 02TA, 0B71), and that the Gysin class of `Z(s)` (Stacks 0B79) is bivariant. The divisor
at infinity is presented as the zero scheme of the pullback of the canonical section of
`𝒪(D_∞)` (Stacks 0F93) and identified with the fibre product `W ×_{𝐏¹_X} X` by
`Stacks.Chow.GysinAtInfinity.infinityIso`. The pushforward identity is Stacks 02T9 for the two
divisors `W_0` and `W_∞`, whose first Chern classes agree because `D_0 - D_∞` is principal on
every integral subscheme meeting neither (Stacks 02SK and 02SJ), together with `i_0^* β = α`,
which is Stacks 02TR on `b⁻¹(𝐀¹_X) ×_X T ≅ 𝐀¹_T`.

The bivariant classes are those of `Stacks.Chow.BivariantClass` at the Gysin system
`Stacks.Chow.gysinSystemOfInvertible` of the first Chern class of an invertible module.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- The construction of Stacks 0F9J, as a property of a class `c ∈ A⁰(W_∞ ⟶ X)`: on every test
scheme `g : T ⟶ X` and for every `β ∈ A_{k+1}(W ×_X T)` restricting over `b⁻¹(𝐀¹_X) ×_X T` to the
flat pullback of `α ∈ A_k(T)`, the class caps `α` to the Gysin image `i_∞^* β`, read on
`W_∞ ×_X T`. -/
def IsGysinAtInfinityCap
    (c : BivariantClass C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
      (modificationProjectionAtInfinity f b) rfl 0) : Prop :=
  haveI := hA
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k)
    (β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)),
    IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) g k α β →
    c.cap g k α =
      chowGroupDegreeEquiv C _ (sub_zero k).symm
        (chowPushforwardOfIso C ((testInfinityDivisor C f b g).subschemeι ≫
            testStr C f (modificationProjection f b) g)
          (pullback.fst (modificationProjectionAtInfinity f b) g ≫
            (modificationProjectionAtInfinity f b ≫ f)) (testInfinityIso C f b g)
          (testInfinityIso_comp_structure C f b g) k
          ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
            (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
            (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
              (pullback.fst (modificationProjection f b) g)) k β))

/-- **Stacks 0F9J.** Let `X` be locally of finite type over the base of chapter 42 and let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre at infinity
`i_∞ : W_∞ ⟶ W`. The class `C = gysinAtInfinityClass ∈ A⁰(W_∞ ⟶ X)`

* is constructed as in the source: `C ∩ α = i_∞^* β` for every lift `β` of `α`;
* is canonical: it is the only class with that property;
* satisfies `i_{∞,*}(C ∩ α) = i_{0,*} α` on every test scheme `T ⟶ X` locally of finite type,
  that is, for `α ∈ A_k(X)` and similarly after any base change by `X' ⟶ X` locally of finite
  type; here `i_0` and `i_∞` are the base changes of the section at zero and of the inclusion of
  the fibre at infinity. -/
@[stacks 0F9J]
theorem gysinAtInfinity :
    IsGysinAtInfinityCap C f b hA (gysinAtInfinityClass C f b hA) ∧
      (∀ c, IsGysinAtInfinityCap C f b hA c → c = gysinAtInfinityClass C f b hA) ∧
      haveI := hA
      ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
        (α : chowGroup C (g ≫ f) k),
        properChowPushforward C (modificationInfinityBaseChangeOver f b g)
            (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
            (modificationInfinityBaseChange_over f b g) k
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ k)
            (Eq.mp (congrArg (chowGroup C (modificationInfinityBaseChangeOver f b g))
              (sub_zero k)) ((gysinAtInfinityClass C f b hA).cap g k α)) =
          properChowPushforward C (g ≫ f) (modificationBaseChangeOver f b g)
            (modificationSectionAtZeroBaseChange f b inferInstance
              (modificationSectionAtZero_comp f b) g)
            (modificationSectionAtZeroBaseChange_over f b g inferInstance
              (modificationSectionAtZero_comp f b)) k
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ k) α := by
  have := hA
  refine ⟨fun g _ k α β hβ ↦ gysinAtInfinityClass_cap_eq_of_isLift C f b hA g hβ, ?_,
    fun g _ k α ↦ gysinAtInfinityClass_pushforward C f b hA g k α⟩
  intro c hc
  apply BivariantClass.ext
  intro T g _ k α
  obtain ⟨β, hβ⟩ := exists_isLift C f (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) g k α
  rw [hc g k α β hβ, gysinAtInfinityClass_cap_eq_of_isLift C f b hA g hβ]

/-- The class at infinity and its pushforward identity, as the datum
`Stacks.Chow.GysinAtInfinityData` of Stacks 0F9J. -/
def gysinAtInfinityData : GysinAtInfinityData C (gysinSystemOfInvertible C) f b hA :=
  haveI := hA
  { finiteTypeModification := inferInstance
    finiteTypeInfinity := inferInstance
    properModification := inferInstance
    properProjectionAtInfinity := inferInstance
    isIsoFibreAtZero := inferInstance
    sectionAtZero_comp := modificationSectionAtZero_comp f b
    properInclusionAtInfinity := fun _ ↦ inferInstance
    properSectionAtZero := fun g ↦ isProper_modificationSectionAtZeroBaseChange f b g _ _
    bivariantClass := gysinAtInfinityClass C f b hA
    pushforward_formula := fun g _ k _ _ α ↦ gysinAtInfinityClass_pushforward C f b hA g k α }

end GysinAtInfinity

end Stacks.Chow

end
