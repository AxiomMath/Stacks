module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums

/-!
# Which operations on cycles come from operations on Chow groups

In the situation of Stacks 0EDT let `X, Y/B` be good and let `φ : Z_m(Y) ⟶ Z_n(X)` be a
homomorphism of cycle groups. `AlgebraicGeometry.Space.chowGroupHomOfCycleHom` descends `φ` to
the Chow groups `CH_m(Y) ⟶ CH_n(X)` of Stacks 0EQ6, part (4), as soon as `φ` carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero. This file records that
the implication is an equivalence, and that the descended map is unique:

* a homomorphism `F : CH_m(Y) ⟶ CH_n(X)` with `F ∘ cls = cls ∘ φ` exists **if and only if** `φ`
  kills rational equivalence to zero;
* there is at most one such `F`, the class map being surjective.

So for an operation on cycles the two questions "does it act on Chow groups compatibly with
classes" and "does it preserve rational equivalence to zero" are the same question, and the
second is in each case the content of a tag of Section 82.21 or Section 82.22. Instantiated at
the pushforward of cycles along a proper morphism (Stacks 0EP1) and at the flat pullback of
cycles (Stacks 0EP9), that reads:

* an operation `p_* : CH_k(X) ⟶ CH_k(Y)` compatible with classes exists iff the vanishing
  statement of **Stacks 0EQC** holds, and it is then unique;
* an operation `f^* : CH_m(Y) ⟶ CH_n(X)` compatible with classes exists iff the vanishing
  statement of **Stacks 0EQB** holds, and it is then unique.

The same statement for the refined Gysin map of Stacks 0ER1 is
`AlgebraicGeometry.Space.gysinCycleMapFactorsThroughRationalEquivalence_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoring`, which is this file's
`AlgebraicGeometry.Space.exists_chowGroupHom_comp_chowClass_iff` at
`AlgebraicGeometry.Space.gysinCycleMap`.

## Main results

* `AlgebraicGeometry.Space.chowGroupHom_eq_of_comp_chowClass_eq` — a homomorphism of Chow groups
  is determined by its effect on the classes of cycles.
* `AlgebraicGeometry.Space.exists_chowGroupHom_comp_chowClass_iff` — a homomorphism of cycle
  groups is induced by one of Chow groups exactly when it kills rational equivalence to zero.
* `AlgebraicGeometry.Space.exists_chowGroupProperPushforwardHom_iff` and
  `AlgebraicGeometry.Space.exists_flatPullbackChowHom_iff` — the same two statements read at
  proper pushforward and at flat pullback, where the right-hand side is the vanishing statement
  of Stacks 0EQC and of Stacks 0EQB respectively.

## References

* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### A homomorphism of Chow groups is determined on classes of cycles -/

/-- Two homomorphisms `CH_m(Y) ⟶ CH_n(X)` which agree on the class of every cycle are equal:
the class map `Z_m(Y) ⟶ CH_m(Y)` of Stacks 0EQ6, part (4), is the quotient map, hence
surjective. -/
theorem chowGroupHom_eq_of_comp_chowClass_eq (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (m n : ℤ)
    {F G : chowGroup.{v} D sY hY m →+ chowGroup.{v} D sX hX n}
    (h : F.comp (chowClass.{v} D sY hY m) = G.comp (chowClass.{v} D sY hY m)) :
    F = G :=
  AddMonoidHom.ext fun c => QuotientAddGroup.induction_on c fun α => DFunLike.congr_fun h α

/-! ### The descent is equivalent to killing rational equivalence to zero -/

/-- **A homomorphism of cycle groups is induced by one of Chow groups exactly when it kills
rational equivalence to zero.** In the situation of Stacks 0EDT let `X, Y/B` be good and let
`φ : Z_m(Y) ⟶ Z_n(X)` be additive. There is a homomorphism `F : CH_m(Y) ⟶ CH_n(X)` of the Chow
groups of Stacks 0EQ6, part (4), with `F [α] = [φ α]` for every cycle `α` if and only if `φ`
carries every cycle rationally equivalent to zero to a cycle rationally equivalent to zero. -/
theorem exists_chowGroupHom_comp_chowClass_iff (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (m n : ℤ)
    (φ : CycleGroup D sY m →+ CycleGroup D sX n) :
    (∃ F : chowGroup.{v} D sY hY m →+ chowGroup.{v} D sX hX n,
        F.comp (chowClass.{v} D sY hY m) = (chowClass.{v} D sX hX n).comp φ) ↔
      ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZero.{v} D sY hY m γ →
        IsRationallyEquivalentToZero.{v} D sX hX n (φ γ) := by
  refine ⟨fun ⟨F, hF⟩ γ hγ => ?_,
    fun hφ => ⟨chowGroupHomOfCycleHom.{v} D sX hX sY hY m n φ hφ,
      AddMonoidHom.ext fun α => rfl⟩⟩
  refine (chowClass_eq_zero_iff.{v} D sX hX n _).1 ?_
  have h : F (chowClass.{v} D sY hY m γ) = chowClass.{v} D sX hX n (φ γ) :=
    DFunLike.congr_fun hF γ
  rw [← h, (chowClass_eq_zero_iff.{v} D sY hY m γ).2 hγ, map_zero]

/-! ### The two operations of Section 82.21 -/

/-- **The cost of proper pushforward on Chow groups is exactly the vanishing statement of
Stacks 0EQC.** For a proper morphism `p : X ⟶ Y` of good algebraic spaces over the base there is
a homomorphism `p_* : CH_k(X) ⟶ CH_k(Y)` with `p_*[α] = [p_*α]` for every cycle `α` if and only
if the pushforward of cycles of Stacks 0EP1 carries cycles rationally equivalent to zero to
cycles rationally equivalent to zero, which is Stacks 0EQC. -/
theorem exists_chowGroupProperPushforwardHom_iff (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {p : X ⟶ Y} (hpB : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p) (k : ℤ) :
    (∃ F : chowGroup.{v} D sX hX k →+ chowGroup.{v} D sY hY k,
        F.comp (chowClass.{v} D sX hX k) =
          (chowClass.{v} D sY hY k).comp
            (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k)) ↔
      ∀ γ : CycleGroup D sX k, IsRationallyEquivalentToZero.{v} D sX hX k γ →
        IsRationallyEquivalentToZero.{v} D sY hY k
          (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k γ) :=
  exists_chowGroupHom_comp_chowClass_iff.{v} D sY hY sX hX k k
    (properCyclePushforward D sX hX sY hY hpB hp.2.1.2 k)

/-- **The cost of flat pullback on Chow groups is exactly the vanishing statement of
Stacks 0EQB.** For a morphism `f : X ⟶ Y` of good algebraic spaces over the base which is flat
of relative dimension `r`, and for `m + r = n`, there is a homomorphism
`f^* : CH_m(Y) ⟶ CH_n(X)` with `f^*[α] = [f^*α]` for every cycle `α` if and only if the flat
pullback of cycles of Stacks 0EP9 carries cycles rationally equivalent to zero to cycles
rationally equivalent to zero, which is Stacks 0EQB. -/
theorem exists_flatPullbackChowHom_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (m n : ℤ)
    (hmn : m + (r : ℤ) = n) :
    (∃ F : chowGroup.{v} D sY hY m →+ chowGroup.{v} D sX hX n,
        F.comp (chowClass.{v} D sY hY m) =
          (chowClass.{v} D sX hX n).comp
            (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn)) ↔
      ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZero.{v} D sY hY m γ →
        IsRationallyEquivalentToZero.{v} D sX hX n
          (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn γ) :=
  exists_chowGroupHom_comp_chowClass_iff.{v} D sX hX sY hY m n
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn)

end AlgebraicGeometry.Space

end
