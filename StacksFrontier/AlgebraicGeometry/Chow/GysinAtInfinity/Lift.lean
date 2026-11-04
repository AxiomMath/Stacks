module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Triviality

/-!
# Lifts over the complement of a divisor at infinity

Let `π : W ⟶ X` be locally of finite type over the base of chapter 42 and let `j : U ⟶ W` be an
open immersion with `U ⟶ X` flat of relative dimension one. For a test scheme `g : T ⟶ X`, a
class `β ∈ A_{k+1}(W ×_X T)` is a *lift* of `α ∈ A_k(T)` when its restriction to `U ×_X T` is the
flat pullback of `α`. This is the auxiliary notion in the construction of the class at infinity of
Stacks 0F9J.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.IsLift` — the lift relation.

## Main results

* `Stacks.Chow.chowGroupRestrict_surjective` and
  `Stacks.Chow.exists_chowPushforwardOfIsClosedImmersion_eq_of_chowGroupRestrict_eq_zero` —
  Stacks 02RX along an arbitrary open immersion.
* `Stacks.Chow.GysinAtInfinity.exists_isLift` — every class has a lift.
* `Stacks.Chow.GysinAtInfinity.IsLift.properChowPushforward`, `IsLift.flatPullbackChow` and
  `IsLift.gysin` — lifts transform under proper pushforward (Stacks 02RG), flat pullback
  (Stacks 02RD) and the Gysin map of a divisor on the test scheme (Stacks 02TA, 0B71).
* `Stacks.Chow.GysinAtInfinity.onChow_chowPushforward_zeroScheme_eq_zero` — the Gysin map of a
  divisor with trivial normal bundle kills classes pushed forward from the divisor (Remark 0B6Z,
  through Stacks 0F95 and 02SP).
* `Stacks.Chow.GysinAtInfinity.IsLift.cap_eq` — when the complement of `U` is such a divisor, its
  Gysin class does not see the choice of the lift.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

variable {X W U : Scheme.{u}} (π : W ⟶ X) (j : U ⟶ W)

/-- The base change `U ×_X T ⟶ W ×_X T` of `j : U ⟶ W` along a test scheme `g : T ⟶ X`. -/
abbrev openBaseChange {T : Scheme.{u}} (g : T ⟶ X) : pullback (j ≫ π) g ⟶ pullback π g :=
  pullback.map (j ≫ π) g π g j (𝟙 T) (𝟙 X) (by simp) (by simp)

/-- The base change of `j` lies over `j` on the first factors. -/
@[reassoc (attr := simp)]
theorem openBaseChange_fst {T : Scheme.{u}} (g : T ⟶ X) :
    openBaseChange π j g ≫ pullback.fst π g = pullback.fst (j ≫ π) g ≫ j :=
  pullback.lift_fst _ _ _

/-- The base change of `j` lies over the identity of `T`. -/
@[reassoc (attr := simp)]
theorem openBaseChange_snd {T : Scheme.{u}} (g : T ⟶ X) :
    openBaseChange π j g ≫ pullback.snd π g = pullback.snd (j ≫ π) g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The square formed by `j`, its base change and the first projections is cartesian. -/
theorem isPullback_openBaseChange {T : Scheme.{u}} (g : T ⟶ X) :
    IsPullback (pullback.fst (j ≫ π) g) (openBaseChange π j g) j (pullback.fst π g) := by
  refine IsPullback.of_bot ?_ (openBaseChange_fst π j g).symm (IsPullback.of_hasPullback π g)
  rw [openBaseChange_snd]
  exact IsPullback.of_hasPullback (j ≫ π) g

/-- The base change of an open immersion `j` along a test scheme is an open immersion. -/
theorem isOpenImmersion_openBaseChange [IsOpenImmersion j] {T : Scheme.{u}} (g : T ⟶ X) :
    IsOpenImmersion (openBaseChange π j g) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_openBaseChange π j g)
    inferInstance

end GysinAtInfinity

/-! ### The localization sequence along an arbitrary open immersion -/

section Localization

variable (C : ChowSituation.{u}) {X Y U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]

/-- Restriction of Chow classes along an open immersion is surjective: Stacks 02RX read along an
arbitrary open immersion, from the surjectivity of restriction of cycles of Stacks 02RC. -/
theorem chowGroupRestrict_surjective (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    (k : ℤ) : Function.Surjective (chowGroupRestrict C sX sU j hj k) := by
  intro q
  obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  obtain ⟨c, hc⟩ := cycleGroupRestrict_surjective C sX sU j hj k d
  exact ⟨QuotientAddGroup.mk' _ c, by rw [chowGroupRestrict_mk, hc]⟩

/-- A class restricting to zero along an open immersion is pushed forward from the closed
complement: Stacks 02RX read along an arbitrary open immersion. -/
theorem exists_chowPushforwardOfIsClosedImmersion_eq_of_chowGroupRestrict_eq_zero
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sY) (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) (hcompl : Set.range i.base = (Set.range j.base)ᶜ) (k : ℤ)
    (β : chowGroup C sX k) (hβ : chowGroupRestrict C sX sU j hj k β = 0) :
    ∃ γ : chowGroup C sY k, chowPushforwardOfIsClosedImmersion C sY sX i hi k γ = β := by
  rw [chowGroupRestrict_eq_chowPushforwardOfIso, AddMonoidHom.comp_apply] at hβ
  have hinj := (chowGroupEquivOfIso C (j.opensRange.ι ≫ sX) sU j.isoOpensRange.inv
    (isoOpensRange_inv_comp_base C sX sU j hj) k).injective
  have h0 : chowGroupOpensRestrictOfIsOpenImmersion C sX j.opensRange k β = 0 :=
    hinj (hβ.trans (map_zero _).symm)
  have hrange : Set.range i.base = (Set.range j.opensRange.ι.base)ᶜ := by
    rw [hcompl, Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
  exact (exact_chowPushforward_chowGroupOpensRestrict C sX sY i hi j.opensRange hrange k β).1 h0

end Localization

namespace GysinAtInfinity

/-! ### Lifts of classes from the test scheme -/

section Lift

variable (C : ChowSituation.{u}) {X W U : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1)

/-- The structure morphism of `W ×_X T` over the base, through `W`. -/
abbrev testStr {T : Scheme.{u}} (g : T ⟶ X) : pullback π g ⟶ C.S :=
  pullback.fst π g ≫ (π ≫ f)

/-- The structure morphism of `U ×_X T` over the base, through `T`. -/
abbrev openStr {T : Scheme.{u}} (g : T ⟶ X) : pullback (j ≫ π) g ⟶ C.S :=
  pullback.snd (j ≫ π) g ≫ (g ≫ f)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [IsOpenImmersion j] [Flat (j ≫ π)] in
/-- The structure morphism of `W ×_X T` restricts to that of `U ×_X T` along the base change of
`j`. -/
theorem openBaseChange_comp_testStr {T : Scheme.{u}} (g : T ⟶ X) :
    openBaseChange π j g ≫ testStr C f π g = openStr C f π j g := by
  rw [testStr, openStr, ← Category.assoc, openBaseChange_fst, Category.assoc,
    ← Category.assoc j π f, pullback.condition_assoc]

omit [Flat (j ≫ π)] in
include hU in
/-- The projection `U ×_X T ⟶ T` has relative dimension one. -/
theorem relativeDimension_openSnd {T : Scheme.{u}} (g : T ⟶ X) :
    AlgebraicGeometry.RelativeDimension (pullback.snd (j ≫ π) g) 1 :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback (j ≫ π) g) hU

/-- `β ∈ A_{k+1}(W ×_X T)` is a lift of `α ∈ A_k(T)` when its restriction to the open
`U ×_X T` is the flat pullback of `α` along `U ×_X T ⟶ T`. -/
def IsLift {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ f) k) (β : chowGroup C (testStr C f π g) (k + 1)) : Prop :=
  haveI := isOpenImmersion_openBaseChange π j g
  chowGroupRestrict C (testStr C f π g) (openStr C f π j g) (openBaseChange π j g)
      (openBaseChange_comp_testStr C f π j g) (k + 1) β =
    flatPullbackChow C (openStr C f π j g) (g ≫ f) (pullback.snd (j ≫ π) g) rfl 1
      (relativeDimension_openSnd π j hU g) k
      (flatPullbackDescends C _ _ _ _ _ _ _) α

/-- Every class `α ∈ A_k(T)` has a lift `β ∈ A_{k+1}(W ×_X T)`. -/
theorem exists_isLift {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ f) k) : ∃ β, IsLift C f π j hU g k α β := by
  have := isOpenImmersion_openBaseChange π j g
  exact chowGroupRestrict_surjective C _ _ (openBaseChange π j g)
    (openBaseChange_comp_testStr C f π j g) (k + 1) _

/-- The zero class is a lift of the zero class. -/
theorem isLift_zero {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    IsLift C f π j hU g k 0 0 := by
  unfold IsLift
  rw [map_zero, map_zero]

/-- The sum of lifts of `α` and `α'` is a lift of `α + α'`. -/
theorem IsLift.add {T : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g] {k : ℤ}
    {α α' : chowGroup C (g ≫ f) k} {β β' : chowGroup C (testStr C f π g) (k + 1)}
    (h : IsLift C f π j hU g k α β) (h' : IsLift C f π j hU g k α' β') :
    IsLift C f π j hU g k (α + α') (β + β') := by
  unfold IsLift at *
  rw [map_add, map_add, h, h']

/-- The difference of two lifts of the same class restricts to zero on `U ×_X T`. -/
theorem IsLift.sub {T : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g] {k : ℤ}
    {α : chowGroup C (g ≫ f) k} {β β' : chowGroup C (testStr C f π g) (k + 1)}
    (h : IsLift C f π j hU g k α β) (h' : IsLift C f π j hU g k α β') :
    haveI := isOpenImmersion_openBaseChange π j g
    chowGroupRestrict C (testStr C f π g) (openStr C f π j g) (openBaseChange π j g)
      (openBaseChange_comp_testStr C f π j g) (k + 1) (β - β') = 0 := by
  unfold IsLift at *
  rw [map_sub, h, h', sub_self]

omit [LocallyOfFiniteType π] in
/-- The base change map `W ×_X T' ⟶ W ×_X T` lies over `W`. -/
@[reassoc (attr := simp)]
theorem bivariantBaseChangeMap_fst' {T T' : Scheme.{u}} (g : T ⟶ X) (h : T' ⟶ T) :
    bivariantBaseChangeMap π g h ≫ pullback.fst π g = pullback.fst π (h ≫ g) :=
  (pullbackMap_fst π (h ≫ g) π g (𝟙 W) h (𝟙 X) (by simp) (by simp)).trans (Category.comp_id _)

omit [LocallyOfFiniteType π] in
omit [LocallyOfFiniteType f] in
/-- The base change map `W ×_X T' ⟶ W ×_X T` is compatible with the structure morphisms over the
base. -/
theorem bivariantBaseChangeMap_comp_testStr {T T' : Scheme.{u}} (g : T ⟶ X) (h : T' ⟶ T) :
    bivariantBaseChangeMap π g h ≫ testStr C f π g = testStr C f π (h ≫ g) := by
  rw [testStr, ← Category.assoc, bivariantBaseChangeMap_fst']

omit [LocallyOfFiniteType f] [LocallyOfFiniteType π] [IsOpenImmersion j] [Flat (j ≫ π)] in
/-- The base change map `U ×_X T' ⟶ U ×_X T` is compatible with the structure morphisms over the
base. -/
theorem bivariantBaseChangeMap_comp_openStr {T T' : Scheme.{u}} (g : T ⟶ X) (h : T' ⟶ T) :
    bivariantBaseChangeMap (j ≫ π) g h ≫ openStr C f π j g = openStr C f π j (h ≫ g) := by
  rw [openStr, openStr, ← Category.assoc, compositeMiddleBaseChange_snd, Category.assoc,
    Category.assoc]

omit [LocallyOfFiniteType π] [IsOpenImmersion j] [Flat (j ≫ π)] in
/-- The two base changes of `j` along a morphism of test schemes form a cartesian square. -/
theorem isPullback_openBaseChange_bivariantBaseChangeMap {T T' : Scheme.{u}} (g : T ⟶ X)
    (h : T' ⟶ T) :
    IsPullback (openBaseChange π j (h ≫ g)) (bivariantBaseChangeMap (j ≫ π) g h)
      (bivariantBaseChangeMap π g h) (openBaseChange π j g) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_bivariantBaseChangeMap π g h)
  · rw [openBaseChange_snd, openBaseChange_snd]
    exact isPullback_bivariantBaseChangeMap (j ≫ π) g h
  · refine pullback.hom_ext ?_ ?_ <;> simp

/-- Restriction of Chow classes commutes with the transport along an equality of degrees. -/
theorem chowGroupRestrict_chowGroupDegreeEquiv_heq {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (m : B ⟶ A)
    [IsOpenImmersion m] (hm : m ≫ sA = sB) {a b : ℤ} (hab : a = b) (x : chowGroup C sA a) :
    chowGroupRestrict C sA sB m hm b (chowGroupDegreeEquiv C sA hab x) ≍
      chowGroupRestrict C sA sB m hm a x := by
  subst hab
  rfl

/-- **Lifts and proper pushforward.** The pushforward of a lift along the base change of a proper
morphism of test schemes is a lift of the pushforward: restriction to the open part commutes with
proper pushforward, and flat pullback along `U ×_X T ⟶ T` commutes with proper pushforward by
Stacks 02RG. -/
theorem IsLift.properChowPushforward {T T' : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g]
    (h : T' ⟶ T) [IsProper h] {k : ℤ} {α' : chowGroup C ((h ≫ g) ≫ f) k}
    {β' : chowGroup C (testStr C f π (h ≫ g)) (k + 1)}
    (hl : IsLift C f π j hU (h ≫ g) k α' β') :
    haveI : IsProper (bivariantBaseChangeMap π g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap π g h)
        inferInstance
    IsLift C f π j hU g k
      (Stacks.Chow.properChowPushforward C ((h ≫ g) ≫ f) (g ≫ f) h (by simp) k
        (properPushforwardDescends C _ _ _ _ _) α')
      (Stacks.Chow.properChowPushforward C (testStr C f π (h ≫ g)) (testStr C f π g)
        (bivariantBaseChangeMap π g h) (bivariantBaseChangeMap_comp_testStr C f π g h) (k + 1)
        (properPushforwardDescends C _ _ _ _ _) β') := by
  have : IsProper (bivariantBaseChangeMap π g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap π g h) inferInstance
  have : IsProper (bivariantBaseChangeMap (j ≫ π) g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (j ≫ π) g h)
      inferInstance
  have := isOpenImmersion_openBaseChange π j g
  have := isOpenImmersion_openBaseChange π j (h ≫ g)
  unfold IsLift at hl ⊢
  rw [chowGroupRestrict_properChowPushforward C (testStr C f π (h ≫ g)) (testStr C f π g)
    (openStr C f π j (h ≫ g)) (openStr C f π j g) (bivariantBaseChangeMap π g h)
    (bivariantBaseChangeMap_comp_testStr C f π g h) (openBaseChange π j (h ≫ g))
    (openBaseChange_comp_testStr C f π j (h ≫ g)) (openBaseChange π j g)
    (openBaseChange_comp_testStr C f π j g) (bivariantBaseChangeMap (j ≫ π) g h)
    (bivariantBaseChangeMap_comp_openStr C f π j g h)
    (isPullback_openBaseChange_bivariantBaseChangeMap π j g h) (k + 1)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) β', hl]
  exact (properPushforwardFlatPullbackBaseChange C ((h ≫ g) ≫ f) (openStr C f π j (h ≫ g))
    (g ≫ f) (openStr C f π j g) h (by simp) (bivariantBaseChangeMap (j ≫ π) g h)
    (bivariantBaseChangeMap_comp_openStr C f π j g h) (pullback.snd (j ≫ π) (h ≫ g)) rfl
    (pullback.snd (j ≫ π) g) rfl (isPullback_bivariantBaseChangeMap (j ≫ π) g h) 1
    (relativeDimension_openSnd π j hU (h ≫ g)) (relativeDimension_openSnd π j hU g) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) α').symm

/-- **Lifts and flat pullback.** The flat pullback of a lift along the base change of a flat
morphism of test schemes is a lift of the flat pullback: restriction to the open part commutes
with flat pullback, and flat pullbacks compose (Stacks 02RD). -/
theorem IsLift.flatPullbackChow {T T' : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) {k : ℤ} {α : chowGroup C (g ≫ f) k}
    {β : chowGroup C (testStr C f π g) (k + 1)} (hl : IsLift C f π j hU g k α β) :
    haveI : LocallyOfFiniteType (bivariantBaseChangeMap π g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap π g h)
        inferInstance
    haveI : Flat (bivariantBaseChangeMap π g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap π g h)
        inferInstance
    IsLift C f π j hU (h ≫ g) (k + (r : ℤ))
      (Stacks.Chow.flatPullbackChow C ((h ≫ g) ≫ f) (g ≫ f) h (by simp) r hr k
        (flatPullbackDescends C _ _ _ _ _ _ _) α)
      (chowGroupDegreeEquiv C (testStr C f π (h ≫ g)) (by ring : k + 1 + (r : ℤ) = k + r + 1)
        (Stacks.Chow.flatPullbackChow C (testStr C f π (h ≫ g)) (testStr C f π g)
          (bivariantBaseChangeMap π g h) (bivariantBaseChangeMap_comp_testStr C f π g h) r
          (AlgebraicGeometry.RelativeDimension.of_isPullback
            (isPullback_bivariantBaseChangeMap π g h) hr) (k + 1)
          (flatPullbackDescends C _ _ _ _ _ _ _) β)) := by
  have : LocallyOfFiniteType (bivariantBaseChangeMap π g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap π g h) inferInstance
  have : Flat (bivariantBaseChangeMap π g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap π g h) inferInstance
  have : LocallyOfFiniteType (bivariantBaseChangeMap (j ≫ π) g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (j ≫ π) g h)
      inferInstance
  have : Flat (bivariantBaseChangeMap (j ≫ π) g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap (j ≫ π) g h)
      inferInstance
  have := isOpenImmersion_openBaseChange π j g
  have := isOpenImmersion_openBaseChange π j (h ≫ g)
  have hrU : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap (j ≫ π) g h) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_bivariantBaseChangeMap (j ≫ π) g h) hr
  unfold IsLift at hl ⊢
  apply eq_of_heq
  refine (chowGroupRestrict_chowGroupDegreeEquiv_heq C _ _ _ _ _ _).trans ?_
  rw [chowGroupRestrict_flatPullbackChow C (testStr C f π (h ≫ g)) (testStr C f π g)
    (openStr C f π j (h ≫ g)) (openStr C f π j g) (bivariantBaseChangeMap π g h)
    (bivariantBaseChangeMap_comp_testStr C f π g h) r
    (AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_bivariantBaseChangeMap π g h) hr)
    (openBaseChange π j (h ≫ g)) (openBaseChange_comp_testStr C f π j (h ≫ g))
    (openBaseChange π j g) (openBaseChange_comp_testStr C f π j g)
    (bivariantBaseChangeMap (j ≫ π) g h) (bivariantBaseChangeMap_comp_openStr C f π j g h)
    (isPullback_openBaseChange_bivariantBaseChangeMap π j g h) hrU (k + 1)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) β, hl]
  exact flatPullbackChow_comm_of_comp_eq C (openStr C f π j (h ≫ g)) (openStr C f π j g)
    ((h ≫ g) ≫ f) (g ≫ f) (bivariantBaseChangeMap (j ≫ π) g h) (pullback.snd (j ≫ π) g)
    (pullback.snd (j ≫ π) (h ≫ g)) h (bivariantBaseChangeMap_comp_openStr C f π j g h) rfl rfl
    (by simp) r 1 hrU (relativeDimension_openSnd π j hU g)
    (relativeDimension_openSnd π j hU (h ≫ g)) hr (compositeMiddleBaseChange_snd _ _ _) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α

/-- The zero scheme of a section of an invertible module on a test scheme, pulled back to
`W ×_X T`. -/
abbrev testDivisor {T : Scheme.{u}} (g : T ⟶ X) (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) : (pullback π g).IdealSheafData :=
  Stacks.Divisors.zeroScheme (pullback π g) ((Scheme.Modules.pullback (pullback.snd π g)).obj M)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd π g) M t)

omit [LocallyOfFiniteType π] [IsOpenImmersion j] [Flat (j ≫ π)] in
/-- Under the identifications of the pulled-back divisors with `U ×_X D` and `W ×_X D`, where
`D = Z(t) ⊆ T`, the inclusion of the divisor on `U ×_X T` in the divisor on `W ×_X T` is the base
change of `j` along `D ⟶ X`. -/
theorem openBaseChange_comp_testDivisor_eq {T : Scheme.{u}} (g : T ⟶ X) (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) :
    (bivariantDivisorBaseChangeIso (j ≫ π) g M t).hom ≫
        zeroSchemeRestrictMap (pullback.snd (j ≫ π) g) (pullback.snd π g) (openBaseChange π j g)
          (openBaseChange_snd π j g) M t =
      openBaseChange π j ((Stacks.Divisors.zeroScheme T M t).subschemeι ≫ g) ≫
        (bivariantDivisorBaseChangeIso π g M t).hom := by
  refine (cancel_mono (testDivisor π g M t).subschemeι).1 ?_
  rw [Category.assoc, Category.assoc, zeroSchemeRestrictMap_comp_subschemeι,
    bivariantDivisorBaseChangeIso_hom_subschemeι, ← Category.assoc,
    bivariantDivisorBaseChangeIso_hom_subschemeι]
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

/-- **Lifts and the Gysin map of a divisor on the test scheme.** Pulling a lift back to the divisor
`D = Z(t) ⊆ T` by the Gysin map of the pulled-back section, and reading it on `W ×_X D` through the
identification of Stacks 0B6Y, gives a lift of the Gysin image: restriction to the open part
commutes with the Gysin map (the open-immersion case of Stacks 02TA), and the Gysin map commutes
with flat pullback along `U ×_X T ⟶ T` (Stacks 0B71). -/
theorem IsLift.gysin {T : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g] (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) {k : ℤ} {α : chowGroup C (g ≫ f) (k + 1)}
    {β : chowGroup C (testStr C f π g) (k + 1 + 1)} (hl : IsLift C f π j hU g (k + 1) α β) :
    IsLift C f π j hU ((Stacks.Divisors.zeroScheme T M t).subschemeι ≫ g) k
      ((gysinSystemOfInvertible C).onChow (g ≫ f) M t k α)
      (chowPushforwardOfIso C ((testDivisor π g M t).subschemeι ≫ testStr C f π g)
        (testStr C f π ((Stacks.Divisors.zeroScheme T M t).subschemeι ≫ g))
        (bivariantDivisorBaseChangeIso π g M t).inv
        (by rw [Iso.inv_comp_eq, testStr, testStr,
          bivariantDivisorBaseChangeIso_hom_comp_structure])
        (k + 1)
        ((gysinSystemOfInvertible C).onChow (testStr C f π g)
          ((Scheme.Modules.pullback (pullback.snd π g)).obj M)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd π g) M t) (k + 1) β)) := by
  set D := Stacks.Divisors.zeroScheme T M t
  set eb := bivariantDivisorBaseChangeIso π g M t
  set eV := bivariantDivisorBaseChangeIso (j ≫ π) g M t
  set j' := zeroSchemeRestrictMap (pullback.snd (j ≫ π) g) (pullback.snd π g)
    (openBaseChange π j g) (openBaseChange_snd π j g) M t
  have := isOpenImmersion_openBaseChange π j g
  have := isOpenImmersion_openBaseChange π j (D.subschemeι ≫ g)
  have hcomm : j' ≫ eb.inv = eV.inv ≫ openBaseChange π j (D.subschemeι ≫ g) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, openBaseChange_comp_testDivisor_eq]
  have hsq : IsPullback j' eV.inv eb.inv (openBaseChange π j (D.subschemeι ≫ g)) :=
    IsPullback.of_vert_isIso ⟨hcomm⟩
  have hpB : pullback.snd π g ≫ g ≫ f = testStr C f π g := by
    rw [testStr, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hj : j' ≫ ((testDivisor π g M t).subschemeι ≫ testStr C f π g) =
      (testDivisor (j ≫ π) g M t).subschemeι ≫ openStr C f π j g := by
    rw [← Category.assoc, zeroSchemeRestrictMap_comp_subschemeι, Category.assoc,
      openBaseChange_comp_testStr]
  have hq' : eV.inv ≫ openStr C f π j (D.subschemeι ≫ g) =
      (testDivisor (j ≫ π) g M t).subschemeι ≫ openStr C f π j g := by
    rw [Iso.inv_comp_eq, openStr, openStr]
    simp [eV, D]
  have hzs : zeroSchemePullbackHom (pullback.snd (j ≫ π) g) M t ≫ 𝟙 _ =
      eV.inv ≫ pullback.snd (j ≫ π) (D.subschemeι ≫ g) := by
    rw [Category.comp_id, Iso.eq_inv_comp]
    refine (cancel_mono D.subschemeι).1 ?_
    rw [Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
      bivariantDivisorBaseChangeIso_hom_subschemeι, compositeMiddleBaseChange_snd]
  unfold IsLift at hl ⊢
  have e1 := chowGroupRestrict_properChowPushforward C
    ((testDivisor π g M t).subschemeι ≫ testStr C f π g) (testStr C f π (D.subschemeι ≫ g))
    ((testDivisor (j ≫ π) g M t).subschemeι ≫ openStr C f π j g)
    (openStr C f π j (D.subschemeι ≫ g)) eb.inv
    (by rw [Iso.inv_comp_eq, testStr, testStr, bivariantDivisorBaseChangeIso_hom_comp_structure])
    j' hj (openBaseChange π j (D.subschemeι ≫ g))
    (openBaseChange_comp_testStr C f π j (D.subschemeι ≫ g)) eV.inv hq' hsq
    (k + 1) (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    ((gysinSystemOfInvertible C).onChow (testStr C f π g)
      ((Scheme.Modules.pullback (pullback.snd π g)).obj M)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd π g) M t) (k + 1) β)
  have e2 := GysinSystem.onChow_openImmersion
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (g ≫ f) (pullback.snd (j ≫ π) g) (pullback.snd π g) (openStr C f π j g)
    (testStr C f π g) rfl hpB (openBaseChange π j g) (openBaseChange_snd π j g) M t (k + 1) j'
    (zeroSchemeRestrictMap_comp_subschemeι _ _ _ _ M t) hj
    (openBaseChange_comp_testStr C f π j g) β
  have h71 := gysinSystemOfInvertible_onChow_flatPullbackChow C (g ≫ f) (pullback.snd (j ≫ π) g)
    1 (relativeDimension_openSnd π j hU g) k M t (openStr C f π j g) rfl
    (flatPullbackDescends C _ _ _ _ _ _ _)
    (by rw [← Category.assoc, zeroSchemePullbackHom_subschemeι, Category.assoc])
        (flatPullbackDescends C _ _ _ _ _ _ _) α
  have hiso := flatPullbackChow_chowPushforwardOfIso C (D.subschemeι ≫ g ≫ f)
    ((testDivisor (j ≫ π) g M t).subschemeι ≫ openStr C f π j g) (D.subschemeι ≫ g ≫ f)
    (openStr C f π j (D.subschemeι ≫ g)) (𝟙 _) (Category.id_comp _) eV.inv hq'
    (zeroSchemePullbackHom (pullback.snd (j ≫ π) g) M t)
    (by rw [← Category.assoc, zeroSchemePullbackHom_subschemeι, Category.assoc])
    (pullback.snd (j ≫ π) (D.subschemeι ≫ g)) rfl hzs 1
    (relativeDimension_zeroSchemePullbackHom _ M t 1 (relativeDimension_openSnd π j hU g))
    (relativeDimension_openSnd π j hU (D.subschemeι ≫ g)) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    ((gysinSystemOfInvertible C).onChow (g ≫ f) M t k α)
  rw [chowPushforwardOfIso_id] at hiso
  refine e1.trans ?_
  refine (congrArg (Stacks.Chow.properChowPushforward C _ _ eV.inv hq' (k + 1)
    (properPushforwardDescends C _ _ _ _ _)) (e2.trans (congrArg _ hl))).trans ?_
  refine (congrArg (Stacks.Chow.properChowPushforward C _ _ eV.inv hq' (k + 1)
    (properPushforwardDescends C _ _ _ _ _)) h71).trans ?_
  exact hiso.symm

omit [LocallyOfFiniteType π] [IsOpenImmersion j] [Flat (j ≫ π)] in
/-- The range of the base change of `j` is the inverse image of the range of `j`. -/
theorem range_openBaseChange {T : Scheme.{u}} (g : T ⟶ X) :
    Set.range (openBaseChange π j g).base = (pullback.fst π g).base ⁻¹' Set.range j.base := by
  have hsq := isPullback_openBaseChange π j g
  rw [← hsq.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (hsq.isoPullback.hom).surjective.range_eq,
    Set.image_univ, Scheme.Pullback.range_snd]

end Lift

/-! ### The divisor at infinity and the vanishing of its Gysin map on its own classes -/

section Vanishing

variable (C : ChowSituation.{u})

/-- **Stacks 0B6Z, on Chow groups.** If an invertible module restricts trivially to the zero scheme
`D` of a section, the Gysin map kills every class pushed forward from `D`: by Stacks 0F95 it is
capping with `c₁(L|_D) = c₁(𝒪_D)`, which is zero by Stacks 02SP. -/
theorem onChow_chowPushforward_zeroScheme_eq_zero {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme Y M t).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme Y M t).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y M t).subschemeι).obj M))
    (m : ℤ) (δ : chowGroup C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) (m + 1)) :
    (gysinSystemOfInvertible C).onChow q M t m
      (chowPushforwardOfIsClosedImmersion C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
        (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl (m + 1) δ) = 0 := by
  induction δ using QuotientAddGroup.induction_on with
  | H d =>
    show (gysinSystemOfInvertible C).onChow q M t m
      (chowPushforwardOfIsClosedImmersion C _ q _ rfl (m + 1)
        (QuotientAddGroup.mk' (rationalEquivalences C _ (m + 1)) d)) = 0
    rw [chowPushforwardOfIsClosedImmersion_mk, GysinSystem.onChow_mk]
    show gysinHomomorphismOfInvertible C q m M t _ = 0
    rw [gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι]
    obtain ⟨e⟩ := htriv
    rw [firstChernClassCapOfInvertible_congr C _ m _
      (SheafOfModules.unit (Stacks.Divisors.zeroScheme Y M t).subscheme.ringCatSheaf) e d,
      firstChernClassCapOfInvertible_unit]

end Vanishing

/-! ### Independence of the lift -/

section Independence

variable (C : ChowSituation.{u}) {X W U : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))

/-- The Gysin class `i_∞^* ∈ A¹(Z(s) ⟶ W)` of the divisor, Stacks 0B79. -/
abbrev divisorClass :
    BivariantClass C (gysinSystemOfInvertible C) (gysinTripleInclusion L s ≫ (π ≫ f)) (π ≫ f)
      (gysinTripleInclusion L s) rfl 1 :=
  (gysinBivariantClass C (π ≫ f) L s).1

omit [LocallyOfFiniteType π] [IsOpenImmersion j] [Flat (j ≫ π)] in
include hcompl in
/-- The pulled-back divisor on `W ×_X T` is the complement of `U ×_X T`. -/
theorem range_gysinTripleDivisor {T : Scheme.{u}} (g : T ⟶ X) :
    Set.range (gysinTripleDivisor L s (pullback.fst π g)).subschemeι.base =
      (Set.range (openBaseChange π j g).base)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, gysinTripleDivisor,
    Stacks.Divisors.zeroScheme_pullback, Scheme.IdealSheafData.support_comap,
    range_openBaseChange, ← Set.preimage_compl, ← hcompl, Scheme.IdealSheafData.range_subschemeι]
  rfl

include hcompl htriv in
/-- **The class is independent of the chosen lift**: two lifts of the same class differ by a class
pushed forward from the divisor (Stacks 02RX), and the Gysin map of the divisor kills such a class
because the divisor has trivial normal bundle (Remark 0B6Z with Stacks 0F95 and 02SP). -/
theorem IsLift.cap_eq {T : Scheme.{u}} {g : T ⟶ X} [LocallyOfFiniteType g] {k : ℤ}
    {α : chowGroup C (g ≫ f) k} {β β' : chowGroup C (testStr C f π g) (k + 1)}
    (hβ : IsLift C f π j hU g k α β) (hβ' : IsLift C f π j hU g k α β') :
    (divisorClass C f π L s).cap (pullback.fst π g) (k + 1) β =
      (divisorClass C f π L s).cap (pullback.fst π g) (k + 1) β' := by
  have := isOpenImmersion_openBaseChange π j g
  obtain ⟨δ, hδ⟩ := exists_chowPushforwardOfIsClosedImmersion_eq_of_chowGroupRestrict_eq_zero C
    (testStr C f π g) _ (openStr C f π j g)
    (gysinTripleDivisor L s (pullback.fst π g)).subschemeι rfl (openBaseChange π j g)
    (openBaseChange_comp_testStr C f π j g) (range_gysinTripleDivisor π j L s hcompl g) (k + 1)
    (β - β') (IsLift.sub C f π j hU hβ hβ')
  rw [← sub_eq_zero, ← map_sub, ← hδ, (gysinBivariantClass C (π ≫ f) L s).2,
    gysinBivariantCap_apply]
  have htrivg := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
    (pullback.fst π g) L s htriv
  rw [show chowPushforwardOfIsClosedImmersion C
      ((gysinTripleDivisor L s (pullback.fst π g)).subschemeι ≫ testStr C f π g)
      (testStr C f π g) (gysinTripleDivisor L s (pullback.fst π g)).subschemeι rfl (k + 1) δ =
      Stacks.Chow.properChowPushforward C _ _ _ rfl (k + 1)
        (properPushforwardDescends C _ _ _ _ _) δ from rfl,
    chowGroupDegreeEquiv_properChowPushforward_comp C _ _ _ rfl (by ring : k + 1 = k + 1 - 1 + 1)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  rw [show Stacks.Chow.properChowPushforward C _ _ _ rfl (k + 1 - 1 + 1)
      (properPushforwardDescends C _ _ _ _ _) _ =
      chowPushforwardOfIsClosedImmersion C _ _ _ rfl (k + 1 - 1 + 1) _ from rfl,
    onChow_chowPushforward_zeroScheme_eq_zero C _ _ _ htrivg, map_zero]

end Independence

end GysinAtInfinity

end Stacks.Chow

end
