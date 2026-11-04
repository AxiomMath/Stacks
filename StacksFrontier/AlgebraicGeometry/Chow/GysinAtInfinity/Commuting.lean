module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ProperModification
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Statement

/-!
# The class at infinity commutes with every bivariant class (Stacks 0FAS)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre at infinity
`i_∞ : W_∞ ⟶ W` and class `C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J. For every `Y ⟶ X` locally of finite
type and every `c ∈ A^p(Y ⟶ X)`, Stacks 0FAS asserts `C ∘ c = c ∘ C` in `A^p(W_∞ ×_X Y ⟶ X)`.

## Main results

* `Stacks.Chow.GysinAtInfinity.isLift_capLift` — capping a lift of `α` with `c` gives a lift of
  `c ∩ α`.
* `Stacks.Chow.GysinAtInfinity.cap_testInfinity` — `c ∩ i_∞^* β` is the Gysin map at infinity
  of `c ∩ β` (condition (3) of Stacks 0B76).
* `Stacks.Chow.BivariantChowClass.restrict_comp_eq_of_bivariantCommute` — commuting classes in
  the sense of Remark 0FA2 have equal composites `res(c₁) ∘ c₂ = res(c₂) ∘ c₁`.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_bivariantCommute` — `C` and `c` commute in
  the sense of Remark 0FA2.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_comp_comm` — **Stacks 0FAS**:
  `C ∘ c = c ∘ C`.

## Implementation notes

The proof is the source's. For `α ∈ CH_k(T)` choose `β ∈ CH_{k+1}(W ×_X T)` restricting over
`b⁻¹(𝐀¹_X) ×_X T` to the flat pullback of `α`; then `C ∩ α = i_∞^* β`
(`Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_cap_eq_of_isLift`). The class `c ∩ β`,
read on `W ×_X (Y ×_X T)`, restricts to the flat pullback of `c ∩ α` because `c` commutes with
restriction to opens and with flat pullback, so `C ∩ (c ∩ α) = i_∞^*(c ∩ β)`; and
`c ∩ i_∞^* β = i_∞^*(c ∩ β)` because `c` is a bivariant class. The two Gysin maps live on
`W ×_X (Y ×_X T)` and on `Y ×_X (W ×_X T)`; they are compared by Stacks 02TA along the canonical
isomorphism, the divisor at infinity of the one pulling back to that of the other.

## References

* [Stacks Project, Tag 0FAS](https://stacks.math.columbia.edu/tag/0FAS)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

/-! ### Transport bookkeeping -/

section Bookkeeping

variable (C : ChowSituation.{u})

/-- Pushforward along the identity, between two equal structure morphisms, is the transport along
their equality. -/
private theorem chowPushforwardOfIso_id_eq_chowGroupCongr {A : Scheme.{u}} {sA sB : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] (h : 𝟙 A ≫ sB = sA) (k : ℤ)
    (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sB (𝟙 A) h k x =
      chowGroupCongr C (by rw [← h, Category.id_comp]) k x := by
  obtain rfl : sA = sB := by rw [← h, Category.id_comp]
  exact chowPushforwardOfIso_id C sA k x

/-- Restriction along an open immersion only depends on the structure morphisms and the class up
to equality. -/
theorem chowGroupRestrict_heq_congr {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB sB' : B ⟶ C.S}
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (v : B ⟶ A) [IsOpenImmersion v]
    (hv : v ≫ sA = sB) (hv' : v ≫ sA' = sB') (hA : sA = sA') (hB : sB = sB') (k : ℤ)
    {x : chowGroup C sA k} {x' : chowGroup C sA' k} (hx : x ≍ x') :
    chowGroupRestrict C sA sB v hv k x ≍ chowGroupRestrict C sA' sB' v hv' k x' := by
  subst hA hB
  cases hx
  rfl

/-- The Gysin map of a Gysin system only depends on the structure morphism and the class up to
equality. -/
theorem onChow_heq_congr (G : GysinSystem C) {A : Scheme.{u}} {q q' : A ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') (L : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) {x : chowGroup C q (k + 1)} {x' : chowGroup C q' (k + 1)}
    (hx : x ≍ x') : G.onChow q L s k x ≍ G.onChow q' L s k x' := by
  subst hq
  cases hx
  rfl

/-- Pushforward along an isomorphism carries heterogeneously equal classes of equal degrees to
heterogeneously equal classes. -/
theorem chowPushforwardOfIso_heq_of_heq {A B : Scheme.{u}} {sA : A ⟶ C.S} {sB : B ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA)
    {k k' : ℤ} (hk : k = k') {x : chowGroup C sA k} {x' : chowGroup C sA k'} (hx : x ≍ x') :
    chowPushforwardOfIso C sA sB u hu k x ≍ chowPushforwardOfIso C sA sB u hu k' x' := by
  subst hk
  cases hx
  rfl

/-- Three composable proper pushforwards are the pushforward along the composite. -/
theorem properChowPushforward_comp₃_eq {A B D E : Scheme.{u}} {sA : A ⟶ C.S} {sB : B ⟶ C.S}
    {sD : D ⟶ C.S} {sE : E ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sB]
    [LocallyOfFiniteType sD] [LocallyOfFiniteType sE] (u : A ⟶ B) (v : B ⟶ D) (w : D ⟶ E)
    (z : A ⟶ E) [IsProper u] [IsProper v] [IsProper w] [IsProper z] (h : u ≫ v ≫ w = z)
    (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sE = sD) (hz : z ≫ sE = sA) (k : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfacw : ProperPushforwardFactorsThroughRationalEquivalence C sD sE w hw k)
    (hfacz : ProperPushforwardFactorsThroughRationalEquivalence C sA sE z hz k)
    (x : chowGroup C sA k) :
    properChowPushforward C sD sE w hw k hfacw
        (properChowPushforward C sB sD v hv k hfacv (properChowPushforward C sA sB u hu k hfacu x))
      = properChowPushforward C sA sE z hz k hfacz x := by
  rw [← properChowPushforward_comp_apply C sA sB sD u v (u ≫ v) rfl hu hv
      (by rw [Category.assoc, hv, hu]) k hfacu hfacv (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C sA sD sE (u ≫ v) w z (by rw [Category.assoc, h]) _ hw hz
      k _ hfacw hfacz]

end Bookkeeping

/-! ### Capping a lift with a bivariant class gives a lift -/

section Lift

variable (C : ChowSituation.{u}) {X W U Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) {G : GysinSystem C}
  (fY : Y ⟶ X) [LocallyOfFiniteType fY] {p : ℤ} (c : BivariantClass C G (fY ≫ f) f fY rfl p)

/-- The class `c ∩ β` of `β ∈ A_{k+1}(W ×_X T)`, read on `W ×_X (Y ×_X T)` through the
canonical isomorphism `Y ×_X (W ×_X T) ≅ W ×_X (Y ×_X T)`, in degree `(k - p) + 1`. -/
def capLift {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (β : chowGroup C (testStr C f π t) (k + 1)) :
    chowGroup C (testStr C f π (pullback.fst fY t ≫ fY)) (k - p + 1) :=
  chowGroupDegreeEquiv C _ (by ring : k + 1 - p = k - p + 1)
    (chowPushforwardOfIso C (pullback.fst fY (pullback.fst π t ≫ π) ≫ (fY ≫ f))
      (testStr C f π (pullback.fst fY t ≫ fY)) (commuteComparisonHom fY π t)
      (commuteComparisonHom_comp_structureMorphism C f fY π t) (k + 1 - p)
      (c.cap (pullback.fst π t ≫ π) (k + 1)
        (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β)))

include hU in
/-- **Capping a lift gives a lift.** If `β ∈ A_{k+1}(W ×_X T)` restricts over `U ×_X T` to the
flat pullback of `α ∈ A_k(T)`, then `c ∩ β` restricts over `U ×_X (Y ×_X T)` to the flat
pullback of `c ∩ α`: restriction to an open is flat pullback of relative dimension zero, and `c`
commutes with both flat pullbacks by Stacks 0B76 (2). -/
theorem isLift_capLift {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    {α : chowGroup C (t ≫ f) k} {β : chowGroup C (testStr C f π t) (k + 1)}
    (hβ : IsLift C f π j hU t k α β) :
    IsLift C f π j hU (pullback.fst fY t ≫ fY) (k - p)
      (chowGroupCongr C (Category.assoc _ _ _).symm (k - p) (c.cap t k α))
      (capLift C f π fY c t k β) := by
  have hιt := isOpenImmersion_openBaseChange π j t
  have hιg := isOpenImmersion_openBaseChange π j (pullback.fst fY t ≫ fY)
  -- the test schemes
  have hm₁ : pullback.snd (j ≫ π) t ≫ t = pullback.fst (j ≫ π) t ≫ (j ≫ π) :=
    pullback.condition.symm
  have hm₂ : openBaseChange π j t ≫ (pullback.fst π t ≫ π) =
      pullback.fst (j ≫ π) t ≫ (j ≫ π) := by
    rw [openBaseChange_fst_assoc]
  have hι' := isPullback_baseChangeMapOfEq fY (pullback.fst π t ≫ π) (openBaseChange π j t)
    (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₂
  have : IsOpenImmersion (baseChangeMapOfEq fY (pullback.fst π t ≫ π) (openBaseChange π j t)
      (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₂) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hι' inferInstance
  have hh' := isPullback_baseChangeMapOfEq fY t (pullback.snd (j ≫ π) t)
    (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₁
  have := flat_baseChangeMapOfEq fY t (pullback.snd (j ≫ π) t)
    (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₁
  have := locallyOfFiniteType_baseChangeMapOfEq fY t (pullback.snd (j ≫ π) t)
    (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₁
  have hr := relativeDimension_openSnd π j hU t
  have hr' := AlgebraicGeometry.RelativeDimension.of_isPullback hh' hr
  have hrg := relativeDimension_openSnd π j hU (pullback.fst fY t ≫ fY)
  -- the comparison isomorphisms and the square relating the two restrictions
  have hsq : IsPullback (baseChangeMapOfEq fY (pullback.fst π t ≫ π) (openBaseChange π j t)
      (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₂) (commuteComparisonHom fY (j ≫ π) t)
      (commuteComparisonHom fY π t) (openBaseChange π j (pullback.fst fY t ≫ fY)) :=
    IsPullback.of_vert_isIso ⟨by
      refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp⟩
  have hsq' : baseChangeMapOfEq fY t (pullback.snd (j ≫ π) t)
      (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₁ ≫ 𝟙 _ =
      commuteComparisonHom fY (j ≫ π) t ≫ pullback.snd (j ≫ π) (pullback.fst fY t ≫ fY) := by
    rw [Category.comp_id]
    refine pullback.hom_ext ?_ ?_ <;> simp
  have hΨU : commuteComparisonHom fY (j ≫ π) t ≫ openStr C f π j (pullback.fst fY t ≫ fY) =
      pullback.fst fY (pullback.fst (j ≫ π) t ≫ (j ≫ π)) ≫ (fY ≫ f) := by
    rw [← commuteComparisonHom_comp_structureMorphism C f fY (j ≫ π) t]
    simp only [openStr, Category.assoc]
    rw [← Category.assoc (pullback.fst fY t) fY f, ← pullback.condition_assoc]
    simp
  have hvY : openBaseChange π j t ≫ ((pullback.fst π t ≫ π) ≫ f) =
      (pullback.fst (j ≫ π) t ≫ (j ≫ π)) ≫ f := by
    rw [← Category.assoc, hm₂]
  have hqY : pullback.snd (j ≫ π) t ≫ (t ≫ f) = (pullback.fst (j ≫ π) t ≫ (j ≫ π)) ≫ f := by
    rw [← Category.assoc, hm₁]
  -- the restriction of `β` and the flat pullback of `α`
  have e4 : chowGroupRestrict C ((pullback.fst π t ≫ π) ≫ f)
      ((pullback.fst (j ≫ π) t ≫ (j ≫ π)) ≫ f) (openBaseChange π j t) hvY (k + 1)
      (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β) ≍
      flatPullbackChow C ((pullback.fst (j ≫ π) t ≫ (j ≫ π)) ≫ f) (t ≫ f)
        (pullback.snd (j ≫ π) t) hqY 1 hr k (flatPullbackDescends C _ _ _ _ _ _ _) α := by
    refine (chowGroupRestrict_heq_congr C (openBaseChange π j t) hvY
      (openBaseChange_comp_testStr C f π j t) (Category.assoc _ _ _)
      hqY.symm (k + 1) (chowGroupCongr_heq C _ _ β)).trans
      ((heq_of_eq hβ).trans ?_)
    exact Stacks.Chow.flatPullbackChow_heq_congr_base C hqY rfl rfl rfl hqY rfl hr hr rfl _ _ α α
      HEq.rfl
  have e5 := (heq_cap_of_heq C G (fY ≫ f) f fY rfl p c
    (pullback.fst (j ≫ π) t ≫ (j ≫ π)) (by push_cast; ring) e4)
  have e6 := BivariantClass.flat_naturality_of_eq C G (fY ≫ f) f fY rfl p c t
    (pullback.snd (j ≫ π) t) (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₁ 1 hr
    (baseChangeMapOfEq fY t (pullback.snd (j ≫ π) t) (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₁)
    hh' (baseChangeMapOfEq_fst _ _ _ _ _) k hqY hr' (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) α
  have e3 := BivariantClass.cap_chowGroupRestrict C G (fY ≫ f) f fY rfl p c
    (pullback.fst π t ≫ π) (openBaseChange π j t) (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₂
    (baseChangeMapOfEq fY (pullback.fst π t ≫ π) (openBaseChange π j t)
      (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₂) hι' (baseChangeMapOfEq_fst _ _ _ _ _) (k + 1) hvY
    (baseChangeMapOfEq_comp_structure _ _ _ _ _ _)
    (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β)
  have e2 := chowGroupRestrict_properChowPushforward C
    (pullback.fst fY (pullback.fst π t ≫ π) ≫ (fY ≫ f)) (testStr C f π (pullback.fst fY t ≫ fY))
    (pullback.fst fY (pullback.fst (j ≫ π) t ≫ (j ≫ π)) ≫ (fY ≫ f))
    (openStr C f π j (pullback.fst fY t ≫ fY)) (commuteComparisonHom fY π t)
    (commuteComparisonHom_comp_structureMorphism C f fY π t)
    (baseChangeMapOfEq fY (pullback.fst π t ≫ π) (openBaseChange π j t)
      (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₂) (baseChangeMapOfEq_comp_structure _ _ _ _ _ _)
    (openBaseChange π j (pullback.fst fY t ≫ fY)) (openBaseChange_comp_testStr C f π j _)
    (commuteComparisonHom fY (j ≫ π) t) hΨU hsq (k + 1 - p)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (c.cap (pullback.fst π t ≫ π) (k + 1) (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β))
  have e7 := flatPullbackChow_chowPushforwardOfIso C (pullback.fst fY t ≫ (fY ≫ f))
    (pullback.fst fY (pullback.fst (j ≫ π) t ≫ (j ≫ π)) ≫ (fY ≫ f))
    ((pullback.fst fY t ≫ fY) ≫ f) (openStr C f π j (pullback.fst fY t ≫ fY)) (𝟙 _)
    (by rw [Category.id_comp, Category.assoc])
    (commuteComparisonHom fY (j ≫ π) t) hΨU
    (baseChangeMapOfEq fY t (pullback.snd (j ≫ π) t) (pullback.fst (j ≫ π) t ≫ (j ≫ π)) hm₁)
    (baseChangeMapOfEq_comp_structure _ _ _ _ _ _) (pullback.snd (j ≫ π) _) rfl hsq' 1 hr' hrg
    (k - p) (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (c.cap t k α)
  rw [chowPushforwardOfIso_id_eq_chowGroupCongr] at e7
  unfold IsLift
  rw [capLift, e7]
  refine eq_of_heq ((chowGroupRestrict_chowGroupDegreeEquiv_heq C _ _ _ _ _ _).trans ?_)
  refine (heq_of_eq e2).trans ?_
  rw [e3]
  exact chowPushforwardOfIso_heq_congr_base C _ _ rfl _ _ rfl rfl (by push_cast; ring) _ _
    (e5.trans e6)

end Lift

/-! ### The cap of `c` on the class at infinity -/

section Commuting

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (fY : Y ⟶ X) [LocallyOfFiniteType fY] {p : ℤ}
  (c : BivariantClass C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl p)
  {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The identification of the zero scheme with `W_∞ ×_X T` lies over `X`. -/
theorem testInfinityIso_comp_test :
    testInfinityIso C f b t ≫ (pullback.fst (modificationProjectionAtInfinity f b) t ≫
        modificationProjectionAtInfinity f b) =
      (testInfinityDivisor C f b t).subschemeι ≫
        (pullback.fst (modificationProjection f b) t ≫ modificationProjection f b) := by
  rw [← testInfinityIso_comp_modificationInfinityBaseChange C f b t, Category.assoc]
  congr 1
  rw [← Category.assoc (modificationInfinityBaseChange f b t),
    modificationInfinityBaseChange_comp_fst, Category.assoc]

/-- The test morphism `W ×_X T ⟶ X`. -/
abbrev wTest : pullback (modificationProjection f b) t ⟶ X :=
  pullback.fst (modificationProjection f b) t ≫ modificationProjection f b

/-- The test morphism `W_∞ ×_X T ⟶ X`. -/
abbrev wInfTest : pullback (modificationProjectionAtInfinity f b) t ⟶ X :=
  pullback.fst (modificationProjectionAtInfinity f b) t ≫ modificationProjectionAtInfinity f b

/-- The invertible module of the divisor at infinity, pulled back to `Y ×_X (W ×_X T)`. -/
abbrev capModule : (pullback fY (wTest C f b t)).Modules :=
  (Scheme.Modules.pullback (pullback.snd fY (wTest C f b t))).obj
    (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))

/-- The section of the divisor at infinity, pulled back to `Y ×_X (W ×_X T)`. -/
abbrev capSection : Γ(capModule C f b fY t, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (pullback.snd fY (wTest C f b t))
    (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
    (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) t))

/-- The divisor at infinity of `Y ×_X (W ×_X T)`. -/
abbrev capDivisor : (pullback fY (wTest C f b t)).IdealSheafData :=
  Stacks.Divisors.zeroScheme (pullback fY (wTest C f b t)) (capModule C f b fY t)
    (capSection C f b fY t)

/-- The identification `(Y ×_X W_T)_∞ ≅ Y ×_X (W_∞ ×_X T)` of the divisor at infinity of
`Y ×_X (W ×_X T)` with the base change of `W_∞ ×_X T`. -/
def capInfinityIso :
    (capDivisor C f b fY t).subscheme ⟶ pullback fY (wInfTest C f b t) :=
  (bivariantDivisorBaseChangeIso fY (wTest C f b t)
      (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
      (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
        (pullback.fst (modificationProjection f b) t))).inv ≫
    (testBaseChangeIso fY (wInfTest C f b t) (testInfinityIso C f b t)
      ((testInfinityDivisor C f b t).subschemeι ≫ wTest C f b t)
      (testInfinityIso_comp_test C f b t)).hom

/-- The morphism `capInfinityIso` is an isomorphism. -/
instance : IsIso (capInfinityIso C f b fY t) := by
  unfold capInfinityIso
  infer_instance

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- `capInfinityIso` is a morphism over the base. -/
theorem capInfinityIso_comp_structure :
    capInfinityIso C f b fY t ≫ (pullback.fst fY (wInfTest C f b t) ≫ (fY ≫ f)) =
      (capDivisor C f b fY t).subschemeι ≫ pullback.fst fY (wTest C f b t) ≫ (fY ≫ f) := by
  rw [capInfinityIso, Category.assoc, ← Category.assoc (testBaseChangeIso _ _ _ _ _).hom,
    testBaseChangeIso_hom_fst, Iso.inv_comp_eq]
  exact (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism (fY ≫ f) fY _ _ _).symm

/-- **The cap of `c` on `i_∞^* β`.** For `β ∈ A_{k+1}(W ×_X T)`, capping the Gysin image
`i_∞^* β ∈ A_k(W_∞ ×_X T)` with `c` is the Gysin map of the divisor at infinity of
`Y ×_X (W ×_X T)` applied to `c ∩ β`: condition (3) of Stacks 0B76 for `c`. -/
theorem cap_testInfinity (k : ℤ)
    (β : chowGroup C (testStr C f (modificationProjection f b) t) (k + 1)) :
    c.cap (wInfTest C f b t) k
      (chowGroupCongr C (Category.assoc _ _ _).symm k
        (chowPushforwardOfIso C ((testInfinityDivisor C f b t).subschemeι ≫
            testStr C f (modificationProjection f b) t)
          (pullback.fst (modificationProjectionAtInfinity f b) t ≫
            (modificationProjectionAtInfinity f b ≫ f)) (testInfinityIso C f b t)
          (testInfinityIso_comp_structure C f b t) k
          ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) t)
            (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
            (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
              (pullback.fst (modificationProjection f b) t)) k β))) =
      chowPushforwardOfIso C ((capDivisor C f b fY t).subschemeι ≫
          pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
        (pullback.fst fY (wInfTest C f b t) ≫ (fY ≫ f))
        (capInfinityIso C f b fY t) (capInfinityIso_comp_structure C f b fY t) (k - p)
        ((gysinSystemOfInvertible C).onChow (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
          (capModule C f b fY t) (capSection C f b fY t) (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))) (by omega :
              (k + 1) - p = (k - p) + 1))
            (c.cap (wTest C f b t) (k + 1)
              (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β))))
    := by
  have hmb : testInfinityIso C f b t ≫ (wInfTest C f b t ≫ f) =
      (testInfinityDivisor C f b t).subschemeι ≫ testStr C f (modificationProjection f b) t := by
    rw [← testInfinityIso_comp_structure C f b t]
    simp only [Category.assoc]
  have hqm : (testInfinityDivisor C f b t).subschemeι ≫ testStr C f (modificationProjection f b) t
      = ((testInfinityDivisor C f b t).subschemeι ≫ wTest C f b t) ≫ f := by
    simp only [testStr, Category.assoc]
  set y := (gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) t)
    (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
    (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) t)) k β with hy
  have hcap := BivariantClass.cap_chowPushforwardOfIso c (wInfTest C f b t)
    (testInfinityIso C f b t) ((testInfinityDivisor C f b t).subschemeι ≫ wTest C f b t)
    (testInfinityIso_comp_test C f b t) _ hqm k hmb y (chowGroupCongr C hqm k y) rfl
  rw [chowGroupCongr_chowPushforwardOfIso_target C _ (Category.assoc _ _ _).symm _ _ hmb k, hcap]
  have hz : chowGroupCongr C hqm k y = (gysinSystemOfInvertible C).onChow (wTest C f b t ≫ f)
      (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
      (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
        (pullback.fst (modificationProjection f b) t)) k
      (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β) :=
    eq_of_heq ((chowGroupCongr_heq C hqm k y).trans
      (onChow_heq_congr C _ (Category.assoc _ _ _).symm
      _ _ k (chowGroupCongr_heq C _ _ β).symm))
  have hgn := c.gysin_naturality (wTest C f b t)
    (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
    (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) t)) k
    (bivariantDivisorBaseChangeIso fY _ _ _) (bivariantDivisorBaseChangeIso_hom_subschemeι fY _ _ _)
    (bivariantDivisorBaseChangeIso_hom_comp_structureMorphism (fY ≫ f) fY _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β)
  rw [properChowPushforward_eq_chowPushforwardOfIso] at hgn
  rw [hz]
  refine Eq.trans ?_ (congrArg (chowPushforwardOfIso C _ _ (capInfinityIso C f b fY t)
    (capInfinityIso_comp_structure C f b fY t) (k - p)) hgn)
  rw [chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  rw [capInfinityIso, Iso.hom_inv_id_assoc]

/-! ### The comparison of the two divisors at infinity -/

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- Read in `W`, the identification of the zero scheme with `W_∞ ×_X T` is the inclusion. -/
@[reassoc]
theorem testInfinityIso_fst_incl :
    testInfinityIso C f b t ≫ pullback.fst (modificationProjectionAtInfinity f b) t ≫
        modificationInclusionAtInfinity f b =
      (testInfinityDivisor C f b t).subschemeι ≫ pullback.fst (modificationProjection f b) t := by
  rw [← testInfinityIso_comp_modificationInfinityBaseChange C f b t, Category.assoc,
    modificationInfinityBaseChange_comp_fst]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The identification of the zero scheme with `W_∞ ×_X T` lies over `T`. -/
@[reassoc]
theorem testInfinityIso_snd :
    testInfinityIso C f b t ≫ pullback.snd (modificationProjectionAtInfinity f b) t =
      (testInfinityDivisor C f b t).subschemeι ≫ pullback.snd (modificationProjection f b) t := by
  rw [← testInfinityIso_comp_modificationInfinityBaseChange C f b t, Category.assoc,
    modificationInfinityBaseChange_comp_snd]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- Two morphisms into `Y ×_X (W_∞ ×_X T)` agree when their points of `Y`, `W` and `T` do. -/
theorem capTarget_hom_ext {Z : Scheme.{u}} {a a' : Z ⟶ pullback fY (wInfTest C f b t)}
    (hY : a ≫ pullback.fst fY (wInfTest C f b t) = a' ≫ pullback.fst fY (wInfTest C f b t))
    (hW : a ≫ pullback.snd fY (wInfTest C f b t) ≫
        pullback.fst (modificationProjectionAtInfinity f b) t ≫
          modificationInclusionAtInfinity f b =
      a' ≫ pullback.snd fY (wInfTest C f b t) ≫
        pullback.fst (modificationProjectionAtInfinity f b) t ≫
          modificationInclusionAtInfinity f b)
    (hT : a ≫ pullback.snd fY (wInfTest C f b t) ≫
        pullback.snd (modificationProjectionAtInfinity f b) t =
      a' ≫ pullback.snd fY (wInfTest C f b t) ≫
        pullback.snd (modificationProjectionAtInfinity f b) t) : a = a' := by
  refine pullback.hom_ext hY (pullback.hom_ext ?_ ?_)
  · rw [← cancel_mono (modificationInclusionAtInfinity f b)]
    simpa only [Category.assoc] using hW
  · simpa only [Category.assoc] using hT

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The inverse of the identification of Stacks 0B6Y, followed by the base change of the divisor,
is the inclusion of the zero scheme of the pulled-back section. -/
theorem bivariantDivisorBaseChangeIso_inv_comp {Z T' : Scheme.{u}} (g : T' ⟶ X) (M : T'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T'.sheaf.obj T'.ringCatSheaf.property M]
    (σ : Γ(M, ⊤)) (fZ : Z ⟶ X) :
    (bivariantDivisorBaseChangeIso fZ g M σ).inv ≫
        bivariantBaseChangeMap fZ g (Stacks.Divisors.zeroScheme T' M σ).subschemeι =
      (Stacks.Divisors.zeroScheme (pullback fZ g)
        ((Scheme.Modules.pullback (pullback.snd fZ g)).obj M)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd fZ g) M σ)).subschemeι := by
  rw [Iso.inv_comp_eq, bivariantDivisorBaseChangeIso_hom_subschemeι]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The point of `Y` of the identification `capInfinityIso`. -/
theorem capInfinityIso_fst :
    capInfinityIso C f b fY t ≫ pullback.fst fY (wInfTest C f b t) =
      (capDivisor C f b fY t).subschemeι ≫ pullback.fst fY (wTest C f b t) := by
  rw [capInfinityIso, Category.assoc, testBaseChangeIso_hom_fst,
    ← bivariantDivisorBaseChangeIso_inv_comp (wTest C f b t) _ _ fY, Category.assoc]
  simp [bivariantBaseChangeMap]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The point of `W` of the identification `capInfinityIso`. -/
theorem capInfinityIso_snd_fst :
    capInfinityIso C f b fY t ≫ pullback.snd fY (wInfTest C f b t) ≫
        pullback.fst (modificationProjectionAtInfinity f b) t ≫
          modificationInclusionAtInfinity f b =
      (capDivisor C f b fY t).subschemeι ≫ pullback.snd fY (wTest C f b t) ≫
        pullback.fst (modificationProjection f b) t := by
  rw [capInfinityIso, Category.assoc, testBaseChangeIso_hom_snd_assoc, testInfinityIso_fst_incl,
    ← bivariantDivisorBaseChangeIso_inv_comp (wTest C f b t) _ _ fY, Category.assoc]
  simp [bivariantBaseChangeMap]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The point of `T` of the identification `capInfinityIso`. -/
theorem capInfinityIso_snd_snd :
    capInfinityIso C f b fY t ≫ pullback.snd fY (wInfTest C f b t) ≫
        pullback.snd (modificationProjectionAtInfinity f b) t =
      (capDivisor C f b fY t).subschemeι ≫ pullback.snd fY (wTest C f b t) ≫
        pullback.snd (modificationProjection f b) t := by
  rw [capInfinityIso, Category.assoc, testBaseChangeIso_hom_snd_assoc, testInfinityIso_snd,
    ← bivariantDivisorBaseChangeIso_inv_comp (wTest C f b t) _ _ fY, Category.assoc]
  simp [bivariantBaseChangeMap]

/-- The test morphism `Y ×_X T ⟶ X`. -/
abbrev yTest : pullback fY t ⟶ X := pullback.fst fY t ≫ fY

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The divisor at infinity of `Y ×_X (W ×_X T)` is the pullback of the divisor at infinity of
`W ×_X (Y ×_X T)` along the comparison isomorphism. -/
theorem capDivisor_eq :
    capDivisor C f b fY t =
      pullbackZeroScheme (commuteComparisonHom fY (modificationProjection f b) t)
      (gysinTripleModule (infinityModule f b)
        (pullback.fst (modificationProjection f b) (yTest fY t)))
      (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
        (pullback.fst (modificationProjection f b) (yTest fY t))) := by
  rw [capDivisor, Stacks.Divisors.zeroScheme_pullback_comp
      (pullback.snd fY (wTest C f b t)) (pullback.fst (modificationProjection f b) t)
      (infinityModule f b) (infinitySectionOnW f b), pullbackZeroScheme,
    Stacks.Divisors.zeroScheme_pullback_comp
      (commuteComparisonHom fY (modificationProjection f b) t)
      (pullback.fst (modificationProjection f b) (yTest fY t)) (infinityModule f b)
      (infinitySectionOnW f b), commuteComparisonHom_fst]

/-- The morphism from the divisor at infinity of `Y ×_X (W ×_X T)` to that of
`W ×_X (Y ×_X T)` over the comparison isomorphism. -/
def capDivisorHom : (capDivisor C f b fY t).subscheme ⟶
    (testInfinityDivisor C f b (yTest fY t)).subscheme :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme (capDivisor_eq C f b fY t)) ≫
    zeroSchemePullbackHom (commuteComparisonHom fY (modificationProjection f b) t) _ _

/-- The morphism `capDivisorHom` is proper. -/
instance : IsProper (capDivisorHom C f b fY t) := by
  unfold capDivisorHom
  infer_instance

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- `capDivisorHom` lies over the comparison isomorphism. -/
@[reassoc]
theorem capDivisorHom_subschemeι :
    capDivisorHom C f b fY t ≫ (testInfinityDivisor C f b (yTest fY t)).subschemeι =
      (capDivisor C f b fY t).subschemeι ≫ commuteComparisonHom fY (modificationProjection f b) t
    := by
  rw [capDivisorHom, Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
    subschemeι_eqToHom (capDivisor_eq C f b fY t)]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType fY] [LocallyOfFiniteType t] in
/-- The two identifications of the divisor at infinity of `Y ×_X (W ×_X T)` with
`Y ×_X (W_∞ ×_X T)` agree. -/
theorem capDivisorHom_comp_eq :
    capDivisorHom C f b fY t ≫ testInfinityIso C f b (yTest fY t) ≫
        commuteComparisonHom (modificationProjectionAtInfinity f b) fY t =
      capInfinityIso C f b fY t := by
  refine capTarget_hom_ext C f b fY t ?_ ?_ ?_
  · rw [capInfinityIso_fst]
    simp only [Category.assoc, commuteComparisonHom_fst, testInfinityIso_snd_assoc,
      capDivisorHom_subschemeι_assoc, commuteComparisonHom_snd_fst]
  · rw [capInfinityIso_snd_fst]
    simp only [Category.assoc, commuteComparisonHom_snd_fst_assoc, testInfinityIso_fst_incl,
      capDivisorHom_subschemeι_assoc, commuteComparisonHom_fst]
  · rw [capInfinityIso_snd_snd]
    simp only [Category.assoc, testInfinityIso_snd_assoc, capDivisorHom_subschemeι_assoc,
      commuteComparisonHom_snd_snd]

/-- **The Gysin map at infinity on `W ×_X (Y ×_X T)`, read on `Y ×_X (W ×_X T)`.** The Gysin
map of the divisor at infinity commutes with pushforward along the comparison isomorphism
`Y ×_X (W ×_X T) ≅ W ×_X (Y ×_X T)` (Stacks 02TA), the divisor at infinity pulling back to the
divisor at infinity. -/
theorem gysin_comparison (k : ℤ)
    (z : chowGroup C (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f)) (k - p + 1)) :
    chowPushforwardOfIso C (pullback.fst (modificationProjectionAtInfinity f b) (yTest fY t) ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (pullback.fst fY (wInfTest C f b t) ≫ (fY ≫ f))
        (commuteComparisonHom (modificationProjectionAtInfinity f b) fY t)
        (commuteComparisonHom_comp_structureMorphism C f _ fY t) (k - p)
      (chowPushforwardOfIso C ((testInfinityDivisor C f b (yTest fY t)).subschemeι ≫
          testStr C f (modificationProjection f b) (yTest fY t))
        (pullback.fst (modificationProjectionAtInfinity f b) (yTest fY t) ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (testInfinityIso C f b (yTest fY t)) (testInfinityIso_comp_structure C f b _) (k - p)
        ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) (yTest fY t))
          (gysinTripleModule (infinityModule f b)
            (pullback.fst (modificationProjection f b) (yTest fY t)))
          (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
            (pullback.fst (modificationProjection f b) (yTest fY t))) (k - p)
          (chowPushforwardOfIso C (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
            (testStr C f (modificationProjection f b) (yTest fY t))
            (commuteComparisonHom fY (modificationProjection f b) t)
            (commuteComparisonHom_comp_structureMorphism C f fY _ t) (k - p + 1) z))) =
      chowPushforwardOfIso C ((capDivisor C f b fY t).subschemeι ≫
          pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
        (pullback.fst fY (wInfTest C f b t) ≫ (fY ≫ f)) (capInfinityIso C f b fY t)
        (capInfinityIso_comp_structure C f b fY t) (k - p)
        ((gysinSystemOfInvertible C).onChow (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
          (capModule C f b fY t) (capSection C f b fY t) (k - p) z) := by
  set o := (gysinSystemOfInvertible C).onChow (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
    (capModule C f b fY t) (capSection C f b fY t) (k - p) z
  have hnat := gysinSystemOfInvertible_isNaturalUnderProperPushforward C
    (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
    (testStr C f (modificationProjection f b) (yTest fY t))
    (commuteComparisonHom fY (modificationProjection f b) t)
    (commuteComparisonHom_comp_structureMorphism C f fY _ t)
    (gysinTripleModule (infinityModule f b)
      (pullback.fst (modificationProjection f b) (yTest fY t)))
    (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) (yTest fY t))) (k - p) _
    (zeroSchemePullbackHom_subschemeι _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) z
  have hx := (onChow_pullbackComp_heq C (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
      (infinityModule f b) (infinitySectionOnW f b) (k - p) z
      (pullback.snd fY (wTest C f b t)) (pullback.fst (modificationProjection f b) t)).trans
    ((onChow_pullback_heq C (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
      (infinityModule f b) (infinitySectionOnW f b) (k - p) z
      (commuteComparisonHom_fst fY (modificationProjection f b) t).symm).trans
    (onChow_pullbackComp_heq C (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f))
      (infinityModule f b) (infinitySectionOnW f b) (k - p) z
      (commuteComparisonHom fY (modificationProjection f b) t)
      (pullback.fst (modificationProjection f b) (yTest fY t))).symm)
  have hconv := chowPushforwardOfIso_eqToHom_eq_of_heq C
    (pullback.fst fY (wTest C f b t) ≫ (fY ≫ f)) (k - p) (capDivisor_eq C f b fY t)
    (by rw [← Category.assoc, subschemeι_eqToHom (capDivisor_eq C f b fY t)]) hx
  have hcd : capDivisorHom C f b fY t ≫ ((testInfinityDivisor C f b (yTest fY t)).subschemeι ≫
      testStr C f (modificationProjection f b) (yTest fY t)) =
      (capDivisor C f b fY t).subschemeι ≫ pullback.fst fY (wTest C f b t) ≫ (fY ≫ f) := by
    rw [← Category.assoc, capDivisorHom_subschemeι, Category.assoc,
      commuteComparisonHom_comp_structureMorphism]
  have h2 := properChowPushforward_comp_apply C _ _ _
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme (capDivisor_eq C f b fY t)))
    (zeroSchemePullbackHom (commuteComparisonHom fY (modificationProjection f b) t) _ _)
    (capDivisorHom C f b fY t) rfl
    (by rw [← Category.assoc, subschemeι_eqToHom (capDivisor_eq C f b fY t)])
    (zeroSchemeSquare_comp_structureMorphism C _ _ _
      (commuteComparisonHom_comp_structureMorphism C f fY _ t) _ _ _
      (zeroSchemePullbackHom_subschemeι _ _ _)) hcd (k - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) o
  have h3 := properChowPushforward_comp₃_eq C (capDivisorHom C f b fY t)
    (testInfinityIso C f b (yTest fY t))
    (commuteComparisonHom (modificationProjectionAtInfinity f b) fY t)
    (capInfinityIso C f b fY t) (capDivisorHom_comp_eq C f b fY t) hcd
    (testInfinityIso_comp_structure C f b _)
    (commuteComparisonHom_comp_structureMorphism C f _ fY t)
    (capInfinityIso_comp_structure C f b fY t) (k - p)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) o
  have hconv' : properChowPushforward C _ _
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme (capDivisor_eq C f b fY t))) _ (k - p)
      (properPushforwardDescends C _ _ _ _ _) o = _ := hconv
  refine Eq.trans ?_ h3
  rw [h2, hconv', ← hnat]
  rfl

end Commuting

end GysinAtInfinity

/-! ### Commuting classes have equal composites -/

section CompositeOfCommuting

variable {C : ChowSituation.{u}} {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X) [LocallyOfFiniteType f₂] {p₁ p₂ : ℤ}

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂] in
/-- The symmetry `Z₂ ×_X Z₁ ≅ Z₁ ×_X Z₂` lies over `X`. -/
theorem pullbackSymmetry_hom_comp_snd_comp :
    (pullbackSymmetry f₂ f₁).hom ≫ (pullback.snd f₁ f₂ ≫ f₂) = pullback.snd f₂ f₁ ≫ f₁ := by
  rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition]

/-- **Stacks 0FA2, read on the bivariant classes of Stacks 0B76.** If `c₁ ∈ A^{p₁}(Z₁ ⟶ X)` and
`c₂ ∈ A^{p₂}(Z₂ ⟶ X)` commute, then `res(c₁) ∘ c₂ = res(c₂) ∘ c₁` in
`A^{p₁+p₂}(Z₁ ×_X Z₂ ⟶ X)`, the second composite being read on `Z₁ ×_X Z₂` through the
symmetry `Z₂ ×_X Z₁ ≅ Z₁ ×_X Z₂` and in degree `p₁ + p₂ = p₂ + p₁`. -/
theorem BivariantChowClass.restrict_comp_eq_of_bivariantCommute
    (c₁ : BivariantChowClass C (f₁ ≫ sX) sX f₁ rfl p₁)
    (c₂ : BivariantChowClass C (f₂ ≫ sX) sX f₂ rfl p₂)
    (h : BivariantCommute C (gysinSystemOfInvertible C) sX f₁ f₂ p₁ p₂
      (BivariantChowClass.equivBivariantClass c₁) (BivariantChowClass.equivBivariantClass c₂)) :
    (c₁.restrict f₂ rfl).comp c₂ =
      (((c₂.restrict f₁ rfl).comp c₁).degreeCongr (add_comm p₂ p₁)).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl f₂ rfl) rfl)
        (pullbackSymmetry f₂ f₁) (pullbackSymmetry_hom_comp_snd_comp f₁ f₂) := by
  ext T t _ k α
  have H := h t k α
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply] at H
  rw [BivariantChowClass.comp_cap, BivariantChowClass.restrict_cap,
    BivariantChowClass.transport_cap]
  set I₁ := c₁.cap (pullback.fst f₂ t ≫ f₂) (k - p₂)
    (chowGroupCongr C (Category.assoc _ _ _).symm (k - p₂) (c₂.cap t k α))
  set I₂ := c₂.cap (pullback.fst f₁ t ≫ f₁) (k - p₁)
    (chowGroupCongr C (Category.assoc _ _ _).symm (k - p₁) (c₁.cap t k α))
  have hI : I₂ ≍ chowPushforwardOfIso C _ _ (commuteComparisonHom f₁ f₂ t)
      (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) (k - p₂ - p₁) I₁ :=
    (chowGroupDegreeEquiv_heq C _ _ _).symm.trans (heq_of_eq H.symm)
  have hv1 : (pullbackLeftPullbackSndIso f₂ f₁ (pullback.fst f₁ t)).inv ≫
      (pullback.fst (pullback.snd f₂ f₁) (pullback.fst f₁ t) ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX))) =
      pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX) := by simp
  have e1 := chowPushforwardOfIso_heq_comp C (commuteComparisonHom f₁ f₂ t)
    (pullbackLeftPullbackSndIso f₂ f₁ (pullback.fst f₁ t)).inv
    (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) hv1 rfl (by ring) I₁ I₂ hI
  have e2 := chowPushforwardOfIso_heq_comp C
    (commuteComparisonHom f₁ f₂ t ≫ (pullbackLeftPullbackSndIso f₂ f₁ (pullback.fst f₁ t)).inv)
    (pullbackRightPullbackFstIso f₁ t (pullback.snd f₂ f₁)).hom
    (by rw [Category.assoc, hv1, commuteComparisonHom_comp_structureMorphism])
    (pullbackRightPullbackFstIso_hom_comp_fst_comp (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)) _ _ _) rfl
    (by ring) I₁ _ e1
  have e3 : ((c₂.restrict f₁ rfl).comp c₁).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
        (pullback.fst (pullback.snd f₂ f₁ ≫ f₁) t ≫ (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX)))
        ((commuteComparisonHom f₁ f₂ t ≫
          (pullbackLeftPullbackSndIso f₂ f₁ (pullback.fst f₁ t)).inv) ≫
          (pullbackRightPullbackFstIso f₁ t (pullback.snd f₂ f₁)).hom)
        (by rw [Category.assoc, pullbackRightPullbackFstIso_hom_comp_fst_comp, Category.assoc, hv1,
          commuteComparisonHom_comp_structureMorphism]) (k - p₂ - p₁) I₁ := by
    rw [BivariantChowClass.comp_cap, BivariantChowClass.restrict_cap]
    exact (chowGroupDegreeEquiv_heq C _ _ _).trans e2
  have e5 := chowPushforwardOfIso_heq_comp C
    ((commuteComparisonHom f₁ f₂ t ≫
      (pullbackLeftPullbackSndIso f₂ f₁ (pullback.fst f₁ t)).inv) ≫
      (pullbackRightPullbackFstIso f₁ t (pullback.snd f₂ f₁)).hom)
    (transportPullbackIso (pullback.snd f₂ f₁ ≫ f₁) (pullback.snd f₁ f₂ ≫ f₂)
      (pullbackSymmetry f₂ f₁) (pullbackSymmetry_hom_comp_snd_comp f₁ f₂) t).hom
    (by rw [Category.assoc, pullbackRightPullbackFstIso_hom_comp_fst_comp, Category.assoc, hv1,
          commuteComparisonHom_comp_structureMorphism])
    (transportPullbackIso_hom_comp_base C (pullback.fst f₂ f₁ ≫ (f₂ ≫ sX))
      (pullback.fst f₁ f₂ ≫ (f₁ ≫ sX)) sX (pullback.snd f₂ f₁ ≫ f₁)
      (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl f₁ rfl) rfl)
      (pullback.snd f₁ f₂ ≫ f₂)
      (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl f₂ rfl) rfl)
      (pullbackSymmetry f₂ f₁) (pullbackSymmetry_hom_comp_snd_comp f₁ f₂) t) rfl (by ring) I₁ _
    ((((c₂.restrict f₁ rfl).comp c₁).degreeCongr_cap (add_comm p₂ p₁) t k α).trans e3)
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans (HEq.trans ?_ e5.symm))
  rw [chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;> simp [transportPullbackIso]

end CompositeOfCommuting

namespace GysinAtInfinity

/-! ### Stacks 0FAS -/

section Statement

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (fY : Y ⟶ X) [LocallyOfFiniteType fY] (p : ℤ)

/-- **Stacks 0FAS, in the form of Remark 0FA2.** In the situation of Stacks 0F9J, let
`fY : Y ⟶ X` be locally of finite type and `c ∈ A^p(Y ⟶ X)`. Then the class at infinity
`C ∈ A⁰(W_∞ ⟶ X)` and `c` commute: `C ∩ (c ∩ α) = c ∩ (C ∩ α)` for `α ∈ CH_k(T)` and every
`T ⟶ X` locally of finite type, the two sides compared by the canonical isomorphism
`W_∞ ×_X (Y ×_X T) ≅ Y ×_X (W_∞ ×_X T)`.

Choose a lift `β ∈ A_{k+1}(W ×_X T)` of `α`. Then `c ∩ β` is a lift of `c ∩ α`
(`Stacks.Chow.GysinAtInfinity.isLift_capLift`), so `C ∩ (c ∩ α) = i_∞^*(c ∩ β)`, while
`c ∩ (C ∩ α) = c ∩ i_∞^* β = i_∞^*(c ∩ β)` by condition (3) of Stacks 0B76 for `c`. -/
theorem gysinAtInfinityClass_bivariantCommute
    (c : BivariantChowClass C (fY ≫ f) f fY rfl p) :
    BivariantCommute C (gysinSystemOfInvertible C) f (modificationProjectionAtInfinity f b) fY 0 p
      (gysinAtInfinityClass C f b hA) (BivariantChowClass.equivBivariantClass c) := by
  have := hA
  generalize BivariantChowClass.equivBivariantClass c = c
  intro T t _ k α
  obtain ⟨β, hβ⟩ := exists_isLift C f (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) t k α
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply,
    gysinAtInfinityClass_cap_eq_of_isLift C f b hA (yTest fY t)
      (isLift_capLift C f (modificationProjection f b) (chartInclusion f b)
        (relativeDimension_chartInclusion_comp f b) fY c t k hβ),
    gysinAtInfinityClass_cap_eq_of_isLift C f b hA t hβ, capLift,
    chowGroupDegreeEquiv_chowPushforwardOfIso C _ _
      (commuteComparisonHom fY (modificationProjection f b) t)]
  set X := c.cap (wTest C f b t) (k + 1) (chowGroupCongr C (Category.assoc _ _ _).symm (k + 1) β)
  have hL := gysin_comparison C f b fY t k
    (chowGroupDegreeEquiv C _ (by ring : k + 1 - p = k - p + 1) X)
  have hR := cap_testInfinity C f b fY c t k β
  rw [eqMp_chowGroup C _ (by ring : k + 1 - p = k - p + 1)] at hR
  refine eq_of_heq (HEq.trans ?_ ((heq_of_eq (hL.trans hR.symm)).trans ?_))
  · refine chowPushforwardOfIso_heq_of_heq C _ _ (sub_zero _) ?_
    exact chowGroupDegreeEquiv_heq C _ _ _
  · refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
    refine heq_cap_of_heq C (gysinSystemOfInvertible C) (fY ≫ f) f fY rfl p c
      (wInfTest C f b t) (sub_zero k).symm ?_
    exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupDegreeEquiv_heq C _ _ _).symm.trans
      (chowGroupCongr_heq C _ _ _).symm)

/-- **Stacks 0FAS.** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over
`S`, let `b : W ⟶ 𝐏¹_X` be a proper morphism which is an isomorphism over `𝐀¹_X`, and let
`C ∈ A⁰(W_∞ ⟶ X)` be the class of Stacks 0F9J. Let `fY : Y ⟶ X` be a morphism locally of finite
type and `c ∈ A^p(Y ⟶ X)`. Then

  `C ∘ c = c ∘ C`   in   `A^p(W_∞ ×_X Y ⟶ X)`.

Here, as in Remark 0FA2, `C ∘ c = res(C) ∘ c` with `res(C) ∈ A⁰(W_∞ ×_X Y ⟶ Y)` the restriction
of `C` along `fY` (Stacks 0F9Z), and `c ∘ C = res(c) ∘ C` with `res(c) ∈ A^p(Y ×_X W_∞ ⟶ W_∞)` the
restriction of `c` along `W_∞ ⟶ X`; the second composite lives on `Y ×_X W_∞` and in degree
`p + 0`, and is read on `W_∞ ×_X Y` through the canonical isomorphism and in degree `0 + p`. The
bivariant classes are those of Stacks 0B76, `Stacks.Chow.BivariantChowClass`, and `C` is
`Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass` read through the bridge
`Stacks.Chow.BivariantChowClass.equivBivariantClass`. -/
@[stacks 0FAS]
theorem gysinAtInfinityClass_comp_comm {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    (hY : fY ≫ f = sY) (c : BivariantChowClass C sY f fY hY p) :
    ((BivariantChowClass.equivBivariantClass.symm (gysinAtInfinityClass C f b hA)).restrict fY
        hY).comp c =
      (((c.restrict (modificationProjectionAtInfinity f b) rfl).comp
          (BivariantChowClass.equivBivariantClass.symm (gysinAtInfinityClass C f b hA))).degreeCongr
        (add_comm p 0)).transport
        (comp_comp_structureMorphism_eq (BivariantChowClass.restrict_structure_eq rfl fY hY) hY)
        (pullbackSymmetry fY (modificationProjectionAtInfinity f b))
        (pullbackSymmetry_hom_comp_snd_comp (modificationProjectionAtInfinity f b) fY) := by
  subst hY
  exact BivariantChowClass.restrict_comp_eq_of_bivariantCommute f
    (modificationProjectionAtInfinity f b) fY _ c
    (gysinAtInfinityClass_bivariantCommute C f b hA fY p c)

end Statement

end GysinAtInfinity

end Stacks.Chow

end
