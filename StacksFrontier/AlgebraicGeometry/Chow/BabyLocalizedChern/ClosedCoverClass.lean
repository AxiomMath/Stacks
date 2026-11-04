module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentExistence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRuleNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem

/-!
# The localized class of a closed cover

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `i₁ : X₁ ⟶ X`, `i₂ : X₂ ⟶ X` be closed immersions with
`X = X₁ ∪ X₂` set theoretically. Let `κ ∈ A^p(X₂)` be a Chow cohomology class whose restriction
to the scheme-theoretic intersection `X₁ ∩ X₂ = X₁ ×_X X₂` vanishes. This file constructs the
bivariant class `κ' ∈ A^p(X₂ ⟶ X)` of the proof of Stacks 0F9H: on a test scheme `g : X' ⟶ X`,
with `X'_j = X_j ×_X X'`, every `α ∈ A_k(X')` is `i'_{1,*} α₁ + i'_{2,*} α₂` (Stacks 0F94), and

  `κ' ∩ α = κ ∩ α₂ ∈ A_{k-p}(X'_2)`,

which is well defined because `α₂` is determined up to classes pushed forward from
`X'_1 ∩ X'_2`, on which `κ` vanishes. The class is characterized by

  `κ' ∩ i'_{2,*} α₂ = κ ∩ α₂`  and  `κ' ∩ i'_{1,*} α₁ = 0`

on every test scheme, and is the only bivariant class with these two properties.

## Main definitions

* `Stacks.Chow.closedCoverLocalizedCap` — the cap operation of `κ'` on a test scheme.
* `Stacks.Chow.closedCoverLocalizedClass` — the bivariant class `κ' ∈ A^p(X₂ ⟶ X)`.

## Main results

* `Stacks.Chow.closedCoverLocalizedClass_cap_pushforward_right` and
  `Stacks.Chow.closedCoverLocalizedClass_cap_pushforward_left` — the two characterizing
  identities, on every test scheme.
* `Stacks.Chow.eq_closedCoverLocalizedClass` — uniqueness: a bivariant class with the two
  properties is `κ'`.

## Implementation notes

All Chow cohomology classes are taken at the Gysin system `Stacks.Chow.gysinSystemOfInvertible`
of the first Chern class of an invertible module, which is the Gysin map of chapter 42. The
operation of `κ` on a test scheme `t : V ⟶ X₂` is `Stacks.Chow.BivariantClass.idRule`.

## References

* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The operation of a Chow cohomology class, with the test morphism left free -/

section IdRule

variable (C : ChowSituation.{u}) {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  {p : ℤ} (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p)

/-- The projection formula for the operation of `κ`, along a proper morphism `w` of test schemes
with `w ≫ t = t'`. -/
theorem idRule_chowPush {V V' : Scheme.{u}} (t : V ⟶ Z) [LocallyOfFiniteType t]
    (t' : V' ⟶ Z) [LocallyOfFiniteType t'] (w : V' ⟶ V) [IsProper w] (hw : w ≫ t = t') (k : ℤ)
    (y : chowGroup C (t' ≫ sZ) k) :
    κ.idRule C sZ (gysinSystemOfInvertible C) t k
        (chowPush C (t' ≫ sZ) (t ≫ sZ) w (by rw [← hw, Category.assoc]) k y) =
      chowPush C (t' ≫ sZ) (t ≫ sZ) w (by rw [← hw, Category.assoc]) (k - p)
        (κ.idRule C sZ (gysinSystemOfInvertible C) t' k y) := by
  subst hw
  exact κ.idRule_properNaturality C sZ (gysinSystemOfInvertible C) t w k _ _ y

/-- The commutation of the operation of `κ` with flat pullback along a flat morphism `w` of test
schemes with `w ≫ t = t'`. -/
theorem idRule_flatPullbackChow_heq {V V' : Scheme.{u}} (t : V ⟶ Z) [LocallyOfFiniteType t]
    (t' : V' ⟶ Z) [LocallyOfFiniteType t'] (w : V' ⟶ V) [LocallyOfFiniteType w] [Flat w]
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension w r) (hw : w ≫ t = t') (k : ℤ)
    (y : chowGroup C (t ≫ sZ) k) :
    κ.idRule C sZ (gysinSystemOfInvertible C) t' (k + (r : ℤ))
        (flatPullbackChow C (t' ≫ sZ) (t ≫ sZ) w (by rw [← hw, Category.assoc]) r hr k
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ w _ r hr k) y) ≍
      flatPullbackChow C (t' ≫ sZ) (t ≫ sZ) w (by rw [← hw, Category.assoc]) r hr (k - p)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ w _ r hr (k - p))
        (κ.idRule C sZ (gysinSystemOfInvertible C) t k y) := by
  subst hw
  exact κ.idRule_flatNaturality C sZ (gysinSystemOfInvertible C) t w r hr k _ _ y

/-- If the restriction of `κ` along `π : W ⟶ Z` vanishes, then `κ` operates as zero on every test
scheme `t : V ⟶ Z` factoring through `π`. -/
theorem idRule_eq_zero_of_chowCohomologyRestriction_eq_zero {W : Scheme.{u}} (π : W ⟶ Z)
    [LocallyOfFiniteType π]
    (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ π p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)
    {V : Scheme.{u}} (t : V ⟶ Z) [LocallyOfFiniteType t] (v : V ⟶ W) (hv : v ≫ π = t) (k : ℤ)
    (y : chowGroup C (t ≫ sZ) k) :
    κ.idRule C sZ (gysinSystemOfInvertible C) t k y = 0 := by
  subst hv
  have : LocallyOfFiniteType v := locallyOfFiniteType_of_comp v π
  have h := BivariantClass.idRule_chowCohomologyRestriction_heq π κ v k y y HEq.rfl
  rw [hκ] at h
  exact (eq_of_heq h).symm.trans (BivariantClass.idRule_zero C _ _ _ _ _)

/-- Transport along an equality of structure morphisms commutes with proper pushforward. -/
theorem chowGroupCongr_chowPush {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (hB : sB = sB')
    (w : A ⟶ B) [IsProper w] (hw : w ≫ sB = sA) (hw' : w ≫ sB' = sA) (k : ℤ)
    (x : chowGroup C sA k) :
    chowGroupCongr C hB k (chowPush C sA sB w hw k x) = chowPush C sA sB' w hw' k x := by
  subst hB
  rfl

/-- Transport along an equality of a structure morphism with itself is the identity. -/
theorem chowGroupCongr_self {A : Scheme.{u}} {s : A ⟶ C.S} [LocallyOfFiniteType s] (h : s = s)
    (k : ℤ) (x : chowGroup C s k) : chowGroupCongr C h k x = x :=
  rfl

/-- The projection formula for the operation of `κ`, with the structure morphism of the source
of the pushforward left free. -/
theorem idRule_chowPush_of_eq {V V' : Scheme.{u}} (t : V ⟶ Z) [LocallyOfFiniteType t]
    (t' : V' ⟶ Z) [LocallyOfFiniteType t'] (w : V' ⟶ V) [IsProper w] (hw : w ≫ t = t')
    (sV' : V' ⟶ C.S) [LocallyOfFiniteType sV'] (hs : t' ≫ sZ = sV') (hwt : w ≫ t ≫ sZ = sV')
    (k : ℤ) (y : chowGroup C sV' k) :
    κ.idRule C sZ (gysinSystemOfInvertible C) t k (chowPush C sV' (t ≫ sZ) w hwt k y) =
      chowPush C (t' ≫ sZ) (t ≫ sZ) w (by rw [← hw, Category.assoc]) (k - p)
        (κ.idRule C sZ (gysinSystemOfInvertible C) t' k (chowGroupCongr C hs.symm k y)) := by
  subst hw hs
  exact idRule_chowPush C sZ κ t (w ≫ t) w rfl k y

/-- **The Gysin identity for the operation of `κ`**, with the two structure morphisms of the zero
scheme compared by an explicit transport. -/
theorem idRule_gysin_chowGroupCongr {V : Scheme.{u}} (t : V ⟶ Z) [LocallyOfFiniteType t]
    (N : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (k : ℤ) (y : chowGroup C (t ≫ sZ) (k + 1)) :
    κ.idRule C sZ (gysinSystemOfInvertible C) ((Stacks.Divisors.zeroScheme V N s).subschemeι ≫ t)
        k (chowGroupCongr C (Category.assoc _ _ _).symm k
          ((gysinSystemOfInvertible C).onChow (t ≫ sZ) N s k y)) =
      chowGroupCongr C (Category.assoc _ _ _).symm (k - p)
        ((gysinSystemOfInvertible C).onChow (t ≫ sZ) N s (k - p)
          (Eq.mp (congrArg (chowGroup C (t ≫ sZ)) (by omega : k + 1 - p = k - p + 1))
            (κ.idRule C sZ (gysinSystemOfInvertible C) t (k + 1) y))) := by
  have h := κ.idRule_gysinNaturality C sZ t N s k y
  refine eq_of_heq ?_
  refine HEq.trans ?_ ((heq_of_eq h).trans (chowGroupCongr_heq C _ _ _).symm)
  exact heq_of_eq (congrArg (κ.idRule C sZ (gysinSystemOfInvertible C)
    ((Stacks.Divisors.zeroScheme V N s).subschemeι ≫ t) k) (eq_of_heq (chowGroupCongr_heq C _ _ _)))

end IdRule

/-! ### The cover of a test scheme -/

section Cover

variable {X X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X)

/-- On a test scheme the base changes of a set-theoretic cover by two closed subschemes cover. -/
theorem range_pullbackSnd_union_range_pullbackSnd
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {T : Scheme.{u}} (g : T ⟶ X) :
    Set.range (pullback.snd i₁ g).base ∪ Set.range (pullback.snd i₂ g).base = Set.univ := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hcover,
    Set.preimage_univ]

end Cover

/-! ### The cap operation -/

section Construction

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sX₁ : X₁ ⟶ C.S) [LocallyOfFiniteType sX₁] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂]
  (i₁ : X₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ sX = sX₁)
  (i₂ : X₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ sX = sX₂)
  (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {p : ℤ}
  (κ : chowCohomologyComponent C (gysinSystemOfInvertible C) sX₂ p)
  (hκ : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX₂ (pullback.snd i₁ i₂) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) κ = 0)

include hi₁ hcover hκ in
/-- **Well-definedness of the cap operation.** If `i'_{1,*} x + i'_{2,*} y = 0` on a test
scheme, then `κ ∩ y = 0`: by Stacks 0F94, `y` is pushed forward from `X'_1 ∩ X'_2`, and `κ`
vanishes there. -/
theorem idRule_eq_zero_of_chowPush_add_chowPush_eq_zero {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (x : chowGroup C (pullback.fst i₁ g ≫ sX₁) k)
    (y : chowGroup C (pullback.fst i₂ g ≫ sX₂) k)
    (hxy : chowPush C (pullback.fst i₁ g ≫ sX₁) (g ≫ sX) (pullback.snd i₁ g)
        (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) k x +
      chowPush C (pullback.fst i₂ g ≫ sX₂) (g ≫ sX) (pullback.snd i₂ g)
        (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) k y = 0) :
    κ.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ g) k y = 0 := by
  obtain ⟨W, wa, wb, _, hw, γ, rfl⟩ := exists_eq_neg_chowPush_of_chowPush_add_chowPush_eq_zero C
    (g ≫ sX) _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g)
    (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g)
    (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover g) k x y hxy
  rw [map_neg, neg_eq_zero]
  have hv : wa ≫ pullback.fst i₁ g ≫ i₁ = wb ≫ pullback.fst i₂ g ≫ i₂ := by
    rw [pullback.condition, pullback.condition, ← Category.assoc, hw, Category.assoc]
  refine (idRule_chowPush C sX₂ κ (pullback.fst i₂ g) (wb ≫ pullback.fst i₂ g) wb rfl k γ).trans ?_
  rw [idRule_eq_zero_of_chowCohomologyRestriction_eq_zero C sX₂ κ (pullback.snd i₁ i₂) hκ
    (wb ≫ pullback.fst i₂ g)
    (pullback.lift (wa ≫ pullback.fst i₁ g) (wb ≫ pullback.fst i₂ g)
      (by rw [Category.assoc, Category.assoc, hv]))
    (pullback.lift_snd _ _ _) k γ, map_zero]

/-- **The cap operation of the localized class** on a test scheme `g : X' ⟶ X`: the descent of
`α₂ ↦ κ ∩ α₂` along the surjection `A_k(X'_1) ⊕ A_k(X'_2) ⟶ A_k(X')` of Stacks 0F94. -/
def closedCoverLocalizedCap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sX) k →+ chowGroup C (pullback.fst i₂ g ≫ sX₂) (k - p) :=
  closedCoverDescent C (g ≫ sX) (pullback.fst i₁ g ≫ sX₁) (pullback.fst i₂ g ≫ sX₂)
    (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g)
    (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g)
    (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover g) k
    (κ.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ g) k)
    (idRule_eq_zero_of_chowPush_add_chowPush_eq_zero C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k)

/-- **The defining formula**: on `i'_{1,*} x + i'_{2,*} y` the cap operation is `κ ∩ y`. -/
theorem closedCoverLocalizedCap_apply {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (x : chowGroup C (pullback.fst i₁ g ≫ sX₁) k)
    (y : chowGroup C (pullback.fst i₂ g ≫ sX₂) k) :
    closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k
        (chowPush C (pullback.fst i₁ g ≫ sX₁) (g ≫ sX) (pullback.snd i₁ g)
            (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) k x +
          chowPush C (pullback.fst i₂ g ≫ sX₂) (g ≫ sX) (pullback.snd i₂ g)
            (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) k y) =
      κ.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ g) k y :=
  closedCoverDescent_apply C (g ≫ sX) _ _ _ _ _ _ _ k _ _ x y

/-- The cap operation kills a class pushed forward along any proper morphism to the test scheme
factoring through `X'_1`. -/
theorem closedCoverLocalizedCap_chowPush_left {T V : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (v : V ⟶ pullback i₁ g)
    [IsProper v] (hv : v ≫ pullback.fst i₁ g ≫ sX₁ = sV) (w : V ⟶ T) [IsProper w]
    (hw : v ≫ pullback.snd i₁ g = w) (hwT : w ≫ g ≫ sX = sV) (k : ℤ) (z : chowGroup C sV k) :
    closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k
      (chowPush C sV (g ≫ sX) w hwT k z) = 0 := by
  have h := closedCoverLocalizedCap_apply C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k
    (chowPush C sV _ v hv k z) 0
  rw [map_zero, add_zero, map_zero,
    chowPush_comp C _ _ _ v (pullback.snd i₁ g) w hw hv _ hwT k z] at h
  exact h

/-- The cap operation of a class pushed forward along any proper morphism to the test scheme
factoring through `X'_2` is the operation of `κ` on its pushforward to `X'_2`. -/
theorem closedCoverLocalizedCap_chowPush_right {T V : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (v : V ⟶ pullback i₂ g)
    [IsProper v] (hv : v ≫ pullback.fst i₂ g ≫ sX₂ = sV) (w : V ⟶ T) [IsProper w]
    (hw : v ≫ pullback.snd i₂ g = w) (hwT : w ≫ g ≫ sX = sV) (k : ℤ) (z : chowGroup C sV k) :
    closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k
      (chowPush C sV (g ≫ sX) w hwT k z) =
        κ.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ g) k
          (chowPush C sV _ v hv k z) := by
  have h := closedCoverLocalizedCap_apply C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k 0
    (chowPush C sV _ v hv k z)
  rw [map_zero, zero_add,
    chowPush_comp C _ _ _ v (pullback.snd i₂ g) w hw hv _ hwT k z] at h
  exact h

/-- Every class on a test scheme is a sum of classes pushed forward from `X'_1` and `X'_2`
(Stacks 0F94). -/
private theorem exists_chowPush_add_chowPush_eq_pullback
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    ∃ (x : chowGroup C (pullback.fst i₁ g ≫ sX₁) k) (y : chowGroup C (pullback.fst i₂ g ≫ sX₂) k),
      chowPush C (pullback.fst i₁ g ≫ sX₁) (g ≫ sX) (pullback.snd i₁ g)
          (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) k x +
        chowPush C (pullback.fst i₂ g ≫ sX₂) (g ≫ sX) (pullback.snd i₂ g)
          (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) k y = α :=
  exists_chowPush_add_chowPush_eq C (g ≫ sX) _ _
    (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g)
    (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g)
    (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover g) k α

/-- **Axiom (1) of Stacks 0B76 for the localized class.** -/
theorem closedCoverLocalizedCap_proper {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [IsProper h] (h' : pullback i₂ (h ≫ g) ⟶ pullback i₂ g) [IsProper h']
    (sq : IsPullback (pullback.snd i₂ (h ≫ g)) h' h (pullback.snd i₂ g))
    (hfst : h' ≫ pullback.fst i₂ g = pullback.fst i₂ (h ≫ g)) (k : ℤ)
    (α : chowGroup C ((h ≫ g) ≫ sX) k) :
    closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k
        (chowPush C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) k α) =
      chowPush C (pullback.fst i₂ (h ≫ g) ≫ sX₂) (pullback.fst i₂ g ≫ sX₂) h'
        (by rw [← Category.assoc, hfst]) (k - p)
        (closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ (h ≫ g) k α) := by
  obtain ⟨x, y, rfl⟩ := exists_chowPush_add_chowPush_eq_pullback C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂
    hcover (h ≫ g) k α
  have sq₁ := isPullback_bivariantBaseChangeMap i₁ g h
  have : IsProper (bivariantBaseChangeMap i₁ g h) :=
    MorphismProperty.of_isPullback sq₁ (P := @IsProper) inferInstance
  rw [map_add,
    chowPush_comm_square C _ _ _ _ (pullback.snd i₁ (h ≫ g)) h (bivariantBaseChangeMap i₁ g h)
      (pullback.snd i₁ g) sq₁.w _ _
      (by rw [← Category.assoc, bivariantBaseChangeMap_fst])
      (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) k x,
    chowPush_comm_square C _ _ _ _ (pullback.snd i₂ (h ≫ g)) h h' (pullback.snd i₂ g) sq.w _ _
      (by rw [← Category.assoc, hfst])
      (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) k y,
    closedCoverLocalizedCap_apply, closedCoverLocalizedCap_apply]
  exact idRule_chowPush C sX₂ κ (pullback.fst i₂ g) (pullback.fst i₂ (h ≫ g)) h' hfst k y

/-- **Axiom (2) of Stacks 0B76 for the localized class.** -/
theorem closedCoverLocalizedCap_flat {T T' : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r)
    (h' : pullback i₂ (h ≫ g) ⟶ pullback i₂ g) [LocallyOfFiniteType h'] [Flat h']
    (sq : IsPullback (pullback.snd i₂ (h ≫ g)) h' h (pullback.snd i₂ g))
    (hfst : h' ≫ pullback.fst i₂ g = pullback.fst i₂ (h ≫ g)) (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ (h ≫ g) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r hr k
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ h _ r hr k) α) ≍
      flatPullbackChow C (pullback.fst i₂ (h ≫ g) ≫ sX₂) (pullback.fst i₂ g ≫ sX₂) h'
        (by rw [← Category.assoc, hfst]) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (k - p)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ h' _ r _ (k - p))
        (closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k α) := by
  obtain ⟨x, y, rfl⟩ := exists_chowPush_add_chowPush_eq_pullback C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂
    hcover g k α
  have sq₁ := isPullback_bivariantBaseChangeMap i₁ g h
  rw [map_add,
    flatPullbackChow_properChowPushforward_unconditional C _ _ _ _ (pullback.snd i₁ g) h
      (bivariantBaseChangeMap i₁ g h) (pullback.snd i₁ (h ≫ g)) sq₁.flip
      (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) (by simp [Category.assoc])
      (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) r hr k x,
    flatPullbackChow_properChowPushforward_unconditional C _ _ _ _ (pullback.snd i₂ g) h h'
      (pullback.snd i₂ (h ≫ g)) sq.flip
      (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) (by simp [Category.assoc])
      (by rw [← Category.assoc, hfst]) r hr k y]
  rw [closedCoverLocalizedCap_apply, closedCoverLocalizedCap_apply]
  exact idRule_flatPullbackChow_heq C sX₂ κ (pullback.fst i₂ g) (pullback.fst i₂ (h ≫ g)) h' r
    _ hfst k y

/-- **Axiom (3) of Stacks 0B76 for the localized class.** The Gysin field of
`Stacks.Chow.BivariantClass`, with the two structure morphisms `(D ⟶ T ⟶ X) ⟶ S` and
`D ⟶ (T ⟶ X ⟶ S)` of the zero scheme compared by an explicit transport. -/
theorem closedCoverLocalizedCap_gysin {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (e : pullback i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≅
        (Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂
        g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback
        (pullback.snd i₂ g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L
        s)).subschemeι = bivariantBaseChangeMap i₂ g (Stacks.Divisors.zeroScheme T L s).subschemeι)
    (hbase : e.hom ≫ ((Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback
        (pullback.snd i₂ g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L
        s)).subschemeι ≫ pullback.fst i₂ g ≫ sX₂) =
      pullback.fst i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX₂)
    (α : chowGroup C (g ≫ sX) (k + 1)) :
    chowPush C (pullback.fst i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX₂)
        ((Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂
            g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L
            s)).subschemeι ≫ pullback.fst i₂ g ≫ sX₂) e.hom hbase (k - p)
        (closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ
            ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
          (chowGroupCongr C (Category.assoc _ _ _).symm k
            ((gysinSystemOfInvertible C).onChow (g ≫ sX) L s k α))) =
      (gysinSystemOfInvertible C).onChow (pullback.fst i₂ g ≫ sX₂)
        ((Scheme.Modules.pullback (pullback.snd i₂ g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s) (k - p)
        (Eq.mp (congrArg (chowGroup C (pullback.fst i₂ g ≫ sX₂))
          (by omega : (k + 1) - p = (k - p) + 1))
          (closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g (k + 1) α)) := by
  obtain ⟨x, y, rfl⟩ := exists_chowPush_add_chowPush_eq_pullback C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂
    hcover g (k + 1) α
  rw [closedCoverLocalizedCap_apply]
  -- the second piece: the morphism of zero schemes is `e⁻¹` followed by the base change of `D`
  have hEι : (Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂
      g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subschemeι =
      e.inv ≫ bivariantBaseChangeMap i₂ g (Stacks.Divisors.zeroScheme T L s).subschemeι := by
    rw [Iso.eq_inv_comp, he]
  have hb₂ : bivariantBaseChangeMap i₂ g (Stacks.Divisors.zeroScheme T L s).subschemeι ≫
      pullback.snd i₂ g =
      pullback.snd i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫
          (Stacks.Divisors.zeroScheme T L s).subschemeι := by
    simp [bivariantBaseChangeMap]
  have hj₂ : (e.inv ≫ pullback.snd i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) ≫
      (Stacks.Divisors.zeroScheme T L s).subschemeι =
      (Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂
          g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subschemeι
          ≫ pullback.snd i₂ g := by
    rw [hEι, Category.assoc, Category.assoc, hb₂]
  have hfstD : e.inv ≫ pullback.fst i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) =
      (Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂
          g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subschemeι
          ≫ pullback.fst i₂ g := by
    rw [hEι, Category.assoc, bivariantBaseChangeMap_fst]
  have h02TA₂ := gysinSystemOfInvertible_isNaturalUnderProperPushforward C _ _ (pullback.snd i₂ g)
    (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) L s k _ hj₂
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) y
  -- the first piece: a morphism of Remark 0B6Y, which factors through the base change of `D`
  obtain ⟨j₁, hj₁⟩ : ∃ j : (pullbackZeroScheme (pullback.snd i₁ g) L s).subscheme ⟶
      (Stacks.Divisors.zeroScheme T L s).subscheme,
      j ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι = (pullbackZeroScheme (pullback.snd i₁ g) L
          s).subschemeι ≫ pullback.snd i₁ g :=
    ⟨_, zeroSchemePullbackHom_subschemeι (pullback.snd i₁ g) L s⟩
  have : IsProper (j₁ ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι) := by
    rw [hj₁]; infer_instance
  have : IsProper j₁ := IsProper.of_comp j₁ (Stacks.Divisors.zeroScheme T L s).subschemeι
  have hφ : ((pullbackZeroScheme (pullback.snd i₁ g) L s).subschemeι ≫ pullback.fst i₁ g) ≫ i₁ = j₁
      ≫ (Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hj₁, Category.assoc]
  obtain ⟨φ₁, hφ₁, hφf⟩ : ∃ φ : (pullbackZeroScheme (pullback.snd i₁ g) L s).subscheme ⟶ pullback
      i₁ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g),
      φ ≫ pullback.snd i₁ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) = j₁ ∧
        φ ≫ pullback.fst i₁ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) =
            (pullbackZeroScheme (pullback.snd i₁ g) L s).subschemeι ≫ pullback.fst i₁ g :=
    ⟨pullback.lift _ _ hφ, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  have : IsProper (φ₁ ≫ pullback.snd i₁ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) := by
      rw [hφ₁]; infer_instance
  have : IsProper φ₁ := IsProper.of_comp φ₁ (pullback.snd i₁ ((Stacks.Divisors.zeroScheme T L
      s).subschemeι ≫ g))
  have h02TA₁ := gysinSystemOfInvertible_isNaturalUnderProperPushforward C _ _ (pullback.snd i₁ g)
    (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) L s k j₁ hj₁
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) x
  have hφs : φ₁ ≫ pullback.fst i₁ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX₁ =
      (pullbackZeroScheme (pullback.snd i₁ g) L s).subschemeι ≫ pullback.fst i₁ g ≫ sX₁ := by
    rw [← Category.assoc, hφf, Category.assoc]
  have hes : e.inv ≫ pullback.fst i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX₂ =
      (Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂
          g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subschemeι
          ≫ pullback.fst i₂ g ≫ sX₂ := by
    rw [← Category.assoc, hfstD, Category.assoc]
  -- the Gysin map of the decomposition, transported to the structure morphism of the test scheme
  have hG := (map_add ((gysinSystemOfInvertible C).onChow (g ≫ sX) L s k) _ _).trans
    (congrArg₂ (· + ·) h02TA₁ h02TA₂)
  have hB₁ : j₁ ≫ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX = (pullbackZeroScheme
      (pullback.snd i₁ g) L s).subschemeι ≫ pullback.fst i₁ g ≫ sX₁ := by
    rw [← hφ₁, Category.assoc φ₁,
      pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ ((Stacks.Divisors.zeroScheme T L
          s).subschemeι ≫ g), hφs]
  have hB₂ : (e.inv ≫ pullback.snd i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g)) ≫
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ≫ sX =
      (Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂
          g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subschemeι
          ≫ pullback.fst i₂ g ≫ sX₂ := by
    rw [Category.assoc e.inv,
      pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ ((Stacks.Divisors.zeroScheme T L
          s).subschemeι ≫ g), hes]
  have e₁ := chowGroupCongr_chowPush C ((pullbackZeroScheme (pullback.snd i₁ g) L s).subschemeι ≫
      pullback.fst i₁ g ≫ sX₁)
    (Category.assoc (Stacks.Divisors.zeroScheme T L s).subschemeι g sX).symm j₁
    (zeroSchemeSquare_comp_structureMorphism C _ _ _
      (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) L s _ hj₁) hB₁ k
          ((gysinSystemOfInvertible C).onChow (pullback.fst i₁ g ≫ sX₁) ((Scheme.Modules.pullback
          (pullback.snd i₁ g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₁ g)
          L s) k x)
  have e₂ := chowGroupCongr_chowPush C ((Stacks.Divisors.zeroScheme (pullback i₂ g)
      ((Scheme.Modules.pullback (pullback.snd i₂ g)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subschemeι ≫ pullback.fst
      i₂ g ≫ sX₂)
    (Category.assoc (Stacks.Divisors.zeroScheme T L s).subschemeι g sX).symm (e.inv ≫ pullback.snd
        i₂ ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g))
    (zeroSchemeSquare_comp_structureMorphism C _ _ _
      (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) L s _ hj₂) hB₂ k
          ((gysinSystemOfInvertible C).onChow (pullback.fst i₂ g ≫ sX₂) ((Scheme.Modules.pullback
          (pullback.snd i₂ g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g)
          L s) k y)
  have k₁ := closedCoverLocalizedCap_chowPush_left C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) _ φ₁ hφs j₁ hφ₁ hB₁ k
        ((gysinSystemOfInvertible C).onChow (pullback.fst i₁ g ≫ sX₁) ((Scheme.Modules.pullback
        (pullback.snd i₁ g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₁ g) L
        s) k x)
  have k₂ := closedCoverLocalizedCap_chowPush_right C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) _ e.inv hes _ rfl hB₂ k
        ((gysinSystemOfInvertible C).onChow (pullback.fst i₂ g ≫ sX₂) ((Scheme.Modules.pullback
        (pullback.snd i₂ g)).obj L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L
        s) k y)
  have hκe := idRule_chowPush_of_eq C sX₂ κ (pullback.fst i₂ ((Stacks.Divisors.zeroScheme T L
      s).subschemeι ≫ g))
    ((Stacks.Divisors.zeroScheme (pullback i₂ g) ((Scheme.Modules.pullback (pullback.snd i₂ g)).obj
        L) (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s)).subschemeι ≫
        pullback.fst i₂ g) e.inv hfstD _ (Category.assoc _ _ _) hes k ((gysinSystemOfInvertible
        C).onChow (pullback.fst i₂ g ≫ sX₂) ((Scheme.Modules.pullback (pullback.snd i₂ g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s) k y)
  have hgy := idRule_gysin_chowGroupCongr C sX₂ κ (pullback.fst i₂ g)
    ((Scheme.Modules.pullback (pullback.snd i₂ g)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd i₂ g) L s) k y
  have hcap := ((congrArg (fun z ↦ closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k
      (chowGroupCongr C (Category.assoc _ _ _).symm k z)) hG).trans
    ((congrArg (closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k)
      ((AddEquiv.map_add _ _ _).trans (congrArg₂ (· + ·) e₁ e₂))).trans
    ((AddMonoidHom.map_add _ _ _).trans ((congrArg₂ (· + ·) k₁ k₂).trans (zero_add _)))))
  have hm : ∀ {a b}, a = b → chowPush C _ _ e.hom hbase (k - p) a =
      chowPush C _ _ e.hom hbase (k - p) b := fun h ↦ congrArg _ h
  refine (hm hcap).trans ?_
  refine (hm hκe).trans ?_
  refine (chowPush_comp C _ _ _ e.inv e.hom (𝟙 _) (Iso.inv_hom_id e) _ hbase
    (by rw [Category.id_comp, Category.assoc]) (k - p) _).trans ?_
  refine (chowPush_id_eq_chowGroupCongr C _ _ _ (k - p) _).trans ?_
  refine (congrArg (chowGroupCongr C _ (k - p)) hgy).trans ?_
  exact (chowGroupCongr_chowGroupCongr C _ _ (k - p) _).trans (chowGroupCongr_self C _ (k - p) _)

/-- **The localized class of Stacks 0F9H.** The bivariant class `κ' ∈ A^p(X₂ ⟶ X)` of a class
`κ ∈ A^p(X₂)` vanishing on `X₁ ∩ X₂`, for a set-theoretic cover `X = X₁ ∪ X₂` by two closed
subschemes: on a test scheme `X' ⟶ X` it sends `i'_{1,*} α₁ + i'_{2,*} α₂` to `κ ∩ α₂`. -/
def closedCoverLocalizedClass :
    BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p where
  cap g _ k := closedCoverLocalizedCap C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    exact closedCoverLocalizedCap_proper C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g h h' sq hfst k α
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ r hr h' sq hfst k α
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    exact closedCoverLocalizedCap_flat C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g h r hr h' sq hfst
      k α
  cap_gysin := by
    intro T g _ L _ s k _ _ _ _ e he hbase α
    exact closedCoverLocalizedCap_gysin C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g L s k e he hbase
      α

/-- **The first characterizing identity of Stacks 0F9H**, on every test scheme `g : X' ⟶ X`:
`κ' ∩ i'_{2,*} α₂ = κ ∩ α₂` for `α₂ ∈ A_k(X'_2)`. -/
theorem closedCoverLocalizedClass_cap_pushforward_right {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (pullback.fst i₂ g ≫ sX₂) k) :
    (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ).cap g k
        (chowPush C (pullback.fst i₂ g ≫ sX₂) (g ≫ sX) (pullback.snd i₂ g)
          (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) k α) =
      κ.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ g) k α := by
  have h := closedCoverLocalizedCap_apply C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k 0 α
  rwa [map_zero, zero_add] at h

/-- **The second characterizing identity of Stacks 0F9H**, on every test scheme `g : X' ⟶ X`:
`κ' ∩ i'_{1,*} α₁ = 0` for `α₁ ∈ A_k(X'_1)`. -/
theorem closedCoverLocalizedClass_cap_pushforward_left {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (pullback.fst i₁ g ≫ sX₁) k) :
    (closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ).cap g k
        (chowPush C (pullback.fst i₁ g ≫ sX₁) (g ≫ sX) (pullback.snd i₁ g)
          (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) k α) = 0 := by
  have h := closedCoverLocalizedCap_apply C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ g k α 0
  rwa [map_zero, add_zero, map_zero] at h

include hcover in
/-- **Uniqueness.** A bivariant class in `A^p(X₂ ⟶ X)` satisfying the two characterizing
identities on every test scheme is the localized class: by Stacks 0F94 every class on a test
scheme is a sum of classes pushed forward from the two pieces. -/
theorem eq_closedCoverLocalizedClass
    (c : BivariantClass C (gysinSystemOfInvertible C) sX₂ sX i₂ hi₂ p)
    (hright : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (pullback.fst i₂ g ≫ sX₂) k),
      c.cap g k (chowPush C (pullback.fst i₂ g ≫ sX₂) (g ≫ sX) (pullback.snd i₂ g)
          (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g) k α) =
        κ.idRule C sX₂ (gysinSystemOfInvertible C) (pullback.fst i₂ g) k α)
    (hleft : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (pullback.fst i₁ g ≫ sX₁) k),
      c.cap g k (chowPush C (pullback.fst i₁ g ≫ sX₁) (g ≫ sX) (pullback.snd i₁ g)
          (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g) k α) = 0) :
    c = closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ := by
  refine BivariantClass.ext C _ sX₂ sX i₂ hi₂ p fun g _ k α ↦ ?_
  have hF := closedCover_addMonoidHom_ext C (g ≫ sX) _ _
    (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism_eq C sX₁ sX i₁ hi₁ g)
    (pullback.snd i₂ g) (pullbackSnd_comp_structureMorphism_eq C sX₂ sX i₂ hi₂ g)
    (range_pullbackSnd_union_range_pullbackSnd i₁ i₂ hcover g) k (c.cap g k)
    ((closedCoverLocalizedClass C sX sX₁ sX₂ i₁ hi₁ i₂ hi₂ hcover κ hκ).cap g k)
    (fun x ↦ by rw [hleft, closedCoverLocalizedClass_cap_pushforward_left])
    (fun y ↦ by rw [hright, closedCoverLocalizedClass_cap_pushforward_right])
  exact DFunLike.congr_fun hF α

end Construction

end Stacks.Chow

end
