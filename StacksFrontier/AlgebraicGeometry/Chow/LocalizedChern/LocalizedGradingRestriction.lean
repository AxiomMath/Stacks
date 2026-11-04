module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseCommute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.DefinedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness

/-!
# Restriction of the localized grading

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`, and let `f : X' ⟶ X` be a morphism
locally of finite type, with base change `i' : Z' = Z ×_X X' ⟶ X'`. Restriction of bivariant
classes along `f` (Stacks 0B7F and Stacks 0F9Z) maps `Aⁱ(X)` to `Aⁱ(X')` and `Aⁱ(Z ⟶ X)` to
`Aⁱ(Z' ⟶ X')`, and so, componentwise, the group

  `A⁽ᵖ⁾(Z ⟶ X) = ∏_{i ≤ p - 1} Aⁱ(X) × ∏_{i ≥ p} Aⁱ(Z ⟶ X)`

of Stacks 0FA0 to `A⁽ᵖ⁾(Z' ⟶ X')`. This file shows that the map commutes with the
multiplication of Stacks 0FA0, and that it is injective when `f` is an envelope (Stacks 0GUC).

The compatibility with the multiplication comes down to the compatibility of restriction with each
of the operations entering it: the product of `A^*(X)`, the pushforward `A^*(Z ⟶ X) ⟶ A^*(X)` of
Stacks 0EPK, and the three products of Stacks 0FA0. Each is a computation on the test schemes:
both sides cap a class `α` on a test scheme `T ⟶ X'` by the cap operations of the given classes on
the test scheme `T ⟶ X' ⟶ X`, read through the canonical isomorphisms of iterated fibre products.

## Main definitions

* `Stacks.Chow.supportedRestriction` — the restriction `Aⁱ(Z ⟶ X) ⟶ Aⁱ(Z' ⟶ X')` along `f`.
* `Stacks.Chow.localizedGradingRestriction` — the restriction `A⁽ᵖ⁾(Z ⟶ X) ⟶ A⁽ᵖ⁾(Z' ⟶ X')`.

## Main results

* `Stacks.Chow.chowCohomologyRestriction_properPushforwardChowCohomology` — restriction commutes
  with the pushforward `A^*(Z ⟶ X) ⟶ A^*(X)`.
* `Stacks.Chow.chowCohomologyRestriction_closedImmersionChowCohomologyRestriction` — restriction
  commutes with the restriction map `A^*(Z ⟶ X) ⟶ A^*(Z)` of Stacks 0FA1.
* `Stacks.Chow.supportedRestriction_supportedRightComp`,
  `Stacks.Chow.supportedRestriction_supportedLeftComp`,
  `Stacks.Chow.supportedRestriction_supportedMul`,
  `Stacks.Chow.supportedRestriction_ambientSupportedMul` — restriction commutes with the products
  of Stacks 0FA0.
* `Stacks.Chow.localizedGradingRestriction_localizedGradingMul` — restriction commutes with the
  multiplication of Stacks 0FA0.
* `Stacks.Chow.localizedGradingRestriction_localizedGradingCutoffMul` — the same for the
  multiplication with any output cutoff `r ≥ p + q - 1`.
* `Stacks.Chow.supportedRestriction_injective_of_isEnvelope`,
  `Stacks.Chow.localizedGradingRestriction_injective_of_isEnvelope` — restriction along an
  envelope is injective.

## Implementation notes

The closed subscheme `Z' = Z ×_X X'` of `X'` is given the structure morphism
`Z' ⟶ X' ⟶ X ⟶ S`, through `X'`, rather than the one through `Z` that the restriction map of
Stacks 0F9Z produces; the two are equal, and `Stacks.Chow.supportedRestriction` reads the
restricted class against the former (`Stacks.Chow.bivariantClassCongrBase`). With this choice the
base change of the data of a localized Chern class along `f`
(`Stacks.Chow.LocalizedChernData.pullback`) has exactly the target grading.

All classes are taken at the Gysin system of the first Chern class rule,
`Stacks.Chow.gysinSystemOfInvertible`, as for the multiplication of Stacks 0FA0.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (f : X' ⟶ X) [LocallyOfFiniteType f]

/-! ### Pushing a cap operation forward to the test scheme -/

/-- The cap operation of a bivariant class at a test morphism `m : T ⟶ X`, pushed forward along the
base change `Z ×_X T ⟶ T`, depends on `m`, the argument and the structure morphism of `T` only up
to equality and heterogeneous equality. -/
theorem BivariantClass.chowPush_cap_heq_of_eq {G : GysinSystem C} {p : ℤ}
    (c : BivariantClass C G sZ sX i hi p) {T : Scheme.{u}} {m m' : T ⟶ X}
    [LocallyOfFiniteType m] [LocallyOfFiniteType m'] (hm : m = m') {sT sT' : T ⟶ C.S}
    [LocallyOfFiniteType sT] [LocallyOfFiniteType sT'] (hsT : sT = sT')
    (h : pullback.snd i m ≫ sT = pullback.fst i m ≫ sZ)
    (h' : pullback.snd i m' ≫ sT' = pullback.fst i m' ≫ sZ) {k : ℤ}
    {x : chowGroup C (m ≫ sX) k} {x' : chowGroup C (m' ≫ sX) k} (hx : x ≍ x') :
    chowPush C (pullback.fst i m ≫ sZ) sT (pullback.snd i m) h (k - p) (c.cap m k x) ≍
      chowPush C (pullback.fst i m' ≫ sZ) sT' (pullback.snd i m') h' (k - p)
        (c.cap m' k x') := by
  subst hm hsT
  cases hx
  rfl

/-! ### The restriction of a class supported on `Z` -/

/-- **The restriction `Aᵖ(Z ⟶ X) ⟶ Aᵖ(Z' ⟶ X')` along `f : X' ⟶ X`** of Stacks 0F9Z, for the
base change `Z' = Z ×_X X' ⟶ X'` of the closed immersion `i`, with `Z'` read over the base through
`X'`. -/
abbrev supportedRestriction {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) :
    BivariantClass C (gysinSystemOfInvertible C) (pullback.snd i f ≫ (f ≫ sX)) (f ≫ sX)
      (pullback.snd i f) rfl p :=
  bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd i f)
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f).symm rfl
    (hv := pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (hv' := rfl) p
    (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)

/-- **The cap operation of a restricted class.** On a test scheme `t : T ⟶ X'` the restriction of
`c` caps as `c` does on `t ≫ f`, pushed forward along the canonical isomorphism
`Z ×_X T ≅ Z' ×_{X'} T`. -/
theorem supportedRestriction_cap {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) {T : Scheme.{u}}
    (t : T ⟶ X') [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    (supportedRestriction C sZ sX i hi f c).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ)
        (pullback.fst (pullback.snd i f) t ≫ (pullback.fst i f ≫ sZ))
        (pullbackLeftPullbackSndIso i f t).inv (by simp) (k - p)
        (c.cap (t ≫ f) k (chowGroupCongr C (Category.assoc t f sX).symm k α)) :=
  bivariantClassCongrBase_cap C (gysinSystemOfInvertible C) (pullback.snd i f) _ rfl p _ t k α α
    HEq.rfl

/-- Restriction commutes with transport along an equality of degrees. -/
theorem supportedRestriction_bivariantClassDegreeCongr {p p' : ℤ} (h : p = p')
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) :
    supportedRestriction C sZ sX i hi f (bivariantClassDegreeCongr C _ sZ sX i hi h c) =
      bivariantClassDegreeCongr C _ _ _ _ rfl h (supportedRestriction C sZ sX i hi f c) := by
  subst h
  rfl

/-- Restriction of classes supported on `Z` is additive. -/
theorem supportedRestriction_sum {p : ℤ} {ι : Type*} (s : Finset ι)
    (c : ι → BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) :
    supportedRestriction C sZ sX i hi f (∑ j ∈ s, c j) =
      ∑ j ∈ s, supportedRestriction C sZ sX i hi f (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, supportedRestriction, bivariantRestriction_zero, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, supportedRestriction,
      supportedRestriction, bivariantRestriction_add, map_add]

/-- Restriction of classes supported on `Z` is additive. -/
theorem supportedRestriction_add {p : ℤ}
    (c d : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) :
    supportedRestriction C sZ sX i hi f (c + d) =
      supportedRestriction C sZ sX i hi f c + supportedRestriction C sZ sX i hi f d := by
  rw [supportedRestriction, supportedRestriction, supportedRestriction, bivariantRestriction_add,
    map_add]

/-! ### Restriction and pushforward -/

/-- **Restriction commutes with the pushforward `A^p(Z ⟶ X) ⟶ A^p(X)`** of Stacks 0EPK:
`f^*(i_* ∘ c) = i'_* ∘ f^*c`. On a test scheme `T ⟶ X'` both sides push the cap operation of `c`
on `T ⟶ X' ⟶ X` forward to `T`. -/
theorem chowCohomologyRestriction_properPushforwardChowCohomology {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (properPushforwardChowCohomology C sX sZ i hi c) =
      properPushforwardChowCohomology C (f ≫ sX) (pullback.snd i f ≫ (f ≫ sX))
        (pullback.snd i f) rfl (supportedRestriction C sZ sX i hi f c) := by
  refine BivariantClass.eq_of_idRule_eq C (f ≫ sX) _ _ _ fun {T} n _ k α ↦ ?_
  rw [chowCohomologyRestriction_idRule, idRule_properPushforwardChowCohomology,
    idRule_properPushforwardChowCohomology]
  have hw : (pullbackLeftPullbackSndIso i f n).inv ≫ pullback.snd (pullback.snd i f) n =
      pullback.snd i (n ≫ f) := by simp
  have hs : pullback.fst (pullback.snd i f) n ≫ (pullback.snd i f ≫ (f ≫ sX)) =
      pullback.fst (pullback.snd i f) n ≫ (pullback.fst i f ≫ sZ) := by
    rw [pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f]
  have e1 := chowPush_heq C (pullback.snd (pullback.snd i f) n)
    (pullbackSnd_comp_structureMorphism rfl n)
    (pullbackSnd_comp_structureMorphism
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) n) hs rfl rfl
    (supportedRestriction_cap C sZ sX i hi f c n k α)
  have e2 := properChowPushforward_comp_apply C _ _ (n ≫ (f ≫ sX))
    (pullbackLeftPullbackSndIso i f n).inv (pullback.snd (pullback.snd i f) n)
    (pullback.snd i (n ≫ f)) hw (by simp)
    (pullbackSnd_comp_structureMorphism
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) n)
    (by rw [← Category.assoc n f sX]; exact pullbackSnd_comp_structureMorphism hi (n ≫ f))
    (k - p) (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (c.cap (n ≫ f) k (chowGroupCongr C (Category.assoc n f sX).symm k α))
  refine eq_of_heq (HEq.trans ?_ (e1.trans (heq_of_eq e2.symm)).symm)
  exact chowPush_heq C (pullback.snd i (n ≫ f)) _ _ rfl (Category.assoc n f sX) rfl HEq.rfl

/-! ### Restriction and the products of Stacks 0FA0 -/

/-- **Restriction commutes with the composition `A^p(Z ⟶ X) × A^q(X) ⟶ A^{p+q}(Z ⟶ X)`**:
`f^*(c ∘ d) = f^*c ∘ f^*d`. -/
theorem supportedRestriction_supportedRightComp {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    supportedRestriction C sZ sX i hi f (supportedRightComp C sZ sX i hi c d) =
      supportedRightComp C (pullback.snd i f ≫ (f ≫ sX)) (f ≫ sX) (pullback.snd i f) rfl
        (supportedRestriction C sZ sX i hi f c)
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ eq_of_heq ?_
  refine (supportedRestriction_cap C sZ sX i hi f _ t k α).trans (HEq.trans ?_
    (supportedRightComp_cap C _ _ _ rfl _ _ t k α).symm)
  refine HEq.trans ?_ (supportedRestriction_cap C sZ sX i hi f c t (k - q) _).symm
  refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    ((supportedRightComp_cap C sZ sX i hi c d (t ≫ f) k _).trans
      (BivariantClass.cap_heq c (t ≫ f) rfl ?_))
  rw [chowCohomologyRestriction_idRule]
  exact (chowGroupCongr_heq C _ _ _).symm

/-- **Restriction commutes with the composition `A^p(Z) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)`**:
`f^*(b ∘ c) = b|_{Z'} ∘ f^*c`, with `b|_{Z'}` the restriction of Stacks 0B7F along
`Z' ⟶ Z`. -/
theorem supportedRestriction_supportedLeftComp {p q : ℤ}
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi q) :
    supportedRestriction C sZ sX i hi f (supportedLeftComp C sZ sX i hi b c) =
      supportedLeftComp C (pullback.snd i f ≫ (f ≫ sX)) (f ≫ sX) (pullback.snd i f) rfl
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 _)
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f).symm
          (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f).symm
          (hv := Category.id_comp _) (hv' := Category.id_comp _) p
          (chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ (pullback.fst i f) p
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b))
        (supportedRestriction C sZ sX i hi f c) := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ eq_of_heq ?_
  refine (supportedRestriction_cap C sZ sX i hi f _ t k α).trans (HEq.trans ?_
    (supportedLeftComp_cap C _ _ _ rfl _ _ t k α).symm)
  set m := pullback.fst (pullback.snd i f) t
  set w := (pullbackLeftPullbackSndIso i f t).inv
  set x := c.cap (t ≫ f) k (chowGroupCongr C (Category.assoc t f sX).symm k α)
  have hhv := pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f
  have hm : w ≫ (m ≫ pullback.fst i f) = pullback.fst i (t ≫ f) := by simp [w, m]
  have hsT : m ≫ (pullback.fst i f ≫ sZ) = (m ≫ pullback.fst i f) ≫ sZ :=
    (Category.assoc _ _ _).symm
  have hφ : w ≫ (m ≫ (pullback.fst i f ≫ sZ)) = pullback.fst i (t ≫ f) ≫ sZ := by
    simp [w, m]
  have hz : chowGroupCongr C (by rw [hhv, hsT]) (k - q)
      ((supportedRestriction C sZ sX i hi f c).cap t k α) ≍
        chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (m ≫ (pullback.fst i f ≫ sZ)) w hφ
          (k - q) x :=
    (chowGroupCongr_heq C _ _ _).trans (supportedRestriction_cap C sZ sX i hi f c t k α)
  have key := BivariantClass.idRule_chowPushforwardOfIso_heq (G := gysinSystemOfInvertible C)
    b (m ≫ pullback.fst i f) w (pullback.fst i (t ≫ f)) hm hsT hφ (k - q) x _ hz x HEq.rfl
  refine HEq.trans ?_ (HEq.trans (HEq.symm ?_) key).symm
  · refine chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
      (supportedLeftComp_cap C sZ sX i hi b c (t ≫ f) k _)
  · refine HEq.symm ?_
    rw [BivariantClass.idRule_bivariantClassCongrBase]
    refine (chowGroupCongr_heq C _ _ _).trans ?_
    refine BivariantClass.idRule_chowCohomologyRestriction_heq (pullback.fst i f) b m (k - q) _ _ ?_
    exact (chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm

/-- **Restriction commutes with the restriction map `Aᵖ(Z ⟶ X) ⟶ Aᵖ(Z)` of Stacks 0FA1**: the
restriction to `Z'` (Stacks 0B7F along `Z' ⟶ Z`) of `res(c) ∈ Aᵖ(Z)` is `res(f^*c) ∈ Aᵖ(Z')`. -/
theorem chowCohomologyRestriction_closedImmersionChowCohomologyRestriction {p : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) :
    bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 _)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f).symm
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f).symm
        (hv := Category.id_comp _) (hv' := Category.id_comp _) p
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sZ (pullback.fst i f) p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Z) hi hi
            (hv := Category.id_comp _) (hv' := Category.id_comp _) p
            (closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) sZ sX i hi p
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c))) =
      closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C)
        (pullback.snd i f ≫ (f ≫ sX)) (f ≫ sX) (pullback.snd i f) rfl p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (supportedRestriction C sZ sX i hi f c) := by
  have hhv := pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f
  refine BivariantClass.eq_of_idRule_eq C (pullback.snd i f ≫ (f ≫ sX)) _ _ _
    fun {T} g _ k α ↦ eq_of_heq ?_
  rw [BivariantClass.idRule_bivariantClassCongrBase,
    closedImmersionChowCohomologyRestriction_idRule]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  have hβ : g ≫ (pullback.snd i f ≫ (f ≫ sX)) = (g ≫ pullback.fst i f) ≫ sZ := by
    rw [hhv, Category.assoc]
  refine (BivariantClass.idRule_chowCohomologyRestriction_heq (pullback.fst i f) _ g k _
    (chowGroupCongr C hβ k α) ((chowGroupCongr_heq C _ _ _).trans
      (chowGroupCongr_heq C _ _ _).symm)).trans ?_
  rw [BivariantClass.idRule_bivariantClassCongrBase,
    closedImmersionChowCohomologyRestriction_idRule]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  set t := g ≫ pullback.snd i f
  set w := (pullbackLeftPullbackSndIso i f t).inv
  set x := c.cap (t ≫ f) k (chowGroupCongr C (Category.assoc t f sX).symm k
    (chowGroupCongr C (Category.assoc g (pullback.snd i f) (f ≫ sX)).symm k α))
  have hw : w ≫ pullback.snd (pullback.snd i f) t = pullback.snd i (t ≫ f) := by simp [w]
  have hs : pullback.fst (pullback.snd i f) t ≫ (pullback.snd i f ≫ (f ≫ sX)) =
      pullback.fst (pullback.snd i f) t ≫ (pullback.fst i f ≫ sZ) := by rw [hhv]
  have e1 := chowPush_heq C (pullback.snd (pullback.snd i f) t)
    (pullbackSnd_comp_structureMorphism rfl t)
    (pullbackSnd_comp_structureMorphism hhv t) hs rfl rfl
    (supportedRestriction_cap C sZ sX i hi f c t k
      (chowGroupCongr C (Category.assoc g (pullback.snd i f) (f ≫ sX)).symm k α))
  have e2 := properChowPushforward_comp_apply C _ _ (t ≫ (f ≫ sX)) w
    (pullback.snd (pullback.snd i f) t) (pullback.snd i (t ≫ f)) hw (by simp [w])
    (pullbackSnd_comp_structureMorphism hhv t)
    (by rw [← Category.assoc t f sX]; exact pullbackSnd_comp_structureMorphism hi (t ≫ f))
    (k - p) (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) x
  refine HEq.trans ?_ (e1.trans (heq_of_eq e2.symm)).symm
  have hm : (g ≫ pullback.fst i f) ≫ i = t ≫ f := by
    simp only [t, Category.assoc, pullback.condition]
  refine BivariantClass.chowPush_cap_heq_of_eq C sZ sX i hi c hm
    (by rw [← Category.assoc, hm, Category.assoc]) _ _ ?_
  exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).trans
    ((chowGroupCongr_heq C _ _ _).trans ((chowGroupCongr_heq C _ _ _).symm.trans
      (chowGroupCongr_heq C _ _ _).symm)))

/-- **Restriction commutes with the third product `res(c) ∘ c'` of Stacks 0FA0**:
`f^*(res(c) ∘ c') = res(f^*c) ∘ f^*c'`. Both products are `c ∘ (i_* ∘ c')`
(`Stacks.Chow.supportedMul_eq_supportedRightComp`), and restriction commutes with the composition
and with the pushforward. -/
theorem supportedRestriction_supportedMul {p q : ℤ}
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi q) :
    supportedRestriction C sZ sX i hi f (supportedMul C sZ sX i hi c c') =
      supportedMul C (pullback.snd i f ≫ (f ≫ sX)) (f ≫ sX) (pullback.snd i f) rfl
        (supportedRestriction C sZ sX i hi f c) (supportedRestriction C sZ sX i hi f c') := by
  rw [supportedMul_eq_supportedRightComp, supportedRestriction_supportedRightComp,
    chowCohomologyRestriction_properPushforwardChowCohomology,
    supportedMul_eq_supportedRightComp]

/-- Restriction of Chow cohomology classes against two equal structure morphisms of the target
gives heterogeneously equal classes. -/
theorem chowCohomologyRestriction_heq_congr_base {Y Y' : Scheme.{u}} {sY sY' : Y ⟶ C.S}
    [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] (hs : sY = sY') (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] {p : ℤ} {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p}
    {a' : chowCohomologyComponent C (gysinSystemOfInvertible C) sY' p} (ha : a ≍ a') :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sY h p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a ≍
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sY' h p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a' := by
  subst hs
  cases ha
  rfl

/-- **Restriction commutes with the second product `res(d) ∘ c` of Stacks 0FA0**:
`f^*(res(d) ∘ c) = res(f^*d) ∘ f^*c`, since restricting `d` to `Z` and then to `Z'` is
restricting it to `X'` and then to `Z'`. -/
theorem supportedRestriction_ambientSupportedMul {p q : ℤ}
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi q) :
    supportedRestriction C sZ sX i hi f (ambientSupportedMul C sZ sX i hi d c) =
      ambientSupportedMul C (pullback.snd i f ≫ (f ≫ sX)) (f ≫ sX) (pullback.snd i f) rfl
        (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)
        (supportedRestriction C sZ sX i hi f c) := by
  rw [ambientSupportedMul, supportedRestriction_supportedLeftComp, ambientSupportedMul]
  congr 1
  refine eq_of_heq ((bivariantClassCongrBase_heq _ _ _ _ _).trans (HEq.trans ?_
    (bivariantClassCongrBase_heq _ _ _ _ _).symm))
  refine (chowCohomologyRestriction_heq_congr_base C hi.symm (pullback.fst i f)
    (bivariantClassCongrBase_heq _ _ _ _ _)).trans ?_
  refine (chowCohomologyRestriction_chowCohomologyRestriction sX i (pullback.fst i f) d).trans ?_
  refine (chowCohomologyRestriction_heq_congr sX (pullback.condition (f := i) (g := f)) d).trans ?_
  exact (chowCohomologyRestriction_chowCohomologyRestriction sX f (pullback.snd i f) d).symm

/-! ### The restriction of the localized grading -/

/-- **The restriction `A⁽ᵖ⁾(Z ⟶ X) ⟶ A⁽ᵖ⁾(Z' ⟶ X')` along `f : X' ⟶ X`**, for the base change
`Z' = Z ×_X X' ⟶ X'` of the closed immersion `i`: the restriction of Stacks 0B7F on the
components of degree `< p`, and the restriction of Stacks 0F9Z
(`Stacks.Chow.supportedRestriction`) on the components of degree `≥ p`. -/
def localizedGradingRestriction {p : ℕ}
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (pullback.snd i f ≫ (f ≫ sX))
      (f ≫ sX) (pullback.snd i f) rfl p :=
  (fun n => chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f n.1
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (a.1 n),
    fun n => supportedRestriction C sZ sX i hi f (a.2 n))

variable {C sZ sX i hi f}

/-- The components of degree `< p` of a restriction are the restrictions of the components. -/
@[simp]
theorem localizedGradingRestriction_fst {p : ℕ}
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p)
    (n : {n : ℤ // n < (p : ℤ)}) :
    (localizedGradingRestriction C sZ sX i hi f a).1 n =
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f n.1
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (a.1 n) :=
  rfl

/-- The components of degree `≥ p` of a restriction are the restrictions of the components. -/
@[simp]
theorem localizedGradingRestriction_snd {p : ℕ}
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p)
    (n : {n : ℤ // (p : ℤ) ≤ n}) :
    (localizedGradingRestriction C sZ sX i hi f a).2 n =
      supportedRestriction C sZ sX i hi f (a.2 n) :=
  rfl

/-- Restriction commutes with taking the pushed components (`Stacks.Chow.localizedGradingPush`)
of an element of `A⁽ᵖ⁾(Z ⟶ X)`. -/
theorem chowCohomologyRestriction_localizedGradingPush {p : ℕ}
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p) (n : ℤ) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f n
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (localizedGradingPush C sZ sX i hi a n) =
      localizedGradingPush C _ _ _ rfl (localizedGradingRestriction C sZ sX i hi f a) n := by
  rcases lt_or_ge n (p : ℤ) with h | h
  · rw [localizedGradingPush_of_lt _ h, localizedGradingPush_of_lt _ h]
    rfl
  · rw [localizedGradingPush_of_le _ h, localizedGradingPush_of_le _ h,
      chowCohomologyRestriction_properPushforwardChowCohomology]
    rfl

/-- Restriction commutes with the summands `aᵢ bⱼ` (`Stacks.Chow.localizedGradingHighTerm`) of the
components of degree `≥ p + q` of a product. -/
theorem supportedRestriction_localizedGradingHighTerm {p q : ℕ}
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n) (j : ℤ) :
    supportedRestriction C sZ sX i hi f (localizedGradingHighTerm C sZ sX i hi a b hn j) =
      localizedGradingHighTerm C _ _ _ rfl (localizedGradingRestriction C sZ sX i hi f a)
        (localizedGradingRestriction C sZ sX i hi f b) hn j := by
  by_cases hp : (p : ℤ) ≤ j
  · by_cases hq : (q : ℤ) ≤ n - j
    · rw [localizedGradingHighTerm_of_le_of_le _ _ _ hp hq,
        localizedGradingHighTerm_of_le_of_le _ _ _ hp hq, supportedRestriction_supportedMul]
      rfl
    · rw [localizedGradingHighTerm_of_le_of_lt _ _ _ hp (not_le.mp hq),
        localizedGradingHighTerm_of_le_of_lt _ _ _ hp (not_le.mp hq),
        supportedRestriction_supportedRightComp]
      rfl
  · have hq : (q : ℤ) ≤ n - j := by push_cast at hn; omega
    rw [localizedGradingHighTerm_of_lt _ _ _ (not_le.mp hp) hq,
      localizedGradingHighTerm_of_lt _ _ _ (not_le.mp hp) hq,
      supportedRestriction_ambientSupportedMul]
    rfl

/-- **Restriction commutes with the multiplication of Stacks 0FA0**: for `f : X' ⟶ X`,
`a ∈ A⁽ᵖ⁾(Z ⟶ X)` and `b ∈ A⁽ᑫ⁾(Z ⟶ X)`, `f^*(a b) = f^*a f^*b` in `A⁽ᵖ⁺ᑫ⁾(Z' ⟶ X')`. -/
theorem localizedGradingRestriction_localizedGradingMul {p q : ℕ}
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi q) :
    localizedGradingRestriction C sZ sX i hi f (localizedGradingMul C sZ sX i hi a b) =
      localizedGradingMul C _ _ _ rfl (localizedGradingRestriction C sZ sX i hi f a)
        (localizedGradingRestriction C sZ sX i hi f b) := by
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · rw [localizedGradingRestriction_fst, localizedGradingMul_fst, localizedGradingMul_fst, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chowCohomologyRestriction_bivariantClassDegreeCongr, chowCohomologyRestriction_mulId,
      chowCohomologyRestriction_localizedGradingPush,
      chowCohomologyRestriction_localizedGradingPush]
  · rw [localizedGradingRestriction_snd, localizedGradingMul_snd, localizedGradingMul_snd,
      supportedRestriction_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [supportedRestriction_bivariantClassDegreeCongr,
      supportedRestriction_localizedGradingHighTerm]

/-- Restriction commutes with the summands `aᵢ bⱼ` (`Stacks.Chow.localizedGradingTerm`) of the
components of degree `n ≥ p + q - 1` of a product. -/
theorem supportedRestriction_localizedGradingTerm {p q : ℕ}
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi q) {n : ℤ}
    (hn : ((p + q : ℕ) : ℤ) ≤ n + 1) (j : ℤ) :
    supportedRestriction C sZ sX i hi f (localizedGradingTerm C sZ sX i hi a b hn j) =
      localizedGradingTerm C _ _ _ rfl (localizedGradingRestriction C sZ sX i hi f a)
        (localizedGradingRestriction C sZ sX i hi f b) hn j := by
  by_cases hp : (p : ℤ) ≤ j
  · by_cases hq : (q : ℤ) ≤ n - j
    · rw [localizedGradingTerm_of_le_of_le _ _ _ hp hq,
        localizedGradingTerm_of_le_of_le _ _ _ hp hq, supportedRestriction_supportedMul]
      rfl
    · rw [localizedGradingTerm_of_le_of_lt _ _ _ hp (not_le.mp hq),
        localizedGradingTerm_of_le_of_lt _ _ _ hp (not_le.mp hq),
        supportedRestriction_supportedRightComp]
      rfl
  · have hq : (q : ℤ) ≤ n - j := by push_cast at hn; omega
    rw [localizedGradingTerm_of_lt _ _ _ (not_le.mp hp) hq,
      localizedGradingTerm_of_lt _ _ _ (not_le.mp hp) hq,
      supportedRestriction_ambientSupportedMul]
    rfl

/-- **Restriction commutes with the multiplication of Stacks 0FA0 with output cutoff `r`**: for
`f : X' ⟶ X`, `a ∈ A⁽ᵖ⁾(Z ⟶ X)`, `b ∈ A⁽ᑫ⁾(Z ⟶ X)` and `p + q ≤ r + 1`, `f^*(a b) = f^*a f^*b`
in `A⁽ʳ⁾(Z' ⟶ X')` (`Stacks.Chow.localizedGradingCutoffMul`). -/
theorem localizedGradingRestriction_localizedGradingCutoffMul {p q r : ℕ} (hr : p + q ≤ r + 1)
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) sZ sX i hi q) :
    localizedGradingRestriction C sZ sX i hi f (localizedGradingCutoffMul C sZ sX i hi r hr a b) =
      localizedGradingCutoffMul C _ _ _ rfl r hr (localizedGradingRestriction C sZ sX i hi f a)
        (localizedGradingRestriction C sZ sX i hi f b) := by
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · rw [localizedGradingRestriction_fst, localizedGradingCutoffMul_fst,
      localizedGradingCutoffMul_fst, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chowCohomologyRestriction_bivariantClassDegreeCongr, chowCohomologyRestriction_mulId,
      chowCohomologyRestriction_localizedGradingPush,
      chowCohomologyRestriction_localizedGradingPush]
  · rw [localizedGradingRestriction_snd, localizedGradingCutoffMul_snd,
      localizedGradingCutoffMul_snd, supportedRestriction_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [supportedRestriction_bivariantClassDegreeCongr, supportedRestriction_localizedGradingTerm]

/-- **Restriction of classes supported on `Z` along an envelope is injective** (Stacks 0GUC): it
is the restriction of Stacks 0F9Z along an envelope, read against an equal structure morphism. -/
theorem supportedRestriction_injective_of_isEnvelope (hf : IsEnvelope f) {p : ℤ} :
    Function.Injective (supportedRestriction C sZ sX i hi f (p := p)) := fun _ _ hab =>
  bivariantRestrictionAddHom_injective_of_isEnvelope' C _ sZ sX i hi f p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) hf
    ((bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.snd i f) _ rfl
      (hv := pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) (hv' := rfl) p).injective hab)

/-- **Restriction of the localized grading along an envelope is injective** (Stacks 0GUC): on
each component it is the restriction of Stacks 0B7F, resp. of Stacks 0F9Z, along an envelope. -/
theorem localizedGradingRestriction_injective_of_isEnvelope (hf : IsEnvelope f) {p : ℕ} :
    Function.Injective (localizedGradingRestriction C sZ sX i hi f (p := p)) := by
  intro a b hab
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · exact chowCohomologyRestriction_injective_of_isEnvelope C (gysinSystemOfInvertible C) sX f n.1
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) hf
      (congrFun (congrArg Prod.fst hab) n)
  · exact supportedRestriction_injective_of_isEnvelope hf (congrFun (congrArg Prod.snd hab) n)

end Stacks.Chow

end
