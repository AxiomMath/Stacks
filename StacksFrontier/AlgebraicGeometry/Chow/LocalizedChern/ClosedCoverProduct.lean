module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Pushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.WhitneyChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentExistence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter

/-!
# Products of classes supported on a closed subscheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. Stacks 0FA0 multiplies classes of
`A^*(X)` and of `A^*(Z ⟶ X)` by three maps:

* `A^p(Z ⟶ X) × A^q(X) ⟶ A^{p+q}(Z ⟶ X)`, `(c, d) ↦ c ∘ d`, composition of bivariant classes;
* `A^p(X) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)`, `(d, c) ↦ res(d) ∘ c`, restriction to `A^p(Z)`
  (Stacks 0B7F) followed by composition;
* `A^p(Z ⟶ X) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)`, `(c, c') ↦ res(c) ∘ c'`, with `res` the
  restriction map of Stacks 0FA1.

The second and third are both composition `A^p(Z) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)` after a
restriction to `A^p(Z)`. This file defines the two compositions and computes them on the test
schemes, and then computes them on the classes `a' ∈ A^*(X₂ ⟶ X)` extended from the second member
of a closed cover `X = X₁ ∪ X₂` (Stacks 0F9H, `Stacks.Chow.closedCoverExtension`): the
restriction of `a'` to `X₂` is `a`, the composition `b ∘ a'` for `b ∈ A^*(X₂)` is the extension
of `b a`, and `a' ∘ d` for `d ∈ A^*(X)` is the extension of `a d|_{X₂}`. These are the
computations behind the phrase "immediate from the characterization of the classes in
Lemma 0F9H" in the proofs of Stacks 0FAK, 0FAL and 0FAN.

## Main definitions

* `Stacks.Chow.supportedLeftComp` — the composition `A^p(Z) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)`.
* `Stacks.Chow.supportedRightComp` — the composition `A^p(Z ⟶ X) × A^q(X) ⟶ A^{p+q}(Z ⟶ X)`.

## Main results

* `Stacks.Chow.supportedLeftComp_cap`, `Stacks.Chow.supportedRightComp_cap` — the two
  compositions on the test schemes.
* `Stacks.Chow.closedImmersionChowCohomologyRestriction_idRule` — the operation of the restriction
  `res(c) ∈ A^p(Z)` of `c ∈ A^p(Z ⟶ X)` on a test scheme `T ⟶ Z` is that of `c` on `T ⟶ Z ⟶ X`.
* `Stacks.Chow.closedImmersionChowCohomologyRestriction_closedCoverExtension` —
  `res(a') = a`.
* `Stacks.Chow.supportedLeftComp_closedCoverExtension` — `b ∘ a' = (b a)'`.
* `Stacks.Chow.supportedRightComp_closedCoverExtension` — `a' ∘ d = (a d|_{X₂})'`.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of degrees through a pushforward -/

/-- Pushing forward a class transported along an equality of degrees is, up to that equality,
pushing forward the class. -/
theorem properChowPushforward_chowGroupDegreeEquiv_heq (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB] (u : A ⟶ B)
    [IsProper u] (hu : u ≫ sB = sA) {k l : ℤ} (hkl : k = l)
    (hfack : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacl : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu l)
    (x : chowGroup C sA k) :
    properChowPushforward C sA sB u hu l hfacl (chowGroupDegreeEquiv C sA hkl x) ≍
      properChowPushforward C sA sB u hu k hfack x := by
  subst hkl
  rfl

/-- The cap operation of a bivariant class at two equal test morphisms, on heterogeneously equal
classes, gives heterogeneously equal classes. -/
theorem BivariantClass.cap_heq_of_eq {C : ChowSituation.{u}} {G : GysinSystem C} {Z X : Scheme.{u}}
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {f : Z ⟶ X}
    [LocallyOfFiniteType f] {hf : f ≫ sX = sZ} {p : ℤ} (c : BivariantClass C G sZ sX f hf p)
    {T : Scheme.{u}}
    {m m' : T ⟶ X} [LocallyOfFiniteType m] [LocallyOfFiniteType m'] (hm : m = m') (k : ℤ)
    {x : chowGroup C (m ≫ sX) k} {x' : chowGroup C (m' ≫ sX) k} (hx : x ≍ x') :
    c.cap m k x ≍ c.cap m' k x' := by
  subst hm
  obtain rfl := eq_of_heq hx
  rfl

/-- Pushing forward from the base changes of a morphism along two equal test morphisms, along
morphisms compatible with the comparison of the base changes, gives heterogeneously equal classes
on heterogeneously equal classes. -/
theorem chowPush_pullback_heq_of_test_eq (C : ChowSituation.{u}) {Z X T B : Scheme.{u}}
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {sB : B ⟶ C.S} [LocallyOfFiniteType sB] (f : Z ⟶ X)
    [LocallyOfFiniteType f] {m m' : T ⟶ X} [LocallyOfFiniteType m] [LocallyOfFiniteType m']
    (hm : m = m') (u : pullback f m ⟶ B) [IsProper u] (u' : pullback f m' ⟶ B)
    [IsProper u'] (hu : u ≫ sB = pullback.fst f m ≫ sZ) (hu' : u' ≫ sB = pullback.fst f m' ≫ sZ)
    (huu' : (pullback.congrHom rfl hm).hom ≫ u' = u) (k : ℤ)
    {x : chowGroup C (pullback.fst f m ≫ sZ) k} {x' : chowGroup C (pullback.fst f m' ≫ sZ) k}
    (hx : x ≍ x') :
    chowPush C _ sB u hu k x ≍ chowPush C _ sB u' hu' k x' := by
  subst hm
  obtain rfl := eq_of_heq hx
  obtain rfl : u = u' := by simpa using huu'.symm
  rfl

/-! ### The two compositions -/

/-- The cap operation of a composite at the first Chern class Gysin system, read for an equal
morphism, is up to the equality of degrees the proper pushforward along the associativity
isomorphism of the two successive caps, followed by the comparison of the base changes. -/
private theorem congrHom_bivariantCompositeOfInvertible_cap_heq (C : ChowSituation.{u})
    {X Y Z T : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] {f' : X ⟶ Z}
    [LocallyOfFiniteType f'] (hff : f ≫ g = f') (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
    (hf' : f' ≫ sZ = sX) {p q : ℤ} (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) (t : T ⟶ Z)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    ((bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b).congrHom hff hf').cap t k α ≍
      properChowPushforward C (pullback.fst (f ≫ g) t ≫ sX) (pullback.fst f' t ≫ sX)
        (pullback.congrHom hff rfl).hom (pullback_congrHom_hom_comp_fst_comp hff t)
        ((k - q) - p) (properPushforwardDescends C _ _ _ _ _)
        (properChowPushforward C (pullback.fst f (pullback.fst g t) ≫ sX)
          (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
          (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) ((k - q) - p)
          (properPushforwardDescends C _ _ _ _ _)
          (a.cap (pullback.fst g t) (k - q) (b.cap t k α))) := by
  rw [BivariantClass.congrHom_cap]
  exact properChowPushforward_chowGroupDegreeEquiv_heq C _ _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) _ _

section Composition

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Z ⟶ X) [LocallyOfFiniteType f]
  (hf : f ≫ sX = sZ) {p q : ℤ}

/-- **The composition `A^p(Z) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)`** of Stacks 0B75, along
`𝟙 Z ≫ f = f`, at the Gysin system of the first Chern class rule. Precomposed with the restriction
maps `A^p(X) ⟶ A^p(Z)` of Stacks 0B7F and `A^p(Z ⟶ X) ⟶ A^p(Z)` of Stacks 0FA1, it gives the
second and third multiplications of Stacks 0FA0. -/
def supportedLeftComp
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf (p + q) :=
  (bivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) f (Category.id_comp sZ) hf p q b c).congrHom
    (Category.id_comp f) hf

/-- **The composition `A^p(Z ⟶ X) × A^q(X) ⟶ A^{p+q}(Z ⟶ X)`** of Stacks 0B75, along
`f ≫ 𝟙 X = f`, at the Gysin system of the first Chern class rule: the first multiplication of
Stacks 0FA0. -/
def supportedRightComp
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf (p + q) :=
  (bivariantCompositeOfInvertible C sZ sX sX f (𝟙 X) hf (Category.id_comp sX) p q c d).congrHom
    (Category.comp_id f) hf

variable [IsClosedImmersion f] in
/-- **The third multiplication `A^p(Z ⟶ X) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)` of Stacks 0FA0**,
for a closed immersion `f`: `(c, c') ↦ res(c) ∘ c'`, with `res : A^p(Z ⟶ X) ⟶ A^p(Z)` the
restriction map of Stacks 0FA1. -/
def supportedMul (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf (p + q) :=
  supportedLeftComp C sZ sX f hf
    (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Z) hf hf p
      (closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) sZ sX f hf p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c)) c'

/-- **The second multiplication `A^p(X) × A^q(Z ⟶ X) ⟶ A^{p+q}(Z ⟶ X)` of Stacks 0FA0**:
`(d, c) ↦ res(d) ∘ c`, with `res : A^p(X) ⟶ A^p(Z)` the restriction map of Stacks 0B7F. -/
def ambientSupportedMul (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf (p + q) :=
  supportedLeftComp C sZ sX f hf
    (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Z) hf hf p
      (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)) c

/-- **The composition `b ∘ c`, on the test schemes.** On a test scheme `t : T ⟶ X`, the cap
operation of `b ∘ c` is the cap operation of `c` followed by the operation of `b` on the test
scheme `Z ×_X T ⟶ Z`; the two sides lie in the Chow groups of degrees `k - (p + q)` and
`(k - q) - p`. -/
theorem supportedLeftComp_cap
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf q) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (supportedLeftComp C sZ sX f hf b c).cap t k α ≍
      b.idRule C sZ (gysinSystemOfInvertible C) (pullback.fst f t) (k - q) (c.cap t k α) := by
  refine (congrHom_bivariantCompositeOfInvertible_cap_heq C _ _ _ _ _ _ _ _ _ b c _ k α).trans
    (heq_of_eq ?_)
  rw [BivariantClass.idRule_apply]
  have hmor : (pullbackRightPullbackFstIso f t (𝟙 Z)).hom ≫
      (pullback.congrHom (Category.id_comp f) rfl).hom = pullback.snd (𝟙 Z) (pullback.fst f t) :=
    pullback.hom_ext (by simp [← pullback.condition]) (by simp)
  exact (properChowPushforward_comp_apply C _ _ _ _ _ _ rfl _ _
    (by rw [hmor]; exact pullbackSnd_comp_structureMorphism (Category.id_comp sZ) _) _
    (properPushforwardDescends C _ _ _ _ _) _ (properPushforwardDescends C _ _ _ _ _) _).symm.trans
    (congrFun (congrArg DFunLike.coe (properChowPushforward_congr C _ _ _ _ hmor _ _ _
      (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _))) _)

/-- **The composition `c ∘ d`, on the test schemes.** On a test scheme `t : T ⟶ X`, the cap
operation of `c ∘ d` is the operation of `d ∈ A^q(X)` on `T` followed by the cap operation of `c`;
the two sides lie in the Chow groups of degrees `k - (p + q)` and `(k - q) - p`. -/
theorem supportedRightComp_cap
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX f hf p)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (supportedRightComp C sZ sX f hf c d).cap t k α ≍
      c.cap t (k - q) (d.idRule C sX (gysinSystemOfInvertible C) t k α) := by
  refine (congrHom_bivariantCompositeOfInvertible_cap_heq C _ _ _ _ _ _ _ _ _ c d _ k α).trans ?_
  rw [BivariantClass.idRule_apply]
  set h := pullback.snd (𝟙 X) t
  have hg' : pullback.fst (𝟙 X) t = h ≫ t := by
    simpa only [Category.comp_id] using (pullback.condition : pullback.fst (𝟙 X) t ≫ 𝟙 X = h ≫ t)
  have hs : pullback.fst (𝟙 X) t ≫ sX = (h ≫ t) ≫ sX := by rw [hg']
  set y := d.cap t k α
  have hpush : pullbackSndPush C sX (Category.id_comp sX) t (k - q) y =
      properChowPushforward C ((h ≫ t) ≫ sX) (t ≫ sX) h (by simp [Category.assoc]) (k - q)
        (properPushforwardDescends C _ _ _ _ _) (chowGroupCongr C hs (k - q) y) :=
    eq_of_heq (properChowPushforward_heq_congr_base C h hs rfl _ _ rfl
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) _ _ (chowGroupCongr_heq C hs (k - q) y).symm)
  rw [hpush, c.proper_naturality t h (bivariantBaseChangeMap f t h)
    (isPullback_bivariantBaseChangeMap f t h) (bivariantBaseChangeMap_fst f t h) (k - q)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  rw [← properChowPushforward_comp_apply C _ _ _ _ _ _ rfl _ _
    (by rw [Category.assoc, pullback_congrHom_hom_comp_fst_comp,
      pullbackRightPullbackFstIso_hom_comp_fst_comp]) _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)]
  refine chowPush_pullback_heq_of_test_eq C f hg' _ _ _ _ ?_ (k - q - p)
    (c.cap_heq_of_eq hg' (k - q) (chowGroupCongr_heq C hs (k - q) y).symm)
  refine pullback.hom_ext ?_ ?_
  · simp [bivariantBaseChangeMap]
  · simp [bivariantBaseChangeMap, h]

end Composition

/-! ### The restriction of a class supported on a closed subscheme, on the test schemes -/

section Restriction

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) {p : ℤ}

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [IsClosedImmersion i] in
include hi in
/-- The base change `Z ×_X T ⟶ T` of `i` along `g ≫ i` lies over the base. -/
theorem pullbackSnd_comp_comp_structureMorphism {T : Scheme.{u}} (g : T ⟶ Z) :
    pullback.snd i (g ≫ i) ≫ (g ≫ (i ≫ sX)) = pullback.fst i (g ≫ i) ≫ sZ := by
  calc pullback.snd i (g ≫ i) ≫ (g ≫ (i ≫ sX)) = (pullback.snd i (g ≫ i) ≫ (g ≫ i)) ≫ sX := by
        simp only [Category.assoc]
    _ = (pullback.fst i (g ≫ i) ≫ i) ≫ sX := by rw [pullback.condition]
    _ = pullback.fst i (g ≫ i) ≫ sZ := by rw [Category.assoc, hi]

/-- **Stacks 0FA1, on the test schemes.** The operation of the restriction `res(c) ∈ A^p(Z)` of a
class `c ∈ A^p(Z ⟶ X)` on a test scheme `g : T ⟶ Z` is the cap operation of `c` on the test
scheme `g ≫ i : T ⟶ X`, pushed forward along the isomorphism `Z ×_X T ⟶ T`. -/
theorem closedImmersionChowCohomologyRestriction_idRule
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p) {T : Scheme.{u}}
    (g : T ⟶ Z) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (i ≫ sX)) k) :
    (closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) sZ sX i hi p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).idRule C (i ≫ sX)
        (gysinSystemOfInvertible C) g k α =
      chowPush C (pullback.fst i (g ≫ i) ≫ sZ) (g ≫ (i ≫ sX)) (pullback.snd i (g ≫ i))
        (pullbackSnd_comp_comp_structureMorphism C sZ sX i hi g) (k - p)
        (c.cap (g ≫ i) k (chowGroupCongr C (Category.assoc g i sX).symm k α)) := by
  have hκbase := transportPullbackIso_hom_comp_base C (pullback.fst i i ≫ sZ) (i ≫ sX) (i ≫ sX)
    (pullback.snd i i) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi i) (𝟙 Z)
    (Category.id_comp (i ≫ sX)) (asIso (pullback.snd i i)) (by simp) g
  have hcap : (closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) sZ sX i hi p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).cap g k α =
      chowPushforwardOfIso C
        (pullback.fst (pullback.snd i i) g ≫ (pullback.fst i i ≫ sZ))
        (pullback.fst (𝟙 Z) g ≫ (i ≫ sX))
        (transportPullbackIso (pullback.snd i i) (𝟙 Z) (asIso (pullback.snd i i)) (by simp)
          g).hom hκbase (k - p)
        (bivariantRestrictionCap C (gysinSystemOfInvertible C) sZ sX i hi i p c g k α) :=
    rfl
  rw [BivariantClass.idRule_apply, hcap, bivariantRestrictionCap_apply]
  simp only [pullbackSndPush, chowPushforwardOfIso]
  have hw₁ : ((transportPullbackIso (pullback.snd i i) (𝟙 Z) (asIso (pullback.snd i i))
      (by simp) g).hom ≫ pullback.snd (𝟙 Z) g) ≫ (g ≫ (i ≫ sX)) =
      pullback.fst (pullback.snd i i) g ≫ (pullback.fst i i ≫ sZ) := by
    rw [Category.assoc, pullbackSnd_comp_structureMorphism (Category.id_comp _) g, hκbase]
  rw [← properChowPushforward_comp_apply C _ _ _ _ _ _ rfl _ _ hw₁ _ _ _
      (properPushforwardDescends C _ _ _ _ _)]
  have hw₂ : ((pullbackLeftPullbackSndIso i i g).inv ≫
      (transportPullbackIso (pullback.snd i i) (𝟙 Z) (asIso (pullback.snd i i)) (by simp) g).hom ≫
        pullback.snd (𝟙 Z) g) ≫ (g ≫ (i ≫ sX)) = pullback.fst i (g ≫ i) ≫ sZ := by
    rw [Category.assoc, hw₁]
    simp
  rw [← properChowPushforward_comp_apply C _ _ _ _ _ _ rfl _ _ hw₂ _ _ _
      (properPushforwardDescends C _ _ _ _ _)]
  refine congrFun (congrArg DFunLike.coe (properChowPushforward_congr C _ _ _ _ ?_ _ _ _
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _))) _
  simp [transportPullbackIso]

end Restriction

/-! ### Components of products of total classes -/

section TotalComponents

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **A component of a product with a homogeneous part.** The degree-`m` component of
`c_i · Q`, for `c_i` the degree-`i` part of `c` and `i + j = m`, is the product
`c_i Q_j ∈ A^{i+j}(Y)` read in degree `m`. -/
theorem TotalChowClass.homPart_mul_apply (c Q : TotalChowClass C sY) {i j m : ℕ}
    (h : i + j = m) :
    (TotalChowClass.homComponent i c * Q) m =
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY)
        (by rw [← h]; push_cast; rfl) ((c i).mulId C sY (Q j)) := by
  rw [TotalChowClass.mul_apply, Finset.sum_eq_single j]
  · have hk : m - j = i := by omega
    subst hk
    rw [TotalChowClass.mulTerm, dite_eq_left (by omega), TotalChowClass.homComponent_apply,
      ite_eq_left rfl]
  · intro k hk hkj
    rw [TotalChowClass.mulTerm]
    split_ifs with hkm
    · rw [TotalChowClass.homComponent_apply, ite_eq_right (by omega), BivariantClass.zero_mulId,
        map_zero]
    · rfl
  · intro hj
    exact absurd (Finset.mem_range.mpr (by omega)) hj

end TotalComponents

/-! ### Classes extended from one member of a closed cover -/

section Extension

variable (C : ChowSituation.{u}) {X X₁ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) [IsClosedImmersion i₁]
  [IsClosedImmersion i₂] {p : ℤ}

/-- **The restriction of an extension.** For `a ∈ A^p(X₂)` vanishing over `X₁ ×_X X₂`, the
restriction (Stacks 0FA1) of its extension `a' ∈ A^p(X₂ ⟶ X)` along the closed cover
`X = X₁ ∪ X₂` (Stacks 0F9H) is `a`. -/
theorem closedImmersionChowCohomologyRestriction_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    closedImmersionChowCohomologyRestriction C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) = a := by
  refine BivariantClass.eq_of_idRule_eq C (i₂ ≫ sX) _ _ _ fun {T} g _ k α ↦ ?_
  have hm : g ≫ i₂ = 𝟙 T ≫ (g ≫ i₂) := (Category.id_comp _).symm
  have hα : chowGroupCongr C (Category.assoc g i₂ sX).symm k α =
      chowPush C (g ≫ (i₂ ≫ sX)) ((g ≫ i₂) ≫ sX) (𝟙 T)
        (by rw [← Category.assoc, ← hm, Category.assoc]) k α :=
    (chowPush_id_eq_chowGroupCongr C _ _ _ k α).symm
  rw [closedImmersionChowCohomologyRestriction_idRule, closedCoverExtension_cap, hα,
    closedCoverExtensionCap_chowPush_second C _ sX i₁ i₂ (i₂ ≫ sX) rfl hcover ha (g ≫ i₂) (𝟙 T) g
      hm k α, chowPush_comp C _ _ _ _ _ (𝟙 T) (pullback.lift_snd _ _ _) _ _ (Category.id_comp _),
    chowPush_id]

/-- A class vanishes over `z : W ⟶ Z` as soon as its operation on every test scheme factoring
through `z` vanishes. -/
private theorem vanishesOver_of_idRule_eq_zero {Z W : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {z : W ⟶ Z} [LocallyOfFiniteType z] {q : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ q}
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ)
      (x : chowGroup C ((t ≫ z) ≫ sZ) k),
      a.idRule C sZ (gysinSystemOfInvertible C) (t ≫ z) k x = 0) :
    BivariantClass.VanishesOver a z := fun t _ k α ↦
  chowPushforwardOfIso_injective C _ _ _ _ (k - q) ((h t k α).trans (map_zero _).symm)

/-- If `a ∈ A^q(Z)` vanishes over `z : W ⟶ Z`, so does `b a` for every `b ∈ A^p(Z)`. -/
theorem BivariantClass.VanishesOver.mulId_left {Z W : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {z : W ⟶ Z} [LocallyOfFiniteType z] {q : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ q}
    (ha : BivariantClass.VanishesOver a z)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p) :
    BivariantClass.VanishesOver (b.mulId C sZ a) z := by
  refine vanishesOver_of_idRule_eq_zero C fun {T} t _ k α ↦ ?_
  have h := BivariantClass.idRule_mulId C sZ b a (t ≫ z) k α
  rw [ha.idRule_eq_zero t (t ≫ z) rfl k α, map_zero] at h
  exact chowGroup_eq_zero_of_heq_zero C (by ring) h

/-- If `a ∈ A^p(Z)` vanishes over `z : W ⟶ Z`, so does `a e` for every `e ∈ A^q(Z)`. -/
theorem BivariantClass.VanishesOver.mulId_right {Z W : Scheme.{u}} {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {z : W ⟶ Z} [LocallyOfFiniteType z] {q : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p}
    (ha : BivariantClass.VanishesOver a z)
    (e : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ q) :
    BivariantClass.VanishesOver (a.mulId C sZ e) z := by
  refine vanishesOver_of_idRule_eq_zero C fun {T} t _ k α ↦ ?_
  have h := BivariantClass.idRule_mulId C sZ a e (t ≫ z) k α
  rw [ha.idRule_eq_zero t (t ≫ z) rfl (k - q)] at h
  exact chowGroup_eq_zero_of_heq_zero C (by ring) h

/-- **Composition with an extension on the left.** For `b ∈ A^p(X₂)` and `a ∈ A^q(X₂)` vanishing
over `X₁ ×_X X₂`, the composition `b ∘ a'` of `b` with the extension of `a` is the extension of
`b a`. With `b` the restriction of a class of `A^p(X)` or of `A^p(X₂ ⟶ X)` (Stacks 0B7F, 0FA1)
this computes the second and third multiplications of Stacks 0FA0 on extensions. -/
theorem supportedLeftComp_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {q : ℤ}
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p)
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) q}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂)) :
    supportedLeftComp C (i₂ ≫ sX) sX i₂ rfl b
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) =
      closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (b.mulId C (i₂ ≫ sX) a) hcover
        (ha.mulId_left C b) := by
  refine IsClosedCoverExtension.eq_closedCoverExtension hcover _
    ⟨fun {T} g _ k α ↦ ?_, fun {T} g _ k α ↦ ?_⟩
  · refine eq_of_heq ((supportedLeftComp_cap C _ sX i₂ rfl b _ g k _).trans ?_)
    rw [closedCoverExtension_cap_second]
    exact (BivariantClass.idRule_mulId C _ b a _ k α).symm
  · have h := supportedLeftComp_cap C _ sX i₂ rfl b
      (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) g k
      (chowPush C _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism rfl g) k α)
    rw [closedCoverExtension_cap_first, map_zero] at h
    exact chowGroup_eq_zero_of_heq_zero C (by ring) h

/-- **Composition with an extension on the right.** For `a ∈ A^p(X₂)` vanishing over
`X₁ ×_X X₂` and `d ∈ A^q(X)`, the composition `a' ∘ d` of the extension of `a` with `d` (the first
multiplication of Stacks 0FA0) is the extension of `a d|_{X₂}`, with `d|_{X₂}` the restriction of
Stacks 0B7F. -/
theorem supportedRightComp_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {q : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    supportedRightComp C (i₂ ≫ sX) sX i₂ rfl
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) d =
      closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
        (a.mulId C (i₂ ≫ sX) (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ q
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d)) hcover
        (ha.mulId_right C _) := by
  refine IsClosedCoverExtension.eq_closedCoverExtension hcover _
    ⟨fun {T} g _ k α ↦ ?_, fun {T} g _ k α ↦ ?_⟩
  · refine eq_of_heq ((supportedRightComp_cap C _ sX i₂ rfl _ d g k _).trans ?_)
    rw [BivariantClass.idRule_chowPush_of_eq d g (pullback.snd i₂ g) (pullback.fst i₂ g ≫ i₂)
      pullback.condition.symm (pullback.fst i₂ g ≫ (i₂ ≫ sX)) (Category.assoc _ _ _),
      ← chowCohomologyRestriction_idRule, closedCoverExtension_cap_second]
    refine HEq.trans (heq_of_eq (congrArg _ (eq_of_heq (chowGroupCongr_heq C _ (k - q) _))))
      (BivariantClass.idRule_mulId C _ a _ _ k α).symm
  · have h := supportedRightComp_cap C _ sX i₂ rfl
      (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) d g k
      (chowPush C _ _ (pullback.snd i₁ g) (pullbackSnd_comp_structureMorphism rfl g) k α)
    rw [BivariantClass.idRule_chowPush_of_eq d g (pullback.snd i₁ g) (pullback.fst i₁ g ≫ i₁)
      pullback.condition.symm (pullback.fst i₁ g ≫ (i₁ ≫ sX)) (Category.assoc _ _ _),
      closedCoverExtension_cap_first] at h
    exact chowGroup_eq_zero_of_heq_zero C (by ring) h

/-- The extension of a class transported along an equality of degrees is the transport of the
extension. -/
theorem closedCoverExtension_bivariantClassDegreeCongr
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {q : ℤ} (h : p = q)
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (ha' : BivariantClass.VanishesOver
      (bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX) (𝟙 X₂) (Category.id_comp _) h a)
      (pullback.snd i₁ i₂)) :
    closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
        (bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX) (𝟙 X₂) (Category.id_comp _) h a)
        hcover ha' =
      bivariantClassDegreeCongr C _ (i₂ ≫ sX) sX i₂ rfl h
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha) := by
  subst h
  rfl

/-- **The third multiplication of Stacks 0FA0 on extensions.** For `a ∈ A^p(X₂)` and
`b ∈ A^q(X₂)` vanishing over `X₁ ×_X X₂`, the product `res(a') ∘ b'` of their extensions along
the closed cover `X = X₁ ∪ X₂` is the extension of `a b`. -/
theorem supportedMul_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {q : ℤ}
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) q}
    (hb : BivariantClass.VanishesOver b (pullback.snd i₁ i₂)) :
    supportedMul C (i₂ ≫ sX) sX i₂ rfl
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl a hcover ha)
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl b hcover hb) =
      closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (a.mulId C (i₂ ≫ sX) b) hcover
        (hb.mulId_left C a) := by
  rw [supportedMul, closedImmersionChowCohomologyRestriction_closedCoverExtension]
  exact supportedLeftComp_closedCoverExtension C sX i₁ i₂ hcover a hb

/-- **The second multiplication of Stacks 0FA0 on extensions.** For `d ∈ A^p(X)` and `b ∈ A^q(X₂)`
vanishing over `X₁ ×_X X₂`, the product `res(d) ∘ b'` is the extension of `d|_{X₂} b`. -/
theorem ambientSupportedMul_closedCoverExtension
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ) {q : ℤ}
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) q}
    (hb : BivariantClass.VanishesOver b (pullback.snd i₁ i₂)) :
    ambientSupportedMul C (i₂ ≫ sX) sX i₂ rfl d
        (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl b hcover hb) =
      closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl
        ((chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d).mulId C (i₂ ≫ sX) b) hcover
        (hb.mulId_left C _) :=
  supportedLeftComp_closedCoverExtension C sX i₁ i₂ hcover _ hb

/-- Extensions are stable under integer multiples. -/
theorem IsClosedCoverExtension.zsmul {G : GysinSystem C} {sX₂ : X₂ ⟶ C.S}
    [LocallyOfFiniteType sX₂] {hi₂ : i₂ ≫ sX = sX₂} {a : chowCohomologyComponent C G sX₂ p}
    {c : BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c) (n : ℤ) :
    IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ (n • a) (n • c) := by
  induction n using Int.induction_on with
  | zero => simpa using IsClosedCoverExtension.zero
  | succ n ih => simpa [add_smul] using ih.add hc
  | pred n ih =>
    rw [sub_smul, one_smul, sub_eq_add_neg, sub_smul, one_smul, sub_eq_add_neg]
    exact ih.add hc.neg

/-- Extensions are stable under finite sums. -/
theorem IsClosedCoverExtension.sum {G : GysinSystem C} {sX₂ : X₂ ⟶ C.S}
    [LocallyOfFiniteType sX₂] {hi₂ : i₂ ≫ sX = sX₂} {ι : Type*} (s : Finset ι)
    {a : ι → chowCohomologyComponent C G sX₂ p} {c : ι → BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : ∀ t ∈ s, IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ (a t) (c t)) :
    IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ (∑ t ∈ s, a t) (∑ t ∈ s, c t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsClosedCoverExtension.zero
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht]
    exact (hc t (Finset.mem_insert_self t s)).add
      (ih fun t' ht' => hc t' (Finset.mem_insert_of_mem ht'))

/-- Extensions are stable under transport along an equality of degrees. -/
theorem IsClosedCoverExtension.bivariantClassDegreeCongr {G : GysinSystem C} {sX₂ : X₂ ⟶ C.S}
    [LocallyOfFiniteType sX₂] {hi₂ : i₂ ≫ sX = sX₂} {q : ℤ} (h : p = q)
    {a : chowCohomologyComponent C G sX₂ p} {c : BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c) :
    IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂
      (Stacks.Chow.bivariantClassDegreeCongr C G sX₂ sX₂ (𝟙 X₂) (Category.id_comp _) h a)
      (Stacks.Chow.bivariantClassDegreeCongr C G sX₂ sX i₂ hi₂ h c) := by
  subst h
  exact hc

omit [LocallyOfFiniteType sX] [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- The degrees of the summands of Newton's recursion. -/
theorem newton_degree_eq {j q : ℕ} (h : j < q) :
    (((j + 1 : ℕ) : ℤ) + ((q - j : ℕ) : ℤ)) = ((q + 1 : ℕ) : ℤ) := by
  push_cast
  omega

/-- **Newton's recursion for extended classes (the generic form of Stacks 0FAK).** Let `c` be a
total class on `X₂` and `P` a sequence of total classes on `X₂` satisfying Newton's recursion
(`Stacks.Chow.TotalChowClass.IsNewtonPowerSums`), with every component `c_i` for `i ≥ 1` and
every `P_p ∈ A^p` vanishing over `X₁ ×_X X₂`. Then their extensions `c'_i`,
`P'_p ∈ A^*(X₂ ⟶ X)` along the closed cover `X = X₁ ∪ X₂` satisfy Newton's recursion with
the multiplication of Stacks 0FA0:
`P'_{p+1} = ∑_{j < p} (-1)^j c'_{j+1} P'_{p-j} + (-1)^p (p + 1) c'_{p+1}`. -/
theorem closedCoverExtension_isNewtonPowerSums
    (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {c : TotalChowClass C (i₂ ≫ sX)} {P : ℕ → TotalChowClass C (i₂ ≫ sX)}
    (hN : TotalChowClass.IsNewtonPowerSums c P)
    (hc : ∀ i, 0 < i → BivariantClass.VanishesOver (c i) (pullback.snd i₁ i₂))
    (hP : ∀ q, BivariantClass.VanishesOver (P q q) (pullback.snd i₁ i₂)) (q : ℕ) :
    closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (P (q + 1) (q + 1)) hcover (hP (q + 1)) =
      ∑ j ∈ (Finset.range q).attach, ((-1 : ℤ) ^ (j : ℕ)) •
          Stacks.Chow.bivariantClassDegreeCongr C _ (i₂ ≫ sX) sX i₂ rfl
            (newton_degree_eq (Finset.mem_range.mp j.2))
            (supportedMul C (i₂ ≫ sX) sX i₂ rfl
              (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (c ((j : ℕ) + 1)) hcover
                (hc _ (Nat.succ_pos _)))
              (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (P (q - j) (q - j)) hcover
                (hP _))) +
        ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) •
          closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (c (q + 1)) hcover
            (hc _ (Nat.succ_pos _)) := by
  refine (IsClosedCoverExtension.eq_closedCoverExtension hcover (hP (q + 1)) ?_).symm
  have key := congrArg (fun x : TotalChowClass C (i₂ ≫ sX) => x (q + 1)) (hN q)
  simp only [TotalChowClass.add_apply, TotalChowClass.sum_apply] at key
  have hterm : ∀ j : Finset.range q,
      (((-1 : ℤ) ^ (j : ℕ)) • (TotalChowClass.homComponent ((j : ℕ) + 1) c * P (q - j))) (q + 1) =
        ((-1 : ℤ) ^ (j : ℕ)) • Stacks.Chow.bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX)
          (𝟙 X₂) (Category.id_comp _) (newton_degree_eq (Finset.mem_range.mp j.2))
          ((c ((j : ℕ) + 1)).mulId C (i₂ ≫ sX) (P (q - j) (q - j))) := fun j => by
    have hj := Finset.mem_range.mp j.2
    change ((-1 : ℤ) ^ (j : ℕ)) •
      (TotalChowClass.homComponent ((j : ℕ) + 1) c * P (q - j)) (q + 1) = _
    rw [TotalChowClass.homPart_mul_apply C (i₂ ≫ sX) c (P (q - j))
      (by omega : (j : ℕ) + 1 + (q - j) = q + 1)]
  have hlast : (((-1 : ℤ) ^ q * ((q : ℤ) + 1)) • TotalChowClass.homComponent (q + 1) c) (q + 1) =
      ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) • c (q + 1) := by
    change ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) • (TotalChowClass.homComponent (q + 1) c) (q + 1) = _
    rw [TotalChowClass.homComponent_apply, ite_eq_left rfl]
  rw [← Finset.sum_attach, Finset.sum_congr rfl fun j _ => hterm j, hlast] at key
  rw [key]
  refine IsClosedCoverExtension.add (IsClosedCoverExtension.sum C sX i₁ i₂ _ fun j _ => ?_)
    ((isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover _).zsmul
      C sX i₁ i₂ _)
  refine IsClosedCoverExtension.zsmul C sX i₁ i₂ ?_ _
  refine IsClosedCoverExtension.bivariantClassDegreeCongr C sX i₁ i₂ _ ?_
  rw [supportedMul_closedCoverExtension]
  exact isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover _

omit [LocallyOfFiniteType sX] [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- The degrees of the summands of the twisting formula. -/
theorem twist_degree_eq {i j : ℕ} (h : j < i) :
    (((i - j : ℕ) : ℤ) + ((j : ℕ) : ℤ)) = ((i : ℕ) : ℤ) := by
  omega

/-- **The twisting formula for extended classes (the generic form of Stacks 0FAN).** Let `a`, `c`
be total classes on `X₂` and `x` a total class on `X` such that, in degree `i`,
`a_i = ∑_{j ≤ i} binom(r - i + j, j) (c_{i-j} (x|_{X₂})^j)_i`, where the coefficient of the term
`j = i` vanishes, and where the components `c_k` for `k ≥ 1` and `a_i` vanish over `X₁ ×_X X₂`.
Then the extensions along the closed cover `X = X₁ ∪ X₂` satisfy
`a'_i = ∑_{j < i} binom(r - i + j, j) c'_{i-j} (x^j)_j`, the product being the first
multiplication `A^{i-j}(X₂ ⟶ X) × A^j(X) ⟶ A^i(X₂ ⟶ X)` of Stacks 0FA0. -/
theorem closedCoverExtension_twist (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {a c : TotalChowClass C (i₂ ≫ sX)} {x : TotalChowClass C sX} (r : ℤ) (i : ℕ)
    (ha : a i = ∑ j ∈ Finset.range (i + 1), Ring.choose (r - i + j) j •
      (TotalChowClass.homComponent (i - j) c * TotalChowClass.res i₂ rfl x ^ j) i)
    (hchoose : Ring.choose (r - i + i) i = 0)
    (hc : ∀ k, 1 ≤ k → BivariantClass.VanishesOver (c k) (pullback.snd i₁ i₂))
    (hai : BivariantClass.VanishesOver (a i) (pullback.snd i₁ i₂)) :
    closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (a i) hcover hai =
      ∑ j ∈ (Finset.range i).attach, Ring.choose (r - i + (j : ℕ)) (j : ℕ) •
        Stacks.Chow.bivariantClassDegreeCongr C _ (i₂ ≫ sX) sX i₂ rfl
          (twist_degree_eq (Finset.mem_range.mp j.2))
          (supportedRightComp C (i₂ ≫ sX) sX i₂ rfl
            (closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl (c (i - j)) hcover
              (hc _ (by have := Finset.mem_range.mp j.2; omega)))
            ((x ^ (j : ℕ)) (j : ℕ))) := by
  refine (IsClosedCoverExtension.eq_closedCoverExtension hcover hai ?_).symm
  have hterm : ∀ j : Finset.range i,
      (Ring.choose (r - i + (j : ℕ)) (j : ℕ) •
        (TotalChowClass.homComponent (i - j) c * TotalChowClass.res i₂ rfl x ^ (j : ℕ)) i) =
      Ring.choose (r - i + (j : ℕ)) (j : ℕ) •
        Stacks.Chow.bivariantClassDegreeCongr C _ (i₂ ≫ sX) (i₂ ≫ sX) (𝟙 X₂)
          (Category.id_comp _) (twist_degree_eq (Finset.mem_range.mp j.2))
          ((c (i - j)).mulId C (i₂ ≫ sX)
            (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX i₂ (j : ℕ)
              (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) ((x ^ (j : ℕ)) (j : ℕ)))) :=
    fun j => by
    have hj := Finset.mem_range.mp j.2
    rw [TotalChowClass.homPart_mul_apply C (i₂ ≫ sX) c _ (by omega : i - j + (j : ℕ) = i),
      ← map_pow, TotalChowClass.res_rfl_apply]
  have hlast : Ring.choose (r - i + i) i •
      (TotalChowClass.homComponent (i - i) c * TotalChowClass.res i₂ rfl x ^ i) i = 0 := by
    rw [hchoose, zero_smul]
  rw [Finset.sum_range_succ, hlast, add_zero, ← Finset.sum_attach,
    Finset.sum_congr rfl fun j _ => hterm j] at ha
  rw [ha]
  refine IsClosedCoverExtension.sum C sX i₁ i₂ _ fun j _ => ?_
  refine IsClosedCoverExtension.zsmul C sX i₁ i₂ ?_ _
  refine IsClosedCoverExtension.bivariantClassDegreeCongr C sX i₁ i₂ _ ?_
  rw [supportedRightComp_closedCoverExtension]
  exact isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover _

/-- Extensions are stable under differences. -/
theorem IsClosedCoverExtension.sub {G : GysinSystem C} {sX₂ : X₂ ⟶ C.S}
    [LocallyOfFiniteType sX₂] {hi₂ : i₂ ≫ sX = sX₂} {a b : chowCohomologyComponent C G sX₂ p}
    {c d : BivariantClass C G sX₂ sX i₂ hi₂ p}
    (hc : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ a c)
    (hd : IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ b d) :
    IsClosedCoverExtension C G sX i₁ i₂ sX₂ hi₂ (a - b) (c - d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hc.add hd.neg

/-- Vanishing is preserved by transport along an equality of degrees. -/
theorem BivariantClass.VanishesOver.bivariantClassDegreeCongr {Z W : Scheme.{u}}
    {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {z : W ⟶ Z} [LocallyOfFiniteType z] {q : ℤ}
    (h : p = q) {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p}
    (ha : BivariantClass.VanishesOver a z) :
    BivariantClass.VanishesOver
      (Stacks.Chow.bivariantClassDegreeCongr C _ sZ sZ (𝟙 Z) (Category.id_comp _) h a) z := by
  subst h
  exact ha

/-- **The third multiplication of Stacks 0FA0 on extensions, through the characterization.** If
`c`, `d ∈ A^*(X₂ ⟶ X)` extend `a`, `b ∈ A^*(X₂)`, with `b` vanishing over `X₁ ×_X X₂`, then
`res(c) ∘ d` extends `a b`. -/
theorem IsClosedCoverExtension.supportedMul (hcover : Set.range i₁ ∪ Set.range i₂ = Set.univ)
    {q : ℤ} {a : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) p}
    {b : chowCohomologyComponent C (gysinSystemOfInvertible C) (i₂ ≫ sX) q}
    (ha : BivariantClass.VanishesOver a (pullback.snd i₁ i₂))
    (hb : BivariantClass.VanishesOver b (pullback.snd i₁ i₂))
    {c : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl p}
    {d : BivariantClass C (gysinSystemOfInvertible C) (i₂ ≫ sX) sX i₂ rfl q}
    (hc : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl a c)
    (hd : IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl b d) :
    IsClosedCoverExtension C (gysinSystemOfInvertible C) sX i₁ i₂ (i₂ ≫ sX) rfl
      (a.mulId C (i₂ ≫ sX) b) (Stacks.Chow.supportedMul C (i₂ ≫ sX) sX i₂ rfl c d) := by
  rw [hc.eq_closedCoverExtension hcover ha, hd.eq_closedCoverExtension hcover hb,
    supportedMul_closedCoverExtension]
  exact isClosedCoverExtension_closedCoverExtension C sX i₁ i₂ (i₂ ≫ sX) rfl hcover _

end Extension

end Stacks.Chow

end
