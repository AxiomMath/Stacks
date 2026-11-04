module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ChowCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import Mathlib.Algebra.DirectSum.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InverseIsoGysin
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity

/-!
# The Chow cohomology ring

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`. **Stacks 0B7E** defines the *Chow cohomology* of `X` to be the
graded `ℤ`-algebra

  `A^*(X) = ⊕_p A^p(X)`,  where  `A^p(X) = A^p(X ⟶ X)`,

whose multiplication is composition of bivariant classes. The groups and the graded group are
`Stacks.Chow.chowCohomologyComponent` and `Stacks.Chow.chowCohomology`. The product of `a ∈ A^p(X)`
and `b ∈ A^q(X)` is the class in `A^{p+q}(X)` that caps as "cap with `b`, then cap with `a`", the
unit is the identity class `1 ∈ A^0(X)`, and `ℤ` acts through the multiples of `1`.

## Main definitions

* `Stacks.Chow.BivariantClass.toIdentityCapRule` — the operation a bivariant class of degree `p`
  for `𝟙 X` induces on the Chow group of each test scheme, which is the inverse of
  `Stacks.Chow.IdentityCapRule.transport`.
* `Stacks.Chow.IdentityCapRule.comp` — the composite of two identity cap rules.
* `Stacks.Chow.chowCohomologyRingMul` — **Stacks 0B7E**, the product `a · b ∈ A^{p+q}(X)`.
* `Stacks.Chow.chowCohomologyUnit` — **Stacks 0B7E**, the unit `1 ∈ A^0(X)`, which is
  `Stacks.Chow.bivariantIdentityClass` with its Gysin hypothesis discharged.
* `Stacks.Chow.chowCohomologyGRing` — the graded ring structure on `A^*(X)`, for an arbitrary
  Gysin system satisfying the isomorphism case of Stacks 02TA.
* `Stacks.Chow.chowCohomologyRing`, `Stacks.Chow.chowCohomologyAlgebra` — the ring and the
  `ℤ`-algebra `A^*(X)` that structure produces through `DirectSum.ring`.
* `Stacks.Chow.chowCohomologyGRingOfInvertible`,
  `Stacks.Chow.chowCohomologyRingOfInvertible`,
  `Stacks.Chow.chowCohomologyAlgebraOfInvertible` — **Stacks 0B7E**, the same three for the Gysin
  system `Stacks.Chow.gysinSystemOfInvertible`, with no hypothesis on that system; their
  multiplication and unit are `Stacks.Chow.chowCohomologyGradedMul` and
  `Stacks.Chow.chowCohomologyGradedOne`.

## Main results

* `Stacks.Chow.BivariantClass.toIdentityCapRule_properNaturality`,
  `Stacks.Chow.BivariantClass.toIdentityCapRule_flatNaturalityAlongBaseChange`,
  `Stacks.Chow.BivariantClass.toIdentityCapRule_gysinNaturality` — the three axioms of Stacks
  0B76, read on the test schemes for the induced rule.
* `Stacks.Chow.IdentityCapRule.comp_properNaturality`,
  `Stacks.Chow.IdentityCapRule.comp_flatNaturalityAlongBaseChange`,
  `Stacks.Chow.IdentityCapRule.comp_gysinNaturality` — the same three for a composite rule.
* `Stacks.Chow.chowCohomologyMul_assoc`, `Stacks.Chow.chowCohomologyUnit_mul`,
  `Stacks.Chow.chowCohomologyMul_unit` — **associativity and the unit laws**.
* `Stacks.Chow.chowCohomologyMul_add`, `Stacks.Chow.chowCohomologyAdd_mul`,
  `Stacks.Chow.chowCohomologyMul_zero`, `Stacks.Chow.chowCohomologyZero_mul` — bilinearity.
* `Stacks.Chow.chowCohomologyMul_toIdentityCapRule_heq` — the product caps as cap with `b`
  followed by cap with `a`, which is the formula of Stacks 0B75 and 0FE0 at `f = g = 𝟙 X`.
* `Stacks.Chow.identityCapRule_gysinNaturality'` — the Gysin axiom for the identity cap rule.
* `Stacks.Chow.chowCohomologyRingMul_eq_chowCohomologyMul`,
  `Stacks.Chow.chowCohomologyRingMul_gysinSystemOfInvertible` — the product built here is the
  composite `Stacks.Chow.chowCohomologyMul` of Stacks 0B75 wherever both are defined.
* `Stacks.Chow.chowCohomologyMulOfInvertible_assoc`,
  `Stacks.Chow.bivariantIdentityClassOfInvertible_chowCohomologyMulOfInvertible`,
  `Stacks.Chow.chowCohomologyMulOfInvertible_bivariantIdentityClassOfInvertible` — associativity
  and the unit laws for that composite, at the Gysin system of the first Chern class rule.

## References

* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]

section Induced

variable (p : ℤ)

/-! ### The identity cap rule of a bivariant class for an identity morphism -/

/-- The identity cap rule a bivariant class of degree `p` for `𝟙 X` induces on the test schemes:
the cap operation, pushed forward along the base-change isomorphism `X ×_X T ⟶ T`. -/
def BivariantClass.toIdentityCapRule
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) : IdentityCapRule C sX p :=
  fun {_T} g _ k ↦
    (chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
      (identityBaseChangeIso_hom_comp_base C sX g) (k - p)).comp (c.cap g k)

/-- The induced rule sends `α` to the pushforward of `c.cap g k α` along the base-change
isomorphism `X ×_X T ⟶ T`. -/
@[simp]
theorem BivariantClass.toIdentityCapRule_apply
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX p c g k α =
      chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C sX g) (k - p) (c.cap g k α) :=
  rfl

/-- The transport of the induced rule is the cap operation it came from. -/
theorem BivariantClass.transport_toIdentityCapRule
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    IdentityCapRule.transport C sX p (BivariantClass.toIdentityCapRule C G sX p c) g k =
      c.cap g k :=
  ((IdentityCapRule.eq_transport_iff C sX p (BivariantClass.toIdentityCapRule C G sX p c) g k
    (c.cap g k)).1 fun _ ↦ rfl).symm

/-- A bivariant class of degree `p` for `𝟙 X` is determined by the identity cap rule it
induces. -/
theorem BivariantClass.eq_of_toIdentityCapRule_eq
    {c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k),
      BivariantClass.toIdentityCapRule C G sX p c g k α =
        BivariantClass.toIdentityCapRule C G sX p d g k α) :
    c = d :=
  BivariantClass.eq_of_pushforward_cap_eq C sX p G c d fun {T} g _ k α ↦ h (T := T) g k α

/-- Two bivariant classes for `𝟙 X` of equal degrees are heterogeneously equal as soon as the
identity cap rules they induce are. -/
theorem BivariantClass.heq_of_toIdentityCapRule_heq {p q : ℤ} (hpq : p = q)
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p)
    (d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) q)
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k),
      BivariantClass.toIdentityCapRule C G sX p c g k α ≍
        BivariantClass.toIdentityCapRule C G sX q d g k α) :
    c ≍ d := by
  subst hpq
  exact heq_of_eq (BivariantClass.eq_of_toIdentityCapRule_eq C G sX p
    fun {T} g _ k α ↦ eq_of_heq (h (T := T) g k α))

/-! ### The induced rule is additive in the class -/

/-- The rule induced by the zero class is zero. -/
theorem BivariantClass.toIdentityCapRule_zero {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX p 0 g k α = 0 := by
  rw [BivariantClass.toIdentityCapRule_apply, BivariantClass.zero_cap, map_zero]

/-- The rule induced by a sum of classes is the sum of the induced rules. -/
theorem BivariantClass.toIdentityCapRule_add
    (c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX p (c + d) g k α =
      BivariantClass.toIdentityCapRule C G sX p c g k α +
        BivariantClass.toIdentityCapRule C G sX p d g k α := by
  rw [BivariantClass.toIdentityCapRule_apply, BivariantClass.add_cap, map_add]
  rfl

/-! ### The proper-pushforward identity for the induced rule -/

/-- **Stacks 0B76 (1) read on the test schemes, for the rule a bivariant class induces.** -/
theorem BivariantClass.toIdentityCapRule_properNaturality
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    IdentityCapRule.ProperNaturality C sX p (BivariantClass.toIdentityCapRule C G sX p c) := by
  intro T T' g _ h _ k hfac hfacp α
  set e : pullback (𝟙 X) g ≅ T := identityBaseChangeIso g with he
  set e' : pullback (𝟙 X) (h ≫ g) ≅ T' := identityBaseChangeIso (h ≫ g) with he'
  set h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g := bivariantBaseChangeMap (𝟙 X) g h with hh'
  have sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g) :=
    isPullback_bivariantBaseChangeMap (𝟙 X) g h
  have hprop : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  have hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g) := by
    simp only [hh', bivariantBaseChangeMap, pullback.map, Category.comp_id, pullback.lift_fst]
  have hm : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hh : h ≫ g ≫ sX = (h ≫ g) ≫ sX := by simp [Category.assoc]
  have hv : e.hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX g
  have hu : e'.hom ≫ (h ≫ g) ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX (h ≫ g)
  have hinv : e.inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX :=
    identityBaseChangeIso_hom_comp C sX g
  have hsq : e'.hom ≫ h = h' ≫ e.hom := sq.w
  have hconj : e'.hom ≫ h ≫ e.inv = h' := by
    rw [← Category.assoc, hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h' hm (k - p) :=
    properPushforwardFactorsThroughRationalEquivalence_congr C
      (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) (e'.hom ≫ h ≫ e.inv) h'
      hconj _ hm (k - p)
      (properPushforwardFactorsThroughRationalEquivalence_isIso_comp_isIso C
        (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) ((h ≫ g) ≫ sX) (g ≫ sX)
        e'.hom h e.inv hu hh hinv (k - p) hfacp)
  rw [BivariantClass.toIdentityCapRule_apply, BivariantClass.toIdentityCapRule_apply,
    c.proper_naturality g h h' sq hfst k hfac hfac' α]
  exact properChowPushforward_comp_eq C _ _ _ _ h' e.hom e'.hom h hsq.symm hm hv hu hh (k - p)
    hfac' (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ e.hom hv (k - p))
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ e'.hom hu (k - p)) hfacp _

/-! ### The flat-pullback identity for the induced rule -/

/-- **Stacks 0B76 (2) read on the test schemes, for the rule a bivariant class induces**, in the
form that carries the base change of the flat morphism and its relative dimension. -/
theorem BivariantClass.toIdentityCapRule_flatNaturalityAlongBaseChange
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    IdentityCapRule.FlatNaturalityAlongBaseChange C sX p
      (BivariantClass.toIdentityCapRule C G sX p c) := by
  intro T T' g _ h _ _ r hr h' sq hfst k
  have hfth' : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hflh' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  intro hr' hfac hfacp α
  have hm : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hh : h ≫ g ≫ sX = (h ≫ g) ≫ sX := by simp [Category.assoc]
  have hbg : (identityBaseChangeIso g).hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX g
  have hbg' : (identityBaseChangeIso (h ≫ g)).hom ≫ (h ≫ g) ≫ sX =
      pullback.fst (𝟙 X) (h ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX (h ≫ g)
  have hsq : h' ≫ (identityBaseChangeIso g).hom = (identityBaseChangeIso (h ≫ g)).hom ≫ h :=
    sq.w.symm
  have hfach' : FlatPullbackFactorsThroughRationalEquivalence C
      (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h' hm r hr' (k - p) :=
    flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C
      (pullback.fst (𝟙 X) g ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (g ≫ sX) ((h ≫ g) ≫ sX)
      (identityBaseChangeIso g).hom hbg (identityBaseChangeIso (h ≫ g)).hom hbg' h' hm h hh
      hsq r hr' hr (k - p) hfacp
  refine HEq.trans (heq_chowPushforwardOfIso_of_heq C (pullback.fst (𝟙 X) (h ≫ g) ≫ sX)
      ((h ≫ g) ≫ sX) (identityBaseChangeIso (h ≫ g)).hom hbg'
      (show k + (r : ℤ) - p = k - p + (r : ℤ) by omega)
      (c.flat_naturality g h r hr h' sq hfst k hr' hfac hfach' α)) ?_
  exact heq_of_eq (flatPullbackChow_chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX)
    (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (g ≫ sX) ((h ≫ g) ≫ sX)
    (identityBaseChangeIso g).hom hbg (identityBaseChangeIso (h ≫ g)).hom hbg' h' hm h hh
    hsq r hr' hr (k - p) hfach' hfacp (c.cap g k α)).symm

/-! ### The Gysin identity for the induced rule -/

/-- **Stacks 0B76 (3) read on the test schemes, for the rule a bivariant class induces**, for a
Gysin system satisfying the isomorphism case of Stacks 02TA. -/
theorem BivariantClass.toIdentityCapRule_gysinNaturality
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p)
    (hiso : G.IsNaturalUnderInverseIso) :
    IdentityCapRule.GysinNaturality C sX p (BivariantClass.toIdentityCapRule C G sX p c) G := by
  intro T g _ N _ s k α
  set D := Stacks.Divisors.zeroScheme T N s with hD
  set N' := (Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N with hN'
  set s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s with hs'
  set E := Stacks.Divisors.zeroScheme (pullback (𝟙 X) g) N' s' with hE
  set e : pullback (𝟙 X) (D.subschemeι ≫ g) ≅ E.subscheme :=
    bivariantDivisorBaseChangeIso (𝟙 X) g N s with hee
  set eD : pullback (𝟙 X) (D.subschemeι ≫ g) ≅ D.subscheme :=
    identityBaseChangeIso (D.subschemeι ≫ g) with heD
  set eg : pullback (𝟙 X) g ≅ T := identityBaseChangeIso g with heg
  have hbgD : eD.hom ≫ (D.subschemeι ≫ g) ≫ sX =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX (D.subschemeι ≫ g)
  have hbgDinv : eD.inv ≫ pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX =
      (D.subschemeι ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp C sX (D.subschemeι ≫ g)
  have hbg : eg.hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX g
  have hbginv : eg.inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX :=
    identityBaseChangeIso_hom_comp C sX g
  have hfstD : bivariantBaseChangeMap (𝟙 X) g D.subschemeι ≫ pullback.fst (𝟙 X) g =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) := by
    simp only [bivariantBaseChangeMap, pullback.map, Category.comp_id, pullback.lift_fst]
  have he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap (𝟙 X) g D.subschemeι :=
    bivariantDivisorBaseChangeIso_hom_subschemeι (𝟙 X) g N s
  have hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX := by
    rw [← Category.assoc, he, ← Category.assoc, hfstD]
  have hj : (eD.inv ≫ e.hom) ≫ (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) =
      D.subschemeι ≫ g ≫ sX := by
    rw [Category.assoc, hbase, hbgDinv, Category.assoc]
  have hinvj : (e.hom ≫ (inv (eD.inv ≫ e.hom))) = eD.hom := by
    rw [IsIso.comp_inv_eq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hidx : k + 1 - p = k - p + 1 := by omega
  have hgys := c.gysin_naturality g N s k e he hbase
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
      (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
      (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) e.hom hbase (k - p)) α
  have hnat := hiso (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) eg.inv (pullback.snd (𝟙 X) g)
    eg.inv_hom_id hbginv N s (k - p) (eD.inv ≫ e.hom) hj
    (by
      rw [Category.assoc, he]
      exact identityBaseChangeIso_inv_bivariantBaseChangeMap g D.subschemeι)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
      (D.subschemeι ≫ g ≫ sX) (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (eD.inv ≫ e.hom) hj
      (k - p))
    (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hidx)
      (chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) eg.hom hbg (k + 1 - p)
        (c.cap g (k + 1) α)))
  have harg : chowPushforwardOfIso C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) eg.inv hbginv
        (k - p + 1)
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hidx)
          (chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) eg.hom hbg (k + 1 - p)
            (c.cap g (k + 1) α))) =
      Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X) g ≫ sX)) hidx) (c.cap g (k + 1) α) := by
    rw [← chowPushforwardOfIso_cast C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) eg.inv hbginv hidx]
    exact congrArg (Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X) g ≫ sX)) hidx))
      (chowPushforwardOfIso_inv_comp C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) eg.hom hbg
        (k + 1 - p) (c.cap g (k + 1) α))
  rw [harg, ← hgys] at hnat
  have hinvjb : (inv (eD.inv ≫ e.hom)) ≫ (D.subschemeι ≫ g ≫ sX) =
      E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX := by
    rw [IsIso.inv_comp_eq, hj]
  have hbgD' : eD.hom ≫ D.subschemeι ≫ g ≫ sX =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX := by
    rwa [← Category.assoc D.subschemeι g sX]
  have hsplit := chowPushforwardOfIso_comp_apply C (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
    (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (D.subschemeι ≫ g ≫ sX) e.hom
    (inv (eD.inv ≫ e.hom)) hbase hinvjb (k - p)
    (c.cap (D.subschemeι ≫ g) k (G.onChow (g ≫ sX) N s k α))
  exact ((hsplit.trans (chowPushforwardOfIso_congr_apply C _ _ _ _ hinvj _ hbgD' _ _)).symm.trans
    (DFunLike.congr_arg (chowPushforwardOfIso C (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX)
      (D.subschemeι ≫ g ≫ sX) (inv (eD.inv ≫ e.hom)) hinvjb (k - p)) hnat)).trans
    (chowPushforwardOfIso_inv_comp C (D.subschemeι ≫ g ≫ sX)
      (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (eD.inv ≫ e.hom) hj (k - p) _)

end Induced

/-! ### The composite of two identity cap rules -/

section Composition

variable (p q : ℤ)

/-- The composite of two identity cap rules: cap with the rule of degree `q`, then with the rule
of degree `p`, transported from degree `(k - q) - p` to degree `k - (p + q)`. -/
def IdentityCapRule.comp (op₁ : IdentityCapRule C sX p) (op₂ : IdentityCapRule C sX q) :
    IdentityCapRule C sX (p + q) := fun {_T} g _ k ↦
  (chowGroupDegreeEquiv C (g ≫ sX) (by ring : k - q - p = k - (p + q))).toAddMonoidHom.comp
    ((op₁ g (k - q)).comp (op₂ g k))

/-- The composite rule sends `α` to `op₁ g (k - q) (op₂ g k α)`, transported to degree
`k - (p + q)`. -/
@[simp]
theorem IdentityCapRule.comp_apply (op₁ : IdentityCapRule C sX p) (op₂ : IdentityCapRule C sX q)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    IdentityCapRule.comp C sX p q op₁ op₂ g k α =
      chowGroupDegreeEquiv C (g ≫ sX) (by ring : k - q - p = k - (p + q))
        (op₁ g (k - q) (op₂ g k α)) :=
  rfl

/-- An identity cap rule carries a heterogeneous equality of Chow classes in two equal degrees to
a heterogeneous equality of their images. -/
theorem IdentityCapRule.heq_of_heq (op : IdentityCapRule C sX p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] {m m' : ℤ} (hm : m = m') {x : chowGroup C (g ≫ sX) m}
    {y : chowGroup C (g ≫ sX) m'} (hxy : x ≍ y) : op g m x ≍ op g m' y := by
  subst hm
  exact heq_of_eq (DFunLike.congr_arg (op g m) (eq_of_heq hxy))

/-- The value of a composite rule, with the transport of the degree removed. -/
theorem IdentityCapRule.comp_apply_heq (op₁ : IdentityCapRule C sX p)
    (op₂ : IdentityCapRule C sX q) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    IdentityCapRule.comp C sX p q op₁ op₂ g k α ≍ op₁ g (k - q) (op₂ g k α) :=
  chowGroupDegreeEquiv_heq C (g ≫ sX) _ _

/-- **Stacks 0B76 (1) for a composite rule.** -/
theorem IdentityCapRule.comp_properNaturality (op₁ : IdentityCapRule C sX p)
    (op₂ : IdentityCapRule C sX q) (h₁ : IdentityCapRule.ProperNaturality C sX p op₁)
    (h₂ : IdentityCapRule.ProperNaturality C sX q op₂) :
    IdentityCapRule.ProperNaturality C sX (p + q) (IdentityCapRule.comp C sX p q op₁ op₂) := by
  intro T T' g _ h _ k hfac hfacpq α
  rw [IdentityCapRule.comp_apply, IdentityCapRule.comp_apply,
    h₂ g h k hfac (properPushforwardDescends C _ _ _ _ _) α,
    h₁ g h (k - q) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) (op₂ (h ≫ g) k α)]
  exact chowGroupDegreeEquiv_properChowPushforward_comp C ((h ≫ g) ≫ sX) (g ≫ sX) h
    (by simp [Category.assoc]) (by ring : k - q - p = k - (p + q))
    (properPushforwardDescends C _ _ _ _ _) hfacpq _

/-- **Stacks 0B76 (2) for a composite rule**, in the form that carries the base change of the
flat morphism. -/
theorem IdentityCapRule.comp_flatNaturalityAlongBaseChange (op₁ : IdentityCapRule C sX p)
    (op₂ : IdentityCapRule C sX q)
    (h₁ : IdentityCapRule.FlatNaturalityAlongBaseChange C sX p op₁)
    (h₂ : IdentityCapRule.FlatNaturalityAlongBaseChange C sX q op₂) :
    IdentityCapRule.FlatNaturalityAlongBaseChange C sX (p + q)
      (IdentityCapRule.comp C sX p q op₁ op₂) := by
  intro T T' g _ h _ _ r hr h' sq hfst k
  have hfth' : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have hflh' : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  intro hr' hfac hfacpq α
  refine HEq.trans (IdentityCapRule.comp_apply_heq C sX p q op₁ op₂ (h ≫ g) (k + (r : ℤ)) _) ?_
  refine HEq.trans (IdentityCapRule.heq_of_heq C sX p op₁ (h ≫ g)
    (by ring : k + (r : ℤ) - q = k - q + (r : ℤ))
    (h₂ g h r hr h' sq hfst k hr' hfac (flatPullbackDescends C _ _ _ _ _ _ _) α)) ?_
  refine HEq.trans (h₁ g h r hr h' sq hfst (k - q) hr'
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (op₂ g k α)) ?_
  exact flatPullbackChow_heq_of_degree C ((h ≫ g) ≫ sX) (g ≫ sX) h (by simp [Category.assoc]) r
    hr (by ring : k - q - p = k - (p + q)) (flatPullbackDescends C _ _ _ _ _ _ _) hfacpq
    (IdentityCapRule.comp_apply_heq C sX p q op₁ op₂ g k α).symm

/-- **Stacks 0B76 (3) for a composite rule.** -/
theorem IdentityCapRule.comp_gysinNaturality (op₁ : IdentityCapRule C sX p)
    (op₂ : IdentityCapRule C sX q) (h₁ : IdentityCapRule.GysinNaturality C sX p op₁ G)
    (h₂ : IdentityCapRule.GysinNaturality C sX q op₂ G) :
    IdentityCapRule.GysinNaturality C sX (p + q) (IdentityCapRule.comp C sX p q op₁ op₂) G := by
  intro T g _ N _ s k α
  have hq : k + 1 - q = k - q + 1 := by omega
  have hq1 : k - q + 1 - p = k - q - p + 1 := by omega
  have hdeg : k - q - p = k - (p + q) := by ring
  have hdeg' : k - q - p + 1 = k - (p + q) + 1 := by rw [hdeg]
  set D := Stacks.Divisors.zeroScheme T N s with hD
  set β := Eq.mp (congrArg (chowGroup C (g ≫ sX)) hq) (op₂ g (k + 1) α) with hβ
  set γ := Eq.mp (congrArg (chowGroup C (g ≫ sX)) hq1) (op₁ g (k - q + 1) β) with hγ
  have e₂ := h₂ g N s k α
  have e₁ := h₁ g N s (k - q) β
  have hfinal : chowGroupDegreeEquiv C (g ≫ sX) hdeg' γ ≍
      Eq.mp (congrArg (chowGroup C (g ≫ sX)) (by omega : k + 1 - (p + q) = k - (p + q) + 1))
        (IdentityCapRule.comp C sX p q op₁ op₂ g (k + 1) α) := by
    refine HEq.trans (chowGroupDegreeEquiv_heq C (g ≫ sX) hdeg' γ) ?_
    refine HEq.trans (chowGroup_cast_heq (g ≫ sX) hq1 (op₁ g (k - q + 1) β)) ?_
    refine HEq.trans (IdentityCapRule.heq_of_heq C sX p op₁ g hq.symm
      (chowGroup_cast_heq (g ≫ sX) hq (op₂ g (k + 1) α))) ?_
    refine HEq.symm (HEq.trans (chowGroup_cast_heq (g ≫ sX)
      (by omega : k + 1 - (p + q) = k - (p + q) + 1) _) ?_)
    exact IdentityCapRule.comp_apply_heq C sX p q op₁ op₂ g (k + 1) α
  exact ((DFunLike.congr_arg (chowGroupDegreeEquiv C ((D.subschemeι ≫ g) ≫ sX) hdeg)
        ((DFunLike.congr_arg (op₁ (D.subschemeι ≫ g) (k - q)) e₂).trans e₁)).trans
      (GysinSystem.onChow_chowGroupDegreeEquiv G (g ≫ sX) N s hdeg hdeg' γ)).trans
    (congrArg (G.onChow (g ≫ sX) N s (k - (p + q))) (eq_of_heq hfinal))

end Composition

/-! ### The unit -/

/-- **Stacks 0B76 (3) for the identity cap rule.** -/
theorem identityCapRule_gysinNaturality' :
    IdentityCapRule.GysinNaturality C sX 0 (identityCapRule C sX) G := by
  intro T g _ N _ s k α
  refine (GysinSystem.onChow_chowGroupDegreeEquiv G (g ≫ sX) N s (sub_zero k).symm
      (by omega : k + 1 = k - 0 + 1) α).trans
    (congrArg (G.onChow (g ≫ sX) N s (k - 0)) (eq_of_heq ?_))
  refine HEq.trans (chowGroupDegreeEquiv_heq C (g ≫ sX) (by omega : k + 1 = k - 0 + 1) α) ?_
  refine HEq.symm (HEq.trans (chowGroup_cast_heq (g ≫ sX)
    (by omega : k + 1 - 0 = k - 0 + 1) _) ?_)
  exact chowGroupDegreeEquiv_heq C (g ≫ sX) (sub_zero (k + 1)).symm α

/-! ### The graded `ℤ`-algebra `A^*(X)` -/

section Algebra

variable (hiso : G.IsNaturalUnderInverseIso)

/-- **Stacks 0B7E, the multiplication.** The product `a · b ∈ A^{p+q}(X)` of `a ∈ A^p(X)` and
`b ∈ A^q(X)`: the bivariant class for `𝟙 X` whose operation on each test scheme is cap with `b`
followed by cap with `a`. -/
def chowCohomologyRingMul {p q : ℤ} (a : chowCohomologyComponent C G sX p)
    (b : chowCohomologyComponent C G sX q) : chowCohomologyComponent C G sX (p + q) :=
  IdentityCapRule.toBivariantClass C sX (p + q)
    (IdentityCapRule.comp C sX p q (BivariantClass.toIdentityCapRule C G sX p a)
      (BivariantClass.toIdentityCapRule C G sX q b)) G
    (IdentityCapRule.comp_properNaturality C sX p q _ _
      (BivariantClass.toIdentityCapRule_properNaturality C G sX p a)
      (BivariantClass.toIdentityCapRule_properNaturality C G sX q b))
    (IdentityCapRule.transportFlatNaturalityAlongBaseChange C sX (p + q) _
      (IdentityCapRule.comp_flatNaturalityAlongBaseChange C sX p q _ _
        (BivariantClass.toIdentityCapRule_flatNaturalityAlongBaseChange C G sX p a)
        (BivariantClass.toIdentityCapRule_flatNaturalityAlongBaseChange C G sX q b)))
    (IdentityCapRule.transportGysinNaturality C sX (p + q) _ G
      (IdentityCapRule.comp_gysinNaturality C G sX p q _ _
        (BivariantClass.toIdentityCapRule_gysinNaturality C G sX p a hiso)
        (BivariantClass.toIdentityCapRule_gysinNaturality C G sX q b hiso)) hiso)

/-- The rule the product induces on the test schemes is the composite of the two rules. -/
@[simp]
theorem chowCohomologyMul_toIdentityCapRule {p q : ℤ} (a : chowCohomologyComponent C G sX p)
    (b : chowCohomologyComponent C G sX q) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX (p + q) (chowCohomologyRingMul C G sX hiso a b) g k α =
      IdentityCapRule.comp C sX p q (BivariantClass.toIdentityCapRule C G sX p a)
        (BivariantClass.toIdentityCapRule C G sX q b) g k α :=
  IdentityCapRule.pushforward_transport C sX (p + q) _ g k α

/-- The cap operation of the product, with the transport of the degree removed: `a · b` caps as
cap with `b` followed by cap with `a`. -/
theorem chowCohomologyMul_toIdentityCapRule_heq {p q : ℤ}
    (a : chowCohomologyComponent C G sX p) (b : chowCohomologyComponent C G sX q)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX (p + q) (chowCohomologyRingMul C G sX hiso a b) g k α ≍
      BivariantClass.toIdentityCapRule C G sX p a g (k - q)
        (BivariantClass.toIdentityCapRule C G sX q b g k α) :=
  (chowCohomologyMul_toIdentityCapRule C G sX hiso a b g k α) ▸
    IdentityCapRule.comp_apply_heq C sX p q _ _ g k α

/-- **Stacks 0B7E, the unit.** The class `1 ∈ A^0(X)`, which acts as the identity on the Chow
group of every test scheme: the class `Stacks.Chow.bivariantIdentityClass`. -/
def chowCohomologyUnit : chowCohomologyComponent C G sX 0 :=
  bivariantIdentityClass C sX G
    (IdentityCapRule.transportGysinNaturality C sX 0 (identityCapRule C sX) G
      (identityCapRule_gysinNaturality' C G sX) hiso)

/-- The rule the unit induces on the test schemes is the identity. -/
@[simp]
theorem chowCohomologyUnit_toIdentityCapRule {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX 0 (chowCohomologyUnit C G sX hiso) g k α =
      identityCapRule C sX g k α :=
  IdentityCapRule.pushforward_transport C sX 0 (identityCapRule C sX) g k α

/-! #### The ring axioms -/

/-- The product of a class with zero is zero. -/
theorem chowCohomologyMul_zero {p q : ℤ} (a : chowCohomologyComponent C G sX p) :
    chowCohomologyRingMul C G sX hiso a (0 : chowCohomologyComponent C G sX q) = 0 := by
  refine BivariantClass.eq_of_toIdentityCapRule_eq C G sX (p + q) fun {T} g _ k α ↦ ?_
  rw [chowCohomologyMul_toIdentityCapRule, IdentityCapRule.comp_apply,
    BivariantClass.toIdentityCapRule_zero, map_zero, map_zero,
    BivariantClass.toIdentityCapRule_zero]

/-- The product of zero with a class is zero. -/
theorem chowCohomologyZero_mul {p q : ℤ} (b : chowCohomologyComponent C G sX q) :
    chowCohomologyRingMul C G sX hiso (0 : chowCohomologyComponent C G sX p) b = 0 := by
  refine BivariantClass.eq_of_toIdentityCapRule_eq C G sX (p + q) fun {T} g _ k α ↦ ?_
  rw [chowCohomologyMul_toIdentityCapRule, IdentityCapRule.comp_apply,
    BivariantClass.toIdentityCapRule_zero, map_zero, BivariantClass.toIdentityCapRule_zero]

/-- The product distributes over addition in the second factor. -/
theorem chowCohomologyMul_add {p q : ℤ} (a : chowCohomologyComponent C G sX p)
    (b b' : chowCohomologyComponent C G sX q) :
    chowCohomologyRingMul C G sX hiso a (b + b') =
      chowCohomologyRingMul C G sX hiso a b + chowCohomologyRingMul C G sX hiso a b' := by
  refine BivariantClass.eq_of_toIdentityCapRule_eq C G sX (p + q) fun {T} g _ k α ↦ ?_
  rw [chowCohomologyMul_toIdentityCapRule, IdentityCapRule.comp_apply,
    BivariantClass.toIdentityCapRule_add, map_add, map_add,
    BivariantClass.toIdentityCapRule_add, chowCohomologyMul_toIdentityCapRule,
    chowCohomologyMul_toIdentityCapRule, IdentityCapRule.comp_apply,
    IdentityCapRule.comp_apply]

/-- The product distributes over addition in the first factor. -/
theorem chowCohomologyAdd_mul {p q : ℤ} (a a' : chowCohomologyComponent C G sX p)
    (b : chowCohomologyComponent C G sX q) :
    chowCohomologyRingMul C G sX hiso (a + a') b =
      chowCohomologyRingMul C G sX hiso a b + chowCohomologyRingMul C G sX hiso a' b := by
  refine BivariantClass.eq_of_toIdentityCapRule_eq C G sX (p + q) fun {T} g _ k α ↦ ?_
  rw [chowCohomologyMul_toIdentityCapRule, IdentityCapRule.comp_apply,
    BivariantClass.toIdentityCapRule_add, map_add,
    BivariantClass.toIdentityCapRule_add, chowCohomologyMul_toIdentityCapRule,
    chowCohomologyMul_toIdentityCapRule, IdentityCapRule.comp_apply,
    IdentityCapRule.comp_apply]

/-- **Stacks 0B7E, the unit law.** `1 · a = a`, the two sides sitting in the degrees `0 + p` and
`p`. -/
theorem chowCohomologyUnit_mul {p : ℤ} (a : chowCohomologyComponent C G sX p) :
    chowCohomologyRingMul C G sX hiso (chowCohomologyUnit C G sX hiso) a ≍ a := by
  refine BivariantClass.heq_of_toIdentityCapRule_heq C G sX (zero_add p) _ a
    fun {T} g _ k α ↦ ?_
  refine HEq.trans (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso _ a g k α) ?_
  rw [chowCohomologyUnit_toIdentityCapRule, identityCapRule_apply]
  exact chowGroup_cast_heq (g ≫ sX) (sub_zero (k - p)).symm _

/-- **Stacks 0B7E, the unit law.** `a · 1 = a`, the two sides sitting in the degrees `p + 0` and
`p`. -/
theorem chowCohomologyMul_unit {p : ℤ} (a : chowCohomologyComponent C G sX p) :
    chowCohomologyRingMul C G sX hiso a (chowCohomologyUnit C G sX hiso) ≍ a := by
  refine BivariantClass.heq_of_toIdentityCapRule_heq C G sX (add_zero p) _ a
    fun {T} g _ k α ↦ ?_
  refine HEq.trans (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso a _ g k α) ?_
  rw [chowCohomologyUnit_toIdentityCapRule, identityCapRule_apply]
  exact IdentityCapRule.heq_of_heq C sX p (BivariantClass.toIdentityCapRule C G sX p a) g
    (sub_zero k) (chowGroup_cast_heq (g ≫ sX) (sub_zero k).symm α)

/-- **Stacks 0B7E, associativity.** `(a · b) · c = a · (b · c)`, the two sides sitting in the
degrees `(p + q) + r` and `p + (q + r)`. -/
theorem chowCohomologyMul_assoc {p q r : ℤ} (a : chowCohomologyComponent C G sX p)
    (b : chowCohomologyComponent C G sX q) (c : chowCohomologyComponent C G sX r) :
    chowCohomologyRingMul C G sX hiso (chowCohomologyRingMul C G sX hiso a b) c ≍
      chowCohomologyRingMul C G sX hiso a (chowCohomologyRingMul C G sX hiso b c) := by
  refine BivariantClass.heq_of_toIdentityCapRule_heq C G sX (add_assoc p q r) _ _
    fun {T} g _ k α ↦ ?_
  refine HEq.trans (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso _ c g k α) ?_
  refine HEq.trans (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso a b g (k - r) _) ?_
  refine HEq.symm (HEq.trans (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso a _ g k α) ?_)
  exact IdentityCapRule.heq_of_heq C sX p (BivariantClass.toIdentityCapRule C G sX p a) g
    (by ring : k - (q + r) = k - r - q)
    (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso b c g k α)

/-- **Stacks 0B7E.** The Chow cohomology of `X` as a graded ring: the degree `p` component is
`A^p(X ⟶ X)`, the multiplication is composition of bivariant classes, the unit is the identity
class `1 ∈ A^0(X)`, and `ℤ` maps to the multiples of `1`. -/
@[instance_reducible]
def chowCohomologyGRing :
    DirectSum.GRing fun p : ℤ ↦ chowCohomologyComponent C G sX p := by
  letI gone : GradedMonoid.GOne fun p : ℤ ↦ chowCohomologyComponent C G sX p :=
    ⟨chowCohomologyUnit C G sX hiso⟩
  letI gmul : GradedMonoid.GMul fun p : ℤ ↦ chowCohomologyComponent C G sX p :=
    ⟨fun a b ↦ chowCohomologyRingMul C G sX hiso a b⟩
  letI gmonoid : GradedMonoid.GMonoid fun p : ℤ ↦ chowCohomologyComponent C G sX p :=
    { __ := gmul
      __ := gone
      one_mul := fun a ↦ Sigma.ext (zero_add a.fst) (chowCohomologyUnit_mul C G sX hiso a.snd)
      mul_one := fun a ↦ Sigma.ext (add_zero a.fst) (chowCohomologyMul_unit C G sX hiso a.snd)
      mul_assoc := fun a b c ↦ Sigma.ext (add_assoc a.fst b.fst c.fst)
        (chowCohomologyMul_assoc C G sX hiso a.snd b.snd c.snd) }
  letI gnuas : DirectSum.GNonUnitalNonAssocSemiring
      fun p : ℤ ↦ chowCohomologyComponent C G sX p :=
    { __ := gmul
      mul_zero := fun a ↦ chowCohomologyMul_zero C G sX hiso a
      zero_mul := fun b ↦ chowCohomologyZero_mul C G sX hiso b
      mul_add := fun a b b' ↦ chowCohomologyMul_add C G sX hiso a b b'
      add_mul := fun a a' b ↦ chowCohomologyAdd_mul C G sX hiso a a' b }
  letI gsemiring : DirectSum.GSemiring fun p : ℤ ↦ chowCohomologyComponent C G sX p :=
    { __ := gnuas
      __ := gmonoid
      natCast := fun n ↦ n • chowCohomologyUnit C G sX hiso
      natCast_zero := zero_nsmul _
      natCast_succ := fun n ↦ succ_nsmul _ n }
  exact
    { __ := gsemiring
      intCast := fun n ↦ n • chowCohomologyUnit C G sX hiso
      intCast_ofNat := fun n ↦ natCast_zsmul _ n
      intCast_negSucc_ofNat := fun n ↦ negSucc_zsmul _ n }

/-- **Stacks 0B7E.** The Chow cohomology `A^*(X)` as a ring. -/
@[instance_reducible]
def chowCohomologyRing : Ring (chowCohomology C G sX) :=
  letI : DirectSum.GRing fun p : ℤ ↦ chowCohomologyComponent C G sX p :=
    chowCohomologyGRing C G sX hiso
  DirectSum.ring _

/-- **Stacks 0B7E.** The Chow cohomology `A^*(X)` as a graded `ℤ`-algebra. -/
@[instance_reducible]
def chowCohomologyAlgebra : @Algebra ℤ (chowCohomology C G sX) _
    (chowCohomologyRing C G sX hiso).toSemiring :=
  letI : Ring (chowCohomology C G sX) := chowCohomologyRing C G sX hiso
  inferInstance

end Algebra

/-! ### Agreement with the product of Stacks 0B75 -/

section Composite

variable (hgys : G.IsNaturalUnderBaseChangeIso) (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The rule that the composite of Stacks 0B75, `Stacks.Chow.chowCohomologyMul`, induces on the
test schemes is the composite of the two rules: cap with `b`, then cap with `a`. -/
theorem toIdentityCapRule_chowCohomologyMul {p q : ℤ} (a : chowCohomologyComponent C G sX p)
    (b : chowCohomologyComponent C G sX q) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX (p + q)
        (chowCohomologyMul C G sX p q hgys hgysc a b) g k α =
      IdentityCapRule.comp C sX p q (BivariantClass.toIdentityCapRule C G sX p a)
        (BivariantClass.toIdentityCapRule C G sX q b) g k α := by
  have ha := BivariantClass.cap_chowPushforwardOfIso a g (identityBaseChangeIso g).hom
    (pullback.fst (𝟙 X) g) (fst_eq_identityBaseChangeIso_hom g).symm
    (pullback.fst (𝟙 X) g ≫ sX) rfl (k - q) (identityBaseChangeIso_hom_comp_base C sX g)
    (b.cap g k α) (b.cap g k α) rfl
  have hw : (testBaseChangeIso (𝟙 X) g (identityBaseChangeIso g).hom (pullback.fst (𝟙 X) g)
      (fst_eq_identityBaseChangeIso_hom g).symm).hom =
      (identityBaseChangeIso (pullback.fst (𝟙 X) g)).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [testBaseChangeIso_hom_fst]
      exact fst_eq_identityBaseChangeIso_hom (pullback.fst (𝟙 X) g)
    · rw [testBaseChangeIso_hom_snd]
      rfl
  rw [BivariantClass.toIdentityCapRule_apply, chowCohomologyMul_cap, IdentityCapRule.comp_apply,
    BivariantClass.toIdentityCapRule_apply, BivariantClass.toIdentityCapRule_apply, ha,
    chowGroupDegreeEquiv_chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX)
      (identityBaseChangeIso g).hom (identityBaseChangeIso_hom_comp_base C sX g)
      (by ring : k - q - p = k - (p + q))]
  exact congrArg _ (congrArg _ (chowPushforwardOfIso_congr_apply C _ _ _ _ hw.symm _ _ _ _))

/-- **The product of Stacks 0B7E is the composite of Stacks 0B75.** Wherever both are
defined, `Stacks.Chow.chowCohomologyRingMul` is `Stacks.Chow.chowCohomologyMul`, the composite
bivariant class of Stacks 0B75 for the two identity morphisms read for `𝟙 X`. -/
theorem chowCohomologyRingMul_eq_chowCohomologyMul (hiso : G.IsNaturalUnderInverseIso) {p q : ℤ}
    (a : chowCohomologyComponent C G sX p) (b : chowCohomologyComponent C G sX q) :
    chowCohomologyRingMul C G sX hiso a b = chowCohomologyMul C G sX p q hgys hgysc a b :=
  BivariantClass.eq_of_toIdentityCapRule_eq C G sX (p + q) fun {T} g _ k α ↦ by
    rw [chowCohomologyMul_toIdentityCapRule, toIdentityCapRule_chowCohomologyMul]

end Composite

/-! ### The Chow cohomology ring of the canonical Gysin system -/

section OfInvertible

/-- At the Gysin system of the first Chern class rule the product of Stacks 0B7E is
`Stacks.Chow.chowCohomologyMulOfInvertible`, the composite of Stacks 0B75. -/
theorem chowCohomologyRingMul_gysinSystemOfInvertible {p q : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    chowCohomologyRingMul C (gysinSystemOfInvertible C) sX
        (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C) a b =
      chowCohomologyMulOfInvertible C sX p q a b :=
  chowCohomologyRingMul_eq_chowCohomologyMul C (gysinSystemOfInvertible C) sX
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)
    (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C) a b

/-- **Stacks 0B7E, a unit law.** `1 · a = a` for the composite of Stacks 0B75 at the Gysin system
of the first Chern class rule, the two sides sitting in the degrees `0 + p` and `p`. -/
theorem bivariantIdentityClassOfInvertible_chowCohomologyMulOfInvertible {p : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    chowCohomologyMulOfInvertible C sX 0 p (bivariantIdentityClassOfInvertible C sX) a ≍ a := by
  rw [← chowCohomologyRingMul_gysinSystemOfInvertible]
  exact chowCohomologyUnit_mul C (gysinSystemOfInvertible C) sX
    (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C) a

/-- **Stacks 0B7E, a unit law.** `a · 1 = a` for the composite of Stacks 0B75 at the Gysin system
of the first Chern class rule, the two sides sitting in the degrees `p + 0` and `p`. -/
theorem chowCohomologyMulOfInvertible_bivariantIdentityClassOfInvertible {p : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    chowCohomologyMulOfInvertible C sX p 0 a (bivariantIdentityClassOfInvertible C sX) ≍ a := by
  rw [← chowCohomologyRingMul_gysinSystemOfInvertible]
  exact chowCohomologyMul_unit C (gysinSystemOfInvertible C) sX
    (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C) a

/-- **Stacks 0B7E, associativity.** `(a · b) · c = a · (b · c)` for the composite of Stacks 0B75
at the Gysin system of the first Chern class rule, the two sides sitting in the degrees
`(p + q) + r` and `p + (q + r)`. -/
theorem chowCohomologyMulOfInvertible_assoc {p q r : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX r) :
    chowCohomologyMulOfInvertible C sX (p + q) r (chowCohomologyMulOfInvertible C sX p q a b) c ≍
      chowCohomologyMulOfInvertible C sX p (q + r) a
        (chowCohomologyMulOfInvertible C sX q r b c) := by
  rw [← chowCohomologyRingMul_gysinSystemOfInvertible,
    ← chowCohomologyRingMul_gysinSystemOfInvertible,
    ← chowCohomologyRingMul_gysinSystemOfInvertible,
    ← chowCohomologyRingMul_gysinSystemOfInvertible]
  exact chowCohomologyMul_assoc C (gysinSystemOfInvertible C) sX
    (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C) a b c

/-- The Chow cohomology of `X` as a graded ring, for the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`: the degree `p` component is `A^p(X ⟶ X)`, the multiplication
is `Stacks.Chow.chowCohomologyGradedMul` (composition of bivariant classes), the unit is
`Stacks.Chow.chowCohomologyGradedOne` (the identity class `1 ∈ A^0(X)`), and `ℤ` maps to the
multiples of `1`. -/
@[instance_reducible, stacks 0B7E "the graded Z-algebra structure on A^*(X): composition of \
bivariant classes as the multiplication, with associativity, the unit 1 in A^0(X) and the two \
distributive laws, for the Gysin system of the genuine first Chern class rule and with no \
hypothesis on that system"]
def chowCohomologyGRingOfInvertible :
    DirectSum.GRing fun p : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX p := by
  letI gmonoid : GradedMonoid.GMonoid
      fun p : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
    { (chowCohomologyGradedMul C sX).toGMul, chowCohomologyGradedOne C sX with
      one_mul := fun a ↦ Sigma.ext (zero_add a.fst)
        (bivariantIdentityClassOfInvertible_chowCohomologyMulOfInvertible C sX a.snd)
      mul_one := fun a ↦ Sigma.ext (add_zero a.fst)
        (chowCohomologyMulOfInvertible_bivariantIdentityClassOfInvertible C sX a.snd)
      mul_assoc := fun a b c ↦ Sigma.ext (add_assoc a.fst b.fst c.fst)
        (chowCohomologyMulOfInvertible_assoc C sX a.snd b.snd c.snd) }
  letI gsemiring : DirectSum.GSemiring
      fun p : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
    { chowCohomologyGradedMul C sX, gmonoid with
      natCast := fun n ↦ n • bivariantIdentityClassOfInvertible C sX
      natCast_zero := zero_nsmul _
      natCast_succ := fun n ↦ succ_nsmul _ n }
  exact
    { __ := gsemiring
      intCast := fun n ↦ n • bivariantIdentityClassOfInvertible C sX
      intCast_ofNat := fun n ↦ natCast_zsmul _ n
      intCast_negSucc_ofNat := fun n ↦ negSucc_zsmul _ n }

/-- The Chow cohomology `A^*(X)` as a ring, for the Gysin system
`Stacks.Chow.gysinSystemOfInvertible`. -/
@[instance_reducible, stacks 0B7E "the ring structure on the graded group A^*(X), with no \
hypothesis on the Gysin system"]
def chowCohomologyRingOfInvertible :
    Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
  letI : DirectSum.GRing fun p : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
    chowCohomologyGRingOfInvertible C sX
  DirectSum.ring _

/-- The *Chow cohomology* of `X`: the graded `ℤ`-algebra `A^*(X)` whose degree `p` component is
`A^p(X ⟶ X)`, for the Gysin system `Stacks.Chow.gysinSystemOfInvertible`. -/
@[instance_reducible, stacks 0B7E "the graded Z-algebra A^*(X), the Chow cohomology of X, \
with no hypothesis on the Gysin system"]
def chowCohomologyAlgebraOfInvertible :
    @Algebra ℤ (chowCohomology C (gysinSystemOfInvertible C) sX) _
      (chowCohomologyRingOfInvertible C sX).toSemiring :=
  letI : Ring (chowCohomology C (gysinSystemOfInvertible C) sX) :=
    chowCohomologyRingOfInvertible C sX
  inferInstance

end OfInvertible

end Stacks.Chow

end
