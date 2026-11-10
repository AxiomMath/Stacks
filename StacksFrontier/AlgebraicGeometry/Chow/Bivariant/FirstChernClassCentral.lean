module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChowInjective
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClassCanonical

/-!
# The first Chern class is central in the Chow cohomology ring

Clause (1) of Stacks 0B7B for the first Chern class built from the canonical Gysin system. The
full statement, both clauses, for the bivariant class of Stacks 0B77, is
`Stacks.Chow.GenuineChern.firstChernClass_mem_center` and
`Stacks.Chow.GenuineChern.comp_firstChernClass`.

## References

* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

namespace Stacks.Chow

/-! ### The line bundle of an invertible module on a test scheme -/

/-- The line-bundle situation of an invertible module on a scheme, with the scheme itself as the
base: the datum `Stacks.LineBundle.Situation` carries a structure morphism that the total space,
its projection and its zero section do not depend on. -/
abbrev lineBundleSituation (T : Scheme.{u}) (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M] :
    Stacks.LineBundle.Situation.{u} where
  X := T
  S := T
  f := 𝟙 T
  L := M

/-! ### Two inputs the naturality axioms of a bivariant class need -/

/-- Negation respects heterogeneous equality of Chow classes across an equality of degrees. -/
private theorem heq_neg_chowGroup {C : ChowSituation.{u}} {A : Scheme.{u}} (q : A ⟶ C.S)
    [LocallyOfFiniteType q] {i j : ℤ} (hij : i = j) {x : chowGroup C q i} {y : chowGroup C q j}
    (h : HEq x y) : HEq (-x) (-y) := by
  subst hij
  exact heq_of_eq (congrArg Neg.neg (eq_of_heq h))

/-- **The relative dimension of the base change of a test morphism.** The flat-pullback axiom of
a bivariant class quantifies over a base change `h'` of the flat test morphism `h` *together
with* its relative dimension, so a consumer applying the axiom has to produce the latter. It can:
relative dimension is stable under base change, which is
`AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension` being a
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` — the same route
`Stacks.Chow.relativeDimension_pullback_snd` takes.

(The implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass` say that this cannot be
produced here, Stacks 02NK being absent. That is stale: the stability instance is present, and
`Stacks.Chow.relativeDimension_pullback_snd` of
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension` is Stacks 02NK.) -/
theorem relativeDimension_bivariantBaseChangeMap {X' X T T' : Scheme.{u}} (f : X' ⟶ X)
    (g : T ⟶ X) (h : T' ⟶ T) [LocallyOfFiniteType h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) :
    letI : LocallyOfFiniteType (bivariantBaseChangeMap f g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h)
        (P := @LocallyOfFiniteType) inferInstance
    AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap f g h) r := by
  have : LocallyOfFiniteType (bivariantBaseChangeMap f g h) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h)
      (P := @LocallyOfFiniteType) inferInstance
  exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension r)
    (isPullback_bivariantBaseChangeMap f g h) ⟨inferInstance, hr⟩).2

/-- **Stacks 0B76 (1) on the test schemes, read against a test morphism presented by an
equality.** The projection formula for an identity cap rule, with the source test morphism given
as a morphism `m` together with `hm : h ≫ g = m` rather than as the literal composite `h ≫ g`.

This is needed for the zero section `o : T ⟶ L` of a line bundle, whose composite with the
projection is the identity of `T`: the source test morphism of the projection formula is then
`o ≫ (p ≫ g)`, which *is* `g` but is not the term `g`. The counterpart for the cap operation of
a bivariant class is `Stacks.Chow.BivariantClass.proper_naturality_of_test_eq`. -/
theorem IdentityCapRule.ProperNaturality.of_test_eq {C : ChowSituation.{u}} {X : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {p : ℤ} {op : IdentityCapRule C sX p}
    (hop : IdentityCapRule.ProperNaturality C sX p op) {T T' : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (m : T' ⟶ X) [LocallyOfFiniteType m]
    (hm : h ≫ g = m) (k : ℤ) (hmb : h ≫ (g ≫ sX) = m ≫ sX)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (m ≫ sX) (g ≫ sX) h hmb k)
    (hfacp : ProperPushforwardFactorsThroughRationalEquivalence C (m ≫ sX) (g ≫ sX) h hmb
      (k - p))
    (α : chowGroup C (m ≫ sX) k) :
    op g k (properChowPushforward C (m ≫ sX) (g ≫ sX) h hmb k hfac α) =
      properChowPushforward C (m ≫ sX) (g ≫ sX) h hmb (k - p) hfacp (op m k α) := by
  subst hm
  exact hop g h k hfac hfacp α

/-! ### Clause (5) of Stacks 0F96 and Stacks 0B74 with the structure morphism independent -/

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- **Clause (5) of Stacks 0F96** with the structure morphism of the total space given as an
independent morphism `sL` together with `hsL : p ≫ sX = sL`, which is the shape the naturality
axioms of a bivariant class present it in: they speak of the test morphism `p ≫ g` and hence of
the structure morphism `(p ≫ g) ≫ sX`, while
`Stacks.Chow.zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow` is stated
at `p ≫ (g ≫ sX)`. The two are the same morphism and not the same term. -/
theorem zeroSection_eq_neg_flatPullback_firstChernClassCapChow_of_base
    (sL : D.totalSpace ⟶ C.S) [LocallyOfFiniteType sL]
    (hsL : D.totalSpaceToBase ≫ sX = sL) (hz : D.zeroSection ≫ sL = sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sL D.zeroSection hz (k + 1))
    (hflat : FlatPullbackFactorsThroughRationalEquivalence C sL sX D.totalSpaceToBase hsL 1
      D.relativeDimension_totalSpaceToBase k)
    (hcast : k + ((1 : ℕ) : ℤ) = k + 1) (α : chowGroup C sX (k + 1)) :
    properChowPushforward C sX sL D.zeroSection hz (k + 1) hfac α =
      -chowGroupCast C sL hcast
        (flatPullbackChow C sL sX D.totalSpaceToBase hsL 1
          D.relativeDimension_totalSpaceToBase k hflat
          (firstChernClassCapChow C k sX D.L α)) := by
  subst hsL
  exact zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow C D sX k α

/-- **Stacks 0B74, the injectivity half**, with the structure morphism of the total space given
as an independent morphism; see
`Stacks.Chow.zeroSection_eq_neg_flatPullback_firstChernClassCapChow_of_base`. -/
theorem flatPullbackChow_totalSpaceToBase_injective_of_base
    (sL : D.totalSpace ⟶ C.S) [LocallyOfFiniteType sL]
    (hsL : D.totalSpaceToBase ≫ sX = sL) (k : ℤ)
    (hflat : FlatPullbackFactorsThroughRationalEquivalence C sL sX D.totalSpaceToBase hsL 1
      D.relativeDimension_totalSpaceToBase k) :
    Function.Injective
      (flatPullbackChow C sL sX D.totalSpaceToBase hsL 1
        D.relativeDimension_totalSpaceToBase k hflat) := by
  subst hsL
  exact flatPullbackChow_totalSpaceToBase_injective C D sX
    D.relativeDimension_totalSpaceToBase k hflat

/-! ### The cap-level identity of Stacks 0B7B -/

/-- **The cap-level identity of Stacks 0B7B.** An identity cap rule satisfying the proper and
flat naturality axioms of Stacks 0B76 commutes with the first Chern class cap product of
Stacks 02TI on every test scheme, the invertible module being the one of a line-bundle situation
whose base is the test scheme.

This is the content of the source's proof: both sides become equal after flat pullback along the
projection `p : L ⟶ T` of the line bundle — on the left by the flat axiom of the rule and clause
(5) of Stacks 0F96, on the right by clause (5) again — and `p^*` is injective by Stacks 0B74.

Instantiated at the rule a bivariant class `c ∈ A^p(X)` induces
(`Stacks.Chow.BivariantClass.toIdentityCapRule`, whose two axioms are
`Stacks.Chow.BivariantClass.toIdentityCapRule_properNaturality` and
`Stacks.Chow.BivariantClass.toIdentityCapRule_flatNaturalityAlongBaseChange`) and at the line
bundle of `g^*ℒ`, this is clause (1) of Stacks 0B7B read on the test schemes. The invertible
module is allowed to be an arbitrary one on the test scheme rather than a pullback of one on `X`,
which is what the proof gives. -/
theorem firstChernClassCapChow_identityCapRule_comm (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ) (op : IdentityCapRule C sX p)
    (hproper : IdentityCapRule.ProperNaturality C sX p op)
    (hflat : IdentityCapRule.FlatNaturalityAlongBaseChange C sX p op)
    (D : Stacks.LineBundle.Situation.{u}) (g : D.X ⟶ X) [LocallyOfFiniteType g] (m : ℤ)
    (hcast : m + 1 - p = m - p + 1) (β : chowGroup C (g ≫ sX) (m + 1)) :
    op g m (firstChernClassCapChow C m (g ≫ sX) D.L β) =
      firstChernClassCapChow C (m - p) (g ≫ sX) D.L
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hcast) (op g (m + 1) β)) := by
  have hsL : D.totalSpaceToBase ≫ (g ≫ sX) = (D.totalSpaceToBase ≫ g) ≫ sX :=
    (Category.assoc _ _ _).symm
  have ho : D.zeroSection ≫ (D.totalSpaceToBase ≫ g) = g := by
    rw [← Category.assoc, D.zeroSection_comp_totalSpaceToBase, Category.id_comp]
  have hz : D.zeroSection ≫ ((D.totalSpaceToBase ≫ g) ≫ sX) = g ≫ sX := by
    rw [← Category.assoc, ho]
  refine flatPullbackChow_totalSpaceToBase_injective_of_base C D (g ≫ sX)
    ((D.totalSpaceToBase ≫ g) ≫ sX) hsL (m - p)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ hsL 1
      D.relativeDimension_totalSpaceToBase (m - p)) ?_
  -- clause (5) of Stacks 0F96, reindexed, in an arbitrary degree
  have key : ∀ (n : ℤ) (γ : chowGroup C (g ≫ sX) (n + 1)),
      Eq.mp (congrArg (chowGroup C ((D.totalSpaceToBase ≫ g) ≫ sX))
        (show n + ((1 : ℕ) : ℤ) = n + 1 by simp))
        (flatPullbackChow C ((D.totalSpaceToBase ≫ g) ≫ sX) (g ≫ sX) D.totalSpaceToBase hsL 1
          D.relativeDimension_totalSpaceToBase n
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ hsL 1
            D.relativeDimension_totalSpaceToBase n)
          (firstChernClassCapChow C n (g ≫ sX) D.L γ)) =
      -properChowPushforward C (g ≫ sX) ((D.totalSpaceToBase ≫ g) ≫ sX) D.zeroSection hz (n + 1)
        (properPushforwardFactorsThroughRationalEquivalence C (g ≫ sX)
          ((D.totalSpaceToBase ≫ g) ≫ sX) D.zeroSection hz (n + 1)) γ := by
    intro n γ
    have h := zeroSection_eq_neg_flatPullback_firstChernClassCapChow_of_base C D (g ≫ sX)
      ((D.totalSpaceToBase ≫ g) ≫ sX) hsL hz n
      (properPushforwardFactorsThroughRationalEquivalence C (g ≫ sX)
        ((D.totalSpaceToBase ≫ g) ≫ sX) D.zeroSection hz (n + 1))
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ hsL 1
        D.relativeDimension_totalSpaceToBase n)
      (by simp) γ
    rw [chowGroupCast_eq_eq_mp] at h
    rw [h, neg_neg]
  -- the flat axiom of the rule along the projection of the line bundle
  have hfl := hflat g D.totalSpaceToBase 1 D.relativeDimension_totalSpaceToBase
    (bivariantBaseChangeMap (𝟙 X) g D.totalSpaceToBase)
    (isPullback_bivariantBaseChangeMap (𝟙 X) g D.totalSpaceToBase)
    (by
      simp only [bivariantBaseChangeMap, pullback.map, Category.comp_id, pullback.lift_fst]) m
    (relativeDimension_bivariantBaseChangeMap (𝟙 X) g D.totalSpaceToBase 1
      D.relativeDimension_totalSpaceToBase)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ 1
      D.relativeDimension_totalSpaceToBase m)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ 1
      D.relativeDimension_totalSpaceToBase (m - p))
    (firstChernClassCapChow C m (g ≫ sX) D.L β)
  -- the projection formula of the rule along the zero section
  have hpr := hproper.of_test_eq (D.totalSpaceToBase ≫ g) D.zeroSection g ho (m + 1) hz
    (properPushforwardFactorsThroughRationalEquivalence C (g ≫ sX)
      ((D.totalSpaceToBase ≫ g) ≫ sX) D.zeroSection hz (m + 1))
    (properPushforwardFactorsThroughRationalEquivalence C (g ≫ sX)
      ((D.totalSpaceToBase ≫ g) ≫ sX) D.zeroSection hz (m + 1 - p)) β
  -- the pushforward along the zero section, reindexed
  have hcs := properChowPushforward_cast C (g ≫ sX) ((D.totalSpaceToBase ≫ g) ≫ sX)
    D.zeroSection hz hcast
    (properPushforwardFactorsThroughRationalEquivalence C (g ≫ sX)
      ((D.totalSpaceToBase ≫ g) ≫ sX) D.zeroSection hz (m + 1 - p))
    (properPushforwardFactorsThroughRationalEquivalence C (g ≫ sX)
      ((D.totalSpaceToBase ≫ g) ≫ sX) D.zeroSection hz (m - p + 1)) (op g (m + 1) β)
  refine eq_of_heq (hfl.symm.trans ?_)
  refine HEq.trans (IdentityCapRule.heq_of_heq C sX p op (D.totalSpaceToBase ≫ g)
    (show m + ((1 : ℕ) : ℤ) = m + 1 by simp)
    (chowGroup_cast_heq ((D.totalSpaceToBase ≫ g) ≫ sX)
      (show m + ((1 : ℕ) : ℤ) = m + 1 by simp) _).symm) ?_
  rw [key m β, map_neg, hpr]
  refine HEq.trans ?_ (chowGroup_cast_heq ((D.totalSpaceToBase ≫ g) ≫ sX)
    (show m - p + ((1 : ℕ) : ℤ) = m - p + 1 by simp) _)
  rw [key (m - p)]
  exact heq_neg_chowGroup ((D.totalSpaceToBase ≫ g) ≫ sX) hcast
    ((chowGroup_cast_heq ((D.totalSpaceToBase ≫ g) ≫ sX) hcast _).symm.trans (heq_of_eq hcs))

/-! ### Clause (1) of Stacks 0B7B: the first Chern class is central in `A^*(X)` -/

/-- The identity cap rule induced by the bivariant first Chern class is the first Chern identity
cap rule it was built from. -/
theorem toIdentityCapRule_firstChernClassBivariantCanonical (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C (canonicalGysinSystem C) sX 1
        (firstChernClassBivariantCanonical C sX L) g k α =
      firstChernIdentityCapRule C sX (canonicalFirstChernCapRule C) L g k α :=
  IdentityCapRule.pushforward_transport C sX 1
    (firstChernIdentityCapRule C sX (canonicalFirstChernCapRule C) L) g k α

/-- **Stacks 0B7B, clause (1)**, for the canonical Gysin system. The first Chern class
`c₁(ℒ) ∈ A^1(X)` lies in the centre of the Chow cohomology ring `A^*(X)` of Stacks 0B7E: it
commutes with every `c ∈ A^p(X)`. The comparison
is heterogeneous because the two products land in `A^{p+1}(X)` and `A^{1+p}(X)`, the same integer
and not the same term.

The product is `Stacks.Chow.chowCohomologyMulOfInvertible`, the composite of Stacks 0B75, which
by `Stacks.Chow.chowCohomologyRingMul_gysinSystemOfInvertible` is the composite of the identity cap
rules of the two factors. By `Stacks.Chow.BivariantClass.heq_of_toIdentityCapRule_heq` a bivariant
class for `𝟙 X` is determined by the rule it induces on the test schemes, and by
`Stacks.Chow.chowCohomologyMul_toIdentityCapRule_heq` the rule of a product is the composite of
the two rules; so the statement reduces to
`Stacks.Chow.firstChernClassCapChow_identityCapRule_comm` at the line bundle of `g^*ℒ`. -/
theorem chowCohomologyMul_firstChernClassBivariantCanonical_comm (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (p : ℤ) (c : chowCohomologyComponent C (canonicalGysinSystem C) sX p) :
    chowCohomologyMulOfInvertible C sX p 1 c (firstChernClassBivariantCanonical C sX L) ≍
      chowCohomologyMulOfInvertible C sX 1 p (firstChernClassBivariantCanonical C sX L) c := by
  refine (heq_of_eq (chowCohomologyRingMul_gysinSystemOfInvertible C sX c
    (firstChernClassBivariantCanonical C sX L))).symm.trans (HEq.trans ?_
      (heq_of_eq (chowCohomologyRingMul_gysinSystemOfInvertible C sX
        (firstChernClassBivariantCanonical C sX L) c)))
  change chowCohomologyRingMul C (canonicalGysinSystem C) sX
      (canonicalGysinSystem_isNaturalUnderInverseIso C) c
      (firstChernClassBivariantCanonical C sX L) ≍
    chowCohomologyRingMul C (canonicalGysinSystem C) sX
      (canonicalGysinSystem_isNaturalUnderInverseIso C)
      (firstChernClassBivariantCanonical C sX L) c
  refine BivariantClass.heq_of_toIdentityCapRule_heq C (canonicalGysinSystem C) sX
    (show p + 1 = 1 + p by ring) _ _ fun {T} g _ k α ↦ ?_
  refine (chowCohomologyMul_toIdentityCapRule_heq C (canonicalGysinSystem C) sX
    (canonicalGysinSystem_isNaturalUnderInverseIso C) c
    (firstChernClassBivariantCanonical C sX L) g k α).trans ?_
  refine HEq.trans ?_ (chowCohomologyMul_toIdentityCapRule_heq C (canonicalGysinSystem C) sX
    (canonicalGysinSystem_isNaturalUnderInverseIso C)
    (firstChernClassBivariantCanonical C sX L) c g k α).symm
  rw [toIdentityCapRule_firstChernClassBivariantCanonical,
    toIdentityCapRule_firstChernClassBivariantCanonical,
    firstChernIdentityCapRule_canonical_apply, firstChernIdentityCapRule_canonical_apply,
    firstChernClassCapChow_identityCapRule_comm C sX p
      (BivariantClass.toIdentityCapRule C (canonicalGysinSystem C) sX p c)
      (BivariantClass.toIdentityCapRule_properNaturality C (canonicalGysinSystem C) sX p c)
      (BivariantClass.toIdentityCapRule_flatNaturalityAlongBaseChange C (canonicalGysinSystem C)
        sX p c)
      (lineBundleSituation T ((Scheme.Modules.pullback g).obj L)) g (k - 1) (by omega)]
  have e1 : BivariantClass.toIdentityCapRule C (canonicalGysinSystem C) sX p c g (k - 1 + 1)
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) (show k = k - 1 + 1 by omega)) α) ≍
      BivariantClass.toIdentityCapRule C (canonicalGysinSystem C) sX p c g k α :=
    IdentityCapRule.heq_of_heq C sX p
      (BivariantClass.toIdentityCapRule C (canonicalGysinSystem C) sX p c) g
      (show k - 1 + 1 = k by omega)
      (chowGroup_cast_heq (g ≫ sX) (show k = k - 1 + 1 by omega) α)
  refine heq_firstChernClassCapChow C (g ≫ sX) _ (by omega) ?_
  exact ((chowGroup_cast_heq (g ≫ sX) (show k - 1 + 1 - p = k - 1 - p + 1 by omega) _).trans
    e1).trans (chowGroup_cast_heq (g ≫ sX) (show k - p = k - p - 1 + 1 by omega) _).symm

end Stacks.Chow

end
