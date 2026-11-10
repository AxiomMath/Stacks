module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible

/-!
# Stacks 0FDZ at the Gysin system of the first Chern class rule

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. The constructions of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction` and
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly` prove **Stacks 0FDZ**,

  `A^p(X ⟶ Y) = ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})`,

for a bivariant class stated against an arbitrary `Stacks.Chow.GysinSystem`, and carry three
Gysin compatibilities as hypotheses: `Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion`,
`Stacks.Chow.GysinSystem.IsNaturalUnderOpensRestriction` and
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackComp`. None of the three follows from
`Stacks.Chow.GysinSystem`, whose `chern` field is unconstrained data: the first Chern class rules
a system supplies at two schemes are unrelated, so nothing ties the two Gysin maps together.

This file discharges all three for the **constructed** Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, whose rule is the genuine first Chern class
`Stacks.Chow.firstChernComponentClass`, and restates Stacks 0FDZ there. That system carries no
hypothesis — its vanishing field is the unconditional Stacks 02TO of
`Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence` — so the tag is registered on
declarations assuming nothing at all.

## Main results

* `Stacks.Chow.firstChernComponentClass_congr` — the first Chern class component rule depends only
  on the isomorphism class of the invertible module.
* `Stacks.Chow.chowGroupRestrict_gysinHomomorphismOnChowOfInvertible` — the open-immersion case of
  **Stacks 0B71** for the Gysin map of an invertible module: restriction along an open immersion
  over the base commutes with the Gysin map, across the square of Remark 0B6Y.
* `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction`,
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackComp`,
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion` — the three compatibilities,
  for the Gysin system of the first Chern class rule.
* `Stacks.Chow.bivariantPieceRestrictionOfInvertible`,
  `Stacks.Chow.bivariantPieceRestrictionHomOfInvertible`,
  `Stacks.Chow.bivariantPieceEquivOfInvertible` — **Stacks 0FDZ** at that system, with no Gysin
  compatibility assumed.

## Implementation notes

### Restriction along an open immersion is flat pullback

The open-immersion compatibility is the case `r = 0` of Stacks 0B71, which
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_of_invertible` proves for the genuine rule
with no hypothesis: restriction of cycles along an open immersion is flat pullback in relative
dimension zero (`Stacks.Chow.cycleGroupRestrict_eq_flatPullback`), and the instance of Stacks 02S1
that flat pullback on Chow groups needs along an open immersion is
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion`. The degree
bookkeeping — the flat pullback lands in degree `k + 0` where restriction lands in degree `k` — is
carried by `Stacks.Chow.heq_chowGroupRestrict_flatPullbackChow`.

### Why the statement does not live beside the other case of Stacks 02TA

`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward`, the proper-pushforward case
of Stacks 02TA for a Gysin system, lives in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem` beside the
invertible-module form of the tag in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible`. The open-immersion case
cannot be stated there: its only unconditional input,
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_of_invertible`, lives in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible`, which already
imports both of those modules *and*
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction`, where the predicate is
defined. This file is the first point downstream of all of them.

### The iterated pullback, and why two compatibilities are needed rather than one

The Gysin axiom of `Stacks.Chow.BivariantClass` quantifies over an invertible module on the *test*
scheme, so the module on a piece of a base change is the pullback of that module along the
piece's projection, while the module on the whole base change is the pullback along its own
projection. Neither is the pullback of the other along the comparison: they agree only up to
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, which is an isomorphism and not an equality. So
the open-immersion compatibility in the form the consumers need factors through two statements —
the ambient-module form, which is the geometry, and the invariance of the Gysin map under that
isomorphism, which is `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackComp`. The second
is where `Stacks.Chow.firstChernComponentClass_congr` enters; the two zero schemes are *equal*
(`Stacks.Chow.zeroScheme_pullback_pullback`), both being the inverse image of the zero scheme
downstairs, so only the component rules have to be compared.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open Stacks.Divisors


/-- **The first Chern class component rule depends only on the isomorphism class of the invertible
module.** Isomorphic invertible modules have rationally equivalent component cycles on every
integral closed subscheme, by
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_of_iso`, and the component *class*
rule is the class of the component cycle rule. -/
theorem firstChernComponentClass_congr (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (e : L ≅ N) : firstChernComponentClass C p k L = firstChernComponentClass C p k N := by
  funext W hW hDim
  exact QuotientAddGroup.eq_iff_sub_mem.2
    (rationallyEquivalent_firstChernComponentCycleRule_of_iso C p k L N e W hW hDim)

/-! ### Transport along an equality of zero schemes -/

section Transport

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

omit [LocallyOfFiniteType p] in
/-- The pushforward of a cycle along the inclusion of a closed subscheme into a larger one is
unchanged, up to the transport of its target, by replacing the smaller subscheme with an equal
one. -/
theorem heq_properPushforward_inclusion {D₁ D₂ W : X.IdealSheafData} (hD : D₁ = D₂) (h₁ : D₁ ≤ W)
    (h₂ : D₂ ≤ W)
    [LocallyOfFiniteType (W.subschemeι ≫ p)] [LocallyOfFiniteType (D₁.subschemeι ≫ p)]
    [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (hfac₁ : Scheme.IdealSheafData.inclusion h₁ ≫ (D₁.subschemeι ≫ p) = W.subschemeι ≫ p)
    (hfac₂ : Scheme.IdealSheafData.inclusion h₂ ≫ (D₂.subschemeι ≫ p) = W.subschemeι ≫ p)
    (x : CycleGroup C (W.subschemeι ≫ p) k) :
    HEq (properPushforward C (W.subschemeι ≫ p) (D₁.subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion h₁) hfac₁ k x)
      (properPushforward C (W.subschemeι ≫ p) (D₂.subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion h₂) hfac₂ k x) := by
  subst hD
  rfl

omit [LocallyOfFiniteType p] in
/-- The fundamental cycle of the inverse image of a closed subscheme in a second one is unchanged,
up to transport, by replacing the second subscheme with an equal one. -/
theorem heq_cycleAssociatedToClosedSubscheme_comap {D₁ D₂ : X.IdealSheafData} (hD : D₁ = D₂)
    (W : X.IdealSheafData) [LocallyOfFiniteType (D₁.subschemeι ≫ p)]
    [LocallyOfFiniteType (D₂.subschemeι ≫ p)] :
    HEq (cycleAssociatedToClosedSubscheme C (D₁.subschemeι ≫ p)
        ((W.comap D₁.subschemeι).subschemeι) k)
      (cycleAssociatedToClosedSubscheme C (D₂.subschemeι ≫ p)
        ((W.comap D₂.subschemeι).subschemeι) k) := by
  subst hD
  rfl

/-- Two rules on integral components attached to equal closed subschemes, agreeing on every
component, have heterogeneously equal extensions to Chow groups. -/
theorem heq_extendChow {D₁ D₂ : X.IdealSheafData} (hD : D₁ = D₂)
    [LocallyOfFiniteType (D₁.subschemeι ≫ p)] [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (R₁ : IntegralComponentRule C p (D₁.subschemeι ≫ p) D₁.subschemeι k)
    (R₂ : IntegralComponentRule C p (D₂.subschemeι ≫ p) D₂.subschemeι k)
    (hR : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      HEq (R₁.cycle W hW hDim) (R₂.cycle W hW hDim)) :
    HEq R₁.extendChow R₂.extendChow := by
  subst hD
  obtain ⟨c₁, hs₁⟩ := R₁
  obtain ⟨c₂, hs₂⟩ := R₂
  have hc : c₁ = c₂ := by
    funext W hW hDim
    exact eq_of_heq (hR W hW hDim)
  subst hc
  rfl

omit [LocallyOfFiniteType p] in
/-- Restriction of Chow classes along the transport of an equality of closed subschemes carries a
class to any class heterogeneously equal to it. -/
theorem chowGroupRestrict_eqToHom_of_heq {D₁ D₂ : X.IdealSheafData} (hD : D₂ = D₁)
    [LocallyOfFiniteType (D₁.subschemeι ≫ p)] [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (x : chowGroup C (D₁.subschemeι ≫ p) k) (y : chowGroup C (D₂.subschemeι ≫ p) k)
    (hxy : HEq x y) :
    chowGroupRestrict C (D₁.subschemeι ≫ p) (D₂.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD))
        (by rw [← Category.assoc, subschemeι_eqToHom hD]) k x = y := by
  subst hD
  obtain rfl := eq_of_heq hxy
  exact chowGroupRestrict_id C _ k x

/-- Restriction of Chow classes along the transport of an equality of closed subschemes carries
the value of a map to the value of any heterogeneously equal map. -/
theorem chowGroupRestrict_eqToHom_apply_of_heq {D₁ D₂ : X.IdealSheafData} (hD : D₂ = D₁)
    [LocallyOfFiniteType (D₁.subschemeι ≫ p)] [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (F₁ : chowGroup C p (k + 1) →+ chowGroup C (D₁.subschemeι ≫ p) k)
    (F₂ : chowGroup C p (k + 1) →+ chowGroup C (D₂.subschemeι ≫ p) k) (hF : HEq F₁ F₂)
    (α : chowGroup C p (k + 1)) :
    chowGroupRestrict C (D₁.subschemeι ≫ p) (D₂.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD))
        (by rw [← Category.assoc, subschemeι_eqToHom hD]) k (F₁ α) = F₂ α := by
  subst hD
  obtain rfl := eq_of_heq hF
  exact chowGroupRestrict_id C _ k _

/-- Two descended Gysin maps attached to equal closed subschemes and equal component rules are
heterogeneously equal: the descent hypotheses are propositions. -/
theorem heq_quotientLift {D₁ D₂ : X.IdealSheafData} (hD : D₁ = D₂)
    [LocallyOfFiniteType (D₁.subschemeι ≫ p)] [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (F₁ : CycleGroup C p (k + 1) →+ chowGroup C (D₁.subschemeι ≫ p) k)
    (F₂ : CycleGroup C p (k + 1) →+ chowGroup C (D₂.subschemeι ≫ p) k) (hF : HEq F₁ F₂)
    (h₁ : ∀ α ∈ rationalEquivalences C p (k + 1), F₁ α = 0)
    (h₂ : ∀ α ∈ rationalEquivalences C p (k + 1), F₂ α = 0) :
    HEq (QuotientAddGroup.lift (rationalEquivalences C p (k + 1)) F₁ h₁)
      (QuotientAddGroup.lift (rationalEquivalences C p (k + 1)) F₂ h₂) := by
  subst hD
  obtain rfl := eq_of_heq hF
  rfl

end Transport

/-! ### The Gysin map of an invertible module sees only the zero scheme and the component rule -/

section Congr

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (s : Γ(L, ⊤)) (t : Γ(N, ⊤))

/-- **The Gysin component cycle depends on the module and the section only through the zero
scheme.** Both branches of its defining case distinction — the pushforward of a representative of
the component rule when the component is contained in the zero scheme, and the fundamental cycle
of the intersection when it is not — are functions of the zero scheme alone. -/
theorem heq_gysinComponentCycle (chern : FirstChernComponentClassRule C p k)
    (hZ : Stacks.Divisors.zeroScheme X L s = Stacks.Divisors.zeroScheme X N t)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    HEq (gysinComponentCycle C p k L s chern W hW hDim)
      (gysinComponentCycle C p k N t chern W hW hDim) := by
  by_cases hle : Stacks.Divisors.zeroScheme X L s ≤ W
  · have hle' : Stacks.Divisors.zeroScheme X N t ≤ W := hZ ▸ hle
    rw [gysinComponentCycle_of_le C p k L s chern W hW hDim hle,
      gysinComponentCycle_of_le C p k N t chern W hW hDim hle']
    exact heq_properPushforward_inclusion C p k hZ hle hle' _ _ _
  · have hle' : ¬ Stacks.Divisors.zeroScheme X N t ≤ W := by
      rw [← hZ]; exact hle
    rw [gysinComponentCycle_of_not_le C p k L s chern W hW hDim hle,
      gysinComponentCycle_of_not_le C p k N t chern W hW hDim hle']
    exact heq_cycleAssociatedToClosedSubscheme_comap C p k hZ W

/-- **The Gysin map on cycles depends on the module and the section only through the zero scheme
and the component rule.** -/
theorem heq_gysinHomomorphism (chern : FirstChernComponentClassRule C p k)
    (hZ : Stacks.Divisors.zeroScheme X L s = Stacks.Divisors.zeroScheme X N t) :
    HEq (gysinHomomorphism C p k L s chern) (gysinHomomorphism C p k N t chern) :=
  heq_extendChow C p k hZ (gysinRule C p k L s chern) (gysinRule C p k N t chern)
    (heq_gysinComponentCycle C p k L N s t chern hZ)

/-- **The descended Gysin map of an invertible module depends on the module only through the zero
scheme and the isomorphism class.** The component rule is an isomorphism invariant by
`Stacks.Chow.firstChernComponentClass_congr`, and the Gysin map sees the module and the section
only through that rule and the zero scheme. -/
theorem heq_gysinHomomorphismOnChowOfInvertible (e : L ≅ N)
    (hZ : Stacks.Divisors.zeroScheme X L s = Stacks.Divisors.zeroScheme X N t)
    (h₁ : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s)
    (h₂ : GysinOfInvertibleFactorsThroughRationalEquivalence C p k N t) :
    HEq (gysinHomomorphismOnChowOfInvertible C p k L s h₁)
      (gysinHomomorphismOnChowOfInvertible C p k N t h₂) := by
  have hchern : firstChernComponentClass C p k L = firstChernComponentClass C p k N :=
    firstChernComponentClass_congr C p k L N e
  refine heq_quotientLift C p k hZ _ _ ?_ h₁ h₂
  change HEq (gysinHomomorphism C p k L s (firstChernComponentClass C p k L))
    (gysinHomomorphism C p k N t (firstChernComponentClass C p k N))
  rw [hchern]
  exact heq_gysinHomomorphism C p k L N s t (firstChernComponentClass C p k N) hZ

end Congr

/-- The Gysin map of an invertible module on cycles, read at two equal degrees and at two cycles
with the same underlying cycle, gives heterogeneously equal classes. -/
theorem heq_gysinHomomorphismOfInvertible (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {k l : ℤ} (hkl : k = l) (x : CycleGroup C p (k + 1))
    (y : CycleGroup C p (l + 1)) (hxy : x.1 = y.1) :
    HEq (gysinHomomorphismOfInvertible C p k L s x)
      (gysinHomomorphismOfInvertible C p l L s y) := by
  subst hkl
  exact heq_of_eq (congrArg (gysinHomomorphismOfInvertible C p k L s) (Subtype.ext hxy))


/-- The morphism of Remark 0B6Y is an open immersion when `f` is: it is the base change of `f`
along the closed immersion of the zero scheme. -/
instance isOpenImmersion_zeroSchemePullbackHom {X X' : Scheme.{u}} (f : X' ⟶ X)
    [IsOpenImmersion f] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) : IsOpenImmersion (zeroSchemePullbackHom f L s) := by
  have h : zeroSchemePullbackHom f L s =
      eqToHom (congrArg Scheme.IdealSheafData.subscheme (zeroScheme_pullback f L s)) ≫
        comapSubschemeMap (Stacks.Divisors.zeroScheme X L s) f := by
    refine (eq_zeroSchemePullbackHom f L s _ ?_).symm
    rw [Category.assoc, comapSubschemeMap_comp_subschemeι, ← Category.assoc,
      subschemeι_eqToHom (zeroScheme_pullback f L s)]
  rw [h]
  infer_instance


/-- **The open-immersion case of Stacks 0B71 for the Gysin map of an invertible module.**
Restriction of Chow classes along an open immersion `u : A ⟶ B` over the base carries the Gysin
map of `Z(s)` to the Gysin map of `Z(u^*s)`, the restriction downstairs being taken along the
morphism `Stacks.Chow.zeroSchemePullbackHom` of Remark 0B6Y.

Restriction along an open immersion is flat pullback in relative dimension zero, by
`Stacks.Chow.cycleGroupRestrict_eq_flatPullback`, so this is
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_of_invertible` at `r = 0`, read on Chow
classes and with the degree transported from `k + 0` to `k`. It carries no hypothesis beyond the
two instances of Stacks 02TO that the two descended Gysin maps need. -/
theorem chowGroupRestrict_gysinHomomorphismOnChowOfInvertible (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsOpenImmersion u]
    (k : ℤ) (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hB : GysinOfInvertibleFactorsThroughRationalEquivalence C sB k L s)
    (hA : GysinOfInvertibleFactorsThroughRationalEquivalence C (u ≫ sB) k
      ((Scheme.Modules.pullback u).obj L) (AlgebraicGeometry.pullbackGlobalSections u L s))
    (α : chowGroup C sB (k + 1)) :
    chowGroupRestrict C ((Stacks.Divisors.zeroScheme B L s).subschemeι ≫ sB)
        ((pullbackZeroScheme u L s).subschemeι ≫ (u ≫ sB)) (zeroSchemePullbackHom u L s)
        (zeroSchemePullbackHom_comp u L s C sB (u ≫ sB) rfl) k
        (gysinHomomorphismOnChowOfInvertible C sB k L s hB α) =
      gysinHomomorphismOnChowOfInvertible C (u ≫ sB) k ((Scheme.Modules.pullback u).obj L)
        (AlgebraicGeometry.pullbackGlobalSections u L s) hA
        (chowGroupRestrict C sB (u ≫ sB) u rfl (k + 1) α) := by
  have hr : AlgebraicGeometry.RelativeDimension u 0 := relativeDimension_of_isOpenImmersion u
  have hrj : AlgebraicGeometry.RelativeDimension (zeroSchemePullbackHom u L s) 0 :=
    relativeDimension_of_isOpenImmersion _
  have hfacj := flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C
    ((Stacks.Divisors.zeroScheme B L s).subschemeι ≫ sB)
    ((pullbackZeroScheme u L s).subschemeι ≫ (u ≫ sB)) (zeroSchemePullbackHom u L s)
    (zeroSchemePullbackHom_comp u L s C sB (u ≫ sB) rfl) k
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    have h1 := heq_chowGroupRestrict_flatPullbackChow C
      ((Stacks.Divisors.zeroScheme B L s).subschemeι ≫ sB)
      ((pullbackZeroScheme u L s).subschemeι ≫ (u ≫ sB)) (zeroSchemePullbackHom u L s)
      (zeroSchemePullbackHom_comp u L s C sB (u ≫ sB) rfl) hrj k hfacj
      (gysinHomomorphismOnChowOfInvertible C sB k L s hB
        (QuotientAddGroup.mk' (rationalEquivalences C sB (k + 1)) c))
    have h2 := gysinHomomorphismOfInvertible_flatPullback_of_invertible C sB u 0 hr k L s c
    have h3 := heq_gysinHomomorphismOfInvertible C (u ≫ sB)
      ((Scheme.Modules.pullback u).obj L) (AlgebraicGeometry.pullbackGlobalSections u L s)
      (by simp : k + ((0 : ℕ) : ℤ) = k)
      ((show k + 1 + ((0 : ℕ) : ℤ) = k + ((0 : ℕ) : ℤ) + 1 by omega) ▸
        flatPullback C (u ≫ sB) sB u rfl 0 hr (k + 1) c)
      (cycleGroupRestrict C sB (u ≫ sB) u rfl (k + 1) c)
      ((val_cycleGroup_cast C (u ≫ sB)
          (show k + 1 + ((0 : ℕ) : ℤ) = k + ((0 : ℕ) : ℤ) + 1 by omega) _).trans
        (cycleGroupRestrict_eq_flatPullback C sB (u ≫ sB) u rfl hr (k + 1) c).symm)
    exact eq_of_heq (h1.trans ((heq_of_eq h2.symm).trans h3))

/-- **The open-immersion case of Stacks 0B71 for the Gysin map of an invertible module**, read
against structure morphisms presented by equalities rather than as literal composites. -/
theorem chowGroupRestrict_gysinHomomorphismOnChowOfInvertible_of_eq (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (u : A ⟶ B) [IsOpenImmersion u] (hu : u ≫ sB = sA) (k : ℤ)
    (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hB : GysinOfInvertibleFactorsThroughRationalEquivalence C sB k L s)
    (hA : GysinOfInvertibleFactorsThroughRationalEquivalence C sA k
      ((Scheme.Modules.pullback u).obj L) (AlgebraicGeometry.pullbackGlobalSections u L s))
    (α : chowGroup C sB (k + 1)) :
    chowGroupRestrict C ((Stacks.Divisors.zeroScheme B L s).subschemeι ≫ sB)
        ((pullbackZeroScheme u L s).subschemeι ≫ sA) (zeroSchemePullbackHom u L s)
        (zeroSchemePullbackHom_comp u L s C sB sA hu) k
        (gysinHomomorphismOnChowOfInvertible C sB k L s hB α) =
      gysinHomomorphismOnChowOfInvertible C sA k ((Scheme.Modules.pullback u).obj L)
        (AlgebraicGeometry.pullbackGlobalSections u L s) hA
        (chowGroupRestrict C sB sA u hu (k + 1) α) := by
  subst hu
  exact chowGroupRestrict_gysinHomomorphismOnChowOfInvertible C sB u k L s hB hA α

/-! ### The Gysin system of the first Chern class rule satisfies the three naturalities -/

/-- The Gysin map of an invertible module does not see the difference between an iterated pullback
and the pullback along the composite. -/
private theorem heq_gysinHomomorphismOnChowOfInvertible_pullbackComp (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) (v : X ⟶ Y) (w : Y ⟶ Z)
    (L : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (h₁ : GysinOfInvertibleFactorsThroughRationalEquivalence C q k
      ((Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback w).obj L))
      (AlgebraicGeometry.pullbackGlobalSections v ((Scheme.Modules.pullback w).obj L)
        (AlgebraicGeometry.pullbackGlobalSections w L s)))
    (h₂ : GysinOfInvertibleFactorsThroughRationalEquivalence C q k
      ((Scheme.Modules.pullback (v ≫ w)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (v ≫ w) L s)) :
    HEq (gysinHomomorphismOnChowOfInvertible C q k
        ((Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback w).obj L))
        (AlgebraicGeometry.pullbackGlobalSections v ((Scheme.Modules.pullback w).obj L)
          (AlgebraicGeometry.pullbackGlobalSections w L s)) h₁)
      (gysinHomomorphismOnChowOfInvertible C q k ((Scheme.Modules.pullback (v ≫ w)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (v ≫ w) L s) h₂) :=
  heq_gysinHomomorphismOnChowOfInvertible C q k ((Scheme.Modules.pullback v).obj
    ((Scheme.Modules.pullback w).obj L)) ((Scheme.Modules.pullback (v ≫ w)).obj L) _ _
    ((Scheme.Modules.pullbackComp v w).app L) (zeroScheme_pullback_pullback v w L s) h₁ h₂

/-- **The open-immersion case of Stacks 02TA for the Gysin operation of a Gysin system, with the
module on the ambient scheme.** The Gysin system of the first Chern class rule of an invertible
module is natural under restriction along an open immersion over the base, with no hypothesis.

Its Gysin operation is `Stacks.Chow.gysinHomomorphismOnChowOfInvertible`, so this is
`Stacks.Chow.chowGroupRestrict_gysinHomomorphismOnChowOfInvertible_of_eq`, the open-immersion case
of Stacks 0B71 at that map, after the quantified open immersion of the two zero schemes is
identified with the morphism of Remark 0B6Y by `Stacks.Chow.eq_zeroSchemePullbackHom`. -/
@[stacks 02TA "the open-immersion case of the naturality of the Gysin operation of a Gysin \
system, for an invertible module on the ambient scheme: restriction along an open immersion over \
the base carries the Gysin map of Z(s) to the Gysin map of Z(u^*s) across the square of Remark \
0B6Y, with no hypothesis"]
theorem gysinSystemOfInvertible_isNaturalUnderOpensRestriction (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).IsNaturalUnderOpensRestriction := by
  intro A B sB _ sA _ u _ hu L _ s k j _ hjsq hj α
  obtain rfl : j = zeroSchemePullbackHom u L s := eq_zeroSchemePullbackHom u L s j hjsq
  exact chowGroupRestrict_gysinHomomorphismOnChowOfInvertible_of_eq C sB sA u hu k L s
    (gysinOfInvertibleDescends C sB L s k)
    (gysinOfInvertibleDescends C sA ((Scheme.Modules.pullback u).obj L)
      (AlgebraicGeometry.pullbackGlobalSections u L s) k) α

/-- **The Gysin operation of the Gysin system of the first Chern class rule does not see the
difference between an iterated pullback of an invertible module and the pullback along the
composite.** The two modules are isomorphic, by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, so their component rules agree by
`Stacks.Chow.firstChernComponentClass_congr`; the two zero schemes are equal by
`Stacks.Chow.zeroScheme_pullback_pullback`; and the Gysin map of an invertible module sees the
module only through those two, by
`Stacks.Chow.heq_gysinHomomorphismOnChowOfInvertible`. -/
theorem gysinSystemOfInvertible_isNaturalUnderPullbackComp (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).IsNaturalUnderPullbackComp := by
  intro A B T q _ v w L _ s k α
  refine chowGroupRestrict_eqToHom_apply_of_heq C q k (zeroScheme_pullback_pullback v w L s).symm
    _ _ ?_ α
  exact heq_gysinHomomorphismOnChowOfInvertible_pullbackComp C q k v w L s _ _

/-- **The open-immersion case of Stacks 02TA for the Gysin operation of a Gysin system.** The
Gysin system of the first Chern class rule of an invertible module is natural under restriction
along an open immersion `u : A ⟶ B` of schemes over a test scheme carrying the module, with no
hypothesis.

The module on `A` is the pullback of the module on the test scheme, not the pullback along `u` of
the module on `B`, so this is not the ambient-module form
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction` but its composite with the
comparison of the two spellings,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackComp`: the quantified open immersion of
the two zero schemes factors as the transport along
`Stacks.Chow.zeroScheme_pullback_pullback` followed by the morphism of Remark 0B6Y, uniquely
because the closed immersion of the zero scheme downstairs is a monomorphism. -/
@[stacks 02TA "the open-immersion case of the naturality of the Gysin operation of a Gysin \
system, for an invertible module pulled back from a test scheme to both schemes -- the form the \
Gysin axiom of a bivariant class quantifies over -- with no hypothesis"]
theorem gysinSystemOfInvertible_isNaturalUnderOpenImmersion (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).IsNaturalUnderOpenImmersion := by
  intro A B T t _ qA _ qB _ u _ hu L _ s k _ _ j _ hjsq hj α
  subst hu
  have hZZ := zeroScheme_pullback_pullback u qB L s
  have hassoc : u ≫ (qB ≫ t) = (u ≫ qB) ≫ t := (Category.assoc u qB t).symm
  obtain rfl : j = eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ.symm) ≫
      zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) := by
    refine (cancel_mono (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι).1 ?_
    rw [hjsq, Category.assoc, zeroSchemePullbackHom_subschemeι, ← Category.assoc,
      subschemeι_eqToHom hZZ.symm]
  rw [← chowGroupRestrict_comp C
    ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ (qB ≫ t))
    ((pullbackZeroScheme u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ ((u ≫ qB) ≫ t))
    (zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s))
    (zeroSchemePullbackHom_comp u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s) C (qB ≫ t) ((u ≫ qB) ≫ t) hassoc) k
    ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback (u ≫ qB)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (u ≫ qB) L s)).subschemeι ≫ ((u ≫ qB) ≫ t))
    (eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ.symm))
    (by rw [← Category.assoc, subschemeι_eqToHom hZZ.symm])]
  rw [gysinSystemOfInvertible_onChow, gysinSystemOfInvertible_onChow,
    chowGroupRestrict_gysinHomomorphismOnChowOfInvertible_of_eq C (qB ≫ t) ((u ≫ qB) ≫ t) u
    hassoc k ((Scheme.Modules.pullback qB).obj L)
    (AlgebraicGeometry.pullbackGlobalSections qB L s)
    (gysinOfInvertibleDescends C (qB ≫ t) ((Scheme.Modules.pullback qB).obj L) _ k)
    (gysinOfInvertibleDescends C ((u ≫ qB) ≫ t) _ _ k) α]
  exact chowGroupRestrict_eqToHom_apply_of_heq C ((u ≫ qB) ≫ t) k hZZ.symm _ _
    (heq_gysinHomomorphismOnChowOfInvertible_pullbackComp C _ k u qB L s _ _) _

/-! ### Stacks 0FDZ at the Gysin system of the first Chern class rule -/

section Unconditional

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) {I J : Type u}
  (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i))

/-- **Stacks 0FDZ.** The restriction `c_i` of a bivariant class `c` of degree `p` for `f : X ⟶ Y`
to the piece `f_i : X_i ⟶ Y_{a(i)}` of a disjoint union decomposition, at the Gysin system of the
first Chern class rule of an invertible module.

This is `Stacks.Chow.bivariantPieceRestriction` with its Gysin compatibility discharged by
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion`, so it assumes nothing. -/
@[stacks 0FDZ "the restriction of a bivariant class to a piece, at the Gysin system of the first \
Chern class rule, with the open-immersion case of Stacks 02TA discharged"]
def bivariantPieceRestrictionOfInvertible (i : I)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    BivariantClass C (gysinSystemOfInvertible C) ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
      (pieceMap f UX UY a ha i)
      (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p :=
  bivariantPieceRestriction C (gysinSystemOfInvertible C) sX sY f hf p UX UY a ha i
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c

/-- **Stacks 0FDZ.** The map `A^p(X ⟶ Y) ⟶ ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})` of the tag at the Gysin
system of the first Chern class rule of an invertible module, with no Gysin compatibility
assumed. -/
@[stacks 0FDZ "the map from A^p(X ⟶ Y) to the product over the pieces, at the Gysin system of \
the first Chern class rule, with the open-immersion case of Stacks 02TA discharged"]
def bivariantPieceRestrictionHomOfInvertible :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p →+
      ∀ i, BivariantClass C (gysinSystemOfInvertible C) ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
        (pieceMap f UX UY a ha i)
        (pieceMap_comp_structureMorphism C sX sY f hf UX UY a ha i) p :=
  bivariantPieceRestrictionHom C (gysinSystemOfInvertible C) sX sY f hf p UX UY a ha
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)

/-- **Stacks 0FDZ.** `A^p(X ⟶ Y) = ∏_{i ∈ I} A^p(X_i ⟶ Y_{a(i)})` at the Gysin system of the
first Chern class rule of an invertible module: a bivariant class of degree `p` for `f : X ⟶ Y`
is the same thing as a family of bivariant classes of degree `p` for the restrictions
`f_i : X_i ⟶ Y_{a(i)}`.

This is `Stacks.Chow.bivariantPieceEquiv` with all three of its Gysin compatibilities discharged,
by `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion`,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction` and
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackComp`. Nothing remains assumed: the
Gysin system itself carries no hypothesis either. -/
@[stacks 0FDZ "A^p(X ⟶ Y) = ∏_i A^p(X_i ⟶ Y_{a(i)}) at the Gysin system of the first Chern \
class rule, with all three Gysin compatibilities discharged"]
def bivariantPieceEquivOfInvertible (hX : IsClopenDecomposition UX) :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p ≃+
      ∀ i, BivariantClass C (gysinSystemOfInvertible C) ((UX i).ι ≫ sX) ((UY (a i)).ι ≫ sY)
        (pieceMap f UX UY a ha i)
        (pieceMap_comp_pieceStructureMorphism C sX sY f hf UX UY a ha i) p :=
  bivariantPieceEquiv C (gysinSystemOfInvertible C) sX sY f hf UX UY a ha hX p
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)

/-- **Stacks 0FDZ.** The isomorphism of the tag is restriction to the pieces. -/
@[simp]
theorem bivariantPieceEquivOfInvertible_apply (hX : IsClopenDecomposition UX)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) (i : I) :
    bivariantPieceEquivOfInvertible C sX sY f hf p UX UY a ha hX c i =
      bivariantPieceRestrictionOfInvertible C sX sY f hf p UX UY a ha i c :=
  rfl

end Unconditional

end Stacks.Chow

end
