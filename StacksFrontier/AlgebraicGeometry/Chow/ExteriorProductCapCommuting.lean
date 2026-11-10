module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductProperPushforward

/-!
# The exterior product by a fundamental class commutes with every cap product

Let `(S, δ)` be a base situation whose base is the spectrum of a field, so that the exterior
product `α × β ∈ CH_{n+m}(X ×_S Y)` of Stacks 0FBV is defined, let `u : Y ⟶ Z` be a morphism of
schemes locally of finite type over `S` and let `c' ∈ A^p(Y ⟶ Z)` be a bivariant class.
**Stacks 0FBY** asserts

  `α × (c' ∩ β) = c' ∩ (α × β)`

in `CH_{n + (m - p)}(X ×_S Y)`, for `α ∈ CH_n(X)` and `β ∈ CH_m(Z)`. The equation is stated as
`Stacks.Chow.CommutesExteriorProductCap` in
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductBivariant`, where it is quantified over every
`α`; this module adds the form for one given `α` and proves it when `α = [X]` is the fundamental
class of an **integral** scheme `X` **flat** over the base of relative dimension `d`.

## Main definitions

* `Stacks.Chow.CommutesExteriorProductCapAt` — the equation of Stacks 0FBY for a single given
  class `α`, with the same two sides `Stacks.Chow.exteriorProductCap` and
  `Stacks.Chow.capExteriorProduct` as the quantified predicate.
* `Stacks.Chow.iteratedExteriorCapIso` — the identification
  `Y ×_Z ((X ×_S Z) ×_Z Z) ≅ X ×_S Y` of the scheme that the iterated cap product of Stacks 0FA2
  lands on, at the test scheme `𝟙 Z`, with the product the equation of Stacks 0FBY is read in.

## Main results

* `Stacks.Chow.commutesExteriorProductCap_iff_forall` — the predicate of Stacks 0FBY is the
  single-class form quantified over `α`, so the two are interchangeable.
* `Stacks.Chow.flatPullbackBivariantClassSnd_cap_heq_chowExteriorProduct` — **clause (1) of
  Stacks 0B0R for the base change of `X` to `Z`**: the class of Stacks 0B78 for
  `pr_Z : X ×_S Z ⟶ Z` caps, at a test scheme `g : T ⟶ Z`, as the exterior product with `[X]`,
  read through the identification `(X ×_S Z) ×_Z T ≅ X ×_S T`.
* `Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass` — **Stacks 0FBY for a
  fundamental class**, the equation above for `α = [X]`.

## Implementation notes

### Why the exterior product may be moved past the cap product at all

By `Stacks.Chow.isExteriorProductBivariantClass_flatPullbackBivariantClass` the operation
`γ ↦ [X] × γ` is the cap operation of a concrete bivariant class towards the base, namely the
flat-pullback class of **Stacks 0B78** for the structure morphism of `X`. What Stacks 0FBY needs
is that this class commutes with `c'` in the sense of **Stacks 0FA2**, and the commuting
statement is about the *base change* of that class to `Z`, which is again a flat-pullback class of
Stacks 0B78 — the one for `pr_Z : X ×_S Z ⟶ Z`, the base change of the structure morphism of `X`.

For a flat-pullback class the commuting is
`Stacks.Chow.bivariantCommute_flatPullbackBivariantClass`, the smooth half of **Stacks 0FF6**,
whose content is the flat-pullback law of Stacks 0B76 (2) for
`c'`. So the source's route through **Stacks 0FBX** — that an arbitrary bivariant class towards
the base commutes with every bivariant class — is not taken here, although
`Stacks.Chow.bivariantCommute_bivariantToBase` is available: for a flat-pullback class the
commuting is the cheaper statement, and taking it directly keeps the hypotheses down to those of
Stacks 0B78. Stacks 0FBX carries, beyond those, Stacks 02S2 and the whole of Stacks 0FBW,
including the generation of Chow groups by proper pushforwards of flat pullbacks; none of that is
needed for the class treated here.

### What is proved and what is not

The class `α` is a fundamental class and not an arbitrary element of `CH_n(X)`. The reason is the
one recorded in `StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductFundamentalClassBivariant`:
`Stacks.Chow.IsExteriorProductBivariantClass` — Stacks 0FBW in its exterior-product form, the
input Stacks 0FBY consumes — is available in this repository exactly for the fundamental classes
of integral schemes flat over the base, because the only statement relating the exterior product
to a flat pullback along a product projection is clause (1) of **Stacks 0B0R**, which requires the
factor it replaces to be such a fundamental class.

The shortest route to a general `α` needs two statements this repository does not have: proper
naturality of the exterior product in its *first* variable, along the morphism
`g × 1_Y : W ×_S Y ⟶ X ×_S Y`, which is the mirror of
`Stacks.Chow.chowExteriorProduct_properChowPushforward_fundamentalChowClass`; and the identity
`[W] × γ = pr_T^* γ` for the flat-pullback base class of a `W` that need not be integral, which
needs Stacks 02R4. Granted those, `Stacks.Chow.bivariantToBaseEquiv` is an isomorphism of groups,
so `α ↦ c_α` is additive and the classes satisfying
`Stacks.Chow.IsExteriorProductBivariantClass` form a subgroup, and
`Stacks.Chow.ChowClassesGeneratedByBaseFlatPullbacks` reduces the general case to generators.

### How the two sides are transported

`Stacks.Chow.BivariantCommute` compares two iterated cap products at a test scheme `t : T ⟶ Z`.
Taking `t = 𝟙 Z` makes the test class the class `β` of the equation, at the cost of three fibre
products of the form `A ×_Z Z`:

* the left-hand iterated cap `c_{[X]} ∩ (c' ∩ β)` lands on `(X ×_S Z) ×_Z (Y ×_Z Z)`, and
  `Stacks.Chow.BivariantClass.capTarget` collapses the inner `Y ×_Z Z` onto `Y` before taking the
  exterior product, so the comparison is the isomorphism case of condition (1) of Stacks 0B76,
  `Stacks.Chow.BivariantClass.cap_chowPushforwardOfTestIso`, followed by the identification
  `(X ×_S Z) ×_Z Y ≅ X ×_S Y`, which is
  `CategoryTheory.Limits.pullbackLeftPullbackSndIso`;
* the right-hand iterated cap `c' ∩ (c_{[X]} ∩ β)` lands on `Y ×_Z ((X ×_S Z) ×_Z Z)`, and the
  same isomorphism case of condition (1) of Stacks 0B76 collapses the inner `(X ×_S Z) ×_Z Z`
  onto `X ×_S Z`, after which `Stacks.Chow.exteriorCapIso` identifies `Y ×_Z (X ×_S Z)` with
  `X ×_S Y`.

The two resulting routes out of `(X ×_S Z) ×_Z (Y ×_Z Z)` agree, which is
`Stacks.Chow.commuteComparisonHom_comp_iteratedExteriorCapIso` and the only geometric input of
the transport. Everything else is bookkeeping: the degrees `(m - p) + d`, `(m - p) - (-d)` and
`d + (m - p)` are one integer written three ways, and `Stacks.Chow.chowGroupDegreeEquiv`,
`Stacks.Chow.chowGroupCongr` and the congruence lemmas up to heterogeneous equality move the
transports out of the way, as everywhere in this part of the library.

## The hypotheses carried

Three, all of them already carried by Stacks 0B78 in this repository, and none of them a part of
the conclusion:

* `hfp : Stacks.Chow.FlatPullbackDescends C` is **Stacks 02S1**. Without it neither
  `Stacks.Chow.flatPullbackChow` nor `Stacks.Chow.chowExteriorProduct` exists, so it is a
  prerequisite of writing the equation down at all.
* `hRG : Stacks.Chow.ProperPushforwardFlatPullbackBaseChange C` is **Stacks 02RG** on Chow
  groups, in the four-corner form of the source.
* `h71 : G.FlatPullbackNaturality d` is **Stacks 0B71** on Chow groups together with the
  identification of **Stacks 0B6Y**.

The last two are consumed only by `Stacks.Chow.flatPullbackBivariantClass`, where they discharge
the proper-pushforward and the Gysin conditions of Stacks 0B76; they are exactly the hypotheses of
Stacks 0B78 and say nothing about the exterior product. Stacks 02S2 is **not** carried: the only
pushforwards occurring are along isomorphisms over the base, for which
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isIso` settles it outright.

## References

* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The equation of Stacks 0FBY for a single class -/

section Statement

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ)
  (hfp : FlatPullbackDescends C)

/-- **Stacks 0FBY for a single class `α`**: for every `β ∈ CH_m(Z)` the exterior product with the
given `α ∈ CH_n(X)` commutes with the cap product of `c ∈ A^p(Y ⟶ Z)`,

  `α × (c ∩ β) = c ∩ (α × β)`,

both sides read in `CH_{n + (m - p)}(X ×_S Y)` through the canonical identifications of
`Stacks.Chow.exteriorProductCap` and `Stacks.Chow.capExteriorProduct`.

This is `Stacks.Chow.CommutesExteriorProductCap` with the quantifier over `α` removed, the two
sides being literally the same. The quantified predicate cannot be instantiated at a particular
`α`, so this is the form in which the equation can be asserted for the classes it is known
for. -/
def CommutesExteriorProductCapAt (c : BivariantClass C G sY sZ u hu p) (n m : ℤ)
    (α : chowGroup C sX n) : Prop :=
  ∀ β : chowGroup C sZ m,
    exteriorProductCap C hδ G sX sY sZ u hu p c n m α β =
      capExteriorProduct C hδ G sX sY sZ u hu p c n m α β

/-- The predicate of Stacks 0FBY is its single-class form quantified over `α`, by definition. -/
theorem commutesExteriorProductCap_iff_forall (c : BivariantClass C G sY sZ u hu p) (n m : ℤ) :
    CommutesExteriorProductCap C hδ G sX sY sZ u hu p c n m ↔
      ∀ α : chowGroup C sX n, CommutesExteriorProductCapAt C hδ G sX sY sZ u hu p c n m α :=
  Iff.rfl

end Statement

/-! ### The comparison morphisms -/

section Morphisms

variable {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (sZ : Z ⟶ S) (u : Y ⟶ Z)

/-- The identification `Y ×_Z ((X ×_S Z) ×_Z Z) ≅ X ×_S Y`. The scheme on the left is where the
iterated cap product of Stacks 0FA2, taken at the test scheme `𝟙 Z` and in the order that caps
with the class of `X` first, lands; the scheme on the right is where the equation of Stacks 0FBY
is read.

It is the base change along `u` of the collapse `(X ×_S Z) ×_Z Z ≅ X ×_S Z`, followed by
`Stacks.Chow.exteriorCapIso`. -/
def iteratedExteriorCapIso :
    (pullback u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) : Scheme.{u}) ⟶
      (pullback sX (u ≫ sZ) : Scheme.{u}) :=
  (pullbackBaseChangeOfTestIso u (pullbackIdIso (pullback.snd sX sZ)).inv
      (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ))).hom ≫
    (exteriorCapIso sX sZ u rfl).hom

/-- The identification of `Y ×_Z ((X ×_S Z) ×_Z Z)` with `X ×_S Y` is the composite it is defined
to be. This is the form in which the two factors are rewritten separately. -/
theorem iteratedExteriorCapIso_eq : iteratedExteriorCapIso sX sZ u =
    (pullbackBaseChangeOfTestIso u (pullbackIdIso (pullback.snd sX sZ)).inv
        (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ))).hom ≫
      (exteriorCapIso sX sZ u rfl).hom :=
  rfl

/-- The identification of `Y ×_Z ((X ×_S Z) ×_Z Z)` with `X ×_S Y` is an isomorphism. -/
instance : IsIso (iteratedExteriorCapIso sX sZ u) := by
  rw [iteratedExteriorCapIso]; infer_instance

/-- The identification of `Y ×_Z ((X ×_S Z) ×_Z Z)` with `X ×_S Y` is a morphism over `S`, which
is what `Stacks.Chow.chowPushforwardOfIso` needs in order to transport Chow classes along it. -/
theorem iteratedExteriorCapIso_comp_structureMorphism :
    iteratedExteriorCapIso sX sZ u ≫ (pullback.fst sX (u ≫ sZ) ≫ sX) =
      pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫
        (u ≫ sZ) := by
  rw [iteratedExteriorCapIso, Category.assoc,
    exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl,
    pullbackBaseChangeOfTestIso_hom_comp]

/-- **The one geometric input of the transport.** The two routes from
`(X ×_S Z) ×_Z (Y ×_Z Z)` to `X ×_S Y` agree: exchanging the two factors by
`Stacks.Chow.commuteComparisonHom` and then collapsing `(X ×_S Z) ×_Z Z` is the same as
collapsing `Y ×_Z Z` first and then identifying `(X ×_S Z) ×_Z Y` with `X ×_S Y`.

Both sides send a point of `(X ×_S Z) ×_Z (Y ×_Z Z)` to its point of `X` and its point of `Y`,
so the identity is settled by the two projections of `X ×_S Y`. -/
theorem commuteComparisonHom_comp_iteratedExteriorCapIso :
    commuteComparisonHom (pullback.snd sX sZ) u (𝟙 Z) ≫ iteratedExteriorCapIso sX sZ u =
      (pullbackBaseChangeOfTestIso (pullback.snd sX sZ) (pullbackIdIso u).inv
          (pullbackIdIso_inv_comp u u)).hom ≫
        (pullbackLeftPullbackSndIso sX sZ u).hom := by
  refine pullback.hom_ext ?_ ?_
  · simp only [iteratedExteriorCapIso, Category.assoc, exteriorCapIso_hom_fst,
      pullbackLeftPullbackSndIso_hom_fst, pullbackBaseChangeOfTestIso_hom_snd_assoc,
      pullbackBaseChangeOfTestIso_hom_fst_assoc, pullbackIdIso_inv_eq_fst,
      commuteComparisonHom_snd_fst_assoc]
  · simp only [iteratedExteriorCapIso, Category.assoc, exteriorCapIso_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd, pullbackBaseChangeOfTestIso_hom_fst,
      pullbackBaseChangeOfTestIso_hom_snd, commuteComparisonHom_fst, pullbackIdIso_inv_eq_fst]

/-- The identification `(X ×_S Z) ×_Z Y ≅ X ×_S Y` is a morphism over `S`: it carries the
structure morphism of `X ×_S Y` to the one of `(X ×_S Z) ×_Z Y` read through the projection to
`X ×_S Z`. -/
theorem pullbackLeftPullbackSndIso_hom_comp_structureMorphism :
    (pullbackLeftPullbackSndIso sX sZ u).hom ≫ (pullback.fst sX (u ≫ sZ) ≫ sX) =
      pullback.fst (pullback.snd sX sZ) u ≫ (pullback.snd sX sZ ≫ sZ) := by
  rw [← Category.assoc, pullbackLeftPullbackSndIso_hom_fst, Category.assoc, pullback.condition]

end Morphisms

/-! ### Transport bookkeeping -/

/-- Pushing forward along an isomorphism over the base absorbs a transport of its source along an
equality of structure morphisms. -/
theorem chowPushforwardOfIso_chowGroupCongr_source (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (hA : sA = sA') (v : A ⟶ B) [IsIso v] (hv : v ≫ sB = sA)
    (hv' : v ≫ sB = sA') (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA' sB v hv' k (chowGroupCongr C hA k x) =
      chowPushforwardOfIso C sA sB v hv k x := by
  subst hA
  rfl

/-! ### The two iterated cap products, transported to `X ×_S Y` -/

/-- Capping a class pushed forward along `(Y ×_Z Z ≅ Y)⁻¹` is the pushforward of the cap at the
test scheme `Y ×_Z Z`, by the isomorphism case of condition (1) of Stacks 0B76. -/
private theorem cap_chowPushforwardOfIso_pullbackIdIso_inv (C : ChowSituation.{u})
    (G : GysinSystem C) {V W Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (v : V ⟶ Z)
    (w : W ⟶ Z) [LocallyOfFiniteType v] [LocallyOfFiniteType w] (q k : ℤ)
    (c : BivariantClass C G (v ≫ sZ) sZ v rfl q)
    (x : chowGroup C (pullback.fst w (𝟙 Z) ≫ (w ≫ sZ)) k) :
    c.cap w k (chowPushforwardOfIso C (pullback.fst w (𝟙 Z) ≫ (w ≫ sZ)) (w ≫ sZ)
        (pullbackIdIso w).inv (pullbackIdIso_inv_comp w (w ≫ sZ)) k x) =
      chowPushforwardOfIso C (pullback.fst v (pullback.fst w (𝟙 Z) ≫ w) ≫ (v ≫ sZ))
        (pullback.fst v w ≫ (v ≫ sZ))
        (pullbackBaseChangeOfTestIso v (pullbackIdIso w).inv (pullbackIdIso_inv_comp w w)).hom
        (pullbackBaseChangeOfTestIso_hom_comp v (pullbackIdIso w).inv
          (pullbackIdIso_inv_comp w w) (v ≫ sZ)) (k - q)
        (c.cap (pullback.fst w (𝟙 Z) ≫ w) k
          (chowGroupCongr C (Category.assoc (pullback.fst w (𝟙 Z)) w sZ).symm k x)) := by
  rw [← chowPushforwardOfIso_chowGroupCongr_source C (w ≫ sZ)
    (Category.assoc (pullback.fst w (𝟙 Z)) w sZ).symm (pullbackIdIso w).inv
    (pullbackIdIso_inv_comp w (w ≫ sZ)) (by rw [pullbackIdIso_inv_comp, Category.assoc]) k x]
  exact BivariantClass.cap_chowPushforwardOfTestIso C G (v ≫ sZ) sZ v rfl q c w
    (pullbackIdIso w).inv (pullbackIdIso_inv_comp w w) k _

section Transport

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z)
  [LocallyOfFiniteType u] (p r m : ℤ)
  (e : BivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl r)
  (c : BivariantClass C G (u ≫ sZ) sZ u rfl p) (β : chowGroup C sZ m)

/-- The iterated cap product `e ∩ (c ∩ β)` at the test scheme `𝟙 Z`, pushed forward to
`X ×_S Y` as `Stacks.Chow.BivariantCommute` presents it, is the cap product of `e` against
`c ∩ β ∈ CH_{m-p}(Y)` itself, pushed forward along `(X ×_S Z) ×_Z Y ≅ X ×_S Y`.

The content is the isomorphism case of condition (1) of Stacks 0B76 for the collapse
`Y ×_Z Z ≅ Y`, which is exactly the collapse `Stacks.Chow.BivariantClass.capTarget` performs,
together with `Stacks.Chow.commuteComparisonHom_comp_iteratedExteriorCapIso`. Nothing is assumed
of `e` or of `c`. -/
theorem iteratedExteriorCapIso_bivariantIteratedCap_fst :
    chowPushforwardOfIso C
        (pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫
          (u ≫ sZ))
        (pullback.fst sX (u ≫ sZ) ≫ sX) (iteratedExteriorCapIso sX sZ u)
        (iteratedExteriorCapIso_comp_structureMorphism sX sZ u) ((m - p) - r)
        (chowPushforwardOfIso C
          (pullback.fst (pullback.snd sX sZ) (pullback.fst u (𝟙 Z) ≫ u) ≫
            (pullback.snd sX sZ ≫ sZ))
          (pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫
            (u ≫ sZ))
          (commuteComparisonHom (pullback.snd sX sZ) u (𝟙 Z))
          (commuteComparisonHom_comp_structureMorphism C sZ (pullback.snd sX sZ) u (𝟙 Z))
          ((m - p) - r)
          (bivariantIteratedCap C G sZ (pullback.snd sX sZ) u r p e c (𝟙 Z) m
            (chowGroupCongr C (Category.id_comp sZ).symm m β))) =
      chowPushforwardOfIso C (pullback.fst (pullback.snd sX sZ) u ≫ (pullback.snd sX sZ ≫ sZ))
        (pullback.fst sX (u ≫ sZ) ≫ sX) (pullbackLeftPullbackSndIso sX sZ u).hom
        (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ u) ((m - p) - r)
        (e.cap u (m - p) (c.capTarget C G (u ≫ sZ) sZ u rfl p m β)) := by
  have htest := cap_chowPushforwardOfIso_pullbackIdIso_inv C G sZ (pullback.snd sX sZ) u r
    (m - p) e (c.cap (𝟙 Z) m (chowGroupCongr C (Category.id_comp sZ).symm m β))
  rw [← BivariantClass.capTarget] at htest
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_congr_apply C _ _
      (commuteComparisonHom (pullback.snd sX sZ) u (𝟙 Z) ≫ iteratedExteriorCapIso sX sZ u)
      ((pullbackBaseChangeOfTestIso (pullback.snd sX sZ) (pullbackIdIso u).inv
          (pullbackIdIso_inv_comp u u)).hom ≫ (pullbackLeftPullbackSndIso sX sZ u).hom)
      (commuteComparisonHom_comp_iteratedExteriorCapIso sX sZ u) _ _ ((m - p) - r),
    ← chowPushforwardOfIso_comp_apply C
      (pullback.fst (pullback.snd sX sZ) (pullback.fst u (𝟙 Z) ≫ u) ≫
        (pullback.snd sX sZ ≫ sZ))
      (pullback.fst (pullback.snd sX sZ) u ≫ (pullback.snd sX sZ ≫ sZ))
      (pullback.fst sX (u ≫ sZ) ≫ sX)
      (pullbackBaseChangeOfTestIso (pullback.snd sX sZ) (pullbackIdIso u).inv
        (pullbackIdIso_inv_comp u u)).hom (pullbackLeftPullbackSndIso sX sZ u).hom
      (pullbackBaseChangeOfTestIso_hom_comp (pullback.snd sX sZ) (pullbackIdIso u).inv
        (pullbackIdIso_inv_comp u u) (pullback.snd sX sZ ≫ sZ))
      (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ u) ((m - p) - r),
    htest, bivariantIteratedCap_apply]
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_comp_structureMorphism,
    pullbackBaseChangeOfTestIso_hom_comp]

/-- The iterated cap product `c ∩ (e ∩ β)` at the test scheme `𝟙 Z`, pushed forward to
`X ×_S Y` as `Stacks.Chow.BivariantCommute` presents it, is the cap product of `c` against the
class `e ∩ β` collapsed onto `X ×_S Z`, pushed forward along `Stacks.Chow.exteriorCapIso`.

Again the content is the isomorphism case of condition (1) of Stacks 0B76, this time for the
collapse `(X ×_S Z) ×_Z Z ≅ X ×_S Z`, and nothing is assumed of `e` or of `c`. The two sides are
produced in the degrees `(m - p) - r` and `(m - r) - p`, which are one integer written two ways,
whence the heterogeneous equality. -/
theorem iteratedExteriorCapIso_bivariantIteratedCap_snd :
    chowPushforwardOfIso C
        (pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫
          (u ≫ sZ))
        (pullback.fst sX (u ≫ sZ) ≫ sX) (iteratedExteriorCapIso sX sZ u)
        (iteratedExteriorCapIso_comp_structureMorphism sX sZ u) ((m - p) - r)
        (chowGroupDegreeEquiv C
          (pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫
            (u ≫ sZ)) (by ring : (m - r) - p = (m - p) - r)
          (bivariantIteratedCap C G sZ u (pullback.snd sX sZ) p r c e (𝟙 Z) m
            (chowGroupCongr C (Category.id_comp sZ).symm m β))) ≍
      chowPushforwardOfIso C (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ))
        (pullback.fst sX (u ≫ sZ) ≫ sX) (exteriorCapIso sX sZ u rfl).hom
        (exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl) ((m - r) - p)
        (c.cap (pullback.snd sX sZ) (m - r)
          (chowPushforwardOfIso C
            (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ))
            (pullback.snd sX sZ ≫ sZ) (pullbackIdIso (pullback.snd sX sZ)).inv
            (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ ≫ sZ)) (m - r)
            (e.cap (𝟙 Z) m (chowGroupCongr C (Category.id_comp sZ).symm m β)))) := by
  have htest := cap_chowPushforwardOfIso_pullbackIdIso_inv C G sZ u (pullback.snd sX sZ) p
    (m - r) c (e.cap (𝟙 Z) m (chowGroupCongr C (Category.id_comp sZ).symm m β))
  rw [← chowGroupDegreeEquiv_chowPushforwardOfIso]
  refine HEq.trans (chowGroupDegreeEquiv_heq C (pullback.fst sX (u ≫ sZ) ≫ sX)
    (by ring : (m - r) - p = (m - p) - r) _) ?_
  rw [chowPushforwardOfIso_congr_apply C _ _ (iteratedExteriorCapIso sX sZ u) _
      (iteratedExteriorCapIso_eq sX sZ u) _ _ ((m - r) - p),
    ← chowPushforwardOfIso_comp_apply C
      (pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫
        (u ≫ sZ))
      (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (pullback.fst sX (u ≫ sZ) ≫ sX)
      (pullbackBaseChangeOfTestIso u (pullbackIdIso (pullback.snd sX sZ)).inv
        (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ))).hom
      (exteriorCapIso sX sZ u rfl).hom
      (pullbackBaseChangeOfTestIso_hom_comp u (pullbackIdIso (pullback.snd sX sZ)).inv
        (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ)) (u ≫ sZ))
      (exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl) ((m - r) - p),
    bivariantIteratedCap_apply, ← htest]
  rw [Category.assoc, exteriorCapIso_hom_comp_structureMorphism,
    pullbackBaseChangeOfTestIso_hom_comp]

end Transport

/-! ### Stacks 0FBY for a fundamental class -/

section Main

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX]
  [IsIntegral X] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z) [LocallyOfFiniteType u]
  (p : ℤ) (d : ℕ) (hfp : FlatPullbackDescends C) (m : ℤ)

/-- **Clause (1) of Stacks 0B0R for the base change of `X` to `Z`.** Let the base be the spectrum
of a field, let `X` be integral and flat over it of relative dimension `d`, and let
`pr_Z : X ×_S Z ⟶ Z` be the base change of the structure morphism of `X` along `sZ`. The
flat-pullback class of **Stacks 0B78** for `pr_Z`, an element of `A^{-d}(X ×_S Z ⟶ Z)`, caps at a
test scheme `g : T ⟶ Z` as the exterior product with the fundamental class `[X]`:

  `c ∩ γ = [X] × γ`   in   `CH_{d+k}(X ×_S T)`,

the class on the left living a priori on `(X ×_S Z) ×_Z T` and being read on `X ×_S T` through
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`.

The cap operation is a flat pullback along the base change `(X ×_S Z) ×_Z T ⟶ T` of `pr_Z`, by
`Stacks.Chow.flatPullbackBivariantClass_cap`; that morphism is the base change `X ×_S T ⟶ T` of
the structure morphism of `X` read on another presentation of the same fibre product, so the two
flat pullbacks agree by the isomorphism case of Stacks 02RG,
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`; and the latter flat pullback is the exterior
product with `[X]` by
`Stacks.Chow.chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct`. -/
theorem flatPullbackBivariantClassSnd_cap_heq_chowExteriorProduct {T : Scheme.{u}} (g : T ⟶ Z)
    [LocallyOfFiniteType g] (k : ℤ) (γ : chowGroup C (g ≫ sZ) k)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    (hRG : ProperPushforwardFlatPullbackBaseChange C) (h71 : G.FlatPullbackNaturality d) :
    chowPushforwardOfIso C (pullback.fst (pullback.snd sX sZ) g ≫ (pullback.snd sX sZ ≫ sZ))
        (pullback.fst sX (g ≫ sZ) ≫ sX) (pullbackLeftPullbackSndIso sX sZ g).hom
        (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ g) (k - -(d : ℤ))
        ((flatPullbackBivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
          (relativeDimension_pullbackSnd sX hfr sZ) hfp hRG h71).cap g k γ) ≍
      chowExteriorProduct C hδ sX (g ≫ sZ) (d : ℤ) k
        (TensorProduct.tmul ℤ (fundamentalChowClass C sX (d : ℤ)) γ) := by
  have hrelZ : AlgebraicGeometry.RelativeDimension (pullback.snd sX sZ) d :=
    relativeDimension_pullbackSnd sX hfr sZ
  have hcap := flatPullbackBivariantClass_cap C G (pullback.snd sX sZ ≫ sZ) sZ
    (pullback.snd sX sZ) rfl d hrelZ hfp hRG h71 g k γ
  have hsq : pullback.snd (pullback.snd sX sZ) g ≫ 𝟙 T =
      (pullbackLeftPullbackSndIso sX sZ g).hom ≫ pullback.snd sX (g ≫ sZ) := by
    simp
  have hiso := flatPullbackChow_chowPushforwardOfIso C (g ≫ sZ)
    (pullback.fst (pullback.snd sX sZ) g ≫ (pullback.snd sX sZ ≫ sZ)) (g ≫ sZ)
    (pullback.fst sX (g ≫ sZ) ≫ sX) (𝟙 T) (Category.id_comp (g ≫ sZ))
    (pullbackLeftPullbackSndIso sX sZ g).hom
    (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ g)
    (pullback.snd (pullback.snd sX sZ) g) (pullbackSnd_comp_structureMorphism rfl g)
    (pullback.snd sX (g ≫ sZ)) pullback.condition.symm hsq d
    (relativeDimension_pullbackSnd (pullback.snd sX sZ) hrelZ g)
    (relativeDimension_pullbackSnd sX hfr (g ≫ sZ)) k (hfp _ _ _ _ d _ k) (hfp _ _ _ _ d _ k) γ
  rw [chowPushforwardOfIso_id] at hiso
  have hprod := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct C hδ sX (g ≫ sZ)
    d (relativeDimension_pullbackSnd sX hfr (g ≫ sZ)) hd k (hfp _ _ _ _ d _ k) γ
  refine HEq.trans (chowPushforwardOfIso_heq_congr C
    (pullback.fst (pullback.snd sX sZ) g ≫ (pullback.snd sX sZ ≫ sZ))
    (pullback.fst sX (g ≫ sZ) ≫ sX) (pullbackLeftPullbackSndIso sX sZ g).hom
    (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ g)
    (by ring : k - -(d : ℤ) = k + (d : ℤ)) _ _ hcap) ?_
  rw [← hiso, ← hprod]
  exact (chowGroupDegreeEquiv_heq C (pullback.fst sX (g ≫ sZ) ≫ sX) (add_comm k (d : ℤ)) _).symm

/-- **Clause (1) of Stacks 0B0R at the identity test scheme, collapsed.** The cap product of the
flat-pullback class of Stacks 0B78 for `pr_Z : X ×_S Z ⟶ Z` against `β ∈ CH_m(Z)` at the test
scheme `𝟙 Z`, a class on `(X ×_S Z) ×_Z Z`, is the exterior product `[X] × β` once that fibre
product is collapsed onto `X ×_S Z`.

This is the same statement as
`Stacks.Chow.flatPullbackBivariantClassSnd_cap_heq_chowExteriorProduct` for `g = 𝟙 Z`, except that
the collapse is read as the identification `(X ×_S Z) ×_Z Z ≅ X ×_S Z` rather than as
`(X ×_S Z) ×_Z Z ≅ X ×_S (Z ×_Z Z)`; the right-hand side is therefore
`Stacks.Chow.exteriorProductOnTarget`, the exterior product presented on the structure morphism of
`X ×_S Z` that makes it a test scheme over `Z`, which is the presentation
`Stacks.Chow.capExteriorProduct` consumes. -/
theorem flatPullbackBivariantClassSnd_cap_id_heq_exteriorProductOnTarget (β : chowGroup C sZ m)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    (hRG : ProperPushforwardFlatPullbackBaseChange C) (h71 : G.FlatPullbackNaturality d) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ))
        (pullback.snd sX sZ ≫ sZ) (pullbackIdIso (pullback.snd sX sZ)).inv
        (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ ≫ sZ))
        (m - -(d : ℤ))
        ((flatPullbackBivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
            (relativeDimension_pullbackSnd sX hfr sZ) hfp hRG h71).cap (𝟙 Z) m
          (chowGroupCongr C (Category.id_comp sZ).symm m β)) ≍
      exteriorProductOnTarget C hδ sX sZ (d : ℤ) m
        (fundamentalChowClass C sX (d : ℤ)) β := by
  have hrelZ : AlgebraicGeometry.RelativeDimension (pullback.snd sX sZ) d :=
    relativeDimension_pullbackSnd sX hfr sZ
  have hcap := flatPullbackBivariantClass_cap C G (pullback.snd sX sZ ≫ sZ) sZ
    (pullback.snd sX sZ) rfl d hrelZ hfp hRG h71 (𝟙 Z) m
    (chowGroupCongr C (Category.id_comp sZ).symm m β)
  have hcollapse : (pullbackIdIso (pullback.snd sX sZ)).inv ≫ (pullback.fst sX sZ ≫ sX) =
      pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ) := by
    rw [pullbackIdIso_inv_comp, pullback.condition]
  have hsq : pullback.snd (pullback.snd sX sZ) (𝟙 Z) ≫ 𝟙 Z =
      (pullbackIdIso (pullback.snd sX sZ)).inv ≫ pullback.snd sX sZ := by
    rw [pullbackIdIso_inv_comp, ← pullback.condition]
  have hiso := flatPullbackChow_chowPushforwardOfIso C (𝟙 Z ≫ sZ)
    (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ)) sZ
    (pullback.fst sX sZ ≫ sX) (𝟙 Z) rfl (pullbackIdIso (pullback.snd sX sZ)).inv hcollapse
    (pullback.snd (pullback.snd sX sZ) (𝟙 Z)) (pullbackSnd_comp_structureMorphism rfl (𝟙 Z))
    (pullback.snd sX sZ) pullback.condition.symm hsq d
    (relativeDimension_pullbackSnd (pullback.snd sX sZ) hrelZ (𝟙 Z)) hrelZ m
    (hfp _ _ _ _ d _ m) (hfp _ _ _ _ d _ m) (chowGroupCongr C (Category.id_comp sZ).symm m β)
  rw [chowPushforwardOfIso_chowGroupCongr_source C sZ (Category.id_comp sZ).symm (𝟙 Z)
      (Category.id_comp sZ) rfl m β, chowPushforwardOfIso_id] at hiso
  have hprod := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct C hδ sX sZ d
    hrelZ hd m (hfp _ _ _ _ d _ m) β
  refine HEq.trans (chowPushforwardOfIso_heq_congr C
    (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ))
    (pullback.snd sX sZ ≫ sZ) (pullbackIdIso (pullback.snd sX sZ)).inv
    (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ ≫ sZ))
    (by ring : m - -(d : ℤ) = m + (d : ℤ)) _ _ hcap) ?_
  rw [← chowGroupCongr_chowPushforwardOfIso_target C
      (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ))
      (pullback.condition (f := sX) (g := sZ)) (pullbackIdIso (pullback.snd sX sZ)).inv hcollapse
      (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ ≫ sZ)) (m + (d : ℤ)) _,
    ← hiso]
  refine HEq.trans (chowGroupCongr_heq C (pullback.condition (f := sX) (g := sZ))
    (m + (d : ℤ)) _) ?_
  refine HEq.trans (chowGroupDegreeEquiv_heq C (pullback.fst sX sZ ≫ sX)
    (add_comm m (d : ℤ)) _).symm ?_
  rw [hprod]
  exact (chowGroupCongr_heq C (pullback.condition (f := sX) (g := sZ)) ((d : ℤ) + m) _).symm

include hfp in
/-- **Stacks 0FBY for a fundamental class**, in the case in which the structure morphism of `Y` is
presented as `u ≫ sZ`.

This is the whole content; the general statement
`Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass` follows by substituting the
equality `u ≫ sZ = sY`, which is what makes `c` a class for `u` in the indices
`Stacks.Chow.BivariantCommute` consumes. -/
private theorem commutesExteriorProductCapAt_fundamentalChowClass_comp
    (c : BivariantClass C G (u ≫ sZ) sZ u rfl p) (β : chowGroup C sZ m)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    (hRG : ProperPushforwardFlatPullbackBaseChange C) (h71 : G.FlatPullbackNaturality d) :
    exteriorProductCap C hδ G sX (u ≫ sZ) sZ u rfl p c (d : ℤ) m
        (fundamentalChowClass C sX (d : ℤ)) β =
      capExteriorProduct C hδ G sX (u ≫ sZ) sZ u rfl p c (d : ℤ) m
        (fundamentalChowClass C sX (d : ℤ)) β := by
  have hrelZ : AlgebraicGeometry.RelativeDimension (pullback.snd sX sZ) d :=
    relativeDimension_pullbackSnd sX hfr sZ
  have hcomm := bivariantCommute_flatPullbackBivariantClass C G sZ (pullback.snd sX sZ) u d
    hrelZ hfp hRG h71 p c (𝟙 Z) m (chowGroupCongr C (Category.id_comp sZ).symm m β)
  have key := congrArg (chowPushforwardOfIso C
    (pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫ (u ≫ sZ))
    (pullback.fst sX (u ≫ sZ) ≫ sX) (iteratedExteriorCapIso sX sZ u)
    (iteratedExteriorCapIso_comp_structureMorphism sX sZ u) ((m - p) - -(d : ℤ))) hcomm
  have hprod := flatPullbackBivariantClassSnd_cap_heq_chowExteriorProduct C hδ G sX sZ d hfp u
    (m - p) (c.capTarget C G (u ≫ sZ) sZ u rfl p m β) hfr hd hRG h71
  have hfst := iteratedExteriorCapIso_bivariantIteratedCap_fst C G sX sZ u p (-(d : ℤ)) m
    (flatPullbackBivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
      hrelZ hfp hRG h71) c β
  have hsnd := iteratedExteriorCapIso_bivariantIteratedCap_snd C G sX sZ u p (-(d : ℤ)) m
    (flatPullbackBivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
      hrelZ hfp hRG h71) c β
  have hcollapse := BivariantClass.cap_heq_congr c (pullback.snd sX sZ)
    (by ring : m - -(d : ℤ) = (d : ℤ) + m) _ _
    (flatPullbackBivariantClassSnd_cap_id_heq_exteriorProductOnTarget C hδ G sX sZ d hfp m β hfr
      hd hRG h71)
  have hpush := chowPushforwardOfIso_heq_congr C
    (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (pullback.fst sX (u ≫ sZ) ≫ sX)
    (exteriorCapIso sX sZ u rfl).hom (exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl)
    (by ring : (m - -(d : ℤ)) - p = ((d : ℤ) + m) - p) _ _ hcollapse
  have htarget := chowPushforwardOfIso_heq_congr C
    (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (pullback.fst sX (u ≫ sZ) ≫ sX)
    (exteriorCapIso sX sZ u rfl).hom (exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl)
    (by ring : (d : ℤ) + (m - p) = ((d : ℤ) + m) - p) _ _
    (chowGroupDegreeEquiv_heq C (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ))
      (by omega : (d : ℤ) + m - p = (d : ℤ) + (m - p))
      (c.cap (pullback.snd sX sZ) ((d : ℤ) + m)
        (exteriorProductOnTarget C hδ sX sZ (d : ℤ) m
          (fundamentalChowClass C sX (d : ℤ)) β)))
  exact eq_of_heq (hprod.symm.trans ((heq_of_eq (hfst.symm.trans key)).trans
    (hsnd.trans (hpush.trans htarget.symm))))

end Main

section Statement

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX]
  [IsIntegral X] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ) (d : ℕ)
  (hfp : FlatPullbackDescends C) (m : ℤ)

include hfp in
/-- **Stacks 0FBY for the fundamental class of an integral scheme flat over the base.** Let the
base be the spectrum of a field, let `X` be integral and flat over it of relative dimension `d`,
let `u : Y ⟶ Z` be a morphism of schemes locally of finite type over the base and let
`c ∈ A^p(Y ⟶ Z)` be a bivariant class. Then for every `β ∈ CH_m(Z)`

  `[X] × (c ∩ β) = c ∩ ([X] × β)`

in `CH_{d + (m - p)}(X ×_S Y)`, where `[X] ∈ CH_d(X)` is the fundamental class of `X` and the two
sides are read through the canonical identifications of `Stacks.Chow.exteriorProductCap` and
`Stacks.Chow.capExteriorProduct`.

The first variable is a fundamental class and not a general `α ∈ CH_n(X)`; see the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting` for what the general
case needs and for why it is unavailable here.

The proof replaces `[X] × -` by the cap operation of the flat-pullback class of Stacks 0B78 for
the structure morphism of `X`, whose base change to `Z` is the flat-pullback class for
`pr_Z : X ×_S Z ⟶ Z`, and that class commutes with `c` by the smooth half of Stacks 0FF6. The
commuting identity is then instantiated at the test scheme `𝟙 Z` and both of its sides are
transported to `X ×_S Y`. -/
@[stacks 0FBY "the equation α × (c ∩ β) = c ∩ (α × β) of the tag, for α the fundamental class \
of an integral scheme X flat of relative dimension d over the base — NOT for a general α ∈ \
CH_n(X), for which the missing inputs are recorded in the module notes; carries Stacks 02S1 as \
hfp, Stacks 02RG on Chow groups as hRG, and Stacks 0B71 with the identification of Stacks 0B6Y \
as h71, these being exactly the hypotheses of Stacks 0B78 in this repository"]
theorem commutesExteriorProductCapAt_fundamentalChowClass
    (c : BivariantClass C G sY sZ u hu p)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    (hRG : ProperPushforwardFlatPullbackBaseChange C) (h71 : G.FlatPullbackNaturality d) :
    CommutesExteriorProductCapAt C hδ G sX sY sZ u hu p c (d : ℤ) m
      (fundamentalChowClass C sX (d : ℤ)) := by
  subst hu
  intro β
  exact commutesExteriorProductCapAt_fundamentalChowClass_comp C hδ G sX sZ u p d hfp m c β hfr
    hd hRG h71

end Statement

end Stacks.Chow

end
