module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Bivariant Chow classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`. A *bivariant class of degree `p` for `f`*
assigns to every morphism `g : T ⟶ Y` locally of finite type and every `k` an additive map

  `c ∩ - : A_k(T) ⟶ A_{k - p}(T ×_Y X)`,

compatibly with the three operations chapter 42 puts on Chow groups: proper pushforward
(Stacks 0GU8), flat pullback of fixed relative dimension (Stacks 0FVK), and the Gysin map of the
zero scheme of a section of an invertible module (Stacks 02TO). The group of all of them is
`A^p(X ⟶ Y)`, and that group is `Stacks.Chow.BivariantClass`, an abelian group under the
pointwise operations.

## Main definitions

* `Stacks.Chow.GysinSystem` — a choice, for every scheme locally of finite type over the base and
  every invertible module on it, of the contained-component first Chern class rule of Stacks 02SO
  together with the vanishing of Stacks 02TO. This is what the Gysin compatibility of a bivariant
  class must be stated against; see the implementation notes.
* `Stacks.Chow.GysinSystem.onChow` — the Gysin map on Chow groups such a system provides.
* `Stacks.Chow.bivariantBaseChangeMap` — the map `T' ×_Y X ⟶ T ×_Y X` induced by `T' ⟶ T`.
* `Stacks.Chow.BivariantClass` — **Stacks 0B76**, the group `A^p(X ⟶ Y)` of bivariant classes of
  degree `p` for `f`.

## Main results

* `Stacks.Chow.BivariantClass.ext` — a bivariant class is determined by its cap operations.
* `Stacks.Chow.BivariantClass.zero_cap`, `add_cap`, `neg_cap`, `sub_cap`, `nsmul_cap`,
  `zsmul_cap` — the abelian group structure is the pointwise one.

## Implementation notes

### Modelling

The base change of `f : X ⟶ Y` along `g : T ⟶ Y` is the chosen categorical pullback
`pullback f g`, with `pullback.fst f g` its map to `X`; a cap operation therefore lands in
`chowGroup C (pullback.fst f g ≫ sX) (k - p)`. The compatibility axioms are stated for an
arbitrary morphism `h'` between two such pullbacks making the indicated square cartesian and
commuting with the maps to `X`, so they apply in particular to the canonical base-change map
`Stacks.Chow.bivariantBaseChangeMap`. In the Gysin axiom the identification of the base change of
the zero scheme `D ⊆ T` with the zero scheme `E` of the pulled-back section is recorded by an
isomorphism `e` over the ambient pullback, and the induced map on Chow groups is proper
pushforward along `e.hom`.

The flat axiom is an `HEq` because the flat pullback of a `k`-cycle has degree `k + r` while the
cap operation of degree `p` produces degree `(k + r) - p` on one side and `(k - p) + r` on the
other; these are the same integer and not the same term.

### The parameters threaded, and why

Each of the three operations a bivariant class must commute with is defined on Chow groups only
once the corresponding operation on cycles is known to preserve rational equivalence. The axioms
of `Stacks.Chow.BivariantClass` supply that from the theorems which prove it:

* Proper pushforward on Chow groups, `Stacks.Chow.properChowPushforward`, is taken with
  `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`, Stacks 02S2 for an
  arbitrary proper morphism over the base.
* Flat pullback on Chow groups, `Stacks.Chow.flatPullbackChow`, is taken with
  `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, Stacks 02S1, and the
  relative dimension of the base-changed morphism is
  `AlgebraicGeometry.RelativeDimension.of_isPullback`, Stacks 02NK.
* The Gysin map on Chow groups, `Stacks.Chow.gysinHomomorphismOnChow`, takes **data**: a
  `Stacks.Chow.FirstChernComponentClassRule`, the rule of Stacks 02SO. Data is the case where
  quantifying is *not* harmless, and the reason is the opposite of the one for a `Prop`:

  > For a `Prop` hypothesis, `(∀ h, P h) ↔ P h₀` by proof irrelevance, so quantifying is free.
  > For **data**, `∀ G, P G` is strictly **stronger** than `P G₀` — a `∀ G` class would have to
  > commute with every candidate component rule, including non-geometric ones, so it is a possibly
  > proper subgroup of `A^p(X ⟶ Y)`. Over-strengthening is as unfaithful to Stacks 0B76 as
  > weakening is. Parameterizing is the only shape in which
  > `Stacks.Chow.BivariantClass C G₀ sX sY f hf p` is *literally* `A^p(X ⟶ Y)` once the genuine
  > `G₀` exists. Hence: **data ⇒ parameter, `Prop` ⇒ quantify.**

  Quantifying *one* `GysinSystem` inside the field would not make the structure uninhabitable:
  it gives a coherent pair of Gysin maps at both sites, and the zero class satisfies the
  Gysin axiom using no property of `G` at all. The objection is over-strengthening, stated above.

  So the rule is a *parameter*: `Stacks.Chow.BivariantClass` takes a `Stacks.Chow.GysinSystem`,
  which supplies a rule and the Stacks 02TO vanishing uniformly in the test scheme, the
  invertible module and the degree. It must be *global* rather than per-scheme, and Stacks 0FDZ
  is what forces that: it maps `BivariantClass C G sX sY f hf p` to a product of
  `BivariantClass C G` at the *same* `G` over *different* schemes. Note also that `factors` is a
  Pi into `Prop`, hence itself a `Prop`, so with proof irrelevance and structure eta two
  `GysinSystem`s with the same `chern` are definitionally equal: the parameter's only real content
  is the 02SO data, and bundling `factors` costs nothing. Substituting the genuine first Chern
  class and the genuine Stacks 02TO recovers Stacks 0B76 verbatim — and that substitution is
  available: `Stacks.Chow.canonicalGysinSystem` is the system of the first Chern class rule of an
  invertible module with the Stacks 02TO vanishing supplied from
  `Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence`, it is the only system carrying
  that rule, and `Stacks.Chow.CanonicalBivariantClass` is this group read against it, with nothing
  assumed.

  For the Gysin system of the first Chern class of an invertible module,
  `Stacks.Chow.gysinSystemOfInvertible`, the bivariant first Chern class of Stacks 0B77 is
  `Stacks.Chow.GenuineChern.firstChernClassBivariantClass`.

  `Stacks.Chow.gysinHomomorphism` takes its rule `chern` as a parameter in the same way, and so
  does `Stacks.Chow.ChernCapOperator`.
* That the pullback of an invertible module is invertible is Stacks 0B8L, the instance
  `Stacks.Divisors.pullback_isInvertible`; the Gysin axiom uses it for the pulled-back module.

### Why the two component compatibilities are not carried here

An arbitrary `GysinSystem` is not enough to **prove** Stacks 0B79 either, and it is
deliberately not made enough. The proper and the flat axiom of the Gysin bivariant class of 0B79
are Stacks 02TA and Stacks 0B71, and this repository has both only under an integral-component
compatibility: `Stacks.Chow.GysinCompatibleWithPushforward` and
`Stacks.Chow.GysinCompatibleWithFlatPullback`. Neither follows from `chern` and
`factors`: take `f = 𝟙 X`, `g = 𝟙 D`, `chern' = 0` and `chern W ≠ 0` for a `W` contained in
the zero scheme. So something has to supply
them, and there are three candidate places.

They are **not** further fields of `GysinSystem`. Both are `Prop`s, so bundling them would cost
nothing for inhabitation — by the proof-irrelevance argument that makes bundling `factors` free,
and the genuine first Chern class does satisfy them, that being exactly the integral-component
case of 02TA and of 0B71. The objection is scope. `GysinSystem` is a *parameter of*
`BivariantClass`, so a new field is a new hypothesis on **every** consumer of `BivariantClass`,
including the ones with no use for it: the abelian group structure below, and Stacks 0B7H, whose
source proof invokes only Stacks 02U7, 02U9, 02U8 and 0B7G. Strengthening a shared parameter
weakens every downstream theorem at once, and silently.

They are **not** `∀`-quantified inside `cap_properPushforward` and `cap_flatPullbackChow`
either. Those fields are the axioms of Stacks 0B76, and a hypothesis added to an axiom *enlarges*
the group, so `BivariantClass` would cease to be `A^p(X ⟶ Y)`.

So they belong to the declarations that need them:
`Stacks.Chow.gysinHomomorphism_properPushforward` and
`Stacks.Chow.gysinHomomorphism_flatPullback` carry them as hypotheses, and the construction of
Stacks 0B79 discharges them for the first Chern class rule. Neither `GysinSystem` nor
`BivariantClass` changes. Read that way, the rule above says to quantify a `Prop` at the use
site, not to move it into the definition of the group.

The Gysin bivariant class of Stacks 0B79 is constructed downstream, as
`Stacks.Chow.gysinBivariantClass`, at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of
the first Chern class rule. There the two component compatibilities hold outright, and the
Gysin axiom is the commutation of two Gysin maps, proved from the key formula of Stacks 0AYC.

### Where `@[stacks 0B76]` sits

The covering set of Stacks 0B76 is the definition of `A^p(X ⟶ Y)` together with its abelian group
structure, and all of it is here: `Stacks.Chow.BivariantClass`, its extensionality lemma, and the
six lemmas recording that the group operations are the pointwise ones. Each of those carries
`@[stacks 0B76]` with a sub-label.

Every one of them carries the `Stacks.Chow.GysinSystem` parameter discussed above, and the
sub-labels say so. That parameter is not a weakening: as argued above, substituting the genuine
first Chern class and the genuine Stacks 02TO recovers Stacks 0B76 verbatim, and `GysinSystem` is
*data*, so parameterizing — rather than quantifying — is the only shape in which
`Stacks.Chow.BivariantClass C G₀ sX sY f hf p` is literally `A^p(X ⟶ Y)`.

The genuine `G₀` is `Stacks.Chow.canonicalGysinSystem`, and
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical` builds it and reads this group against
it as `Stacks.Chow.CanonicalBivariantClass`, with the Stacks 02S1 and 02S2 binders of the two
axioms discharged. That declaration carries `@[stacks 0B76]` for the unrestricted form; the
sub-labels here name the parameters the declarations in this file carry.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The Gysin operation a bivariant class is stated against -/

/-- **Stacks 02SO and 02TO, as a single datum.** For every scheme locally of finite type over the
base, every invertible module on it and every degree, the contained-component first Chern class
rule of Stacks 02SO, together with the vanishing of Stacks 02TO that lets the resulting Gysin map
descend from cycles to Chow groups.

This is what invertible modules provide by Stacks 02SO and Stacks 02TO; the resulting system is
`Stacks.Chow.gysinSystemOfInvertible`. Bundling the two is what makes the Gysin axiom of
`Stacks.Chow.BivariantClass` statable: that axiom compares the Gysin map on a test scheme with the
Gysin map on its base change, so a rule for one scheme and one degree is not enough. See the
module docstring. -/
structure GysinSystem (C : ChowSituation.{u}) where
  /-- The contained-component rule of Stacks 02SO, for every base, invertible module and
  degree. -/
  chern : ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L] (k : ℤ),
    FirstChernComponentClassRule C q k
  /-- The Gysin map built from that rule kills rational equivalences: Stacks 02TO. -/
  factors : ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ),
    GysinFactorsThroughRationalEquivalence C q k L s (chern q L k)

/-- **Stacks 02TO.** The Gysin map on Chow groups, `i^* : A_{k+1}(T) ⟶ A_k(Z(s))`, that a Gysin
system provides for the zero scheme of a section `s` of an invertible module on `T`. -/
def GysinSystem.onChow {C : ChowSituation.{u}} (G : GysinSystem C) {T : Scheme.{u}}
    (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) :
    chowGroup C q (k + 1) →+
      chowGroup C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) k :=
  gysinHomomorphismOnChow C q k L s (G.chern q L k) (G.factors q L s k)

/-- On the class of a cycle, the Gysin map of a Gysin system is the Gysin map on cycles. -/
@[simp]
theorem GysinSystem.onChow_mk {C : ChowSituation.{u}} (G : GysinSystem C) {T : Scheme.{u}}
    (q : T ⟶ C.S) [LocallyOfFiniteType q] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (α : CycleGroup C q (k + 1)) :
    G.onChow q L s k (QuotientAddGroup.mk' (rationalEquivalences C q (k + 1)) α) =
      gysinHomomorphism C q k L s (G.chern q L k) α :=
  rfl

/-! ### Base change of the chosen pullback -/

/-- The map `T' ×_Y X ⟶ T ×_Y X` between two base changes of `f : X ⟶ Y` induced by a morphism
`h : T' ⟶ T` of their bases. -/
abbrev bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (h : T' ⟶ T) :
    pullback f (h ≫ g) ⟶ pullback f g :=
  pullback.map f (h ≫ g) f g (𝟙 X) h (𝟙 Y) (by simp) (by simp)

/-! ### Bivariant classes -/

/-- **Stacks 0B76.** A bivariant class of degree `p` for `f : X ⟶ Y`: a rule assigning to every
morphism `g : T ⟶ Y` locally of finite type and every `k` an additive map
`A_k(T) ⟶ A_{k-p}(T ×_Y X)`, natural for proper pushforward, for flat pullback of fixed relative
dimension, and for the Gysin map of the zero scheme of a section of an invertible module. The
group of all of them is denoted `A^p(X ⟶ Y)`.

Stated against a `Stacks.Chow.GysinSystem`, which supplies the first Chern class rule of Stacks
02SO and the vanishing of Stacks 02TO; see the module docstring. -/
@[stacks 0B76 "the group A^p(X ⟶ Y) of bivariant classes of degree p for f, stated \
against a GysinSystem supplying the first Chern class rule of Stacks 02SO and the \
vanishing of Stacks 02TO"]
structure BivariantClass (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) where
  /-- The cap operation on the Chow group of each test scheme. -/
  cap : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst f g ≫ sX) (k - p)
  /-- Cap product commutes with proper pushforward: Stacks 0B76 (1). Pushforward on Chow groups
  is taken with the descent of Stacks 02S2 that holds for every proper morphism. -/
  cap_properPushforward : ∀ {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T)
      [IsProper h] (h' : pullback f (h ≫ g) ⟶ pullback f g)
      (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
      (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ),
      letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
      ∀ (α : chowGroup C ((h ≫ g) ≫ sY) k),
        cap g k (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h
            (by simp [Category.assoc]) k
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C ((h ≫ g) ≫ sY)
              (g ≫ sY) h (by simp [Category.assoc]) k) α) =
          properChowPushforward C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
            (by rw [← Category.assoc, hfst]) (k - p)
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
              (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
              (by rw [← Category.assoc, hfst]) (k - p)) (cap (h ≫ g) k α)
  /-- Cap product commutes with flat pullback of fixed relative dimension: Stacks 0B76 (2). Flat
  pullback on Chow groups is taken with the descent of Stacks 02S1, and the relative dimension of
  the base change is that of Stacks 02NK. -/
  cap_flatPullbackChow : ∀ {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (h : T' ⟶ T)
      [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
      (h' : pullback f (h ≫ g) ⟶ pullback f g)
      (sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
      (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g)) (k : ℤ),
      letI : LocallyOfFiniteType h' :=
        MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
      letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
      ∀ (α : chowGroup C (g ≫ sY) k),
        HEq
          (cap (h ≫ g) (k + (r : ℤ))
            (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r hr k
              (flatPullbackFactorsThroughRationalEquivalence_general C ((h ≫ g) ≫ sY) (g ≫ sY) h
                (by simp [Category.assoc]) r hr k) α))
          (flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
            (by rw [← Category.assoc, hfst]) r
            (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (k - p)
            (flatPullbackFactorsThroughRationalEquivalence_general C
              (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX) h'
              (by rw [← Category.assoc, hfst]) r
              (AlgebraicGeometry.RelativeDimension.of_isPullback sq hr) (k - p))
            (cap g k α))
  /-- Cap product commutes with the Gysin map of every pulled-back divisor: Stacks 0B76 (3). The
  identification `e` of the base change of the divisor with the zero scheme of the pulled-back
  section (Stacks 0B6Y) is an isomorphism, and pushforward along it is proper pushforward
  `Stacks.Chow.properChowPushforward` along `e.hom`. -/
  cap_gysin : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
      (s : Γ(L, ⊤)) (k : ℤ),
      let D := Stacks.Divisors.zeroScheme T L s
      let L' := (Scheme.Modules.pullback (pullback.snd f g)).obj L
      let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s
      let E := Stacks.Divisors.zeroScheme (pullback f g) L' s'
      ∀ (e : pullback f (D.subschemeι ≫ g) ≅ E.subscheme)
        (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap f g D.subschemeι)
        (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst f g ≫ sX) =
          pullback.fst f (D.subschemeι ≫ g) ≫ sX)
        (α : chowGroup C (g ≫ sY) (k + 1)),
        properChowPushforward C (pullback.fst f (D.subschemeι ≫ g) ≫ sX)
            (E.subschemeι ≫ pullback.fst f g ≫ sX) e.hom hbase (k - p)
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
              (pullback.fst f (D.subschemeι ≫ g) ≫ sX) (E.subschemeι ≫ pullback.fst f g ≫ sX)
              e.hom hbase (k - p))
            (cap (D.subschemeι ≫ g) k (G.onChow (g ≫ sY) L s k α)) =
          G.onChow (pullback.fst f g ≫ sX) L' s' (k - p)
            (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
              (by omega : (k + 1) - p = (k - p) + 1)) (cap g (k + 1) α))

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

section Naturality

variable {C G sX sY f hf p}

/-- Condition (1) of Stacks 0B76, read with any proofs of the descent of Stacks 02S2 along the two
morphisms: proper pushforward on Chow groups does not depend on the proof. -/
theorem BivariantClass.proper_naturality (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (q : T' ⟶ T)
    [IsProper q] (q' : pullback f (q ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (q ≫ g)) q' q (pullback.snd f g))
    (fst_eq : q' ≫ pullback.fst f g = pullback.fst f (q ≫ g)) (k : ℤ) :
    letI : IsProper q' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((q ≫ g) ≫ sY) (g ≫ sY) q
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst f (q ≫ g) ≫ sX) (pullback.fst f g ≫ sX) q'
        (by rw [← Category.assoc, fst_eq]) (k - p))
      (α : chowGroup C ((q ≫ g) ≫ sY) k),
      c.cap g k (properChowPushforward C ((q ≫ g) ≫ sY) (g ≫ sY) q
          (by simp [Category.assoc]) k hfac α) =
        properChowPushforward C (pullback.fst f (q ≫ g) ≫ sX) (pullback.fst f g ≫ sX) q'
          (by rw [← Category.assoc, fst_eq]) (k - p) hfac' (c.cap (q ≫ g) k α) :=
  fun _ _ α ↦ c.cap_properPushforward g q q' sq fst_eq k α

/-- Condition (2) of Stacks 0B76, read with any proofs of the descent of Stacks 02S1 and of the
relative dimension of the base change: flat pullback on Chow groups does not depend on them. -/
theorem BivariantClass.flat_naturality (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (q : T' ⟶ T)
    [LocallyOfFiniteType q] [Flat q] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r)
    (q' : pullback f (q ≫ g) ⟶ pullback f g)
    (sq : IsPullback (pullback.snd f (q ≫ g)) q' q (pullback.snd f g))
    (fst_eq : q' ≫ pullback.fst f g = pullback.fst f (q ≫ g)) (k : ℤ) :
    letI : LocallyOfFiniteType q' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat q' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension q' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((q ≫ g) ≫ sY) (g ≫ sY) q
        (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst f (q ≫ g) ≫ sX) (pullback.fst f g ≫ sX) q'
        (by rw [← Category.assoc, fst_eq]) r hr' (k - p))
      (α : chowGroup C (g ≫ sY) k),
      HEq
        (c.cap (q ≫ g) (k + (r : ℤ))
          (flatPullbackChow C ((q ≫ g) ≫ sY) (g ≫ sY) q (by simp [Category.assoc]) r hr k
            hfac α))
        (flatPullbackChow C (pullback.fst f (q ≫ g) ≫ sX) (pullback.fst f g ≫ sX) q'
          (by rw [← Category.assoc, fst_eq]) r hr' (k - p) hfac' (c.cap g k α)) :=
  fun _ _ _ α ↦ c.cap_flatPullbackChow g q r hr q' sq fst_eq k α

/-- Condition (3) of Stacks 0B76, read with any proof of the descent of Stacks 02S2 along the
identification `e`: proper pushforward on Chow groups does not depend on the proof. -/
theorem BivariantClass.gysin_naturality (c : BivariantClass C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
      (pullback f g).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd f g)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s
    let E := Stacks.Divisors.zeroScheme (pullback f g) L' s'
    ∀ (e : pullback f (D.subschemeι ≫ g) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap f g D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst f g ≫ sX) =
        pullback.fst f (D.subschemeι ≫ g) ≫ sX)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst f (D.subschemeι ≫ g) ≫ sX) (E.subschemeι ≫ pullback.fst f g ≫ sX)
        e.hom hbase (k - p))
      (α : chowGroup C (g ≫ sY) (k + 1)),
      properChowPushforward C (pullback.fst f (D.subschemeι ≫ g) ≫ sX)
          (E.subschemeι ≫ pullback.fst f g ≫ sX) e.hom hbase (k - p) hfac
          (c.cap (D.subschemeι ≫ g) k (G.onChow (g ≫ sY) L s k α)) =
        G.onChow (pullback.fst f g ≫ sX) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
            (by omega : (k + 1) - p = (k - p) + 1)) (c.cap g (k + 1) α)) :=
  fun e he hbase _ α ↦ c.cap_gysin g L s k e he hbase α

end Naturality

/-- **Stacks 0B76.** Two bivariant classes agree as soon as all their cap operations agree. -/
@[ext, stacks 0B76 "extensionality: a bivariant class is determined by its cap operations"]
theorem BivariantClass.ext {c d : BivariantClass C G sX sY f hf p}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sY) k), c.cap g k α = d.cap g k α) : c = d := by
  cases c with
  | mk ccap cproper cflat cgysin =>
    cases d with
    | mk dcap dproper dflat dgysin =>
      have hcap : @ccap = @dcap := by
        funext T g hg k
        exact AddMonoidHom.ext fun α => h (T := T) g k α
      cases hcap
      congr

/-- **Stacks 0B76.** The zero bivariant class, capping to zero on every test scheme. -/
instance : Zero (BivariantClass C G sX sY f hf p) where
  zero :=
    { cap := fun _ _ _ => 0
      cap_properPushforward := by intros; simp
      cap_flatPullbackChow := by
        intro T T' g hg h hh fh r hr h' sq hfst k α
        dsimp
        have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
        rw [hidx]
        simp
      cap_gysin := by
        intro T g hg L hL s k
        dsimp only
        let F : ℤ → Type u := chowGroup C (pullback.fst f g ≫ sX)
        have cast_zero (i j : ℤ) (h : i = j) : Eq.mp (congrArg F h) (0 : F i) = 0 := by
          cases h
          rfl
        intro e he hbase α
        have hidx : (k + 1) - p = (k - p) + 1 := by omega
        conv_lhs => arg 2; change (0 : _)
        rw [map_zero]
        conv_rhs => arg 2; arg 2; change (0 : _)
        rw [cast_zero _ _ hidx, map_zero] }

/-- **Stacks 0B76.** The pointwise sum of two bivariant classes. -/
instance : Add (BivariantClass C G sX sY f hf p) where
  add c d :=
    { cap := fun g _ k => c.cap g k + d.cap g k
      cap_properPushforward := by
        intro T T' g hg h hh h' sq hfst k α
        simp only [AddMonoidHom.add_apply, map_add]
        exact congrArg₂ (· + ·) (c.cap_properPushforward g h h' sq hfst k α)
          (d.cap_properPushforward g h h' sq hfst k α)
      cap_flatPullbackChow := by
        intro T T' g hg h hh fh r hr h' sq hfst k α
        let F : ℤ → Type u := chowGroup C (pullback.fst f (h ≫ g) ≫ sX)
        have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
        have hc := c.cap_flatPullbackChow g h r hr h' sq hfst k α
        have hd := d.cap_flatPullbackChow g h r hr h' sq hfst k α
        have cast_add (i j : ℤ) (hij : i = j) (a b : F j) :
            cast (congrArg F hij).symm (a + b) =
              cast (congrArg F hij).symm a + cast (congrArg F hij).symm b := by
          cases hij
          rfl
        simp only [AddMonoidHom.add_apply, map_add]
        apply (eq_cast_iff_heq (e := (congrArg F hidx).symm)).1
        rw [cast_add _ _ hidx]
        exact congrArg₂ (· + ·) ((eq_cast_iff_heq (e := (congrArg F hidx).symm)).2 hc)
          ((eq_cast_iff_heq (e := (congrArg F hidx).symm)).2 hd)
      cap_gysin := by
        intro T g hg L hL s k D L' s' E e he hbase α
        let F : ℤ → Type u := chowGroup C (pullback.fst f g ≫ sX)
        have hidx : (k + 1) - p = (k - p) + 1 := by omega
        have cast_add (i j : ℤ) (hij : i = j) (a b : F i) :
            Eq.mp (congrArg F hij) (a + b) =
              Eq.mp (congrArg F hij) a + Eq.mp (congrArg F hij) b := by
          cases hij
          rfl
        have hc := c.cap_gysin g L s k e he hbase α
        have hd := d.cap_gysin g L s k e he hbase α
        let β := G.onChow (g ≫ sY) L s k α
        have happ : (c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k +
            d.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k) β =
            c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k β +
              d.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k β := rfl
        simp only [AddMonoidHom.add_apply]
        rw [cast_add _ _ hidx, happ, map_add]
        simpa only [AddMonoidHom.add_apply, Pi.add_apply, map_add] using
          congrArg₂ (· + ·) hc hd }

/-- **Stacks 0B76.** The pointwise negation of a bivariant class. -/
instance : Neg (BivariantClass C G sX sY f hf p) where
  neg c :=
    { cap := fun g _ k => -c.cap g k
      cap_properPushforward := by
        intro T T' g hg h hh h' sq hfst k α
        simpa only [AddMonoidHom.neg_apply, map_neg] using
          congrArg Neg.neg (c.cap_properPushforward g h h' sq hfst k α)
      cap_flatPullbackChow := by
        intro T T' g hg h hh fh r hr h' sq hfst k α
        let F : ℤ → Type u := chowGroup C (pullback.fst f (h ≫ g) ≫ sX)
        have hidx : (k + (r : ℤ)) - p = (k - p) + (r : ℤ) := by omega
        have hc := c.cap_flatPullbackChow g h r hr h' sq hfst k α
        have cast_neg (i j : ℤ) (hij : i = j) (a : F j) :
            cast (congrArg F hij).symm (-a) = -cast (congrArg F hij).symm a := by
          cases hij
          rfl
        simp only [AddMonoidHom.neg_apply, map_neg]
        apply (eq_cast_iff_heq (e := (congrArg F hidx).symm)).1
        rw [cast_neg _ _ hidx]
        exact congrArg Neg.neg ((eq_cast_iff_heq (e := (congrArg F hidx).symm)).2 hc)
      cap_gysin := by
        intro T g hg L hL s k D L' s' E e he hbase α
        let F : ℤ → Type u := chowGroup C (pullback.fst f g ≫ sX)
        have hidx : (k + 1) - p = (k - p) + 1 := by omega
        have cast_neg (i j : ℤ) (hij : i = j) (a : F i) :
            Eq.mp (congrArg F hij) (-a) = -(Eq.mp (congrArg F hij) a) := by
          cases hij
          rfl
        have hc := c.cap_gysin g L s k e he hbase α
        let β := G.onChow (g ≫ sY) L s k α
        have happ : (-c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k) β =
            -c.cap ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) k β := rfl
        simp only [AddMonoidHom.neg_apply]
        rw [cast_neg _ _ hidx, happ, map_neg]
        simpa only [AddMonoidHom.neg_apply, Pi.neg_apply, map_neg] using congrArg Neg.neg hc }

/-- **Stacks 0B76.** The zero bivariant class caps to zero. -/
@[simp, stacks 0B76 "the zero of the group A^p(X ⟶ Y)"]
theorem BivariantClass.zero_cap {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    (0 : BivariantClass C G sX sY f hf p).cap g k α = 0 :=
  rfl

/-- **Stacks 0B76.** A sum of bivariant classes caps to the sum of their cap products. -/
@[simp, stacks 0B76 "addition in A^p(X ⟶ Y) is pointwise on cap products"]
theorem BivariantClass.add_cap (c d : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (c + d).cap g k α = c.cap g k α + d.cap g k α :=
  rfl

/-- **Stacks 0B76.** A negated bivariant class caps to the negated cap product. -/
@[simp, stacks 0B76 "negation in A^p(X ⟶ Y) is pointwise on cap products"]
theorem BivariantClass.neg_cap (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (-c).cap g k α = -c.cap g k α :=
  rfl

/-- **Stacks 0B76.** Bivariant classes of degree `p` for `f` form a commutative additive
monoid. -/
instance : AddCommMonoid (BivariantClass C G sX sY f hf p) where
  add_assoc a b c := by
    apply BivariantClass.ext
    intro T g hg k α
    simp only [BivariantClass.add_cap]
    exact _root_.add_assoc _ _ _
  zero_add a := by
    apply BivariantClass.ext
    intro T g hg k α
    simp only [BivariantClass.add_cap, BivariantClass.zero_cap]
    exact _root_.zero_add _
  add_zero a := by
    apply BivariantClass.ext
    intro T g hg k α
    simp only [BivariantClass.add_cap, BivariantClass.zero_cap]
    exact _root_.add_zero _
  add_comm a b := by
    apply BivariantClass.ext
    intro T g hg k α
    simp only [BivariantClass.add_cap]
    exact _root_.add_comm _ _
  nsmul := nsmulRec

/-- **Stacks 0B76.** The difference of two bivariant classes. -/
instance : Sub (BivariantClass C G sX sY f hf p) where
  sub a b := a + -b

/-- **Stacks 0B76.** The group `A^p(X ⟶ Y)` of bivariant classes of degree `p` for `f`. -/
instance : AddCommGroup (BivariantClass C G sX sY f hf p) where
  toAddCommMonoid := inferInstance
  toNeg := inferInstance
  toSub := inferInstance
  neg_add_cancel a := by
    apply BivariantClass.ext
    intro T g hg k α
    simp only [BivariantClass.add_cap, BivariantClass.neg_cap, BivariantClass.zero_cap]
    exact _root_.neg_add_cancel _
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec

/-- **Stacks 0B76.** A difference of bivariant classes caps to the difference of their cap
products. -/
@[simp, stacks 0B76 "subtraction in A^p(X ⟶ Y) is pointwise on cap products"]
theorem BivariantClass.sub_cap (c d : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (c - d).cap g k α = c.cap g k α - d.cap g k α := by
  simp [sub_eq_add_neg]

/-- **Stacks 0B76.** A natural multiple of a bivariant class caps to that multiple of its cap
product. -/
@[simp, stacks 0B76 "natural multiples in A^p(X ⟶ Y) are pointwise on cap products"]
theorem BivariantClass.nsmul_cap (n : ℕ) (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (n • c).cap g k α = n • c.cap g k α := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

/-- **Stacks 0B76.** An integer multiple of a bivariant class caps to that multiple of its cap
product. -/
@[simp, stacks 0B76 "integer multiples in A^p(X ⟶ Y) are pointwise on cap products"]
theorem BivariantClass.zsmul_cap (n : ℤ) (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (n • c).cap g k α = n • c.cap g k α := by
  cases n with
  | ofNat n => exact BivariantClass.nsmul_cap C G sX sY f hf p n c g k α
  | negSucc n => simp [BivariantClass.nsmul_cap]

/-- The canonical map between two base changes of `f : X ⟶ Y` is itself a base change: the square
it forms with the two projections to the test schemes is cartesian. -/
public theorem isPullback_bivariantBaseChangeMap {X Y T T' : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (h : T' ⟶ T) :
    IsPullback (pullback.snd f (h ≫ g)) (bivariantBaseChangeMap f g h) h (pullback.snd f g) := by
  refine (IsPullback.of_hasPullback (pullback.snd f g) h).flip.of_iso
    (pullbackLeftPullbackSndIso f g h) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · refine (pullback.hom_ext ?_ ?_).symm
    · simp [bivariantBaseChangeMap, pullback.map]
    · simp only [bivariantBaseChangeMap, pullback.map, Category.comp_id, Category.assoc,
        pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd_assoc, Iso.refl_hom]
      exact pullback.condition.symm
  · simp
  · simp

end Stacks.Chow

end
