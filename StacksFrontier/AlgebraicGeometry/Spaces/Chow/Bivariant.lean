module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Bivariant classes for good algebraic spaces

In the situation of Stacks 0EDT let `f : X ⟶ Y` be a morphism of good algebraic spaces over the
base space `B` and let `p` be an integer. A *bivariant class `c` of degree `p` for `f`* assigns to
every good `Y' ⟶ Y` over `B` and every `k` an additive map

  `c ∩ - : CH_k(Y') ⟶ CH_{k-p}(X')`,  where  `X' = Y' ×_Y X`,

compatibly with the three operations chapter 82 puts on the Chow groups of good algebraic spaces:
proper pushforward, flat pullback of fixed relative dimension, and the refined Gysin map of
Stacks 0ER1. The group of all of them is `A^p(X ⟶ Y)`, and that group is
`AlgebraicGeometry.Space.BivariantClass`, an abelian group under the pointwise operations.

## Main definitions

* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.Ambient` — the ambient category of the
  Chow theory of a base situation, presheaves on its big fppf category.
* `AlgebraicGeometry.Space.GysinDatum` — the vanishing locus of Stacks 0ER1, in the form the
  Gysin compatibility of a bivariant class needs it: a closed subspace which is good over the
  base.
* `AlgebraicGeometry.Space.ChowGroupSystem` — the data of Stacks 82.15 and Stacks 82.22 which
  this development does not construct, bundled: rational equivalence on every good algebraic
  space over the base, proper pushforward, flat pullback of fixed relative dimension, and the
  refined Gysin maps. See the implementation notes.
* `AlgebraicGeometry.Space.ChowGroupSystem.chow` — the Chow group `CH_k(X')` such a system
  provides, `AlgebraicGeometry.Space.ChowGroupSystem.cycleClass` its quotient map from the
  group of `k`-cycles, and `AlgebraicGeometry.Space.ChowGroupSystem.chowCongr` its transport
  along an equality of structure morphisms.
* `AlgebraicGeometry.Space.bivariantBaseChangeMap` — the map `Y'' ×_Y X ⟶ Y' ×_Y X` induced by
  a morphism `Y'' ⟶ Y'`.
* `AlgebraicGeometry.Space.BivariantClass` — **Stacks 0ERJ**, the group `A^p(X ⟶ Y)` of
  bivariant classes of degree `p` for `f`.

## Main results

* `AlgebraicGeometry.Space.BivariantClass.ext` — a bivariant class is determined by its cap
  operations.
* `AlgebraicGeometry.Space.BivariantClass.zero_cap`,
  `AlgebraicGeometry.Space.BivariantClass.add_cap`,
  `AlgebraicGeometry.Space.BivariantClass.neg_cap`,
  `AlgebraicGeometry.Space.BivariantClass.sub_cap`,
  `AlgebraicGeometry.Space.BivariantClass.nsmul_cap`,
  `AlgebraicGeometry.Space.BivariantClass.zsmul_cap` — the abelian group structure on
  `A^p(X ⟶ Y)` is the pointwise one.

## Implementation notes

### What is parameterized, and why

Rational equivalence of cycles on an algebraic space is *not* available in this repository.
Only the groups `Z_k(X)` of `k`-cycles are, as `AlgebraicGeometry.Space.CycleGroup`: rational
equivalence is defined by the principal divisors `div(f)` of rational functions on the integral
closed subspaces of δ-dimension `k + 1`, and the order of vanishing of a rational function along
a prime divisor of an integral algebraic space is not constructed here. That obstruction and its
consequences are recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence`. With `CH_k` absent, so are the
three operations on it that Stacks 0ERJ quantifies over, and so is the refined Gysin
homomorphism of Stacks 0ER1, whose target is a Chow group already.

So all of it is a parameter: `AlgebraicGeometry.Space.ChowGroupSystem` is the datum of rational
equivalence on every good algebraic space over the base — a subgroup of `Z_k`, so that `CH_k` is
its quotient and comes with its abelian group structure and its cycle class map for free —
together with proper pushforward, flat pullback of relative dimension `r`, and, for the Gysin
maps, a predicate singling out the vanishing loci of Stacks 0ER1 among the good closed subspaces
and a Gysin map for each of them. Every declaration below carries that parameter, and
`@[stacks 0ERJ]` is placed on `AlgebraicGeometry.Space.BivariantClass` with a description saying
so: the definition of `A^p(X ⟶ Y)` is here in full, over data the source has already
constructed by the time it states 0ERJ and this repository has not.

Goodness of an algebraic space over the base,
`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.IsGood`, is a `Prop` taken as an explicit
argument rather than an instance, which is how the whole Chow development for algebraic spaces
is written. A Chow group therefore depends on a goodness proof;
definitional proof irrelevance makes that dependence invisible, so two spellings of one goodness
proof give the same group.

### Modelling

The fibre product `X' = Y' ×_Y X` is the categorical pullback `pullback f g` of the ambient
presheaf category, which has all limits; `pullback.fst f g` is its map to `X`, so a cap operation
lands in `G.chow (pullback.fst f g ≫ sX) _ (k - p)`. Goodness of that pullback over the base is
itself a theorem this repository does not have, so it is a hypothesis of the cap operation, where
proof irrelevance again makes it harmless.

The compatibility axioms are stated for an arbitrary morphism `h'` between two such pullbacks
making the indicated square cartesian and commuting with the maps to `X`, so they apply in
particular to the canonical base change map
`AlgebraicGeometry.Space.bivariantBaseChangeMap`. In the Gysin axiom the identification of the
base change of the vanishing locus `D' ⊆ Y'` with the vanishing locus `E' ⊆ X'` of the
pulled-back section is recorded by an isomorphism over the ambient pullback, and the induced map
on Chow groups is proper pushforward along it.

The flat axiom is an `HEq` because the flat pullback of a `k`-cycle has degree `k + r` while the
cap operation of degree `p` produces degree `(k + r) - p` on one side and `(k - p) + r` on the
other; these are the same integer and not the same term.

### The hypotheses inside the axioms

Properness of the base change `h'`, flatness and relative dimension of `h'`, and goodness of the
spaces involved are hypotheses of the axiom fields rather than conclusions, because the theorems
that would supply them for algebraic spaces — stability of properness, flatness and relative
dimension under base change, and goodness of a fibre product of good spaces — are not available
here. They are forced by typing, in the sense that the operations in the conclusion cannot be
written down without them, and each appears in the conclusion; proof irrelevance therefore makes
the quantified field equivalent to the unconditional one. The same applies to the hypothesis that
the pulled-back vanishing locus is again one of the loci of Stacks 0ER1.

## References

* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The ambient category -/

/-- The ambient category of the Chow theory of a base situation `D`: the presheaves on the big
fppf category over the base scheme of `D`. The good algebraic spaces over the base space
`D.space` are the objects of this category equipped with a morphism to `D.space` satisfying
`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.IsGood`. -/
abbrev BaseSpaceDimensionSituation.Ambient (D : BaseSpaceDimensionSituation.{u}) : Type (u + 1) :=
  (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u

/-! ### The vanishing locus a Gysin map is attached to -/

/-- The vanishing locus `D = Z(s)` of Stacks 0ER1 on a good algebraic space `X/B`, in the form
the Gysin compatibility of a bivariant class needs it: a closed subspace of `X` which is itself
good over the base. The invertible module and the global section it comes from are not recorded,
only the closed immersion they produce; which closed subspaces do arise this way is the predicate
`AlgebraicGeometry.Space.ChowGroupSystem.IsGysinDatum`. -/
structure GysinDatum (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient}
    (sX : X ⟶ D.space) where
  /-- The vanishing locus, as an object of the ambient category. -/
  locus : D.Ambient
  /-- The closed immersion `i : D ⟶ X` of the vanishing locus into the ambient space. -/
  ι : locus ⟶ X
  /-- The map from the vanishing locus is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion D.site D.base D.base_mem ι
  /-- The vanishing locus is again good over the base. -/
  isGood : D.IsGood (ι ≫ sX)

/-! ### The Chow-group data a bivariant class is stated against -/

/-- **The data of Stacks 82.15 and Stacks 82.22 that this development does not construct.** For
every good algebraic space over the base and every `k`, the subgroup of `k`-cycles rationally
equivalent to zero — so that the Chow group `CH_k` is its quotient — together with the proper
pushforward, the flat pullback of fixed relative dimension and the refined Gysin maps of
Stacks 0ER1 on those Chow groups.

This is what chapter 82 provides by the time it states Stacks 0ERJ. Bundling it is what makes
the three compatibility axioms of a bivariant class statable at all; see the implementation notes
of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant` for why none of it is available
here. -/
structure ChowGroupSystem (D : BaseSpaceDimensionSituation.{u}) where
  /-- The subgroup of `k`-cycles rationally equivalent to zero, on every good algebraic space
  over the base: the kernel of the cycle class map of Stacks 82.15. -/
  rationalEquivalences : ∀ {X : D.Ambient} (sX : X ⟶ D.space), D.IsGood sX → ∀ k : ℤ,
    AddSubgroup (CycleGroup D sX k)
  /-- Proper pushforward on Chow groups, along a proper morphism of good algebraic spaces over
  the base. -/
  properPushforward : ∀ {X Y : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (h : X ⟶ Y) (_hcomp : h ≫ sY = sX)
    (_hproper : IsProper D.site D.base D.base_mem h) (k : ℤ),
    CycleGroup D sX k ⧸ rationalEquivalences sX hX k →+
      CycleGroup D sY k ⧸ rationalEquivalences sY hY k
  /-- Flat pullback on Chow groups, along a flat morphism of good algebraic spaces over the base
  of relative dimension `r`; it raises the δ-dimension by `r`. -/
  flatPullback : ∀ {X Y : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (h : X ⟶ Y) (_hcomp : h ≫ sY = sX)
    (_hflat : IsFlat D.site D.base D.base_mem h) (r : ℕ)
    (_hr : HasRelativeDimension r D.site D.base D.base_mem h) (k : ℤ),
    CycleGroup D sY k ⧸ rationalEquivalences sY hY k →+
      CycleGroup D sX (k + (r : ℤ)) ⧸ rationalEquivalences sX hX (k + (r : ℤ))
  /-- Which good closed subspaces of a good algebraic space over the base are the vanishing
  locus `Z(s)` of a global section `s` of an invertible module, as in Stacks 0ER1. -/
  IsGysinDatum : ∀ {X : D.Ambient} (sX : X ⟶ D.space), D.IsGood sX → GysinDatum D sX → Prop
  /-- The refined Gysin homomorphism `i^* : CH_{k+1}(X) ⟶ CH_k(D)` of Stacks 0ER1, for every
  vanishing locus of a global section of an invertible module. -/
  gysin : ∀ {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (d : GysinDatum D sX)
    (_hd : IsGysinDatum sX hX d) (k : ℤ),
    CycleGroup D sX (k + 1) ⧸ rationalEquivalences sX hX (k + 1) →+
      CycleGroup D (d.ι ≫ sX) k ⧸ rationalEquivalences (d.ι ≫ sX) d.isGood k

/-- The Chow group `CH_k(X)` of a good algebraic space over the base that a Chow-group system
provides: the `k`-cycles modulo the system's rational equivalence. -/
abbrev ChowGroupSystem.chow {D : BaseSpaceDimensionSituation.{u}} (G : ChowGroupSystem D)
    {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) : Type (u + 1) :=
  CycleGroup D sX k ⧸ G.rationalEquivalences sX hX k

/-- The cycle class map `Z_k(X) ⟶ CH_k(X)` of a Chow-group system. -/
def ChowGroupSystem.cycleClass {D : BaseSpaceDimensionSituation.{u}} (G : ChowGroupSystem D)
    {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    CycleGroup D sX k →+ G.chow sX hX k :=
  QuotientAddGroup.mk' (G.rationalEquivalences sX hX k)

/-- Two spellings of the structure morphism of a good algebraic space over the base give the
same Chow group: goodness is a proposition, so the group depends on the morphism alone. -/
def ChowGroupSystem.chowCongr {D : BaseSpaceDimensionSituation.{u}} (G : ChowGroupSystem D)
    {X : D.Ambient} {s t : X ⟶ D.space} (hs : D.IsGood s) (ht : D.IsGood t) (h : s = t)
    (k : ℤ) : G.chow s hs k ≃+ G.chow t ht k := by
  subst h
  exact AddEquiv.refl _

/-! ### Base change of the ambient pullback -/

/-- The map `Y'' ×_Y X ⟶ Y' ×_Y X` between two base changes of `f : X ⟶ Y` induced by a
morphism `h : Y'' ⟶ Y'` of their bases. -/
abbrev bivariantBaseChangeMap (D : BaseSpaceDimensionSituation.{u}) {X Y Y' Y'' : D.Ambient}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : Y'' ⟶ Y') :
    pullback f (h ≫ g) ⟶ pullback f g :=
  pullback.map f (h ≫ g) f g (𝟙 X) h (𝟙 Y) (by simp) (by simp)

/-! ### Bivariant classes -/

/-- **Stacks 0ERJ.** A bivariant class of degree `p` for a morphism `f : X ⟶ Y` of good
algebraic spaces over the base: a rule assigning to every good `Y' ⟶ Y` over the base and every
`k` an additive map `CH_k(Y') ⟶ CH_{k-p}(Y' ×_Y X)`, natural for proper pushforward, for flat
pullback of fixed relative dimension, and for the refined Gysin maps of Stacks 0ER1. The group
of all of them is denoted `A^p(X ⟶ Y)`.

Stated against an `AlgebraicGeometry.Space.ChowGroupSystem`, which supplies the Chow groups of
Stacks 82.15 and the three operations on them that the axioms quantify over, none of which this
repository constructs; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant`. -/
@[stacks 0ERJ "over the parameterized Chow groups of 82.15 and Gysin maps of 82.22"]
structure BivariantClass (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D)
    {X Y : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hf : f ≫ sY = sX) (p : ℤ) where
  /-- The cap operation `c ∩ - : CH_k(Y') ⟶ CH_{k-p}(Y' ×_Y X)` on the Chow group of every good
  test space over `Y`. -/
  cap : ∀ {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ),
    G.chow (g ≫ sY) hY' k →+ G.chow (pullback.fst f g ≫ sX) hX' (k - p)
  /-- Cap product commutes with proper pushforward: Stacks 0ERJ (1). -/
  proper_naturality : ∀ {Y' Y'' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (h : Y'' ⟶ Y')
    (hY'' : D.IsGood ((h ≫ g) ≫ sY)) (hX'' : D.IsGood (pullback.fst f (h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (_sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g))
    (hh' : IsProper D.site D.base D.base_mem h') (k : ℤ)
    (α : G.chow ((h ≫ g) ≫ sY) hY'' k),
    cap g hY' hX' k
        (G.properPushforward ((h ≫ g) ≫ sY) hY'' (g ≫ sY) hY' h
          (Category.assoc h g sY).symm hh k α) =
      G.properPushforward (pullback.fst f (h ≫ g) ≫ sX) hX'' (pullback.fst f g ≫ sX) hX' h'
        (by rw [← Category.assoc, hfst]) hh' (k - p) (cap (h ≫ g) hY'' hX'' k α)
  /-- Cap product commutes with flat pullback of fixed relative dimension: Stacks 0ERJ (2). -/
  flat_naturality : ∀ {Y' Y'' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (h : Y'' ⟶ Y')
    (hY'' : D.IsGood ((h ≫ g) ≫ sY)) (hX'' : D.IsGood (pullback.fst f (h ≫ g) ≫ sX))
    (hh : IsFlat D.site D.base D.base_mem h) (r : ℕ)
    (hr : HasRelativeDimension r D.site D.base D.base_mem h)
    (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (_sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g))
    (hh' : IsFlat D.site D.base D.base_mem h')
    (hr' : HasRelativeDimension r D.site D.base D.base_mem h') (k : ℤ)
    (α : G.chow (g ≫ sY) hY' k),
    HEq
      (cap (h ≫ g) hY'' hX'' (k + (r : ℤ))
        (G.flatPullback ((h ≫ g) ≫ sY) hY'' (g ≫ sY) hY' h (Category.assoc h g sY).symm hh r
          hr k α))
      (G.flatPullback (pullback.fst f (h ≫ g) ≫ sX) hX'' (pullback.fst f g ≫ sX) hX' h'
        (by rw [← Category.assoc, hfst]) hh' r hr' (k - p) (cap g hY' hX' k α))
  /-- Cap product commutes with the refined Gysin map of every pulled-back vanishing locus:
  Stacks 0ERJ (3). -/
  gysin_naturality : ∀ {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (d : GysinDatum D (g ≫ sY))
    (hd : G.IsGysinDatum (g ≫ sY) hY' d) (e : GysinDatum D (pullback.fst f g ≫ sX))
    (he : G.IsGysinDatum (pullback.fst f g ≫ sX) hX' e)
    (hXd : D.IsGood (pullback.fst f (d.ι ≫ g) ≫ sX))
    (iso : pullback f (d.ι ≫ g) ≅ e.locus)
    (_hiso : iso.hom ≫ e.ι = bivariantBaseChangeMap D f g d.ι)
    (hbase : iso.hom ≫ (e.ι ≫ pullback.fst f g ≫ sX) = pullback.fst f (d.ι ≫ g) ≫ sX)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom) (k : ℤ)
    (α : G.chow (g ≫ sY) hY' (k + 1)),
    G.properPushforward (pullback.fst f (d.ι ≫ g) ≫ sX) hXd
        (e.ι ≫ pullback.fst f g ≫ sX) e.isGood iso.hom hbase hisoProper (k - p)
        (cap (d.ι ≫ g) d.isGood hXd k (G.gysin (g ≫ sY) hY' d hd k α)) =
      G.gysin (pullback.fst f g ≫ sX) hX' e he (k - p)
        (Eq.mp (congrArg (G.chow (pullback.fst f g ≫ sX) hX')
          (by omega : k + 1 - p = k - p + 1)) (cap g hY' hX' (k + 1) α))

variable (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D) {X Y : D.Ambient}
  (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
  (hf : f ≫ sY = sX) (p : ℤ)

/-- **Stacks 0ERJ.** Two bivariant classes agree as soon as all their cap operations agree. -/
@[ext]
theorem BivariantClass.ext {c d : BivariantClass D G sX hX sY hY f hf p}
    (h : ∀ {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
      (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ) (α : G.chow (g ≫ sY) hY' k),
      c.cap g hY' hX' k α = d.cap g hY' hX' k α) : c = d := by
  cases c with
  | mk ccap cproper cflat cgysin =>
    cases d with
    | mk dcap dproper dflat dgysin =>
      have hcap : @ccap = @dcap := by
        funext Y' g hY' hX' k
        exact AddMonoidHom.ext fun α ↦ h g hY' hX' k α
      cases hcap
      congr

/-- **Stacks 0ERJ.** The zero bivariant class, capping to zero on every good test space. -/
instance : Zero (BivariantClass D G sX hX sY hY f hf p) where
  zero :=
    { cap := fun _ _ _ _ => 0
      proper_naturality := by intros; simp
      flat_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        simp only [AddMonoidHom.zero_apply, map_zero]
        have hidx : k + (r : ℤ) - p = k - p + (r : ℤ) := by omega
        rw [hidx]
      gysin_naturality := by
        intro Y' g hY' hX' d hd e he hXd iso _hiso hbase hisoProper k α
        have cast_zero : ∀ (i j : ℤ) (hij : i = j),
            Eq.mp (congrArg (G.chow (pullback.fst f g ≫ sX) hX') hij)
                (0 : G.chow (pullback.fst f g ≫ sX) hX' i) = 0 := by
          intro i j hij
          cases hij
          rfl
        simp only [AddMonoidHom.zero_apply, map_zero]
        rw [cast_zero, map_zero]
        omega }

/-- **Stacks 0ERJ.** The pointwise sum of two bivariant classes. -/
instance : Add (BivariantClass D G sX hX sY hY f hf p) where
  add c d :=
    { cap := fun g hY' hX' k => c.cap g hY' hX' k + d.cap g hY' hX' k
      proper_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        simp only [AddMonoidHom.add_apply, map_add]
        exact congrArg₂ (· + ·)
          (c.proper_naturality g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α)
          (d.proper_naturality g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α)
      flat_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        let F : ℤ → Type (u + 1) := G.chow (pullback.fst f (h ≫ g) ≫ sX) hX''
        have hidx : k + (r : ℤ) - p = k - p + (r : ℤ) := by omega
        have hc := c.flat_naturality g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        have hd := d.flat_naturality g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
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
      gysin_naturality := by
        intro Y' g hY' hX' dd hdd e he hXd iso _hiso hbase hisoProper k α
        have cast_add : ∀ (i j : ℤ) (hij : i = j)
            (a b : G.chow (pullback.fst f g ≫ sX) hX' i),
            Eq.mp (congrArg (G.chow (pullback.fst f g ≫ sX) hX') hij) (a + b) =
              Eq.mp (congrArg (G.chow (pullback.fst f g ≫ sX) hX') hij) a +
                Eq.mp (congrArg (G.chow (pullback.fst f g ≫ sX) hX') hij) b := by
          intro i j hij a b
          cases hij
          rfl
        have hc := c.gysin_naturality g hY' hX' dd hdd e he hXd iso _hiso hbase hisoProper k α
        have hd := d.gysin_naturality g hY' hX' dd hdd e he hXd iso _hiso hbase hisoProper k α
        simp only [AddMonoidHom.add_apply]
        rw [map_add, hc, hd, ← map_add, ← cast_add]
        omega }

/-- **Stacks 0ERJ.** The pointwise negation of a bivariant class. -/
instance : Neg (BivariantClass D G sX hX sY hY f hf p) where
  neg c :=
    { cap := fun g hY' hX' k => -c.cap g hY' hX' k
      proper_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        simpa only [AddMonoidHom.neg_apply, map_neg] using
          congrArg Neg.neg (c.proper_naturality g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α)
      flat_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        let F : ℤ → Type (u + 1) := G.chow (pullback.fst f (h ≫ g) ≫ sX) hX''
        have hidx : k + (r : ℤ) - p = k - p + (r : ℤ) := by omega
        have hc := c.flat_naturality g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        have cast_neg (i j : ℤ) (hij : i = j) (a : F j) :
            cast (congrArg F hij).symm (-a) = -cast (congrArg F hij).symm a := by
          cases hij
          rfl
        simp only [AddMonoidHom.neg_apply, map_neg]
        apply (eq_cast_iff_heq (e := (congrArg F hidx).symm)).1
        rw [cast_neg _ _ hidx]
        exact congrArg Neg.neg ((eq_cast_iff_heq (e := (congrArg F hidx).symm)).2 hc)
      gysin_naturality := by
        intro Y' g hY' hX' dd hdd e he hXd iso _hiso hbase hisoProper k α
        have cast_neg : ∀ (i j : ℤ) (hij : i = j)
            (a : G.chow (pullback.fst f g ≫ sX) hX' i),
            Eq.mp (congrArg (G.chow (pullback.fst f g ≫ sX) hX') hij) (-a) =
              -Eq.mp (congrArg (G.chow (pullback.fst f g ≫ sX) hX') hij) a := by
          intro i j hij a
          cases hij
          rfl
        have hc := c.gysin_naturality g hY' hX' dd hdd e he hXd iso _hiso hbase hisoProper k α
        simp only [AddMonoidHom.neg_apply]
        rw [map_neg, hc, ← map_neg, ← cast_neg]
        omega }

/-- **Stacks 0ERJ.** The zero bivariant class caps to zero. -/
@[simp]
theorem BivariantClass.zero_cap {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ) (α : G.chow (g ≫ sY) hY' k) :
    (0 : BivariantClass D G sX hX sY hY f hf p).cap g hY' hX' k α = 0 :=
  rfl

/-- **Stacks 0ERJ.** A sum of bivariant classes caps to the sum of their cap products. -/
@[simp]
theorem BivariantClass.add_cap (c d : BivariantClass D G sX hX sY hY f hf p) {Y' : D.Ambient}
    (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
    (α : G.chow (g ≫ sY) hY' k) :
    (c + d).cap g hY' hX' k α = c.cap g hY' hX' k α + d.cap g hY' hX' k α :=
  rfl

/-- **Stacks 0ERJ.** A negated bivariant class caps to the negated cap product. -/
@[simp]
theorem BivariantClass.neg_cap (c : BivariantClass D G sX hX sY hY f hf p) {Y' : D.Ambient}
    (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
    (α : G.chow (g ≫ sY) hY' k) :
    (-c).cap g hY' hX' k α = -c.cap g hY' hX' k α :=
  rfl

/-- **Stacks 0ERJ.** Bivariant classes of degree `p` for `f` form a commutative additive
monoid. -/
instance : AddCommMonoid (BivariantClass D G sX hX sY hY f hf p) where
  add_assoc a b c := by
    apply BivariantClass.ext
    intro Y' g hY' hX' k α
    simp only [BivariantClass.add_cap]
    exact _root_.add_assoc _ _ _
  zero_add a := by
    apply BivariantClass.ext
    intro Y' g hY' hX' k α
    simp only [BivariantClass.add_cap, BivariantClass.zero_cap]
    exact _root_.zero_add _
  add_zero a := by
    apply BivariantClass.ext
    intro Y' g hY' hX' k α
    simp only [BivariantClass.add_cap, BivariantClass.zero_cap]
    exact _root_.add_zero _
  add_comm a b := by
    apply BivariantClass.ext
    intro Y' g hY' hX' k α
    simp only [BivariantClass.add_cap]
    exact _root_.add_comm _ _
  nsmul := nsmulRec

/-- **Stacks 0ERJ.** The difference of two bivariant classes. -/
instance : Sub (BivariantClass D G sX hX sY hY f hf p) where
  sub a b := a + -b

/-- **Stacks 0ERJ.** The group `A^p(X ⟶ Y)` of bivariant classes of degree `p` for `f`. -/
instance : AddCommGroup (BivariantClass D G sX hX sY hY f hf p) where
  toAddCommMonoid := inferInstance
  toNeg := inferInstance
  toSub := inferInstance
  neg_add_cancel a := by
    apply BivariantClass.ext
    intro Y' g hY' hX' k α
    simp only [BivariantClass.add_cap, BivariantClass.neg_cap, BivariantClass.zero_cap]
    exact _root_.neg_add_cancel _
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec

/-- **Stacks 0ERJ.** A difference of bivariant classes caps to the difference of their cap
products. -/
@[simp]
theorem BivariantClass.sub_cap (c d : BivariantClass D G sX hX sY hY f hf p) {Y' : D.Ambient}
    (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
    (α : G.chow (g ≫ sY) hY' k) :
    (c - d).cap g hY' hX' k α = c.cap g hY' hX' k α - d.cap g hY' hX' k α := by
  simp [sub_eq_add_neg]

/-- **Stacks 0ERJ.** A natural multiple of a bivariant class caps to that multiple of its cap
product. -/
@[simp]
theorem BivariantClass.nsmul_cap (n : ℕ) (c : BivariantClass D G sX hX sY hY f hf p)
    {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ) (α : G.chow (g ≫ sY) hY' k) :
    (n • c).cap g hY' hX' k α = n • c.cap g hY' hX' k α := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

/-- **Stacks 0ERJ.** An integer multiple of a bivariant class caps to that multiple of its cap
product. -/
@[simp]
theorem BivariantClass.zsmul_cap (n : ℤ) (c : BivariantClass D G sX hX sY hY f hf p)
    {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ) (α : G.chow (g ≫ sY) hY' k) :
    (n • c).cap g hY' hX' k α = n • c.cap g hY' hX' k α := by
  cases n with
  | ofNat n => exact BivariantClass.nsmul_cap D G sX hX sY hY f hf p n c g hY' hX' k α
  | negSucc n => simp [BivariantClass.nsmul_cap]

end AlgebraicGeometry.Space

end
