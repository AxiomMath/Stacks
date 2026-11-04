module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection

/-!
# Bivariant classes over the constructed Chow groups

In the situation of Stacks 0EDT let `f : X ⟶ Y` be a morphism of good algebraic spaces over the
base space `D.space` and let `p` be an integer.  **Stacks 0ERJ** calls a *bivariant class `c` of
degree `p` for `f`* a rule assigning to every morphism `g : Y' ⟶ Y` of good algebraic spaces
over the base and every `k` a homomorphism

  `c ∩ - : CH_k(Y') ⟶ CH_{k-p}(X')`,  where  `X' = Y' ×_Y X`,

commuting with proper pushforward, with flat pullback of fixed relative dimension, and with the
refined Gysin maps of Stacks 0ER1.  The collection of all of them is `A^p(X ⟶ Y)`, and it is
`AlgebraicGeometry.Space.BivariantClassCanonical`, an abelian group under the pointwise
operations.

## Main definitions

* `AlgebraicGeometry.Space.cycleGroupDegreeCongr` — the transport of `Z_k(X)` along an equality
  of degrees.
* `AlgebraicGeometry.Space.bivariantPullbackSheaf`,
  `AlgebraicGeometry.Space.bivariantPullbackSection` and
  `AlgebraicGeometry.Space.bivariantPullbackVanishingLocus` — the triple
  `(𝒩', t', j' : E' → X')` of Stacks 0ERJ (3), the inverse image along `X' ⟶ Y'` of a triple
  `(ℒ', s', i' : D' → Y')` on the test space, by Stacks 0ER3.
* `AlgebraicGeometry.Space.BivariantClassCanonical` — **Stacks 0ERJ**, the group
  `A^p(X ⟶ Y)` of bivariant classes of degree `p` for `f`, over the Chow groups
  `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6 and the operations of
  Stacks 0EP1, Stacks 0EP8 and Stacks 0ER1.

## Main results

* `AlgebraicGeometry.Space.BivariantClassCanonical.ext` — a bivariant class is determined by its
  cap operations.
* `AlgebraicGeometry.Space.BivariantClassCanonical.zero_cap`,
  `AlgebraicGeometry.Space.BivariantClassCanonical.add_cap`,
  `AlgebraicGeometry.Space.BivariantClassCanonical.neg_cap`,
  `AlgebraicGeometry.Space.BivariantClassCanonical.sub_cap` — the abelian group structure on
  `A^p(X ⟶ Y)` is the pointwise one.
* `AlgebraicGeometry.Space.trivialChowGroupSystem` and
  `AlgebraicGeometry.Space.subsingleton_chow_trivialChowGroupSystem` — a
  `AlgebraicGeometry.Space.ChowGroupSystem` whose Chow groups are all trivial.

## Implementation notes

### The Chow groups and the operations

The Chow groups and the three operations the axioms of Stacks 0ERJ quantify over are the following:

* `CH_k(Y')` is `AlgebraicGeometry.Space.chowGroupCanonical`, the quotient of `Z_k(Y')` by the
  cycles rationally equivalent to zero of Stacks 0EQ6 part (2), with the principal divisors read at
  the canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK;
* proper pushforward is `AlgebraicGeometry.Space.properCyclePushforward`, Stacks 0EP1;
* flat pullback of relative dimension `r` is `AlgebraicGeometry.Space.flatPullbackMap`, Stacks
  0EP8;
* the refined Gysin map of a triple `(ℒ, s, i : E → Y')` as in Stacks 0ER1 is
  `AlgebraicGeometry.Space.gysinCycleMap` at the component rule
  `AlgebraicGeometry.Space.sectionGysinRule`, in which clause (1)(a) is the cycle `[E ∩ W]_k` of
  Stacks 0EE9 and clause (1)(b) the Weil divisor `div_{ℒ|_W}(t_W)` of Stacks 0EQE at the regular
  meromorphic section of Stacks 0EPQ. The triple `(ℒ, s)` is quantified over in the axiom, as the
  source quantifies over `(ℒ', s', i' : D' → Y')`.

The pulled-back triple `(𝒩', t', j' : E' → X')` of axiom (3) is *not* quantified over: it is the
inverse image of `(ℒ', s')` along `X' = Y' ×_Y X ⟶ Y'`, which is Stacks 0ER3, namely
`AlgebraicGeometry.Space.bivariantPullbackSheaf` and
`AlgebraicGeometry.Space.bivariantPullbackSection`, with `E'` its vanishing locus
`AlgebraicGeometry.Space.bivariantPullbackVanishingLocus`. The refined Gysin map depends on the
sheaf and not only on the locus, through clause (1)(b) of Stacks 0ER1. An assertion quantified over
an arbitrary pair whose vanishing locus is merely isomorphic to the base change of `D'` would be
strictly stronger than Stacks 0ERJ: taking `s' = 0`, so that `D' = Y'` and `E' = X'`, it would
demand `c ∩ (c₁(ℒ') ∩ α) = c₁(𝒩) ∩ (c ∩ α)` for every invertible `𝒩` on `X'`, which already fails
for the identity class.

### Cycle representatives

The three operations above are maps *of cycles*, and each axiom is stated by asserting the
existence of *cycle representatives* through which the equation holds. Axiom (1) reads: for every
cycle `α''` on `Y''` there is a cycle `β''` on `X''` with

  `c ∩ [α''] = [β'']`   and   `c ∩ [h_*α''] = [h'_*β'']`.

Given the descent of the operations to the Chow groups (Stacks 0EQC, Stacks 0EQB and Stacks 0ERA)
this is equivalent to the source's `c ∩ h_*α'' = h'_*(c ∩ α'')`. One direction takes any
representative `β''` of `c ∩ [α'']`, which exists because the class map is surjective, and rewrites
`[h'_*β''] = h'_*[β'']`; the other takes a representative `α''` of a given class and runs the same
rewriting backwards. The universally quantified reading, "*for every* representative `β''` of
`c ∩ [α'']`, `c ∩ [h_*α''] = [h'_*β'']`", is stronger: instantiating it at `α'' = 0` and at a `β''`
rationally equivalent to zero yields `[h'_*β''] = 0`, that is, Stacks 0EQC.

### The degree bookkeeping

`AlgebraicGeometry.Space.flatPullbackMap` takes its target degree as an argument together with the
equation `m + r = n` defining it, so axiom (2) needs no transport: the two readings `(k + r) - p`
and `(k - p) + r` of the degree of the flat pullback of `c ∩ α` are handled by instantiating `n` at
the first. Axiom (3) does need one, because the refined Gysin map of Stacks 0ER1 is typed
`Z_{k+1}(X) ⟶ Z_k(E)` with no such freedom, and the class it is applied to has degree `k + 1 - p`
while the map wants `(k - p) + 1`; that is `AlgebraicGeometry.Space.cycleGroupDegreeCongr`.

### Hypotheses of the axiom fields

Properness of the base change `h'`, its flatness and relative dimension, and goodness of the spaces
involved are hypotheses of the axiom fields. Each of them appears in the conclusion of its field,
since the operations cannot be written down without it. In axiom (3) the identification of
`Y' ×_Y X ×_{Y'} D'` with the vanishing locus `E' ⊆ X'` of the pulled-back section is likewise
recorded by an isomorphism over the ambient pullback, as in
`AlgebraicGeometry.Space.BivariantClass`.


## References

* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### Transport of cycles along an equality of degrees -/

/-- The group of `k`-cycles transported along an equality of degrees `k = l`. -/
def cycleGroupDegreeCongr {X : D.Ambient} (sX : X ⟶ D.space) {k l : ℤ} (h : k = l) :
    CycleGroup D sX k ≃+ CycleGroup D sX l := by
  subst h
  exact AddEquiv.refl _

/-- Transport of cycles along `rfl` is the identity. -/
@[simp]
theorem cycleGroupDegreeCongr_refl {X : D.Ambient} (sX : X ⟶ D.space) (k : ℤ)
    (α : CycleGroup D sX k) : cycleGroupDegreeCongr D sX (rfl : k = k) α = α :=
  rfl

/-! ### The pullback to `Y' ×_Y X` of a section of an invertible sheaf on `Y'` -/

section GysinPullback

variable {X Y Y' : D.Ambient} (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (f : X ⟶ Y) (g : Y' ⟶ Y)
  (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX))
  (L : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (t : L.sections)

/-- The projection `X' = Y' ×_Y X ⟶ Y'` of the base change of `f : X ⟶ Y` along a test space
`g : Y' ⟶ Y`, as a morphism of algebraic spaces over the base.  This is the morphism along
which Stacks 0ERJ (3) pulls the triple `(ℒ', s', i' : D' → Y')` back to `X'`. -/
abbrev bivariantTestProjection :
    (⟨pullback f g, hX'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y', hY'.1⟩ :=
  ObjectProperty.homMk (pullback.snd f g)

/-- The sheaf `𝒩' = (X' → Y')^*ℒ'` of Stacks 0ERJ (3): the inverse image to `X' = Y' ×_Y X` of
an invertible sheaf on the test space `Y'`, by Stacks 0ER3. -/
abbrev bivariantPullbackSheaf :
    Modules.{u, u} D.site D.base D.base_mem (pullback f g) hX'.1 :=
  pullbackSheaf D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
    (bivariantTestProjection D sX sY f g hY' hX') L

/-- The section `t' = (X' → Y')^*s'` of Stacks 0ERJ (3): the inverse image to `X'` of a global
section of `ℒ'`, by Stacks 0ER3. -/
abbrev bivariantPullbackSection :
    (bivariantPullbackSheaf D sX sY f g hY' hX' L).sections :=
  pullbackGlobalSection D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
    (bivariantTestProjection D sX sY f g hY' hX') L t

/-- **Stacks 0B8P.** The inverse image to `X'` of an invertible sheaf on `Y'` is invertible. -/
theorem isInvertibleSheaf_bivariantPullbackSheaf (hL : IsInvertibleSheaf D (g ≫ sY) hY' L) :
    IsInvertibleSheaf D (pullback.fst f g ≫ sX) hX'
      (bivariantPullbackSheaf D sX sY f g hY' hX' L) :=
  isInvertibleSheaf_pullbackSheaf D (g ≫ sY) hY' (pullback.fst f g ≫ sX) hX'
    (bivariantTestProjection D sX sY f g hY' hX') L hL

/-- The vanishing locus `E' = Z(t') ⊆ X'` of the pulled-back section, which Stacks 0ER3
identifies with the base change `X' ×_{Y'} D'` of the vanishing locus `D' = Z(s') ⊆ Y'`. -/
abbrev bivariantPullbackVanishingLocus :
    ClosedSubspaces D.site D.base D.base_mem (pullback f g) :=
  vanishingLocus D (pullback.fst f g ≫ sX) hX' (bivariantPullbackSheaf D sX sY f g hY' hX' L)
    (bivariantPullbackSection D sX sY f g hY' hX' L t)

end GysinPullback

/-! ### Bivariant classes -/

/-- A bivariant class of degree `p` for a morphism `f : X ⟶ Y` of good algebraic spaces over the
base: a rule assigning to every good `g : Y' ⟶ Y` over the base and every `k` an additive map
`CH_k(Y') ⟶ CH_{k-p}(Y' ×_Y X)`, natural for proper pushforward, for flat pullback of fixed
relative dimension, and for the refined Gysin maps of Stacks 0ER1. The group of all of them is
denoted `A^p(X ⟶ Y)`.

The Chow groups are `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6, and the three
operations are the operations on cycles of Stacks 0EP1, Stacks 0EP8 and Stacks 0ER1; each axiom
asserts the source's equation through cycle representatives. -/
@[stacks 0ERJ "the group A^p(X → Y) of bivariant classes of degree p, over the constructed Chow \
groups of Stacks 0EQ6 and the constructed proper pushforward, flat pullback and refined Gysin \
maps of Stacks 0EP1, 0EP8 and 0ER1; the three naturality axioms are stated through cycle \
representatives, equivalently to the source's equations, because the descent of those three \
operations to Chow groups is Stacks 0EQC, 0EQB and 0ERA and is not proved here"]
structure BivariantClassCanonical {X Y : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hf : f ≫ sY = sX) (p : ℤ) where
  /-- The cap operation `c ∩ - : CH_k(Y') ⟶ CH_{k-p}(Y' ×_Y X)` on the Chow group of every good
  test space over `Y`. -/
  cap : ∀ {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ),
    chowGroupCanonical.{v} D (g ≫ sY) hY' k →+
      chowGroupCanonical.{v} D (pullback.fst f g ≫ sX) hX' (k - p)
  /-- Cap product commutes with proper pushforward: Stacks 0ERJ (1). -/
  proper_naturality : ∀ {Y' Y'' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (h : Y'' ⟶ Y')
    (hY'' : D.IsGood ((h ≫ g) ≫ sY)) (hX'' : D.IsGood (pullback.fst f (h ≫ g) ≫ sX))
    (hh : IsProper D.site D.base D.base_mem h) (h' : pullback f (h ≫ g) ⟶ pullback f g)
    (_sq : IsPullback (pullback.snd f (h ≫ g)) h' h (pullback.snd f g))
    (hfst : h' ≫ pullback.fst f g = pullback.fst f (h ≫ g))
    (hh' : IsProper D.site D.base D.base_mem h') (k : ℤ)
    (α : CycleGroup D ((h ≫ g) ≫ sY) k),
    ∃ β : CycleGroup D (pullback.fst f (h ≫ g) ≫ sX) (k - p),
      cap (h ≫ g) hY'' hX'' k (chowClassCanonical.{v} D ((h ≫ g) ≫ sY) hY'' k α) =
          chowClassCanonical.{v} D (pullback.fst f (h ≫ g) ≫ sX) hX'' (k - p) β ∧
        cap g hY' hX' k (chowClassCanonical.{v} D (g ≫ sY) hY' k
            (properCyclePushforward D ((h ≫ g) ≫ sY) hY'' (g ≫ sY) hY'
              (Category.assoc h g sY).symm hh.2.1.2 k α)) =
          chowClassCanonical.{v} D (pullback.fst f g ≫ sX) hX' (k - p)
            (properCyclePushforward D (pullback.fst f (h ≫ g) ≫ sX) hX''
              (pullback.fst f g ≫ sX) hX' (by rw [← Category.assoc, hfst]) hh'.2.1.2 (k - p) β)
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
    (α : CycleGroup D (g ≫ sY) k),
    ∃ β : CycleGroup D (pullback.fst f g ≫ sX) (k - p),
      cap g hY' hX' k (chowClassCanonical.{v} D (g ≫ sY) hY' k α) =
          chowClassCanonical.{v} D (pullback.fst f g ≫ sX) hX' (k - p) β ∧
        cap (h ≫ g) hY'' hX'' (k + (r : ℤ))
            (chowClassCanonical.{v} D ((h ≫ g) ≫ sY) hY'' (k + (r : ℤ))
              (flatPullbackMap D ((h ≫ g) ≫ sY) hY'' (g ≫ sY) hY' h
                (Category.assoc h g sY).symm r hh hr k (k + (r : ℤ)) rfl α)) =
          chowClassCanonical.{v} D (pullback.fst f (h ≫ g) ≫ sX) hX''
            (k + (r : ℤ) - p)
            (flatPullbackMap D (pullback.fst f (h ≫ g) ≫ sX) hX'' (pullback.fst f g ≫ sX) hX'
              h' (by rw [← Category.assoc, hfst]) r hh' hr' (k - p) (k + (r : ℤ) - p)
              (by omega) β)
  /-- Cap product commutes with the refined Gysin map of every pulled-back vanishing locus:
  Stacks 0ERJ (3). -/
  gysin_naturality : ∀ {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX))
    (L : Modules.{u, u} D.site D.base D.base_mem Y' hY'.1) (t : L.sections)
    (hL : IsInvertibleSheaf D (g ≫ sY) hY' L)
    (hXd : D.IsGood (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX))
    (iso : pullback f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≅
      (bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.toFunctor)
    (_hiso : iso.hom ≫ (bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.ι =
      bivariantBaseChangeMap D f g (vanishingLocus D (g ≫ sY) hY' L t).1.ι)
    (hbase : iso.hom ≫ ((bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.ι ≫
        pullback.fst f g ≫ sX) =
      pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX)
    (hisoProper : IsProper D.site D.base D.base_mem iso.hom) (k : ℤ)
    (α : CycleGroup D (g ≫ sY) (k + 1)),
    ∃ (β : CycleGroup D (pullback.fst f g ≫ sX) (k - p + 1))
      (γ : CycleGroup D (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX)
        (k - p)),
      cap g hY' hX' (k + 1)
            (chowClassCanonical.{v} D (g ≫ sY) hY' (k + 1) α) =
          chowClassCanonical.{v} D (pullback.fst f g ≫ sX) hX' (k + 1 - p)
            (cycleGroupDegreeCongr D (pullback.fst f g ≫ sX) (by omega) β) ∧
        cap ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g)
              (isGood_vanishingLocus D (g ≫ sY) hY' L t) hXd k
              (chowClassCanonical.{v} D ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g ≫ sY)
                (isGood_vanishingLocus D (g ≫ sY) hY' L t) k
                (gysinCycleMap D (g ≫ sY) (vanishingLocus D (g ≫ sY) hY' L t)
                  (isGood_vanishingLocus D (g ≫ sY) hY' L t) k
                  (sectionGysinRule D (g ≫ sY) hY' L t k hL) α)) =
            chowClassCanonical.{v} D
              (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX) hXd (k - p)
              γ ∧
          chowClassCanonical.{v} D
              ((bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.ι ≫
                pullback.fst f g ≫ sX)
              (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX'
                (bivariantPullbackSheaf D sX sY f g hY' hX' L)
                (bivariantPullbackSection D sX sY f g hY' hX' L t)) (k - p)
              (properCyclePushforward D
                (pullback.fst f ((vanishingLocus D (g ≫ sY) hY' L t).1.ι ≫ g) ≫ sX) hXd
                ((bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.ι ≫
                  pullback.fst f g ≫ sX)
                (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX'
                  (bivariantPullbackSheaf D sX sY f g hY' hX' L)
                  (bivariantPullbackSection D sX sY f g hY' hX' L t)) hbase
                hisoProper.2.1.2 (k - p) γ) =
            chowClassCanonical.{v} D
              ((bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t).1.ι ≫
                pullback.fst f g ≫ sX)
              (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX'
                (bivariantPullbackSheaf D sX sY f g hY' hX' L)
                (bivariantPullbackSection D sX sY f g hY' hX' L t)) (k - p)
              (gysinCycleMap D (pullback.fst f g ≫ sX)
                (bivariantPullbackVanishingLocus D sX sY f g hY' hX' L t)
                (isGood_vanishingLocus D (pullback.fst f g ≫ sX) hX'
                  (bivariantPullbackSheaf D sX sY f g hY' hX' L)
                  (bivariantPullbackSection D sX sY f g hY' hX' L t)) (k - p)
                (sectionGysinRule D (pullback.fst f g ≫ sX) hX'
                  (bivariantPullbackSheaf D sX sY f g hY' hX' L)
                  (bivariantPullbackSection D sX sY f g hY' hX' L t) (k - p)
                  (isInvertibleSheaf_bivariantPullbackSheaf D sX sY f g hY' hX' L hL)) β)

/-! ### The group structure -/

variable {X Y : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
  (hY : D.IsGood sY) (f : X ⟶ Y) (hf : f ≫ sY = sX) (p : ℤ)

/-- **Stacks 0ERJ.** Two bivariant classes agree as soon as all their cap operations agree. -/
@[ext]
theorem BivariantClassCanonical.ext {c d : BivariantClassCanonical D sX hX sY hY f hf p}
    (h : ∀ {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
      (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
      (α : chowGroupCanonical D (g ≫ sY) hY' k),
      c.cap g hY' hX' k α = d.cap g hY' hX' k α) : c = d := by
  cases c with
  | mk ccap cproper cflat cgysin =>
    cases d with
    | mk dcap dproper dflat dgysin =>
      have hcap : @ccap = @dcap := by
        funext Y' g hY' hX' k
        exact AddMonoidHom.ext fun α => h (Y' := Y') g hY' hX' k α
      cases hcap
      congr

/-- **Stacks 0ERJ.** The zero bivariant class, capping to zero on every good test space. -/
instance : Zero (BivariantClassCanonical D sX hX sY hY f hf p) where
  zero :=
    { cap := fun _ _ _ _ => 0
      proper_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        exact ⟨0, by simp, by simp⟩
      flat_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        exact ⟨0, by simp, by simp⟩
      gysin_naturality := by
        intro Y' g hY' hX' L t hL hXd iso _hiso hbase hisoProper k α
        exact ⟨0, 0, by simp, by simp, by simp⟩ }

/-- **Stacks 0ERJ.** The pointwise sum of two bivariant classes. -/
instance : Add (BivariantClassCanonical D sX hX sY hY f hf p) where
  add c d :=
    { cap := fun g hY' hX' k => c.cap g hY' hX' k + d.cap g hY' hX' k
      proper_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        obtain ⟨βc, hc1, hc2⟩ :=
          c.proper_naturality g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        obtain ⟨βd, hd1, hd2⟩ :=
          d.proper_naturality g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        exact ⟨βc + βd, by simp [hc1, hd1], by simp [hc2, hd2]⟩
      flat_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        obtain ⟨βc, hc1, hc2⟩ :=
          c.flat_naturality g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        obtain ⟨βd, hd1, hd2⟩ :=
          d.flat_naturality g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        exact ⟨βc + βd, by simp [hc1, hd1], by simp [hc2, hd2]⟩
      gysin_naturality := by
        intro Y' g hY' hX' L t hL hXd iso _hiso hbase hisoProper k α
        obtain ⟨βc, γc, hc1, hc2, hc3⟩ :=
          c.gysin_naturality g hY' hX' L t hL hXd iso _hiso hbase hisoProper k α
        obtain ⟨βd, γd, hd1, hd2, hd3⟩ :=
          d.gysin_naturality g hY' hX' L t hL hXd iso _hiso hbase hisoProper k α
        exact ⟨βc + βd, γc + γd, by simp [hc1, hd1], by simp [hc2, hd2],
          by simp [hc3, hd3]⟩ }

/-- **Stacks 0ERJ.** The pointwise negation of a bivariant class. -/
instance : Neg (BivariantClassCanonical D sX hX sY hY f hf p) where
  neg c :=
    { cap := fun g hY' hX' k => -c.cap g hY' hX' k
      proper_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        obtain ⟨βc, hc1, hc2⟩ :=
          c.proper_naturality g hY' hX' h hY'' hX'' hh h' _sq hfst hh' k α
        exact ⟨-βc, by simp [hc1], by simp [hc2]⟩
      flat_naturality := by
        intro Y' Y'' g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        obtain ⟨βc, hc1, hc2⟩ :=
          c.flat_naturality g hY' hX' h hY'' hX'' hh r hr h' _sq hfst hh' hr' k α
        exact ⟨-βc, by simp [hc1], by simp [hc2]⟩
      gysin_naturality := by
        intro Y' g hY' hX' L t hL hXd iso _hiso hbase hisoProper k α
        obtain ⟨βc, γc, hc1, hc2, hc3⟩ :=
          c.gysin_naturality g hY' hX' L t hL hXd iso _hiso hbase hisoProper k α
        exact ⟨-βc, -γc, by simp [hc1], by simp [hc2], by simp [hc3]⟩ }

/-- **Stacks 0ERJ.** The zero bivariant class caps to zero. -/
@[simp]
theorem BivariantClassCanonical.zero_cap {Y' : D.Ambient} (g : Y' ⟶ Y)
    (hY' : D.IsGood (g ≫ sY)) (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical D (g ≫ sY) hY' k) :
    (0 : BivariantClassCanonical D sX hX sY hY f hf p).cap g hY' hX' k α = 0 :=
  rfl

/-- **Stacks 0ERJ.** A sum of bivariant classes caps to the sum of their cap products. -/
@[simp]
theorem BivariantClassCanonical.add_cap (c d : BivariantClassCanonical D sX hX sY hY f hf p)
    {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical D (g ≫ sY) hY' k) :
    (c + d).cap g hY' hX' k α = c.cap g hY' hX' k α + d.cap g hY' hX' k α :=
  rfl

/-- **Stacks 0ERJ.** A negated bivariant class caps to the negated cap product. -/
@[simp]
theorem BivariantClassCanonical.neg_cap (c : BivariantClassCanonical D sX hX sY hY f hf p)
    {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical D (g ≫ sY) hY' k) :
    (-c).cap g hY' hX' k α = -c.cap g hY' hX' k α :=
  rfl

/-- **Stacks 0ERJ.** Bivariant classes of degree `p` for `f` form a commutative additive
monoid. -/
instance : AddCommMonoid (BivariantClassCanonical D sX hX sY hY f hf p) where
  add_assoc a b c := by ext; simp [_root_.add_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  add_comm a b := by
    ext
    simp only [BivariantClassCanonical.add_cap]
    exact _root_.add_comm _ _
  nsmul := nsmulRec

/-- **Stacks 0ERJ.** The difference of two bivariant classes. -/
instance : Sub (BivariantClassCanonical D sX hX sY hY f hf p) where
  sub a b := a + -b

/-- **Stacks 0ERJ.** The group `A^p(X ⟶ Y)` of bivariant classes of degree `p` for `f`. -/
instance : AddCommGroup (BivariantClassCanonical D sX hX sY hY f hf p) where
  toAddCommMonoid := inferInstance
  toNeg := inferInstance
  toSub := inferInstance
  neg_add_cancel a := by ext; simp
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec

/-- **Stacks 0ERJ.** A difference of bivariant classes caps to the difference of their cap
products. -/
@[simp]
theorem BivariantClassCanonical.sub_cap (c d : BivariantClassCanonical D sX hX sY hY f hf p)
    {Y' : D.Ambient} (g : Y' ⟶ Y) (hY' : D.IsGood (g ≫ sY))
    (hX' : D.IsGood (pullback.fst f g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical D (g ≫ sY) hY' k) :
    (c - d).cap g hY' hX' k α = c.cap g hY' hX' k α - d.cap g hY' hX' k α := by
  simp [sub_eq_add_neg]

/-! ### A Chow-group system with trivial Chow groups -/

/-- **A Chow-group system all of whose Chow groups are trivial.** Every cycle is declared
rationally equivalent to zero, so each `CH_k` is the quotient by `⊤`, and the three operations
are zero. -/
def trivialChowGroupSystem : ChowGroupSystem D where
  rationalEquivalences _ _ _ := ⊤
  properPushforward _ _ _ _ _ _ _ _ := 0
  flatPullback _ _ _ _ _ _ _ _ _ _ := 0
  IsGysinDatum _ _ _ := True
  gysin _ _ _ _ _ := 0

/-- Every Chow group of `AlgebraicGeometry.Space.trivialChowGroupSystem` is trivial. -/
theorem subsingleton_chow_trivialChowGroupSystem {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) :
    Subsingleton ((trivialChowGroupSystem D).chow sX hX k) :=
  QuotientAddGroup.subsingleton_iff.2 rfl

end AlgebraicGeometry.Space

end
