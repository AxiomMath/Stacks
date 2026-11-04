module

public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# Condition (RS*) from the comparison at thickening pushouts

`Deformation.Artin.SatisfiesRSStar` ([Stacks Project, Tag 07Y8]) quantifies over a square of the
big *affine* fppf site presented algebraically: a cartesian square of rings of global sections in
which one map is a surjection with square-zero kernel. The equivalence it asserts is a special
case of the one asserted for an arbitrary *geometric* thickening pushout in the big fppf site, so
condition (RS*) is a formal consequence of the latter.

This file records that implication, in three forms, each a hypothesis of the shape "the
comparison functor is an equivalence at every square of such-and-such a kind" and a conclusion of
condition (RS*). No tag is claimed: the hypothesis is the content.

The first form is the sharpest, and says what the reduction really needs. The squares that
condition (RS*) produces are very special: all four of their corners are affine, and the
thickening among them is of *first order*, its kernel ideal sheaf being square-zero rather than
merely nilpotent. So the comparison functor need only be known to be an equivalence at squares of
that kind — a strictly smaller assertion than the one made of an arbitrary thickening pushout
between arbitrary objects of the site.

Passing from the algebraic presentation of the square to its geometric one needs two facts about
affine schemes, both proved here:

* a morphism of affine schemes which is surjective on global sections with square-zero kernel is
  a first-order thickening — it is a closed immersion by
  `AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine`, and its kernel ideal sheaf is
  square-zero because over an affine scheme an ideal sheaf is determined by its ideal of global
  sections;
* a cartesian square of global sections of four affine schemes, one of whose maps is surjective,
  is a cocartesian square of schemes — this is [Stacks Project, Tag 0ET0]
  (`Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective`) transported along
  `AlgebraicGeometry.Scheme.isoSpec`.

In particular neither [Stacks Project, Tag 07RT] (the existence of the pushout along a thickening
and an affine morphism) nor [Stacks Project, Tag 06AD] (a thickening of an affine scheme is
affine) is needed: all four corners of the square of (RS*) are already affine, so Tag 0ET0 alone
identifies the fourth corner with the pushout.

## Main results

* `Deformation.Artin.isFirstOrderThickening_of_surjective_appTop` — the first fact above.
* `Deformation.Artin.isPushout_of_isPullback_appTop` — the second; this is observation (1) of
  the section [Stacks Project, Tag 0CXN], registered under that tag.
* `Deformation.Artin.surjective_and_ker_sq_eq_bot_of_isPullback` — in a cartesian square of
  commutative rings, surjectivity with square-zero kernel passes to the opposite map.
* `Deformation.Artin.isFirstOrderThickening_of_isPullback_appTop` — hence the morphism opposite
  to the thickening in such a square of affine schemes is a first-order thickening too.
* `Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair`
  — the implication from the sharpest hypothesis: the comparison is an equivalence at every
  pushout square of the site with affine corners along a *pair* of first-order thickenings, the
  thickening of the square and the morphism opposite to it.
* `Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine` — the
  same with the hypothesis asked for at squares in which only the thickening of the square is
  known to be of first order.
* `Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence` — the implication
  from the hypothesis at an arbitrary thickening pushout, for an arbitrary category fibred in
  groupoids over the big fppf site.
* `Deformation.Artin.satisfiesRSStar_of_isAlgebraicStack_of_fiberSquareComparison_isEquivalence` —
  the same with the hypothesis in the shape it is asserted of an algebraic stack, so that the
  (RS*) property of an algebraic stack is a single application of it.

## Implementation notes

Nothing in the first two implications uses the algebraic-stack condition, or indeed any property
of the fibred category beyond the assumed equivalence: their proofs only rewrite the algebraic
hypotheses of (RS*) as the geometric hypotheses of the assumed equivalence. The algebraic-stack
condition appears only in
`Deformation.Artin.satisfiesRSStar_of_isAlgebraicStack_of_fiberSquareComparison_isEquivalence`,
where it is part of the hypothesis being applied rather than of the reduction.

Each hypothesis carries the fibred-category instance used to form the chosen pullbacks as a
`letI` over `CategoryTheory.Functor.IsFiberedInGroupoids.isFibered` of the given witness.
`CategoryTheory.Functor.IsFibered` is a `Prop`, so this agrees with any other witness by proof
irrelevance and the hypothesis is insensitive to which one a consumer supplies.

Affineness of the corners is carried as an explicit hypothesis rather than an instance so that
the hypothesis can be stated for an arbitrary square of the site; `IsAffineHom` of the affine
morphism is then not asked for at all, being a consequence of affineness of its source and
target.

`Deformation.Artin.isFirstOrderThickening_of_surjective_appTop` and
`Deformation.Artin.isPushout_of_isPullback_appTop` are statements about affine schemes with no
deformation-theoretic content; they are kept here because this is their only consumer.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
* [Stacks Project, Tag 0CXN](https://stacks.math.columbia.edu/tag/0CXN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

/-- A morphism of affine schemes which is surjective on global sections with square-zero kernel
is a first-order thickening: it is a closed immersion, and its kernel ideal sheaf is square-zero
because over an affine scheme an ideal sheaf is determined by its ideal of global sections. -/
public theorem isFirstOrderThickening_of_surjective_appTop {U W : Scheme.{u}} [IsAffine U]
    [IsAffine W] (g : U ⟶ W) (hsurj : Function.Surjective g.appTop.hom)
    (hker : RingHom.ker g.appTop.hom ^ 2 = ⊥) :
    Stacks.Thickenings.IsFirstOrderThickening g := by
  have hci : IsClosedImmersion g := IsClosedImmersion.of_surjective_of_isAffine g hsurj
  refine ⟨hci, ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  simpa [AlgebraicGeometry.Scheme.ker_of_isAffine] using hker

/-- A cartesian square of global sections of four affine schemes, one of whose maps is surjective
on global sections, is a cocartesian square of schemes. This is [Stacks Project, Tag 0ET0]
transported along `AlgebraicGeometry.Scheme.isoSpec`. -/
@[stacks 0CXN "observation (1): Spec(A') = Spec(A) ⨿_{Spec(B)} Spec(B') in the category of \
schemes, for A' = A ×_B B' with B' → B surjective (the square-zero kernel is not needed)"]
public theorem isPushout_of_isPullback_appTop {U V W Z : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine W] [IsAffine Z]
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (hsq : IsPullback i.appTop j.appTop f.appTop g.appTop)
    (hsurj : Function.Surjective g.appTop.hom) : IsPushout f g i j :=
  (Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective
      g.appTop f.appTop i.appTop j.appTop hsq hsurj).flip.of_iso'
    U.isoSpec V.isoSpec W.isoSpec Z.isoSpec
    (Scheme.isoSpec_hom_naturality f) (Scheme.isoSpec_hom_naturality g)
    (Scheme.isoSpec_hom_naturality i) (Scheme.isoSpec_hom_naturality j)

/-- **In a cartesian square of commutative rings, surjectivity passes from one map to the
opposite one.** If `g : B ⟶ C` is surjective and the square with sides `p`, `q`, `f`, `g` is
cartesian, then `p : P ⟶ A` is surjective: an element of `A` is paired with a lift through `g` of
its image in `C`. -/
public theorem surjective_of_isPullback {P A B C : CommRingCat.{u}}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback p q f g)
    (hg : Function.Surjective g.hom) : Function.Surjective p.hom := fun a => by
  obtain ⟨b, hb⟩ := hg (f.hom a)
  obtain ⟨e, he, -⟩ := Types.exists_of_isPullback (h.map (forget CommRingCat.{u})) a b hb.symm
  exact ⟨e, he⟩

/-- **In a cartesian square of commutative rings, surjectivity and square-zero-ness of the
kernel pass from one map to the opposite one.** If `g : B ⟶ C` is surjective with square-zero
kernel and the square with sides `p`, `q`, `f`, `g` is cartesian, then `p : P ⟶ A` is surjective
with square-zero kernel.

Surjectivity lifts an element of `A` through `g` and pairs the two; the kernel of `p` is carried
into the kernel of `g` by `q`, so a product of two of its elements dies under both projections
and is therefore zero. Both steps read the cartesian square elementwise through the forgetful
functor to types, which preserves and reflects limits. -/
public theorem surjective_and_ker_sq_eq_bot_of_isPullback {P A B C : CommRingCat.{u}}
    {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback p q f g)
    (hg : Function.Surjective g.hom) (hker : RingHom.ker g.hom ^ 2 = ⊥) :
    Function.Surjective p.hom ∧ RingHom.ker p.hom ^ 2 = ⊥ := by
  have hT := h.map (forget CommRingCat.{u})
  refine ⟨surjective_of_isPullback h hg, le_antisymm ?_ bot_le⟩
  · rw [pow_two]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    rw [RingHom.mem_ker] at hx hy
    have hmem : ∀ z, p.hom z = 0 → q.hom z ∈ RingHom.ker g.hom := fun z hz => by
      rw [RingHom.mem_ker, ← CommRingCat.comp_apply, ← h.w, CommRingCat.comp_apply, hz, map_zero]
    have hq : q.hom (x * y) = 0 := by
      have hm : q.hom x * q.hom y ∈ RingHom.ker g.hom ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul (hmem x hx) (hmem y hy)
      rw [hker] at hm
      rw [map_mul]
      exact hm
    have hp : p.hom (x * y) = 0 := by rw [map_mul, hx, zero_mul]
    have hz := Types.ext_of_isPullback hT (x₁ := x * y) (y₁ := 0)
      (by simpa using hp) (by simpa using hq)
    simpa using hz

/-- **The leg of an affine thickening pushout opposite to the thickening is a first-order
thickening too.** For a cartesian square of global sections of four affine schemes in which
`g` is surjective with square-zero kernel, the opposite morphism `i` is a first-order
thickening.

Only affineness of the source and target of `i` is used:
`Deformation.Artin.surjective_and_ker_sq_eq_bot_of_isPullback` moves the two algebraic
properties across the cartesian square, and
`Deformation.Artin.isFirstOrderThickening_of_surjective_appTop` reads them geometrically. -/
public theorem isFirstOrderThickening_of_isPullback_appTop {U V W Z : Scheme.{u}}
    [IsAffine V] [IsAffine Z] (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (hsq : IsPullback i.appTop j.appTop f.appTop g.appTop)
    (hsurj : Function.Surjective g.appTop.hom)
    (hker : RingHom.ker g.appTop.hom ^ 2 = ⊥) :
    Stacks.Thickenings.IsFirstOrderThickening i :=
  have h := surjective_and_ker_sq_eq_bot_of_isPullback hsq hsurj hker
  isFirstOrderThickening_of_surjective_appTop i h.1 h.2

/-- **Condition (RS*) holds as soon as the comparison functor is an equivalence at every pushout
square with affine corners along a pair of first-order thickenings.** Let `p` be a category
fibred in groupoids over the big fppf site of `S`. Suppose that for every commutative square
`i ≫ a = f ≫ b` of the site whose four corners have affine underlying scheme, whose image in
schemes is a pushout, and in which *both* `i` and `b` become first-order thickenings, the
comparison `Deformation.Artin.fiberSquareComparison` is an equivalence. Then `p` satisfies
condition (RS*) of [Stacks Project, Tag 07Y8].

This is the sharpest implication of this file. The squares condition (RS*) quantifies over have
all four corners affine; the surjection with square-zero kernel they carry becomes a thickening
of *first order*; and so does the morphism opposite to it, by
`Deformation.Artin.isFirstOrderThickening_of_isPullback_appTop`. So no more than this is ever
used. -/
public theorem satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒜 : Type v} [Category.{w} 𝒜] (p : 𝒜 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hcomp :
      letI : p.IsFibered := hp.isFibered
      ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y')
        (b : Y ⟶ Y') (w : i ≫ a = f ≫ b),
        IsAffine ((BigFppfOver.toScheme B S hS).obj X) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj X') →
        IsAffine ((BigFppfOver.toScheme B S hS).obj Y) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj Y') →
        Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
        Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map b) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          (fiberSquareComparison p (Functor.chosenPullbacks p) f i b a w.symm).IsEquivalence) :
    SatisfiesRSStar B S hS p hp := by
  let _ : p.IsFibered := hp.isFibered
  intro U V W Z f g i j hcomm hsq hsurj hker
  have hU : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj U)) := U.property
  have hV : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  have hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj W)) := W.property
  have hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  have hw : (BigAffineFppf.inclusion B S hS).map g ≫ (BigAffineFppf.inclusion B S hS).map j =
      (BigAffineFppf.inclusion B S hS).map f ≫ (BigAffineFppf.inclusion B S hS).map i := by
    simpa only [Functor.map_comp] using
      (congrArg (BigAffineFppf.inclusion B S hS).map hcomm).symm
  have hfirst : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map g)) :=
    isFirstOrderThickening_of_surjective_appTop _ hsurj hker
  have hfirstb : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map i)) :=
    isFirstOrderThickening_of_isPullback_appTop _ _ _ _ hsq hsurj hker
  have hpush : IsPushout
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map f))
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map g))
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map i))
      ((BigFppfOver.toScheme B S hS).map ((BigAffineFppf.inclusion B S hS).map j)) :=
    isPushout_of_isPullback_appTop _ _ _ _ hsq hsurj
  exact hcomp ((BigAffineFppf.inclusion B S hS).map g)
    ((BigAffineFppf.inclusion B S hS).map f) ((BigAffineFppf.inclusion B S hS).map j)
    ((BigAffineFppf.inclusion B S hS).map i) hw hU hW hV hZ hfirst hfirstb hpush.flip

/-- **Condition (RS*) holds as soon as the comparison functor is an equivalence at every pushout
square with affine corners along a first-order thickening.** Let `p` be a category fibred in
groupoids over the big fppf site of `S`. Suppose that for every commutative square
`i ≫ a = f ≫ b` of the site whose four corners have affine underlying scheme, whose image in
schemes is a pushout, and in which `i` becomes a first-order thickening, the comparison
`Deformation.Artin.fiberSquareComparison` is an equivalence. Then `p` satisfies condition (RS*)
of [Stacks Project, Tag 07Y8].

This is
`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair`
with its hypothesis asked for at squares in which only the thickening `i` is known to be of
first order. -/
public theorem satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒜 : Type v} [Category.{w} 𝒜] (p : 𝒜 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hcomp :
      letI : p.IsFibered := hp.isFibered
      ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y')
        (b : Y ⟶ Y') (w : i ≫ a = f ≫ b),
        IsAffine ((BigFppfOver.toScheme B S hS).obj X) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj X') →
        IsAffine ((BigFppfOver.toScheme B S hS).obj Y) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj Y') →
        Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          (fiberSquareComparison p (Functor.chosenPullbacks p) f i b a w.symm).IsEquivalence) :
    SatisfiesRSStar B S hS p hp :=
  satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair B S hS p hp
    fun i f a b w hX hX' hY hY' hfirst _hfirstb hpush =>
      hcomp i f a b w hX hX' hY hY' hfirst hpush

/-- **Condition (RS*) holds as soon as the comparison functor at every thickening pushout is an
equivalence.** Let `p` be a category fibred in groupoids over the big fppf site of `S`. Suppose
that for every commutative square `i ≫ a = f ≫ b` of the site whose image in schemes is a
pushout along the thickening `i` and the affine morphism `f`, the comparison
`Deformation.Artin.fiberSquareComparison` is an equivalence. Then `p` satisfies condition (RS*)
of [Stacks Project, Tag 07Y8].

This is
`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine` with its
hypothesis weakened to the one asserted at an arbitrary thickening pushout: a first-order
thickening is a thickening, and a morphism of affine schemes is affine. -/
public theorem satisfiesRSStar_of_fiberSquareComparison_isEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒜 : Type v} [Category.{w} 𝒜] (p : 𝒜 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (hcomp :
      letI : p.IsFibered := hp.isFibered
      ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y')
        (b : Y ⟶ Y') (w : i ≫ a = f ≫ b),
        Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
        IsAffineHom ((BigFppfOver.toScheme B S hS).map f) →
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          (fiberSquareComparison p (Functor.chosenPullbacks p) f i b a w.symm).IsEquivalence) :
    SatisfiesRSStar B S hS p hp :=
  satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine B S hS p hp
    fun i f a b w _hX _hX' _hY _hY' hfirst hpush =>
      hcomp i f a b w hfirst.isThickening inferInstance hpush

/-- **Condition (RS*) for a fibred category whose comparison functor at every thickening pushout
is an equivalence, with the hypothesis in the shape it is asserted of an algebraic stack.** The
hypothesis quantifies over every based category over the site satisfying
`AlgebraicGeometry.Stack.IsAlgebraicStack`, and is applied to the one at hand; the conclusion is
condition (RS*) of [Stacks Project, Tag 07Y8] for every witness of the fibred-in-groupoids
property.

This is `Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence` with its
hypothesis supplied by that assertion. Nothing beyond the assertion is used: the
algebraic-stack condition enters only as the assertion's own hypothesis. -/
public theorem satisfiesRSStar_of_isAlgebraicStack_of_fiberSquareComparison_isEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hcomp : ∀ {X X' Y Y' : BigFppfOver B S hS}
      (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i) →
      ∀ [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)],
        IsPushout ((BigFppfOver.toScheme B S hS).map i)
            ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map a)
            ((BigFppfOver.toScheme B S hS).map b) →
          ∀ (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
            (h𝒵 : AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒵),
            letI : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
            (fiberSquareComparison 𝒵.p (Functor.chosenPullbacks 𝒵.p)
              f i b a w.symm).IsEquivalence)
    (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒳 : AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒳)
    (hp : 𝒳.p.IsFiberedInGroupoids) :
    SatisfiesRSStar B S hS 𝒳.p hp :=
  satisfiesRSStar_of_fiberSquareComparison_isEquivalence B S hS 𝒳.p hp
    fun i f a b w hi _hf hsq => hcomp i f a b w hi hsq 𝒳 h𝒳

end Deformation.Artin

end
