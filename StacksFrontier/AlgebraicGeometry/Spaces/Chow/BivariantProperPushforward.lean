module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Proper pushforward of a bivariant class for good algebraic spaces

In the base situation of Stacks 0EDT let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of good
algebraic spaces over the base space `B`, let `f` be proper and let `c ∈ A^p(X ⟶ Z)`. Stacks
0ERQ asserts that the rule sending a good test space `q : Z' ⟶ Z` over `B` and a class
`α ∈ CH_k(Z')` to

  `f'_*(c ∩ α) ∈ CH_{k-p}(Z' ×_Z Y)`,

where `f' : Z' ×_Z X ⟶ Z' ×_Z Y` is the base change of `f`, is again a bivariant class of
degree `p`, that is, an element of `A^p(Y ⟶ Z)`.

This file supplies the base change and the rule, and everything about the rule that does not depend
on the three naturality engines of the source proof: the base change of `f` is proper, so the
rule is defined; the rule satisfies the proper-pushforward condition of Stacks 0ERJ, which is
part of the source proof carried by Stacks 0EP2; and the rule determines the pushed-forward
class uniquely.

## Main definitions

* `AlgebraicGeometry.Space.bivariantPushforwardBaseChange` — the base change
  `Z' ×_Z X ⟶ Z' ×_Z Y` of `f` along a test space `q : Z' ⟶ Z`.
* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.HasGoodBivariantPullbacks` — goodness
  over the base of the fibre products `Z' ×_Z X`, for every good test space `Z' ⟶ Z`.
* `AlgebraicGeometry.Space.ChowGroupSystem.HasFunctorialProperPushforward` — Stacks 0EP2 as a
  property of the parameterized Chow-group system: proper pushforward along a composite is the
  composite of the proper pushforwards.
* `AlgebraicGeometry.Space.bivariantProperPushforwardCap` — the cap operation
  `α ↦ f'_*(c ∩ α)` of the pushed-forward class.
* `AlgebraicGeometry.Space.IsBivariantProperPushforward` — the assertion that a bivariant class
  of degree `p` for `g` caps by that rule, which is the defining property of the pushforward.

## Main results

* `AlgebraicGeometry.Space.isPullback_bivariantPushforwardBaseChange` — the square exhibiting
  `Z' ×_Z X ⟶ Z' ×_Z Y` as a base change of `f`, whence
  `AlgebraicGeometry.Space.isProper_bivariantPushforwardBaseChange`: that base change is proper.
* `AlgebraicGeometry.Space.isPullback_bivariantBaseChangeMap` and
  `AlgebraicGeometry.Space.isProper_bivariantBaseChangeMap` — the same for the base-change map
  of test spaces `AlgebraicGeometry.Space.bivariantBaseChangeMap`.
* `AlgebraicGeometry.Space.properPushforward_square` — in a commuting square of proper
  morphisms of good algebraic spaces over the base, the two composite proper pushforwards on
  Chow groups agree.
* `AlgebraicGeometry.Space.bivariantProperPushforwardCap_proper_naturality` — **the
  proper-pushforward condition of Stacks 0ERJ for the rule of Stacks 0ERQ**.
* `AlgebraicGeometry.Space.eq_of_isBivariantProperPushforward` — **uniqueness**: two bivariant
  classes satisfying the rule for the same `c` are equal.

## Implementation notes

### The two hypotheses the rule needs

A bivariant class for `g : Y ⟶ Z` caps on every good test space `q : Z' ⟶ Z`, and writing the
rule down asks for two things at each of them which chapter 82 has and this repository does
not.

The first is goodness over the base of the fibre product `Z' ×_Z X`, which is the source of the
pushforward. Goodness of a fibre product of good algebraic spaces is not available here — it is
a hypothesis of the cap operation of `AlgebraicGeometry.Space.BivariantClass` itself — and the
cap operation quantifies over the test space, so the goodness cannot be an argument of the rule
at a single test space. It is therefore quantified once and for all, as
`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.HasGoodBivariantPullbacks`.

The second is Stacks 0EP2, functoriality of proper pushforward, which is what makes the
proper-pushforward condition hold for the rule. The Chow groups and their proper pushforward
are a parameter here, `AlgebraicGeometry.Space.ChowGroupSystem`, and that structure carries no
compatibilities at all; so functoriality is a hypothesis on the system,
`AlgebraicGeometry.Space.ChowGroupSystem.HasFunctorialProperPushforward`. It is a hypothesis of
the enclosing theorem and deliberately not part of
`AlgebraicGeometry.Space.IsBivariantProperPushforward`: inside, it would weaken the
characterization and the uniqueness statement with it.

Properness of the base change of `f`, on the other hand, is *not* a hypothesis. Properness of
morphisms of algebraic spaces is stable under base change by Stacks 04WP,
`AlgebraicGeometry.Space.isProper_isStableUnderBaseChange`, and stable under composition by
Stacks 04XY, `AlgebraicGeometry.Space.isProper_comp'`; both are available here. Each is stated
on the category of algebraic spaces over the base scheme of Stacks 02X2, so a cartesian square
of presheaves whose four corners are algebraic spaces is transported into that full
subcategory, which is where the algebraicity hypotheses below come from.

### What the rule is, and what is still missing

No transport of degrees is needed: a class of degree `p` for `f ≫ g` and one of degree `p` for
`g` both cap `CH_k(Z')` into degree `k - p`, and proper pushforward preserves the degree. So
`AlgebraicGeometry.Space.IsBivariantProperPushforward` is an equality of Chow classes rather
than a heterogeneous equality and uniqueness is immediate from
`AlgebraicGeometry.Space.BivariantClass.ext`.

Constructing the pushed-forward class is therefore exactly filling the three naturality fields
of `AlgebraicGeometry.Space.BivariantClass` for
`AlgebraicGeometry.Space.bivariantProperPushforwardCap`. The source proof of Stacks 0ERQ
invokes Stacks 0EP2, 0EPD and 0ER5, one for each field, and only the first is reachable here:

* **Proper** (Stacks 0EP2). Done, from the functoriality hypothesis above:
  `AlgebraicGeometry.Space.bivariantProperPushforwardCap_proper_naturality`. The two base
  changes of `f`, over `Z'` and over `Z''`, and the two base changes of the proper test
  morphism `h : Z'' ⟶ Z'`, over `X` and over `Y`, form a commuting square of proper morphisms,
  and functoriality traverses it both ways.
* **Flat** (Stacks 0EPD). Not done: the condition asks flat pullback to commute with proper
  pushforward in the cartesian square formed by the two base changes of `f` and the two flat
  base changes of the test morphism. That is a second compatibility of the parameterized
  system, independent of functoriality, and the condition is a heterogeneous equality of
  classes in the two spellings `(k + r) - p` and `(k - p) + r` of one degree.
* **Gysin** (Stacks 0ER5). Not done, and blocked for a structural reason. The condition of
  Stacks 0ERJ for the pushed-forward class hands one identification of the base change of a
  vanishing locus with the vanishing locus of a pulled-back section, that on the `Y`-side;
  invoking the condition for `c` needs the one on the `X`-side, and that is data — a
  `AlgebraicGeometry.Space.GysinDatum` on `Z' ×_Z X` together with an isomorphism — which the
  `Y`-side identification does not produce and which nothing in scope supplies.

So no declaration below carries the bare tag: Stacks 0ERQ says that the rule *is* a bivariant
class, and that existence is not proved here. The declarations which do carry the tag name the
part of the lemma they discharge.

## References

* [Stacks Project, Tag 0ERQ](https://stacks.math.columbia.edu/tag/0ERQ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The base change of the proper morphism -/

/-- The base change `Z' ×_Z X ⟶ Z' ×_Z Y` of `f : X ⟶ Y` along a test space `q : Z' ⟶ Z`, for a
composable pair `f : X ⟶ Y`, `g : Y ⟶ Z` of morphisms of the ambient category. -/
def bivariantPushforwardBaseChange (D : BaseSpaceDimensionSituation.{u}) {X Y Z Z' : D.Ambient}
    (f : X ⟶ Y) (g : Y ⟶ Z) (q : Z' ⟶ Z) : pullback (f ≫ g) q ⟶ pullback g q :=
  pullback.map (f ≫ g) q g q f (𝟙 Z') (𝟙 Z) (by simp) (by simp)

/-- The base change of `f` is compatible with the projections to `X` and to `Y`. -/
@[reassoc (attr := simp)]
theorem bivariantPushforwardBaseChange_fst (D : BaseSpaceDimensionSituation.{u})
    {X Y Z Z' : D.Ambient} (f : X ⟶ Y) (g : Y ⟶ Z) (q : Z' ⟶ Z) :
    bivariantPushforwardBaseChange D f g q ≫ pullback.fst g q =
      pullback.fst (f ≫ g) q ≫ f :=
  pullback.lift_fst _ _ _

/-- The base change of `f` is a morphism over the test space. -/
@[reassoc (attr := simp)]
theorem bivariantPushforwardBaseChange_snd (D : BaseSpaceDimensionSituation.{u})
    {X Y Z Z' : D.Ambient} (f : X ⟶ Y) (g : Y ⟶ Z) (q : Z' ⟶ Z) :
    bivariantPushforwardBaseChange D f g q ≫ pullback.snd g q = pullback.snd (f ≫ g) q :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The base change of `f` along a test space is a morphism over the base. -/
theorem bivariantPushforwardBaseChange_comp_structure (D : BaseSpaceDimensionSituation.{u})
    {X Y Z Z' : D.Ambient} {sX : X ⟶ D.space} {sY : Y ⟶ D.space} {f : X ⟶ Y}
    (hf : f ≫ sY = sX) (g : Y ⟶ Z) (q : Z' ⟶ Z) :
    bivariantPushforwardBaseChange D f g q ≫ (pullback.fst g q ≫ sY) =
      pullback.fst (f ≫ g) q ≫ sX := by
  rw [← Category.assoc, bivariantPushforwardBaseChange_fst, Category.assoc, hf]

/-- The base change `Z' ×_Z X ⟶ Z' ×_Z Y` of `f` along a test space `q : Z' ⟶ Z` is a base
change of `f` in the strict sense: it sits in a cartesian square over `f`, the vertical legs
being the projections to `X` and to `Y`. -/
theorem isPullback_bivariantPushforwardBaseChange (D : BaseSpaceDimensionSituation.{u})
    {X Y Z Z' : D.Ambient} (f : X ⟶ Y) (g : Y ⟶ Z) (q : Z' ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) q) (bivariantPushforwardBaseChange D f g q) f
      (pullback.fst g q) :=
  .of_bot (by rw [bivariantPushforwardBaseChange_snd]; exact .of_hasPullback (f ≫ g) q)
    (bivariantPushforwardBaseChange_fst D f g q).symm (.of_hasPullback g q)

/-- A cartesian square of presheaves on the big fppf site whose four corners are algebraic
spaces over the base is cartesian in the category of algebraic spaces of Stacks 02X2, the
inclusion of that full subcategory being fully faithful. -/
theorem isPullback_algebraicSpaces (D : BaseSpaceDimensionSituation.{u}) {P A B C : D.Ambient}
    {a : P ⟶ A} {b : P ⟶ B} {u : A ⟶ C} {v : B ⟶ C} (hP : IsAlgebraicSpace D.site D.base
      D.base_mem P) (hA : IsAlgebraicSpace D.site D.base D.base_mem A)
    (hB : IsAlgebraicSpace D.site D.base D.base_mem B)
    (hC : IsAlgebraicSpace D.site D.base D.base_mem C) (sq : IsPullback a b u v) :
    IsPullback (ObjectProperty.homMk a : (⟨P, hP⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨A, hA⟩)
      (ObjectProperty.homMk b : (⟨P, hP⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨B, hB⟩)
      (ObjectProperty.homMk u : (⟨A, hA⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨C, hC⟩)
      (ObjectProperty.homMk v : (⟨B, hB⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨C, hC⟩) :=
  IsPullback.of_map_of_faithful
    (ObjectProperty.ι (fun F : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace D.site D.base D.base_mem F)) sq

/-- **Stacks 0ERQ.** The base change of a proper morphism along a test space is proper, so the
rule of Stacks 0ERQ has a proper morphism to push forward along. -/
@[stacks 0ERQ "properness of the base change of the proper morphism, so that the rule \
is defined"]
theorem isProper_bivariantPushforwardBaseChange (D : BaseSpaceDimensionSituation.{u})
    {X Y Z Z' : D.Ambient} (f : X ⟶ Y) (g : Y ⟶ Z) (q : Z' ⟶ Z)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hPX : IsAlgebraicSpace D.site D.base D.base_mem (pullback (f ≫ g) q))
    (hPY : IsAlgebraicSpace D.site D.base D.base_mem (pullback g q))
    (hf : IsProper D.site D.base D.base_mem f) :
    IsProper D.site D.base D.base_mem (bivariantPushforwardBaseChange D f g q) :=
  (isProper_isStableUnderBaseChange D.site D.base D.base_mem).of_isPullback
    (isPullback_algebraicSpaces D hPX hX hPY hY
      (isPullback_bivariantPushforwardBaseChange D f g q)) hf

/-- The base-change map of test spaces is compatible with the projections to `X`. -/
private theorem bivariantBaseChangeMap_fst (D : BaseSpaceDimensionSituation.{u})
    {X Y Y' Y'' : D.Ambient} (f : X ⟶ Y) (g : Y' ⟶ Y) (h : Y'' ⟶ Y') :
    bivariantBaseChangeMap D f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The base-change map of test spaces `Y'' ×_Y X ⟶ Y' ×_Y X` sits in a cartesian square over
`h : Y'' ⟶ Y'`, the vertical legs being the projections to the test spaces. -/
theorem isPullback_bivariantBaseChangeMap (D : BaseSpaceDimensionSituation.{u})
    {X Y Y' Y'' : D.Ambient} (f : X ⟶ Y) (g : Y' ⟶ Y) (h : Y'' ⟶ Y') :
    IsPullback (pullback.snd f (h ≫ g)) (bivariantBaseChangeMap D f g h) h
      (pullback.snd f g) := by
  exact .of_bot
    (by rw [bivariantBaseChangeMap_fst]; exact (IsPullback.of_hasPullback f (h ≫ g)).flip)
    (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback f g).flip

/-- The base-change map of test spaces is proper as soon as the morphism of test spaces is. -/
theorem isProper_bivariantBaseChangeMap (D : BaseSpaceDimensionSituation.{u})
    {X Y Y' Y'' : D.Ambient} (f : X ⟶ Y) (g : Y' ⟶ Y) (h : Y'' ⟶ Y')
    (hY' : IsAlgebraicSpace D.site D.base D.base_mem Y')
    (hY'' : IsAlgebraicSpace D.site D.base D.base_mem Y'')
    (hP : IsAlgebraicSpace D.site D.base D.base_mem (pullback f g))
    (hP' : IsAlgebraicSpace D.site D.base D.base_mem (pullback f (h ≫ g)))
    (hh : IsProper D.site D.base D.base_mem h) :
    IsProper D.site D.base D.base_mem (bivariantBaseChangeMap D f g h) :=
  (isProper_isStableUnderBaseChange D.site D.base D.base_mem).of_isPullback
    (isPullback_algebraicSpaces D hP' hY'' hP hY' (isPullback_bivariantBaseChangeMap D f g h)) hh

/-! ### The two hypotheses the rule needs -/

/-- Goodness over the base of the fibre products the rule of Stacks 0ERQ pushes forward from:
for every good test space `q : Z' ⟶ Z` over the base, the fibre product `Z' ×_Z X` is again
good over the base. Goodness of a fibre product of good algebraic spaces is not available in
this repository; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantProperPushforward`. -/
def BaseSpaceDimensionSituation.HasGoodBivariantPullbacks
    (D : BaseSpaceDimensionSituation.{u}) {X Y Z : D.Ambient} (sX : X ⟶ D.space)
    (sZ : Z ⟶ D.space) (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∀ {Z' : D.Ambient} (q : Z' ⟶ Z), D.IsGood (q ≫ sZ) →
    D.IsGood (pullback.fst (f ≫ g) q ≫ sX)

/-- **Stacks 0EP2 as a property of a parameterized Chow-group system:** proper pushforward
along a composite of proper morphisms of good algebraic spaces over the base is the composite
of the proper pushforwards. The composite is presented as an arbitrary morphism together with a
proof that it equals the composite, so that the statement can be applied to a morphism which is
only known to factor. -/
def ChowGroupSystem.HasFunctorialProperPushforward {D : BaseSpaceDimensionSituation.{u}}
    (G : ChowGroupSystem D) : Prop :=
  ∀ {A B C : D.Ambient} (sA : A ⟶ D.space) (hA : D.IsGood sA) (sB : B ⟶ D.space)
    (hB : D.IsGood sB) (sC : C ⟶ D.space) (hC : D.IsGood sC) (a : A ⟶ B) (b : B ⟶ C)
    (m : A ⟶ C) (_hm : m = a ≫ b) (ha : a ≫ sB = sA) (hb : b ≫ sC = sB) (hm' : m ≫ sC = sA)
    (hpa : IsProper D.site D.base D.base_mem a) (hpb : IsProper D.site D.base D.base_mem b)
    (hpm : IsProper D.site D.base D.base_mem m) (k : ℤ) (α : G.chow sA hA k),
    G.properPushforward sB hB sC hC b hb hpb k (G.properPushforward sA hA sB hB a ha hpa k α) =
      G.properPushforward sA hA sC hC m hm' hpm k α

/-- In a commuting square of proper morphisms of good algebraic spaces over the base, the two
composite proper pushforwards on Chow groups agree: both are the pushforward along the common
composite, by functoriality. -/
theorem properPushforward_square (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D)
    (hfun : G.HasFunctorialProperPushforward) {A B E F : D.Ambient} (sA : A ⟶ D.space)
    (hA : D.IsGood sA) (sB : B ⟶ D.space) (hB : D.IsGood sB) (sE : E ⟶ D.space)
    (hE : D.IsGood sE) (sF : F ⟶ D.space) (hF : D.IsGood sF) (u : A ⟶ B) (v : B ⟶ F)
    (w : A ⟶ E) (z : E ⟶ F) (hsq : u ≫ v = w ≫ z) (hu : u ≫ sB = sA) (hv : v ≫ sF = sB)
    (hw : w ≫ sE = sA) (hz : z ≫ sF = sE) (hpu : IsProper D.site D.base D.base_mem u)
    (hpv : IsProper D.site D.base D.base_mem v) (hpw : IsProper D.site D.base D.base_mem w)
    (hpz : IsProper D.site D.base D.base_mem z) (k : ℤ) (α : G.chow sA hA k) :
    G.properPushforward sB hB sF hF v hv hpv k (G.properPushforward sA hA sB hB u hu hpu k α) =
      G.properPushforward sE hE sF hF z hz hpz k
        (G.properPushforward sA hA sE hE w hw hpw k α) := by
  have hcomp : (u ≫ v) ≫ sF = sA := by rw [Category.assoc, hv, hu]
  have hpc : IsProper D.site D.base D.base_mem (u ≫ v) :=
    isProper_comp' D.site D.base D.base_mem u v hB.1 hF.1 hpu hpv
  rw [hfun sA hA sB hB sF hF u v (u ≫ v) rfl hu hv hcomp hpu hpv hpc k α,
    hfun sA hA sE hE sF hF w z (u ≫ v) hsq hw hz hcomp hpw hpz hpc k α]

/-! ### The cap operation of the pushed-forward class -/

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D) {X Y Z : D.Ambient}
  (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
  (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f ≫ sY = sX)
  (hfg : (f ≫ g) ≫ sZ = sX) (hproper : IsProper D.site D.base D.base_mem f)
  (hgood : D.HasGoodBivariantPullbacks sX sZ f g) (p : ℤ)
  (c : BivariantClass D G sX hX sZ hZ (f ≫ g) hfg p)

/-- **Stacks 0ERQ.** The cap operation of the proper pushforward of a bivariant class `c` for
`f ≫ g` along the proper morphism `f`: cap with `c`, then push forward along the base change of
`f` to the test space. -/
def bivariantProperPushforwardCap {Z' : D.Ambient} (q : Z' ⟶ Z) (hZ' : D.IsGood (q ≫ sZ))
    (hY' : D.IsGood (pullback.fst g q ≫ sY)) (k : ℤ) :
    G.chow (q ≫ sZ) hZ' k →+ G.chow (pullback.fst g q ≫ sY) hY' (k - p) :=
  (G.properPushforward (pullback.fst (f ≫ g) q ≫ sX) (hgood q hZ')
      (pullback.fst g q ≫ sY) hY' (bivariantPushforwardBaseChange D f g q)
      (bivariantPushforwardBaseChange_comp_structure D hf g q)
      (isProper_bivariantPushforwardBaseChange D f g q hX.1 hY.1 (hgood q hZ').1 hY'.1 hproper)
      (k - p)).comp
    (c.cap q hZ' (hgood q hZ') k)

/-- The cap operation of the proper pushforward, read on an element. -/
theorem bivariantProperPushforwardCap_apply {Z' : D.Ambient} (q : Z' ⟶ Z)
    (hZ' : D.IsGood (q ≫ sZ)) (hY' : D.IsGood (pullback.fst g q ≫ sY)) (k : ℤ)
    (α : G.chow (q ≫ sZ) hZ' k) :
    bivariantProperPushforwardCap D G sX hX sY hY sZ hZ f g hf hfg hproper hgood p c q hZ'
        hY' k α =
      G.properPushforward (pullback.fst (f ≫ g) q ≫ sX) (hgood q hZ')
        (pullback.fst g q ≫ sY) hY' (bivariantPushforwardBaseChange D f g q)
        (bivariantPushforwardBaseChange_comp_structure D hf g q)
        (isProper_bivariantPushforwardBaseChange D f g q hX.1 hY.1 (hgood q hZ').1 hY'.1
          hproper)
        (k - p) (c.cap q hZ' (hgood q hZ') k α) :=
  rfl

/-- **Stacks 0ERQ.** The proper-pushforward condition of Stacks 0ERJ for the rule of 0ERQ:
the cap operation `α ↦ f'_*(c ∩ α)` commutes with proper pushforward along a morphism of good
test spaces over `Z`. This is the part of the source proof carried by Stacks 0EP2, which enters
as functoriality of the parameterized proper pushforward. -/
@[stacks 0ERQ "the proper-pushforward condition of Stacks 0ERJ for the rule, over \
functoriality of the parameterized proper pushforward"]
theorem bivariantProperPushforwardCap_proper_naturality
    (hfun : G.HasFunctorialProperPushforward) {Z' Z'' : D.Ambient} (q : Z' ⟶ Z)
    (hZ' : D.IsGood (q ≫ sZ)) (hY' : D.IsGood (pullback.fst g q ≫ sY)) (h : Z'' ⟶ Z')
    (hZ'' : D.IsGood ((h ≫ q) ≫ sZ)) (hY'' : D.IsGood (pullback.fst g (h ≫ q) ≫ sY))
    (hh : IsProper D.site D.base D.base_mem h) (h' : pullback g (h ≫ q) ⟶ pullback g q)
    (hsq : IsPullback (pullback.snd g (h ≫ q)) h' h (pullback.snd g q))
    (hfst : h' ≫ pullback.fst g q = pullback.fst g (h ≫ q))
    (hh' : IsProper D.site D.base D.base_mem h') (k : ℤ)
    (α : G.chow ((h ≫ q) ≫ sZ) hZ'' k) :
    bivariantProperPushforwardCap D G sX hX sY hY sZ hZ f g hf hfg hproper hgood p c q hZ'
        hY' k
        (G.properPushforward ((h ≫ q) ≫ sZ) hZ'' (q ≫ sZ) hZ' h (Category.assoc h q sZ).symm
          hh k α) =
      G.properPushforward (pullback.fst g (h ≫ q) ≫ sY) hY'' (pullback.fst g q ≫ sY) hY' h'
        (by rw [← Category.assoc, hfst]) hh' (k - p)
        (bivariantProperPushforwardCap D G sX hX sY hY sZ hZ f g hf hfg hproper hgood p c
          (h ≫ q) hZ'' hY'' k α) := by
  have hmfst : bivariantBaseChangeMap D (f ≫ g) q h ≫ pullback.fst (f ≫ g) q =
      pullback.fst (f ≫ g) (h ≫ q) :=
    bivariantBaseChangeMap_fst D (f ≫ g) q h
  have hmsq : IsPullback (pullback.snd (f ≫ g) (h ≫ q))
      (bivariantBaseChangeMap D (f ≫ g) q h) h (pullback.snd (f ≫ g) q) :=
    isPullback_bivariantBaseChangeMap D (f ≫ g) q h
  have hmproper : IsProper D.site D.base D.base_mem (bivariantBaseChangeMap D (f ≫ g) q h) :=
    isProper_bivariantBaseChangeMap D (f ≫ g) q h hZ'.1 hZ''.1 (hgood q hZ').1
      (hgood (h ≫ q) hZ'').1 hh
  have hsquare : bivariantBaseChangeMap D (f ≫ g) q h ≫ bivariantPushforwardBaseChange D f g q =
      bivariantPushforwardBaseChange D f g (h ≫ q) ≫ h' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc, hmfst,
        Category.assoc, hfst, bivariantPushforwardBaseChange_fst]
    · rw [Category.assoc, bivariantPushforwardBaseChange_snd, Category.assoc, ← hsq.w,
        bivariantPushforwardBaseChange_snd_assoc, hmsq.w]
  rw [bivariantProperPushforwardCap_apply, bivariantProperPushforwardCap_apply,
    c.proper_naturality q hZ' (hgood q hZ') h hZ'' (hgood (h ≫ q) hZ'') hh
      (bivariantBaseChangeMap D (f ≫ g) q h) hmsq hmfst hmproper k α]
  exact properPushforward_square D G hfun (pullback.fst (f ≫ g) (h ≫ q) ≫ sX)
    (hgood (h ≫ q) hZ'') (pullback.fst (f ≫ g) q ≫ sX) (hgood q hZ')
    (pullback.fst g (h ≫ q) ≫ sY) hY'' (pullback.fst g q ≫ sY) hY'
    (bivariantBaseChangeMap D (f ≫ g) q h) (bivariantPushforwardBaseChange D f g q)
    (bivariantPushforwardBaseChange D f g (h ≫ q)) h' hsquare
    (by rw [← Category.assoc, hmfst])
    (bivariantPushforwardBaseChange_comp_structure D hf g q)
    (bivariantPushforwardBaseChange_comp_structure D hf g (h ≫ q))
    (by rw [← Category.assoc, hfst]) hmproper
    (isProper_bivariantPushforwardBaseChange D f g q hX.1 hY.1 (hgood q hZ').1 hY'.1 hproper)
    (isProper_bivariantPushforwardBaseChange D f g (h ≫ q) hX.1 hY.1 (hgood (h ≫ q) hZ'').1
      hY''.1 hproper)
    hh' (k - p) (c.cap (h ≫ q) hZ'' (hgood (h ≫ q) hZ'') k α)

/-- **Stacks 0ERQ.** The assertion that a bivariant class of degree `p` for `g` is *the* proper
pushforward of `c` along `f`: on every good test space over `Z` its cap operation is cap with
`c` followed by proper pushforward along the base change of `f`. -/
def IsBivariantProperPushforward (hg : g ≫ sZ = sY)
    (d : BivariantClass D G sY hY sZ hZ g hg p) : Prop :=
  ∀ {Z' : D.Ambient} (q : Z' ⟶ Z) (hZ' : D.IsGood (q ≫ sZ))
    (hY' : D.IsGood (pullback.fst g q ≫ sY)) (k : ℤ) (α : G.chow (q ≫ sZ) hZ' k),
    d.cap q hZ' hY' k α =
      bivariantProperPushforwardCap D G sX hX sY hY sZ hZ f g hf hfg hproper hgood p c q hZ'
        hY' k α

/-- **Stacks 0ERQ.** The rule of Stacks 0ERQ determines the pushed-forward class: two bivariant
classes of degree `p` for `g` that both push `c` forward along `f` are equal. -/
@[stacks 0ERQ "uniqueness of the class defined by the rule"]
theorem eq_of_isBivariantProperPushforward (hg : g ≫ sZ = sY)
    {d d' : BivariantClass D G sY hY sZ hZ g hg p}
    (hd : IsBivariantProperPushforward D G sX hX sY hY sZ hZ f g hf hfg hproper hgood p c hg d)
    (hd' : IsBivariantProperPushforward D G sX hX sY hY sZ hZ f g hf hfg hproper hgood p c hg
      d') :
    d = d' :=
  BivariantClass.ext D G sY hY sZ hZ g hg p fun q hZ' hY' k α =>
    (hd q hZ' hY' k α).trans (hd' q hZ' hY' k α).symm

end Pushforward

end AlgebraicGeometry.Space

end
