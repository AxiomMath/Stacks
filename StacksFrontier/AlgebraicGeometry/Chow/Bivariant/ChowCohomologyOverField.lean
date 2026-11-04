module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Bivariant classes towards a field and Chow homology

Let `k` be a field and let `X` be a scheme locally of finite type over `k`. **Stacks 0FBW** says
that there is a canonical identification

  `A^p(X ⟶ Spec k) = CH_{-p}(X)`   for all `p ∈ ℤ`.

The map is cap product with the fundamental class of the point: a bivariant class `c` of degree
`p` for the structure morphism `X ⟶ Spec k` has a cap operation on the Chow groups of every test
scheme over `Spec k`, and the test scheme `Spec k` itself contributes

  `c ∩ [Spec k] ∈ CH_{0 - p}(X ×_{Spec k} Spec k) = CH_{-p}(X)`,

the product collapsing through its first projection. That map is `Stacks.Chow.bivariantToBaseEval`
and it is **injective**, which is the half of the identification proved here. See the
implementation notes for the half that is not.

## Main definitions

* `Stacks.Chow.bivariantToBase` — the group `A^p(X ⟶ Spec k)` of bivariant classes of degree `p`
  for the structure morphism of `X`, namely `Stacks.Chow.BivariantClass` with the identity of the
  base as the structure morphism of the target.
* `Stacks.Chow.baseFundamentalClass` — the fundamental class `[Spec k] ∈ CH_0(Spec k)`, in the
  form a cap operation of such a class consumes it.
* `Stacks.Chow.capBaseFundamentalClass` — cap product with `[Spec k]`, before the collapse of the
  product.
* `Stacks.Chow.chowGroupBaseUnitCollapse` — the collapse
  `CH_{0-p}(X ×_{Spec k} Spec k) ≃ CH_{-p}(X)` along the first projection.
* `Stacks.Chow.bivariantToBaseEval` — **Stacks 0FBW**, the canonical map
  `A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)`.
* `Stacks.Chow.IntegralFundamentalClassIsFlatPullback` — the input the source proof takes from the
  base being a field which this repository cannot supply; see below.

## Main results

* `Stacks.Chow.cap_fundamentalChowClass_eq_zero_of_cap_baseFundamentalClass_eq_zero` — the
  geometric step of the source proof: for an integral test scheme `T` over the base, `c ∩ [T]` is
  the flat pullback of `c ∩ [Spec k]` along the base change of `T ⟶ Spec k` to `X`, so if
  `c ∩ [Spec k]` vanishes then so does `c ∩ [T]`, in every degree.
* `Stacks.Chow.eq_of_cap_baseFundamentalClass_eq` — two bivariant classes for `X ⟶ Spec k` that
  cap the fundamental class of the point to the same Chow class are equal.
* `Stacks.Chow.bivariantToBaseEval_injective` — **Stacks 0FBW**, injectivity of the canonical map
  `A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)`.

## Implementation notes

### What is proved and what is not

Stacks 0FBW is an identification, and only its injectivity is proved here; both `@[stacks 0FBW]`
attributes are therefore keyed. Injectivity is the direction the source proof derives from the
laws of a bivariant class, and that derivation is carried out in full: `[T]` is the flat
pullback of `[Spec k]` for an integral `T`, the flat-pullback law of Stacks 0B76 therefore
computes `c ∩ [T]` from `c ∩ [Spec k]`, and Stacks 02UC — which is
`Stacks.Chow.BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero` in this repository —
upgrades "kills the fundamental class of every integral test scheme" to "is zero".

Surjectivity is **not** proved, and cannot be reached from this repository. The source constructs
the inverse by sending `α ∈ CH_{-p}(X)` to the class `β ↦ α × β`, and verifies that it is
bivariant by factoring the structure morphism through `∐ X_i` and writing the rule as
`g_* ∘ ν ∘ f^*`: a flat pullback class (Stacks 0B78), a degree-zero class, and a proper
pushforward of bivariant classes (Stacks 0EPK). Of those, Stacks 0EPK is only *characterized*
here — `Stacks.Chow.IsBivariantProperPushforward` pins the pushed-forward class down uniquely but
no declaration produces one — and the coproduct `∐ X_i` together with the product decomposition
of its Chow groups is not available either; see
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ChowGroup`. Writing the exterior product
down is not the obstruction: `Stacks.Chow.chowExteriorProduct` of Stacks 0FBV exists. What is
missing is the proof that it satisfies the three naturality laws of Stacks 0B76.

### The base

The base is kept as a general `Stacks.Chow.ChowSituation`, as in
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree`, rather than being specialized to
`Stacks.Chow.fieldChowSituation`; every statement below instantiates to a field through that
situation, whose base scheme is `Spec k` reducibly, so no transport along an equality of schemes
appears anywhere.

That the base is the spectrum of a field is expressed by the two instance hypotheses
`[Subsingleton C.S]` and `[IsIntegral C.S]` on its base scheme: a scheme which is integral and
whose space is a subsingleton is the spectrum of a field, by Mathlib's
`AlgebraicGeometry.isField_of_isIntegral_of_subsingleton`, and conversely `Spec k` for a field `k`
satisfies both. They are instance hypotheses rather than an equality of schemes so that nothing
has to be transported, and they are discharged by instance search at
`Stacks.Chow.fieldChowSituation`. Flatness of everything over the base is a *consequence* of them,
supplied by Mathlib's instance making every morphism to an integral scheme with a subsingleton
space flat, not a hypothesis.

### The two remaining hypotheses

Both are prerequisites of Stacks 0FBW and neither is its conclusion:

* `hS1 : Stacks.Chow.FlatPullbackDescends C` — **Stacks 02S1**, that flat pullback of cycles
  factors through rational equivalence, bundled over every flat morphism over the base. It is
  what makes `Stacks.Chow.flatPullbackChow` exist at all and is a standing hypothesis throughout
  this repository.
* `hfund : Stacks.Chow.IntegralFundamentalClassIsFlatPullback C hS1` — an integral scheme
  locally of finite type over the base has a relative dimension (**Stacks 02NJ**, **Stacks
  02NK**) and its fundamental class is the flat pullback of the fundamental class of the base
  (**Stacks 02R4**).

Both speak only about Chow homology and flatness; neither mentions bivariant classes.

### Why the cap operation is read at `𝟙 (Spec k)`

The target of the structure morphism is the base itself, so the structure morphism of the target
is `𝟙 (Spec k)` and the test scheme realizing `[Spec k]` is `Spec k` through `𝟙 (Spec k)`. A cap
operation of `Stacks.Chow.BivariantClass` at the test morphism `g` is indexed by `g ≫ sY`, which
is here `𝟙 (Spec k) ≫ 𝟙 (Spec k)`, and the base change of the structure morphism along it is
`X ×_{Spec k} Spec k` rather than `X`. Both are collapsed by
`Stacks.Chow.chowGroupBaseUnitCollapse`, built from `Stacks.Chow.chowGroupEquivOfIso` and
`Stacks.Chow.chowGroupDegreeEquiv`; the same collapse appears in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePoint` for Stacks 0FG0 (2).

## References

* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-! ### The group `A^p(X ⟶ Spec k)` and the canonical map to Chow homology -/

/-- **Stacks 0B76 for the structure morphism.** The group `A^p(X ⟶ Spec k)` of bivariant classes
of degree `p` for the structure morphism of `X`: the target is the base itself, whose structure
morphism is the identity. -/
abbrev bivariantToBase : Type (u + 1) :=
  BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p

/-- The fundamental class `[Spec k] ∈ CH_0(Spec k)` of the base, in the form in which the cap
operation of a bivariant class towards the base consumes it: the test scheme is the base through
its identity, so the Chow group is indexed by `𝟙 (Spec k) ≫ 𝟙 (Spec k)`. -/
abbrev baseFundamentalClass : chowGroup C (𝟙 C.S ≫ 𝟙 C.S) 0 :=
  fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) 0

/-- The collapse `CH_{0-p}(X ×_{Spec k} Spec k) ≃ CH_{-p}(X)`: the first projection of a product
one of whose factors is the base is an isomorphism, and `0 - p` and `-p` are the same integer
written two ways. -/
def chowGroupBaseUnitCollapse :
    chowGroup C (pullback.fst sX (𝟙 C.S) ≫ sX) (0 - p) ≃+ chowGroup C sX (-p) :=
  (chowGroupDegreeEquiv C (pullback.fst sX (𝟙 C.S) ≫ sX) (zero_sub p)).trans
    (chowGroupEquivOfIso C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl (-p))

/-- Cap product with the fundamental class of the base, `c ↦ c ∩ [Spec k]`, as an additive map.
Its value lives on the base change `X ×_{Spec k} Spec k` and in degree `0 - p`; both are collapsed
by `Stacks.Chow.chowGroupBaseUnitCollapse`. -/
def capBaseFundamentalClass :
    bivariantToBase C G sX p →+ chowGroup C (pullback.fst sX (𝟙 C.S) ≫ sX) (0 - p) where
  toFun c := c.cap (𝟙 C.S) 0 (baseFundamentalClass C)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `capBaseFundamentalClass` sends a bivariant class `c` to `c ∩ [Spec k]`. -/
@[simp]
theorem capBaseFundamentalClass_apply (c : bivariantToBase C G sX p) :
    capBaseFundamentalClass C G sX p c = c.cap (𝟙 C.S) 0 (baseFundamentalClass C) :=
  rfl

/-- **Stacks 0FBW.** The canonical map `A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)`: cap product with the
fundamental class of the point, read through the collapse of `X ×_{Spec k} Spec k` onto `X` along
its first projection. It is injective by `Stacks.Chow.bivariantToBaseEval_injective`;
surjectivity is not proved here, see the implementation notes of this module. -/
@[stacks 0FBW "the canonical map A^p(X → Spec k) → CH_{-p}(X), cap product with the \
fundamental class of the point"]
def bivariantToBaseEval : bivariantToBase C G sX p →+ chowGroup C sX (-p) :=
  (chowGroupBaseUnitCollapse C sX p).toAddMonoidHom.comp (capBaseFundamentalClass C G sX p)

/-- `bivariantToBaseEval` sends a bivariant class `c` to the image of `c ∩ [Spec k]` under
`chowGroupBaseUnitCollapse`. -/
@[simp]
theorem bivariantToBaseEval_apply (c : bivariantToBase C G sX p) :
    bivariantToBaseEval C G sX p c =
      chowGroupBaseUnitCollapse C sX p (c.cap (𝟙 C.S) 0 (baseFundamentalClass C)) :=
  rfl

/-- The canonical map of Stacks 0FBW is cap product with the fundamental class of the point up to
an isomorphism, so two bivariant classes have the same image exactly when they cap `[Spec k]` to
the same Chow class. -/
theorem bivariantToBaseEval_eq_iff (c d : bivariantToBase C G sX p) :
    bivariantToBaseEval C G sX p c = bivariantToBaseEval C G sX p d ↔
      c.cap (𝟙 C.S) 0 (baseFundamentalClass C) = d.cap (𝟙 C.S) 0 (baseFundamentalClass C) := by
  rw [bivariantToBaseEval_apply, bivariantToBaseEval_apply]
  exact (chowGroupBaseUnitCollapse C sX p).injective.eq_iff

/-! ### What the base being a field contributes -/

/-- The second of the two things the proof of Stacks 0FBW takes from the base being a field, the
first being that every scheme over the base is flat over it (a Mathlib instance): an integral
scheme `T` locally of finite type over the base is of some relative dimension `r` over
it (**Stacks 02NJ**, **Stacks 02NK**, the dimension of `T`), its fundamental class is
concentrated in that degree, and in that degree it is the flat pullback of the fundamental class
of the base (**Stacks 02R4**):

  `[T] = (T ⟶ Spec k)^* [Spec k]`.

The morphism `v : T ⟶ Spec k` whose flat pullback is taken and the structure morphism `sT` of `T`
are the same morphism, presented separately and tied by `hv : v ≫ sS = sT` because a cap
operation of a bivariant class towards the base indexes its Chow groups by composites with the
identity of the base; `hsS : sS = 𝟙 (Spec k)` likewise pins `sS` down as the structure morphism
of the base, so that `fundamentalChowClass C sS 0` is `[Spec k]`.

Nothing here mentions bivariant classes: this is a statement about Chow homology and flatness
alone. Flatness of `v` is not assumed: Mathlib's instances find it, the base being integral with
a one-point space. -/
def IntegralFundamentalClassIsFlatPullback (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] (hS1 : FlatPullbackDescends C) : Prop :=
  ∀ {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] [IsIntegral T]
      (sS : C.S ⟶ C.S) [LocallyOfFiniteType sS] (_hsS : sS = 𝟙 C.S)
      (v : T ⟶ C.S) [LocallyOfFiniteType v] (hv : v ≫ sS = sT),
    ∃ (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension v r),
      (∀ k : ℤ, k ≠ (0 : ℤ) + (r : ℤ) → fundamentalChowClass C sT k = 0) ∧
        fundamentalChowClass C sT ((0 : ℤ) + (r : ℤ)) =
          flatPullbackChow C sT sS v hv r hr 0 (hS1 sT sS v hv r hr 0)
            (fundamentalChowClass C sS 0)

/-! ### Injectivity of the canonical map -/

/-- **The geometric step in the proof of Stacks 0FBW.** Let `c ∈ A^p(X ⟶ Spec k)` cap the
fundamental class of the point to zero and let `T` be an integral scheme locally of finite type
over `Spec k`. Then `c ∩ [T] = 0` in every degree: the fundamental class `[T]` is the flat
pullback of `[Spec k]` along `T ⟶ Spec k`, and cap product commutes with flat pullback — the
second law of Stacks 0B76 — so `c ∩ [T]` is the flat pullback of `c ∩ [Spec k]` along the base
change of `T ⟶ Spec k` to `X`. -/
theorem cap_fundamentalChowClass_eq_zero_of_cap_baseFundamentalClass_eq_zero
    [Subsingleton C.S] [IsIntegral C.S] (hS1 : FlatPullbackDescends C)
    (hfund : IntegralFundamentalClassIsFlatPullback C hS1)
    (c : bivariantToBase C G sX p) (hc : c.cap (𝟙 C.S) 0 (baseFundamentalClass C) = 0)
    {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ) :
    c.cap (g ≫ 𝟙 C.S) k (fundamentalChowClass C ((g ≫ 𝟙 C.S) ≫ 𝟙 C.S) k) = 0 := by
  have hb : g ≫ (𝟙 C.S ≫ 𝟙 C.S) = (g ≫ 𝟙 C.S) ≫ 𝟙 C.S := by simp
  obtain ⟨r, hr, hzero, heq⟩ :=
    hfund ((g ≫ 𝟙 C.S) ≫ 𝟙 C.S) (𝟙 C.S ≫ 𝟙 C.S) (Category.comp_id (𝟙 C.S)) g hb
  by_cases hk : k = (0 : ℤ) + (r : ℤ)
  · subst hk
    have sq := isPullback_bivariantBaseChangeMap sX (𝟙 C.S) g
    have : LocallyOfFiniteType (bivariantBaseChangeMap sX (𝟙 C.S) g) :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat (bivariantBaseChangeMap sX (𝟙 C.S) g) :=
      MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    have hr' : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap sX (𝟙 C.S) g) r :=
      AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
    have hnat := c.flat_naturality (𝟙 C.S) g r hr (bivariantBaseChangeMap sX (𝟙 C.S) g) sq
      (bivariantBaseChangeMap_fst sX (𝟙 C.S) g) 0 hr' (hS1 _ _ g _ r hr 0)
      (hS1 _ _ (bivariantBaseChangeMap sX (𝟙 C.S) g) _ r hr' (0 - p)) (baseFundamentalClass C)
    rw [hc, map_zero] at hnat
    have hz : c.cap (g ≫ 𝟙 C.S) ((0 : ℤ) + (r : ℤ))
        (fundamentalChowClass C ((g ≫ 𝟙 C.S) ≫ 𝟙 C.S) ((0 : ℤ) + (r : ℤ))) ≍
          (0 : chowGroup C (pullback.fst sX (g ≫ 𝟙 C.S) ≫ sX) ((0 - p) + (r : ℤ))) := by
      rw [heq]
      exact hnat
    exact chowGroup_eq_zero_of_heq_zero C (by ring) hz
  · rw [hzero k hk, map_zero]

/-- **Stacks 0FBW, injectivity.** Two bivariant classes of degree `p` for the structure morphism
`X ⟶ Spec k` whose cap products with the fundamental class of the point agree are equal.

The proof is the one in the source: by Stacks 02UC a bivariant class is zero as soon as it kills
the fundamental class of every integral scheme locally of finite type over the base, and those
fundamental classes are flat pullbacks of the fundamental class of the base, so the flat-pullback
law of Stacks 0B76 computes them all from `c ∩ [Spec k]`. -/
theorem eq_of_cap_baseFundamentalClass_eq
    [Subsingleton C.S] [IsIntegral C.S] (hS1 : FlatPullbackDescends C)
    (hfund : IntegralFundamentalClassIsFlatPullback C hS1)
    {c d : bivariantToBase C G sX p}
    (h : c.cap (𝟙 C.S) 0 (baseFundamentalClass C) = d.cap (𝟙 C.S) 0 (baseFundamentalClass C)) :
    c = d := by
  rw [← sub_eq_zero, BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero C G sX
    (𝟙 C.S) sX (Category.comp_id sX) p]
  intro T g _ _ k
  refine BivariantClass.cap_fundamentalChowClass_eq_zero_congr C G sX (𝟙 C.S) sX
    (Category.comp_id sX) p (c - d) (Category.comp_id g).symm k ?_
  refine cap_fundamentalChowClass_eq_zero_of_cap_baseFundamentalClass_eq_zero C G sX p hS1
    hfund (c - d) ?_ g k
  rw [BivariantClass.sub_cap, h, sub_self]

/-- **Stacks 0FBW, injectivity.** The canonical map `A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)` of Stacks 0FBW
is injective: a bivariant class of degree `p` for the structure morphism of `X` is determined by
its cap product with the fundamental class of the point. Surjectivity is not proved here; see the
implementation notes of this module. -/
@[stacks 0FBW "injectivity of the canonical identification, for the base being the spectrum of a \
field; hS1 is Stacks 02S1 and hfund is Stacks 02NK with Stacks 02R4"]
theorem bivariantToBaseEval_injective
    [Subsingleton C.S] [IsIntegral C.S] (hS1 : FlatPullbackDescends C)
    (hfund : IntegralFundamentalClassIsFlatPullback C hS1) :
    Function.Injective (bivariantToBaseEval C G sX p) := fun _ _ h ↦
  eq_of_cap_baseFundamentalClass_eq C G sX p hS1 hfund
    ((bivariantToBaseEval_eq_iff C G sX p _ _).mp h)

end Stacks.Chow

end
