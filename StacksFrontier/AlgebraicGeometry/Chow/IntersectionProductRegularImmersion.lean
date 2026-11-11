module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalIso
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct

/-!
# The intersection product with the class of a regularly embedded closed subscheme

Let `k` be a field, let `X` be a scheme smooth over `k` and let `i : Y ⟶ X` be a regular closed
immersion of codimension `r`. **Stacks 0FFE** asserts that for `α ∈ CH_*(X)`, and for `Y`
equidimensional of dimension `e`,

  `α · [Y]_e = i_*(i^!(α))`   in   `CH_*(X)`,

where `·` is the intersection product of **Stacks 0FC0**, `i^!` is the Gysin map of the regular
immersion and `[Y]_e` is read on `X` as `i_*[Y]_e`, exactly as the source's proof does.

The source proves this by writing `α = c ∩ [X]_d` with `c ∈ A^{d-*}(X)` (Stacks 0FC2) and then
running the chain

  `i_*(i^!(c ∩ [X]_d)) = i_*(c ∩ i^![X]_d) = i_*(c ∩ [Y]_e) = c ∩ i_*[Y]_e = α · [Y]_e`,

whose four steps are Stacks 0FF6, Stacks 0FF7, the proper-pushforward law of a bivariant class
(Stacks 0B76 (1)) and Stacks 0FC2 again. This file runs that chain for a Gysin class `ci`
characterized by Stacks 0FBK over a general base, proving the second and third steps and taking the
first and fourth as hypotheses in the shape the chain uses there. The complete statement of Stacks
0FFE, for the Gysin map of Stacks 0FF3 of a regular closed immersion into a scheme smooth over a
field, with every step proved, is
`Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin`.

## Main definitions

* `Stacks.Chow.chowGroupIdentityPullbackCollapse`, and
  `Stacks.Chow.chowGroupPullbackIdentityCollapse` — the collapses
  `CH_k(X ×_X Y) ≃ CH_k(Y)` and `CH_k(Y ×_X X) ≃ CH_k(Y)` of the two base changes of `i` and of
  the identity of `X` against each other, proper pushforward along the projection that is an
  isomorphism.
* `Stacks.Chow.chowGroupSelfProductUnitCollapse` — the collapse `CH_k(X ×_X X) ≃ CH_k(X)` of the
  self-product of the identity of `X`, read over the structure morphism `𝟙 X ≫ sX` that the
  intersection product of Stacks 0FC0 at `a = b = 𝟙 X` lands over.
* `Stacks.Chow.chowCohomologyCap` — the operational action `α ↦ c ∩ α` of `A^p(X)` on
  `CH_*(X)`: the cap operation at the test scheme `𝟙 X`, read on `X`.
* `Stacks.Chow.chowCohomologyCapOnSubscheme` — the action `β ↦ c ∩ β` of `A^p(X)` on
  `CH_*(Y)`: the cap operation of `c` at the test scheme `i`, read on `Y`.
* `Stacks.Chow.closedImmersionBivariantCap` — the action `α ↦ c' ∩ α` of `A^p(Y ⟶ X)` on
  `CH_*(X)` with values in `CH_*(Y)`, which is the Gysin map `i^!` when `c'` is the Gysin class
  of Stacks 0FBK.

## Main results

* `Stacks.Chow.schemeDeltaDimension_pullback_id` — the base change `Y ×_X X` of `i` along the
  identity has the delta-dimension of `Y`.
* `Stacks.Chow.chowCohomologyCap_fundamentalChowClass` — the action of `c ∈ A^p(X)` on the
  fundamental class `[X]_d` is the map of **Stacks 0FC2**.
* `Stacks.Chow.closedImmersionBivariantCap_fundamentalChowClass` — **Stacks 0FF7** for a regular
  closed immersion: `i^![X]_d = [Y]_{d-r}` for the Gysin class of Stacks 0FBK.
* `Stacks.Chow.chowCohomologyCap_properChowPushforward` — **Stacks 0B76 (1)** at the test scheme
  `𝟙 X`: `c ∩ i_*β = i_*(c ∩ β)` in `CH_*(X)`.
* `Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_gysin` —
  the chain of the proof of Stacks 0FFE for a Gysin class characterized by Stacks 0FBK, given
  its first and fourth steps: `α · i_*[Y]_e = i_*(i^!(α))`.

## Implementation notes

### What the three objects of the tag are here

The intersection product `α · β` is `Stacks.Chow.intersectionProduct` of
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct`, which is Stacks 0FC0, taken at
`a = b = 𝟙 X`: that is the case `Y = Z = X` in which the source's product on
`CH_*(Y) × CH_*(Z) ⟶ CH_*(Y ×_X Z)` is a multiplication on `CH_*(X)`. Its value lands on
`X ×_X X`, which `Stacks.Chow.chowGroupSelfProductUnitCollapse` collapses onto `X`. Its defining
bivariant class is the Gysin class `Δ^!` of the diagonal, carried as `cd` in the degree `d` it
has; for `X` smooth over a field and equidimensional of dimension `d` that degree is `d` by
Stacks 0FBR.

Smoothness of `X` is therefore not itself a hypothesis below: it enters only through the
existence of `cd`, exactly as in
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionProduct`, where
`Stacks.Chow.isRegularImmersion_diagonal_of_smooth` and
`Stacks.Chow.diagonalVirtualNormalGysinClass` are what produce that class from it. For the same
reason the base is a general `Stacks.Chow.ChowSituation` carrying the side conditions of the
exterior product of Stacks 0FBV rather than `Spec k`; those conditions hold for the spectrum of
a field, which is the source's base.

The Gysin map `i^!` is the cap operation of a bivariant class `ci ∈ A^r(Y ⟶ X)` satisfying the
characterizing relation `Stacks.Chow.IsVirtualNormalGysinClass` of **Stacks 0FBK** for the
virtual normal bundle `NP` of `i`, which is how section 42.54 of the source defines `i^!` for a
regular closed immersion. The lci Gysin map of Stacks 0FF3 itself is
`Stacks.Chow.lciGysinMap`, and the complete statement for it is
`Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin`.
Regularity of `i`
enters through that datum and through the degree `r` in which the conclusion of Stacks 0FBM is
read, which is the vanishing-excess case; the hypothesis `_hreg` recording it separately is
therefore unused.

The class `[Y]_e` is `Stacks.Chow.fundamentalChowClass` of **Stacks 0FE4**, and `i_*` is
`Stacks.Chow.properChowPushforward`.

### The degree `e`, and the source's reduction to components

The two sides of the identity live in `CH_{(d-p)+e-d}(X)` and in `CH_{(d-p)-r}(X)`, so the
identity has a statement only for `e = d - r`, and `e` is written `d - r` below. For `X`
equidimensional of dimension `d` and `i` a regular closed immersion of codimension `r` that is
the dimension of `Y`, which is the source's hypothesis.

Equidimensionality of `X` is *not* assumed: `d` is only the degree of the carried diagonal
class, so the statement below is the one the source obtains after its first reduction, for an
arbitrary such degree. The reduction itself — splitting a smooth `X` into its clopen pieces of
constant dimension — is carried out in the proof of
`Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin`,
with the classes graded by codimension.

### The two inputs taken here, and that neither of them is the conclusion

`h0FBP` is the step `i^!(c ∩ x) = c ∩ i^!(x)`, read on `Y`, for the class `ci` of this file. This
is the `i^!` half of **Stacks 0FF6**, which the source discharges by **Stacks 0FBP** (Lemma
42.54.8 of the source). Both are proved in the library — Stacks 0FBP as
`Stacks.Chow.VirtualNormalBundle.completedClass_bivariantCommute` and Stacks 0FF6 for the lci
Gysin map as `Stacks.Chow.completedCommutesAfterBaseChange_lciGysinMap` — but for the classes
built there, not for an arbitrary class `ci` satisfying the relation of Stacks 0FBK, which is why
the step is a hypothesis of this form of the chain. The general form of the assertion is
`Stacks.Chow.BivariantCommute` of **Stacks 0FA2**, of which `h0FBP` is the instance
at the test scheme `𝟙 X` read through the two collapses above. It is a statement about `ci` and
`c` alone: it mentions neither the intersection product nor proper pushforward, so it is not the
conclusion.

`h0FC2` is the step `α · β = c ∩ β` for the class `c` representing `α`, which is clause (1) of
**Stacks 0FC2** — the surjectivity of `c ↦ c ∩ [X]_d` — together with clause (2), that the
isomorphism carries composition of bivariant classes to the intersection product. Both clauses
are proved in the library over a field
(`Stacks.Chow.chowCohomologyCapFundamentalClass_bijective_of_smooth_field` and
`Stacks.Chow.chowCohomologyCapFundamentalClass_mulId_of_smooth_field`), for the product formed with
the canonical diagonal class; here `cd` is an arbitrary diagonal class over a general base, so the
step is a hypothesis of this form of the chain. The representability half appears separately as
`hα`, which fixes `α` to be `c ∩ [X]_d`. Both
are statements about `c`, `α` and the product; neither mentions `i`, `i^!` or proper
pushforward, so neither is the conclusion.

### The delta-dimension hypothesis

"`Y` equidimensional of dimension `e`" appears as the bound
`dim_δ(Y) ≤ e`, which is what Stacks 0FBM consumes and what equidimensionality of dimension `e`
gives. Taking a bound rather than an equality only widens the statement, and `e` is pinned by
the degrees as above, so no case of the source is lost.
`Stacks.Chow.schemeDeltaDimension_pullback_id` transports the bound to the fibre product
`Y ×_X X` on which Stacks 0FBM reads it.

### Remaining carried inputs

`hinj` is Stacks 02TY and `hcone` is the value of `ι_* ∘ j^* ∘ C` on a fundamental class; both
are inputs of `Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass`, discussed in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection`. `hpp` is Stacks 02S2 and
`hdesc` is Stacks 02S1, in the bundled flat-pullback form that `Stacks.Chow.bundleFlatPullback`
consumes; the three instances on the base scheme and `hδ` are the side conditions of the exterior
product of Stacks 0FBV that Stacks 0FC0 already carries. The instances of Stacks 02S1 that the
exterior product itself needs are *not* carried: Stacks 0FC0 supplies them from the general case
of Stacks 02S1, so they do not appear below.

## References

* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transports along equalities of structure morphisms and of degrees -/

/-- The transport of a Chow group along the reflexivity of its structure morphism is the
identity. -/
private theorem chowGroupCongr_rfl (C : ChowSituation.{u}) {T : Scheme.{u}} {q : T ⟶ C.S}
    [LocallyOfFiniteType q] (k : ℤ) (x : chowGroup C q k) :
    chowGroupCongr C (rfl : q = q) k x = x := rfl

/-- Proper pushforward commutes with the transport of Chow groups along an equality of
degrees. -/
private theorem properChowPushforward_degreeTransport (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (u : A ⟶ B) [IsProper u] (hu : u ≫ sB = sA) {k l : ℤ} (h : k = l)
    (hk : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hl : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu l)
    (x : chowGroup C sA k) :
    properChowPushforward C sA sB u hu l hl (chowGroupDegreeEquiv C sA h x) =
      chowGroupDegreeEquiv C sB h (properChowPushforward C sA sB u hu k hk x) := by
  subst h
  rfl

/-! ### The three collapses -/

section Collapse

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Y ⟶ X) [IsClosedImmersion i]

/-- The collapse `CH_k(X ×_X Y) ≃ CH_k(Y)` of the base change of the identity of `X` along
`i : Y ⟶ X`: proper pushforward along the second projection, which is an isomorphism. -/
def chowGroupIdentityPullbackCollapse (k : ℤ) :
    chowGroup C (pullback.fst (𝟙 X) i ≫ sX) k ≃+ chowGroup C (i ≫ sX) k :=
  chowGroupEquivOfIso C (pullback.fst (𝟙 X) i ≫ sX) (i ≫ sX) (pullback.snd (𝟙 X) i)
    (by rw [← Category.assoc, ← pullback.condition, Category.comp_id]) k

/-- The collapse `CH_k(Y ×_X X) ≃ CH_k(Y)` of the base change of `i : Y ⟶ X` along the identity
of `X`: proper pushforward along the first projection, which is an isomorphism. -/
def chowGroupPullbackIdentityCollapse (k : ℤ) :
    chowGroup C (pullback.fst i (𝟙 X) ≫ (i ≫ sX)) k ≃+ chowGroup C (i ≫ sX) k :=
  chowGroupEquivOfIso C (pullback.fst i (𝟙 X) ≫ (i ≫ sX)) (i ≫ sX) (pullback.fst i (𝟙 X)) rfl k

/-- The collapse `CH_k(X ×_X X) ≃ CH_k(X)` of the self-product of the identity of `X`, read over
the structure morphism `𝟙 X ≫ sX` that the intersection product of Stacks 0FC0 at
`a = b = 𝟙 X` lands over: proper pushforward along the first projection. -/
def chowGroupSelfProductUnitCollapse (k : ℤ) :
    chowGroup C (pullback.fst (𝟙 X) (𝟙 X) ≫ (𝟙 X ≫ sX)) k ≃+ chowGroup C sX k :=
  chowGroupEquivOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ (𝟙 X ≫ sX)) sX (pullback.fst (𝟙 X) (𝟙 X))
    (by rw [Category.id_comp]) k

/-- The base change `Y ×_X X` of a closed immersion `i : Y ⟶ X` along the identity of `X` has
the delta-dimension of `Y`: the first projection is an isomorphism over the base. -/
theorem schemeDeltaDimension_pullback_id :
    schemeDeltaDimension C (pullback.fst i (𝟙 X) ≫ (i ≫ sX)) =
      schemeDeltaDimension C (i ≫ sX) := by
  have h := schemeDeltaDimension_comp_iso C (pullbackIdIso i) (pullback.fst i (𝟙 X) ≫ (i ≫ sX))
  have h2 : (pullbackIdIso i).hom ≫ (pullback.fst i (𝟙 X) ≫ (i ≫ sX)) = i ≫ sX := by
    rw [← Category.assoc, pullbackIdIso_hom_fst, Category.id_comp]
  exact h.symm.trans (schemeDeltaDimension_congr C h2)

end Collapse

/-! ### The cap operations on `X` and on `Y` -/

section Action

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i : Y ⟶ X) [IsClosedImmersion i] (p : ℤ)

/-- The operational action `α ↦ c ∩ α` of a bivariant class `c ∈ A^p(X)` on `CH_*(X)`: the cap
operation of `c` at the test scheme `𝟙 X`, read on `X` through the collapse of `X ×_X X`. -/
def chowCohomologyCap (c : chowCohomologyComponent C G sX p) (k : ℤ) :
    chowGroup C sX k →+ chowGroup C sX (k - p) :=
  ((chowGroupEquivOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) sX (pullback.fst (𝟙 X) (𝟙 X)) rfl
      (k - p)).toAddMonoidHom).comp
    ((c.cap (𝟙 X) k).comp (chowGroupCongr C (Category.id_comp sX).symm k).toAddMonoidHom)

/-- The action `β ↦ c ∩ β` of a bivariant class `c ∈ A^p(X)` on `CH_*(Y)` for a closed subscheme
`i : Y ⟶ X`: the cap operation of `c` at the test scheme `i`, read on `Y`. -/
def chowCohomologyCapOnSubscheme (c : chowCohomologyComponent C G sX p) (k : ℤ) :
    chowGroup C (i ≫ sX) k →+ chowGroup C (i ≫ sX) (k - p) :=
  ((chowGroupIdentityPullbackCollapse C sX i (k - p)).toAddMonoidHom).comp (c.cap i k)

/-- The action `α ↦ c' ∩ α` of a bivariant class `c' ∈ A^p(Y ⟶ X)` taking `CH_k(X)` to
`CH_{k-p}(Y)`: the cap operation of `c'` at the test scheme `𝟙 X`, read on `Y`. For the Gysin
class of Stacks 0FBK this is the Gysin map `i^!` of a regular closed immersion. -/
def closedImmersionBivariantCap (ci : BivariantClass C G (i ≫ sX) sX i rfl p) (k : ℤ) :
    chowGroup C sX k →+ chowGroup C (i ≫ sX) (k - p) :=
  ((chowGroupPullbackIdentityCollapse C sX i (k - p)).toAddMonoidHom).comp
    ((ci.cap (𝟙 X) k).comp (chowGroupCongr C (Category.id_comp sX).symm k).toAddMonoidHom)

/-- **Stacks 0FC2.** The action of `c ∈ A^p(X)` on the fundamental class `[X]_d` is the value at
`c` of the map `A^p(X) ⟶ CH_{d-p}(X)` of Stacks 0FC2. -/
theorem chowCohomologyCap_fundamentalChowClass (c : chowCohomologyComponent C G sX p) (d : ℤ) :
    chowCohomologyCap C G sX p c d (fundamentalChowClass C sX d) =
      chowCohomologyCapFundamentalClass C G sX d p c := by
  simp only [chowCohomologyCap, chowCohomologyCapFundamentalClass_apply,
    AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    chowGroupCongr_fundamentalChowClass C (Category.id_comp sX).symm d]
  rfl

end Action

/-! ### Stacks 0FF7 for a regular closed immersion -/

section Gysin

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y N : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sN : N ⟶ C.S) [LocallyOfFiniteType sN] (i : Y ⟶ X)
  [IsClosedImmersion i] (q : N ⟶ Y) [LocallyOfFiniteType q] (hq : q ≫ (i ≫ sX) = sN) (r : ℕ)
  (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq rfl) 0)
  (NP : VirtualNormalBundleProjection i q r) (hdesc : FlatPullbackDescends C)

/-- **Stacks 0FF7 for a regular closed immersion.** For `i : Y ⟶ X` a closed immersion carrying a
virtual normal bundle of constant rank `r` and `ci` the Gysin class `i^!` of Stacks 0FBK for it,
`i^![X]_d = [Y]_{d-r}` whenever `dim_δ(Y) ≤ d - r`. This is the case `g = 𝟙 X` of the
factorization `f = i ≫ g` of Stacks 0FF3, in which the smooth factor contributes nothing. -/
theorem closedImmersionBivariantCap_fundamentalChowClass
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (i ≫ sX) sN i q hq r NP.flat NP.relativeDimension hdesc g k))
    {ci : BivariantClass C G (i ≫ sX) sX i rfl (r : ℤ)}
    (hci : IsVirtualNormalGysinClass C G (i ≫ sX) sX sN i rfl q hq r 0 E
      (bundleFlatPullback C (i ≫ sX) sN i q hq r NP.flat NP.relativeDimension hdesc) NP ci)
    (d : ℤ) (hY : schemeDeltaDimension C (i ≫ sX) ≤ ((d - (r : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C (pullback.fst (q ≫ i) (𝟙 X) ≫ sN)
        (by omega : d - (0 : ℤ) = (d - (r : ℤ)) + (r : ℤ))
        (E.cap (𝟙 X) d (fundamentalChowClass C (𝟙 X ≫ sX) d)) =
      fundamentalChowClass C (pullback.fst (q ≫ i) (𝟙 X) ≫ sN) ((d - (r : ℤ)) + (r : ℤ))) :
    closedImmersionBivariantCap C G sX i (r : ℤ) ci d (fundamentalChowClass C sX d) =
      fundamentalChowClass C (i ≫ sX) (d - (r : ℤ)) := by
  have hdim : schemeDeltaDimension C (pullback.fst i (𝟙 X) ≫ (i ≫ sX)) ≤
      ((d - (r : ℤ) : ℤ) : EInt) := by
    rw [schemeDeltaDimension_pullback_id C sX i]
    exact hY
  have key := virtualNormalGysinCap_fundamentalChowClass C G (i ≫ sX) sX sN i rfl q hq r E NP
    hdesc hinj hci (𝟙 X) d hdim hcone
  simp only [closedImmersionBivariantCap, chowGroupPullbackIdentityCollapse,
    AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    chowGroupEquivOfIso_apply, chowGroupCongr_fundamentalChowClass C (Category.id_comp sX).symm d,
    key]
  exact chowPushforwardOfIso_fundamentalChowClass C (pullback.fst i (𝟙 X) ≫ (i ≫ sX)) (i ≫ sX)
    (pullback.fst i (𝟙 X)) rfl (d - (r : ℤ))

end Gysin

/-! ### The proper-pushforward law at the test scheme `𝟙 X` -/

section Pushforward

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i : Y ⟶ X) [IsClosedImmersion i] (p : ℤ)

/-- **Stacks 0B76 (1).** For a closed immersion `i : Y ⟶ X` and `c ∈ A^p(X)` the identity
`c ∩ i_*β = i_*(c ∩ β)` holds in `CH_{k-p}(X)` for every `β ∈ CH_k(Y)`: the
proper-pushforward law of a bivariant class at the test scheme `𝟙 X`, read through the collapses
of `X ×_X X` and of `X ×_X Y`. -/
theorem chowCohomologyCap_properChowPushforward (hpp : ProperPushforwardDescends C)
    (c : chowCohomologyComponent C G sX p) (k : ℤ) (β : chowGroup C (i ≫ sX) k) :
    chowCohomologyCap C G sX p c k
        (properChowPushforward C (i ≫ sX) sX i rfl k (hpp _ _ _ _ _) β) =
      properChowPushforward C (i ≫ sX) sX i rfl (k - p) (hpp _ _ _ _ _)
        (chowCohomologyCapOnSubscheme C G sX i p c k β) := by
  set h' := testBaseChangeMapOfEq (𝟙 X) (𝟙 X) i i (Category.comp_id i) with hh'
  have hfst : h' ≫ pullback.fst (𝟙 X) (𝟙 X) = pullback.fst (𝟙 X) i :=
    testBaseChangeMapOfEq_fst (𝟙 X) (𝟙 X) i i (Category.comp_id i)
  have hsnd : h' ≫ pullback.snd (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) i ≫ i :=
    testBaseChangeMapOfEq_snd (𝟙 X) (𝟙 X) i i (Category.comp_id i)
  have hvA : pullback.snd (𝟙 X) i ≫ (i ≫ sX) = pullback.fst (𝟙 X) i ≫ sX := by
    rw [← Category.assoc, ← pullback.condition, Category.comp_id]
  have hsq : h' ≫ pullback.fst (𝟙 X) (𝟙 X) = pullback.snd (𝟙 X) i ≫ i := by
    rw [hfst, ← pullback.condition, Category.comp_id]
  have hu : h' ≫ (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) = pullback.fst (𝟙 X) i ≫ sX := by
    rw [← Category.assoc, hfst]
  have hfac : ProperPushforwardFactorsThroughRationalEquivalence C (i ≫ sX) (𝟙 X ≫ sX) i
      (by rw [Category.id_comp]) k := hpp _ _ _ _ _
  have hmain := BivariantClass.cap_properChowPushforward c hpp (𝟙 X) i i
    (Category.comp_id i) h' hfst hsnd k β
  have hcongr := properChowPushforward_chowGroupCongr C (rfl : (i ≫ sX) = (i ≫ sX))
    (Category.id_comp sX).symm i rfl (by rw [Category.id_comp]) k (hpp _ _ _ _ _) hfac β
  have hcomm := chowPushforwardOfIso_comm_properChowPushforward C
    (pullback.fst (𝟙 X) i ≫ sX) (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) (i ≫ sX) sX
    (pullback.snd (𝟙 X) i) (pullback.fst (𝟙 X) (𝟙 X)) h' i hsq hvA rfl hu rfl (k - p)
    (hpp _ _ _ _ _) (hpp _ _ _ _ _) (c.cap i k β)
  simp only [chowCohomologyCap, chowCohomologyCapOnSubscheme, chowGroupIdentityPullbackCollapse,
    AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    chowGroupEquivOfIso_apply, hcongr, chowGroupCongr_rfl, hmain, hcomm]

end Pushforward

/-! ### Stacks 0FFE -/

section Main

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {X Y N : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sN : N ⟶ C.S)
  [LocallyOfFiniteType sN] (i : Y ⟶ X) [IsClosedImmersion i]
  (q : N ⟶ Y) [LocallyOfFiniteType q] (hq : q ≫ (i ≫ sX) = sN) (r : ℕ)
  (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq rfl) 0)
  (NP : VirtualNormalBundleProjection i q r) (hdesc : FlatPullbackDescends C)
  (hpp : ProperPushforwardDescends C) (d p : ℤ)
  (cd : BivariantClass C G sX (selfProductStructure C sX) (pullback.diagonal sX)
    (diagonal_comp_selfProductStructure C sX) d)

/-- **The chain of the proof of Stacks 0FFE, for a Gysin class characterized by Stacks 0FBK.**
The complete statement of Stacks 0FFE is
`Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin`.
Let `i : Y ⟶ X` be a closed immersion of schemes locally of finite type over
the base, carrying a virtual normal bundle of constant rank `r`, let `cd` be a Gysin class of the
diagonal of `X` of degree `d` — the class `Δ^!` through which Stacks 0FC0 defines the
intersection product, of degree `d` for `X` smooth and equidimensional of dimension `d` — and let
`ci` be the Gysin class `i^!` of Stacks 0FBK for `i`. Let `α = c ∩ [X]_d` for a bivariant class
`c ∈ A^p(X)`, and let `Y` have delta-dimension at most `e = d - r`. Then

  `α · i_*[Y]_e = i_*(i^!(α))`   in   `CH_{e-p}(X)`,

the two sides being read on `X` through the collapse of `X ×_X X` and through the transport
between the two ways of writing their common degree.

The proof is the source's: `h0FC2` replaces the product by `c ∩ -`,
`Stacks.Chow.chowCohomologyCap_properChowPushforward` moves `i_*` across `c ∩ -`,
`Stacks.Chow.closedImmersionBivariantCap_fundamentalChowClass` identifies `i^![X]_d` with
`[Y]_e`, and `h0FBP` moves `i^!` across `c ∩ -`. See the implementation notes for what each
hypothesis is, and why neither carried hypothesis is the conclusion. -/
theorem intersectionProduct_fundamentalChowClass_eq_pushforward_gysin
    (c : chowCohomologyComponent C G sX p)
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (i ≫ sX) sN i q hq r NP.flat NP.relativeDimension hdesc g k))
    {ci : BivariantClass C G (i ≫ sX) sX i rfl (r : ℤ)}
    (hci : IsVirtualNormalGysinClass C G (i ≫ sX) sX sN i rfl q hq r 0 E
      (bundleFlatPullback C (i ≫ sX) sN i q hq r NP.flat NP.relativeDimension hdesc) NP ci)
    (hY : schemeDeltaDimension C (i ≫ sX) ≤ ((d - (r : ℤ) : ℤ) : EInt))
    (_hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)
    (hcone : chowGroupDegreeEquiv C (pullback.fst (q ≫ i) (𝟙 X) ≫ sN)
        (by omega : d - (0 : ℤ) = (d - (r : ℤ)) + (r : ℤ))
        (E.cap (𝟙 X) d (fundamentalChowClass C (𝟙 X ≫ sX) d)) =
      fundamentalChowClass C (pullback.fst (q ≫ i) (𝟙 X) ≫ sN) ((d - (r : ℤ)) + (r : ℤ)))
    (α : chowGroup C sX (d - p))
    (hα : chowCohomologyCap C G sX p c d (fundamentalChowClass C sX d) = α)
    (h0FBP : ∀ (k : ℤ) (x : chowGroup C sX k),
      closedImmersionBivariantCap C G sX i (r : ℤ) ci (k - p)
          (chowCohomologyCap C G sX p c k x) =
        chowGroupDegreeEquiv C (i ≫ sX) (by ring : k - (r : ℤ) - p = k - p - (r : ℤ))
          (chowCohomologyCapOnSubscheme C G sX i p c (k - (r : ℤ))
            (closedImmersionBivariantCap C G sX i (r : ℤ) ci k x)))
    (h0FC2 : ∀ β : chowGroup C sX (d - (r : ℤ)),
      chowGroupSelfProductUnitCollapse C sX ((d - p) + (d - (r : ℤ)) - d)
          (intersectionProduct C hδ G sX (𝟙 X) (𝟙 X) d cd (d - p) (d - (r : ℤ))
            (TensorProduct.tmul ℤ (chowGroupCongr C (Category.id_comp sX).symm (d - p) α)
              (chowGroupCongr C (Category.id_comp sX).symm (d - (r : ℤ)) β))) =
        chowGroupDegreeEquiv C sX
          (by ring : (d - (r : ℤ)) - p = (d - p) + (d - (r : ℤ)) - d)
          (chowCohomologyCap C G sX p c (d - (r : ℤ)) β)) :
    chowGroupSelfProductUnitCollapse C sX ((d - p) + (d - (r : ℤ)) - d)
        (intersectionProduct C hδ G sX (𝟙 X) (𝟙 X) d cd (d - p) (d - (r : ℤ))
          (TensorProduct.tmul ℤ (chowGroupCongr C (Category.id_comp sX).symm (d - p) α)
            (chowGroupCongr C (Category.id_comp sX).symm (d - (r : ℤ))
              (properChowPushforward C (i ≫ sX) sX i rfl (d - (r : ℤ)) (hpp _ _ _ _ _)
                (fundamentalChowClass C (i ≫ sX) (d - (r : ℤ))))))) =
      chowGroupDegreeEquiv C sX (by ring : (d - p) - (r : ℤ) = (d - p) + (d - (r : ℤ)) - d)
        (properChowPushforward C (i ≫ sX) sX i rfl ((d - p) - (r : ℤ)) (hpp _ _ _ _ _)
          (closedImmersionBivariantCap C G sX i (r : ℤ) ci (d - p) α)) := by
  have hgysin := closedImmersionBivariantCap_fundamentalChowClass C G sX sN i q hq r E NP hdesc
    hinj hci d hY hcone
  have hcommute := h0FBP d (fundamentalChowClass C sX d)
  rw [hα, hgysin] at hcommute
  rw [h0FC2 (properChowPushforward C (i ≫ sX) sX i rfl (d - (r : ℤ)) (hpp _ _ _ _ _)
      (fundamentalChowClass C (i ≫ sX) (d - (r : ℤ)))),
    chowCohomologyCap_properChowPushforward C G sX i p hpp c (d - (r : ℤ)) _, hcommute,
    properChowPushforward_degreeTransport C (i ≫ sX) sX i rfl _ (hpp _ _ _ _ _)
      (hpp _ _ _ _ _)]
  refine (chowGroupDegreeEquiv_eq_iff_heq C sX _ _ _).2 ?_
  exact ((chowGroupDegreeEquiv_heq C sX _ _).symm).trans
    ((chowGroupDegreeEquiv_heq C sX _ _).symm)

end Main

end Stacks.Chow

end
