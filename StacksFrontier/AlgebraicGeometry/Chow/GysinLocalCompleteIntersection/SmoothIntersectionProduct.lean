module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalIso
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.Factorization
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.GysinMap
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.GysinMapCommutes
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.SelfIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic

/-!
# The Gysin map of a morphism of smooth schemes and the intersection product

Let `k` be a field and let `f : X ⟶ Y` be a morphism of schemes smooth over `k`. Then `f` is a
local complete intersection morphism for which the Gysin map exists (Stacks 069M, Stacks 0FF3),
so it has a Gysin map `f^! ∈ A^*(X ⟶ Y)^∧`, and both `X` and `Y` carry the intersection product
`α · β = Δ^!(α × β)` of Stacks 0FC0. Stacks 0FFB and Stacks 0FFC relate the two:

* **Stacks 0FFB.** `f^!(α · β) = f^!α · f^!β` for `α, β ∈ CH_*(Y)`;
* **Stacks 0FFC.** if `f` is proper, `f_*(α · f^!β) = f_*α · β` for `α ∈ CH_*(X)` and
  `β ∈ CH_*(Y)` (the projection formula).

The source reduces to `X` equidimensional of dimension `d` and `Y` equidimensional of dimension
`e`, where `f^!` has degree `e - d`, and argues as follows. By Stacks 0FC2 the map
`A^p(Y) ⟶ CH_{e-p}(Y)`, `c ↦ c ∩ [Y]_e`, is an isomorphism carrying composition to the
intersection product, so `α = c ∩ [Y]_e` and `α · β = c ∩ β`; by Stacks 0FF6 the class `f^!`
commutes with `c`; and by Stacks 0FF7 `f^![Y]_e = [X]_d`. Hence

  `f^!(α · β) = f^!(c ∩ β) = res(c) ∩ f^!β = (res(c) ∩ [X]_d) · f^!β = f^!α · f^!β`,

the last step because `f^!α = f^!(c ∩ [Y]_e) = res(c) ∩ f^![Y]_e = res(c) ∩ [X]_d`. For
Stacks 0FFC one writes `β = c ∩ [Y]_e`, so `f^!β = res(c) ∩ [X]_d`, and then
`α · f^!β = res(c) ∩ α` by Stacks 0FC2 for `X` and the symmetry of the product, so that
`f_*(α · f^!β) = f_*(res(c) ∩ α) = c ∩ f_*α = β · f_*α`, the middle step being the
proper-pushforward law of the bivariant class `c`.

This file carries out both arguments in the equidimensional case, first for an arbitrary class
`F ∈ A^{e-d}(X ⟶ Y)` with the two properties of `f^!` that they use
(`Stacks.Chow.BivariantClass.capTargetHom_selfIntersectionProduct`,
`Stacks.Chow.BivariantClass.properChowPushforward_selfIntersectionProduct_capTargetHom`), then for
`f^!` itself, where Stacks 0FF6 is proved (`Stacks.Chow.smoothGysinClass_bivariantCommute`) and
the instances of Stacks 0FF7 and 0FC2 (and the symmetry of the product) are taken as hypotheses.

## Main definitions

* `Stacks.Chow.lciGysinMapComponent` — the degree `q` part `f^! ∈ A^q(X ⟶ Y)` of the Gysin map of
  Stacks 0FF3 of a local complete intersection morphism, read in `∏_p A^p(X ⟶ Y)` through
  Stacks 0FE0.
* `Stacks.Chow.lciGysinChow` — the Gysin map `f^! : CH_n(Y) ⟶ CH_{n-q}(X)` in degree `q`.
* `Stacks.Chow.chowCohomologyRestrictionOfEq` — the restriction `res : A^p(Y) ⟶ A^p(X)` along
  `f : X ⟶ Y` of Stacks 0B7F, read over the structure morphism of `X`.
* `Stacks.Chow.smoothGysinClass`, `Stacks.Chow.smoothGysinChow` — the same two for a morphism of
  schemes smooth over the base, where the local complete intersection property and the existence
  of the Gysin map are theorems.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_smooth_of_smooth` — a morphism of
  schemes smooth over a common base is a local complete intersection morphism.
* `Stacks.Chow.chowCohomologyCap_properChowPushforward_restriction` — the projection formula
  `c ∩ f_*γ = f_*(res(c) ∩ γ)` for a proper `f` and `c ∈ A^p(Y)`.
* `Stacks.Chow.BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute` — if a class
  `F ∈ A^q(X ⟶ Y)` commutes with `c ∈ A^p(Y)` in the sense of Stacks 0FA2, then
  `F ∩ (c ∩ β) = res(c) ∩ (F ∩ β)` on `CH_*(Y)`.
* `Stacks.Chow.smoothGysinChow_selfIntersectionProduct` — **Stacks 0FFB**, equidimensional case:
  `f^!(α · β) = f^!α · f^!β`.
* `Stacks.Chow.properChowPushforward_selfIntersectionProduct_smoothGysinChow` —
  **Stacks 0FFC**, equidimensional case: `f_*(α · f^!β) = f_*α · β`.

## Implementation notes

### The hypotheses

The main theorems take as hypotheses exactly the statements of other tags that the source's
argument cites, each in the shape in which this repository states (part of) that tag, and none
of them about the Gysin map applied to an intersection product:

* `h0FF7` — **Stacks 0FF7** at `Y' = Y`: `f^![Y]_e = [X]_{e-(e-d)}`, the fundamental class of
  `X` in degree `d` written as the degree `f^!` produces. It is the shape of
  `Stacks.Chow.lciGysinCap_fundamentalChowClass_id`.
* `h0FF6` (the theorems for an arbitrary `F` only) — **Stacks 0FF6** at `Y'' = Y' = Y`: `F`
  commutes, in the sense of Stacks 0FA2 (`Stacks.Chow.BivariantCommute`), with every
  `c ∈ A^p(Y)`. For `F = f^!` it is proved, `Stacks.Chow.smoothGysinClass_bivariantCommute`. Its
  consequence on `CH_*(Y)`, `F ∩ (c ∩ β) = res(c) ∩ (F ∩ β)`, is
  `Stacks.Chow.BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute`.
* `h0FC2Y_surjective` — the surjective half of the first clause of **Stacks 0FC2** for `Y`:
  `Stacks.Chow.chowCohomologyCapFundamentalClass`, `c ↦ c ∩ [Y]_e`, is onto in every degree.
* `h0FC2Y_cap`, `h0FC2X_cap` — the second clause of **Stacks 0FC2** for `Y` and for `X`, in the
  form `c ∩ β = (c ∩ [Y]_e) · β` of the action of `A^p(Y)` on `CH_*(Y)`; this is the shape of
  `Stacks.Chow.chowCohomologyCap_eq_intersectionProduct`, which proves it for a class of the
  diagonal with the two properties of Stacks 0FBP and Stacks 0FBS.
* `h0FC0X_comm`, `h0FC0Y_comm` (Stacks 0FFC only) — the symmetry `α · β = β · α` of the
  intersection product, which Stacks 0FC0 records as clear and which the source's proof of
  Stacks 0FFC invokes ("the commutativity of the intersection product").

The intersection products are `Stacks.Chow.selfIntersectionProduct`, formed with classes `DX`
and `DY` of the diagonals of `X` and `Y` in degrees `d` and `e`, carried as arguments as that
definition carries them.

### What is not carried out

The source's first step — the decomposition of `X` and `Y` into connected components, after
which both are equidimensional — is not carried out: a single-degree Chow group cannot express
the general statement, and the equidimensionality enters only through the degrees `d` and `e`
at which the hypotheses above are stated. Nor is Stacks 0FC2's injectivity used: only
surjectivity, on `Y`, enters.

### The degree of `f^!`

The Gysin map `Stacks.Chow.lciGysinMap` lies in the completed group `A^*(X ⟶ Y)^∧` of Stacks 0FE0,
whose degree support is finite on each connected component of `X` but not uniformly. Its degree `q`
part is read through `Stacks.Chow.completedBivariantSequenceOfInvertible`, the embedding
`A^*(X ⟶ Y)^∧ ⟶ ∏_q A^q(X ⟶ Y)` of Stacks 0FE0, and acts on `CH_*(Y)` by
`Stacks.Chow.BivariantClass.capTarget`. In the equidimensional case `f^!` has degree `e - d` (the
rank `e` of the normal sheaf of the graph `X ⟶ X ×_k Y` minus the relative dimension `d` of the
projection to `Y`), and its part of that degree is the one used.

## References

* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 069M](https://stacks.math.columbia.edu/tag/069M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- **Stacks 069M with Stacks 069K.** A morphism `f : X ⟶ Y` of schemes smooth over a common base
`S` is a local complete intersection morphism: the composite `X ⟶ Y ⟶ S` is smooth, hence
syntomic, hence a local complete intersection morphism, and Stacks 069M descends this to `f`
along the smooth morphism `Y ⟶ S`. -/
theorem AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_smooth_of_smooth
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (sY : Y ⟶ S) [Smooth sY] (sX : X ⟶ S) [Smooth sX]
    (hf : f ≫ sY = sX) : IsLocalCompleteIntersectionMorphism f :=
  isLocalCompleteIntersectionMorphism_of_comp_of_smooth f sY
    (hf ▸ isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_smooth sX))

namespace Stacks.Chow

/-! ### The Gysin map in a single degree, and the restriction of Chow cohomology -/

section Gysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- The degree `q` part `f^! ∈ A^q(X ⟶ Y)` of the Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3
of a local complete intersection morphism for which the Gysin map exists: its image under the
embedding `A^*(X ⟶ Y)^∧ ⟶ ∏_q A^q(X ⟶ Y)` of Stacks 0FE0, at the coordinate `q`. -/
abbrev lciGysinMapComponent (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)
    (q : ℤ) : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf q :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  completedBivariantSequenceOfInvertible C sX sY f hf (lciGysinMap C sX sY hf hlci h) q

/-- The Gysin map `f^! : CH_n(Y) ⟶ CH_{n-q}(X)` in degree `q` of a local complete intersection
morphism for which the Gysin map exists: cap product of `Stacks.Chow.lciGysinMapComponent` with a
class on its own target, read on `X`. -/
abbrev lciGysinChow (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)
    (q n : ℤ) : chowGroup C sY n →+ chowGroup C sX (n - q) :=
  (lciGysinMapComponent C sX sY hf hlci h q).capTargetHom C (gysinSystemOfInvertible C) sX sY f hf
    q n

/-- **Stacks 0B7F.** The restriction map `res : A^p(Y) ⟶ A^p(X)` along `f : X ⟶ Y`,
`Stacks.Chow.chowCohomologyRestriction`, read over the structure morphism `sX` of `X` rather than
over `f ≫ sY`. -/
abbrev chowCohomologyRestrictionOfEq (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso)
    (p : ℤ) : chowCohomologyComponent C G sY p →+ chowCohomologyComponent C G sX p :=
  (bivariantClassCongrBase C G (𝟙 X) hf hf p).toAddMonoidHom.comp
    (chowCohomologyRestriction C G sY f p hgys)

end Gysin

section Smooth

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [Smooth sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [Smooth sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- The degree `q` part of the Gysin map of a morphism `f : X ⟶ Y` of schemes smooth over the
base: `Stacks.Chow.lciGysinMapComponent`, with `f` a local complete intersection morphism by
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_smooth_of_smooth` and the Gysin map
existing by `Stacks.Chow.GysinMapExists.of_smooth_source`. -/
abbrev smoothGysinClass (q : ℤ) : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf q :=
  lciGysinMapComponent C sX sY hf
    (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf)
    (GysinMapExists.of_smooth_source f sY sX hf) q

/-- The Gysin map `f^! : CH_n(Y) ⟶ CH_{n-q}(X)` in degree `q` of a morphism of schemes smooth over
the base: `Stacks.Chow.lciGysinChow`, with both of its side conditions discharged as in
`Stacks.Chow.smoothGysinClass`. -/
abbrev smoothGysinChow (q n : ℤ) : chowGroup C sY n →+ chowGroup C sX (n - q) :=
  lciGysinChow C sX sY hf (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf)
    (GysinMapExists.of_smooth_source f sY sX hf) q n

end Smooth

/-! ### The projection formula for a class of `A^p(Y)` -/

section Projection

variable (C : ChowSituation.{u}) (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso)
  {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] [IsProper f]
  (hf : f ≫ sY = sX) (p : ℤ)

/-- **The projection formula for Chow cohomology.** For a proper morphism `f : X ⟶ Y`, a class
`c ∈ A^p(Y)` and `γ ∈ CH_k(X)`,

  `c ∩ f_*γ = f_*(res(c) ∩ γ)`   in   `CH_{k-p}(Y)`,

where `res(c) ∈ A^p(X)` is the restriction of Stacks 0B7F. Both sides are `c ∩ γ` formed at the
test scheme `f : X ⟶ Y` and pushed forward to `Y`: the left by the proper-pushforward law of `c`,
Stacks 0B76 (1), the right by the cap formula of the restriction. -/
theorem chowCohomologyCap_properChowPushforward_restriction
    (c : chowCohomologyComponent C G sY p) (k : ℤ) (γ : chowGroup C sX k) :
    chowCohomologyCap C G sY p c k
        (properChowPushforward C sX sY f hf k (properPushforwardDescends C _ _ _ _ _) γ) =
      properChowPushforward C sX sY f hf (k - p) (properPushforwardDescends C _ _ _ _ _)
        (chowCohomologyCap C G sX p (chowCohomologyRestrictionOfEq C sX sY hf G hgys p c) k γ) := by
  subst hf
  have key : ∀ (m : X ⟶ Y) [LocallyOfFiniteType m] [IsProper m], m = f →
      ∀ (α : chowGroup C (m ≫ sY) k), α ≍ γ →
      properChowPushforward C (pullback.fst (𝟙 Y) m ≫ sY) sY (pullback.fst (𝟙 Y) m) rfl (k - p)
          (properPushforwardDescends C _ _ _ _ _) (c.cap m k α) =
        properChowPushforward C (pullback.fst (𝟙 Y) f ≫ sY) sY (pullback.fst (𝟙 Y) f) rfl (k - p)
          (properPushforwardDescends C _ _ _ _ _) (c.cap f k γ) := by
    intro m _ _ hm α hα
    subst hm
    cases hα
    rfl
  have hpp : ProperPushforwardDescends C := properPushforwardDescends C
  -- the left-hand side: the proper-pushforward law of `c` at the test morphism `f`
  have hL : chowCohomologyCap C G sY p c k
        (properChowPushforward C (f ≫ sY) sY f rfl k (hpp _ _ _ _ _) γ) =
      properChowPushforward C (pullback.fst (𝟙 Y) f ≫ sY) sY (pullback.fst (𝟙 Y) f) rfl (k - p)
        (hpp _ _ _ _ _) (c.cap f k γ) := by
    simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
    rw [properChowPushforward_chowGroupCongr C (rfl : f ≫ sY = f ≫ sY)
      (Category.id_comp sY).symm f rfl (by simp) k _ (hpp _ _ _ _ _)]
    rw [show chowGroupCongr C (rfl : f ≫ sY = f ≫ sY) k γ = γ from rfl]
    rw [BivariantClass.cap_properChowPushforward c hpp (𝟙 Y) f f (Category.comp_id f)
      (testBaseChangeMapOfEq (𝟙 Y) (𝟙 Y) f f (Category.comp_id f))
      (testBaseChangeMapOfEq_fst _ _ _ _ _) (testBaseChangeMapOfEq_snd _ _ _ _ _) k γ]
    rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _ _ _ _ (hpp _ _ _ _ _)]
    exact (properChowPushforward_comp_apply C _ _ _ _ _ _
      (testBaseChangeMapOfEq_fst _ _ _ _ _) _ _ _ _ _ _ _ _).symm
  rw [hL]
  -- the right-hand side: the cap formula of the restriction, Stacks 0B7F, at the test scheme `𝟙 X`
  set α := chowGroupCongr C (Category.id_comp (f ≫ sY)).symm k γ
  have hres := chowCohomologyRestriction_cap C G sY f p hgys c (𝟙 X) k α
  have hm : 𝟙 X ≫ f = f := Category.id_comp f
  rw [← key (𝟙 X ≫ f) hm (chowGroupCongr C (Category.assoc (𝟙 X) f sY).symm k α)
    ((chowGroupCongr_heq _ _ _ _).trans (chowGroupCongr_heq _ _ _ _))]
  have hfstsnd : pullback.fst (𝟙 Y) (𝟙 X ≫ f) = pullback.snd (𝟙 Y) (𝟙 X ≫ f) ≫ f := by
    rw [← Category.comp_id (pullback.fst (𝟙 Y) (𝟙 X ≫ f)), pullback.condition, Category.id_comp]
  rw [properChowPushforward_congr C _ _ _ _ hfstsnd rfl (by rw [hfstsnd, Category.assoc]) _ _
    (hpp _ _ _ _ _)]
  rw [properChowPushforward_comp_apply C (pullback.fst (𝟙 Y) (𝟙 X ≫ f) ≫ sY) (f ≫ sY) sY
    (pullback.snd (𝟙 Y) (𝟙 X ≫ f)) f _ rfl (by rw [← Category.assoc, ← hfstsnd]) rfl
    (by rw [hfstsnd, Category.assoc]) _ (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _)]
  refine congrArg (properChowPushforward C (f ≫ sY) sY f rfl (k - p) (hpp _ _ _ _ _)) ?_
  have hR : chowCohomologyCap C G (f ≫ sY) p
        (chowCohomologyRestrictionOfEq C (f ≫ sY) sY rfl G hgys p c) k γ =
      chowPushforwardOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ (f ≫ sY)) (f ≫ sY)
        (pullback.fst (𝟙 X) (𝟙 X)) rfl (k - p)
        ((chowCohomologyRestriction C G sY f p hgys c).cap (𝟙 X) k α) := rfl
  have hfs : pullback.fst (𝟙 X) (𝟙 X) = (identityBaseChangeIso (𝟙 X)).hom := by
    rw [asIso_hom, ← Category.comp_id (pullback.fst (𝟙 X) (𝟙 X)), pullback.condition,
      Category.comp_id]
  rw [hR, chowPushforwardOfIso_congr_apply C _ _ _ _ hfs rfl (by rw [← hfs])]
  refine eq_of_heq ((properChowPushforward_heq_congr_base C (pullback.snd (𝟙 Y) (𝟙 X ≫ f)) rfl
    (Category.id_comp (f ≫ sY)).symm _ (identityBaseChangeIso_hom_comp_base C _ _) rfl _
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) _ _
    HEq.rfl).trans ?_)
  refine HEq.trans (heq_of_eq hres.symm) ?_
  exact chowPushforwardOfIso_heq _ _ _ rfl (Category.id_comp (f ≫ sY)) rfl HEq.rfl

end Projection

/-! ### A class commuting with `c ∈ A^p(Y)`, on the Chow groups of `Y` -/

section Commute

variable (C : ChowSituation.{u}) (G : GysinSystem C) (hgys : G.IsNaturalUnderBaseChangeIso)
  {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p q : ℤ)

/-- **Stacks 0FA2 at the test scheme `Y`.** If `F ∈ A^q(X ⟶ Y)` commutes with `c ∈ A^p(Y)` in
the sense of Stacks 0FA2, then for `β ∈ CH_k(Y)`

  `F ∩ (c ∩ β) = res(c) ∩ (F ∩ β)`   in   `CH_{k-p-q}(X)`,

where `res(c) ∈ A^p(X)` is the restriction of Stacks 0B7F. This is the commutation read at the
test scheme `𝟙 Y`: the two iterated cap operations land on `X ×_Y (Y ×_Y Y)` and
`Y ×_Y (X ×_Y Y)`, and both are carried to `X` — the first by the proper-pushforward law of `F`,
the second by the cap formula of the restriction and the proper-pushforward law of `c`. -/
theorem BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute
    (F : BivariantClass C G sX sY f hf q) (c : chowCohomologyComponent C G sY p)
    (hcomm : BivariantCommute C G sY f (𝟙 Y) q p (bivariantClassCongrBase C G f hf.symm rfl q F)
      (bivariantClassCongrBase C G (𝟙 Y) (Category.id_comp sY).symm rfl p c))
    (k : ℤ) (β : chowGroup C sY k) :
    F.capTarget C G sX sY f hf q (k - p) (chowCohomologyCap C G sY p c k β) =
      chowGroupDegreeEquiv C sX (by ring : k - q - p = k - p - q)
        (chowCohomologyCap C G sX p (chowCohomologyRestrictionOfEq C sX sY hf G hgys p c) (k - q)
          (F.capTarget C G sX sY f hf q k β)) := by
  subst hf
  replace hcomm : BivariantCommute C G sY f (𝟙 Y) q p F
      (bivariantClassCongrBase C G (𝟙 Y) (Category.id_comp sY).symm rfl p c) := hcomm
  show F.capTarget C G (f ≫ sY) sY f rfl q (k - p) (chowCohomologyCap C G sY p c k β) =
      chowGroupDegreeEquiv C (f ≫ sY) (by ring : k - q - p = k - p - q)
        (chowCohomologyCap C G (f ≫ sY) p (chowCohomologyRestriction C G sY f p hgys c) (k - q)
          (F.capTarget C G (f ≫ sY) sY f rfl q k β))
  have hpp : ProperPushforwardDescends C := properPushforwardDescends C
  have hBC := hcomm (𝟙 Y) k (chowGroupCongr C (Category.id_comp sY).symm k β)
  -- the left-hand side is `F ∩ (c ∩ β)`, by the proper-pushforward law of `F`
  have hL : F.capTarget C G (f ≫ sY) sY f rfl q (k - p) (chowCohomologyCap C G sY p c k β) =
      chowPushforwardOfIso C (pullback.fst f (𝟙 Y) ≫ (f ≫ sY)) (f ≫ sY) (pullbackIdIso f).inv
        (pullbackIdIso_inv_comp f (f ≫ sY)) (k - p - q)
        (properChowPushforward C (pullback.fst f (pullback.fst (𝟙 Y) (𝟙 Y) ≫ 𝟙 Y) ≫ (f ≫ sY))
          (pullback.fst f (𝟙 Y) ≫ (f ≫ sY))
          (testBaseChangeMapOfEq f (𝟙 Y) (pullback.fst (𝟙 Y) (𝟙 Y))
            (pullback.fst (𝟙 Y) (𝟙 Y) ≫ 𝟙 Y) rfl)
          (by rw [← Category.assoc, testBaseChangeMapOfEq_fst]) (k - p - q) (hpp _ _ _ _ _)
          (bivariantIteratedCap C G sY f (𝟙 Y) q p F
            (bivariantClassCongrBase C G (𝟙 Y) (Category.id_comp sY).symm rfl p c) (𝟙 Y) k
            (chowGroupCongr C (Category.id_comp sY).symm k β))) := by
    simp only [BivariantClass.capTarget, chowCohomologyCap, AddMonoidHom.coe_comp,
      Function.comp_apply, AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
    congr 1
    rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _ _ _ _ (hpp _ _ _ _ _),
      properChowPushforward_chowGroupCongr C
        (show pullback.fst (𝟙 Y) (𝟙 Y) ≫ sY = (pullback.fst (𝟙 Y) (𝟙 Y) ≫ 𝟙 Y) ≫ sY by simp)
        (Category.id_comp sY).symm _ rfl (by simp) (k - p) _ (hpp _ _ _ _ _),
      BivariantClass.cap_properChowPushforward F hpp (𝟙 Y) (pullback.fst (𝟙 Y) (𝟙 Y))
        (pullback.fst (𝟙 Y) (𝟙 Y) ≫ 𝟙 Y) rfl
        (testBaseChangeMapOfEq f (𝟙 Y) (pullback.fst (𝟙 Y) (𝟙 Y))
          (pullback.fst (𝟙 Y) (𝟙 Y) ≫ 𝟙 Y) rfl) (testBaseChangeMapOfEq_fst _ _ _ _ _)
        (testBaseChangeMapOfEq_snd _ _ _ _ _) (k - p)]
    rw [bivariantIteratedCap_apply]
    congr 3
  -- the common value: `c ∩ (f^! ∩ β)` read on `X`
  have hw : (pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (pullbackIdIso f).inv) ≫ (f ≫ sY) =
      pullback.fst (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (𝟙 Y ≫ sY) := by
    rw [Category.assoc, pullbackIdIso_inv_comp, ← Category.assoc (pullback.fst f (𝟙 Y)),
      ← Category.assoc, ← pullback.condition, Category.assoc]
  -- the right-hand side, by the cap formula of the restriction and the proper-pushforward law
  -- of `c`
  have hR : chowCohomologyCap C G (f ≫ sY) p (chowCohomologyRestriction C G sY f p hgys c) (k - q)
        (F.capTarget C G (f ≫ sY) sY f rfl q k β) ≍
      chowPushforwardOfIso C (pullback.fst (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (𝟙 Y ≫ sY))
        (f ≫ sY) (pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (pullbackIdIso f).inv) hw
        ((k - q) - p)
        (bivariantIteratedCap C G sY (𝟙 Y) f p q
          (bivariantClassCongrBase C G (𝟙 Y) (Category.id_comp sY).symm rfl p c) F (𝟙 Y) k
          (chowGroupCongr C (Category.id_comp sY).symm k β)) := by
    have hres := chowCohomologyRestriction_cap C G sY f p hgys c (𝟙 X) (k - q)
      (chowGroupCongr C (Category.id_comp (f ≫ sY)).symm (k - q)
        (F.capTarget C G (f ≫ sY) sY f rfl q k β))
    have hfs : pullback.fst (𝟙 X) (𝟙 X) = (identityBaseChangeIso (𝟙 X)).hom := by
      rw [asIso_hom, ← Category.comp_id (pullback.fst (𝟙 X) (𝟙 X)), pullback.condition,
        Category.comp_id]
    simp only [chowCohomologyCap, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, chowGroupEquivOfIso_apply]
    rw [chowPushforwardOfIso_congr_apply C _ _ _ _ hfs rfl (by rw [← hfs])]
    refine (chowPushforwardOfIso_heq _ _ (identityBaseChangeIso_hom_comp_base C _ _) rfl
      (Category.id_comp (f ≫ sY)).symm rfl HEq.rfl).trans ?_
    rw [hres, chowGroupCongr_chowGroupCongr]
    simp only [BivariantClass.capTarget]
    have hinv : (pullbackIdIso f).inv ≫ (𝟙 X ≫ f) = pullback.fst f (𝟙 Y) ≫ f := by
      rw [Category.id_comp, pullbackIdIso_inv_comp]
    rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _ (pullbackIdIso f).inv _ _
        (hpp _ _ _ _ _),
      properChowPushforward_chowGroupCongr C
        (show pullback.fst f (𝟙 Y) ≫ (f ≫ sY) = (pullback.fst f (𝟙 Y) ≫ f) ≫ sY by simp)
        _ (pullbackIdIso f).inv _ (by rw [← Category.assoc, hinv]) (k - q) _ (hpp _ _ _ _ _),
      BivariantClass.cap_properChowPushforward c hpp (𝟙 X ≫ f) (pullbackIdIso f).inv
        (pullback.fst f (𝟙 Y) ≫ f) hinv
        (testBaseChangeMapOfEq (𝟙 Y) (𝟙 X ≫ f) (pullbackIdIso f).inv
          (pullback.fst f (𝟙 Y) ≫ f) hinv) (testBaseChangeMapOfEq_fst _ _ _ _ _)
        (testBaseChangeMapOfEq_snd _ _ _ _ _) (k - q),
      ← properChowPushforward_eq_chowPushforwardOfIso C _ _ (identityBaseChangeIso (𝟙 X ≫ f)).hom
        _ _ (hpp _ _ _ _ _),
      ← properChowPushforward_comp_apply C _ _ _ _ (identityBaseChangeIso (𝟙 X ≫ f)).hom
        (pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (pullbackIdIso f).inv)
        (by rw [asIso_hom, testBaseChangeMapOfEq_snd]) _ _
        (by rw [Category.id_comp, hw, Category.id_comp]) _ _ _ (hpp _ _ _ _ _)]
    refine properChowPushforward_heq_congr_base C _ (by simp) (Category.id_comp (f ≫ sY)) _ _ rfl
      _ _ _ _ ?_
    rw [bivariantIteratedCap_apply]
    exact (bivariantClassCongrBase_cap C G (𝟙 Y) _ _ p c _ (k - q) _ _ HEq.rfl).symm
  -- assemble through the commutation `hBC`
  have hmor : commuteComparisonHom (𝟙 Y) f (𝟙 Y) ≫
      testBaseChangeMapOfEq f (𝟙 Y) (pullback.fst (𝟙 Y) (𝟙 Y)) (pullback.fst (𝟙 Y) (𝟙 Y) ≫ 𝟙 Y)
        rfl = pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, testBaseChangeMapOfEq_fst, commuteComparisonHom_fst]
    · rw [Category.assoc, testBaseChangeMapOfEq_snd, commuteComparisonHom_snd_fst]
      calc pullback.fst (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f)
          = pullback.fst (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ 𝟙 Y := (Category.comp_id _).symm
        _ = pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (pullback.fst f (𝟙 Y) ≫ f) :=
          pullback.condition
        _ = pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (pullback.snd f (𝟙 Y) ≫ 𝟙 Y) :=
          congrArg (pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ ·) pullback.condition
        _ = pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ pullback.snd f (𝟙 Y) := by
          rw [Category.comp_id]
  rw [hL]
  refine HEq.trans ?_ ((chowGroupDegreeEquiv_heq _ _ _ _).trans hR).symm |> eq_of_heq
  rw [← chowPushforwardOfIso_inv_comp C _ _ (commuteComparisonHom f (𝟙 Y) (𝟙 Y))
    (commuteComparisonHom_comp_structureMorphism C sY f (𝟙 Y) (𝟙 Y)) (k - p - q)
    (bivariantIteratedCap C G sY f (𝟙 Y) q p F _ (𝟙 Y) k _), hBC]
  have hw' : (inv (commuteComparisonHom f (𝟙 Y) (𝟙 Y)) ≫
      testBaseChangeMapOfEq f (𝟙 Y) (pullback.fst (𝟙 Y) (𝟙 Y)) (pullback.fst (𝟙 Y) (𝟙 Y) ≫ 𝟙 Y)
        rfl) ≫ (pullback.fst f (𝟙 Y) ≫ (f ≫ sY)) =
      pullback.fst (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (𝟙 Y ≫ sY) := by
    rw [inv_commuteComparisonHom, hmor, ← hw, Category.assoc, pullbackIdIso_inv_comp]
  rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _
      (inv (commuteComparisonHom f (𝟙 Y) (𝟙 Y))) _ _ (hpp _ _ _ _ _),
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _ (pullbackIdIso f).inv _ _
      (hpp _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ _ _ (inv (commuteComparisonHom f (𝟙 Y) (𝟙 Y))) _ _
      rfl _ _ hw' _ _ _ (hpp _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ _ _ _ (pullbackIdIso f).inv
      (pullback.snd (𝟙 Y) (pullback.fst f (𝟙 Y) ≫ f) ≫ (pullbackIdIso f).inv)
      (by rw [inv_commuteComparisonHom, hmor]) _ _ hw _ _ _ (hpp _ _ _ _ _)]
  exact properChowPushforward_heq_congr C _ _ _ hw (by ring) _ _ _ _
    (chowGroupDegreeEquiv_heq _ _ _ _)

end Commute

/-! ### Commuting after every base change implies commuting -/

section AfterBaseChange

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {f : X ⟶ Y} [LocallyOfFiniteType f] {p : ℤ}

/-- Commuting with every class does not depend on the structure morphism of the target. -/
theorem BivariantClass.commutesWithEveryClass_congrTarget {sY sY' : Y ⟶ C.S}
    [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] (e : sY = sY') {hf : f ≫ sY = sX}
    {hf' : f ≫ sY' = sX} (c : BivariantClass C G sX sY f hf p) :
    (bivariantClassCongrBase C G f rfl e (hv := hf) (hv' := hf') p c).CommutesWithEveryClass ↔
      c.CommutesWithEveryClass := by
  subst e
  rfl

variable {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {hf : f ≫ sY = sX}

/-- The restriction of a class along the identity of its target, transported along
`X ×_Y Y ≅ X`, is the class itself, read over `𝟙 Y ≫ s_Y`. -/
theorem bivariantTransport_bivariantRestriction_id (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sX sY f hf p) :
    bivariantTransport C G (pullback.fst f (𝟙 Y) ≫ sX) sX (𝟙 Y ≫ sY) (pullback.snd f (𝟙 Y))
        (pullbackSnd_comp_structureMorphism_eq C sX sY f hf (𝟙 Y)) f
        (by rw [Category.id_comp, hf]) (asIso (pullback.fst f (𝟙 Y)))
        (by rw [asIso_hom, pullback.condition, Category.comp_id]) p hgys
        (bivariantRestriction C G sX sY f hf (𝟙 Y) p hgys c) =
      bivariantClassCongrBase C G f rfl (Category.id_comp sY).symm (hv := hf)
        (hv' := by rw [Category.id_comp, hf]) p c := by
  refine BivariantClass.ext _ _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  have hR := bivariantClassCongrBase_cap C G f rfl (Category.id_comp sY).symm (hv := hf)
    (hv' := by rw [Category.id_comp, hf]) p c t k
    (chowGroupCongr C (by rw [Category.id_comp]) k α) α (chowGroupCongr_heq C _ k α)
  refine Eq.trans ?_ (eq_of_heq hR).symm
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, chowPushforwardOfIso_comp_apply]
  have e : t ≫ 𝟙 Y = t := Category.comp_id t
  rw [← chowPushforwardOfIso_congrHom_cap C G sX sY f hf p c e (by simp) k α
    (by rw [Category.assoc]) (by rw [Category.id_comp])]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (by ext <;> simp [transportPullbackIso]) _ _ _ _

/-- **A class commuting with every class after every base change commutes with every class**:
its restriction along the identity of its target is the class itself. -/
theorem BivariantClass.CommutesAfterBaseChange.commutesWithEveryClass
    {c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p}
    (hc : c.CommutesAfterBaseChange) : c.CommutesWithEveryClass := by
  have h1 := BivariantClass.CommutesWithEveryClass.bivariantTransport (sW := 𝟙 Y ≫ sY)
    (hu := by rw [Category.id_comp, hf]) (asIso (pullback.fst f (𝟙 Y)))
    (by rw [asIso_hom, pullback.condition, Category.comp_id]) (hc (𝟙 Y))
  rw [bivariantTransport_bivariantRestriction_id] at h1
  exact (BivariantClass.commutesWithEveryClass_congrTarget _ _).1 h1

end AfterBaseChange

/-- Stacks 0FF6 on `CH_*(Y)`: `F ∩ (c ∩ β) = res(c) ∩ (F ∩ β)` for `F` commuting with `c`. -/
private theorem capTargetHom_chowCohomologyCap_restriction
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (d e : ℤ)
    (F : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (e - d))
    (h0FF6 : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p),
      BivariantCommute C (gysinSystemOfInvertible C) sY f (𝟙 Y) (e - d) p
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) f hf.symm rfl (e - d)
          F)
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y) (Category.id_comp sY).symm
          rfl p c))
    (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (m : ℤ) (β : chowGroup C sY m) :
    F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) (m - p)
        (chowCohomologyCap C (gysinSystemOfInvertible C) sY p c m β) =
      chowGroupDegreeEquiv C sX (by ring : m - (e - d) - p = m - p - (e - d))
        (chowCohomologyCap C (gysinSystemOfInvertible C) sX p
          (chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c) (m - (e - d))
          (F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) m β)) :=
  BivariantClass.capTarget_chowCohomologyCap_of_bivariantCommute C
    (gysinSystemOfInvertible C) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) sX sY f
    hf p (e - d) _ c (h0FF6 p c) m β

/-- Stacks 0FF6 and 0FF7: `F ∩ (c ∩ [Y]_e) = res(c) ∩ [X]_d`. -/
private theorem capTargetHom_chowCohomologyCapFundamentalClass
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (d e : ℤ)
    (F : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (e - d))
    (h0FF7 : F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) e
        (fundamentalChowClass C sY e) =
      fundamentalChowClass C sX (e - (e - d)))
    (h0FF6 : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p),
      BivariantCommute C (gysinSystemOfInvertible C) sY f (𝟙 Y) (e - d) p
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) f hf.symm rfl (e - d)
          F)
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y) (Category.id_comp sY).symm
          rfl p c))
    (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) (e - p)
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p c) ≍
      chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p
        (chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c) := by
  have congrCapFund : ∀ {k k' : ℤ}, k = k' →
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p
          (chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c) k
          (fundamentalChowClass C sX k) ≍
        chowCohomologyCap C (gysinSystemOfInvertible C) sX p
          (chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c) k'
          (fundamentalChowClass C sX k') := by
    rintro k k' rfl
    rfl
  rw [← chowCohomologyCap_fundamentalChowClass C (gysinSystemOfInvertible C) sY p c e,
    capTargetHom_chowCohomologyCap_restriction C sX sY hf d e F h0FF6 p c e, h0FF7,
    ← chowCohomologyCap_fundamentalChowClass C (gysinSystemOfInvertible C) sX p _ d]
  exact (chowGroupDegreeEquiv_heq _ _ _ _).trans (congrCapFund (by ring))

/-- The intersection product on `X` respects heterogeneous equality of its arguments. -/
private theorem selfIntersectionProduct_heq_congr (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (d : ℤ)
    (DX : BivariantClass C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
      (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) d)
    {k k' l l' : ℤ} (hk : k = k') (hl : l = l')
    {x : chowGroup C sX k} {x' : chowGroup C sX k'} {y : chowGroup C sX l}
    {y' : chowGroup C sX l'} (hx : x ≍ x') (hy : y ≍ y') :
    selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX k l x y ≍
      selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX k' l' x' y' := by
  subst hk hl
  cases hx
  cases hy
  rfl

/-! ### Stacks 0FFB and Stacks 0FFC -/

section Product

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Smooth sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [Smooth sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (d e : ℤ)
  (DX : BivariantClass C (gysinSystemOfInvertible C) sX (selfProductStructure C sX)
    (pullback.diagonal sX) (diagonal_comp_selfProductStructure C sX) d)
  (DY : BivariantClass C (gysinSystemOfInvertible C) sY (selfProductStructure C sY)
    (pullback.diagonal sY) (diagonal_comp_selfProductStructure C sY) e)

omit [Smooth sX] [Smooth sY] in
/-- **The argument of Stacks 0FFB, for an arbitrary class `F ∈ A^{e-d}(X ⟶ Y)`.** Let the
intersection products of Stacks 0FC0 on `X` and on `Y` be formed with the classes `DX` and `DY` of
the diagonals, in degrees `d` and `e`. If `F ∩ [Y]_e = [X]_d` (`h0FF7`), `F` commutes with every
`c ∈ A^p(Y)` (`h0FF6`), and the two clauses of Stacks 0FC2 hold on `Y` and the second on `X`
(`h0FC2Y_surjective`, `h0FC2Y_cap`, `h0FC2X_cap`), then `F ∩ (α · β) = (F ∩ α) · (F ∩ β)`.

This is the source's proof of Stacks 0FFB, which uses of the Gysin map `f^!` only these two
properties. It applies to `f^!` (`Stacks.Chow.smoothGysinChow_selfIntersectionProduct`) and to the
flat pullback class of Stacks 0B78 of a flat morphism. -/
theorem BivariantClass.capTargetHom_selfIntersectionProduct
    (F : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (e - d))
    (h0FF7 : F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) e
        (fundamentalChowClass C sY e) =
      fundamentalChowClass C sX (e - (e - d)))
    (h0FF6 : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p),
      BivariantCommute C (gysinSystemOfInvertible C) sY f (𝟙 Y) (e - d) p
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) f hf.symm rfl (e - d)
          F)
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y) (Category.id_comp sY).symm
          rfl p c))
    (h0FC2Y_surjective : ∀ p : ℤ,
      Function.Surjective (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p))
    (h0FC2Y_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
      (m : ℤ) (β : chowGroup C sY m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sY p c m β =
        chowGroupDegreeEquiv C sY (by ring : (e - p) + m - e = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY (e - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p c) β))
    (h0FC2X_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
      (m : ℤ) (γ : chowGroup C sX m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p c m γ =
        chowGroupDegreeEquiv C sX (by ring : (d - p) + m - d = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX (d - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p c) γ))
    (n m : ℤ) (α : chowGroup C sY n) (β : chowGroup C sY m) :
    F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) (n + m - e)
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY n m α β) =
      chowGroupDegreeEquiv C sX
        (by ring : (n - (e - d)) + (m - (e - d)) - d = n + m - e - (e - d))
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX (n - (e - d))
          (m - (e - d)) (F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) n α)
          (F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) m β)) := by
  have congrGysin : ∀ {k k' : ℤ}, k = k' → ∀ {x : chowGroup C sY k} {x' : chowGroup C sY k'},
      x ≍ x' →
        F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) k x ≍
          F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) k' x' := by
    intro k k' hk x x' hx
    subst hk
    cases hx
    rfl
  obtain ⟨p, rfl⟩ : ∃ p, n = e - p := ⟨e - n, by ring⟩
  obtain ⟨c, rfl⟩ := h0FC2Y_surjective p α
  -- `f^!α = res(c) ∩ [X]_d`, by Stacks 0FF6 and Stacks 0FF7
  have hα := capTargetHom_chowCohomologyCapFundamentalClass C sX sY hf d e F h0FF7 h0FF6 p c
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  have h1 : selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY (e - p) m
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p c) β ≍
      chowCohomologyCap C (gysinSystemOfInvertible C) sY p c m β := by
    rw [h0FC2Y_cap p c m β]
    exact (chowGroupDegreeEquiv_heq _ _ _ _).symm
  refine (congrGysin (by ring) h1).trans ?_
  rw [capTargetHom_chowCohomologyCap_restriction C sX sY hf d e F h0FF6 p c m β,
    h0FC2X_cap p _]
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
  exact selfIntersectionProduct_heq_congr C hδ sX d DX (by ring) rfl hα.symm HEq.rfl

omit [Smooth sX] [Smooth sY] in
/-- **The argument of Stacks 0FFC, for an arbitrary class `F ∈ A^{e-d}(X ⟶ Y)` of a proper
morphism.** Under the hypotheses of
`Stacks.Chow.BivariantClass.capTargetHom_selfIntersectionProduct` together with the symmetry of the
two products, `f_*(α · (F ∩ β)) = f_*α · β`.

This is the source's proof of Stacks 0FFC, which uses of the Gysin map `f^!` only the two
properties `F ∩ [Y]_e = [X]_d` and that `F` commutes with every `c ∈ A^p(Y)`. It applies to `f^!`
(`Stacks.Chow.properChowPushforward_selfIntersectionProduct_smoothGysinChow`) and to the flat
pullback class of Stacks 0B78 of a flat proper morphism. -/
theorem BivariantClass.properChowPushforward_selfIntersectionProduct_capTargetHom [IsProper f]
    (F : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf (e - d))
    (h0FF7 : F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) e
        (fundamentalChowClass C sY e) =
      fundamentalChowClass C sX (e - (e - d)))
    (h0FF6 : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p),
      BivariantCommute C (gysinSystemOfInvertible C) sY f (𝟙 Y) (e - d) p
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) f hf.symm rfl (e - d)
          F)
        (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y) (Category.id_comp sY).symm
          rfl p c))
    (h0FC2Y_surjective : ∀ p : ℤ,
      Function.Surjective (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p))
    (h0FC2Y_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
      (m : ℤ) (β : chowGroup C sY m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sY p c m β =
        chowGroupDegreeEquiv C sY (by ring : (e - p) + m - e = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY (e - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p c) β))
    (h0FC2X_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
      (m : ℤ) (γ : chowGroup C sX m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p c m γ =
        chowGroupDegreeEquiv C sX (by ring : (d - p) + m - d = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX (d - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p c) γ))
    (h0FC0X_comm : ∀ (k l : ℤ) (x : chowGroup C sX k) (y : chowGroup C sX l),
      selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX k l x y =
        chowGroupDegreeEquiv C sX (by ring : l + k - d = k + l - d)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX l k y x))
    (h0FC0Y_comm : ∀ (k l : ℤ) (x : chowGroup C sY k) (y : chowGroup C sY l),
      selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY k l x y =
        chowGroupDegreeEquiv C sY (by ring : l + k - e = k + l - e)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY l k y x))
    (n m : ℤ) (α : chowGroup C sX n) (β : chowGroup C sY m) :
    properChowPushforward C sX sY f hf (n + (m - (e - d)) - d)
        (properPushforwardDescends C _ _ _ _ _)
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX n (m - (e - d)) α
          (F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) m β)) =
      chowGroupDegreeEquiv C sY (by ring : n + m - e = n + (m - (e - d)) - d)
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY n m
          (properChowPushforward C sX sY f hf n (properPushforwardDescends C _ _ _ _ _) α) β) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = e - p := ⟨e - m, by ring⟩
  obtain ⟨c, rfl⟩ := h0FC2Y_surjective p β
  -- `f^!β = res(c) ∩ [X]_d`, by Stacks 0FF6 and Stacks 0FF7
  have hβ := capTargetHom_chowCohomologyCapFundamentalClass C sX sY hf d e F h0FF7 h0FF6 p c
  -- `α · f^!β = res(c) ∩ α`, by the symmetry of the product and Stacks 0FC2 on `X`
  have h1 : selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX n (e - p - (e - d))
      α
      (F.capTargetHom C (gysinSystemOfInvertible C) sX sY f hf (e - d) (e - p)
        (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p c)) ≍
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p
        (chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p c) n α := by
    refine (selfIntersectionProduct_heq_congr C hδ sX d DX rfl (by ring) HEq.rfl hβ).trans ?_
    rw [h0FC0X_comm, h0FC2X_cap p _ n α]
    exact (chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _).symm
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm)
  refine (properChowPushforward_heq_congr C sX sY f hf (by ring) _
    (properPushforwardDescends C _ _ _ _ _) _ _ h1).trans ?_
  rw [← chowCohomologyCap_properChowPushforward_restriction C (gysinSystemOfInvertible C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) sX sY hf p c n α, h0FC2Y_cap,
    h0FC0Y_comm]
  exact (chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _)

omit [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S] in
/-- **Stacks 0FF6 for a morphism of smooth schemes**, in the form the arguments of Stacks 0FFB and
Stacks 0FFC consume: every degree of the Gysin map `f^!` commutes with every `c ∈ A^p(Y)`. The
Gysin map commutes with every class after every base change
(`Stacks.Chow.completedCommutesAfterBaseChange_lciGysinMap`), so in particular with every class. -/
theorem smoothGysinClass_bivariantCommute (q p : ℤ)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    BivariantCommute C (gysinSystemOfInvertible C) sY f (𝟙 Y) q p
      (bivariantClassCongrBase C (gysinSystemOfInvertible C) f hf.symm rfl q
        (smoothGysinClass C sX sY hf q))
      (bivariantClassCongrBase C (gysinSystemOfInvertible C) (𝟙 Y) (Category.id_comp sY).symm
        rfl p c) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  (completedCommutesAfterBaseChange_lciGysinMap C sX sY hf
    (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth f sY sX hf)
    (GysinMapExists.of_smooth_source f sY sX hf) q).commutesWithEveryClass (𝟙 Y) p _

/-- **Stacks 0FFB, the equidimensional case: `f^!(α · β) = f^!α · f^!β`.** Let `f : X ⟶ Y` be a
morphism of schemes smooth over the base, with `X` of dimension `d` and `Y` of dimension `e`, so
that the Gysin map `f^!` of Stacks 0FF3 (which exists) has degree `e - d`, and let the
intersection products of Stacks 0FC0 on `X` and on `Y` be formed with the classes `DX` and `DY`
of the diagonals. Then for `α ∈ CH_n(Y)` and `β ∈ CH_m(Y)`

  `f^!(α · β) = f^!α · f^!β`   in   `CH_{n+m-e-(e-d)}(X)`,

granted the following instances of other tags, which is where the dimensions enter (that `f^!`
commutes with every `c ∈ A^p(Y)`, Stacks 0FF6, is `Stacks.Chow.smoothGysinClass_bivariantCommute`):

* `h0FF7`, Stacks 0FF7: `f^![Y]_e = [X]_d`;
* `h0FC2Y_surjective`, Stacks 0FC2 for `Y`: every class of `CH_*(Y)` is `c ∩ [Y]_e`;
* `h0FC2Y_cap`, `h0FC2X_cap`, Stacks 0FC2 for `Y` and `X`: `c ∩ β = (c ∩ [Y]_e) · β`, and the
  same on `X` with `[X]_d`.

The proof is the source's: writing `α = c ∩ [Y]_e`, one has `α · β = c ∩ β`, so
`f^!(α · β) = res(c) ∩ f^!β = (res(c) ∩ [X]_d) · f^!β`, and `res(c) ∩ [X]_d = f^!α`. -/
theorem smoothGysinChow_selfIntersectionProduct
    (h0FF7 : smoothGysinChow C sX sY hf (e - d) e (fundamentalChowClass C sY e) =
      fundamentalChowClass C sX (e - (e - d)))
    (h0FC2Y_surjective : ∀ p : ℤ,
      Function.Surjective (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p))
    (h0FC2Y_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
      (m : ℤ) (β : chowGroup C sY m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sY p c m β =
        chowGroupDegreeEquiv C sY (by ring : (e - p) + m - e = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY (e - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p c) β))
    (h0FC2X_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
      (m : ℤ) (γ : chowGroup C sX m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p c m γ =
        chowGroupDegreeEquiv C sX (by ring : (d - p) + m - d = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX (d - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p c) γ))
    (n m : ℤ) (α : chowGroup C sY n) (β : chowGroup C sY m) :
    smoothGysinChow C sX sY hf (e - d) (n + m - e)
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY n m α β) =
      chowGroupDegreeEquiv C sX
        (by ring : (n - (e - d)) + (m - (e - d)) - d = n + m - e - (e - d))
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX (n - (e - d))
          (m - (e - d)) (smoothGysinChow C sX sY hf (e - d) n α)
          (smoothGysinChow C sX sY hf (e - d) m β)) :=
  BivariantClass.capTargetHom_selfIntersectionProduct C hδ sX sY hf d e DX DY
    (smoothGysinClass C sX sY hf (e - d)) h0FF7
    (smoothGysinClass_bivariantCommute C sX sY hf (e - d)) h0FC2Y_surjective h0FC2Y_cap h0FC2X_cap
    n m α β

/-- **Stacks 0FFC, the equidimensional case: the projection formula
`f_*(α · f^!β) = f_*α · β`.** Let `f : X ⟶ Y` be a proper morphism of schemes smooth over the
base, with `X` of dimension `d` and `Y` of dimension `e`, so that the Gysin map `f^!` of
Stacks 0FF3 (which exists) has degree `e - d`, and let the intersection products of Stacks 0FC0
on `X` and on `Y` be formed with the classes `DX` and `DY` of the diagonals. Then for
`α ∈ CH_n(X)` and `β ∈ CH_m(Y)`

  `f_*(α · f^!β) = f_*α · β`   in   `CH_{n+m-e}(Y)`,

granted the instances `h0FF7`, `h0FC2Y_surjective`, `h0FC2Y_cap` and `h0FC2X_cap` of
Stacks 0FF7 and 0FC2 described at `Stacks.Chow.smoothGysinChow_selfIntersectionProduct`,
together with the symmetry `h0FC0X_comm`, `h0FC0Y_comm` of the two intersection products, which
the source's proof invokes.

The proof is the source's: writing `β = c ∩ [Y]_e`, one has `f^!β = res(c) ∩ [X]_d`, so
`α · f^!β = res(c) ∩ α`; then `f_*(res(c) ∩ α) = c ∩ f_*α` by
`Stacks.Chow.chowCohomologyCap_properChowPushforward_restriction`, which is `β · f_*α`. -/
theorem properChowPushforward_selfIntersectionProduct_smoothGysinChow [IsProper f]
    (h0FF7 : smoothGysinChow C sX sY hf (e - d) e (fundamentalChowClass C sY e) =
      fundamentalChowClass C sX (e - (e - d)))
    (h0FC2Y_surjective : ∀ p : ℤ,
      Function.Surjective (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p))
    (h0FC2Y_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
      (m : ℤ) (β : chowGroup C sY m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sY p c m β =
        chowGroupDegreeEquiv C sY (by ring : (e - p) + m - e = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY (e - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sY e p c) β))
    (h0FC2X_cap : ∀ (p : ℤ) (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
      (m : ℤ) (γ : chowGroup C sX m),
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p c m γ =
        chowGroupDegreeEquiv C sX (by ring : (d - p) + m - d = m - p)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX (d - p) m
            (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p c) γ))
    (h0FC0X_comm : ∀ (k l : ℤ) (x : chowGroup C sX k) (y : chowGroup C sX l),
      selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX k l x y =
        chowGroupDegreeEquiv C sX (by ring : l + k - d = k + l - d)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX l k y x))
    (h0FC0Y_comm : ∀ (k l : ℤ) (x : chowGroup C sY k) (y : chowGroup C sY l),
      selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY k l x y =
        chowGroupDegreeEquiv C sY (by ring : l + k - e = k + l - e)
          (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY l k y x))
    (n m : ℤ) (α : chowGroup C sX n) (β : chowGroup C sY m) :
    properChowPushforward C sX sY f hf (n + (m - (e - d)) - d)
        (properPushforwardDescends C _ _ _ _ _)
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sX d DX n (m - (e - d)) α
          (smoothGysinChow C sX sY hf (e - d) m β)) =
      chowGroupDegreeEquiv C sY (by ring : n + m - e = n + (m - (e - d)) - d)
        (selfIntersectionProduct C hδ (gysinSystemOfInvertible C) sY e DY n m
          (properChowPushforward C sX sY f hf n (properPushforwardDescends C _ _ _ _ _) α) β) :=
  BivariantClass.properChowPushforward_selfIntersectionProduct_capTargetHom C hδ sX sY hf d e
    DX DY (smoothGysinClass C sX sY hf (e - d)) h0FF7
    (smoothGysinClass_bivariantCommute C sX sY hf (e - d)) h0FC2Y_surjective h0FC2Y_cap
    h0FC2X_cap h0FC0X_comm h0FC0Y_comm n m α β

end Product

end Stacks.Chow

end
