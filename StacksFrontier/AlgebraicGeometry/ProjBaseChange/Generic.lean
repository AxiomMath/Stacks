module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Charts of a morphism of projective spectra, and gluing isomorphy

This file isolates the two scheme-level mechanisms that the comparison of the two models of
projective space needs, both stated for an arbitrary graded ring homomorphism.

The first is that the standard affine chart of the source of `AlgebraicGeometry.Proj.map` is the
fibre product of `Proj` of the source with the standard affine chart of the target: the chart
square is a pullback square. The second is the gluing principle: a morphism whose base change
along each member of an open cover of the target is an isomorphism is an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.ProjBaseChange.ι_comp_projMap`: `AlgebraicGeometry.Proj.map`
  restricted to the Tag 01MY domain of definition is
  `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`. Together with
  `Stacks.AlgebraicGeometry.ProjBaseChange.mapHom_eq_projMap` this identifies the morphism this
  repository builds on the domain of definition with Mathlib's, whenever the latter exists.
* `Stacks.AlgebraicGeometry.ProjBaseChange.awayι_comp_projMap`: the chart square of
  `AlgebraicGeometry.Proj.map` commutes. The map of degree-zero localizations is not required to
  be `HomogeneousLocalization.Away.map` on the nose: it is specified by its values on fractions,
  and the image of the homogeneous element is an independent variable, so that a *different*
  spelling of the same localization can be used on the target.
* `Stacks.AlgebraicGeometry.ProjBaseChange.isPullback_awayι_projMap`: that square is a pullback
  square, because the inverse image of a standard open is a standard open.
* `Stacks.AlgebraicGeometry.ProjBaseChange.isIso_of_isPullback_cover`: being an isomorphism is
  Zariski-local on the target, in the form needed here: an open cover of the target by schemes
  (not by opens) together with, for each member, a pullback square whose remaining leg is an
  isomorphism.

## Implementation notes

The hypothesis `hst : ψ s = t` with `t` a variable is what makes the chart lemmas usable. In the
application the element of the target ring is `ψ (Tᵢ)` while the ring identification available is
for `Tᵢ`, and `ψ (Tᵢ) = Tᵢ` is not a definitional equality: `HomogeneousLocalization.Away ℬ (ψ s)`
and `HomogeneousLocalization.Away ℬ t` are then different types and no rewrite can pass between
them, because the membership proofs in `AlgebraicGeometry.Proj.awayι` depend on the element. Taking
the element as a variable and substituting removes the problem at the cost of one extra hypothesis.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousIdeal HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.ProjBaseChange

universe u

section

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Mathlib's morphism restricted to the domain of definition is this repository's.** When
`ℬ₊ ≤ 𝒜₊.map ψ`, so that `AlgebraicGeometry.Proj.map` exists, its restriction along the inclusion
of the Tag 01MY domain of definition is `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`. -/
public theorem ι_comp_projMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    (mapDomain 𝒜 ℬ ψ).ι ≫ AlgebraicGeometry.Proj.map ψ hψ = mapHom 𝒜 ℬ ψ := by
  refine mapDomain_hom_ext 𝒜 ℬ ψ _ _ fun d hd f hf => ?_
  rw [homOfLE_mapHom, ← Category.assoc, Scheme.homOfLE_ι, mapAwayHom,
    ← basicOpenToSpec_comp_awayι ℬ hd (mem_of_mem 𝒜 ℬ ψ hf), Category.assoc,
    AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd f hf]

/-- **This repository's morphism on the domain of definition is Mathlib's.** The domain of
definition is everything as soon as `ℬ₊ ≤ 𝒜₊.map ψ`, and then the two morphisms agree. -/
public theorem mapHom_eq_projMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤) :
    (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ hdom.symm).hom ≫ mapHom 𝒜 ℬ ψ =
      AlgebraicGeometry.Proj.map ψ hψ := by
  rw [← ι_comp_projMap 𝒜 ℬ ψ hψ, ← Category.assoc, ← Category.assoc]
  convert Category.id_comp (AlgebraicGeometry.Proj.map ψ hψ)
  rw [Category.assoc, Scheme.isoOfEq_hom_ι, ← Scheme.topIso_hom, Iso.inv_hom_id]

/-- **The chart square of `AlgebraicGeometry.Proj.map` commutes.** On the standard affine chart
`D₊(t)` of the source, `AlgebraicGeometry.Proj.map ψ` is the morphism of affine schemes induced by
the map `𝒜_{(s)} → ℬ_{(t)}` of degree-zero homogeneous localizations.

The element `t` of `B` and the ring homomorphism `θ` are variables, constrained only by `ψ s = t`
and by the values of `θ` on fractions; so `θ` may be any spelling of
`HomogeneousLocalization.Away.map ψ s`. -/
@[ega "II 2.8.1" "special case", ega "II 3.7.2" "partial"]
public theorem awayι_comp_projMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    {d : ℕ} (hd : 0 < d) {s : A} (hs : s ∈ 𝒜 d) {t : B} (ht : t ∈ ℬ d) (hst : ψ s = t)
    (θ : Away 𝒜 s →+* Away ℬ t)
    (hθ : ∀ (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) (ha' : ψ a ∈ ℬ (k • d)),
      θ (Away.mk 𝒜 hs k a ha) = Away.mk ℬ ht k (ψ a) ha') :
    AlgebraicGeometry.Proj.awayι ℬ t ht hd ≫ AlgebraicGeometry.Proj.map ψ hψ =
      Spec.map (CommRingCat.ofHom θ) ≫ AlgebraicGeometry.Proj.awayι 𝒜 s hs hd := by
  subst hst
  have hθ' : θ = Away.map ψ s := by
    refine RingHom.ext fun x => ?_
    obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
    rw [hθ k a ha (ψ.map_mem ha), Away.map_mk]
  subst hθ'
  exact AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd s hs

/-- **The chart square of `AlgebraicGeometry.Proj.map` is a pullback square.** The standard affine
chart `D₊(ψ s)` of the source is the fibre product of the source with the standard affine chart
`D₊(s)` of the target: the inverse image of `D₊(s)` is `D₊(ψ s)`, and both charts are open
immersions. -/
public theorem isPullback_awayι_projMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    {d : ℕ} (hd : 0 < d) {s : A} (hs : s ∈ 𝒜 d) {t : B} (ht : t ∈ ℬ d) (hst : ψ s = t)
    (θ : Away 𝒜 s →+* Away ℬ t)
    (hθ : ∀ (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) (ha' : ψ a ∈ ℬ (k • d)),
      θ (Away.mk 𝒜 hs k a ha) = Away.mk ℬ ht k (ψ a) ha') :
    IsPullback (AlgebraicGeometry.Proj.awayι ℬ t ht hd) (Spec.map (CommRingCat.ofHom θ))
      (AlgebraicGeometry.Proj.map ψ hψ) (AlgebraicGeometry.Proj.awayι 𝒜 s hs hd) :=
  (IsOpenImmersion.isPullback (Spec.map (CommRingCat.ofHom θ))
    (AlgebraicGeometry.Proj.awayι ℬ t ht hd) (AlgebraicGeometry.Proj.awayι 𝒜 s hs hd)
    (AlgebraicGeometry.Proj.map ψ hψ)
    (awayι_comp_projMap 𝒜 ℬ ψ hψ hd hs ht hst θ hθ)
    (by
      rw [AlgebraicGeometry.Proj.opensRange_awayι, AlgebraicGeometry.Proj.opensRange_awayι,
        AlgebraicGeometry.Proj.map_preimage_basicOpen, hst])).flip

end

section gluing

variable {X Y : Scheme.{u}}

/-- **Being an isomorphism is Zariski-local on the target.** If the target is covered by opens
`V i`, each the image of an open immersion `g i`, and if for each `i` the morphism has a fibre
product over `g i` whose projection to the source of `g i` is an isomorphism, then the morphism
is an isomorphism.

This is `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top` at
`CategoryTheory.MorphismProperty.isomorphisms`, phrased for a cover by schemes and abstract
pullback squares rather than for opens and `AlgebraicGeometry.morphismRestrict`. The open
immersion property of `g i` is an explicit hypothesis rather than an instance: in the application
the target is built from `AlgebraicGeometry.projectiveSpaceAtUniverse`, which instance search does
not see through. -/
public theorem isIso_of_isPullback_cover (f : X ⟶ Y) {ι : Type*} (V : ι → Y.Opens)
    (hV : ⨆ i, V i = ⊤) (Z : ι → Scheme.{u}) (g : ∀ i, Z i ⟶ Y)
    (hgi : ∀ i, IsOpenImmersion (g i)) (hgV : ∀ i, Set.range (g i).base = (V i : Set Y))
    (W : ι → Scheme.{u}) (p : ∀ i, W i ⟶ X) (q : ∀ i, W i ⟶ Z i)
    (h : ∀ i, IsPullback (p i) (q i) f (g i)) (hq : ∀ i, IsIso (q i)) :
    IsIso f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme.{u}) V hV fun i => ?_
  have _ := hgi i
  have _ := hq i
  rw [show V i = (g i).opensRange from TopologicalSpace.Opens.ext (hgV i).symm,
    (MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
      (morphismRestrictOpensRange f (g i)), MorphismProperty.isomorphisms.iff,
    show pullback.snd f (g i) = (h i).isoPullback.inv ≫ q i by
      rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]]
  infer_instance

end gluing

end Stacks.AlgebraicGeometry.ProjBaseChange

end
