module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongCoproduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.CoverDense

/-!
# Domination by the base change of an affine scheme étale over the target

Let `f : X ⟶ Y` be a universal homeomorphism and let `U` be a quasi-compact scheme étale over
`X`. Property (C) for `f`, Stacks Project, Tag 04DW, produces a scheme `W₀` étale over `Y` and a
surjection `X ×_Y W₀ ⟶ U` over `X`. This file performs the reduction the second proof of Stacks
Project, Tag 04DZ makes immediately afterwards: because `U` is quasi-compact, `W₀` may be
replaced by the disjoint union of finitely many of its affine opens, so that the dominating
scheme over `Y` may be taken *affine*.

That is what makes the inductive step of the source's proof run inside the affine case: the
induction hypothesis is applied to the universal homeomorphism `X ×_Y W ⟶ W`, whose source and
target have to be affine.

## Main definitions

* `Stacks.Etale.opensFactorMap` — for an open subscheme `A` of `W₀`, the comparison morphism
  `X ×_Y A ⟶ X ×_Y W₀`. **This is a new definition.**

## Main results

* `Stacks.Etale.range_opensFactorMap` — its range is the inverse image of `A` under the
  projection `X ×_Y W₀ ⟶ W₀`.
* `Stacks.Etale.exists_isAffine_etale_domination` — the reduction: a quasi-compact scheme étale
  over `X` is dominated, by a surjection over `X`, by the base change along `f` of an *affine*
  scheme étale over `Y`.

## Implementation notes

The comparison morphism is built from Mathlib's pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, which presents `X ×_Y A` as
`(X ×_Y W₀) ×_{W₀} A`; its range is then the inverse image of `A` by
`AlgebraicGeometry.Scheme.Pullback.range_fst`, with no open-immersion hypothesis needed.

The finitely many affine opens are extracted by compactness from the open cover of `U` whose
member attached to an affine open `A` of `W₀` is the image under the dominating surjection of the
inverse image of `A`. That surjection is étale, being a morphism over `X` between two schemes
étale over `X`, hence an open map, which is what makes those images open.

The disjoint union is indexed by the elements of the resulting finite subset of the affine opens
of `W₀`, so its index type is a subtype of `AlgebraicGeometry.Scheme.affineOpens` and therefore
lies in the same universe; finiteness of the index gives affineness of the coproduct, and
étaleness of the fold map is `AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### The base change of an open subscheme of the dominating scheme -/

section Factor

variable (f : X ⟶ Y) {W₀ : Scheme.{u}} (v : W₀ ⟶ Y) (A : W₀.Opens)

/-- **The base change of an open subscheme of the target of a morphism.** For `f : X ⟶ Y`, a
morphism `v : W₀ ⟶ Y` and an open subscheme `A` of `W₀`, this is the comparison morphism
`X ×_Y A ⟶ X ×_Y W₀`, obtained by reading `X ×_Y A` as `(X ×_Y W₀) ×_{W₀} A`. -/
def opensFactorMap : pullback f (A.ι ≫ v) ⟶ pullback f v :=
  (pullbackLeftPullbackSndIso f v A.ι).inv ≫ pullback.fst (pullback.snd f v) A.ι

/-- The comparison morphism of an open subscheme commutes with the projection to `X`. -/
@[reassoc]
lemma opensFactorMap_fst :
    opensFactorMap f v A ≫ pullback.fst f v = pullback.fst f (A.ι ≫ v) := by
  simpa only [opensFactorMap, Category.assoc] using
    pullbackLeftPullbackSndIso_inv_fst f v A.ι

/-- The range of the comparison morphism of an open subscheme is the inverse image of that open
subscheme under the projection to `W₀`. -/
lemma range_opensFactorMap :
    Set.range (opensFactorMap f v A).base = (pullback.snd f v).base ⁻¹' (A : Set W₀) := by
  have hsurj : Function.Surjective (pullbackLeftPullbackSndIso f v A.ι).inv.base := fun z ↦
    ⟨(pullbackLeftPullbackSndIso f v A.ι).hom.base z, by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      simp⟩
  have hcomp : Set.range (opensFactorMap f v A).base =
      Set.range (pullback.fst (pullback.snd f v) A.ι).base := by
    refine Set.Subset.antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · obtain ⟨z, rfl⟩ := hx
      exact ⟨(pullbackLeftPullbackSndIso f v A.ι).inv.base z,
        (Scheme.Hom.comp_apply _ _ z).symm⟩
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨z', hz'⟩ := hsurj z
      exact ⟨z', by rw [opensFactorMap, Scheme.Hom.comp_apply, hz']⟩
  rw [hcomp, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

end Factor

/-! ### The reduction to an affine dominating scheme -/

/-- **A finite family of affine opens whose images cover the target.** Let `h₀ : Z ⟶ U` be a
surjective open map onto a quasi-compact scheme and `σ : Z ⟶ W₀` any morphism. Then finitely many
affine opens `A` of `W₀` already have images `h₀ '' (σ ⁻¹' A)` covering `U`. -/
lemma exists_finset_affineOpens_image_preimage_cover {Z W₀ U : Scheme.{u}} [CompactSpace U]
    (h₀ : Z ⟶ U) [Surjective h₀] (hopen : IsOpenMap h₀.base) (σ : Z ⟶ W₀) :
    ∃ t : Finset W₀.affineOpens,
      (Set.univ : Set U) ⊆ ⋃ A ∈ t, h₀.base '' (σ.base ⁻¹' (A.1 : Set W₀)) := by
  refine (isCompact_univ (X := U)).elim_finite_subcover
    (fun A : W₀.affineOpens ↦ h₀.base '' (σ.base ⁻¹' (A.1 : Set W₀)))
    (fun A ↦ hopen _ (A.1.2.preimage σ.base.hom.continuous)) fun x _ ↦ ?_
  obtain ⟨m, rfl⟩ := h₀.surjective x
  obtain ⟨A, hA, hmA, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W₀) (x := σ.base m) (U := ⊤)
      (TopologicalSpace.Opens.mem_top _)
  exact Set.mem_iUnion.2 ⟨⟨A, hA⟩, m, hmA, rfl⟩

/-- **A quasi-compact scheme étale over `X` is dominated by the base change of an affine scheme
étale over `Y`.** Let `f : X ⟶ Y` be a universal homeomorphism and let `p : U ⟶ X` be étale with
`U` quasi-compact. Then there is an *affine* scheme `W` étale over `Y` and a surjection
`X ×_Y W ⟶ U` of schemes over `X`.

Property (C) for `f`, Stacks Project, Tag 04DW, gives such a `W₀` without affineness; the images
in `U` of the inverse images of the affine opens of `W₀` form an open cover of `U`, finitely many
of them suffice, and their disjoint union is an affine scheme étale over `Y` whose base change
still surjects onto `U`. -/
theorem exists_isAffine_etale_domination (f : X ⟶ Y) [UniversalHomeomorphism f]
    {U : Scheme.{u}} (p : U ⟶ X) [Etale p] [CompactSpace U] :
    ∃ (W : Scheme.{u}) (w : W ⟶ Y) (_ : Etale w) (_ : IsAffine W) (h : pullback f w ⟶ U),
      Surjective h ∧ h ≫ p = pullback.fst f w := by
  classical
  obtain ⟨hint, -, -⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance
  have _ : IsIntegralHom f := hint
  obtain ⟨hhom, hhomeq⟩ := isHomeomorph_iff_exists_homeomorph.mp
    (EtaleCohomology.isHomeomorph_base_of_universalHomeomorphism f)
  have hce : Topology.IsClosedEmbedding f := hhomeq ▸ hhom.isClosedEmbedding
  obtain ⟨W₀, v, hv, h₀, hh₀surj, hh₀⟩ :=
    EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding f hce p inferInstance
  have _ : Etale v := hv
  have _ : Surjective h₀ := hh₀surj
  have _ : Etale (h₀ ≫ p) := by rw [hh₀]; infer_instance
  have _ : Etale h₀ := Etale.of_comp h₀ p
  obtain ⟨t, ht⟩ :=
    exists_finset_affineOpens_image_preimage_cover h₀ h₀.isOpenMap (pullback.snd f v)
  set Ws : {A : W₀.affineOpens // A ∈ t} → Scheme.{u} := fun i ↦ (i.1.1).toScheme
  set qs : ∀ i, Ws i ⟶ Y := fun i ↦ (i.1.1).ι ≫ v
  have _ : ∀ i, IsAffine (Ws i) := fun i ↦ i.1.2
  have hwetale : Etale (Sigma.desc qs) :=
    have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have hpb : IsPullback (Sigma.desc fun i ↦ pullback.fst f (qs i))
      (Limits.Sigma.map fun i ↦ pullback.snd f (qs i)) f (Sigma.desc qs) :=
    isPullback_sigmaDesc_sigmaMap qs (Over.mk f)
  set ec := hpb.isoPullback
  set dom : (∐ fun i ↦ pullback f (qs i)) ⟶ U :=
    Sigma.desc (fun i ↦ opensFactorMap f v i.1.1 ≫ h₀) with hdom
  have domp : dom ≫ p = Sigma.desc fun i ↦ pullback.fst f (qs i) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [hdom, ← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Category.assoc, hh₀,
      opensFactorMap_fst]
  refine ⟨∐ Ws, Sigma.desc qs, hwetale, inferInstance, ec.inv ≫ dom, ⟨fun x ↦ ?_⟩, ?_⟩
  · obtain ⟨A, hAt, m, hmA, hmx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    obtain ⟨z, hz⟩ := (range_opensFactorMap f v A.1).ge hmA
    refine ⟨ec.hom.base ((Sigma.ι (fun i ↦ pullback f (qs i)) ⟨A, hAt⟩).base z), ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc, ← Scheme.Hom.comp_apply, hdom,
      Sigma.ι_desc, Scheme.Hom.comp_apply, hz, hmx]
  · rw [Category.assoc, domp, ← hpb.isoPullback_hom_fst, Iso.inv_hom_id_assoc]

end Stacks.Etale

end

end
