module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase

/-!
# The affine case reduces to its surjective case over the open image

The second proof of Stacks Project, Tag 04DZ dominates an affine scheme `U` étale over `X` by the
base change of a scheme `W` étale over `Y`, and then descends along `W ⟶ Y`. For that descent
`W ⟶ Y` has to be a covering, that is surjective; but the image of `W` in `Y` is only the image
of `U` in `X` carried across the homeomorphism `f`, so `W ⟶ Y` is surjective exactly when
`U ⟶ X` is.

This file performs the reduction which makes that hypothesis available: the affine case of
Stacks Project, Tag 04E0 for a bound `n` follows from its *surjective* case for the same bound,
read over an arbitrary target. The image of `U` in `X` is an open subscheme, `f` carries it to an
open subscheme `T` of `Y`, and `U` is already surjective onto `f ⁻¹ᵁ T`; a scheme étale over `T`
is a scheme étale over `Y`, and its base change along `f` is its base change along the
restriction `f ∣_ T`. The target `T` is no longer affine, which is why the surjective statement
is formulated for an arbitrary target.

## Main definitions

* `Stacks.Etale.EssSurjEtalePullbackSurjectiveBounded` — the surjective case: along a universal
  homeomorphism `f : X ⟶ Y` with *arbitrary* `X` and `Y`, every affine scheme étale, affine as a
  morphism and surjective over `X`, whose fibre degrees are bounded by `n`, is the base change
  along `f` of a scheme étale over `Y`.

## Main results

* `Stacks.Etale.essSurjAffineEtalePullbackBounded_of_surjectiveBounded` — the surjective case for
  a bound implies the affine case for that bound.

## Implementation notes

The affineness of `U ⟶ X` is carried as a hypothesis rather than deduced, because the target of
the surjective statement is an arbitrary scheme: a morphism from an affine scheme to a
non-separated scheme need not be affine. In the two places the statement is used the hypothesis
is free — over an affine target it is automatic, and over the open subscheme `T` it is inherited
from the affine case by cancelling the separated open immersion `(f ⁻¹ᵁ T).ι`.

The restriction of `U ⟶ X` to the open subscheme is produced by
`AlgebraicGeometry.IsOpenImmersion.lift` rather than by
`AlgebraicGeometry.Scheme.Hom.resLE`, so that its source is `U` itself and no identification of
`U` with its own top open subscheme is needed. Its fibre-degree bound comes from the bound on
`U ⟶ X` by base change, the comparison being that the first projection of
`U ×_X (f ⁻¹ᵁ T)` is an open immersion onto all of `U`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

/-- **The surjective case of the affine case of Stacks Project, Tag 04E0, over an arbitrary
target.** Along a universal homeomorphism `f : X ⟶ Y` of arbitrary schemes, every affine scheme
`U` which is étale and surjective over `X` by an affine morphism, and whose fibre degrees are
bounded by `n`, is over `X` the base change along `f` of a scheme étale over `Y`.

The target is arbitrary because the inductive step of the second proof of Stacks Project,
Tag 04DZ reaches the surjective case only after restricting the target to the open image of `U`,
which is not affine. -/
def EssSurjEtalePullbackSurjectiveBounded (n : ℕ) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), UniversalHomeomorphism f →
    ∀ (U : Scheme.{u}) (p : U ⟶ X), Etale p → IsAffine U → IsAffineHom p → Surjective p →
      BoundsFiberDegrees p (n : ℤ) →
        ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
          e.hom ≫ p = pullback.snd q f

variable {X Y : Scheme.{u}}

/-- The open subscheme of `Y` which corresponds, under a universal homeomorphism `f : X ⟶ Y`, to
the open image of a morphism `p` étale over `X`. -/
private def imageOpens (f : X ⟶ Y) [UniversalHomeomorphism f] {U : Scheme.{u}} (p : U ⟶ X)
    [Etale p] : Y.Opens :=
  ⟨f.base '' Set.range p.base,
    (EtaleCohomology.isHomeomorph_base_of_universalHomeomorphism f).isOpenMap _
      p.isOpenMap.isOpen_range⟩

/-- The inverse image of `Stacks.Etale.imageOpens` is the open image of `p`, because `f` is
injective on points. -/
private lemma coe_preimage_imageOpens (f : X ⟶ Y) [UniversalHomeomorphism f] {U : Scheme.{u}}
    (p : U ⟶ X) [Etale p] :
    ((f ⁻¹ᵁ imageOpens f p : X.Opens) : Set X) = Set.range p.base :=
  Set.preimage_image_eq _
    (EtaleCohomology.isHomeomorph_base_of_universalHomeomorphism f).injective

/-- **The affine case of Stacks Project, Tag 04E0 for a bound follows from its surjective case
for the same bound.** Restricting the target of `f` to the open subscheme corresponding to the
image of `U` makes `U` surjective, and a scheme étale over that open subscheme is a scheme étale
over `Y` whose base change along `f` is its base change along the restriction of `f`. -/
theorem essSurjAffineEtalePullbackBounded_of_surjectiveBounded (n : ℕ)
    (h : EssSurjEtalePullbackSurjectiveBounded.{u} n) :
    EssSurjAffineEtalePullbackBounded.{u} n := by
  intro X Y f _ _ _ U p hp hU hdeg
  set T : Y.Opens := imageOpens f p with hT
  have hrange : Set.range p.base ⊆ Set.range (f ⁻¹ᵁ T).ι.base := by
    rw [Scheme.Opens.range_ι, hT]
    exact (coe_preimage_imageOpens f p).ge
  set pT := IsOpenImmersion.lift (f ⁻¹ᵁ T).ι p hrange
  have hpT : pT ≫ (f ⁻¹ᵁ T).ι = p := IsOpenImmersion.lift_fac _ _ _
  have : Etale (pT ≫ (f ⁻¹ᵁ T).ι) := hpT ▸ hp
  have hpTet : Etale pT := Etale.of_comp pT (f ⁻¹ᵁ T).ι
  have hpTaff : IsAffineHom pT :=
    MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) pT (f ⁻¹ᵁ T).ι
      inferInstance (by rw [hpT]; infer_instance)
  have hpTsurj : Surjective pT := by
    refine ⟨fun z ↦ ?_⟩
    have hz : (f ⁻¹ᵁ T).ι.base z ∈ Set.range p.base := by
      rw [← coe_preimage_imageOpens f p]
      exact z.2
    obtain ⟨uu, huu⟩ := hz
    refine ⟨uu, (f ⁻¹ᵁ T).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hpT]
    exact huu
  have hsqU : IsPullback (𝟙 U) pT p (f ⁻¹ᵁ T).ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hpT]⟩
  have hpTdeg : BoundsFiberDegrees pT (n : ℤ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} (k : _ ⟶ _) ↦ BoundsFiberDegrees k (n : ℤ)) hsqU hdeg
  obtain ⟨V, q, hq, e, he⟩ := h (f ∣_ T) (universalHomeomorphism_morphismRestrict f T) U pT
    hpTet hU hpTaff hpTsurj hpTdeg
  have hsq : IsPullback (pullback.fst q (f ∣_ T))
      (pullback.snd q (f ∣_ T) ≫ (f ⁻¹ᵁ T).ι) (q ≫ T.ι) f :=
    (IsPullback.of_hasPullback q (f ∣_ T)).paste_vert (isPullback_morphismRestrict f T)
  refine ⟨V, q ≫ T.ι, inferInstance, ?_, hsq.isoPullback.symm ≪≫ e, ?_⟩
  · exact isAffine_of_isAffine_pullback f (q ≫ T.ι)
      (IsAffine.of_isIso (hsq.isoPullback.symm ≪≫ e).hom)
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hpT, reassoc_of% he]
    exact hsq.isoPullback_inv_snd

end Stacks.Etale

end

end
