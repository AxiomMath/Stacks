module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale

/-!
# Étaleness of a morphism of algebraic spaces is read off an étale chart of its target

Étaleness of a morphism `f : F ⟶ G` of algebraic spaces over `S` can be tested on one
surjective étale scheme chart of its *target*: the morphism is étale exactly when its base
change along such a chart is étale.  This is condition (3) of Stacks 03FS, the one condition of
that tag which `StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion` leaves open; with it
all four conditions of the tag become available as a single equivalence.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isEtale_tfae` is **Stacks 03FS** entire: the equivalence of all four
  conditions of the tag.
* `AlgebraicGeometry.Space.isEtale_pullback_snd_of_isEtale` and
  `AlgebraicGeometry.Space.isEtale_of_isEtale_pullback_snd` are the two implications the
  equivalence is made of, stated separately because each is weaker in its hypotheses than the
  equivalence: the first needs no algebraicity at all and the second needs it only of the
  target.
* `AlgebraicGeometry.Space.presheaf_pullback_fst`: the base change of an étale chart of the
  target along the morphism is again étale after every represented base change.

## Implementation notes

The base change is `CategoryTheory.Limits.pullback.snd f ψ`, the projection
`F ×_G h_V ⟶ h_V`, which is the idiom of
`AlgebraicGeometry.Space.exists_surjective_etale_chart_of_presheaf`; the fibre product is taken
in presheaves, where it always exists, so no representability and no algebraicity of the fibre
product is needed anywhere below.  In particular the proof does not go through the quotient of
`F ×_G h_V` by an étale equivalence relation and so does not need the effective descent of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`, which is what blocks
`AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart`, the same statement for the relative
property of a *representable* morphism.

Both implications turn on the fact that the other projection
`CategoryTheory.Limits.pullback.fst f ψ : F ×_G h_V ⟶ F` is a base change of the chart `ψ` and
therefore surjective and étale after every represented base change, which is
`AlgebraicGeometry.Space.presheaf_pullback_fst`.

*The forward implication.* Let `φ : h_U ⟶ F ×_G h_V` be an étale chart of the fibre product.
Composing with `pullback.fst f ψ` gives an étale chart of `F`, so `φ ≫ pullback.fst f ψ ≫ f` is
étale because `f` is; and that composite is `(φ ≫ pullback.snd f ψ) ≫ ψ` by the pullback
square.  Now `φ ≫ pullback.snd f ψ` is a morphism between representables, so Yoneda fullness
exhibits it as `yoneda.map l`, and part (2) of Stacks 03EC,
`AlgebraicGeometry.Space.etale_of_comp_etale_chart`, cancels the étale chart `ψ` to give that
`l` is an étale morphism of schemes.

*The reverse implication.* The composite `pullback.fst f ψ ≫ f` is `pullback.snd f ψ ≫ ψ`,
hence étale by Stacks 03FT from the hypothesis and from étaleness of the chart `ψ`.  Given an
étale chart `φ : h_U ⟶ F`, base change it along `pullback.fst f ψ`: since that morphism is
étale after every represented base change it is representable, so the base change is a morphism
`χ` of the site, surjective and étale because `pullback.fst f ψ` is both after every
represented base change.  The remaining projection of that square is a base change of `φ` and so
is itself étale after every represented base change, which makes `yoneda.map χ ≫ φ ≫ f` étale;
part (3) of Stacks 03EC,
`AlgebraicGeometry.Space.etale_of_comp_surjective_etale`, descends that along `χ` to
`φ ≫ f`.

Algebraicity of the source is used by neither implication, so
`AlgebraicGeometry.Space.isEtale_pullback_snd_of_isEtale` and
`AlgebraicGeometry.Space.isEtale_of_isEtale_pullback_snd` omit it; it is assumed in
`AlgebraicGeometry.Space.isEtale_tfae` only because conditions (2) and (4) of the tag need a
chart of the source. Condition (3) packaged as an equivalence is
`AlgebraicGeometry.Space.isEtale_iff_exists_target_chart` of
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms`, which does assume it.

## References

* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The projection `F ×_G h_V ⟶ F` of the fibre product of a morphism `f : F ⟶ G` of presheaves
with a morphism `ψ : h_V ⟶ G` out of a representable inherits from `ψ` every property obtained
by `CategoryTheory.MorphismProperty.presheaf` from a property of scheme morphisms: it is a base
change of `ψ`.

This is `AlgebraicGeometry.Space.presheaf_of_isPullback` at the canonical fibre product
square. -/
theorem presheaf_pullback_fst {V : BigFppfOver B S hS} {Q : MorphismProperty Scheme.{u}}
    (ψ : yoneda.obj V ⟶ G) (f : F ⟶ G)
    (hψ : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf ψ) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.fst f ψ) :=
  presheaf_of_isPullback B S hS (IsPullback.of_hasPullback f ψ).flip hψ

/-- The base change of an étale morphism of algebraic spaces along an étale scheme chart of its
target is étale.

This is the forward implication of condition (3) of Stacks 03FS.  Neither the source nor the
target is required to be an algebraic space, and the chart is not required to be surjective. -/
theorem isEtale_pullback_snd_of_isEtale (f : F ⟶ G) (hf : IsEtale B S hS f)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ G)
    (hψe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ) :
    IsEtale B S hS (pullback.snd f ψ) := by
  intro U φ hφ
  have h1 := hf U (φ ≫ pullback.fst f ψ)
    (isEtale_of_presheaf_etale B S hS (presheaf_pullback_fst B S hS ψ f hψe) U φ hφ)
  obtain ⟨l, hlm⟩ := yoneda.map_surjective (φ ≫ pullback.snd f ψ)
  have hl : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map l) :=
    etale_of_comp_etale_chart B S hS (a := (φ ≫ pullback.snd f ψ) ≫ ψ) (c := ψ) (l := l)
      (by rwa [Category.assoc, ← pullback.condition, ← Category.assoc]) hψe (by rw [hlm])
  rw [← hlm]
  exact presheaf_yoneda_map_of_inverseImage B S hS
    (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})) inferInstance l hl

/-- A morphism of algebraic spaces over `S` whose base change along one surjective étale scheme
chart of its target is étale is itself étale.

This is the reverse implication of condition (3) of Stacks 03FS.  No algebraicity of the source
is needed. -/
theorem isEtale_of_isEtale_pullback_snd (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    {V : BigFppfOver B S hS} (ψ : yoneda.obj V ⟶ G)
    (hψs : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hψe : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hbc : IsEtale B S hS (pullback.snd f ψ)) :
    IsEtale B S hS f := by
  have hbs := presheaf_pullback_fst B S hS ψ f hψs
  have hbe := presheaf_pullback_fst B S hS ψ f hψe
  have hcomp : IsEtale B S hS (pullback.fst f ψ ≫ f) := by
    rw [pullback.condition]
    exact isEtale_comp B S hS hbc (isEtale_of_presheaf_etale B S hS hψe)
  intro U φ hφ
  set hrep := hbe.rep with hrepdef
  set χ := hrep.snd φ with hχdef
  have sq : IsPullback (hrep.fst φ) (yoneda.map χ) (pullback.fst f ψ) φ := hrep.isPullback φ
  have hχs : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map χ) :=
    hbs.property φ (hrep.fst φ) χ sq
  have hχe : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map χ) :=
    hbe.property φ (hrep.fst φ) χ sq
  have hρ := presheaf_of_isPullback B S hS sq.flip hφ
  have h1 := hcomp _ (hrep.fst φ) hρ
  exact AlgebraicGeometry.Space.etale_of_comp_surjective_etale B S hS hG χ (φ ≫ f)
    (by rwa [← Category.assoc, ← sq.w, Category.assoc])

/-- **Stacks 03FS.** For a morphism `f : F ⟶ G` of algebraic spaces over `S` the following four
conditions are equivalent: `f` is étale; there is a surjective étale scheme chart of `F` whose
composite with `f` is étale; there is a surjective étale scheme chart of `G` along which the
base change of `f` is étale; and `f` fits into a commuting square of étale scheme charts, with
the chart of `F` surjective, whose upper morphism of schemes is étale.

Conditions (1), (2) and (4) are `AlgebraicGeometry.Space.isEtale_iff_exists_source_chart` and
`AlgebraicGeometry.Space.isEtale_iff_exists_etale_chart_square`; condition (3) is
`AlgebraicGeometry.Space.isEtale_iff_exists_target_chart`. -/
@[stacks 03FS]
theorem isEtale_tfae (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    List.TFAE [
      IsEtale B S hS f,
      (∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        IsEtale B S hS (p ≫ f)),
      (∃ (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ G),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf ψ ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf ψ ∧
        IsEtale B S hS (pullback.snd f ψ)),
      (∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F) (q : yoneda.obj V ⟶ G) (α : U ⟶ V),
        p ≫ f = yoneda.map α ≫ q ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q ∧
        AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map α))
    ] := by
  tfae_have 1 ↔ 2 := isEtale_iff_exists_source_chart B S hS hF hG f
  tfae_have 1 ↔ 3 := isEtale_iff_exists_target_chart B S hS hF hG f
  tfae_have 1 ↔ 4 := isEtale_iff_exists_etale_chart_square B S hS hF hG f
  tfae_finish

end AlgebraicGeometry.Space

end
