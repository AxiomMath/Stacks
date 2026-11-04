module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FiniteEtaleStratification
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 03S0 for the objects of a big étale site

An object `U` of the small étale site of a quasi-compact quasi-separated `Y` whose own scheme is
quasi-compact and quasi-separated admits a partition of `Y` into constructible locally closed
subschemes over each of which the base change of `U` is finite étale, with the strata presented
as objects of the big étale site and the base change as small étale base change. This is
`AlgebraicGeometry.HasFiniteEtaleStratification`, the form in which the library's Stacks 03S8 (1)
and Stacks 09Y9 ask for Stacks 03S0.

The mathematics is `AlgebraicGeometry.exists_constructible_partition_finite_etale`, the library's
Stacks 03S0 for schemes. What is added is the passage to the site: a stratum is a scheme
admitting an immersion into `Y`, hence a monomorphism, and the size cutoff of a big étale site is
a strong prelimit cardinal, so the stratum lies below the cutoff and is an object of the site;
and the structure morphism of the small étale base change `(smallEtaleBaseChange B i).obj U` is
by construction the second projection of a fibre product, which is a second pullback of the same
cospan as the one the statement for schemes produces, so the two agree up to an isomorphism over
the stratum.

## Main results

* `AlgebraicGeometry.hasFiniteEtaleStratification` — the stratification for one étale object.
* `AlgebraicGeometry.etaleFiniteStratificationExists` —
  `AlgebraicGeometry.EtaleFiniteStratificationExists`, which is what the conditional statements
  of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles` carry
  as the hypothesis `h03S0`.

## References

* [Stacks Project, Tag 03S0](https://stacks.math.columbia.edu/tag/03S0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 03S0 for an object of a small étale site.** For `Y` a quasi-compact quasi-separated
scheme of a big étale site and `U` an étale object over `Y` whose own scheme is quasi-compact and
quasi-separated, `Y` has a partition into constructible locally closed subschemes, presented as
objects of the site, over each of which the small étale base change of `U` is finite étale. -/
public theorem hasFiniteEtaleStratification (B : BigEtaleSite.{u}) (Y : B.Scheme)
    (U : SmallEtale B Y.obj Y.property) (hYc : CompactSpace Y.obj)
    (hYq : QuasiSeparatedSpace Y.obj) (hU : IsQCQSEtaleObject B Y U) :
    HasFiniteEtaleStratification B Y U := by
  have hUc : CompactSpace (B.inclusion.obj U.obj.left) := hU.1
  have hUq : QuasiSeparatedSpace (B.inclusion.obj U.obj.left) := hU.2
  have hyc : CompactSpace (B.inclusion.obj Y) := hYc
  have hyq : QuasiSeparatedSpace (B.inclusion.obj Y) := hYq
  have het : Etale (B.inclusion.map U.obj.hom) := U.property
  obtain ⟨P, hP, hconstr, hstrata⟩ :=
    exists_constructible_partition_finite_etale (B.inclusion.map U.obj.hom)
  refine ⟨P, hP, hconstr, fun S hS => ?_⟩
  obtain ⟨Z, i, himm, hrange, hfin, _⟩ := hstrata S hS
  have himm' : IsImmersion i := himm
  have hZ : Z.size < B.cutoff :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit i Y.property
  let i' : B.obj Z hZ ⟶ Y := ObjectProperty.homMk i
  have hmap : B.inclusion.map i' = i := ObjectProperty.ι_map _
  refine ⟨B.obj Z hZ, i', ?_, ?_, ?_, ((smallEtaleBaseChange B i').obj U).property⟩
  · rwa [hmap]
  · rwa [hmap]
  -- The structure morphism of the base change is the second projection of a fibre product,
  -- hence a pullback of the same cospan as the projection the statement for schemes produces.
  show IsFinite (B.inclusion.map (pullback.snd U.obj.hom i'))
  have hsq : IsPullback (B.inclusion.map (pullback.snd U.obj.hom i'))
      (B.inclusion.map (pullback.fst U.obj.hom i')) (B.inclusion.map i')
      (B.inclusion.map U.obj.hom) :=
    ((IsPullback.of_hasPullback U.obj.hom i').map B.inclusion).flip
  rw [hmap] at hsq
  have hfin' : IsFinite (pullback.fst i (B.inclusion.map U.obj.hom)) := hfin
  rw [← hsq.isoPullback_hom_fst]
  infer_instance

/-- **Stacks 03S0 for a big étale site.** Every étale object with quasi-compact quasi-separated
scheme over a quasi-compact quasi-separated scheme of the site becomes finite étale on the strata
of a partition of its base into constructible locally closed subschemes of the site.

This is the hypothesis `h03S0` of
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf` and of
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_stratification`. -/
public theorem etaleFiniteStratificationExists (B : BigEtaleSite.{u}) :
    EtaleFiniteStratificationExists B :=
  hasFiniteEtaleStratification B

end AlgebraicGeometry

end
