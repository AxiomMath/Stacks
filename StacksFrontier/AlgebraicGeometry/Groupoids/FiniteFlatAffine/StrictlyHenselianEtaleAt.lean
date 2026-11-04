module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleQuotientMorphism
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.SectionCoproduct
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StrictlyHenselianSection
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StrictlyHenselianSectionExists

/-!
# Étaleness of `C → C'` over a strictly henselian invariant ring

This file assembles the "Claim" of [Stacks Project, Tag 0DT9] into its conclusion: if the
invariant ring `C` of `G` is **strictly henselian**, then the map on invariant rings `C → C'` is
étale at every point `p'` of `Spec C'` lying over the closed point of `Spec C`.

The three inputs are the three preceding files:

* the ring splitting gives a section `σ : U ⟶ U'` of `f : U' ⟶ U` which is an open immersion with
  closed image containing the fibre `U'_{p'}`
  (`AlgebraicGeometry.GroupoidScheme.exists_section_of_strictlyHenselian`);
* the image of that section is an **invariant** open
  (`AlgebraicGeometry.GroupoidScheme.isInvariantSet_range_of_section`);
* the sheet of an invariant section is a disjoint piece of `G'` with the same invariant ring as
  `G` (`AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_of_section`), so
  `C → C'` is étale at each of its points.

That `p'` is one of those points is the last step: a point `u` of `U` over the closed point of
`Spec C` — there is one, the quotient morphism being surjective — is carried by `σ` into the fibre
`U'_{p'}`, and a point of the sheet maps to a point of `Spec C₁` above `p'`.

The conclusion here is étaleness of `C → C'` over a strictly henselian base only. Tag 0DT9 asserts
étaleness over an arbitrary base, obtained from this by writing the strict henselization of `C` at
a point as a filtered colimit of étale `C`-algebras and descending the decomposition to a finite
stage (`StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleInvariantRingMapAssembly`).

## Main results

* `AlgebraicGeometry.GroupoidScheme.etaleAt_specMap_invariantRingMap_of_strictlyHenselian`:
  **over a strictly henselian invariant ring, `Spec C' ⟶ Spec C` is étale at every point of
  `Spec C'` above the closed point of `Spec C`.**
* `AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap_of_strictlyHenselian_of_subsingleton`:
  **the first conclusion of Tag 0DT9 when `C` is strictly henselian local with a single prime**:
  then every point of `Spec C'` lies over the closed point.
* `AlgebraicGeometry.GroupoidScheme.isPullback_mapObjects_of_strictlyHenselian_of_subsingleton`:
  **the second conclusion of Tag 0DT9 in that same case**: `U' = Spec C' ×_{Spec C} U`.

## References

* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

section StrictlyHenselian

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
  [StrictlyHenselianLocalRing (invariantRing G)] [Etale F.mapObjects.left]

/-- **Over a strictly henselian invariant ring the map on invariant rings is étale above the
closed point.** This is the "Claim" of [Stacks Project, Tag 0DT9] together with the step that
converts it into étaleness: the sheet of the section produced by the ring splitting is an
invariant clopen of `U'`, hence a disjoint piece of `G'` whose invariant ring is `C`. -/
theorem etaleAt_specMap_invariantRingMap_of_strictlyHenselian
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (p' : Spec (.of (invariantRing G')))
    (hp' : (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    EtaleAt (Spec.map (CommRingCat.ofHom (invariantRingMap F))) p' := by
  obtain ⟨σ, hoi, hσ, hcl, hfib⟩ :=
    exists_section_of_strictlyHenselian F hsource htarget hstab p' hp'
  have := hoi
  have hV : IsInvariantOpen G' σ.opensRange :=
    isInvariantSet_range_of_section F hsource htarget hstab p' hp' hσ
      σ.opensRange.isOpen hfib
  obtain ⟨u, hu⟩ :=
    surjective_objectsToInvariantSpectrum G
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))
  have hσu : (objectsToInvariantSpectrum G').base (σ.base u) = p' :=
    mem_fibre_of_section_of_mem_closedFibre F hsource htarget hstab p' hp' hσ hfib u hu
  have hι : σ.opensRange.ι.base ((liftSection σ).base u) = σ.base u :=
    congrArg (fun k : G.objects.left ⟶ G'.objects.left => k.base u) (liftSection_ι (σ := σ))
  have hpt : (restrictInvariantOpenHom G' σ.opensRange hV).mapObjects.left.base
      ((liftSection σ).base u) = σ.base u := hι
  have hbase := base_objectsToInvariantSpectrum_mapObjects
    (restrictInvariantOpenHom G' σ.opensRange hV) ((liftSection σ).base u)
  rw [hpt, hσu] at hbase
  rw [hbase]
  exact etaleAt_specMap_invariantRingMap_of_section F hsource hσ hcl hV _

/-- **The first conclusion of [Stacks Project, Tag 0DT9] in the sub-case where `Spec C` is a
single point.** If the invariant ring `C` is strictly henselian local *and* its maximal ideal is
its only prime, then every point of `Spec C'` lies over the closed point of `Spec C`, so the
pointwise étaleness above the closed point is étaleness everywhere. The general case is
`AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap`. -/
theorem etale_invariantRingMap_of_strictlyHenselian_of_subsingleton
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (hsub : Subsingleton (PrimeSpectrum (invariantRing G))) :
    (invariantRingMap F).Etale := by
  have h : Etale (Spec.map (CommRingCat.ofHom (invariantRingMap F))) :=
    (etale_iff_forall_etaleAt _).mpr fun p' =>
      etaleAt_specMap_invariantRingMap_of_strictlyHenselian F hsource htarget hstab p'
        (@Subsingleton.elim (PrimeSpectrum (invariantRing G)) hsub _ _)
  exact HasRingHomProperty.Spec_iff.mp h

/-- **The second conclusion of [Stacks Project, Tag 0DT9] in the sub-case where `Spec C` is a
single point**: `U' = Spec C' ×_{Spec C} U`. -/
theorem isPullback_mapObjects_of_strictlyHenselian_of_subsingleton
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (hsub : Subsingleton (PrimeSpectrum (invariantRing G))) :
    IsPullback F.mapObjects.left (objectsToInvariantSpectrum G')
      (objectsToInvariantSpectrum G) (Spec.map (CommRingCat.ofHom (invariantRingMap F))) :=
  isPullback_mapObjects_of_etale_invariantRingMap F htarget hstab
    (etale_invariantRingMap_of_strictlyHenselian_of_subsingleton F hsource htarget hstab hsub)

end StrictlyHenselian

end AlgebraicGeometry.GroupoidScheme

end

end
