module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre

/-!
# Strict henselizations in two big étale sites

The étale local ring `𝒪^{sh}_{S,s}` of a scheme `S` at a geometric point `s` is formed in a big
étale site `B` containing `S`. Two such sites `B` and `B'` give canonically isomorphic rings: both
are identified with the strict henselization of the ordinary local ring at the image of `s` in the
separable closure of its residue field inside the residue field of `s`
(`AlgebraicGeometry.etaleLocalRingEquivStrictHenselization`), compatibly with the
ordinary-to-étale germ maps and with evaluation of germs in the residue field of `s`. This file
records the resulting isomorphism and its spectrum, and uses them to build, for a morphism
`f : X ⟶ S`, a geometric point `x` of `X`, and sites `B₁` containing `X` and `B₂` containing `S`,
a morphism of strict henselizations `Spec 𝒪^{sh}_{X,x} ⟶ Spec 𝒪^{sh}_{S,f(x)}` (taken in `B₁` and
`B₂`) lying over `f` and compatible with the canonical geometric points.

## Main definitions

* `AlgebraicGeometry.etaleLocalRingSiteChange` is the isomorphism of étale local rings formed in
  two big étale sites.
* `AlgebraicGeometry.strictHenselizationSiteChange` is its spectrum.
* `AlgebraicGeometry.strictHenselizationSquareMapVia` is the morphism of strict henselizations
  across two sites, through a third site containing both schemes.

## Main results

* `AlgebraicGeometry.strictHenselizationSiteChange_comp` and
  `AlgebraicGeometry.geometricPointToStrictHenselization_strictHenselizationSiteChange`: the
  change of site lies over `S` and preserves the canonical geometric point.
* `AlgebraicGeometry.strictHenselizationSquareMapVia_comp` and
  `AlgebraicGeometry.geometricPointToStrictHenselization_strictHenselizationSquareMapVia`: the
  same two compatibilities for the morphism across two sites.

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

section SiteChange

variable (B B' : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (hS' : B'.Contains S)
  (s : GeometricPoint S)

/-- **The étale local rings at a geometric point formed in two big étale sites are isomorphic**:
both are the strict henselization of the ordinary local ring at the image of the point. -/
def etaleLocalRingSiteChange : ↥(etaleLocalRing B S hS s) ≃+* ↥(etaleLocalRing B' S hS' s) :=
  (etaleLocalRingEquivStrictHenselization B S hS s).symm.trans
    (etaleLocalRingEquivStrictHenselization B' S hS' s)

/-- The change of site intertwines the two identifications with the strict henselization. -/
private theorem etaleLocalRingSiteChange_equivStrictHenselization
    (t : (geometricHenselizationTower S s).strictHenselization) :
    etaleLocalRingSiteChange B B' S hS hS' s (etaleLocalRingEquivStrictHenselization B S hS s t) =
      etaleLocalRingEquivStrictHenselization B' S hS' s t := by
  rw [etaleLocalRingSiteChange, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]

/-- The change of site is compatible with the ordinary-to-étale germ maps. -/
theorem etaleLocalRingSiteChange_fromLocalRing
    (r : ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))) :
    etaleLocalRingSiteChange B B' S hS hS' s (structureSheafStalkFromLocalRing B S hS s r) =
      structureSheafStalkFromLocalRing B' S hS' s r := by
  rw [← (etaleLocalRing_strictHenselization_canonical B S hS s
    (geometricHenselizationTower S s)).property.1 r,
    etaleLocalRingSiteChange_equivStrictHenselization]
  exact (etaleLocalRing_strictHenselization_canonical B' S hS' s
    (geometricHenselizationTower S s)).property.1 r

/-- The change of site is compatible with evaluation of germs in the residue field of the
geometric point. -/
theorem toGeometricField_etaleLocalRingSiteChange (a : ↥(etaleLocalRing B S hS s)) :
    structureSheafStalkToGeometricField B' S hS' s (etaleLocalRingSiteChange B B' S hS hS' s a) =
      structureSheafStalkToGeometricField B S hS s a := by
  obtain ⟨t, rfl⟩ := (etaleLocalRingEquivStrictHenselization B S hS s).surjective a
  rw [etaleLocalRingSiteChange_equivStrictHenselization]
  exact ((etaleLocalRing_strictHenselization_canonical B' S hS' s
    (geometricHenselizationTower S s)).property.2 t).trans
    ((etaleLocalRing_strictHenselization_canonical B S hS s
      (geometricHenselizationTower S s)).property.2 t).symm

/-- The change of site composed with the ordinary-to-étale germ map, as ring homomorphisms. -/
theorem etaleLocalRingSiteChange_comp_fromLocalRing :
    (etaleLocalRingSiteChange B B' S hS hS' s).toRingHom.comp
        (structureSheafStalkFromLocalRing B S hS s) =
      structureSheafStalkFromLocalRing B' S hS' s :=
  RingHom.ext (etaleLocalRingSiteChange_fromLocalRing B B' S hS hS' s)

/-- Evaluation of germs after the change of site, as ring homomorphisms. -/
theorem toGeometricField_comp_etaleLocalRingSiteChange :
    (structureSheafStalkToGeometricField B' S hS' s).comp
        (etaleLocalRingSiteChange B B' S hS hS' s).toRingHom =
      structureSheafStalkToGeometricField B S hS s :=
  RingHom.ext (toGeometricField_etaleLocalRingSiteChange B B' S hS hS' s)

/-- **The change of big étale site for strict henselizations**: the isomorphism
`Spec 𝒪^{sh}_{S,s} ⟶ Spec 𝒪^{sh}_{S,s}` from the strict henselization formed in `B'` to the one
formed in `B`, the spectrum of `AlgebraicGeometry.etaleLocalRingSiteChange`. -/
def strictHenselizationSiteChange :
    strictHenselization B' S hS' s ⟶ strictHenselization B S hS s :=
  Spec.map (CommRingCat.ofHom (etaleLocalRingSiteChange B B' S hS hS' s).toRingHom)

/-- The change of site lies over `S`. -/
theorem strictHenselizationSiteChange_comp :
    strictHenselizationSiteChange B B' S hS hS' s ≫ strictHenselizationToBase B S hS s =
      strictHenselizationToBase B' S hS' s := by
  simp only [strictHenselizationSiteChange, strictHenselizationToBase]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    etaleLocalRingSiteChange_comp_fromLocalRing]

/-- The change of site carries the canonical geometric point to the canonical geometric point. -/
theorem geometricPointToStrictHenselization_strictHenselizationSiteChange :
    geometricPointToStrictHenselization B' S hS' s ≫ strictHenselizationSiteChange B B' S hS hS' s =
      geometricPointToStrictHenselization B S hS s := by
  simp only [strictHenselizationSiteChange, geometricPointToStrictHenselization]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toGeometricField_comp_etaleLocalRingSiteChange]

end SiteChange

section Square

variable (B₁ B₂ B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B₁.Contains X)
  (hS : B₂.Contains S) (hXB : B.Contains X) (hSB : B.Contains S) (f : X ⟶ S)
  (x : GeometricPoint X)

/-- **The morphism of strict henselizations across two big étale sites.** For `f : X ⟶ S`, a
geometric point `x` of `X`, a site `B₁` containing `X`, a site `B₂` containing `S` and a site `B`
containing both, the morphism `Spec 𝒪^{sh}_{X,x} ⟶ Spec 𝒪^{sh}_{S,f(x)}` from the strict
henselization formed in `B₁` to the one formed in `B₂`: change to `B`, the canonical morphism
`AlgebraicGeometry.strictHenselizationSquareMap` in `B`, and change to `B₂`. -/
def strictHenselizationSquareMapVia :
    strictHenselization B₁ X hX x ⟶ strictHenselization B₂ S hS (x.map f) :=
  strictHenselizationSiteChange B B₁ X hXB hX x ≫ strictHenselizationSquareMap B hXB hSB f x ≫
    strictHenselizationSiteChange B₂ B S hS hSB (x.map f)

/-- The morphism of strict henselizations across two sites lies over `f`. -/
theorem strictHenselizationSquareMapVia_comp :
    strictHenselizationSquareMapVia B₁ B₂ B hX hS hXB hSB f x ≫
        strictHenselizationToBase B₂ S hS (x.map f) =
      strictHenselizationToBase B₁ X hX x ≫ f := by
  rw [strictHenselizationSquareMapVia, Category.assoc, Category.assoc,
    strictHenselizationSiteChange_comp, strictHenselizationSquareMap_comp, ← Category.assoc,
    strictHenselizationSiteChange_comp]

/-- The morphism of strict henselizations across two sites carries the canonical geometric point
to the canonical geometric point. -/
theorem geometricPointToStrictHenselization_strictHenselizationSquareMapVia :
    geometricPointToStrictHenselization B₁ X hX x ≫
        strictHenselizationSquareMapVia B₁ B₂ B hX hS hXB hSB f x =
      geometricPointToStrictHenselization B₂ S hS (x.map f) := by
  rw [strictHenselizationSquareMapVia, ← Category.assoc,
    geometricPointToStrictHenselization_strictHenselizationSiteChange, ← Category.assoc,
    geometricPointToStrictHenselization_strictHenselizationSquareMap,
    geometricPointToStrictHenselization_strictHenselizationSiteChange]

end Square

end AlgebraicGeometry
