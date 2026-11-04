module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleGlobalCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UniverseLiftExt

/-!
# Vanishing of étale cohomology is carried to a universe lift of the coefficients

Sheaf cohomology on the small étale site of a scheme `X : Scheme.{u}` is defined at coefficients
`AddCommGrpCat.{u}`, because `CategoryTheory.Sheaf.H'` pins its coefficient universe to the
morphism universe of the site.  Several consumers need it at a larger coefficient universe
instead — the internal hom of two `𝒪`-modules on the small étale site has its sections one
universe up, since they are indexed by the objects of the site.

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift` compares the two
cohomology groups at the two universes `u` and `u + 1`, with the `Ext` universes pinned to the
coefficient universes.  This file records the one-directional statement the consumers use, at an
arbitrary target universe `max u t` and arbitrary `Ext` universes: vanishing in a degree is
carried from coefficients `AddCommGrpCat.{u}` to their universe lift.

## Main results

* `AlgebraicGeometry.subsingleton_H_uliftFunctor_smallEtale`: vanishing of étale cohomology in a
  degree is carried from coefficients `AddCommGrpCat.{u}` to their universe lift.

## Implementation notes

The generic comparison is
`Stacks.Sheaves.UniverseLift.subsingleton_H_uliftFunctor_of_subsingleton_H`; its two hypotheses
on the site — compatibility of the lift with sheafification and preservation of injective
objects — are the base's `AlgebraicGeometry.etaleUlift_properties` at `v = u`.

The instances `Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale` and
`Stacks.EtaleCohomology.enoughInjectives_sheaf_smallEtale`, reached through the imports of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift`, are indexed by
`max (u + 1) v`, and instance search for `EnoughInjectives` at coefficients `AddCommGrpCat.{u}`
gets stuck on `max (u + 1) ?v =?= u` through them; their priority is lowered locally, as in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleAffineQuasicoherentVanishing.lean`, and
the instance at the morphism universe,
`AlgebraicGeometry.enoughInjectives_sheaf_smallEtaleTopology`, is supplied by name.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t w z u

namespace AlgebraicGeometry

attribute [local instance 0] Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale
  Stacks.EtaleCohomology.enoughInjectives_sheaf_smallEtale in
/-- **Vanishing of étale cohomology is carried to a universe lift of the coefficients.**  This
is `Stacks.Sheaves.UniverseLift.subsingleton_H_uliftFunctor_of_subsingleton_H` with its
sheafification and injectivity hypotheses discharged on the small étale site by
`AlgebraicGeometry.etaleUlift_properties`. -/
theorem subsingleton_H_uliftFunctor_smallEtale (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max u t}]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt.{z} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u t})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (h : Subsingleton (Sheaf.H.{w} F n)) :
    Subsingleton (Sheaf.H.{z} ((sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{t, u}).obj F) n) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    enoughInjectives_sheaf_smallEtaleTopology X
  obtain ⟨hsh, hinj⟩ := etaleUlift_properties.{u, u, t} X
  have := hsh
  have := hinj
  exact Stacks.Sheaves.UniverseLift.subsingleton_H_uliftFunctor_of_subsingleton_H _ F n h

end AlgebraicGeometry

end
