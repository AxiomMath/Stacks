module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricFibreBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections

/-!
# Derived global sections after derived direct image, for abelian sheaves on small étale sites

Let `g : T ⟶ Z` be a morphism of schemes. This file proves

`RΓ(Z, -) ∘ Rg_* ≅ RΓ(T, -)`

as functors `D(T_étale) ⟶ D(Ab)` on the **unbounded** derived categories of abelian sheaves for
the small étale topology. It is the global-sections statement of Stacks 0D6H read at abelian
coefficients on the small étale sites of schemes, which is the shape the geometric-fibre
constructions of Stacks 0GIX need: taking `g` to be the structure morphism
`AlgebraicGeometry.geometricFibreToPoint f s : X_s ⟶ s` of a geometric fibre gives
`RΓ(s, Rq_*M) ≅ RΓ(X_s, M)`.

## Main results

All in the namespace `Stacks.EtaleCohomology`.

* `isKInjective_mapHomologicalComplex_smallEtalePushforwardAb` — degreewise direct image of
  abelian étale sheaves carries K-injective complexes to K-injective complexes.
* `computesSecond_smallEtalePushforwardAb_globalSections` — the hypothesis of the brick
  `Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes`, discharged.
* `smallEtaleDerivedGlobalSectionsPushforwardIsoAb` — the isomorphism
  `Rg_* ⋙ RΓ(Z, -) ≅ RΓ(T, -)`.

## Implementation notes

**Abelian coefficients make the hard input free.** The library's form of the global-sections clause
of Stacks 0D6H for ringed sites and module coefficients,
`Stacks.Cohomology.LerayUnbounded.derivedGlobalSectionsPushforwardIsoGeneral`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/LerayForUnboundedGlobalSectionsGeneral.lean`), has to discharge
`Stacks.Cohomology.LerayUnbounded.ComputesSecond f_* (Γ(D, -))` by hand — corepresenting global
sections by the structure sheaf and running the derived pullback adjunction of Stacks 07A6 —
because the stronger statement Stacks 093Y, that degreewise `f_*` preserves K-injectivity, is a
statement about *flat* morphisms and is false for a general morphism of ringed sites: `f^*` on
modules is not exact.

At abelian coefficients there is no such obstruction. The inverse image `g⁻¹` of abelian étale
sheaves is exact (`Stacks.EtaleCohomology.smallEtalePullbackAb_preservesFiniteLimits` and
`..._preservesFiniteColimits`), so the adjoint criterion of Stacks 08BJ,
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, gives K-injectivity of `g_* I`
outright for every morphism of schemes. `ComputesSecond` then follows from
`Stacks.Cohomology.LerayUnbounded.computesSecond_of_isKInjective`, and the conclusion is one
application of the coefficient-agnostic brick
`Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` to the **underived** identification
`Stacks.EtaleCohomology.smallEtalePushforwardGammaIsoAb`, which is already available for an
arbitrary morphism of schemes. So the two assembled files of the module case collapse here to
three short declarations; none of the ringed-site machinery is ported.

**No Stacks attribute.** Stacks 0D6H is a statement about a morphism of *ringed* sites and the
functors `D(O_C) ⟶ D(Γ(O_D))` on complexes of modules, with the target read through the ring map
`Γ(O_D) ⟶ Γ(O_C)`; both of its clauses are already registered, on
`Stacks.Cohomology.LerayUnbounded.derivedGlobalSectionsPushforwardIsoGeneral` and
`...derivedSectionsOverObjectPushforwardIsoGeneral`. What is proved here is the abelian instance
on small étale sites, which states strictly less than the tag, and so it is left untagged — the
same choice, for the same reason, as
`Stacks.ComparingTopologies.derivedGlobalSectionsComparisonIso`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/DerivedGlobalSections.lean`).

**The derivations are not hypotheses here.**
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections` and
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAb` carry the existence of the derivation as
an instance argument, and the files that use them carry it as a variable binder, because
`DerivedEtale.lean` does not see
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse`. This file makes
that a local instance, after which the three derivations are found by instance search and the
statement below is unconditional in `g`. In a context that does carry the binders the two
spellings of each functor agree by proof irrelevance, so the isomorphism applies there verbatim.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {T Z : Scheme.{u}} (g : T ⟶ Z)

/-- **Stacks 08BJ for abelian sheaves on small étale sites.** Degreewise direct image of abelian
sheaves along the morphism of small étale sites induced by `g : T ⟶ Z` carries K-injective
cochain complexes to K-injective cochain complexes.

No hypothesis on `g`: the adjoint criterion asks the left adjoint to be exact, and the left
adjoint here is the inverse image `g⁻¹` of abelian étale sheaves, which is exact for every
morphism of schemes. This is what fails at module coefficients, where the corresponding
statement is Stacks 093Y and needs flatness. -/
public theorem isKInjective_mapHomologicalComplex_smallEtalePushforwardAb
    (I : CochainComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((smallEtalePushforwardAb g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (smallEtalePushforwardAb g)
    (smallEtalePullbackAb g) (smallEtaleAdjunctionAb g) I

/-- **Global sections on `Z` are computed at the direct image of a K-injective complex.** The
hypothesis on which the brick `Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` runs,
discharged for every morphism of schemes: `g_* I` is itself K-injective by
`Stacks.EtaleCohomology.isKInjective_mapHomologicalComplex_smallEtalePushforwardAb`, and the
unit of a right derived functor is invertible on a K-injective complex. -/
public theorem computesSecond_smallEtalePushforwardAb_globalSections :
    Stacks.Cohomology.LerayUnbounded.ComputesSecond (smallEtalePushforwardAb g)
      (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) :=
  Stacks.Cohomology.LerayUnbounded.computesSecond_of_isKInjective _ _ fun I hI =>
    have := hI
    isKInjective_mapHomologicalComplex_smallEtalePushforwardAb g I

/-- **Derived global sections after derived direct image, for abelian sheaves on small étale
sites.** For a morphism of schemes `g : T ⟶ Z`,

`Rg_* ⋙ RΓ(Z, -) ≅ RΓ(T, -)`

as functors `D(T_étale) ⟶ D(Ab)` on the unbounded derived categories of abelian sheaves for the
small étale topology. Nothing is assumed of `g`, and no boundedness is assumed of the
coefficients.

Both sides are right derived functors of the same functor on the unbounded homotopy category of
complexes of abelian sheaves on `T`: the underived identification is
`Stacks.EtaleCohomology.smallEtalePushforwardGammaIsoAb`, and the composite of the two derivations
is a derivation of the composite by
`Stacks.EtaleCohomology.computesSecond_smallEtalePushforwardAb_globalSections`.

This is the abelian instance on small étale sites of the global-sections statement of Stacks
0D6H, whose tagged form for ringed sites and module coefficients is
`Stacks.Cohomology.LerayUnbounded.derivedGlobalSectionsPushforwardIsoGeneral`; see the
implementation notes of this file for why no attribute is carried here. Taking `g` to be
`AlgebraicGeometry.geometricFibreToPoint f s` gives the comparison `RΓ(s, Rq_*M) ≅ RΓ(X_s, M)`
for the geometric fibre of a morphism at a geometric point. -/
public def smallEtaleDerivedGlobalSectionsPushforwardIsoAb :
    smallEtaleDerivedPushforwardAb g ⋙ smallEtaleDerivedGlobalSections Z ≅
      smallEtaleDerivedGlobalSections T :=
  Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes (smallEtalePushforwardAb g)
    (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
    (smallEtalePushforwardGammaIsoAb g) (computesSecond_smallEtalePushforwardAb_globalSections g)

/-- **The factorization that determines the global-sections isomorphism.** On every complex `J`
of abelian sheaves on the small étale site of `T`, the isomorphism
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsPushforwardIsoAb`, precomposed with the
unit of the derivation of global sections on `Z` and with the image of the unit of the derivation
of direct image, is the degreewise underived identification
`Stacks.EtaleCohomology.smallEtalePushforwardGammaIsoAb` followed by the unit of the derivation
of global sections on `T`.

The isomorphism is `CategoryTheory.Functor.rightDerivedNatIso` between two right derived functors
of one and the same functor on the unbounded homotopy category, so this is one application of
`CategoryTheory.Functor.rightDerivedNatTrans_app`, the composite of the two units being the
comparison `Stacks.Cohomology.LerayUnbounded.derivedCompUnit` that exhibits `Rg_* ⋙ RΓ(Z, -)` as
such a derived functor. Since the source is a right derived functor, this property determines the
map; it is what lets the isomorphism be composed with any other transformation pinned by the same
units, such as the two canonical maps of Stacks 0GIX. -/
public theorem smallEtaleDerivedGlobalSectionsPushforwardIsoAb_fac_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedGlobalSectionsUnit Z).app
          (((smallEtalePushforwardAb g).mapHomotopyCategory (.up ℤ)).obj J) ≫
        (smallEtaleDerivedGlobalSections Z).map
            ((smallEtaleDerivedPushforwardAbUnit g).app J) ≫
          (smallEtaleDerivedGlobalSectionsPushforwardIsoAb g).hom.app
            (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (smallEtalePushforwardGammaIsoAb g) (.up ℤ)).hom.app J) ≫
        (smallEtaleDerivedGlobalSectionsUnit T).app J :=
  let := Stacks.Cohomology.LerayUnbounded.isRightDerivedFunctor_derivedCompUnit_of_computes
    (smallEtalePushforwardAb g) (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1})
    (computesSecond_smallEtalePushforwardAb_globalSections g)
  (Category.assoc _ _ _).symm.trans
    (Functor.rightDerivedNatTrans_app _ _
      (Stacks.Cohomology.LerayUnbounded.derivedCompUnit (smallEtalePushforwardAb g)
        (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}))
      (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}))
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
        (smallEtalePushforwardGammaIsoAb g) (.up ℤ)) DerivedCategory.Qh).hom J)

end Stacks.EtaleCohomology

end
