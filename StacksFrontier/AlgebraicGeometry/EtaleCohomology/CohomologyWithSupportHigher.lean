module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris

/-!
# Surjectivity of restriction to an open subscheme on an injective abelian sheaf

Let `j : U ⟶ X` be an open immersion of schemes of a big étale site and let `ℐ` be an injective
abelian sheaf on the small étale site of `X`.  This file proves that the unit
`ℐ ⟶ j_*(ℐ|_U)` of the inverse-image/direct-image adjunction along `j` is an epimorphism, and
deduces that the sequence

`0 ⟶ i_*ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0`

of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportSequence` is *short*
exact at an injective abelian sheaf, when `j` is the inclusion of the complement of a closed
immersion `i : Z ⟶ X`.

## Main results

* `AlgebraicGeometry.SmallEtale.surjective_openRestriction_unit_app_app_of_injective` — sections
  of the unit over an object of the small étale site of `X` are surjective.
* `AlgebraicGeometry.SmallEtale.epi_openRestriction_unit_app_of_injective` — hence the unit is an
  epimorphism of abelian sheaves.
* `AlgebraicGeometry.epi_complementRestriction_app_of_injective` — the same at the inclusion of
  the open complement of a closed immersion.
* `AlgebraicGeometry.supportedSectionsShortComplex_shortExact_of_injective` — the sequence
  `0 ⟶ i_*ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0` is short exact at an injective abelian sheaf.

## Implementation notes

Through `AlgebraicGeometry.SmallEtale.openRestrictionIso` and
`AlgebraicGeometry.SmallEtale.openRestrictionIso_unit_app`, the unit at an object `W` of the
small étale site of `X` is restriction of sections along the projection `W ×_X U ⟶ W`, the
counit of `AlgebraicGeometry.SmallEtale.openPostcomposeAdjunction`. That projection is an open
immersion of schemes, hence a monomorphism of the site, and restriction of sections of an
injective abelian sheaf along a monomorphism of the site is surjective by [Stacks, Tag 093X]
(`Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective`).

## References

* [Stacks Project, Tag 093X](https://stacks.math.columbia.edu/tag/093X)
* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X' X : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

/-- The projection `W ×_X U ⟶ W`, the counit of post-composition against base change, is an
open immersion of schemes. -/
public instance isOpenImmersion_openPostcomposeAdjunction_counit
    (W : SmallEtale B X.obj X.property) :
    IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
      ((openPostcomposeAdjunction B j).counit.app W)) := by
  rw [openPostcomposeAdjunction_counit_toScheme]
  have := hasPullbacks_bigEtaleSite B
  have : PreservesLimitsOfShape WalkingCospan B.inclusion :=
    preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback
    (IsPullback.map B.inclusion (IsPullback.of_hasPullback W.obj.hom j).flip)
    (show IsOpenImmersion (B.inclusion.map j) from inferInstance)

/-- The counit of post-composition against base change is a monomorphism of the small étale
site. -/
public instance mono_openPostcomposeAdjunction_counit
    (W : SmallEtale B X.obj X.property) :
    Mono ((openPostcomposeAdjunction B j).counit.app W) :=
  (SmallEtale.toScheme B X.obj X.property).mono_of_mono_map
    (inferInstanceAs (Mono ((SmallEtale.toScheme B X.obj X.property).map
      ((openPostcomposeAdjunction B j).counit.app W))))

/-- **Sections of the unit `ℐ ⟶ j_*(ℐ|_U)` over an object of the small étale site of `X` are
surjective, for `ℐ` injective.** -/
public theorem surjective_openRestriction_unit_app_app_of_injective
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    [Injective I] (W : SmallEtale B X.obj X.property) :
    Function.Surjective
      ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app I).hom.app (op W)) := by
  intro t
  have hiso : Function.Surjective
      (((openRestrictionIso.{u, v} B j).hom.app I).hom.app
        (op ((smallEtaleBaseChange B j).obj W))) :=
    have : IsIso (((openRestrictionIso.{u, v} B j).hom.app I).hom.app
      (op ((smallEtaleBaseChange B j).obj W))) := inferInstance
    (ConcreteCategory.bijective_of_isIso _).2
  obtain ⟨s', hs'⟩ := hiso t
  obtain ⟨s, hs⟩ :=
    Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective
      (SmallEtale.topology B X.obj X.property) I
      ((openPostcomposeAdjunction B j).counit.app W) s'
  exact ⟨s, by rw [← openRestrictionIso_unit_app B j I W s, hs, hs']⟩

/-- **The unit `ℐ ⟶ j_*(ℐ|_U)` is an epimorphism of abelian sheaves, for `ℐ` injective.** -/
public theorem epi_openRestriction_unit_app_of_injective
    (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    [Injective I] :
    Epi (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).unit.app I) :=
  have : Sheaf.IsLocallySurjective
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app I) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      fun W => surjective_openRestriction_unit_app_app_of_injective B j I W.unop
  inferInstance

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- The inclusion of the open complement of a closed immersion is an open immersion. -/
public instance isOpenImmersion_closedComplementInclusion :
    IsOpenImmersion (B.inclusion.map (closedComplementInclusion B i)) := by
  change IsOpenImmersion (closedComplementOpen B i).ι
  infer_instance

/-- **Restriction to the open complement is surjective on an injective abelian sheaf.**  The
component at an injective abelian sheaf of the natural transformation `𝟭 ⟶ j_*j^{-1}` is an
epimorphism, `j` being the inclusion of the open complement of the closed immersion. -/
public theorem epi_complementRestriction_app_of_injective
    (I : SmallEtaleAbelianSheaf B X) [Injective I] :
    Epi ((complementRestriction B i).app I) :=
  SmallEtale.epi_openRestriction_unit_app_of_injective.{u, u + 1} B
    (closedComplementInclusion B i) I

/-- **The sequence `0 ⟶ i_*ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0` is short exact at an injective abelian
sheaf.** -/
public theorem supportedSectionsShortComplex_shortExact_of_injective
    (I : SmallEtaleAbelianSheaf B X) [Injective I] :
    (supportedSectionsShortComplex B i I).ShortExact where
  exact := supportedSectionsShortComplex_exact B i I
  mono_f := mono_supportedSectionsPushforwardInclusion_app B i I
  epi_g := epi_complementRestriction_app_of_injective B i I

end AlgebraicGeometry

end
