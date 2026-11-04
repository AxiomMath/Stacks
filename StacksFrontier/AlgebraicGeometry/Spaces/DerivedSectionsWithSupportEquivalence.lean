module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveSectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedComplexesEquivalence
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedAdjunction

/-!
# The quasi-inverse of the supported derived equivalence is the derived sections with support

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. Direct image of
abelian sheaves on small étale sites induces an equivalence `i_* : D(Z_étale) ≌ D_{|Z|}(X_étale)`
whose quasi-inverse is the inverse image `i^{-1}`. This file shows that on `D_{|Z|}(X_étale)` the
inverse image also agrees with the derived functor `R𝓗_Z` of the sections with support in `|Z|`:

`i^{-1}|_{D_Z(X_étale)} = R𝓗_Z|_{D_{|Z|}(X_étale)}`.

## Main definitions

* `derivedSectionsWithSupportOnClosedSubspace` is `R𝓗_Z : D(X_étale) ⥤ D(Z_étale)` on unbounded
  derived categories, the total right derived functor of the functor `𝓗_Z` of sections with
  support in `|Z|`, with `derivedSectionsWithSupportOnClosedSubspaceUnit` its derivation unit.
* `derivedSmallEtalePushforwardDerivedSectionsWithSupportAdjunction` is the adjunction
  `i_*^D ⊣ R𝓗_Z` on unbounded derived categories.
* `derivedPushforwardCompDerivedSectionsWithSupportIsoId` is the resulting natural isomorphism
  `R𝓗_Z ∘ i_*^D ≅ 𝟭` on `D(Z_étale)`.

## Main results

* `derivedSmallEtalePushforwardSupportedEquivalence_inverse_derivedSectionsWithSupport`: the
  quasi-inverse of the equivalence `D(Z_étale) ≌ D_{|Z|}(X_étale)` is `R𝓗_Z` restricted to
  `D_{|Z|}(X_étale)`.
* `derivedSmallEtaleInverseImage_iso_derivedSectionsWithSupport_of_supported`: `i^{-1}` and
  `R𝓗_Z` agree on `D_{|Z|}(X_étale)`.
* `isRightDerivedFunctor_mapDerivedCategory_smallEtaleAbelianPushforward`: `Ri_* = i_*`, i.e. the
  degreewise action of `i_*` on unbounded derived categories is its right derived functor.

## References

* [Stacks Project, Lemma 69.9.4 (Tag 0AEI)](https://stacks.math.columbia.edu/tag/0AEI)
* [Stacks Project, Section 69.9 (Tag 0A4L)](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4M](https://stacks.math.columbia.edu/tag/0A4M)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Lemma 13.31.9 (Tag 08BJ)](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 100000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### K-injective resolutions of complexes of abelian sheaves -/

/-- Abelian sheaves on the small étale site of a presheaf on the big fppf category over `S` form
a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_smallEtaleAbelianSheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}) :=
  let : EssentiallySmall.{u + 1} (SmallEtale B S hS F) := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}

/-- **Stacks 079P for abelian sheaves on a small étale site.** Every cochain complex of abelian
sheaves on the small étale site of a presheaf on the big fppf category over `S` admits a
quasi-isomorphism into a K-injective complex. -/
theorem exists_quasiIso_isKInjective_smallEtaleAbelianSheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (K : CochainComplex (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}) ℤ) :
    ∃ (I : CochainComplex (Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}) ℤ)
      (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  let := isGrothendieckAbelian_smallEtaleAbelianSheaf B S hS F
  Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _ K

variable {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)

/-- **Stacks 08BJ for the small étale direct image.** The direct image of abelian sheaves along a
closed immersion carries K-injective cochain complexes to K-injective cochain complexes. -/
theorem isKInjective_smallEtaleAbelianPushforward_mapHomologicalComplex
    (J : CochainComplex (abelianSheaves.{u + 1} B S hS Z) ℤ) (hJ : J.IsKInjective) :
    CochainComplex.IsKInjective
      (((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) :=
  let := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  let := hJ
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _
    (smallEtaleAbelianInverseImage B S hS i hi.rep)
    (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep) J

/-! ### The derived functor `R𝓗_Z` on the unbounded derived category -/

/-- The functor `𝓗_Z` of sections with support in `|Z|`, taken degreewise on the homotopy category
and followed by the localization, has a pointwise right derived functor relative to the
quasi-isomorphisms: K-injective complexes compute it, and every complex has a K-injective
resolution. -/
instance hasPointwiseRightDerivedFunctor_sectionsWithSupportInClosedSubspace :
    Functor.HasPointwiseRightDerivedFunctor
      ((sectionsWithSupportInClosedSubspace B S hS i hi).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ)) := by
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 2, u + 2, u + 2, u + 2, u + 2}
    ((sectionsWithSupportInClosedSubspace B S hS i hi).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B S hS X.1)).1

/-- **The derived functor `R𝓗_Z : D(X_étale) ⥤ D(Z_étale)`**, on the unbounded derived
categories of abelian sheaves on small étale sites: the total right derived functor of the functor
`𝓗_Z` of sections with support in the point set of a closed immersion `i : Z ⟶ X`.

The bounded below version is
`AlgebraicGeometry.Space.derivedSectionsWithSupportInClosedSubspace`. -/
@[stacks 0A4L "the derived functor R𝓗_Z on unbounded derived categories"]
def derivedSectionsWithSupportOnClosedSubspace :
    smallEtaleDerivedCategory.{u + 1} B S hS X ⥤ smallEtaleDerivedCategory.{u + 1} B S hS Z :=
  Functor.totalRightDerived
    ((sectionsWithSupportInClosedSubspace B S hS i hi).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ))

/-- The canonical comparison from the sections with support in `|Z|` of a complex, taken
degreewise, to the value of `R𝓗_Z` on it. -/
abbrev derivedSectionsWithSupportOnClosedSubspaceUnit :
    (sectionsWithSupportInClosedSubspace B S hS i hi).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsWithSupportOnClosedSubspace B S hS i hi :=
  Functor.totalRightDerivedUnit
    ((sectionsWithSupportInClosedSubspace B S hS i hi).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ))

/-- The comparison exhibits `R𝓗_Z` as the right derived functor of `𝓗_Z`. -/
instance derivedSectionsWithSupportOnClosedSubspace_isRightDerivedFunctor :
    (derivedSectionsWithSupportOnClosedSubspace B S hS i hi).IsRightDerivedFunctor
      (derivedSectionsWithSupportOnClosedSubspaceUnit B S hS i hi)
      (HomotopyCategory.quasiIso (abelianSheaves.{u + 1} B S hS X) (ComplexShape.up ℤ)) := by
  dsimp only [derivedSectionsWithSupportOnClosedSubspace,
    derivedSectionsWithSupportOnClosedSubspaceUnit]
  infer_instance

/-! ### The derived adjunction `i_*^D ⊣ R𝓗_Z` -/

/-- The unit of the adjunction `i_* ⊣ 𝓗_Z` of Stacks 0A4M is an isomorphism: the direct image is
fully faithful by Stacks 04E5 part (2), so the sections with support in `|Z|` of a sheaf pushed
forward from `Z` recover that sheaf. -/
instance isIso_unit_pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion :
    IsIso (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i hi).unit :=
  haveI := (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).full
  haveI :=
    (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi).faithful
  inferInstance

/-- **The adjunction `i_*^D ⊣ R𝓗_Z` on unbounded derived categories.** The direct image `i_*` of
abelian sheaves along a closed immersion is exact, so it induces a functor on unbounded derived
categories by acting degreewise, and its underived right adjoint `𝓗_Z` derives to a right adjoint
of that functor. -/
def derivedSmallEtalePushforwardDerivedSectionsWithSupportAdjunction :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory ⊣
      derivedSectionsWithSupportOnClosedSubspace B S hS i hi := by
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint
    (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i hi)
    (derivedSectionsWithSupportOnClosedSubspace B S hS i hi)
    (derivedSectionsWithSupportOnClosedSubspaceUnit B S hS i hi)
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B S hS X.1)

/-- **The unit of the derived adjunction is invertible**, so `R𝓗_Z(i_*K) = K` for every `K` in
`D(Z_étale)`. -/
instance isIso_unit_derivedSmallEtalePushforwardDerivedSectionsWithSupportAdjunction :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    IsIso (derivedSmallEtalePushforwardDerivedSectionsWithSupportAdjunction B S hS i hi).unit := by
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact Stacks.Cohomology.SupportedComplexes.isIso_unit_of_fullyFaithful_of_isKInjective_map
    (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i hi)
    (isKInjective_smallEtaleAbelianPushforward_mapHomologicalComplex B S hS i hi)
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B S hS X.1)
    (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B S hS Z.1)
    (derivedSmallEtalePushforwardDerivedSectionsWithSupportAdjunction B S hS i hi)
    (Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint_unit_app
      (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i hi)
      (derivedSectionsWithSupportOnClosedSubspace B S hS i hi)
      (derivedSectionsWithSupportOnClosedSubspaceUnit B S hS i hi)
      (exists_quasiIso_isKInjective_smallEtaleAbelianSheaf B S hS X.1))

/-- **`R𝓗_Z ∘ i_*^D ≅ 𝟭` on `D(Z_étale)`**, the isomorphism being the inverse of the unit of the
derived adjunction. -/
def derivedPushforwardCompDerivedSectionsWithSupportIsoId :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory ⋙
        derivedSectionsWithSupportOnClosedSubspace B S hS i hi ≅
      𝟭 (smallEtaleDerivedCategory.{u + 1} B S hS Z) := by
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact (asIso (derivedSmallEtalePushforwardDerivedSectionsWithSupportAdjunction
    B S hS i hi).unit).symm

/-! ### The quasi-inverse of the equivalence -/

/-- **The quasi-inverse is the derived sections with support.** The quasi-inverse of the
equivalence `D(Z_étale) ≌ D_{|Z|}(X_étale)` induced by the direct image along a closed immersion
`i : Z ⟶ X` of algebraic spaces over `S` is the derived functor `R𝓗_Z` of sections with support
in `|Z|`, restricted to `D_{|Z|}(X_étale)`. -/
@[stacks 0AEI "the identification of the quasi-inverse with the derived sections with support \
R𝓗_Z, the second description in the displayed formula"]
def derivedSmallEtalePushforwardSupportedEquivalence_inverse_derivedSectionsWithSupport :
    (derivedSmallEtalePushforwardSupportedEquivalence B S hS i hi).inverse ≅
      (cohomologySupportedOn.{u + 1} B S hS X
          (Set.range (pointsMap B S hS Z.1 i.hom))).ι ⋙
        derivedSectionsWithSupportOnClosedSubspace B S hS i hi := by
  letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  set E := derivedSmallEtalePushforwardSupportedEquivalence B S hS i hi
  set ι := (cohomologySupportedOn.{u + 1} B S hS X
    (Set.range (pointsMap B S hS Z.1 i.hom))).ι
  set R := derivedSectionsWithSupportOnClosedSubspace B S hS i hi
  refine (Functor.rightUnitor E.inverse).symm ≪≫ ?_
  refine Functor.isoWhiskerLeft E.inverse
    (asIso (derivedSmallEtalePushforwardDerivedSectionsWithSupportAdjunction
      B S hS i hi).unit) ≪≫ ?_
  refine Functor.isoWhiskerLeft E.inverse (Functor.isoWhiskerRight
    (derivedSmallEtalePushforwardSupportedEquivalence_functor B S hS i hi).symm R) ≪≫ ?_
  refine Functor.isoWhiskerLeft E.inverse (Functor.associator E.functor ι R) ≪≫ ?_
  refine (Functor.associator E.inverse E.functor (ι ⋙ R)).symm ≪≫ ?_
  exact Functor.isoWhiskerRight E.counitIso (ι ⋙ R) ≪≫ Functor.leftUnitor (ι ⋙ R)

/-- **The inverse image agrees with the derived sections with support.** On the subcategory
`D_{|Z|}(X_étale)` of complexes of abelian sheaves whose cohomology sheaves are supported on the
point set of a closed immersion `i : Z ⟶ X`, the inverse image `i^{-1}` and the derived functor
`R𝓗_Z` of sections with support in `|Z|` agree:

`i^{-1}|_{D_Z(X_étale)} = R𝓗_Z|_{D_{|Z|}(X_étale)}`.

Both are the quasi-inverse of the equivalence
`AlgebraicGeometry.Space.derivedSmallEtalePushforwardSupportedEquivalence`. -/
@[stacks 0AEI "the displayed equality i^{-1}|_{D_Z} = R𝓗_Z|_{D_{|Z|}} of the two descriptions \
of the quasi-inverse"]
def derivedSmallEtaleInverseImage_iso_derivedSectionsWithSupport_of_supported :
    letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
    (cohomologySupportedOn.{u + 1} B S hS X
          (Set.range (pointsMap B S hS Z.1 i.hom))).ι ⋙
        (smallEtaleAbelianInverseImage B S hS i hi.rep).mapDerivedCategory ≅
      (cohomologySupportedOn.{u + 1} B S hS X
          (Set.range (pointsMap B S hS Z.1 i.hom))).ι ⋙
        derivedSectionsWithSupportOnClosedSubspace B S hS i hi := by
  letI := additive_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteLimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  letI := preservesFiniteColimits_smallEtaleAbelianInverseImage B S hS i hi.rep
  exact (derivedSmallEtalePushforwardSupportedEquivalence_inverse B S hS i hi).symm ≪≫
    derivedSmallEtalePushforwardSupportedEquivalence_inverse_derivedSectionsWithSupport
      B S hS i hi

/-- **`Ri_* = i_*`.** For a closed immersion `i`, the degreewise action of the direct image
`i_*` on unbounded derived categories is the right derived functor `Ri_*`. -/
@[stacks 0AEI "Ri_* = i_*, the pushforward along a closed immersion being its own right \
derived functor"]
theorem isRightDerivedFunctor_mapDerivedCategory_smallEtaleAbelianPushforward :
    letI := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategory.IsRightDerivedFunctor
      (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  let := preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi
  exact Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact _

end AlgebraicGeometry.Space

end
