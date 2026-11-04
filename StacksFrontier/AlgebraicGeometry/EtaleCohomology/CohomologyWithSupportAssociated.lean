module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExactIdentity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportLongExact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallEtaleAssociatedModuleColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsLongExact

/-!
# Cohomology with support of an associated sheaf on the small étale site

Let `X` be a scheme of a big étale site `B`, let `Z ⊆ X` be a closed subset with open complement
`U`, and let `i : Z' ⟶ X` be a closed immersion of `B`.  On `𝒪_X`-modules the functor
`F ↦ i_*ℋ_Z(F)` of sections supported on `Z` sits in a short complex
`i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)` which is short exact on injectives, and so does the functor
`G ↦ i_*ℋ_{Z'}(G)` on abelian sheaves of the small étale site of `X`.  The two long exact
sequences of right derived functors then determine `R^q(i_*ℋ_Z)` from the restriction map
`F ⟶ j_*(F|_U)` and from the higher direct images `R^p j_*(F|_U)`, `p ≥ 1`, and likewise on the
étale side (Stacks 0A45).

The functor which compares the two sides is `F ↦ Fᵃ`: the associated module on the small étale
site, `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, followed by its underlying abelian
sheaf and the universe lift of abelian sheaves, the étale functor `i_*ℋ_{Z'}` being defined on
abelian sheaves with coefficients in the next universe.  All three factors are exact.  This file
proves that, and deduces that whenever `Fᵃ` carries the restriction map of `F` to that of `Fᵃ`
and commutes with the higher direct images along `j`, it carries `i_*ℋ^q_Z(F)` to
`i_*ℋ^q_{Z'}(Fᵃ)` for every `q`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedSheafULift`: the functor `F ↦ Fᵃ` from `𝒪_X`-modules
  to abelian sheaves of the small étale site of `X` in the next universe.
* `AlgebraicGeometry.supportedCohomologyAssociatedSheafULiftIso`: `(i_*ℋ^q_Z(F))ᵃ ≅
  i_*ℋ^q_{Z'}(Fᵃ)` for every `q`, from the compatibility of `F ↦ Fᵃ` with `F ⟶ j_*(F|_U)` and
  with `R^p j_*`, `p ≥ 1`.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedSheafULift` and
  `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedSheafULift`: `F ↦ Fᵃ` is exact.

## Implementation notes

The closed subset `Z` of the Zariski side and the closed immersion `i` of the étale side are
independent parameters of `AlgebraicGeometry.supportedCohomologyAssociatedSheafULiftIso`: the
two hypotheses comparing the restriction maps and the higher direct images are what relate them,
and the conclusion is an instance of
`CategoryTheory.mapRightDerivedIsoOfShortExactOnInjectives`.

The source category of `AlgebraicGeometry.SmallEtale.associatedSheafULift` is spelled
`SheafOfModules (structureSheafRing X)`, the spelling of the Zariski functor `i_*ℋ_Z`, while
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf` is stated on
`SheafOfModules X.ringCatSheaf`.  The two are equal by `rfl`, but instance search does not
identify them, so the exactness instances are found on
`AlgebraicGeometry.SmallEtale.associatedSheafULiftAux`, the same composite in the second
spelling, and transported by `exact`.

Right exactness of the underlying abelian sheaf functor needs the sheafification instances of
the small étale site at `AddCommGrpCat.{u}`.  They are found by instance search on their own,
but not as arguments of `Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf`, whose
universe parameters are then left undetermined, so they are passed explicitly.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 0A46](https://stacks.math.columbia.edu/tag/0A46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- `F ↦ Fᵃ` with coefficients in the next universe, on `SheafOfModules X.ringCatSheaf`, the
spelling of the source category of `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, in
which instance search sees through the composite. -/
abbrev associatedSheafULiftAux :
    SheafOfModules.{u} X.obj.ringCatSheaf ⥤ SmallEtaleAbelianSheaf B X :=
  associatedModuleOfSheaf B X.obj X.property ⋙
    SheafOfModules.toSheaf.{u} (structureSheaf B X.obj X.property) ⋙
      Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
        (SmallEtale.topology B X.obj X.property)

/-- **`F ↦ Fᵃ` with coefficients in the next universe.**  The associated module of an
`𝒪_X`-module on the small étale site of `X`, read as an abelian sheaf and lifted to the
universe of the coefficients of `AlgebraicGeometry.SmallEtaleAbelianSheaf`. -/
public def associatedSheafULift :
    SheafOfModules.{u} (structureSheafRing X.obj.toRingedSpace) ⥤ SmallEtaleAbelianSheaf B X :=
  associatedSheafULiftAux B X

/-- On a module, `AlgebraicGeometry.SmallEtale.associatedSheafULift` is the universe lift of the
abelian sheaf underlying the associated module. -/
public theorem associatedSheafULift_obj (F : SheafOfModules.{u} X.obj.ringCatSheaf) :
    (associatedSheafULift B X).obj F =
      (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u}
        (SmallEtale.topology B X.obj X.property)).obj
        ((SheafOfModules.toSheaf.{u} (structureSheaf B X.obj X.property)).obj
          ((associatedModuleOfSheaf B X.obj X.property).obj F)) := rfl

/-- **`F ↦ Fᵃ` is left exact**: the associated module is (Stacks 08H8), and so are the
underlying abelian sheaf and the universe lift. -/
public instance preservesFiniteLimits_associatedSheafULift :
    PreservesFiniteLimits (associatedSheafULift B X) := by
  have : PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} (structureSheaf B X.obj X.property)) := inferInstance
  have h : PreservesFiniteLimits (associatedSheafULiftAux B X) := inferInstance
  exact h

/-- **`F ↦ Fᵃ` is right exact**: the associated module is a left adjoint, and the underlying
abelian sheaf and the universe lift preserve finite colimits. -/
public instance preservesFiniteColimits_associatedSheafULift :
    PreservesFiniteColimits (associatedSheafULift B X) := by
  have h₁ : HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u} :=
    inferInstance
  have h₂ : (SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have := @Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _ _ _
    (structureSheaf B X.obj X.property) h₁ h₂
  have : PreservesFiniteColimits (associatedModuleOfSheaf B X.obj X.property) :=
    ⟨fun K _ _ => preservesColimitsOfShape_associatedModuleOfSheaf B X.obj X.property K⟩
  have h : PreservesFiniteColimits (associatedSheafULiftAux B X) := inferInstance
  exact h

end SmallEtale

open Stacks.Cohomology.SupportedComplexes ExtensionByZeroModules
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.SheafOfModules.SupportedSections

variable (B : BigEtaleSite.{u}) {Z' X : B.Scheme} (i : Z' ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)] (Z : Set X.obj) (hZ : IsClosed Z)

/-- **`(i_*ℋ^q_Z(F))ᵃ ≅ i_*ℋ^q_{Z'}(Fᵃ)` for every `q`**, granted that `F ↦ Fᵃ` carries the
restriction map `F ⟶ j_*(F|_U)` to the restriction map `Fᵃ ⟶ j_*(Fᵃ|_U)` up to an isomorphism
`e₀`, and the higher direct images `R^p j_*(F|_U)` to `R^p(j_*(-|_U))(Fᵃ)` for `p ≥ 1`.

Both sides sit in the long exact sequences of the short complexes `i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)`,
which are short exact on injectives, and `F ↦ Fᵃ` is exact, so this is
`CategoryTheory.mapRightDerivedIsoOfShortExactOnInjectives`. -/
public def supportedCohomologyAssociatedSheafULiftIso
    (F : SheafOfModules.{u} (structureSheafRing X.obj.toRingedSpace))
    (e₀ : (SmallEtale.associatedSheafULift B X).obj
        ((jStar (openComplement Z hZ) (structureSheafRing X.obj.toRingedSpace) ⋙
          jPush (openComplement Z hZ) (structureSheafRing X.obj.toRingedSpace)).obj F) ≅
      (complementPullbackPushforward B i).obj ((SmallEtale.associatedSheafULift B X).obj F))
    (hw : (SmallEtale.associatedSheafULift B X).map
        ((jStarAdjunction (openComplement Z hZ)
          (structureSheafRing X.obj.toRingedSpace)).unit.app F) ≫ e₀.hom =
      (complementRestriction B i).app ((SmallEtale.associatedSheafULift B X).obj F))
    (e : ∀ p : ℕ, 0 < p → ((SmallEtale.associatedSheafULift B X).obj
        (((jStar (openComplement Z hZ) (structureSheafRing X.obj.toRingedSpace) ⋙
          jPush (openComplement Z hZ) (structureSheafRing X.obj.toRingedSpace)).rightDerived
            p).obj F) ≅
      ((complementPullbackPushforward B i).rightDerived p).obj
        ((SmallEtale.associatedSheafULift B X).obj F)))
    (q : ℕ) :
    (SmallEtale.associatedSheafULift B X).obj
        (((supportedSectionsFunctor X.obj.toRingedSpace Z).rightDerived q).obj F) ≅
      ((supportedSectionsPushforward B i).rightDerived q).obj
        ((SmallEtale.associatedSheafULift B X).obj F) :=
  mapRightDerivedIsoOfShortExactOnInjectives _ _ _
    (supportedSectionsShortComplex_shortExact_on_injectives X.obj.toRingedSpace Z hZ)
    (supportedSectionsPushforwardInclusion B i) (complementRestriction B i)
    (supportedSectionsPushforwardInclusion_comp_complementRestriction B i)
    (supportedShortComplex_shortExact_on_injectives B i)
    (SmallEtale.associatedSheafULift B X) F e₀ hw e q

end AlgebraicGeometry

end
