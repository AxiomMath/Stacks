module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.CategoryTheory.Sites.DenseSubsiteSheafifySections

/-!
# Sheafification of a presheaf of modules does not change the affine charts

Let `F` be an algebraic space over a scheme `S`, let `R` be a sheaf of rings on its small étale
site and let `P` be a presheaf of `R`-modules.  The affine étale charts of `F` form a dense
subsite of the small étale site (Stacks 04JS), so if the restriction of `P` to the affine charts
is already a sheaf, then the unit `P ⟶ P^#` of the sheafification of presheaves of modules is an
isomorphism over every affine chart.

This is the module analogue of
`AlgebraicGeometry.Space.isIso_toSheafify_app_of_isAffine`: the step that turns a computation of
the sections of a presheaf of modules on affine charts into a computation of the sections of its
sheafification there.  Its intended use is the sheaf `𝒦_F(M)` of meromorphic sections of
Stacks 0EN5, which is by definition the sheafification of the presheaf `M ⊗_{𝒪_F} 𝒦_F`, so that
`𝒦_F(M)(U) = M(U) ⊗_{𝒪_F(U)} 𝒦_F(U)` over an affine chart `U`.

## Main results

* `AlgebraicGeometry.Space.isIso_sheafificationUnit_app_affineEtale` and
  `AlgebraicGeometry.Space.isIso_sheafificationUnit_app_of_isAffine`: the unit of the
  sheafification of a presheaf of modules is an isomorphism over an affine chart.
* `AlgebraicGeometry.Space.bijective_toMeromorphicSectionSheaf_of_isAffine`: over an affine chart
  the sections of `𝒦_F(M)` are exactly those of `M ⊗_{𝒪_F} 𝒦_F`.

## Implementation notes

The underlying morphism of presheaves of abelian groups of the unit of
`PresheafOfModules.sheafification` is the unit of the sheafification of presheaves of abelian
groups (`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`), so the content is
`CategoryTheory.Presheaf.isIso_toSheafify_app_of_isDenseSubsite` applied to
`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`; what remains is that a
morphism of modules which is bijective is an isomorphism, the forgetful functor of `ModuleCat`
reflecting isomorphisms.  Presheaves of abelian groups on the small étale site admit
sheafification in the universe `max (u + 1) z` of the sections of `𝒦_F(M)` through
`AlgebraicGeometry.Space.moduleHasWeakSheafify`, where the local equivalences are the locally
bijective morphisms by `AlgebraicGeometry.Space.moduleWEqualsLocallyBijective`.

## References

* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u z

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Sheafification of a presheaf of modules on the small étale site does not change the
sections over an affine chart**, as soon as the restriction of the presheaf to the affine étale
charts is a sheaf. -/
theorem isIso_sheafificationUnit_app_affineEtale (hF : IsAlgebraicSpace B S hS F)
    (R : Sheaf (SmallEtale.topology B S hS F) RingCat.{u})
    (P : PresheafOfModules.{max (u + 1) z} R.obj)
    (hP : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      ((AffineEtale.inclusion B S hS F).op ⋙ P.presheaf))
    (U : AffineEtale B S hS F) :
    IsIso (((PresheafOfModules.sheafificationAdjunction.{max (u + 1) z}
        (𝟙 R.obj)).unit.app P).app
      (op ((AffineEtale.inclusion B S hS F).obj U))) := by
  obtain ⟨h₁, h₂⟩ := AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF
  have : IsIso ((toSheafify (SmallEtale.topology B S hS F) P.presheaf).app
      (op ((AffineEtale.inclusion B S hS F).obj U))) :=
    Presheaf.isIso_toSheafify_app_of_isDenseSubsite _ _ _ P.presheaf hP U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify (SmallEtale.topology B S hS F) P.presheaf).app
      (op ((AffineEtale.inclusion B S hS F).obj U)))

/-- **Sheafification of a presheaf of modules on the small étale site does not change the
sections over a chart with affine underlying scheme**, as soon as the restriction of the
presheaf to the affine étale charts is a sheaf. -/
theorem isIso_sheafificationUnit_app_of_isAffine (hF : IsAlgebraicSpace B S hS F)
    (R : Sheaf (SmallEtale.topology B S hS F) RingCat.{u})
    (P : PresheafOfModules.{max (u + 1) z} R.obj)
    (hP : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      ((AffineEtale.inclusion B S hS F).op ⋙ P.presheaf))
    (U : SmallEtale B S hS F) (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    IsIso (((PresheafOfModules.sheafificationAdjunction.{max (u + 1) z}
      (𝟙 R.obj)).unit.app P).app (op U)) :=
  isIso_sheafificationUnit_app_affineEtale.{u, z} B S hS F hF R P hP ⟨U, hU⟩

/-- **Over an affine chart the sheaf of meromorphic sections of Stacks 0EN5 has exactly the
sections of the presheaf `M ⊗_{𝒪_F} 𝒦_F`**, as soon as that presheaf is a sheaf on the affine
étale charts. -/
theorem bijective_toMeromorphicSectionSheaf_of_isAffine (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u} B S hS F hF)
    (hM : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      ((AffineEtale.inclusion B S hS F).op ⋙ meromorphicSectionModuleUp B S hS F hF M))
    (U : SmallEtale B S hS F) (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    Function.Bijective (toMeromorphicSectionSheaf B S hS F hF M U) := by
  obtain ⟨h₁, h₂⟩ := AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF
  have : IsIso ((toSheafify (SmallEtale.topology B S hS F)
      (meromorphicSectionModuleUp B S hS F hF M)).app (op U)) :=
    Presheaf.isIso_toSheafify_app_of_isDenseSubsite _ _ _
      (meromorphicSectionModuleUp B S hS F hF M) hM ⟨U, hU⟩
  exact (ConcreteCategory.bijective_of_isIso
    ((toSheafify (SmallEtale.topology B S hS F)
      (meromorphicSectionModuleUp B S hS F hF M)).app (op U))).comp
    Equiv.ulift.symm.bijective

end AlgebraicGeometry.Space

end
