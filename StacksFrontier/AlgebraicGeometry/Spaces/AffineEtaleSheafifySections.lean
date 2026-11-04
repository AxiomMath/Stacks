module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctions
public import StacksFrontier.CategoryTheory.Sites.DenseSubsiteSheafifySections

/-!
# Sheafification on the small étale site does not change the affine charts

Let `F` be an algebraic space over a scheme `S` and let `P` be a presheaf of commutative rings
on its small étale site.  The affine étale charts of `F` form a dense subsite of the small étale
site (Stacks 04JS); if the restriction of `P` to the affine charts is a sheaf, then the canonical
map `P ⟶ P^#` into the sheafification is an isomorphism over every affine chart.

## Main results

* `AlgebraicGeometry.Space.isIso_toSheafify_app_affineEtale`: the canonical map into the
  sheafification is an isomorphism over an object of the affine étale site, and
* `AlgebraicGeometry.Space.isIso_toSheafify_app_of_isAffine`: the same, stated for an étale
  chart whose underlying scheme is affine.

## References

* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Sheafification on the small étale site does not change the sections over an affine
chart**, as soon as the restriction of the presheaf to the affine étale charts is a sheaf. -/
theorem isIso_toSheafify_app_affineEtale (hF : IsAlgebraicSpace B S hS F)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u})
    (hP : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      ((AffineEtale.inclusion B S hS F).op ⋙ P))
    (U : AffineEtale B S hS F) :
    IsIso ((toSheafify (SmallEtale.topology B S hS F) P).app
      (op ((AffineEtale.inclusion B S hS F).obj U))) := by
  obtain ⟨_, _⟩ := AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF
  exact Presheaf.isIso_toSheafify_app_of_isDenseSubsite _ _ _ P hP U

/-- **Sheafification on the small étale site does not change the sections over a chart with
affine underlying scheme**, as soon as the restriction of the presheaf to the affine étale
charts is a sheaf. -/
theorem isIso_toSheafify_app_of_isAffine (hF : IsAlgebraicSpace B S hS F)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u})
    (hP : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      ((AffineEtale.inclusion B S hS F).op ⋙ P))
    (U : SmallEtale B S hS F) (hU : IsAffine (smallEtaleScheme B S hS F U)) :
    IsIso ((toSheafify (SmallEtale.topology B S hS F) P).app (op U)) :=
  isIso_toSheafify_app_affineEtale B S hS F hF P hP ⟨U, hU⟩

end AlgebraicGeometry.Space

end
