module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.Cotangent.Spaces.CotangentComplex

/-!
# The inverse image of the structure sheaf along an étale morphism, at the universe of the site

Let `p : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The first clause of Stacks 03LV is `p⁻¹𝒪_X = 𝒪_U`.  This file supplies that
clause for the structure sheaves whose sections have been lifted into the universe of the small
étale sites:

`p_small⁻¹(ULift 𝒪_X) ≅ ULift 𝒪_U`,

the inverse image now being that of the morphism of small étale topoi at `Type (u + 1)`.  Here
`AlgebraicGeometry.Space.smallEtaleStructureSheafULift` is the sheaf of rings over which
`AlgebraicGeometry.Space.cotangentComplex` is a complex of modules.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictionStructureSheafIso`: the restriction of `𝒪_X` along
  small étale postcomposition with `p` is `𝒪_U`, at the universe of the structure rings.
* `AlgebraicGeometry.Space.etaleInverseImageStructureSheafULiftIso`: the isomorphism
  `p_small⁻¹(ULift 𝒪_X) ≅ ULift 𝒪_U` of sheaves of commutative rings with sections in the
  universe of the small étale site of `U`.

## Main results

* `AlgebraicGeometry.Space.etaleInverseImageStructureSheafULiftIso_hom`: the forward map is the
  composite of the two canonical comparisons it is built from.

## Implementation notes

The inverse image of the morphism of small étale topoi is restriction along the postcomposition
functor of Stacks 03LP, at `Type (u + 1)` by
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` and at the universe `u` of the
structure rings by `AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`.
Restriction along a functor of sites commutes with `AlgebraicGeometry.SheafOfModules.sheafULift`
on the nose, so the comparison is the `Type (u + 1)` restriction comparison followed by
`sheafULift` applied to `AlgebraicGeometry.Space.etaleInverseImageStructureSheafIso`.

Here `u` is the universe of the algebraic spaces and of their structure rings, and `u + 1` is
the universe of their small étale sites.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 08VD](https://stacks.math.columbia.edu/tag/08VD)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X : AlgebraicSpaces B S hS}

/-- **Stacks 03LV, the clause `p⁻¹𝒪_X = 𝒪_U`, in restriction form.**  For an étale morphism
`p : U ⟶ X` of algebraic spaces, the restriction of the structure sheaf of `X` along small
étale postcomposition with `p` is the structure sheaf of `U`, as sheaves of commutative rings
with sections in the universe of the structure rings. -/
noncomputable def etaleRestrictionStructureSheafIso (p : U ⟶ X)
    (hp : IsEtale B S hS p.hom) :
    ((smallEtalePostcomp B S hS p hp).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)).obj
        (smallEtaleRingedTopos B S hS X).O ≅
      (smallEtaleRingedTopos B S hS U).O :=
  (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
      (smallEtaleRingedToposHom B S hS p).toToposHom
      (smallToposMorphismTypeU_inverseImageIso B S hS p hp)
      (smallEtaleRingedTopos B S hS X).O).symm ≪≫
    etaleInverseImageStructureSheafIso B S hS p hp

/-- **Stacks 03LV, the clause `p⁻¹𝒪_X = 𝒪_U`, at the universe of the small étale sites.**  For
an étale morphism `p : U ⟶ X` of algebraic spaces, the inverse image along the morphism of
small étale topoi of the structure sheaf of `X` with sections lifted into the universe of the
site is the structure sheaf of `U` with its sections lifted likewise. -/
noncomputable def etaleInverseImageStructureSheafULiftIso (p : U ⟶ X)
    (hp : IsEtale B S hS p.hom) :
    (smallToposMorphism B S hS p).inverseImageRing.obj
        (smallEtaleStructureSheafULift B S hS X) ≅
      smallEtaleStructureSheafULift B S hS U :=
  inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
      (smallToposMorphism B S hS p) (smallToposMorphism_inverseImageIso B S hS p hp)
      (smallEtaleStructureSheafULift B S hS X) ≪≫
    (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).mapIso
      (etaleRestrictionStructureSheafIso B S hS p hp)

/-- The forward map of `AlgebraicGeometry.Space.etaleInverseImageStructureSheafULiftIso` is the
identification of the inverse image with restriction, followed by the lift of the clause of
Stacks 03LV at the universe of the structure rings. -/
lemma etaleInverseImageStructureSheafULiftIso_hom (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    (etaleInverseImageStructureSheafULiftIso B S hS p hp).hom =
      (inverseImageCommRingRestrictionIso (SmallEtale.topology B S hS U.1)
          (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS p hp)
          (smallToposMorphism B S hS p) (smallToposMorphism_inverseImageIso B S hS p hp)
          (smallEtaleStructureSheafULift B S hS X)).hom ≫
        (SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS U.1)).map
          (etaleRestrictionStructureSheafIso B S hS p hp).hom :=
  rfl

end AlgebraicGeometry.Space

end
