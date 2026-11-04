module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkCohomology

/-!
# Restriction maps on the étale cohomology of algebraic spaces

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism of
its objects. This file supplies the three pieces of structure that compare the étale cohomology
of `X` with that of `Y`:

* the derived adjunction `f⁻¹ ⊣ Rf_*` on the unbounded derived categories of abelian sheaves on
  the spaces-étale sites;
* the identification `f⁻¹ ℤ_X ≅ ℤ_Y` of the inverse image of a constant sheaf;
* the canonical restriction map `Hⁿ(X, F) ⟶ Hⁿ(Y, f⁻¹ F)`, which is the map of Stacks 0DG5 for
  the projection `X_{k'} ⟶ X`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleDerivedAdjunction`: `f⁻¹ ⊣ Rf_*`.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleAbelianInverseImageConstantIso`: inverse image
  carries constant sheaves to constant sheaves.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleCohomologyRestrictionMap`: the restriction map
  on étale cohomology.

## Implementation notes

As for schemes (`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`), the restriction map is
the map on `Ext` groups out of the constant sheaf `ℤ` induced by the exact functor `f⁻¹`,
followed by the identification of `f⁻¹ ℤ_X` with `ℤ_Y`. That identification involves no choice:
both functors are left adjoint to evaluation at the final object of the spaces-étale site of `X`,
base change carrying the final object to a final object.

## References

* [Stacks Project, Tag 0DG5](https://stacks.math.columbia.edu/tag/0DG5)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Homology.DerivedSquare (totalRightDerived totalRightDerivedUnit)
open AlgebraicGeometry.Space

universe u w

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- **The derived inverse image is left adjoint to the derived direct image** on the unbounded
derived categories of abelian sheaves on the spaces-étale sites (Stacks 09T5): the underived
adjunction `f⁻¹ ⊣ f_*` has an exact left adjoint, and K-injective resolutions exist in the
Grothendieck abelian category of abelian sheaves. -/
def smallEtaleDerivedAdjunction :
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f)).mapDerivedCategory ⊣
      totalRightDerived (smallEtalePushforward T f) :=
  Stacks.DerivedFunctor.derivedAdjunction (smallEtaleAbelianAdjunction T f)
    (totalRightDerived (smallEtalePushforward T f))
    (totalRightDerivedUnit (smallEtalePushforward T f))
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)

/-- **Inverse image carries constant sheaves to constant sheaves.** Both functors are left
adjoint to evaluation at the final object of the spaces-étale site of `X`, read on the
spaces-étale site of `Y` at the base change of that final object, which is final. -/
def smallEtaleAbelianInverseImageConstantIso :
    constantSheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1} ⋙
        CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f) ≅
      constantSheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1} :=
  ((constantSheafAdj (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}
      (Space.SpacesEtale.isTerminal_idObj T.fppfSite S T.fppf_mem X)).comp
    (smallEtaleAbelianAdjunction T f)).leftAdjointUniq
      ((constantSheafAdj (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}
        (Space.isTerminal_spacesBaseChange_idObj T.fppfSite S T.fppf_mem f)).ofNatIsoRight
          (NatIso.ofComponents (fun _ => Iso.refl _)
            (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)))

/-- **The restriction map on étale cohomology** `Hⁿ(X, F) ⟶ Hⁿ(Y, f⁻¹ F)` along a morphism
`f : Y ⟶ X` of algebraic spaces of the big étale site: apply the exact inverse-image functor to an
`Ext` class out of the constant sheaf `ℤ`, then identify the inverse image of that constant sheaf
with the constant sheaf on `Y`. -/
def spacesEtaleCohomologyRestrictionMap
    [HasExt.{w} (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})]
    [HasExt.{w} (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})]
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) (q : ℕ) :
    Sheaf.H.{w} F q →+
      Sheaf.H.{w} ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f)).obj F) q :=
  ((Abelian.Ext.mk₀
      ((smallEtaleAbelianInverseImageConstantIso T f).app
        (AddCommGrpCat.of (ULift ℤ))).inv).precomp
        ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f)).obj F)
        (Nat.zero_add q)).comp
    ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f)).mapExtAddHom
      ((constantSheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) F q)

end AlgebraicGeometry.BigEtaleSpaceSite

end
