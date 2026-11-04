module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Étale inverse image of abelian sheaves on spaces-étale sites preserves K-injectives

Let `h : U ⟶ V` be an étale morphism of algebraic spaces of a big étale site. The inverse
image of abelian sheaves along the morphism of spaces-étale topoi of `h` is restriction along
postcomposition with `h`, and it carries K-injective complexes to K-injective complexes.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleAbelianInverseImageIsoPostcomp`: the inverse
  image of abelian sheaves along an étale morphism is restriction along postcomposition.

## Main results

* `AlgebraicGeometry.Space.preservesEqualizers_spacesEtalePostcomp`: postcomposition preserves
  equalizers.
* `AlgebraicGeometry.BigEtaleSpaceSite.isKInjective_smallEtaleAbelianInverseImage_of_isEtale`:
  the étale inverse image preserves K-injective complexes.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The slice-category smallness instances `CategoryTheory.small_over` and
-- `CategoryTheory.locallySmall_over` send the searches for the sheaf pullback's left Kan
-- extensions here into a typeclass timeout, so they are switched off in this file.
attribute [-instance] CategoryTheory.small_over CategoryTheory.locallySmall_over

universe u

namespace AlgebraicGeometry.Space

/-- Postcomposition preserves equalizers of spaces-étale sites: they are computed on the
underlying algebraic spaces, which postcomposition leaves unchanged. -/
instance preservesEqualizers_spacesEtalePostcomp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    PreservesLimitsOfShape WalkingParallelPair (spacesEtalePostcomp B S hS f hf) :=
  have : ReflectsLimitsOfShape WalkingParallelPair (SpacesEtale.toSpaces B S hS Y) :=
    inferInstance
  have : PreservesLimitsOfShape WalkingParallelPair
      (spacesEtalePostcomp B S hS f hf ⋙ SpacesEtale.toSpaces B S hS Y) := by
    change PreservesLimitsOfShape WalkingParallelPair (SpacesEtale.toSpaces B S hS X)
    infer_instance
  preservesLimitsOfShape_of_reflects_of_preserves _ (SpacesEtale.toSpaces B S hS Y)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] smallEtaleAbelianInverseImage_additive

/-- The inverse image of abelian sheaves along the morphism of spaces-étale topoi of an étale
morphism `h` is restriction along postcomposition with `h`. -/
def smallEtaleAbelianInverseImageIsoPostcomp {U V : T.Spaces} (h : U ⟶ V)
    (hh : Space.IsEtale T.fppfSite S T.fppf_mem h.hom) :
    CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T h) ≅
      (Space.spacesEtalePostcomp T.fppfSite S T.fppf_mem h hh).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem U)
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem V) :=
  haveI : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem V) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  haveI : ((Space.spacesEtalePostcomp T.fppfSite S T.fppf_mem h hh).sheafPushforwardContinuous
      Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem U)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem V)).Additive := ⟨rfl⟩
  ProEtale.liftSheafNatIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem U) _ _
    (Functor.isoWhiskerLeft
      (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem V) (forget Ab.{u + 1}))
      (Space.spacesToposMorphism_inverseImageIso T.fppfSite S T.fppf_mem h hh))

/-- **The étale inverse image of abelian sheaves preserves K-injective complexes.** -/
theorem isKInjective_smallEtaleAbelianInverseImage_of_isEtale {U V : T.Spaces} (h : U ⟶ V)
    (hh : Space.IsEtale T.fppfSite S T.fppf_mem h.hom)
    (I : CochainComplex (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem V)
      Ab.{u + 1}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T h)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let u' := Space.spacesEtalePostcomp T.fppfSite S T.fppf_mem h hh
  let J' := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem U
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem V
  let R := u'.sheafPushforwardContinuous Ab.{u + 1} J' J
  let L := Functor.sheafPullbackConstruction.sheafPullback u' Ab.{u + 1} J' J
  let adj : L ⊣ R := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u' Ab.{u + 1} J' J
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u + 1, u + 1, u + 1, u + 1}
      u' J' J
  have : PreservesFiniteColimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits AddCommGrpCat.{u + 1} u' J' J
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  have hR := CochainComplex.isKInjective_mapHomologicalComplex_of_exact R L adj I
  exact CochainComplex.isKInjective_of_iso
    (((NatIso.mapHomologicalComplex (smallEtaleAbelianInverseImageIsoPostcomp T h hh)
      (ComplexShape.up ℤ)).app I).symm)

end AlgebraicGeometry.BigEtaleSpaceSite

end
