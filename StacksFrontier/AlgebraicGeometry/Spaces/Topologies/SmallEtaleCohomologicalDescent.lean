module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleCohomology
public import StacksFrontier.CategoryTheory.Adjunction.AdjunctionUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Cohomological descent for the big étale topos of an algebraic space (Stacks 0DGC)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `X` one of its objects.
The morphism of topoi `π_X` from the big étale topos of `X` to its spaces-étale topos has the
property that `π_{X,*} ∘ π_X⁻¹` is the identity, so a complex on the spaces-étale site of `X`
is recovered from its inverse image: the canonical map `K ⟶ Rπ_{X,*}π_X⁻¹K` is an isomorphism
for every unbounded derived object `K`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleAbelianAdjunction` is the adjunction
  `π_X⁻¹ ⊣ π_{X,*}` on abelian sheaves and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleDerivedAdjunction` is its descent to the
  unbounded derived categories, whose unit is the map of the source.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_inverseImage_comp_pushforwardIso`:
  `π_{X,*} ∘ π_X⁻¹` is the identity on sheaves of sets, and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_abelianInverseImage_comp_restrictionIso` the
  same on abelian sheaves.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedAdjunction_unit`:
  **Stacks 0DGC**.

## Implementation notes

The composite identity `π_{X,*} ∘ π_X⁻¹ ≅ 𝟭` is the identity-morphism case of the
transitivity isomorphism of Tag 0DG7: `π_X⁻¹ ⋙ i_f⁻¹ ≅ f_small⁻¹` at `f = 𝟙 X`, after
identifying `i_X⁻¹` with `π_{X,*}` — which is Tag 0DF3 — and `(𝟙 X)_small⁻¹` with the identity
functor, base change along an identity being an identity.

Both `π_X⁻¹` and `π_{X,*}` are exact, so neither needs a derived functor of its own: they act
on the derived categories through `CategoryTheory.Functor.mapDerivedCategory`, and
`Rπ_{X,*} = π_{X,*}` there. The map of the source is the unit of the derived adjunction, and it
is an isomorphism by `Stacks.Adjunction.isIso_unit_of_comp_iso_id` — the composite being
isomorphic to the identity is enough, the isomorphism need not be known to be the inverse of
the unit.

The abelian statements are obtained from the statements for sheaves of sets by
`AlgebraicGeometry.ProEtale.liftSheafNatIso`, a natural transformation of the underlying
sheaves of sets between additive functors into abelian sheaves being automatically additive.

## References

* [Stacks Project, Tag 0DGC](https://stacks.math.columbia.edu/tag/0DGC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) (X : T.Spaces)

attribute [local instance] HasDerivedCategory.standard

/-- The direct image `π_{X,*}` preserves limits. -/
local instance bigToSmall_pushforward_preservesLimits :
    PreservesLimitsOfSize.{0, 0} (bigToSmallEtaleMorphism T X).pushforward :=
  (bigToSmallEtaleMorphism T X).adj.rightAdjoint_preservesLimits

/-- The direct image `π_{X,*}` preserves finite limits. -/
local instance bigToSmall_pushforward_preservesFiniteLimits :
    PreservesFiniteLimits (bigToSmallEtaleMorphism T X).pushforward := inferInstance

-- `bigToSmallAbelianInverseImage_additive` is declared in
-- `StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigSmallEtaleCohomology.lean` as a
-- `local instance`, which exports the declaration but not the attribute, so the attribute is
-- re-enabled here rather than the declaration restated.
attribute [local instance] bigToSmallAbelianInverseImage_additive

/-! ### The composite of inverse image and direct image -/

/-- **Stacks 0DGC.** Restricting back to the spaces-étale site of `X` the inverse image of a
sheaf of sets along `π_X` returns that sheaf: `π_{X,*} ∘ π_X⁻¹` is the identity functor. -/
@[stacks 0DGC "the composite is the identity, for sheaves of sets"]
noncomputable def bigToSmall_inverseImage_comp_pushforwardIso :
    (bigToSmallEtaleMorphism T X).inverseImage ⋙ (bigToSmallEtaleMorphism T X).pushforward ≅
      𝟭 (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :=
  Functor.isoWhiskerLeft _ (smallToBig_inverseImageIso_bigToSmall_pushforward T X).symm ≪≫
    bigToSmall_inverseImageFactorizationIso T (𝟙 X) ≪≫
    smallEtaleMorphismIdInverseImageIso T X

/-- Restriction of abelian sheaves to the spaces-étale site of `X` is the abelian direct image
along `π_X`. -/
noncomputable def bigToSmallEtaleRestrictionIso :
    ProEtale.mapAbelianSheaf (bigToSmallEtaleMorphism T X).pushforward ≅
      bigToSmallEtaleRestriction T X := by
  refine (?_ : ProEtale.mapAbelianSheaf
    ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
      (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology X)) ≅ bigToSmallEtaleRestriction T X)
  exact ProEtale.mapAbelianSheafRestrictionIso.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X)

/-- **Stacks 0DGC.** The same composite identity for abelian sheaves: restricting the abelian
inverse image along `π_X` back to the spaces-étale site of `X` returns the sheaf. -/
@[stacks 0DGC "the composite is the identity, for abelian sheaves"]
noncomputable def bigToSmall_abelianInverseImage_comp_restrictionIso :
    CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X) ⋙
        bigToSmallEtaleRestriction T X ≅
      𝟭 (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  refine ProEtale.liftSheafNatIso
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) _ _ ?_
  exact Functor.isoWhiskerLeft
    (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (forget Ab.{u + 1}))
    (bigToSmall_inverseImage_comp_pushforwardIso T X)

/-! ### The adjunction and its derived unit -/

/-- The adjunction `π_X⁻¹ ⊣ π_{X,*}` on abelian sheaves. -/
noncomputable def bigToSmallEtaleAbelianAdjunction :
    CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X) ⊣
      bigToSmallEtaleRestriction T X :=
  letI := (bigToSmallEtaleMorphism T X).preservesFiniteLimits
  (ProEtale.mapAbelianSheafAdjunction (bigToSmallEtaleMorphism T X).adj).ofNatIsoRight
    (bigToSmallEtaleRestrictionIso T X)

/-- The adjunction `π_X⁻¹ ⊣ Rπ_{X,*}` on the unbounded derived categories of abelian sheaves.
Both functors are exact, so both are induced degreewise and `Rπ_{X,*} = π_{X,*}`. -/
noncomputable def bigToSmallEtaleDerivedAdjunction :
    (CategoryTheory.Sites.abelianInverseImage
        (bigToSmallEtaleMorphism T X)).mapDerivedCategory ⊣
      (bigToSmallEtaleRestriction T X).mapDerivedCategory :=
  Adjunction.mapDerivedCategory (bigToSmallEtaleAbelianAdjunction T X)

/-- **Stacks 0DGC.** For every complex `K` on the spaces-étale site of `X` the canonical map
`K ⟶ Rπ_{X,*}π_X⁻¹K` is an isomorphism. -/
@[stacks 0DGC "the derived unit is an isomorphism"]
theorem isIso_bigToSmallEtaleDerivedAdjunction_unit
    (K : DerivedCategory
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})) :
    IsIso ((bigToSmallEtaleDerivedAdjunction T X).unit.app K) := by
  have hθ := ProEtale.derivedCompIso (bigToSmall_abelianInverseImage_comp_restrictionIso T X)
  have h : IsIso (bigToSmallEtaleDerivedAdjunction T X).unit :=
    Stacks.Adjunction.isIso_unit_of_comp_iso_id (bigToSmallEtaleDerivedAdjunction T X)
      (hθ ≪≫ ProEtale.derivedIdIso)
  let _ := h
  infer_instance

end AlgebraicGeometry.BigEtaleSpaceSite

end
