module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounitFromAffine
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesSheaf

/-!
# Quasi-coherent modules on the small affine étale site: existence

Let `S` be a scheme. Restriction along the inclusion of the affine objects identifies sheaves of
modules on the ringed site `(S_étale, 𝒪)` with sheaves of modules on the ringed site
`(S_{affine, étale}, 𝒪_affine)` (the Comparison Lemma for sheaves of modules). This file shows
that a sheaf of modules `𝓕` on `S_{affine, étale}` which is quasi-coherent on that ringed site is
the restriction of a quasi-coherent `𝒪`-module on `S_étale`, and is isomorphic to
`𝒢ᵃ|_{S_{affine, étale}}` for a quasi-coherent `𝒪_S`-module `𝒢`. These are conditions (3) and (4)
of [Stacks, Tag 0GZX] at `τ = étale`, and they give equivalences of categories
`QCoh(S_étale, 𝒪) ≌ QCoh(S_{affine, étale}, 𝒪_affine)` and
`QCoh(𝒪_S) ≌ QCoh(S_{affine, étale}, 𝒪_affine)`.

## Main definitions

* `CategoryTheory.ObjectProperty.fullyFaithfulLift`: the corestriction of a fully faithful functor
  to a full subcategory containing its image is fully faithful.
* `AlgebraicGeometry.smallAffineEtaleModuleRestrictionEquivalence`: the equivalence
  `Mod(S_étale, 𝒪) ≌ Mod(S_{affine, étale}, 𝒪_affine)` given by restriction.
* `AlgebraicGeometry.smallAffineEtaleModuleRestrictionQcoh`: restriction of quasi-coherent modules,
  `QCoh(S_étale, 𝒪) ⥤ QCoh(S_{affine, étale}, 𝒪_affine)`.
* `AlgebraicGeometry.smallAffineEtaleAssociatedModuleQcohOnSite`: the functor
  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}`, `QCoh(𝒪_S) ⥤ QCoh(S_{affine, étale}, 𝒪_affine)`.
* `AlgebraicGeometry.smallAffineEtaleAssociatedModuleQcohEquivalence`: the equivalence
  `QCoh(𝒪_S) ≌ QCoh(S_{affine, étale}, 𝒪_affine)` with functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}`.

## Main results

* `AlgebraicGeometry.smallAffineEtale_essImage_associatedModuleQcoh` and
  `AlgebraicGeometry.smallAffineEtale_exists_associatedModuleQcoh_restriction_iso`: a sheaf of
  modules on `S_{affine, étale}` that is quasi-coherent on the ringed site, respectively whose
  base-change maps are isomorphisms, is isomorphic to `𝒢ᵃ|_{S_{affine, étale}}` for a
  quasi-coherent `𝒪_S`-module `𝒢`.
* `AlgebraicGeometry.smallAffineEtale_exists_isQuasicoherentOnSite_restriction_iso`: a
  quasi-coherent module on `S_{affine, étale}` is the restriction of a quasi-coherent module on
  `S_étale`.
* `AlgebraicGeometry.isEquivalence_smallAffineEtaleModuleRestrictionQcoh`: restriction is an
  equivalence `QCoh(S_étale, 𝒪) ≌ QCoh(S_{affine, étale}, 𝒪_affine)`.
* `AlgebraicGeometry.isEquivalence_smallAffineEtaleAssociatedModuleQcohOnSite`: the functor
  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` is an equivalence `QCoh(𝒪_S) ≌ QCoh(S_{affine, étale}, 𝒪_affine)`.

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GZW](https://stacks.math.columbia.edu/tag/0GZW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DR](https://stacks.math.columbia.edu/tag/03DR)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u u₁ v₁ u₂ v₂

namespace CategoryTheory.ObjectProperty

/-- The corestriction `P.lift F hF` of a fully faithful functor `F` to a full subcategory `P`
containing its image is fully faithful. -/
public noncomputable def fullyFaithfulLift {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (P : ObjectProperty D) {F : C ⥤ D} (hF : ∀ X, P (F.obj X))
    (hff : F.FullyFaithful) : (P.lift F hF).FullyFaithful :=
  have := hff.full
  have := hff.faithful
  have : (P.lift F hF).Full := inferInstance
  have : (P.lift F hF).Faithful := inferInstance
  .ofFullyFaithful _

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Limits of the shape indexed by the affine objects over an object of the small étale site
exist in `AddCommGrpCat`, the small affine étale site being essentially small. -/
public instance SmallAffineEtale.hasLimitsOfShape_structuredArrow_addCommGrpCat
    (X : (SmallEtale B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (SmallAffineEtale.inclusion B S hS).op)
      AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The Comparison Lemma for sheaves of modules on the small affine étale site: restriction of
sheaves of modules along the inclusion of the affine objects, over the restricted structure sheaf,
is an equivalence `Mod(S_étale, 𝒪) ≌ Mod(S_{affine, étale}, 𝒪_affine)`. -/
public noncomputable def smallAffineEtaleModuleRestrictionEquivalence :
    SheafOfModules.{u} (SmallEtale.structureSheaf B S hS) ≌
      SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
        (SmallAffineEtale.topology B S hS) (SmallEtale.topology B S hS)
        (SmallAffineEtale.inclusion B S hS) (SmallEtale.structureSheaf B S hS)) :=
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence.{u}
    (SmallAffineEtale.topology B S hS) (SmallEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (SmallEtale.structureSheaf B S hS)

/-- The functor of `AlgebraicGeometry.smallAffineEtaleModuleRestrictionEquivalence` is
restriction of modules to the affine objects. -/
public theorem smallAffineEtaleModuleRestrictionEquivalence_functor :
    (smallAffineEtaleModuleRestrictionEquivalence B S hS).functor =
      smallAffineEtaleModuleRestriction B S hS :=
  rfl

/-! ### The existence of `𝒢`, and condition (3) -/

/-- If `F` is quasi-coherent on the ringed site `(S_{affine, étale}, 𝒪_affine)`, so is the
restriction of a preimage of `F` under the restriction functor. -/
private theorem isQuasicoherentOnSite_restriction_objPreimage
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O))
    (hF : F.IsQuasicoherentOnSite) :
    ((smallAffineEtaleModuleRestriction B S hS).obj
      ((smallAffineEtaleModuleRestriction B S hS).objPreimage F)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((smallAffineEtaleModuleRestriction B S hS).objObjPreimageIso F).symm hF

/-- A sheaf of modules on the small affine étale site of `S` which is quasi-coherent on the ringed
site `(S_{affine, étale}, 𝒪_affine)` is the restriction of a quasi-coherent `𝒪`-module on
`(S_étale, 𝒪)`. -/
@[stacks 0GZX "(2) ⇒ (3) at τ = étale"]
public theorem smallAffineEtale_exists_isQuasicoherentOnSite_restriction_iso
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O))
    (hF : F.IsQuasicoherentOnSite) :
    ∃ N : SheafOfModules.{u} (SmallEtale.structureSheaf B S hS), N.IsQuasicoherentOnSite ∧
      Nonempty ((smallAffineEtaleModuleRestriction B S hS).obj N ≅ F) := by
  refine ⟨(smallAffineEtaleModuleRestriction B S hS).objPreimage F, ?_,
    ⟨(smallAffineEtaleModuleRestriction B S hS).objObjPreimageIso F⟩⟩
  obtain ⟨G, ⟨e⟩⟩ := SmallEtale.essImage_associatedModuleQcoh_of_affineRestriction B S hS _
    (isQuasicoherentOnSite_restriction_objPreimage B S hS F hF)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso e
    (SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS G.obj G.property)

/-- A sheaf of modules `𝓕` on the small affine étale site of `S` which is quasi-coherent on the
ringed site `(S_{affine, étale}, 𝒪_affine)` lies in the essential image of the functor
`𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` on quasi-coherent `𝒪_S`-modules. -/
@[stacks 0GZX "(4) at τ = étale, existence of 𝒢"]
public theorem smallAffineEtale_essImage_associatedModuleQcoh
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O))
    (hF : F.IsQuasicoherentOnSite) :
    (smallAffineEtaleAssociatedModuleQcoh B S hS).essImage F := by
  have e : (smallAffineEtaleModuleRestriction B S hS).obj
      ((smallAffineEtaleModuleRestriction B S hS).objPreimage F) ≅ F :=
    (smallAffineEtaleModuleRestriction B S hS).objObjPreimageIso F
  have hN := isQuasicoherentOnSite_restriction_objPreimage B S hS F hF
  refine ⟨⟨(SmallEtale.restrictModule B S hS).obj
      ((smallAffineEtaleModuleRestriction B S hS).objPreimage F),
    SmallEtale.isQuasicoherent_restrictModule_of_affineRestriction B S hS _ hN⟩, ⟨?_⟩⟩
  exact (smallAffineEtaleModuleRestriction B S hS).mapIso
    (@asIso _ _ _ _ _ (SmallEtale.isIso_counit_of_affineRestriction B S hS _ hN)) ≪≫ e

/-- A sheaf of modules on the small affine étale site of `S` all of whose base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms is isomorphic to `𝒢ᵃ|_{S_{affine, étale}}` for a
quasi-coherent `𝒪_S`-module `𝒢`. -/
@[stacks 0GZX "(1) ⇒ (4) at τ = étale, existence of 𝒢"]
public theorem smallAffineEtale_exists_associatedModuleQcoh_restriction_iso
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineEtaleRingedSite B S hS).O))
    (hF : ∀ ⦃U V : SmallAffineEtale B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineEtaleRingedSite B S hS) F f)) :
    ∃ G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
      Nonempty ((smallAffineEtaleAssociatedModuleQcoh B S hS).obj G ≅ F) :=
  smallAffineEtale_essImage_associatedModuleQcoh B S hS F
    (smallAffineEtale_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS F hF)

/-! ### Conditions (2) and (3) are equivalent, as an equivalence of categories -/

/-- Restriction of quasi-coherent modules to the affine objects, as a functor
`QCoh(S_étale, 𝒪) ⥤ QCoh(S_{affine, étale}, 𝒪_affine)`: the corestriction of
`AlgebraicGeometry.smallAffineEtaleModuleRestriction` to the quasi-coherent modules. -/
public noncomputable abbrev smallAffineEtaleModuleRestrictionQcoh :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf B S hS)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineEtaleRingedSite B S hS).O)).FullSubcategory :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (SmallEtale.structureSheaf B S hS)).ι ⋙ smallAffineEtaleModuleRestriction B S hS)
    fun M => smallAffineEtale_isQuasicoherentOnSite_restriction B S hS M.obj M.property

/-- The restriction functor on quasi-coherent modules is fully faithful. -/
public noncomputable def fullyFaithfulSmallAffineEtaleModuleRestrictionQcoh :
    (smallAffineEtaleModuleRestrictionQcoh B S hS).FullyFaithful :=
  ObjectProperty.fullyFaithfulLift _ _
    ((ObjectProperty.fullyFaithfulι _).comp
      (fullyFaithfulSmallAffineEtaleModuleRestriction B S hS))

/-- The restriction functor on quasi-coherent modules is essentially surjective. -/
public theorem essSurj_smallAffineEtaleModuleRestrictionQcoh :
    (smallAffineEtaleModuleRestrictionQcoh B S hS).EssSurj where
  mem_essImage F := by
    obtain ⟨N, hN, ⟨e⟩⟩ :=
      smallAffineEtale_exists_isQuasicoherentOnSite_restriction_iso B S hS F.obj F.property
    exact ⟨⟨N, hN⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Restriction to the affine objects is an equivalence
`QCoh(S_étale, 𝒪) ≌ QCoh(S_{affine, étale}, 𝒪_affine)` between the categories of quasi-coherent
modules. -/
@[stacks 0GZX "(2) ⇔ (3) at τ = étale"]
public theorem isEquivalence_smallAffineEtaleModuleRestrictionQcoh :
    (smallAffineEtaleModuleRestrictionQcoh B S hS).IsEquivalence :=
  have hff := fullyFaithfulSmallAffineEtaleModuleRestrictionQcoh B S hS
  have := hff.full
  have := hff.faithful
  have := essSurj_smallAffineEtaleModuleRestrictionQcoh B S hS
  {}

/-! ### Conditions (2) and (4) are equivalent, as an equivalence of categories -/

/-- The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` from quasi-coherent `𝒪_S`-modules to
quasi-coherent modules on the ringed site `(S_{affine, étale}, 𝒪_affine)`, as a functor
`QCoh(𝒪_S) ⥤ QCoh(S_{affine, étale}, 𝒪_affine)`. -/
public noncomputable abbrev smallAffineEtaleAssociatedModuleQcohOnSite :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineEtaleRingedSite B S hS).O)).FullSubcategory :=
  ObjectProperty.lift _ (smallAffineEtaleAssociatedModuleQcoh B S hS) fun M =>
    smallAffineEtale_isQuasicoherentOnSite_restriction B S hS _
      (SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS M.obj
        M.property)

/-- The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` into quasi-coherent modules on the ringed site is
fully faithful. -/
public noncomputable def fullyFaithfulSmallAffineEtaleAssociatedModuleQcohOnSite :
    (smallAffineEtaleAssociatedModuleQcohOnSite B S hS).FullyFaithful :=
  ObjectProperty.fullyFaithfulLift _ _
    (fullyFaithfulSmallAffineEtaleAssociatedModuleQcoh B S hS)

/-- The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` into quasi-coherent modules on the ringed site is
essentially surjective. -/
public theorem essSurj_smallAffineEtaleAssociatedModuleQcohOnSite :
    (smallAffineEtaleAssociatedModuleQcohOnSite B S hS).EssSurj where
  mem_essImage F := by
    obtain ⟨G, ⟨e⟩⟩ :=
      smallAffineEtale_essImage_associatedModuleQcoh B S hS F.obj F.property
    exact ⟨G, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}` is an equivalence from the quasi-coherent
`𝒪_S`-modules onto the quasi-coherent modules on the ringed site `(S_{affine, étale}, 𝒪_affine)`:
every such module comes from a `𝒢`, and from a unique one. -/
@[stacks 0GZX "(2) ⇔ (4) at τ = étale"]
public theorem isEquivalence_smallAffineEtaleAssociatedModuleQcohOnSite :
    (smallAffineEtaleAssociatedModuleQcohOnSite B S hS).IsEquivalence :=
  have hff := fullyFaithfulSmallAffineEtaleAssociatedModuleQcohOnSite B S hS
  have := hff.full
  have := hff.faithful
  have := essSurj_smallAffineEtaleAssociatedModuleQcohOnSite B S hS
  {}

/-- The equivalence of categories `QCoh(𝒪_S) ≌ QCoh(S_{affine, étale}, 𝒪_affine)` with functor
`𝒢 ↦ 𝒢ᵃ|_{S_{affine, étale}}`. -/
@[stacks 0GZX "(2) ⇔ (4) at τ = étale"]
public noncomputable def smallAffineEtaleAssociatedModuleQcohEquivalence :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineEtaleRingedSite B S hS).O)).FullSubcategory :=
  have := isEquivalence_smallAffineEtaleAssociatedModuleQcohOnSite B S hS
  (smallAffineEtaleAssociatedModuleQcohOnSite B S hS).asEquivalence

end AlgebraicGeometry

end
