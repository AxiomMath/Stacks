module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineSiteAssociatedModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesExists
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiUnique
public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineZariskiCartesian
public import StacksFrontier.AlgebraicGeometry.Modules.CartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Quasi-coherent modules on the small affine Zariski site: existence

Let `S` be a scheme, `S_Zar` its small Zariski site with structure sheaf `𝒪`, and
`(S_{affine, Zar}, 𝒪_affine)` the ringed site of its affine objects. Every quasi-coherent module
`𝓕` on `(S_{affine, Zar}, 𝒪_affine)` is isomorphic to `𝒢ᵃ|_{S_{affine, Zar}}` for a
quasi-coherent `𝒪_S`-module `𝒢`, and is the restriction of a quasi-coherent module on
`(S_Zar, 𝒪)`. Hence both restriction along the equivalence of ringed topoi (0GZW) and the functor
`𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` are equivalences of categories of quasi-coherent modules.

## The argument

* The equivalence of ringed topoi (0GZW) is upgraded to sheaves of modules by
  `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`, which needs limits in
  `AddCommGrpCat` of the shape indexed by the affine objects over an object of `S_Zar`; these
  exist because the small affine Zariski site is essentially small. So `𝓕` is the restriction of
  a sheaf of `𝒪`-modules `𝒩` on `S_Zar`.
* `𝒢` is the restriction of `𝒩` along the morphism of ringed sites of Remark 03FH. It is
  quasi-coherent in the sense of Stacks 01BD, because its base-change comparison between nested
  affine opens of `S` is the comparison of `𝒩` between the corresponding affine objects of
  `S_Zar`.
* `𝒢ᵃ ≅ 𝒩` is the counit of the associated-module adjunction, an isomorphism because
  `AlgebraicGeometry.SmallZariski.restrictModule` is an equivalence.

The structure-sheaf comparison `AlgebraicGeometry.smallZariskiCommStructureIso` is the counit of
the equivalence of sites of Stacks 020X, acting on sections as a restriction map of `𝒪_S`,
followed by `AlgebraicGeometry.smallZariskiCommStructurePresheafIso`, whose components are
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`; forgetting commutativity, it is
`AlgebraicGeometry.SmallZariski.structureMap`. The object of the small Zariski site chosen over an
open `V` of `S` has open image `V`, so the object chosen over an affine open is affine.

## Main definitions

* `AlgebraicGeometry.smallZariskiCommStructurePresheafIso` and
  `AlgebraicGeometry.smallZariskiCommStructureIso`: the structure-sheaf comparison of the small
  Zariski site in `CommRingCat`-valued form.
* `AlgebraicGeometry.smallAffineZariskiModuleRestrictionQcoh`: restriction of *quasi-coherent*
  modules along the equivalence (0GZW), `QCoh(S_Zar, 𝒪) ⥤ QCoh(S_{affine, Zar}, 𝒪_affine)`.
* `AlgebraicGeometry.smallAffineZariskiAssociatedModuleQcohOnSite`: the functor
  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}`, corestricted to the quasi-coherent modules on
  `(S_{affine, Zar}, 𝒪_affine)`.

## Main results

* `AlgebraicGeometry.smallAffineZariski_essImage_associatedModuleQcoh` and
  `AlgebraicGeometry.smallAffineZariski_exists_associatedModuleQcoh_restriction_iso`: a
  quasi-coherent module on `(S_{affine, Zar}, 𝒪_affine)`, respectively a module all of whose
  base-change maps are isomorphisms, is `𝒢ᵃ|_{S_{affine, Zar}}` for a quasi-coherent
  `𝒪_S`-module `𝒢`.
* `AlgebraicGeometry.smallAffineZariski_exists_isQuasicoherentOnSite_restriction_iso` and
  `AlgebraicGeometry.isEquivalence_smallAffineZariskiModuleRestrictionQcoh`: a quasi-coherent
  module on `(S_{affine, Zar}, 𝒪_affine)` is the restriction of a quasi-coherent module on
  `(S_Zar, 𝒪)`, and restriction is an equivalence
  `QCoh(S_Zar, 𝒪) ≌ QCoh(S_{affine, Zar}, 𝒪_affine)`.
* `AlgebraicGeometry.isEquivalence_smallAffineZariskiAssociatedModuleQcohOnSite` and
  `AlgebraicGeometry.smallAffineZariskiAssociatedModuleQcohEquivalence`: the functor
  `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` is an equivalence
  `QCoh(𝒪_S) ≌ QCoh(S_{affine, Zar}, 𝒪_affine)`.

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GZW](https://stacks.math.columbia.edu/tag/0GZW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure-sheaf comparison in `CommRingCat`-valued form -/

/-- The presheaf of commutative rings of global functions on the objects of the small Zariski
site of `S`. -/
public noncomputable abbrev smallZariskiCommRings :=
  Stacks.Sites.commStructurePresheaf S
    (SmallZariski.inclusion B S hS ⋙ Over.post B.inclusion)

/-- **Over an object of the small Zariski site of `S`, the sections of `𝒪_S` on its open image
are its own global functions**, in `CommRingCat`. The components are
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`. -/
public noncomputable def smallZariskiCommStructurePresheafIso :
    (smallZariskiToOpens B S hS).op ⋙ S.presheaf ≅ smallZariskiCommRings B S hS :=
  NatIso.ofComponents
    (fun X => (IsOpenImmersion.ΓIsoTop (smallZariskiOpenImmersion B S hS X.unop)).symm)
    (fun {X Y} f =>
      openImmersion_ΓIsoTop_naturality
        ((SmallZariski.toScheme B S hS).map f.unop)
        (smallZariskiOpenImmersion B S hS Y.unop)
        (smallZariskiOpenImmersion B S hS X.unop)
        (smallZariskiOpenImmersion_comp B S hS f.unop)
        ((smallZariskiToOpens B S hS).map f.unop).le)

/-- **The comparison of structure sheaves of the small Zariski site of `S`, in `CommRingCat`.**
It is the counit of the equivalence of sites of Stacks 020X, acting on sections as a restriction
map of `𝒪_S`, followed by
`AlgebraicGeometry.smallZariskiCommStructurePresheafIso`.  Forgetting commutativity gives
`AlgebraicGeometry.SmallZariski.structureMap`, by
`AlgebraicGeometry.whiskerRight_smallZariskiCommStructureIso_hom`. -/
public noncomputable def smallZariskiCommStructureIso :
    S.presheaf ≅ (SmallZariski.opensToSmallZariski B S hS).op ⋙ smallZariskiCommRings B S hS :=
  (Functor.isoWhiskerRight (smallZariskiSiteEquiv B S hS).op.counitIso S.presheaf).symm ≪≫
    Functor.isoWhiskerLeft (SmallZariski.opensToSmallZariski B S hS).op
      (smallZariskiCommStructurePresheafIso B S hS)

/-- **`AlgebraicGeometry.smallZariskiCommStructureIso` is a lifting of
`AlgebraicGeometry.SmallZariski.structureMap`**: forgetting commutativity returns that map on the
nose. -/
public theorem whiskerRight_smallZariskiCommStructureIso_hom :
    Functor.whiskerRight (smallZariskiCommStructureIso B S hS).hom
        (forget₂ CommRingCat RingCat.{u}) =
      (SmallZariski.structureMap B S hS).hom :=
  rfl

/-! ### The chosen object over an open -/

/-- **The open image of the object of the small Zariski site chosen over an open `V` of `S` is
`V`.** -/
public theorem smallZariskiToOpens_opensToSmallZariski_obj (V : S.Opens) :
    (smallZariskiToOpens B S hS).obj ((SmallZariski.opensToSmallZariski B S hS).obj V) = V :=
  le_antisymm ((smallZariskiSiteEquiv B S hS).counit.app V).le
    ((smallZariskiSiteEquiv B S hS).counitIso.inv.app V).le

/-- **The object of the small Zariski site chosen over an affine open is affine.** -/
public theorem isAffine_opensToSmallZariski_obj (V : S.Opens) (hV : IsAffineOpen V) :
    IsAffine ((SmallZariski.toScheme B S hS).obj
      ((SmallZariski.opensToSmallZariski B S hS).obj V)) := by
  have hr : (smallZariskiOpenImmersion B S hS
      ((SmallZariski.opensToSmallZariski B S hS).obj V)).opensRange = V :=
    smallZariskiToOpens_opensToSmallZariski_obj B S hS V
  have : IsAffine (V : Scheme.{u}) := hV
  exact IsAffine.of_isIso
    (IsOpenImmersion.isoOfRangeEq
      (smallZariskiOpenImmersion B S hS ((SmallZariski.opensToSmallZariski B S hS).obj V)) V.ι
      (by rw [← Scheme.Hom.coe_opensRange, hr]; exact (Scheme.Opens.range_ι V).symm)).hom

/-! ### Cartesian sections descend to the opens of `S` -/

/-- **Cartesian sections descend from the small Zariski site to the opens of `S`.**  If the
sections of a sheaf of modules on `S_Zar` are the base change of one another along the morphism of
the site chosen over an inclusion `V' ≤ V` of opens of `S`, then the same holds for its
restriction along the morphism of ringed sites of Remark 03FH. -/
public theorem smallZariski_bijective_restrictionBaseChange_restrictModule
    (G : SheafOfModules.{u} (SmallZariski.structureSheaf B S hS))
    {V V' : S.Opens} (hle : V' ≤ V)
    (h : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := smallZariskiCommRings B S hS) G.val
      ((SmallZariski.opensToSmallZariski B S hS).map (homOfLE hle)).op)) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := S.presheaf) ((SmallZariski.restrictModule B S hS).obj G).val (homOfLE hle).op) :=
  Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars
    (smallZariskiCommStructureIso B S hS).hom
    (fun U => NatIso.isIso_app_of_isIso _ U)
    ((PresheafOfModules.pushforward₀ (SmallZariski.opensToSmallZariski B S hS)
      (smallZariskiCommRings B S hS ⋙ forget₂ CommRingCat RingCat)).obj G.val)
    (homOfLE hle).op h

/-- **A sheaf of modules on the small Zariski site of `S` whose restriction to the affine objects
is quasi-coherent is cartesian between affine objects.** -/
public theorem smallZariski_bijective_restrictionBaseChange_of_affineRestriction
    (G : SheafOfModules.{u} (SmallZariski.structureSheaf B S hS))
    (hG : ((smallAffineZariskiModuleRestriction B S hS).obj G).IsQuasicoherentOnSite)
    {T T' : SmallZariski B S hS}
    (hT : IsAffine ((SmallZariski.toScheme B S hS).obj T))
    (hT' : IsAffine ((SmallZariski.toScheme B S hS).obj T'))
    (f : T ⟶ T') :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := smallZariskiCommRings B S hS) G.val f.op) := by
  have h₂ := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hG
  have h₃ := SmallAffineZariski.isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u}
    B S hS _ h₂
    ((SmallAffineZariski.inclusion B S hS).preimage
      (X := (⟨T, hT⟩ : SmallAffineZariski B S hS)) (Y := ⟨T', hT'⟩) f)
  have h₄ := Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_uliftForPresentation
    (SmallAffineZariski.affineChartRings B S hS) _ _ _ h₃
  have h₅ := Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_restriction
    (J := SmallZariski.topology B S hS) (K := SmallAffineZariski.topology B S hS)
    (SmallAffineZariski.inclusion B S hS) (smallZariskiCommRings B S hS) _ G _ h₄
  rwa [(SmallAffineZariski.inclusion B S hS).map_preimage] at h₅

/-- **The restriction to the opens of `S` of a sheaf of modules on `S_Zar` whose restriction to
the affine objects is quasi-coherent is a quasi-coherent `𝒪_S`-module** in the sense of
Stacks 01BD. -/
public theorem smallZariski_isQuasicoherent_restrictModule_of_affineRestriction
    (G : SheafOfModules.{u} (SmallZariski.structureSheaf B S hS))
    (hG : ((smallAffineZariskiModuleRestriction B S hS).obj G).IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((SmallZariski.restrictModule B S hS).obj G) := by
  refine Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction
    _ fun V V' hV hV' hle =>
      smallZariski_bijective_restrictionBaseChange_restrictModule B S hS G hle ?_
  exact smallZariski_bijective_restrictionBaseChange_of_affineRestriction B S hS G hG
    (isAffine_opensToSmallZariski_obj B S hS V' hV')
    (isAffine_opensToSmallZariski_obj B S hS V hV)
    ((SmallZariski.opensToSmallZariski B S hS).map (homOfLE hle))

/-! ### The existence of `𝒢` -/

/-- Limits of the shape indexed by the affine objects over an object of the small Zariski site
exist in `AddCommGrpCat`, the small affine Zariski site being essentially small. -/
public instance SmallAffineZariski.hasLimitsOfShape_structuredArrow_addCommGrpCat
    (X : (SmallZariski B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (SmallAffineZariski.inclusion B S hS).op)
      AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The counit of the associated-module adjunction of the small Zariski site is an isomorphism at
every sheaf of modules. -/
public theorem isIso_counit_smallZariskiAssociatedModuleAdjunction
    (G : SheafOfModules.{u} (SmallZariski.structureSheaf B S hS)) :
    IsIso ((SmallZariski.associatedModuleAdjunction B S hS).counit.app G) :=
  NatIso.isIso_app_of_isIso _ G

/-- A sheaf of modules on the small affine Zariski site of `S` which is quasi-coherent on the
ringed site `(S_{affine, Zar}, 𝒪_affine)` is the restriction of a quasi-coherent `𝒪`-module on
`(S_Zar, 𝒪)`, i.e. corresponds to one under the equivalence of ringed topoi (0GZW). -/
@[stacks 0GZX "(2) ⇒ (3) at τ = Zariski"]
public theorem smallAffineZariski_exists_isQuasicoherentOnSite_restriction_iso
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O))
    (hF : F.IsQuasicoherentOnSite) :
    ∃ N : SheafOfModules.{u} (SmallZariski.structureSheaf B S hS), N.IsQuasicoherentOnSite ∧
      Nonempty ((smallAffineZariskiModuleRestriction B S hS).obj N ≅ F) := by
  refine ⟨(smallAffineZariskiModuleRestriction B S hS).objPreimage F, ?_,
    ⟨(smallAffineZariskiModuleRestriction B S hS).objObjPreimageIso F⟩⟩
  have hN : ((smallAffineZariskiModuleRestriction B S hS).obj
      ((smallAffineZariskiModuleRestriction B S hS).objPreimage F)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((smallAffineZariskiModuleRestriction B S hS).objObjPreimageIso F).symm hF
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    (@asIso _ _ _ _ _ (isIso_counit_smallZariskiAssociatedModuleAdjunction B S hS _)) ?_
  exact SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _
    (smallZariski_isQuasicoherent_restrictModule_of_affineRestriction B S hS _ hN)

/-- A sheaf of modules `𝓕` on the small affine Zariski site of `S` which is quasi-coherent on the
ringed site `(S_{affine, Zar}, 𝒪_affine)` comes from a quasi-coherent `𝒪_S`-module `𝒢` by the
procedure of Descent, Section 35.8: it is in the essential image of
`𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}`. -/
@[stacks 0GZX "(4) at τ = Zariski, existence of 𝒢"]
public theorem smallAffineZariski_essImage_associatedModuleQcoh
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O))
    (hF : F.IsQuasicoherentOnSite) :
    (smallAffineZariskiAssociatedModuleQcoh B S hS).essImage F := by
  obtain ⟨N, -, ⟨e⟩⟩ :=
    smallAffineZariski_exists_isQuasicoherentOnSite_restriction_iso B S hS F hF
  refine ⟨⟨(SmallZariski.restrictModule B S hS).obj N,
    smallZariski_isQuasicoherent_restrictModule_of_affineRestriction B S hS _
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hF)⟩, ⟨?_⟩⟩
  exact (smallAffineZariskiModuleRestriction B S hS).mapIso
    (@asIso _ _ _ _ _
      (isIso_counit_smallZariskiAssociatedModuleAdjunction B S hS _)) ≪≫ e

/-- A sheaf of modules `𝓕` on the small affine Zariski site of `S` all of whose base-change maps
`𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` are isomorphisms is isomorphic to `𝒢ᵃ|_{S_{affine, Zar}}` for a
quasi-coherent `𝒪_S`-module `𝒢`. -/
@[stacks 0GZX "(1) ⇒ (4) at τ = Zariski, existence of 𝒢"]
public theorem smallAffineZariski_exists_associatedModuleQcoh_restriction_iso
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O))
    (hF : ∀ ⦃U V : SmallAffineZariski B S hS⦄ (f : U ⟶ V),
      IsIso (Stacks.SheafOfModules.canonicalMap (smallAffineZariskiRingedSite B S hS) F f)) :
    ∃ G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
      Nonempty ((smallAffineZariskiAssociatedModuleQcoh B S hS).obj G ≅ F) :=
  smallAffineZariski_essImage_associatedModuleQcoh B S hS F
    (smallAffineZariski_isQuasicoherentOnSite_of_canonicalMap_isIso B S hS F hF)

/-! ### Restriction of quasi-coherent modules is an equivalence -/

/-- **Restriction of quasi-coherent modules along the equivalence of ringed topoi (0GZW)**: the
functor `QCoh(S_Zar, 𝒪) ⥤ QCoh(S_{affine, Zar}, 𝒪_affine)`. -/
public noncomputable abbrev smallAffineZariskiModuleRestrictionQcoh :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallZariski.structureSheaf B S hS)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineZariskiRingedSite B S hS).O)).FullSubcategory :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (SmallZariski.structureSheaf B S hS)).ι ⋙ smallAffineZariskiModuleRestriction B S hS)
    fun M => smallAffineZariski_isQuasicoherentOnSite_restriction B S hS M.obj M.property

/-- The restriction functor on quasi-coherent modules is fully faithful. -/
public noncomputable def fullyFaithfulSmallAffineZariskiModuleRestrictionQcoh :
    (smallAffineZariskiModuleRestrictionQcoh B S hS).FullyFaithful :=
  ObjectProperty.fullyFaithfulLift _ _
    ((ObjectProperty.fullyFaithfulι _).comp
      (fullyFaithfulSmallAffineZariskiModuleRestriction B S hS))

/-- The restriction functor on quasi-coherent modules is essentially surjective. -/
public theorem essSurj_smallAffineZariskiModuleRestrictionQcoh :
    (smallAffineZariskiModuleRestrictionQcoh B S hS).EssSurj where
  mem_essImage F := by
    obtain ⟨N, hN, ⟨e⟩⟩ :=
      smallAffineZariski_exists_isQuasicoherentOnSite_restriction_iso B S hS F.obj F.property
    exact ⟨⟨N, hN⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- The equivalence of ringed topoi (0GZW) induces an equivalence
`QCoh(S_Zar, 𝒪) ≌ QCoh(S_{affine, Zar}, 𝒪_affine)` between the categories of quasi-coherent
modules. -/
@[stacks 0GZX "(2) ⇔ (3) at τ = Zariski"]
public theorem isEquivalence_smallAffineZariskiModuleRestrictionQcoh :
    (smallAffineZariskiModuleRestrictionQcoh B S hS).IsEquivalence :=
  have hff := fullyFaithfulSmallAffineZariskiModuleRestrictionQcoh B S hS
  have := hff.full
  have := hff.faithful
  have := essSurj_smallAffineZariskiModuleRestrictionQcoh B S hS
  {}

/-! ### `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` is an equivalence -/

/-- **The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}`, corestricted to the quasi-coherent modules on
the ringed site `(S_{affine, Zar}, 𝒪_affine)`**, as a functor
`QCoh(𝒪_S) ⥤ QCoh(S_{affine, Zar}, 𝒪_affine)`. -/
public noncomputable abbrev smallAffineZariskiAssociatedModuleQcohOnSite :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineZariskiRingedSite B S hS).O)).FullSubcategory :=
  ObjectProperty.lift _ (smallAffineZariskiAssociatedModuleQcoh B S hS) fun M =>
    smallAffineZariski_isQuasicoherentOnSite_restriction B S hS _
      (SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS M.obj
        M.property)

/-- The corestricted functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` is fully faithful. -/
public noncomputable def fullyFaithfulSmallAffineZariskiAssociatedModuleQcohOnSite :
    (smallAffineZariskiAssociatedModuleQcohOnSite B S hS).FullyFaithful :=
  ObjectProperty.fullyFaithfulLift _ _
    (fullyFaithfulSmallAffineZariskiAssociatedModuleQcoh B S hS)

/-- The corestricted functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` is essentially surjective. -/
public theorem essSurj_smallAffineZariskiAssociatedModuleQcohOnSite :
    (smallAffineZariskiAssociatedModuleQcohOnSite B S hS).EssSurj where
  mem_essImage F := by
    obtain ⟨G, ⟨e⟩⟩ :=
      smallAffineZariski_essImage_associatedModuleQcoh B S hS F.obj F.property
    exact ⟨G, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- The functor `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}` is an equivalence from the quasi-coherent
`𝒪_S`-modules onto the quasi-coherent modules on the ringed site `(S_{affine, Zar}, 𝒪_affine)`:
every such module comes from a `𝒢`, and from a unique one. -/
@[stacks 0GZX "(2) ⇔ (4) at τ = Zariski"]
public theorem isEquivalence_smallAffineZariskiAssociatedModuleQcohOnSite :
    (smallAffineZariskiAssociatedModuleQcohOnSite B S hS).IsEquivalence :=
  have hff := fullyFaithfulSmallAffineZariskiAssociatedModuleQcohOnSite B S hS
  have := hff.full
  have := hff.faithful
  have := essSurj_smallAffineZariskiAssociatedModuleQcohOnSite B S hS
  {}

/-- The equivalence of categories `QCoh(𝒪_S) ≌ QCoh(S_{affine, Zar}, 𝒪_affine)` whose functor
is `𝒢 ↦ 𝒢ᵃ|_{S_{affine, Zar}}`. -/
@[stacks 0GZX "(2) ⇔ (4) at τ = Zariski"]
public noncomputable def smallAffineZariskiAssociatedModuleQcohEquivalence :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallAffineZariskiRingedSite B S hS).O)).FullSubcategory :=
  have := isEquivalence_smallAffineZariskiAssociatedModuleQcohOnSite B S hS
  (smallAffineZariskiAssociatedModuleQcohOnSite B S hS).asEquivalence

end AlgebraicGeometry

end
