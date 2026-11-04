module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleReindexComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureModuleSmallBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleSheafCondition

/-!
# `f_*𝒪_X` on an étale chart of the target is the direct image of structure sheaves there

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, let `V` be an étale scheme chart of `Y`, and let `ψ : V ×_Y X ⟶ V` be the
cartesian projection, read as a morphism of schemes. If `ψ` is affine, the restriction of the
direct image `f_*𝒪_X` (Stacks 03ZV) to the slice of the small étale site of `Y` at `V` is the
module `Mᵃ` (Stacks 03DU) of the scheme-level direct image `ψ_*𝒪_{V ×_Y X}`.

## Main definitions

* `AlgebraicGeometry.Space.overPushforwardStructureModuleIsoSliceAssociatedModule`: the
  isomorphism `(f_*𝒪_X)|_V ≅ (ψ_*𝒪_{V ×_Y X})ᵃ`.

## Implementation notes

The affineness hypothesis is needed to form the right-hand side:
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule` takes a quasi-coherent module on the
chart's scheme, and `Stacks.Morphisms.pushforwardStructureSheaf` of a morphism of schemes is
quasi-coherent for an affine morphism (`Stacks.Modules.isQuasicoherent_pushforwardStructureSheaf`).

The affineness instance is passed positionally to
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`, which asks for it of
`AlgebraicGeometry.SmallEtale.schemeHom` of the cartesian projection: that morphism is
`(BigFppfOver.toScheme ‹_›).map (hf.snd V.1.hom)` by `rfl` but not syntactically, so instance
search does not find it.

Each direct image is written with every argument of `CategoryTheory.SheafOfModules.pushforward`
given, at the spellings `AlgebraicGeometry.Space.chartSchemeSiteModulePushforwardIso` uses: the
chart arrives at two spellings of its ambient category and the slice at two spellings of its
topology, and a continuity datum proved at one is not found by instance search at the other.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)

/-- For a representable morphism `f : X ⟶ Y` of algebraic spaces and an étale scheme chart `V`
of `Y` whose cartesian projection `ψ : V ×_Y X ⟶ V` is affine, the restriction to the slice at
`V` of `f_*𝒪_X` (Stacks 03ZV) is the module `Mᵃ` (Stacks 03DU) of the scheme-level direct image
`ψ_*𝒪_{V ×_Y X}`. -/
def overPushforwardStructureModuleIsoSliceAssociatedModule
    [haff : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom))] :
    (pushforwardStructureModule B S hS f).over V ≅
      SmallEtale.sliceAssociatedModule B S hS Y.1 Y.2 V
        (Stacks.Morphisms.pushforwardStructureSheaf
          ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)))
        (SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent B S hS Y.1 V
          (Stacks.Morphisms.pushforwardStructureSheaf
            ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)))) := by
  have h12 : (pushforwardStructureModule B S hS f).over V ≅
      (@SheafOfModules.pushforward.{u}
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).C _
        ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hf V)).C _
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
        ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hf V)).J
        (Over.post (X := V) (smallBaseChange B S hS f hf))
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hf V)).O)
        (isContinuous_overPost_smallBaseChange B S hS f hf V)
        (chartLocalizedSharp B S hS f hf V)).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
            (baseChangeChart B S hS f hf V)).O))) :=
    (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS Y) V).mapIso
        (pushforwardStructureModuleIsoSmallBaseChange B S hS f hf) ≪≫
      eqToIso (over_smallBaseChangeModulePushforward_obj B S hS f hf V
        (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)))
  have hunit :
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          (chartScheme (baseChangeChart B S hS f hf V))
          ((SmallEtale.toOver B S hS X.1).obj
            (baseChangeChart B S hS f hf V)).left.property).obj
          (SheafOfModules.unit
            (chartScheme (baseChangeChart B S hS f hf V)).ringCatSheaf) ≅
        SheafOfModules.unit
          (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hf V)) :=
    @asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit
      (associatedBigEtaleSite B) (chartScheme (baseChangeChart B S hS f hf V))
      ((SmallEtale.toOver B S hS X.1).obj (baseChangeChart B S hS f hf V)).left.property)
  have h4 :
      (@SheafOfModules.pushforward.{u}
          (chartSchemeSite B S hS Y V) _
          (chartSchemeSite B S hS X (baseChangeChart B S hS f hf V)) _
          (chartSchemeTopology B S hS Y V)
          (chartSchemeTopology B S hS X (baseChangeChart B S hS f hf V))
          (chartSchemeBaseChange B S hS f hf V)
          (chartSchemeSiteStructureSheaf B S hS Y V)
          (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hf V))
          (isContinuous_chartSchemeBaseChange B S hS f hf V)
          (chartSchemeBaseChangeSharp B S hS f hf V)).obj
          (SheafOfModules.unit
            (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hf V))) ≅
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            (chartScheme V) ((SmallEtale.toOver B S hS Y.1).obj V).left.property).obj
          (Stacks.Morphisms.pushforwardStructureSheaf
            ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom))) :=
    (@SheafOfModules.pushforward.{u}
        (chartSchemeSite B S hS Y V) _
        (chartSchemeSite B S hS X (baseChangeChart B S hS f hf V)) _
        (chartSchemeTopology B S hS Y V)
        (chartSchemeTopology B S hS X (baseChangeChart B S hS f hf V))
        (chartSchemeBaseChange B S hS f hf V)
        (chartSchemeSiteStructureSheaf B S hS Y V)
        (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hf V))
        (isContinuous_chartSchemeBaseChange B S hS f hf V)
        (chartSchemeBaseChangeSharp B S hS f hf V)).mapIso hunit.symm ≪≫
      @_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
        (associatedBigEtaleSite B) _ _ (baseChangeChartHom B S hS f hf V).left haff
        (SheafOfModules.unit (chartScheme (baseChangeChart B S hS f hf V)).ringCatSheaf)
        inferInstance
  refine ((chartModuleReindexEquivalence B S hS Y V).trans
    (representedSmallEtaleModuleEquivalence B S hS
      (chartOverObject B S hS Y V)).symm).fullyFaithfulFunctor.preimageIso ?_
  refine ((chartModuleReindexEquivalence B S hS Y V).trans
    (representedSmallEtaleModuleEquivalence B S hS
      (chartOverObject B S hS Y V)).symm).functor.mapIso h12 ≪≫ ?_
  refine eqToIso (chartSchemeSiteModule_eq_inverse_chartModuleReindex B S hS Y V _).symm ≪≫ ?_
  refine chartSchemeSiteModulePushforwardIso B S hS f hf V
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hf V)).O))) ≪≫ ?_
  refine h4 ≪≫ ?_
  refine _root_.AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules
      (associatedBigEtaleSite B) (chartScheme V)
      ((SmallEtale.toOver B S hS Y.1).obj V).left.property
      (Stacks.Morphisms.pushforwardStructureSheaf
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom))) ≪≫ ?_
  refine (representedSmallEtaleModuleEquivalence B S hS
      (chartOverObject B S hS Y V)).unitIso.app _ ≪≫ ?_
  exact eqToIso (congrArg
    (fun P => (representedSmallEtaleModuleEquivalence B S hS
      (chartOverObject B S hS Y V)).inverse.obj P)
    (chartModuleReindex_sliceAssociatedModule B S hS Y V
      (Stacks.Morphisms.pushforwardStructureSheaf
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)))).symm)

end AlgebraicGeometry.Space

end
