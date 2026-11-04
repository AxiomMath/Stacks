module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtalePushforwardModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRelocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSiteInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentToSmall
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteMorphismLocalization

/-!
# The slice of a big site of an algebraic space at an object is the big site of that object

Let `X` be an algebraic space and `W : Y ⟶ X` an object of its big étale (resp. big fppf) site.
The iterated slice equivalence `(Spaces/X)/W ≌ Spaces/Y` identifies the localization at `W` of the
big étale (resp. big fppf) ringed site of `X` with the big étale (resp. big fppf) ringed site of
`Y`; the structure sheaves agree on the nose, both being global functions on the underlying
algebraic space. For `W` étale over `X` this identification is compatible with the localization of
`π_X` and with the identification of Stacks 04LZ on the spaces-étale sites.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.sliceRingedSiteHom`: the identification for the big étale
  site, as a morphism of ringed sites with underlying functor `Over.iteratedSliceBackward W`.
* `AlgebraicGeometry.BigFppfSpaceSite.sliceRingedSiteHom`: the same for the big fppf site.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.localized_spacesEtaleRestriction_comp`: the square
  formed by the localization of `π_X` at an étale chart, `π_Y`, and the two identifications
  commutes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

/-- A continuous functor with a left adjoint is a morphism of sites, being representably flat. -/
private theorem isMorphismOfSites_of_adjunction {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [G.IsContinuous J K] : G.IsMorphismOfSites J K :=
  haveI : G.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) {X : E.Spaces}

/-- The iterated slice functor `Spaces/Y ⥤ (Spaces/X)/W` is a morphism of the big étale sites:
it is continuous and, being a right adjoint, representably flat. -/
theorem iteratedSliceBackward_isMorphismOfSites (W : Over X) :
    (Over.iteratedSliceBackward W).IsMorphismOfSites (E.bigEtaleTopology W.left)
      ((E.bigEtaleTopology X).over W) := by
  exact isMorphismOfSites_of_adjunction (Over.iteratedSliceEquiv W).toAdjunction _ _

/-- **The slice at `W : Y ⟶ X` of the big étale ringed site of `X` is the big étale ringed site
of `Y`**, as a morphism of ringed sites whose functor is the iterated slice equivalence. -/
def sliceRingedSiteHom (W : Over X) :
    RingedSite.Hom ((E.bigEtaleRingedSite X).over W) (E.bigEtaleRingedSite W.left) where
  u := Over.iteratedSliceBackward W
  isMorphismOfSites := iteratedSliceBackward_isMorphismOfSites E W
  fsharp := 𝟙 _

variable {Y : E.Spaces} (p : Y ⟶ X) (hp : Space.IsEtale E.fppfSite S E.fppf_mem p.hom)

/-- **The localization of `π_X` at an étale chart is `π_Y`.** For an étale `p : Y ⟶ X`, the
localization of `π_X` at the object `p` of the spaces-étale site of `X`, followed by the
identification of Stacks 04LZ, is the identification of the slice of the big étale site at `p`
with the big étale site of `Y`, followed by `π_Y`. -/
theorem localized_spacesEtaleRestriction_comp :
    ((spacesEtaleRestrictionRingedSiteHom E X).localized
        (Space.etaleObject E.fppfSite S E.fppf_mem p hp)).comp
      (Space.spacesEtaleLocalizationRingedSiteHom E.fppfSite S E.fppf_mem p hp) =
    (sliceRingedSiteHom E (Over.mk p)).comp (spacesEtaleRestrictionRingedSiteHom E Y) := by
  refine RingedSite.Hom.ext_of_heq _ _ rfl (heq_of_eq ?_)
  ext V x
  rfl

/-- `smallToSlice` is a morphism of sites: it is continuous and, being an equivalence, a right
adjoint. -/
theorem smallToSlice_isMorphismOfSites (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    (Space.SpacesEtale.smallToSlice E.fppfSite S E.fppf_mem Q).IsMorphismOfSites
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem Q.obj.left)
      ((Space.SpacesEtale.topology E.fppfSite S E.fppf_mem X).over Q) := by
  exact isMorphismOfSites_of_adjunction
    (G := Space.SpacesEtale.smallToSlice E.fppfSite S E.fppf_mem Q)
    (Space.SpacesEtale.sliceEquivSmall E.fppfSite S E.fppf_mem Q).toAdjunction _ _

/-- **The slice at `Q` of the ringed spaces-étale site of `X` is the ringed spaces-étale site of
`Q`**, as a morphism of ringed sites with functor `smallToSlice` and identity structure map; its
direct image of modules is `AlgebraicGeometry.Space.SpacesEtale.moduleToSmall` after restriction
to the slice. -/
def smallSliceRingedSiteHom (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    RingedSite.Hom ((Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem X).over Q)
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Q.obj.left) where
  u := Space.SpacesEtale.smallToSlice E.fppfSite S E.fppf_mem Q
  isMorphismOfSites := smallToSlice_isMorphismOfSites E Q
  fsharp := 𝟙 _

/-- **The localization of `π_X` at an object `Q` of the spaces-étale site is `π_Q`**, through the
identifications of the two slices with the sites of `Q`. -/
theorem localized_spacesEtaleRestriction_comp_smallSlice
    (Q : Space.SpacesEtale E.fppfSite S E.fppf_mem X) :
    ((spacesEtaleRestrictionRingedSiteHom E X).localized Q).comp (smallSliceRingedSiteHom E Q) =
    (sliceRingedSiteHom E Q.obj).comp (spacesEtaleRestrictionRingedSiteHom E Q.obj.left) := by
  refine RingedSite.Hom.ext_of_heq _ _ rfl (heq_of_eq ?_)
  ext V x
  rfl

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) {X : T.Spaces}

/-- The iterated slice functor is a morphism of the big fppf sites. -/
theorem iteratedSliceBackward_isMorphismOfSites (W : Over X) :
    (Over.iteratedSliceBackward W).IsMorphismOfSites (BigFppfSpaceOver.topology T W.left)
      ((BigFppfSpaceOver.topology T X).over W) := by
  exact isMorphismOfSites_of_adjunction (Over.iteratedSliceEquiv W).toAdjunction _ _

/-- **The slice at `W : Y ⟶ X` of the big fppf ringed site of `X` is the big fppf ringed site of
`Y`.** -/
def sliceRingedSiteHom (W : Over X) :
    RingedSite.Hom ((bigFppfRingedSite T X).over W) (bigFppfRingedSite T W.left) where
  u := Over.iteratedSliceBackward W
  isMorphismOfSites := iteratedSliceBackward_isMorphismOfSites T W
  fsharp := 𝟙 _

end AlgebraicGeometry.BigFppfSpaceSite

end
