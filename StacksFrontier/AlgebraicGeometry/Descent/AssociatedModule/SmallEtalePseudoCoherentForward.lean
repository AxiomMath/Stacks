module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentObligation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence passes from the small Zariski site to the small étale site

Let `S` be a scheme, `ε` the comparison morphism from the small étale site of `S` to its small
Zariski site, and `E` an object of `D(𝒪_S)`. If `E` is `m`-pseudo-coherent then so is `ε^*E`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.opensRestrictionSection`: a section of restriction of
  `𝒪_S`-modules to the slice over an open `V`, the direct image along `V ↪ S`.

## Main results

* `AlgebraicGeometry.SmallEtale.coversTop_obj_opensToSmallEtale`: the images under `ε` of all
  the opens of `S` cover the final object of the small étale topos of `S`.
* `AlgebraicGeometry.SmallEtale.opensRestrictionSectionIso`: `opensRestrictionSection` is a
  section of restriction to the slice over `V`.
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_sliceStructureMap`: the
  associated-module functor of the small étale site of the slice over an open of `S` is left
  exact.
* `AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`: if `E` is
  `m`-pseudo-coherent on the small Zariski site then `ε^*E` is `m`-pseudo-coherent on the small
  étale site.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The family of all opens of a scheme covers the final object of its small Zariski site. -/
public theorem coversTop_id_opens :
    (Opens.grothendieckTopology ↥S).CoversTop (id : S.Opens → S.Opens) := fun U =>
  (Opens.grothendieckTopology ↥S).superset_covering (fun T _g _ => ⟨T, ⟨𝟙 T⟩⟩)
    ((Opens.grothendieckTopology ↥S).top_mem U)

/-- The images under `ε` of all the opens of `S` cover the final object of the small étale topos
of `S`. -/
public theorem coversTop_obj_opensToSmallEtale :
    (topology B S hS).CoversTop (opensToSmallEtale B S hS).obj :=
  coversTop_opensToSmallEtale B S hS (id : S.Opens → S.Opens) (coversTop_id_opens S)

/-! ### Restriction to the slice over an open has a left exact section -/

/-- A section of restriction of `𝒪_S`-modules to the slice over an open `V`: read through the
identification `AlgebraicGeometry.Scheme.Modules.overEquiv` of sheaves of modules on the small
Zariski site of `S` localized at `V` with `𝒪_V`-modules, it is the direct image along the open
immersion `V ↪ S`. -/
public noncomputable def opensRestrictionSection (V : S.Opens) :
    SheafOfModules.{u} (S.ringCatSheaf.over V) ⥤ SheafOfModules.{u} S.ringCatSheaf :=
  (Scheme.Modules.overEquiv V).functor ⋙ Scheme.Modules.pushforward V.ι

/-- The section `opensRestrictionSection` is left exact. -/
public noncomputable instance preservesFiniteLimits_opensRestrictionSection (V : S.Opens) :
    PreservesFiniteLimits (opensRestrictionSection S V) :=
  comp_preservesFiniteLimits (Scheme.Modules.overEquiv V).functor
    (Scheme.Modules.pushforward V.ι)

/-- `opensRestrictionSection` is a section of restriction to the slice over `V`. -/
public noncomputable def opensRestrictionSectionIso (V : S.Opens) :
    opensRestrictionSection S V ⋙ SheafOfModules.overFunctor.{u} S.ringCatSheaf V ≅ 𝟭 _ :=
  have h : (opensRestrictionSection S V ⋙ SheafOfModules.overFunctor.{u} S.ringCatSheaf V) ⋙
      (Scheme.Modules.overEquiv V).functor ≅ (Scheme.Modules.overEquiv V).functor :=
    Functor.isoWhiskerLeft (opensRestrictionSection S V)
        (Scheme.Modules.overFunctorEquiv V) ≪≫
      Functor.isoWhiskerLeft (Scheme.Modules.overEquiv V).functor
        (Scheme.Modules.restrictFunctorAdjCounitIso V.ι) ≪≫
      (Scheme.Modules.overEquiv V).functor.rightUnitor
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.overEquiv V).unitIso ≪≫
    Functor.isoWhiskerRight h (Scheme.Modules.overEquiv V).inverse ≪≫
    (Scheme.Modules.overEquiv V).unitIso.symm

/-- The associated-module functor of the small étale site of the slice of `S` over an open `V` is
left exact. -/
public theorem preservesFiniteLimits_pullback_sliceStructureMap (V : S.Opens) :
    PreservesFiniteLimits (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)) := by
  have hF : PreservesFiniteLimits (SheafOfModules.pullback.{u} (structureMap B S hS)) :=
    preservesFiniteLimits_associatedModule B S hS
  exact preservesFiniteLimits_of_natIso
    (F := opensRestrictionSection S V ⋙
      (SheafOfModules.pullback.{u} (structureMap B S hS) ⋙
        SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
          ((opensToSmallEtale B S hS).obj V)))
    ((Functor.isoWhiskerLeft (opensRestrictionSection S V)
        (associatedModuleOverIso B S hS V)).symm ≪≫
      Functor.isoWhiskerRight (opensRestrictionSectionIso S V)
        (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)) ≪≫
      Functor.leftUnitor _)

variable [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- If `E` is `m`-pseudo-coherent on the small Zariski site of `S` then `ε^*E` is
`m`-pseudo-coherent on the small étale site of `S`, where the derived functor is
`CategoryTheory.Functor.mapDerivedCategory` of the associated-module functor. -/
@[stacks 08HE "clause (1) ⇒ (2) only: if `E` is `m`-pseudo-coherent on the small Zariski site of
  `S` then `ε^*E` is `m`-pseudo-coherent on the small étale site of `S`, `ε` being the comparison
  of Stacks 08H7. Clause (2) ⇒ (1) is
  `AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent`.", sga "6 I 2.13" "special case"]
public theorem pseudoCoherentToAssociatedModule_of_slice_exact
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    (m : ℤ) :
    PseudoCoherentToAssociatedModule B S hS E m := by
  intro hE
  let G : ∀ V : S.Opens, _ := fun V => SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)
  have hη : ∀ V : S.Opens, _ :=
    fun V => asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))
  exact AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses
    (X := smallEtaleRingedSite B S hS)
    (Y := S.zariskiRingedSite)
    (opensToSmallEtale B S hS) (associatedModuleOfSheaf B S hS)
    G
    (additive_associatedModuleOfSheaf B S hS)
    (preservesFiniteLimits_associatedModuleOfSheaf B S hS)
    (preservesFiniteColimits_associatedModuleOfSheaf B S hS)
    (fun V => SheafOfModules.pullback_additive (sliceStructureMap B S hS V))
    (preservesFiniteLimits_pullback_sliceStructureMap B S hS)
    (fun V => PreservesColimitsOfSize.preservesFiniteColimits.{0, 0}
      (F := SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)))
    inferInstance
    (coversTop_obj_opensToSmallEtale B S hS)
    hη
    (associatedModuleOverIso B S hS) E m hE

end AlgebraicGeometry.SmallEtale

end
