module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.QuasicoherenceOverMapDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesianEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialBigFppfModuleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModulePullbackEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.UnitIsoMapBijective
public import StacksFrontier.CategoryTheory.Adjunction.UnitIsoOfIntertwining

/-!
# Descent of quasi-coherent modules along an fppf hypercovering of algebraic spaces

Let `a : U → X` be an fppf hypercovering of an algebraic space `X` by a simplicial algebraic
space `U`. The pullback `a^* : QCoh(𝒪_X) → QCoh(𝒪_U)` along the morphism of ringed topoi
`a : (Sh(U_{étale}), 𝒪_U) ⟶ (Sh(X_{étale}), 𝒪_X)` of Stacks 0DE7 is an equivalence with
quasi-inverse `a_*` (Stacks 0DHD).

The proof goes around the square of Stacks 0DHC,
```
  (Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total}) --h--> (Sh(U_{étale}), 𝒪_U)
           | a_fppf                                          | a
           v                                                 v
  (Sh((Spaces/X)_fppf), 𝒪_{big}) ---------a_X-----------> (Sh(X_{étale}), 𝒪_X)
```
in which `a_{fppf}^*` is fully faithful with the cartesian modules as essential image
(Stacks 0DAB), `a_X^*` is an equivalence on quasi-coherent modules (Stacks 0DGN (5)), and the unit
of `h` is invertible on quasi-coherent modules (Stacks 0DH0). Quasi-coherence of the module `H`
with `a_{fppf}^*H ≅ h^*G` descends along the fppf covering `U_0 ⟶ X` (Stacks 03DN).

## Main results

All in the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `isIso_augmentationRingedToposHom_unit_app`: the unit `F ⟶ a_*a^*F` is invertible for
  quasi-coherent `F`.
* `exists_isQuasicoherentOnSite_augmentation_pullbackModules_obj_iso`: every quasi-coherent
  `𝒪_U`-module is `a^*F` for a quasi-coherent `F`.
* `descent_quasicoherent_of_isHypercoveringAugmentation`: **Stacks 0DHD.**
* `quasicoherentDescentEquivalence`: the equivalence `QCoh(𝒪_X) ≌ QCoh(𝒪_U)` given by `a^*` and
  `a_*`.

## References

* [Stacks Project, Tag 0DHD](https://stacks.math.columbia.edu/tag/0DHD)
* [Stacks Project, Tag 0DHC](https://stacks.math.columbia.edu/tag/0DHC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial Stacks.CategoryTheory.Hypercovering

universe u

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  {a : U ⟶ (SimplicialObject.const T.Spaces).obj X}

section FullyFaithful

/-- `h^*` is bijective on morphisms into a quasi-coherent `𝒪_U`-module, as the unit of `h` is
invertible there (Stacks 0DH0). -/
private theorem bijective_bigFppfTotalRingedHom_pullbackModules_map
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O))
    [G.IsQuasicoherentOnSite]
    (P : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O)) :
    Function.Bijective (fun f : P ⟶ G ↦
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1} (bigFppfTotalRingedHom a).toModulesHom).map f) :=
  (((bigFppfTotalRingedHom a).pullbackAdjPushforwardModules.isIso_unit_app_iff_bijective_map G).1
    (isIso_bigFppfTotalRingedHom_unit_app a G)) P

variable (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)

include h

/-- **`a^*` is bijective on morphisms into a quasi-coherent module.** Going around the square of
Stacks 0DHC, `h^*a^* ≅ a_{fppf}^*a_X^*`, where `a_{fppf}^*` is fully faithful (Stacks 0DAB),
`a_X^*` is bijective on morphisms into the quasi-coherent `F` (Stacks 0DGN (6)) and `h^*` is
bijective on morphisms into the quasi-coherent `a^*F` (Stacks 0DH0). -/
theorem bijective_augmentationRingedToposHom_pullbackModules_map
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)))
    [hF : F.IsQuasicoherentOnSite]
    (Y : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X))) :
    Function.Bijective (fun φ : Y ⟶ F ↦
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1}
        (augmentationRingedToposHom a).toModulesHom).map φ) := by
  have hX := ((BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X).pullbackAdjPushforwardModules
    |>.isIso_unit_app_iff_bijective_map F).1
      (BigFppfSpaceSite.isIso_fppfToSpacesEtaleRingedHom_unit_app_bigFppfModuleUnitTopos F) Y
  have hff := (nonempty_fullyFaithful_bigFppfAugmentation_pullbackModules h).some
  have h1 := (Functor.bijective_comp_map_iff_unitIsoMapBijective (hff.map_bijective _ _)).2 hX
  have h2 := (Functor.bijective_map_iff_of_natIso_unitIsoMapBijective
    (RingedToposHom.pullbackModulesCompIso (bigFppfAugmentationRingedHom a)
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)) Y F).2 h1
  have h3 := (Functor.bijective_map_iff_of_natIso_unitIsoMapBijective
    (bigFppfAugmentationSquareTwoIso a).pullbackModulesIso Y F).2 h2
  have h4 := (Functor.bijective_map_iff_of_natIso_unitIsoMapBijective
    (RingedToposHom.pullbackModulesCompIso (bigFppfTotalRingedHom a)
      (augmentationRingedToposHom a)) Y F).1 h3
  have hA := isQuasicoherentOnSite_augmentationRingedToposHom_pullbackModules_obj a F
  exact (Functor.bijective_comp_map_iff_unitIsoMapBijective
    (@bijective_bigFppfTotalRingedHom_pullbackModules_map _ _ _ _ a _ hA _)).1 h4

/-- **The unit `F ⟶ a_*a^*F` is an isomorphism for a quasi-coherent `𝒪_X`-module `F`.** -/
theorem isIso_augmentationRingedToposHom_unit_app
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)))
    [F.IsQuasicoherentOnSite] :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (augmentationRingedToposHom a)).unit.app F) :=
  ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (augmentationRingedToposHom a)).isIso_unit_app_iff_bijective_map F).2
    (bijective_augmentationRingedToposHom_pullbackModules_map h F)

end FullyFaithful

section EssentiallySurjective

variable (a) in
/-- Every object `V/U_n` of `(Spaces/U)_{fppf,total}` maps to the image under `u` of the final
object `U_n/U_n` of `(U_n)_{spaces,étale}`. -/
theorem nonempty_hom_toBigFppfTotal_obj (A : Grothendieck (SimplicialOver.slices U)) :
    ∃ V : SimplicialSpacesEtaleSite T.schemeSite S T.scheme_mem U,
      Nonempty (A ⟶ (bigFppfTotalRingedSiteHom a).u.obj V) :=
  ⟨(degreeInclusion U A.base.unop).obj
      (SpacesEtale.idObj T.schemeSite S T.scheme_mem (U.obj A.base)),
    ⟨⟨𝟙 _, Over.mkIdTerminal.from _⟩⟩⟩

variable (a) in
/-- **`h^*` carries quasi-coherent `𝒪_U`-modules to quasi-coherent `𝒪_{big,total}`-modules**
(Stacks 03DO for the morphism of ringed sites of `h`). -/
theorem isQuasicoherentOnSite_bigFppfTotalRingedHom_pullbackModules_obj
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O))
    [hG : G.IsQuasicoherentOnSite] :
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1}
      (bigFppfTotalRingedHom a).toModulesHom).obj G).IsQuasicoherentOnSite := by
  rw [bigFppfTotalRingedHom_eq_ringedToposHom]
  have hq := Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom
    (bigFppfTotalRingedSiteHom a) (nonempty_hom_toBigFppfTotal_obj a) hG
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (bigFppfTotalRingedSiteHom a).ringedToposHom).ofNatIsoRight
        (bigFppfTotalRingedSiteHom a).pushforwardToposIso).leftAdjointUniq
      (bigFppfTotalRingedSiteHom a).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos).app
        G).symm hq

variable (a) in
/-- **A module whose pullback along `a_{fppf}` is quasi-coherent restricts to a quasi-coherent
module along `V/U_n ↦ V/X`**: `a_{fppf}^*` is that restriction, read through restrictions of
scalars along isomorphisms of structure sheaves. -/
theorem isQuasicoherentOnSite_restrictionModules_of_bigFppfAugmentation
    (H : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (BigFppfSpaceOver.topology T X)) (BigFppfSpaceSite.structureSheaf T X)))
    (hH : ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1}
      (bigFppfAugmentationRingedHom a).toModulesHom).obj H).IsQuasicoherentOnSite) :
    ((Stacks.Sheaves.ToposPullback.restrictionModules (SimplicialOver.totalTopology T.topology U)
      (BigFppfSpaceOver.topology T X) (SimplicialOver.augmentationFunctor U a)
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (BigFppfSpaceOver.topology T X))
        (BigFppfSpaceSite.structureSheaf T X))).obj H).IsQuasicoherentOnSite := by
  have := isIso_bigFppfAugmentationRingedHom_fSharpInverseImage a
  have e :=
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
      (bigFppfAugmentationRingedHom a).toModulesHom).app _).symm ≪≫
    (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp
      (bigFppfAugmentationRingedHom a).toModulesHom).mapIso
        ((Stacks.Sheaves.ToposPullback.restrictionModuleIso
          (SimplicialOver.totalTopology T.topology U) (BigFppfSpaceOver.topology T X)
          (SimplicialOver.augmentationFunctor U a)
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
            (J := (BigFppfSpaceOver.topology T X))
            (BigFppfSpaceSite.structureSheaf T X))).app H).symm
  have h3 := SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hH
  open Stacks.SheafOfModules in
  have h2 := isQuasicoherentOnSite_of_restrictScalars_of_isIso_quasicoherenceOverMapDescent _ _ h3
  open Stacks.SheafOfModules in
  exact isQuasicoherentOnSite_of_restrictScalars_of_isIso_quasicoherenceOverMapDescent
    (Stacks.Sheaves.ToposPullback.restrictionRingIso (SimplicialOver.totalTopology T.topology U)
      (BigFppfSpaceOver.topology T X) (SimplicialOver.augmentationFunctor U a)
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (BigFppfSpaceOver.topology T X)) (BigFppfSpaceSite.structureSheaf T X))).hom _ h2

variable (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)

attribute [local instance] slicesι_isContinuous slicesι_isCocontinuous in
include h in
/-- **Quasi-coherence descends along `a_{fppf}`**: a module `H` on `(Spaces/X)_fppf` whose
pullback `a_{fppf}^*H` is quasi-coherent is quasi-coherent. The restriction of `a_{fppf}^*H` to
the component of degree `0` is the restriction of `H` along `V/U_0 ↦ V/X`, and `U_0 ⟶ X` is an
fppf covering (Stacks 03DN). -/
theorem isQuasicoherentOnSite_of_bigFppfAugmentation_pullbackModules_obj
    (H : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (BigFppfSpaceOver.topology T X)) (BigFppfSpaceSite.structureSheaf T X)))
    (hH : ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1}
      (bigFppfAugmentationRingedHom a).toModulesHom).obj H).IsQuasicoherentOnSite) :
    H.IsQuasicoherentOnSite := by
  have hR := isQuasicoherentOnSite_restrictionModules_of_bigFppfAugmentation a H hH
  have : ∀ V : Over (U.obj (op ⦋0⦌)), (Over.post (X := V) (slicesι U ⦋0⦌)).IsContinuous
      ((BigFppfSpaceOver.topology T (U.obj (op ⦋0⦌))).over V)
      ((SimplicialOver.totalTopology T.topology U).over ((slicesι U ⦋0⦌).obj V)) :=
    fun V ↦ Functor.isContinuous_overPost _ _ _ V
  have h0 := Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1} (J := SimplicialOver.totalTopology T.topology U)
    (K := BigFppfSpaceOver.topology T (U.obj (op ⦋0⦌))) (slicesι U ⦋0⦌) (𝟙 _) (IsIso.id _) _ hR
  have hEq : slicesι U ⦋0⦌ ⋙ SimplicialOver.augmentationFunctor U a =
      Over.map (a.app (op ⦋0⦌)) :=
    SimplicialOver.ι_comp_augmentationFunctor U a (op ⦋0⦌)
  have h1 :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward_of_comp_eq_quasicoherenceOverMapDescent
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (BigFppfSpaceOver.topology T X)) (BigFppfSpaceSite.structureSheaf T X))
    (slicesι U ⦋0⦌) (SimplicialOver.augmentationFunctor U a) (Over.map (a.app (op ⦋0⦌))) hEq H
    h0
  have hcov : Sieve.generate (Presieve.singleton (a.app (op ⦋0⦌))) ∈ T.topology X := by
    rw [← T.toGrothendieck_pretopology_bigFppfPretopology]
    exact ⟨_, h.1, Sieve.le_generate _⟩
  exact
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_pushforward_overMap_quasicoherenceOverMapDescent
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (BigFppfSpaceOver.topology T X))
      (BigFppfSpaceSite.structureSheaf T X)) H (I := PUnit) (fun _ ↦ a.app (op ⦋0⦌))
    (Stacks.SheafOfModules.coversTop_over_mk_of_generate_singleton_mem_quasicoherenceOverMapDescent
      _ hcov) (fun _ ↦ h1)

variable (T X) in
/-- **Stacks 0DGN (5), essential surjectivity, for the morphism of ringed topoi `a_X`**: every
quasi-coherent module `H` on `(Spaces/X)_fppf` is `a_X^*F` for a quasi-coherent `𝒪_X`-module
`F`. -/
theorem exists_fppfToSpacesEtaleRingedHom_pullbackModules_obj_iso
    (H : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (BigFppfSpaceOver.topology T X)) (BigFppfSpaceSite.structureSheaf T X)))
    [hH : H.IsQuasicoherentOnSite] :
    ∃ F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)), F.IsQuasicoherentOnSite ∧
      Nonempty ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1,
          u + 1, u + 1, u + 1, u + 1}
        (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X).toModulesHom).obj F ≅ H) := by
  rw [BigFppfSpaceSite.fppfToSpacesEtaleRingedHom_eq_ringedToposHom_bigFppfModuleUnitTopos]
  let E := BigFppfSpaceSite.quasicoherentPullbackEquivalence T X
  let H' : (SheafOfModules.isQuasicoherentOnSite.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (BigFppfSpaceSite.bigFppfRingedSite T X).O)).FullSubcategory := ⟨H, hH⟩
  refine ⟨(E.inverse.obj H').obj, (E.inverse.obj H').property, ⟨?_⟩⟩
  exact ((((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).ringedToposHom).ofNatIsoRight
        (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).pushforwardToposIso).leftAdjointUniq
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T
        X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos).app _) ≪≫
    (ObjectProperty.ι _).mapIso (E.counitIso.app H')

include h in
/-- **`a^*` is essentially surjective onto quasi-coherent `𝒪_U`-modules.** For `G`
quasi-coherent, `h^*G` is quasi-coherent and cartesian (Stacks 0D7M), hence `h^*G ≅ a_{fppf}^*H`
(Stacks 0DAB) with `H` quasi-coherent (Stacks 03DN along `U_0 ⟶ X`), hence `H ≅ a_X^*F` with `F`
quasi-coherent (Stacks 0DGN (5)). Going around the square of Stacks 0DHC, `h^*a^*F ≅ h^*G`, and
`h^*` is fully faithful on quasi-coherent modules (Stacks 0DH0). -/
theorem exists_isQuasicoherentOnSite_augmentation_pullbackModules_obj_iso
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O))
    [hG : G.IsQuasicoherentOnSite] :
    ∃ F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)), F.IsQuasicoherentOnSite ∧
      Nonempty ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1,
          u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a).toModulesHom).obj F ≅ G) := by
  have hM := isQuasicoherentOnSite_bigFppfTotalRingedHom_pullbackModules_obj a G
  open CategoryTheory.SimplicialSiteSituation in
  have hcart :=
    ((isQuasicoherentOnSite_iff_isCartesianModule_and_isQuasicoherentOnSite_componentModule
      (SimplicialOver.situation T.topology U) (bigFppfTotalStructureSheaf a) _).1 hM).1
  obtain ⟨H, ⟨e⟩⟩ := (bigFppfAugmentation_pullbackModules_essImage_iff h _).2 hcart
  have hH := isQuasicoherentOnSite_of_bigFppfAugmentation_pullbackModules_obj h H
    (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hM)
  obtain ⟨F, hF, ⟨eF⟩⟩ := @exists_fppfToSpacesEtaleRingedHom_pullbackModules_obj_iso _ T X H hH
  refine ⟨F, hF, ?_⟩
  have hA := @isQuasicoherentOnSite_augmentationRingedToposHom_pullbackModules_obj _ _ _ _ _ a F hF
  have iso1 := ((RingedToposHom.pullbackModulesCompIso (bigFppfTotalRingedHom a)
      (augmentationRingedToposHom a)).app F).symm ≪≫
    (bigFppfAugmentationSquareTwoIso a).pullbackModulesIso.app F ≪≫
    (RingedToposHom.pullbackModulesCompIso (bigFppfAugmentationRingedHom a)
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)).app F ≪≫
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1}
        (bigFppfAugmentationRingedHom a).toModulesHom).mapIso eF ≪≫ e
  exact Functor.nonempty_iso_of_bijective_map_unitIsoMapBijective _
    (@bijective_bigFppfTotalRingedHom_pullbackModules_map _ _ _ _ a _ hA)
    (bijective_bigFppfTotalRingedHom_pullbackModules_map (a := a) _) iso1

end EssentiallySurjective

section Descent

variable (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)

include h

/-- The counit `a^*a_*G ⟶ G` is an isomorphism for a quasi-coherent `𝒪_U`-module `G`. -/
theorem isIso_augmentationRingedToposHom_counit_app
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O))
    [G.IsQuasicoherentOnSite] :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (augmentationRingedToposHom a)).counit.app G) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_isQuasicoherentOnSite_augmentation_pullbackModules_obj_iso h G
  have := @isIso_augmentationRingedToposHom_unit_app _ _ _ _ _ h F hF
  exact Adjunction.isIso_counit_app_of_isIso_unit_app_representedZariskiModuleAdjunction
    (RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (augmentationRingedToposHom a)) e

/-- The direct image `a_*G` of a quasi-coherent `𝒪_U`-module `G` is quasi-coherent. -/
theorem isQuasicoherentOnSite_augmentationRingedToposHom_pushforwardModules_obj
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O))
    [G.IsQuasicoherentOnSite] :
    ((RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (augmentationRingedToposHom a)).obj G).IsQuasicoherentOnSite := by
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_isQuasicoherentOnSite_augmentation_pullbackModules_obj_iso h G
  have := @isIso_augmentationRingedToposHom_unit_app _ _ _ _ _ h F hF
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a)).unit.app F) ≪≫
      (RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a)).mapIso e) hF

/-- **Stacks 0DHD.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial
algebraic space over `S` and `a : U → X` an augmentation which is an fppf hypercovering of `X`.
Then `a^* : QCoh(𝒪_X) → QCoh(𝒪_U)` is an equivalence with quasi-inverse `a_*`, for the morphism
of ringed topoi `a : (Sh(U_{étale}), 𝒪_U) ⟶ (Sh(X_{étale}), 𝒪_X)` of Stacks 0DE7: `a^*` and
`a_*` preserve quasi-coherence, and the unit `F ⟶ a_*a^*F` and the counit `a^*a_*G ⟶ G` are
isomorphisms for quasi-coherent `F` and `G`. -/
theorem descent_quasicoherent_of_isHypercoveringAugmentation :
    (∀ F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)), F.IsQuasicoherentOnSite →
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a).toModulesHom).obj F).IsQuasicoherentOnSite) ∧
    (∀ G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O),
      G.IsQuasicoherentOnSite →
      ((RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a)).obj G).IsQuasicoherentOnSite) ∧
    (∀ F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)), F.IsQuasicoherentOnSite →
      IsIso
        ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a)).unit.app F)) ∧
    (∀ G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (ringedSite U).J) (ringedSite U).O),
      G.IsQuasicoherentOnSite →
      IsIso
        ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a)).counit.app G)) :=
  ⟨fun F hF ↦ @isQuasicoherentOnSite_augmentationRingedToposHom_pullbackModules_obj _ _ _ _ _
      a F hF,
    fun G hG ↦ @isQuasicoherentOnSite_augmentationRingedToposHom_pushforwardModules_obj _ _ _ _ _
      h G hG,
    fun F hF ↦ @isIso_augmentationRingedToposHom_unit_app _ _ _ _ _ h F hF,
    fun G hG ↦ @isIso_augmentationRingedToposHom_counit_app _ _ _ _ _ h G hG⟩

/-- The equivalence `a^* : QCoh(𝒪_X) ≌ QCoh(𝒪_U)` of Stacks 0DHD, with quasi-inverse `a_*`: the
adjunction `a^* ⊣ a_*` restricted to quasi-coherent modules. -/
def quasicoherentDescentEquivalence :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
          (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
          (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X))).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
          (J := (ringedSite U).J) (ringedSite U).O)).FullSubcategory :=
  (RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (augmentationRingedToposHom a)).restrictEquivalence
    (descent_quasicoherent_of_isHypercoveringAugmentation h).1
    (descent_quasicoherent_of_isHypercoveringAugmentation h).2.1
    (descent_quasicoherent_of_isHypercoveringAugmentation h).2.2.1
    (fun {G G'} g hG hG' _ ↦ by
      have := (descent_quasicoherent_of_isHypercoveringAugmentation h).2.2.2 G hG
      have := (descent_quasicoherent_of_isHypercoveringAugmentation h).2.2.2 G' hG'
      rw [(IsIso.eq_inv_comp _).2
        ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
            (augmentationRingedToposHom a)).counit_naturality g).symm]
      infer_instance)

/-- The functor of the equivalence of Stacks 0DHD is `a^*`. -/
theorem quasicoherentDescentEquivalence_functor_comp_ι :
    (quasicoherentDescentEquivalence h).functor ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1} (augmentationRingedToposHom a).toModulesHom :=
  rfl

/-- The inverse of the equivalence of Stacks 0DHD is `a_*`. -/
theorem quasicoherentDescentEquivalence_inverse_comp_ι :
    (quasicoherentDescentEquivalence h).inverse ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u
          + 1} (augmentationRingedToposHom a) :=
  rfl

end Descent

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
