module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleExtensionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleQuasicoherentWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAContinuousFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Quasi-coherent modules on the affine objects of the spaces-étale site

Let `X` be an algebraic space over a scheme `S` and `𝓕` a quasi-coherent `𝒪_X`-module on the
spaces-étale site `X_{spaces,étale}`, with sections in `Type (u + 1)`. Over an object `V` of
`X_{spaces,étale}` represented by an affine scheme, `𝓕|_V` has a global presentation, and
`Hⁿ(V, 𝓕) = 0` for `n > 0`.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `SpacesEtale.exists_hom_comparisonFunctor_obj_of_isAffineScheme_spacesEtaleAffineVanishing`: an
  object represented by an affine scheme maps to the image of an affine étale chart under the
  comparison functor of Stacks 03G1.
* `hasGlobalPresentation_over_of_isAffineScheme_spacesEtaleAffineVanishing`: a quasi-coherent
  module is globally presented over every object represented by an affine scheme.

In the namespace `AlgebraicGeometry.BigFppfSpaceSite`:

* `isZero_rightDerived_evaluation_of_isAffineScheme_spacesEtaleAffineVanishing`: a quasi-coherent
  module has no higher cohomology over an object represented by an affine scheme.
* `exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing`: every object of
  `X_{spaces,étale}` has a covering family by objects represented by affine schemes.
* `isZero_moduleCohomology_of_isAffineScheme_spacesEtaleAffineVanishing`: the same vanishing for
  `Stacks.Cohomology.moduleCohomology`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Modules

universe u v r z

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {𝒪 : Cᵒᵖ ⥤ CommRingCat.{r}}
  (h𝒪 : Presheaf.IsSheaf J (SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  (hset : Presheaf.IsSheaf J
    (SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪 ⋙ forget RingCat.{r}))

/-- **A global presentation over an object ascends along the universe lift of the coefficient
rings**: if lowering the coefficient universe of `M` gives a module presented over `Z`, then `M`
is presented over `Z`. -/
theorem hasGlobalPresentation_over_of_sheafRingULiftDown_spacesEtaleAffineVanishing
    (M : SheafOfModules.{max u v r z} (structureSheafRingULift.{u, v, r, z} hset)) (Z : C)
    (h : (((sheafRingULiftDown.{u, v, r, z, max u v r z} h𝒪 hset).obj M).over
      Z).HasGlobalPresentation) :
    (M.over Z).HasGlobalPresentation :=
  hasGlobalPresentation_sheafRingULiftUp.{max u v, v, r, z} (J := J.over Z)
    (𝒪 := (Over.forget Z).op ⋙ 𝒪) (Sheaf.over (⟨_, h𝒪⟩ : Sheaf J RingCat.{r}) Z).property
    (Sheaf.over (⟨_, hset⟩ : Sheaf J (Type r)) Z).property _ h

end Stacks.Modules

namespace CategoryTheory.Functor

universe w v₀ u₀ r₁ r₂

/-- **Vanishing of a right derived functor of module-valued functors can be read on underlying
abelian groups**: if `E₁` and `E₂` agree after forgetting the module structures, then
`RⁿE₂(X) = 0` forces `RⁿE₁(X) = 0`. -/
theorem isZero_rightDerived_of_iso_comp_forget₂_spacesEtaleAffineVanishing {A : Type u₀}
    [Category.{v₀} A] [Abelian A] [HasInjectiveResolutions A] {R₁ : Type r₁} {R₂ : Type r₂}
    [Ring R₁] [Ring R₂]
    (E₁ : A ⥤ ModuleCat.{w} R₁) (E₂ : A ⥤ ModuleCat.{w} R₂) [E₁.Additive] [E₂.Additive]
    (e : E₁ ⋙ forget₂ (ModuleCat.{w} R₁) AddCommGrpCat.{w} ≅
      E₂ ⋙ forget₂ (ModuleCat.{w} R₂) AddCommGrpCat.{w})
    (n : ℕ) (X : A) (h : IsZero ((E₂.rightDerived n).obj X)) :
    IsZero ((E₁.rightDerived n).obj X) := by
  obtain ⟨e₁⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology E₁
    (forget₂ (ModuleCat.{w} R₁) AddCommGrpCat.{w}) n X
  obtain ⟨e₂⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology E₂
    (forget₂ (ModuleCat.{w} R₂) AddCommGrpCat.{w}) n X
  have h₁ :
      IsZero ((forget₂ (ModuleCat.{w} R₁) AddCommGrpCat.{w}).obj ((E₁.rightDerived n).obj X)) :=
    ((forget₂ (ModuleCat.{w} R₂) AddCommGrpCat.{w}).map_isZero h).of_iso
      (e₁ ≪≫ (Functor.rightDerivedIsoOfIso e n).app X ≪≫ e₂.symm)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.subsingleton_of_isZero h₁

end CategoryTheory.Functor

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

/-- **An object of `X_{spaces,étale}` represented by an affine scheme maps to the image of an
affine étale chart** under the comparison functor of Stacks 03G1. -/
theorem exists_hom_comparisonFunctor_obj_of_isAffineScheme_spacesEtaleAffineVanishing
    (V : SpacesEtale B S hS X) (hV : IsAffineScheme B S hS X V) :
    ∃ A : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 A ∧
      Nonempty (V ⟶ (comparisonFunctor B S hS X).obj A) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hV
  have he : IsEtale B S hS e.hom.hom := by
    have h := isEtale_comp_iso B S hS (𝟙 (yoneda.obj W))
      ((ObjectProperty.ι _).mapIso e) (isEtale_id B S hS _)
    rwa [Category.id_comp] at h
  have hA : IsEtaleChart B S hS X.1 (CostructuredArrow.mk (e.hom.hom ≫ V.obj.hom.hom)) :=
    V.property W e.hom.hom ((isEtale_iff_presheaf_of_yoneda B S hS _).mp he)
  refine ⟨⟨CostructuredArrow.mk (e.hom.hom ≫ V.obj.hom.hom), hA⟩, hW, ⟨?_⟩⟩
  refine ObjectProperty.homMk (Over.homMk e.inv ?_)
  apply ObjectProperty.hom_ext
  show e.inv.hom ≫ e.hom.hom ≫ V.obj.hom.hom = V.obj.hom.hom
  rw [← Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
  rfl

end SpacesEtale

/-- **A quasi-coherent module on `X_{spaces,étale}` is globally presented over every object
represented by an affine scheme.** -/
theorem hasGlobalPresentation_over_of_isAffineScheme_spacesEtaleAffineVanishing
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O))
    [hF : F.IsQuasicoherentOnSite] (V : SpacesEtale B S hS X)
    (hV : SpacesEtale.IsAffineScheme B S hS X V) :
    (F.over V).HasGlobalPresentation := by
  obtain ⟨A, hA, ⟨g⟩⟩ :=
    SpacesEtale.exists_hom_comparisonFunctor_obj_of_isAffineScheme_spacesEtaleAffineVanishing
      B S hS X V hV
  refine SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} F g ?_
  rw [hasGlobalPresentation_over_comparisonFunctor_obj_iff_spacesEtaleQuasicoherentWeakSerre]
  have hq :=
    (isQuasicoherentOnSite_iff_spacesEtaleToSmallEtaleModules_obj_spacesEtaleQuasicoherentWeakSerre
      B S hS X F).mp hF
  have hgp := hasGlobalPresentation_over_of_isCartesianOnAffineCharts.{0, u} B S hS X.1 X.2 _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse B S hS X.1 X.2 _ hq) A hA
  exact Stacks.Modules.hasGlobalPresentation_over_of_sheafRingULiftDown_spacesEtaleAffineVanishing.{
    u + 1, u, u, 0}
    (isSheaf_structureRingPresheaf_smallEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre B S hS X)
    (isSheaf_structureRingPresheaf_forget B S hS X.1 X.2) _ A hgp

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigFppfSpaceSite

open Opposite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (X : T.Spaces)

/-- Sheaves of modules on `X_{spaces,étale}` form an abelian category. -/
noncomputable local instance abelian_spacesEtaleModules_spacesEtaleAffineVanishing :
    Abelian (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)) :=
  inferInstance

/-- Sheaves of modules on `(Spaces/X)_fppf` form an abelian category. -/
noncomputable local instance abelian_bigFppfModules_spacesEtaleAffineVanishing :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O)) :=
  inferInstance

/-- Sheaves of modules on `X_{spaces,étale}` have enough injectives. -/
local instance enoughInjectives_spacesEtaleModules_spacesEtaleAffineVanishing :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- Abelian sheaves on `X_{spaces,étale}` have enough injectives. -/
local instance enoughInjectives_spacesEtaleSheaf_spacesEtaleAffineVanishing :
    EnoughInjectives (Sheaf (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X)
      AddCommGrpCat.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- Sheaves of modules on `(Spaces/X)_fppf` have enough injectives. -/
local instance enoughInjectives_bigFppfRingedToposModules_spacesEtaleAffineVanishing :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- Abelian sheaves on the spaces-étale site of `X` have `Ext` groups in the universe of its
morphisms. -/
local instance hasExt_spacesEtaleSheaf_spacesEtaleAffineVanishing :
    HasExt.{u + 1} (Sheaf (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X)
      AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _

/-- Sheaves of modules on the spaces-étale site of `X` have `Ext` groups in the universe of its
morphisms. -/
local instance hasExt_spacesEtaleModules_spacesEtaleAffineVanishing :
    HasExt.{u + 1} (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)) :=
  Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _

/-- **The direct image along `a_X : (Spaces/X)_fppf ⟶ X_{spaces,étale}` of an injective module
has no higher cohomology over any object of `X_{spaces,étale}`.** -/
theorem isZero_rightDerived_evaluation_pushforward_of_injective_spacesEtaleAffineVanishing
    (Z : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfRingedSite T X)).O)) [Injective Z]
    (V : Space.SpacesEtale T.schemeSite S T.scheme_mem X) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O) (op V)).rightDerived n).obj
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.obj Z)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine
    Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
      _ _ _ m _ (?_ : IsZero (Sheaf.H'.{u + 1} _ _ _))
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  have h := Stacks.CechSite.injective_module_subsingleton_ext_of_continuous.{u + 1, 0, u + 1, u + 1,
    u + 1, u + 1, u + 1}
    (bigFppfRingedSite T X) (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X)
    (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X) Z V (m + 1) (Nat.succ_pos m)
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((presheafToSheaf _ _).mapIso (Functor.isoWhiskerRight
      (uliftYonedaIsoYoneda.{u + 1, u + 1}.app V) AddCommGrpCat.free)) (m + 1) h

/-- **Stacks 03DW/01XB on `X_{spaces,étale}`: a quasi-coherent module has no higher cohomology
over an object represented by an affine scheme.** -/
theorem isZero_rightDerived_evaluation_of_isAffineScheme_spacesEtaleAffineVanishing
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [F.IsQuasicoherentOnSite] (V : Space.SpacesEtale T.schemeSite S T.scheme_mem X)
    (hV : Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X V) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O) (op V)).rightDerived
        n).obj F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := RingedToposSiteHom.pushforwardTopos_additive.{u + 1}
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
  have :
      (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.IsRightAdjoint :=
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos
      (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom).isRightAdjoint
  have := isIso_unit_app_of_isQuasicoherentOnSite F
  have hgp := hasGlobalPresentation_over_pullback F V
    (Space.hasGlobalPresentation_over_of_isAffineScheme_spacesEtaleAffineVanishing T.schemeSite S
      T.scheme_mem X F V hV)
  have hfppf : IsZero (((SheafOfModules.evaluation (bigFppfRingSheaf T X)
      (op ((Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj V))).rightDerived
        (m + 1)).obj
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F)) :=
    Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
      _ _ _ m _ (@isZero_H'_of_hasGlobalPresentation _ _ _ _ _ hV hgp (m + 1) (Nat.succ_pos m))
  have hcomp := Stacks.RightDerivedComp.objIsoOfAcyclicImage
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O) (op V))
    (isZero_rightDerived_pushforward_pullback F)
    (fun Z _ ↦
      isZero_rightDerived_evaluation_pushforward_of_injective_spacesEtaleAffineVanishing T X Z V)
    (m + 1)
  refine (Functor.isZero_rightDerived_of_iso_comp_forget₂_spacesEtaleAffineVanishing _ _
    (Iso.refl _) (m + 1) _ hfppf).of_iso
    ((((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O) (op V)).rightDerived
        (m + 1)).mapIso
        (asIso ((RingedToposSiteHom.pullbackPushforwardAdjunctionTopos
          (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom).unit.app F))) ≪≫ hcomp.symm)

/-- **Every object of `X_{spaces,étale}` has a covering family by objects represented by affine
schemes.** -/
theorem exists_preZeroHypercover_isAffineScheme_spacesEtaleAffineVanishing
    (V : Space.SpacesEtale T.schemeSite S T.scheme_mem X) :
    ∃ 𝒰 : PreZeroHypercover.{u + 1} V,
      𝒰.sieve₀ ∈ Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X V ∧
        ∀ i, Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X (𝒰.X i) := by
  obtain ⟨E, hcovE, hE⟩ :=
    Space.SpacesEtale.exists_isCovering_isAffineScheme_spacesAffineCovering T.schemeSite S
      T.scheme_mem X V
  exact ⟨E, Precoverage.generate_mem_toGrothendieck (R := E.presieve₀) ⟨E, rfl, hcovE⟩, hE⟩

/-- **The Olsson--Laszlo vanishing on `X_{spaces,étale}`** (Stacks 0D6R with `B` the objects
represented by affine schemes and `d_V = 0`): `Hᵖ(V, 𝓕) = 0` for `p > 0`, `V` represented by an
affine scheme and `𝓕` quasi-coherent. -/
theorem isZero_moduleCohomology_of_isAffineScheme_spacesEtaleAffineVanishing
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    (hF : F.IsQuasicoherentOnSite) (V : Space.SpacesEtale T.schemeSite S T.scheme_mem X)
    (hV : Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X V) (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.Cohomology.moduleCohomology.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O) V p F) :=
  isZero_rightDerived_evaluation_of_isAffineScheme_spacesEtaleAffineVanishing T X F V hV p hp

end AlgebraicGeometry.BigFppfSpaceSite

end
