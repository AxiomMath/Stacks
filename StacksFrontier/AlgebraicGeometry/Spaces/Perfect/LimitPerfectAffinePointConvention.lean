module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffinePointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.BaseChangeLimitsConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimitSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationBaseChangeSpace

/-!
# The affine case of Stacks 09RJ under the convention of Stacks 07SD

In Situation 09RH the chapter's standing convention (Section 70.2, tag 07SD) says that the limits
the chapter forms from the system — the limits of the base changes, over a stage `X_i`, of the
later stages to an affine object of the site — lie in the site
(`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`). This file proves the two facts the
affine case of Stacks 09RJ draws from it, for the base change `X_i ×_{X₀} U` of the situation
along an affine point `u : h_U ⟶ X₀`
(`AlgebraicGeometry.Space.DescentSituation.affinePointSituation`):

* the limit `X ×_{X₀} U` is affine, the projection `X ⟶ X₀` being affine by Stacks 07SF, part (1);
* its ring of global functions is the filtered colimit of those of the `X_i ×_{X₀} U`, by
  Stacks 07SI for the structure sheaf;

and from them, as for the size bound of Stacks 07SF, the affine case of essential surjectivity:
every perfect object of `D(𝒪_{X ×_{X₀} U})` descends to some stage.  The convention passes to the
base changes of the situation used in the induction of Stacks 08GP.

The convention is implied by the size bound `#I < B.cutoff.ord.cof`
(`AlgebraicGeometry.Space.DescentSituation.siteContainsBaseChangeLimits_of_lt_cof`) and is
strictly weaker than it: the system of finitely generated subrings of a large ring satisfies it.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.affineLimitModel`: an affine object of the site
  representing `X ×_{X₀} U`.

## Main results

* `DescentSituation.isAffineHom_limitCone_π_of_siteContainsBaseChangeLimits`: under the
  convention, every projection from the limit to a stage is affine.
* `AlgebraicGeometry.Space.DescentSituation.siteContainsBaseChangeLimits_affinePointSituation` and
  `siteContainsBaseChangeLimits_stagesBaseChangeAlong`: the convention passes to base changes.
* `DescentSituation.exists_isPerfect_affinePointStage_of_siteContainsBaseChangeLimits`: the
  affine case of essential surjectivity for perfect objects.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Section 70.2 (Tag 07SD)](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Lemma 70.5.1 (Tag 07SF)](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-! ### The convention and its inheritance -/

/-- **The size bound of Stacks 07SF implies the convention of Stacks 07SD.** -/
theorem siteContainsBaseChangeLimits_of_lt_cof (hI : #I < B.cutoff.ord.cof) :
    SiteContainsBaseChangeLimits B S hS D.system :=
  have : Nonempty I := ⟨D.base⟩
  IsSiteSmall.siteContainsBaseChangeLimits B S hS D.system (IsSiteSmall.of_lt_cof_op hI)

/-- **Stacks 07SF, part (1), in a descent situation, under the convention of Stacks 07SD.** Every
projection from the limit to a stage is affine. -/
theorem isAffineHom_limitCone_π_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) (i : Iᵒᵖ) :
    IsAffineHom B S hS (D.limitCone.π.app i) := by
  have : Nonempty I := ⟨D.base⟩
  have : HasLimit D.system := ⟨⟨⟨_, D.isLimit⟩⟩⟩
  have hlim := isAffineHom_limitπ_of_siteContainsBaseChangeLimits B S hS D.system hconv
    (fun {_ _} f => D.transition_affine f) i
  have he : (D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)).hom ≫
      limit.π D.system i = D.limitCone.π.app i :=
    D.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit D.system) i
  rw [← he]
  exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _) hlim

/-- The convention passes to the stages at or beyond the chosen index. -/
theorem siteContainsBaseChangeLimits_stagesSystem
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    SiteContainsBaseChangeLimits B S hS (stagesSystem D) :=
  hconv.comp_subtypeGe D.base

/-- **The convention passes to the base change of Situation 09RH along a quasi-compact
quasi-separated algebraic space over its chosen stage.** -/
theorem siteContainsBaseChangeLimits_stagesBaseChangeAlong
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hTqc : IsQuasiCompactSpace B S hS T)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T)
    (t : T ⟶ (stagesSystem D).obj (op (baseStage D))) :
    SiteContainsBaseChangeLimits B S hS (D.stagesBaseChangeAlong hT hTqc hTqs t).system :=
  (D.siteContainsBaseChangeLimits_stagesSystem hconv).baseChangeOverSystem (stagesToBase D) t

section AffinePoint

variable {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  (u : yoneda.obj U ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hconv : SiteContainsBaseChangeLimits B S hS D.system)

include hconv in
/-- **The convention passes to the base change of Situation 09RH along an affine point.** -/
theorem siteContainsBaseChangeLimits_affinePointSituation :
    SiteContainsBaseChangeLimits B S hS (affinePointSituation D hU u).system :=
  (D.siteContainsBaseChangeLimits_stagesSystem hconv).baseChangeOverSystem (stagesToBase D) u

include hconv in
/-- The limit `X ×_{X₀} U` of the base change along an affine point is an affine algebraic space,
under the convention. -/
theorem isAffineSpace_affinePointSituation_limitCone_of_siteContainsBaseChangeLimits :
    IsAffineSpace B S hS (affinePointSituation D hU u).limitCone.pt :=
  IsAffineHom.isAffineSpace_source
    (IsAffineHom.of_isPullback (IsPullback.of_hasPullback _ u)
      (D.isAffineHom_limitCone_π_of_siteContainsBaseChangeLimits hconv (op D.base)))
    (isAffineSpace_yoneda B S hS U hU)

include hconv in
/-- **Stacks 07SI for the structure sheaf, on the base change along an affine point, under the
convention.** -/
theorem isGlobalFunctionsColimit_affinePointSituation_of_siteContainsBaseChangeLimits :
    (affinePointSituation D hU u).IsGlobalFunctionsColimit :=
  (affinePointSituation D hU u).isGlobalFunctionsColimit_of_siteContainsBaseChangeLimits
    (D.siteContainsBaseChangeLimits_affinePointSituation hU u hconv)

end AffinePoint

/-! ### The affine model of the base-changed limit -/

section Model

variable {D} {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  (u : yoneda.obj U ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hconv : SiteContainsBaseChangeLimits B S hS D.system)

/-- A chosen affine object of the site representing the base-changed limit `X ×_{X₀} U`. -/
def affineLimitModel : BigFppfOver B S hS :=
  (isAffineSpace_affinePointSituation_limitCone_of_siteContainsBaseChangeLimits D hU u hconv).choose

/-- The chosen model `AlgebraicGeometry.Space.DescentSituation.affineLimitModel` is affine. -/
instance isAffine_affineLimitModel :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineLimitModel hU u hconv)) :=
  (isAffineSpace_affinePointSituation_limitCone_of_siteContainsBaseChangeLimits D hU u
    hconv).choose_spec.1

/-- The chosen isomorphism of the base-changed limit with its affine model. -/
def affineLimitModelIso :
    (affinePointSituation D hU u).limitCone.pt ≅ yoneda.obj (affineLimitModel hU u hconv) :=
  (isAffineSpace_affinePointSituation_limitCone_of_siteContainsBaseChangeLimits D hU u
    hconv).choose_spec.2.some


/-- The projection from the affine model of the base-changed limit to the affine model of a
base-changed stage, read off the projection of the limit cone. -/
def affineLimitModelProj (i : D.Stages) : affineLimitModel hU u hconv ⟶ affineModel hU u i :=
  yoneda.preimage ((affineLimitModelIso hU u hconv).inv ≫
    (affinePointSituation D hU u).limitCone.π.app (op i) ≫ (affineModelIso hU u i).hom)

/-- The Yoneda image of the projection between affine models is the projection of the limit cone
read through the chosen isomorphisms with the affine models. -/
theorem yoneda_map_affineLimitModelProj (i : D.Stages) :
    yoneda.map (affineLimitModelProj hU u hconv i) = (affineLimitModelIso hU u hconv).inv ≫
      (affinePointSituation D hU u).limitCone.π.app (op i) ≫ (affineModelIso hU u i).hom :=
  yoneda.map_preimage _


/-- **The affine model of the base-changed limit, as the vertex of a cocone on the diagram of
the affine models of the base-changed stages.** -/
def affineLimitModelCocone : Cocone (affineModelDiagram hU u) where
  pt := op (affineLimitModel hU u hconv)
  ι :=
    { app := fun i => (affineLimitModelProj hU u hconv i).op
      naturality := fun {i j} h => by
        have key : affineLimitModelProj hU u hconv j ≫ affineModelMap hU u (leOfHom h) =
            affineLimitModelProj hU u hconv i := by
          refine yoneda.map_injective ?_
          rw [CategoryTheory.Functor.map_comp, yoneda_map_affineLimitModelProj,
            yoneda_map_affineModelMap, yoneda_map_affineLimitModelProj]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          rw [← Category.assoc ((affinePointSituation D hU u).limitCone.π.app (op j)),
            (affinePointSituation D hU u).limitCone.w (homOfLE (leOfHom h)).op]
        exact (congrArg Quiver.Hom.op key).trans (Category.comp_id _).symm }

/-- The vertex of `AlgebraicGeometry.Space.DescentSituation.affineLimitModelCocone` is the affine
model of the base-changed limit. -/
@[simp]
theorem affineLimitModelCocone_pt :
    (affineLimitModelCocone hU u hconv).pt = op (affineLimitModel hU u hconv) :=
  rfl

/-- The leg of `AlgebraicGeometry.Space.DescentSituation.affineLimitModelCocone` at a stage is the
projection `AlgebraicGeometry.Space.DescentSituation.affineLimitModelProj`. -/
@[simp]
theorem affineLimitModelCocone_ι_app (i : D.Stages) :
    (affineLimitModelCocone hU u hconv).ι.app i = (affineLimitModelProj hU u hconv i).op := rfl


/-- The isomorphism of the base-changed limit with its affine model, in the category of
algebraic spaces over the base. -/
def affineLimitModelSpaceIso :
    (affinePointSituation D hU u).limitSpace ≅
      (⟨yoneda.obj (affineLimitModel hU u hconv),
        isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.isoMk _ (affineLimitModelIso hU u hconv)


/-- The ring of global functions of the base-changed limit, identified with the ring of global
functions of its affine model. -/
def affineLimitModelSectionsEquiv :
    Γ((BigFppfOver.toScheme B S hS).obj (affineLimitModel hU u hconv), ⊤) ≃+*
      globalFunctions' B S hS (affinePointSituation D hU u).limitSpace.obj :=
  (globalFunctionsYonedaRingEquiv B S hS (affineLimitModel hU u hconv)).symm.trans
    (globalFunctionsMapEquiv B S hS (affineLimitModelSpaceIso hU u hconv))


/-- **The projection of the limit cone of the base-changed situation, read through the chosen
isomorphisms with the affine models**: the square
`X ×_{X₀} U ⟶ X_i ×_{X₀} U ⟶ h_{V_i}` versus `X ×_{X₀} U ⟶ h_{V_∞} ⟶ h_{V_i}` commutes.

This is `AlgebraicGeometry.Space.DescentSituation.yoneda_map_affineLimitModelProj` read in the
category of algebraic spaces over the base. -/
theorem projection_comp_affineModelSpaceIso_hom_affineLimitModel (i : D.Stages) :
    (affinePointSituation D hU u).projection i ≫ (affineModelSpaceIso hU u i).hom =
      (affineLimitModelSpaceIso hU u hconv).hom ≫
        representedSpaceMap B S hS (affineLimitModelProj hU u hconv i) :=
  ObjectProperty.hom_ext _
    (((congrArg (fun φ => (affineLimitModelIso hU u hconv).hom ≫ φ)
          (yoneda_map_affineLimitModelProj hU u hconv i)).trans
      ((affineLimitModelIso hU u hconv).hom_inv_id_assoc _)).symm)


/-- The identification of the global functions of the base-changed limit with those of its
affine model is pullback along the chosen isomorphism after the identification at the
representing object. -/
theorem affineLimitModelSectionsEquiv_apply
    (s : Γ((BigFppfOver.toScheme B S hS).obj (affineLimitModel hU u hconv), ⊤)) :
    affineLimitModelSectionsEquiv hU u hconv s =
      globalFunctionsMap B S hS (affineLimitModelSpaceIso hU u hconv).hom
        ((globalFunctionsYonedaRingEquiv B S hS (affineLimitModel hU u hconv)).symm s) := rfl


/-- **The identification of global functions with those of the affine models intertwines the
maps to the limit**: the ring map of a projection of the affine models becomes pullback along the
corresponding projection of the limit cone of the base-changed situation. -/
theorem affineLimitModelSectionsEquiv_sections_map (i : D.Stages)
    (s : Γ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i), ⊤)) :
    affineLimitModelSectionsEquiv hU u hconv
        (((BigFppfOver.toScheme B S hS).map (affineLimitModelProj hU u hconv i)).appTop.hom s) =
      globalFunctionsMap B S hS ((affinePointSituation D hU u).projection i)
        (affineModelSectionsEquiv hU u i s) := by
  rw [affineLimitModelSectionsEquiv_apply, affineModelSectionsEquiv_apply,
    ← globalFunctionsMap_globalFunctionsYonedaRingEquiv_symm,
    globalFunctionsMap_globalFunctionsMap, globalFunctionsMap_globalFunctionsMap,
    projection_comp_affineModelSpaceIso_hom_affineLimitModel]


/-- **The ring of global functions of the affine model of the base-changed limit is the filtered
colimit of the rings of global functions of the affine models of the base-changed stages**,
elementwise.

This is Stacks 07SI for the structure sheaf on the base-changed situation,
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit_affinePointSituation`,
transferred across `AlgebraicGeometry.Space.DescentSituation.affineModelSectionsEquiv` and
`affineLimitModelSectionsEquiv` by `Stacks.IsStagesColimit.ofEquiv`. -/
theorem isStagesColimit_affineLimitModelSections :
    Stacks.IsStagesColimit
      (fun (i j : D.Stages) (h : i ≤ j)
          (s : Γ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i), ⊤)) =>
        ((BigFppfOver.toScheme B S hS).map (affineModelMap hU u h)).appTop.hom s)
      (fun (i : D.Stages) s =>
        ((BigFppfOver.toScheme B S hS).map (affineLimitModelProj hU u hconv i)).appTop.hom s) :=
  Stacks.IsStagesColimit.ofEquiv _ _
    (fun i => (affineModelSectionsEquiv hU u i).toEquiv)
    (affineLimitModelSectionsEquiv hU u hconv).toEquiv
    (fun _ _ h s => affineModelSectionsEquiv_sections_map hU u h s)
    (fun i s => affineLimitModelSectionsEquiv_sections_map hU u hconv i s)
    (isGlobalFunctionsColimit_affinePointSituation_of_siteContainsBaseChangeLimits D hU u hconv)


/-- **The hypothesis `hc` of the affine case, discharged for the cocone of affine models**: the
cocone of rings of global functions over the diagram of affine models of the base-changed stages,
with the ring of the affine model of the base-changed limit as its vertex, is a colimit cocone.

This is `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_affineLimitModelSections` —
Stacks 07SI for the structure sheaf, read on the affine models — turned from its elementwise form
into the categorical one by `Stacks.isColimit_commRingCat_of_elementwise`. -/
def isColimit_mapCocone_affineLimitModelCocone :
    IsColimit ((bigFppfSectionsRing B S hS).mapCocone (affineLimitModelCocone hU u hconv)) := by
  refine Stacks.isColimit_commRingCat_of_elementwise _ _ ?_ ?_
  · exact fun t => (isStagesColimit_affineLimitModelSections hU u hconv).exists_stage t
  · intro i x y hxy
    obtain ⟨j, h, hj⟩ :=
      (isStagesColimit_affineLimitModelSections hU u hconv).exists_trans_eq i x y hxy
    exact ⟨j, homOfLE h, hj⟩


section AffineBase

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- **The affine case of the essential surjectivity half of Stacks 09RJ, on the affine models,
under the convention of Stacks 07SD.**  Every perfect object of `D(𝒪_{h_{V_∞}})` is, at some stage
`j`, the derived pullback along `h_{V_∞} ⟶ h_{V_j}` of a perfect object of `D(𝒪_{h_{V_j}})`. -/
theorem exists_isPerfect_affineLimitModelStage
    (E : @DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (affineLimitModel hU u hconv))
      (isAlgebraicSpace_yoneda B S hS (affineLimitModel hU u hconv)))
        _ _ (HasDerivedCategory.standard _))
    (hE : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
          (yoneda.obj (affineLimitModel hU u hconv))
      (isAlgebraicSpace_yoneda B S hS (affineLimitModel hU u hconv)))
      (smallEtaleRingedSite B S hS (yoneda.obj (affineLimitModel hU u hconv))
      (isAlgebraicSpace_yoneda B S hS (affineLimitModel hU u hconv))).IsPerfect E) :
    ∃ (j : D.Stages) (Ej : @DerivedCategory (Modules.{u, u} B S hS
        (yoneda.obj (affineModel hU u j))
        (isAlgebraicSpace_yoneda B S hS (affineModel hU u j))) _ _ (HasDerivedCategory.standard _)),
      letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (yoneda.obj (affineModel hU u j))
        (isAlgebraicSpace_yoneda B S hS (affineModel hU u j)))
      (smallEtaleRingedSite B S hS (yoneda.obj (affineModel hU u j))
          (isAlgebraicSpace_yoneda B S hS (affineModel hU u j))).IsPerfect Ej ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS
          (representedSpaceMap B S hS (affineLimitModelProj hU u hconv j))).obj Ej ≅ E) := by
  let := fun (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) =>
    HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  have : ∀ j : D.Stages, IsAffine ((BigFppfOver.toScheme B S hS).obj
      (unop ((affineModelDiagram hU u).obj j))) := fun j => isAffine_affineModel hU u j
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (unop (affineLimitModelCocone hU u hconv).pt)) := isAffine_affineLimitModel hU u hconv
  exact exists_isPerfect_representedAffineStage B S hS (affineModelDiagram hU u)
    (affineLimitModelCocone hU u hconv) (isColimit_mapCocone_affineLimitModelCocone hU u hconv) E hE


include hconv in
/-- **The affine case of the essential surjectivity half of Stacks 09RJ, under the convention of
Stacks 07SD.**  For an affine point `u : h_U ⟶ X₀` of the chosen stage, every perfect object of
`D(𝒪_{X ×_{X₀} U})` is, at some stage `j`, the derived pullback along the projection
`X ×_{X₀} U ⟶ X_j ×_{X₀} U` of a perfect object of `D(𝒪_{X_j ×_{X₀} U})`. -/
theorem exists_isPerfect_affinePointStage_of_siteContainsBaseChangeLimits
    (E : @DerivedCategory (Modules.{u, u} B S hS (affinePointSituation D hU u).limitSpace.obj
      (affinePointSituation D hU u).limitSpace.property) _ _ (HasDerivedCategory.standard _))
    (hE : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
          (affinePointSituation D hU u).limitSpace.obj
      (affinePointSituation D hU u).limitSpace.property)
      (smallEtaleRingedSite B S hS (affinePointSituation D hU u).limitSpace.obj
      (affinePointSituation D hU u).limitSpace.property).IsPerfect E) :
    ∃ (j : D.Stages) (Ej : @DerivedCategory (Modules.{u, u} B S hS
        ((affinePointSituation D hU u).stage j).obj
        ((affinePointSituation D hU u).stage j).property) _ _ (HasDerivedCategory.standard _)),
      letI := HasDerivedCategory.standard (Modules.{u, u} B S hS
        ((affinePointSituation D hU u).stage j).obj
        ((affinePointSituation D hU u).stage j).property)
      (smallEtaleRingedSite B S hS ((affinePointSituation D hU u).stage j).obj
          ((affinePointSituation D hU u).stage j).property).IsPerfect Ej ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS
          ((affinePointSituation D hU u).projection j)).obj Ej ≅ E) := by
  let := fun (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) =>
    HasDerivedCategory.standard (Modules.{u, u} B S hS X hX)
  obtain ⟨j, Ej, hEj, ⟨ι⟩⟩ := exists_isPerfect_affineLimitModelStage hU u hconv
    ((smallEtaleDerivedModulePullback B S hS (affineLimitModelSpaceIso hU u hconv).inv).obj E)
    (isPerfect_smallEtaleDerivedModulePullback (affineLimitModelSpaceIso hU u hconv).inv E hE)
  refine ⟨j, (smallEtaleDerivedModulePullback B S hS (affineModelSpaceIso hU u j).hom).obj Ej,
    isPerfect_smallEtaleDerivedModulePullback (affineModelSpaceIso hU u j).hom Ej hEj, ⟨?_⟩⟩
  exact (smallEtaleDerivedModulePullbackCompIso B S hS
        ((affinePointSituation D hU u).projection j) (affineModelSpaceIso hU u j).hom).app Ej ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS
        (projection_comp_affineModelSpaceIso_hom_affineLimitModel hU u hconv j)).app Ej ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS (affineLimitModelSpaceIso hU u hconv).hom
        (representedSpaceMap B S hS (affineLimitModelProj hU u hconv j))).symm.app Ej ≪≫
        (smallEtaleDerivedModulePullback B S hS
            (affineLimitModelSpaceIso hU u hconv).hom).mapIso ι ≪≫
          (smallEtaleDerivedModulePullbackHomInvIso B S hS
            (affineLimitModelSpaceIso hU u hconv)).app E

end AffineBase

end Model

end DescentSituation

end AlgebraicGeometry.Space

end
