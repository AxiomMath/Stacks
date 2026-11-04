module

public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothRepresentedCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CocontinuousPushforwardCorepresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedLowerShriekOnAcyclicSheaf
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Restricted K-injective complexes compute the direct image along the lisse-étale sites

Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks and `f'` its restriction to the
lisse-étale sites, and `(g')⁻¹` restriction of abelian sheaves from the étale to the lisse-étale
site of `𝒳`. For every K-injective complex `I` of abelian sheaves on `𝒳_{étale}`, the restriction
`(g')⁻¹ I` computes the total right derived direct image `Rf'_*`.

Sections of `f'_*` over a smooth object `y` of `𝒴` are corepresented by the free abelian sheaf
`ℤ[(g')⁻¹ h_y]` on the restriction of the presheaf `h_y : x ↦ Hom_𝒴(f(x), y)`, and

`Ext^q(ℤ[(g')⁻¹ h_y], (g')⁻¹ E) = 0` for `q ≥ 1` and `E` injective on `𝒳_{étale}`.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.directImageCorep`: the sheaf `ℤ[(g')⁻¹ h_y]`.
* `AlgebraicGeometry.Stack.LisseEtale.lowerShriekDirectImageCorepIso`:
  `g'_!(ℤ[(g')⁻¹ h_y]) ≅ ℤ[h_y]`.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.ext_pushforwardCorep_restriction_eq_zero`: the vanishing of
  the higher `Ext` above.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_derivedPushforwardUnit_restriction`: `(g')⁻¹ I`
  computes `Rf'_*` for every K-injective `I`.
* `AlgebraicGeometry.Stack.LisseEtale.qh_map_bijective_directImageCorep_restriction`: a complex
  `Z` on `𝒳_{étale}` computing `RHom` out of sectionwise torsion-free sheaves has restriction
  computing `RHom` out of `ℤ[(g')⁻¹ h_y]`.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent CategoryTheory.Abelian

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- The sheaf on the lisse-étale site of `𝒳` corepresenting the sections over `y` of the direct
image along the restriction `f'` of `f`: the free abelian sheaf on the presheaf
`x' ↦ Hom_{𝒴'}(f'(x'), y)`. -/
abbrev directImageCorep (y : LisseEtale.{u, w} B S hS 𝒴) :
    Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorep.{u}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)) y

/-- `directImageCorep` is the free abelian sheaf on the restriction to the lisse-étale site of the
presheaf `x ↦ Hom_𝒴(f(x), y)` on `𝒳`. -/
def directImageCorepIso (y : LisseEtale.{u, w} B S hS 𝒴) :
    directImageCorep B S hS f hf y ≅
      (Presheaf.freeAbelianSheaf.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)).obj
        ((smoothObject.{u, w} B S hS 𝒳).ι.op ⋙
          (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj)) :=
  (Presheaf.freeAbelianSheaf.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)).mapIso
    (Functor.isoWhiskerLeft
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (smoothObject_map.{u, w} B S hS f hf)).op
      (uliftYonedaRestrictIso (u := (smoothObject.{u, w} B S hS 𝒴).ι) y).symm)

/-- For a smooth object `y` of `𝒴`, an injective abelian sheaf `E` on the étale site of `𝒳` and
`n : ℕ`,

`Ext^{n+1}(ℤ[(g')⁻¹ h_y], (g')⁻¹ E) = 0`. -/
theorem ext_pushforwardCorep_restriction_eq_zero (y : LisseEtale.{u, w} B S hS 𝒴)
    (E : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u + 1})
    (hE : Injective E) (n : ℕ) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    ∀ a : Ext (directImageCorep B S hS f hf y)
      ((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)).obj E) (n + 1), a = 0 := by
  have hcl := isClosedUnderSitePullback_smoothObject 𝒳
  have := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (smoothObject.{u, w} B S hS 𝒳) .etale 𝒳.val.isFiberedInGroupoids hcl
  intro a
  refine Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_iso_first
    (directImageCorepIso B S hS f hf y) (n + 1) ?_ a
  have : Injective (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      AddCommGrpCat.{u + 1}) E := hE
  exact ext_restriction_eq_zero_of_mem (isClosedUnderRepresentableCovers_smoothRepresented 𝒳)
    (objectAcyclic.{u, w} B S hS 𝒳)
    (smoothRepresented_homPresheaf f y) E n

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks, `Rf'_*` a total right
derived functor of the direct image along the restriction `f'` of `f` to the lisse-étale sites,
and `I` a K-injective complex of abelian sheaves on the étale site of `𝒳`. Then the comparison
`f'_*((g')⁻¹ I) ⟶ Rf'_*((g')⁻¹ I)` is an isomorphism, where `(g')⁻¹` is restriction to the
lisse-étale site. -/
theorem isIso_derivedPushforwardUnit_restriction
    (Rf' : DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒴) AddCommGrpCat.{u + 1}))
    (αf' : haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
      haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
          (smoothObject.{u, w} B S hS 𝒳)
          (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (inclusionTopology.{u, w} B S hS 𝒴)).Additive :=
        Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
      ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
          (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (inclusionTopology.{u, w} B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
    (hRf' : Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
      (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)))
    (I : CochainComplex (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      AddCommGrpCat.{u + 1}) ℤ) (hI : I.IsKInjective) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    IsIso (αf'.app (((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  have := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  have := isLeftDerivedFunctor_derivedAbelianLowerShriek_comp.{u, w} B S hS 𝒳
  refine Stacks.Cohomology.CocontinuousPushforwardCorep.isIso_rightDerivedUnit_of_qh_bijective.{u}
    (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)) Rf' αf' _ (fun y n => ?_)
  have h := Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_single_restriction.{u + 1, u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι (directImageCorep B S hS f hf y)
    (ext_pushforwardCorep_restriction_eq_zero B S hS f hf y) (I⟦n⟧)
  refine Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
          n).app I)) h

/-- The lower shriek of the corepresenting sheaf `directImageCorep` is the free abelian sheaf on
the Hom presheaf: `g'_!(ℤ[(g')⁻¹ h_y]) ≅ ℤ[h_y]`. -/
def lowerShriekDirectImageCorepIso (y : LisseEtale.{u, w} B S hS 𝒴) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    ((smoothObject.{u, w} B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
        (inclusionTopology.{u, w} B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).obj
        (directImageCorep B S hS f hf y) ≅
      (Presheaf.freeAbelianSheaf.{u + 1} (associatedTopology B S hS 𝒳.val.val.p
        (etaleTopology B))).obj (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have hcl := isClosedUnderSitePullback_smoothObject 𝒳
  haveI := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (smoothObject.{u, w} B S hS 𝒳) .etale 𝒳.val.isFiberedInGroupoids hcl
  have hiso := isIso_freeComparison.{u + 1, u, u + 1, u + 1}
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
    ((smoothObject.{u, w} B S hS 𝒳).ι.inheritedTopology
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale))
    (smoothObject.{u, w} B S hS 𝒳).ι (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj)
    (fun F hF => restrictHom_bijective_of_mem.{u + 1, u, u + 1, u + 1}
      ((smoothObject.{u, w} B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale))
      (isClosedUnderRepresentableCovers_smoothRepresented 𝒳)
      (smoothRepresented_homPresheaf f y) F hF)
  ((smoothObject.{u, w} B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).mapIso
      (directImageCorepIso B S hS f hf y) ≪≫
    @asIso _ _ _ _ (freeComparison (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale)
      ((smoothObject.{u, w} B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale))
      (smoothObject.{u, w} B S hS 𝒳).ι
      (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj)) hiso

/-- Let `Z` be a complex of abelian sheaves on the
étale site of `𝒳` such that homotopy classes of morphisms out of every sectionwise torsion-free
abelian sheaf, placed in degree `0`, into every shift of `Z` are the morphisms of the derived
category. Then the same holds for morphisms out of the sheaf
`directImageCorep` corepresenting sections of `f'_*` into the shifts of the restriction of `Z`
to the lisse-étale site, for any topology `K'` on the lisse-étale site equal to the inherited one.
-/
theorem qh_map_bijective_directImageCorep_restriction
    (K' : GrothendieckTopology (LisseEtale.{u, w} B S hS 𝒳))
    (hK' : inclusionTopology.{u, w} B S hS 𝒳 = K') [HasSheafify K' AddCommGrpCat.{u + 1}]
    [(smoothObject.{u, w} B S hS 𝒳).ι.IsContinuous K'
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))]
    (y : LisseEtale.{u, w} B S hS 𝒴)
    (Z : CochainComplex (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      AddCommGrpCat.{u + 1}) ℤ)
    (hZ : ∀ (A₀ : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}), (∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V)) → ∀ m : ℤ,
      Function.Bijective (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor _ 0).obj A₀) ⟶
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (Z⟦m⟧)) → _))
    (n : ℤ) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj
            (Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorep.{u} K'
              (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
                (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf)) y)) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((((smoothObject.{u, w} B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            K' (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Z⟦n⟧)) → _) := by
  subst hK'
  have := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have : ((smoothObject.{u, w} B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).PreservesZeroMorphisms :=
    Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) (smoothObject.{u, w} B S hS 𝒳).ι
  have := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  have := isLeftDerivedFunctor_derivedAbelianLowerShriek_comp.{u, w} B S hS 𝒳
  have :=
    Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekComparison_app_single.{
      u + 1, u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι (directImageCorep B S hS f hf y)
      (ext_pushforwardCorep_restriction_eq_zero B S hS f hf y)
  have hQ : Function.Bijective (DerivedCategory.Qh.map :
      ((Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekOnHomotopy.{u + 1}
          (inclusionTopology.{u, w} B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          (smoothObject.{u, w} B S hS 𝒳).ι).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj (directImageCorep B S hS f hf y))) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (Z⟦n⟧)) → _) := by
    refine DerivedCategory.qh_map_bijective_of_iso_source
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        (((HomologicalComplex.singleMapHomologicalComplex
          ((smoothObject.{u, w} B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
            (inclusionTopology.{u, w} B S hS 𝒳)
            (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)))
          (ComplexShape.up ℤ) 0).app (directImageCorep B S hS f hf y)) ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso
          (lowerShriekDirectImageCorepIso B S hS f hf y))) ?_
    have key : ∀ X : Type (u + 1), Module.IsTorsionFree ℤ (FreeAbelianGroup X) :=
      fun _ => Module.Flat.isTorsionFree
    exact hZ _ (ModuleSheafCohomology.isTorsionFree_sheafify _ _ fun _ => key _) n
  refine Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((smoothObject.{u, w} B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (inclusionTopology.{u, w} B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n |>.app Z)) ?_
  exact Stacks.Cohomology.DerivedLowerShriek.map_bijective_of_adjunction_comparison
    (Stacks.Cohomology.DerivedLowerShriek.abelianHomotopyAdjunction.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι)
    DerivedCategory.Qh DerivedCategory.Qh
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι)
    _ _ (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction_unit_fac.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι) _ _ hQ

end Derived

end AlgebraicGeometry.Stack.LisseEtale
