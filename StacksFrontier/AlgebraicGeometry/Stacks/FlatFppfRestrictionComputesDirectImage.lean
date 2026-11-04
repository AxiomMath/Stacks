module

public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothRepresentedCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedLowerShriekUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CocontinuousPushforwardCorepresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedLowerShriekOnAcyclicSheaf
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Restricted K-injective complexes compute the direct image along the flat-fppf sites

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks and `f'` its restriction to the flat-fppf
sites (**Stacks 07AT** (2)). This is the flat-fppf twin of
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleRestrictionComputesDirectImage.lean`.
Restriction `(g')⁻¹` of abelian sheaves from the fppf to the flat-fppf site of `𝒳` does *not*
preserve K-injective complexes in general (that would need `g'_!` to be exact). This file proves
what Stacks 07AV needs instead: for every K-injective complex `I` of abelian sheaves on
`𝒳_{fppf}`, the restriction `(g')⁻¹ I` computes the total right derived direct image `Rf'_*`.

Sections over a flat object `y` of `𝒴` of `f'_*` are corepresented by the free abelian sheaf
`ℤ[(g')⁻¹ h_y]` on the restriction of the presheaf `h_y : x ↦ Hom_𝒴(f(x), y)`
(`Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorepRepresentation`). That presheaf
is represented by the 2-fibre product `𝒳 ×_𝒴 (Sch/V)`, flat over `𝒳`
(`AlgebraicGeometry.Stack.FlatFppf.flatRepresented_homPresheaf`), so by the Čech dévissage of
Stacks 07AK

`Ext^q(ℤ[(g')⁻¹ h_y], (g')⁻¹ E) = 0` for `q ≥ 1` and `E` injective on `𝒳_{fppf}`.

That makes the comparison `Lg'_!(ℤ[(g')⁻¹ h_y]) ⟶ g'_!(ℤ[(g')⁻¹ h_y])` an isomorphism, so the
derived adjunction `Lg'_! ⊣ (g')⁻¹` of Stacks 07AS (3) identifies morphisms out of
`ℤ[(g')⁻¹ h_y]` into the shifts of `(g')⁻¹ I` in the homotopy category with those in the derived
category (`Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_single_restriction`), which is
the corepresentable criterion for `(g')⁻¹ I` to compute `Rf'_*`
(`Stacks.Cohomology.CocontinuousPushforwardCorep.isIso_rightDerivedUnit_of_qh_bijective`).

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.ext_pushforwardCorep_restriction_eq_zero`: the vanishing of
  the higher `Ext` above.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_derivedPushforwardUnit_restriction`: `(g')⁻¹ I`
  computes `Rf'_*` for every K-injective `I`.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent CategoryTheory.Abelian

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

/-- The sheaf on the flat-fppf site of `𝒳` corepresenting the sections over `y` of the direct
image along the restriction `f'` of `f`: the free abelian sheaf on the presheaf
`x' ↦ Hom_{𝒴'}(f'(x'), y)`. -/
abbrev directImageCorep (y : FlatFppf B S hS 𝒴) :
    Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorep.{u}
    (inclusionTopology B S hS 𝒳)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)) y

/-- `directImageCorep` is the free abelian sheaf on the restriction to the flat-fppf site of the
presheaf `x ↦ Hom_𝒴(f(x), y)` on `𝒳`. -/
def directImageCorepIso (y : FlatFppf B S hS 𝒴) :
    directImageCorep B S hS f hf y ≅
      (Presheaf.freeAbelianSheaf.{u + 1} (inclusionTopology B S hS 𝒳)).obj
        ((objectProperty B S hS 𝒳).ι.op ⋙
          (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj)) :=
  (Presheaf.freeAbelianSheaf.{u + 1} (inclusionTopology B S hS 𝒳)).mapIso
    (Functor.isoWhiskerLeft
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf)).op
      (uliftYonedaRestrictIso (u := (objectProperty B S hS 𝒴).ι) y).symm)

/-- **Stacks 07AK at the 2-fibre product `V ×_{y, 𝒴} 𝒳`, as a vanishing of `Ext`.** For a flat
object `y` of `𝒴`, an injective abelian sheaf `E` on the fppf site of `𝒳` and `n : ℕ`,

`Ext^{n+1}(ℤ[(g')⁻¹ h_y], (g')⁻¹ E) = 0`.

This is `Stacks.Sites.CoverDescent.ext_restriction_eq_zero_of_mem` for the class
`AlgebraicGeometry.Stack.FlatRepresentedUpToIso`, closed under representable covers by
`AlgebraicGeometry.Stack.FlatFppf.isClosedUnderRepresentableCovers_flatRepresented`, at its
member `h_y` (`AlgebraicGeometry.Stack.FlatFppf.flatRepresented_homPresheaf`), with the
object-level vanishing **Stacks 0D6X** (`AlgebraicGeometry.Stack.FlatFppf.objectAcyclic`). -/
theorem ext_pushforwardCorep_restriction_eq_zero (y : FlatFppf B S hS 𝒴)
    (E : Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AddCommGrpCat.{u + 1})
    (hE : Injective E) (n : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    ∀ a : Ext (directImageCorep B S hS f hf y)
      ((subsiteRestriction B S hS 𝒳.val.val.p B.topology
        (flatObject B S hS 𝒳.val)).obj E) (n + 1), a = 0 := by
  have hcl := FlatFppf.isClosedUnderSitePullback B S hS 𝒳
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := isCocontinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (objectProperty B S hS 𝒳) .fppf 𝒳.val.isFiberedInGroupoids hcl
  intro a
  refine Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_iso_first
    (directImageCorepIso B S hS f hf y) (n + 1) ?_ a
  have : Injective (C := Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      AddCommGrpCat.{u + 1}) E := hE
  exact ext_restriction_eq_zero_of_mem (isClosedUnderRepresentableCovers_flatRepresented 𝒳)
    (@fun I hI d m c => objectAcyclic B S hS 𝒳 I hI d m c)
    (flatRepresented_homPresheaf f y) E n

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Restricted K-injective complexes compute the derived direct image along the flat-fppf
sites.** Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, `Rf'_*` a total right
derived functor of the direct image along the restriction `f'` of `f` to the flat-fppf sites,
and `I` a K-injective complex of abelian sheaves on the fppf site of `𝒳`. Then the comparison
`f'_*((g')⁻¹ I) ⟶ Rf'_*((g')⁻¹ I)` is an isomorphism, where `(g')⁻¹` is restriction to the
flat-fppf site.

By `Stacks.Cohomology.CocontinuousPushforwardCorep.isIso_rightDerivedUnit_of_qh_bijective` it
suffices that, for every flat object `y` of `𝒴` and every `n`, homotopy classes out of the
sheaf `directImageCorep` corepresenting sections over `y` into `((g')⁻¹ I)[n]` be the morphisms
of the derived category; that is
`Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_single_restriction` at the K-injective
complex `I[n]`, whose hypothesis is
`AlgebraicGeometry.Stack.FlatFppf.ext_pushforwardCorep_restriction_eq_zero`. -/
theorem isIso_derivedPushforwardUnit_restriction
    (Rf' : DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology B S hS 𝒴) AddCommGrpCat.{u + 1}))
    (αf' : haveI := isCocontinuous_subsiteFunctor B S hS f hf
      haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
          (flatObject B S hS 𝒳.val)
          (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
        (inclusionTopology B S hS 𝒴)).Additive :=
        Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
      ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
          (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
        (inclusionTopology B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
    (hRf' : Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
      (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)))
    (I : CochainComplex (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
      AddCommGrpCat.{u + 1}) ℤ) (hI : I.IsKInjective) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    haveI := isCocontinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    IsIso (αf'.app (((subsiteRestriction B S hS 𝒳.val.val.p B.topology
      (flatObject B S hS 𝒳.val)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := isCocontinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := isCocontinuous_subsiteFunctor B S hS f hf
  have : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
    (inclusionTopology B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  have := abelianLowerShriek_hasPointwiseLeftDerivedFunctor B S hS 𝒳
  open Stacks.Cohomology in
  have := DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (abelianLowerShriekAcyclic B S hS 𝒳) DerivedCategory.Qh
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
  have := hRf'
  have := hI
  refine Stacks.Cohomology.CocontinuousPushforwardCorep.isIso_rightDerivedUnit_of_qh_bijective.{u}
    (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)) Rf' αf' _ (fun y n => ?_)
  have : (I⟦n⟧).IsKInjective := inferInstance
  have h := Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_single_restriction.{u + 1, u + 1}
    (inclusionTopology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (objectProperty B S hS 𝒳).ι (directImageCorep B S hS f hf y)
    (fun E hE m a => ext_pushforwardCorep_restriction_eq_zero B S hS f hf y E hE m a) (I⟦n⟧)
  refine Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((subsiteRestriction B S hS 𝒳.val.val.p B.topology
        (flatObject B S hS 𝒳.val)).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
          n).app I)) h

/-- **The lower shriek of the corepresenting sheaf is the free abelian sheaf on the Hom
presheaf**: `g'_!(ℤ[(g')⁻¹ h_y]) ≅ ℤ[h_y]`, by the degree-zero half of the Čech dévissage
(`Stacks.Sites.CoverDescent.isIso_freeComparison` at the member `h_y` of the class
`AlgebraicGeometry.Stack.FlatRepresentedUpToIso`). -/
def lowerShriekDirectImageCorepIso (y : FlatFppf B S hS 𝒴) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    haveI := isCocontinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    ((objectProperty B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
        (inclusionTopology B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p B.topology)).obj
        (directImageCorep B S hS f hf y) ≅
      (Presheaf.freeAbelianSheaf.{u + 1} (associatedTopology B S hS 𝒳.val.val.p
        B.topology)).obj (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj) :=
  haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  haveI := isCocontinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have hcl := FlatFppf.isClosedUnderSitePullback B S hS 𝒳
  haveI := isRightAdjoint_subsiteRestriction_of_isClosedUnderSitePullback hcl
  haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p (objectProperty B S hS 𝒳) .fppf 𝒳.val.isFiberedInGroupoids hcl
  have hiso := isIso_freeComparison.{u + 1, u, u + 1, u + 1}
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
    ((objectProperty B S hS 𝒳).ι.inheritedTopology
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf))
    (objectProperty B S hS 𝒳).ι (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj)
    (fun F hF => restrictHom_bijective_of_mem.{u + 1, u, u + 1, u + 1}
      ((objectProperty B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf))
      (isClosedUnderRepresentableCovers_flatRepresented 𝒳)
      (flatRepresented_homPresheaf f y) F hF)
  ((objectProperty B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
      (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology)).mapIso
      (directImageCorepIso B S hS f hf y) ≪≫
    @asIso _ _ _ _ (freeComparison (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      ((objectProperty B S hS 𝒳).ι.inheritedTopology
        (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf))
      (objectProperty B S hS 𝒳).ι
      (f.hom.hom.toFunctor.op ⋙ uliftYoneda.{u + 1}.obj y.obj)) hiso

/-- **Restricted complexes that compute `RHom` out of torsion-free sheaves compute `RHom` out of
the corepresenting sheaves of the direct image.** Let `Z` be a complex of abelian sheaves on the
fppf site of `𝒳` such that homotopy classes of morphisms out of every sectionwise torsion-free
abelian sheaf, placed in degree `0`, into every shift of `Z` are the morphisms of the derived
category (for instance a K-injective complex, or the underlying abelian complex of a K-injective
complex of modules, Stacks 0D6J). Then the same holds for morphisms out of the sheaf
`directImageCorep` corepresenting sections of `f'_*` into the shifts of the restriction of `Z`
to the flat-fppf site, for any topology `K'` on the flat-fppf site equal to the inherited one.

The lower shriek of `directImageCorep` is the free abelian sheaf on the Hom presheaf
(`lowerShriekDirectImageCorepIso`), which is sectionwise torsion-free, and the derived lower
shriek of `directImageCorep` is its lower shriek
(`Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekComparison_app_single`);
`Stacks.Cohomology.DerivedLowerShriek.map_bijective_of_adjunction_comparison` then moves the
bijectivity across the derived adjunction `Lg'_! ⊣ (g')⁻¹`. -/
theorem qh_map_bijective_directImageCorep_restriction
    (K' : GrothendieckTopology (FlatFppf B S hS 𝒳))
    (hK' : inclusionTopology B S hS 𝒳 = K') [HasSheafify K' AddCommGrpCat.{u + 1}]
    [(objectProperty B S hS 𝒳).ι.IsContinuous K'
      (associatedTopology B S hS 𝒳.val.val.p B.topology)]
    (y : FlatFppf B S hS 𝒴)
    (Z : CochainComplex (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
      AddCommGrpCat.{u + 1}) ℤ)
    (hZ : ∀ (A₀ : Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
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
                (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)) y)) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            K' (associatedTopology B S hS 𝒳.val.val.p B.topology)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Z⟦n⟧)) → _) := by
  subst hK'
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := isCocontinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have : ((objectProperty B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
      (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology)).PreservesZeroMorphisms :=
    Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek.{u + 1}
      (inclusionTopology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
  have := abelianLowerShriek_hasPointwiseLeftDerivedFunctor B S hS 𝒳
  open Stacks.Cohomology in
  have := DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (abelianLowerShriekAcyclic B S hS 𝒳) DerivedCategory.Qh
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
  open Stacks.Cohomology in
  have := DerivedLowerShriek.isIso_derivedAbelianLowerShriekComparison_app_single.{u + 1, u + 1}
    (inclusionTopology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (objectProperty B S hS 𝒳).ι (directImageCorep B S hS f hf y)
    (fun E hE m a => ext_pushforwardCorep_restriction_eq_zero B S hS f hf y E hE m a)
  have hQ : Function.Bijective (DerivedCategory.Qh.map :
      ((Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekOnHomotopy.{u + 1}
          (inclusionTopology B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p B.topology)
          (objectProperty B S hS 𝒳).ι).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj (directImageCorep B S hS f hf y))) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (Z⟦n⟧)) → _) := by
    refine DerivedCategory.qh_map_bijective_of_iso_source
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        (((HomologicalComplex.singleMapHomologicalComplex
          ((objectProperty B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u + 1}
            (inclusionTopology B S hS 𝒳)
            (associatedTopology B S hS 𝒳.val.val.p B.topology))
          (ComplexShape.up ℤ) 0).app (directImageCorep B S hS f hf y)) ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso
          (lowerShriekDirectImageCorepIso B S hS f hf y))) ?_
    have key : ∀ X : Type (u + 1), Module.IsTorsionFree ℤ (FreeAbelianGroup X) :=
      fun _ => Module.Flat.isTorsionFree
    exact hZ _ (fun V => ModuleSheafCohomology.isTorsionFree_sheafify _ _ (fun W => key _) V) n
  refine Stacks.Cohomology.DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (inclusionTopology B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p B.topology)).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n |>.app Z)) ?_
  exact Stacks.Cohomology.DerivedLowerShriek.map_bijective_of_adjunction_comparison
    (Stacks.Cohomology.DerivedLowerShriek.abelianHomotopyAdjunction.{u + 1}
      (inclusionTopology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (objectProperty B S hS 𝒳).ι)
    DerivedCategory.Qh DerivedCategory.Qh
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{u + 1}
      (inclusionTopology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (objectProperty B S hS 𝒳).ι)
    _ _ (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction_unit_fac.{u + 1}
      (inclusionTopology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (objectProperty B S hS 𝒳).ι) _ _ hQ

end Derived

end AlgebraicGeometry.Stack.FlatFppf
