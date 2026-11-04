module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportKInjective

/-!
# The derived counit at a K-injective complex

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)` by [Stacks, Tag 0A75], and `Ri_* ⊣ R ℰom(𝒪_Z, -)` on the
unbounded derived categories by [Stacks, Tag 0A76].

A K-injective complex `I` of `𝒪_X`-modules computes `R ℰom(𝒪_Z, -)`: the isomorphism
`derivedSheafHomExactSupportKInjectiveIso` identifies `R ℰom(𝒪_Z, -)(Q I)` with
`Q (ℰom(𝒪_Z, I))`.  This file records that under this identification the counit of the derived
adjunction of [Stacks, Tag 0A76] is nothing but the counit of the degreewise adjunction of
[Stacks, Tag 0A75]: the trace map of the derived adjunction at `Q I` is computed by the
degreewise evaluation maps, with no resolution in the way.

All names below live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main results

* `derivedSheafHomExactSupportKInjectiveIso_inv_comp_counit`: at a K-injective complex `I` the
  composite of `Ri_*` applied to the inverse of the K-injective comparison isomorphism with the
  counit of [Stacks, Tag 0A76] is the canonical identification
  `Ri_*(Q K) ≅ Q (i_* K)` followed by `Q` of the counit of [Stacks, Tag 0A75] applied
  degreewise.

## Implementation notes

The proof unfolds the inverse of `derivedSheafHomExactSupportKInjectiveIso` into its four
factors and processes them from the right: naturality of the derived counit absorbs the
identification `Qh (quotient I) ≅ Q I`, the description
`derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app` of the derived counit
replaces the derived-functor comparison map by the counit on homotopy categories, and
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` converts the resulting
homotopy-category identification of `Ri_*` into the cochain-level one.

Three coincidences make the remaining factors disappear.  The two components of
`Functor.mapHomotopyCategoryFactors` that occur are identity morphisms, because the functor
induced on the homotopy category is a `CategoryTheory.Quotient.lift`; the counit of
`Adjunction.mapHomotopyCategoryAdjunction` at a complex in the image of the quotient is the
class of the counit of `Adjunction.mapHomologicalComplexAdjunction`, because the former is a
`CategoryTheory.Quotient.natTransLift` of the latter; and the two identifications of the
localization functors on `D(𝒪_Z)` cancel.  Each of the first two holds by `rfl` followed by one
application of `Functor.map_id`, but the morphism it rewrites has a source and a target that
agree only definitionally.  The three composite steps are therefore isolated as private lemmas,
whose statements fix one spelling of the objects involved, and `Functor.comp_obj` brings the
spellings in the main goal into that same form before the rewrites are applied.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The component of `Functor.mapHomotopyCategoryFactors` is an identity morphism after `Qh`,
since the functor induced on the homotopy category is a `CategoryTheory.Quotient.lift`. -/
private theorem qh_map_mapHomotopyCategoryFactors_inv_app
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    (F : V ⥤ W) [F.Additive] (K : CochainComplex V ℤ) :
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) =
      𝟙 _ := CategoryTheory.Functor.map_id _ _

/-- The component of `Functor.mapHomotopyCategoryFactors` for sheaf Hom with exact support,
followed by the derived-functor comparison map and by the counit of the derived adjunction of
[Stacks, Tag 0A76], is the homotopy-category factorisation of `Ri_*` followed by the counit of
the adjunction of [Stacks, Tag 0A75] on homotopy categories. -/
private theorem qh_mapHomotopyCategoryFactors_comp_comparison_comp_counit
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (modulePushforward S.i).mapDerivedCategory.map
          (DerivedCategory.Qh.map
            ((S.sheafHomExactSupport.mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).inv.app I)) ≫
        (modulePushforward S.i).mapDerivedCategory.map
            (S.derivedSheafHomExactSupportComparison.app
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
                (ComplexShape.up ℤ)).obj I)) ≫
          S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
            (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
                (ComplexShape.up ℤ)).obj I)) =
      (modulePushforward S.i).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.Z))
            (ComplexShape.up ℤ)).obj
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
                (ComplexShape.up ℤ)).obj I)) := by
  rw [qh_map_mapHomotopyCategoryFactors_inv_app]
  erw [CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans
    (S.derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app _)

/-- The component of `Functor.mapHomotopyCategoryFactors` for pushforward, followed by the
counit of the adjunction of [Stacks, Tag 0A75] on homotopy categories and by the identification
of the two localization functors, is that identification followed by the image under `Q` of the
counit on cochain complexes. -/
private theorem qh_mapHomotopyCategoryFactors_comp_counit_comp_quotientCompQhIso
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    DerivedCategory.Qh.map
          (((modulePushforward S.i).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        DerivedCategory.Qh.map
            ((Adjunction.mapHomotopyCategoryAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app
                ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
                  (ComplexShape.up ℤ)).obj I)) ≫
          (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I =
      (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing S.X))).hom.app
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app
              I) := by
  rw [qh_map_mapHomotopyCategoryFactors_inv_app]
  exact (Category.id_comp _).trans
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing S.X))).hom.naturality _)

/-- Derived pushforward of the identification of the two localization functors cancels against
derived pushforward of its inverse. -/
private theorem mapDerivedCategory_map_quotientCompQhIso_inv_comp_hom
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (modulePushforward S.i).mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing S.Z))).inv.app
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        (modulePushforward S.i).mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing S.Z))).hom.app
              ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) =
      𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
  exact CategoryTheory.Functor.map_id _ _

/-- **[Stacks, Tag 0A76].** At a K-injective complex `I` of `𝒪_X`-modules the counit of the
derived adjunction `Ri_* ⊣ R ℰom(𝒪_Z, -)` is the degreewise counit of the adjunction
`i_* ⊣ ℰom(𝒪_Z, -)` of [Stacks, Tag 0A75]: composing `Ri_*` applied to the inverse of the
isomorphism `R ℰom(𝒪_Z, -)(Q I) ≅ Q (ℰom(𝒪_Z, I))` with the derived counit gives the canonical
identification `Ri_*(Q K) ≅ Q (i_* K)` followed by the image under `Q` of the counit on cochain
complexes. -/
theorem derivedSheafHomExactSupportKInjectiveIso_inv_comp_counit
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupportKInjectiveIso I).inv ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (DerivedCategory.Q.obj I) =
      (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app
              I) := by
  have hcomparison := S.qh_mapHomotopyCategoryFactors_comp_comparison_comp_counit I
  have htail := S.qh_mapHomotopyCategoryFactors_comp_counit_comp_quotientCompQhIso I
  have hloc := S.mapDerivedCategory_map_quotientCompQhIso_inv_comp_hom I
  -- Naturality of the derived counit along `Qh (quotient I) ⟶ Q I`.
  have hcounit : (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupport.map
            ((DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I)) ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (DerivedCategory.Q.obj I) =
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
              (ComplexShape.up ℤ)).obj I)) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I :=
    S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.naturality _
  -- The homotopy-category factorisation of `Ri_*` at the class of `ℰom(𝒪_Z, I)`.
  have hfh := (modulePushforward S.i).mapDerivedCategoryFactorsh_hom_app
    ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  -- Bring every spelling of the objects involved into the same normal form, so that the
  -- rewrites below match.
  dsimp only [CategoryTheory.Functor.comp_obj] at hcomparison htail hloc hcounit
  rw [S.derivedSheafHomExactSupportKInjectiveIso_inv I]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  dsimp only [CategoryTheory.Functor.comp_obj]
  simp only [hcounit]
  simp only [reassoc_of% hcomparison]
  simp only [hfh, Category.assoc, htail, Iso.inv_hom_id_app_assoc, reassoc_of% hloc]

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
