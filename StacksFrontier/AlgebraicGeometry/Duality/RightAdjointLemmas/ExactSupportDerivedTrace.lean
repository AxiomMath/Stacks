module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportKInjective
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit

/-!
# The trace of Tag 0A76 at the class of a cochain complex

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)` ([Stacks, Tag 0A75]) and the derived functors are again
adjoint ([Stacks, Tag 0A76]).  The counit of the derived adjunction — the *trace*
`Ri_* R ℰom(𝒪_Z, K) ⟶ K` — is produced by a universal property, and
`…derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app` describes it only through
the factorization that Maltsiniotis' theorem gives: the trace *precomposed with* the derived
pushforward of the derived-functor comparison map, and with the counit on the right-hand side
being that of the adjunction induced on *homotopy categories*.

**This file replaces that homotopy-category counit by the degreewise underived trace of
[Stacks, Tag 0A75], and crosses the resulting statement from `DerivedCategory.Qh` to
`DerivedCategory.Q`.**  The induced adjunction on homotopy categories is a descent of the
degreewise one along the homotopy quotient, so at the class of a complex its counit is the class
of the degreewise counit
(`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction_counit_app_quotient`); substituting that
into the factorization gives the first description of the derived trace of
[Stacks, Tag 0A76] in terms of the underived trace of [Stacks, Tag 0A75].  Composing with the
naturality of the trace along `CategoryTheory.DerivedCategory.quotientCompQhIso` and with
`Stacks.DerivedCategoryComparisons`
`.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom` then puts it below
`DerivedCategory.Q`, which is where a consumer starting from a K-injective cochain complex works:
`…derivedSheafHomExactSupportCochainComparison` and `…derivedSheafHomExactSupportKInjectiveIso`
both live there.

## Main definitions

There are no new definitions.

## Main results

* `…derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_quotient`: the derived
  trace of [Stacks, Tag 0A76] at the class of a cochain complex, in terms of the degreewise
  underived trace of [Stacks, Tag 0A75], below `DerivedCategory.Qh`.
* `…derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q`: the same below
  `DerivedCategory.Q`, precomposed with the cochain-level derived-functor comparison map.
* `…derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q_of_isKInjective`:
  **the derived trace of [Stacks, Tag 0A76] at the class of a K-injective cochain complex,
  solved for**, as the isomorphism computing `R ℰom(𝒪_Z, -)` there followed by the degreewise
  underived trace of [Stacks, Tag 0A75].

## Implementation notes

`DerivedCategory.Qh` carries `no_expose`, so in this project `Qh.obj ((quotient _ _).obj I)` and
`Q.obj I` are two different objects and the crossing is genuine isomorphism algebra rather than a
change of spelling.  What *is* a change of spelling, and what makes the crossing awkward, is the
pair `(F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient _ c).obj K)` versus
`(HomotopyCategory.quotient _ c).obj ((F.mapHomologicalComplex c).obj K)`: those two objects agree
only by unfolding the `CategoryTheory.Quotient.lift` that defines
`CategoryTheory.Functor.mapHomotopyCategory`, which is semireducible, and the components of
`CategoryTheory.Functor.mapHomotopyCategoryFactors` are identities straddling them.  A composite
one of whose factors straddles the pair is type-correct at default transparency but not at
`implicit` transparency, so neither `rw` nor `simp only [Category.assoc]` can be applied to it —
Mathlib's own proof of `…mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app` turns the transparency
check off, which is forbidden here.  Every step of the two proofs below is therefore a term:
`Eq.trans` chains with hand-written `congrArg` motives, each elaborated at default transparency.
The first move is to drop the straddling identity factor from
`…derivedSheafHomExactSupportCochainComparison`
(`…derivedSheafHomExactSupportCochainComparison_app_eq`), which leaves exactly one straddle in the
whole computation, between the comparison map at `(quotient _ _).obj I` and the object `Q.obj I`.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.DerivedCategoryComparisons
  (mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **[Stacks, Tag 0A76].** The derived trace at the class of a cochain complex, in terms of the
degreewise underived trace of [Stacks, Tag 0A75].

This is `…derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app` at the class of a
cochain complex, with the counit of the adjunction induced on homotopy categories replaced by the
class of the degreewise counit of [Stacks, Tag 0A75] — which is what it is there, the induced
adjunction being a descent of the degreewise one along the homotopy quotient. -/
@[reassoc]
theorem derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_quotient
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
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
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
              (ComplexShape.up ℤ)).map
            ((Adjunction.mapHomologicalComplexAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction
                (ComplexShape.up ℤ)).counit.app I)) := by
  have h := S.derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app
    ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
      (ComplexShape.up ℤ)).obj I)
  rw [Adjunction.mapHomotopyCategoryAdjunction_counit_app_quotient] at h
  exact h

/-- The cochain-level derived-functor comparison map of sheaf Hom with exact support at a cochain
complex, with the identity factor dropped.

`…derivedSheafHomExactSupportCochainComparison_app` writes it as four factors, the second of which
is `DerivedCategory.Qh` applied to a component of
`CategoryTheory.Functor.mapHomotopyCategoryFactors` — an identity straddling the two
spellings `(quotient _ _).obj (ℰom(𝒪_Z, I))` and
`(ℰom(𝒪_Z, -).mapHomotopyCategory _).obj ((quotient _ _).obj I)` of one object.  Dropping it
is what makes the rest of the computation a composite with only one straddle in it. -/
theorem derivedSheafHomExactSupportCochainComparison_app_eq
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    S.derivedSheafHomExactSupportCochainComparison.app I =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).inv.app
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        S.derivedSheafHomExactSupportComparison.app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
              (ComplexShape.up ℤ)).obj I) ≫
          S.derivedSheafHomExactSupport.map
            ((DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I) := by
  refine (S.derivedSheafHomExactSupportCochainComparison_app I).trans ?_
  refine congrArg (fun t => (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing S.Z))).inv.app
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫ t) ?_
  exact (congrArg (fun t => t ≫ S.derivedSheafHomExactSupportComparison.app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
          (ComplexShape.up ℤ)).obj I) ≫
      S.derivedSheafHomExactSupport.map
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I))
    (DerivedCategory.Qh.map_id _)).trans (Category.id_comp _)

/-- The derived trace of [Stacks, Tag 0A76] read at `DerivedCategory.Q.obj I`, with the
homotopy-category comparison map of `…derivedModulePushforwardSheafHomExactSupportAdjunction`
`_counit_app_quotient` still in place.

This is the step that crosses from `DerivedCategory.Qh` to `DerivedCategory.Q`: naturality of the
trace along `DerivedCategory.quotientCompQhIso` moves the trace from `Qh.obj ((quotient _ _).obj
I)` to `Q.obj I`, the `Qh`-level factorization is substituted, and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom`
turns the `Qh`-level identification of `Ri_*` into the `Q`-level one. -/
private theorem derivedTrace_keyStep
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupportComparison.app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
              (ComplexShape.up ℤ)).obj I)) ≫
        (modulePushforward S.i).mapDerivedCategory.map
            (S.derivedSheafHomExactSupport.map
              ((DerivedCategory.quotientCompQhIso
                (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I)) ≫
          S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
            (DerivedCategory.Q.obj I) =
      (modulePushforward S.i).mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).hom.app
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((Adjunction.mapHomologicalComplexAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction
                (ComplexShape.up ℤ)).counit.app I) := by
  have hnat : (modulePushforward S.i).mapDerivedCategory.map
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
  refine (congrArg (fun t => (modulePushforward S.i).mapDerivedCategory.map
      (S.derivedSheafHomExactSupportComparison.app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
          (ComplexShape.up ℤ)).obj I)) ≫ t) hnat).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I)
    (S.derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_quotient I)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (modulePushforward S.i).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.Z))
        (ComplexShape.up ℤ)).obj
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫ t)
    (DerivedCategory.quotientCompQhIso_hom_naturality
      ((Adjunction.mapHomologicalComplexAdjunction
        S.modulePushforwardSheafHomExactSupportAdjunction
          (ComplexShape.up ℤ)).counit.app I))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ DerivedCategory.Q.map
      ((Adjunction.mapHomologicalComplexAdjunction
        S.modulePushforwardSheafHomExactSupportAdjunction
          (ComplexShape.up ℤ)).counit.app I))
    (mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom (modulePushforward S.i)
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))).trans ?_
  exact Category.assoc _ _ _

/-- **[Stacks, Tag 0A76].** The derived trace at the class of a cochain complex, below
`DerivedCategory.Q`: the cochain-level derived-functor comparison map of sheaf Hom with exact
support, pushed forward and followed by the trace, is the `Q`-level identification of `Ri_*`
followed by the class of the degreewise underived trace of [Stacks, Tag 0A75]. -/
@[reassoc]
theorem derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupportCochainComparison.app I) ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (DerivedCategory.Q.obj I) =
      (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Adjunction.mapHomologicalComplexAdjunction
            S.modulePushforwardSheafHomExactSupportAdjunction
              (ComplexShape.up ℤ)).counit.app I) := by
  rw [S.derivedSheafHomExactSupportCochainComparison_app_eq I,
    CategoryTheory.Functor.map_comp]
  refine (congrArg (fun t => (_ ≫ t) ≫ _) (CategoryTheory.Functor.map_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (S.derivedTrace_keyStep I))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
    (congrArg _ (Iso.inv_hom_id_app _ _)))).trans ?_
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **[Stacks, Tag 0A76], the derived trace at a K-injective class, solved for.**  At the class
of a K-injective cochain complex `I` the trace `Ri_* R ℰom(𝒪_Z, Q I) ⟶ Q I` is the isomorphism
`…derivedSheafHomExactSupportKInjectiveIso` computing `R ℰom(𝒪_Z, -)` there, pushed forward,
followed by the `Q`-level identification of `Ri_*` and by the class of the degreewise underived
trace of [Stacks, Tag 0A75].

This is the description of the derived trace that a consumer working with a K-injective
representative needs; everything on the right-hand side is below `DerivedCategory.Q`. -/
theorem derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        (DerivedCategory.Q.obj I) =
      (modulePushforward S.i).mapDerivedCategory.map
          (S.derivedSheafHomExactSupportKInjectiveIso I).hom ≫
        (modulePushforward S.i).mapDerivedCategoryFactors.hom.app
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((Adjunction.mapHomologicalComplexAdjunction
              S.modulePushforwardSheafHomExactSupportAdjunction
                (ComplexShape.up ℤ)).counit.app I) := by
  have h : (S.derivedSheafHomExactSupportKInjectiveIso I).hom ≫
      S.derivedSheafHomExactSupportCochainComparison.app I = 𝟙 _ :=
    (S.derivedSheafHomExactSupportKInjectiveIso I).hom_inv_id
  rw [← S.derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q I,
    ← Functor.map_comp_assoc, h, CategoryTheory.Functor.map_id, Category.id_comp]

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
