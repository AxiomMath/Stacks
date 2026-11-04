module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleComparisonLqcFbc
public import StacksFrontier.AlgebraicGeometry.Topologies.ComparisonPushforwardInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Homology.CompositeCollapseHomotopyCategory

/-!
# Fppf and étale cohomology of a locally quasi-coherent module with flat base change

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `ℱ` a presheaf of
`𝒪_𝒳`-modules which is locally quasi-coherent and whose comparison maps `c_φ` are isomorphisms
along the arrows lying over flat morphisms locally of finite presentation. By the first assertion
of **Stacks 075R** `ℱ` is an `𝒪_𝒳`-module, and by its clause (1) the higher direct images of `ℱ`
along the comparison morphism `ε : 𝒳_{fppf} ⟶ 𝒳_{étale}` vanish.

This file proves clause (2) of **Stacks 075R**: the cohomology of `ℱ` on `𝒳` and over each object
`x` of `𝒳`, and the corresponding derived sections, are the same whether computed in the fppf or
in the étale topology. The source deduces this from (1) and the Leray spectral sequence (Stacks
0733); here the collapse is obtained directly. The direct image `ε_*` changes neither the
underlying presheaf of modules nor its sections, so global sections and sections over `x` on the
fppf site factor as `ε_*` followed by the same functors on the étale site. The functor `ε_*` is
left exact and preserves injective objects, its left adjoint being fppf sheafification
(`Stacks.SheafOfModules.preservesInjectiveObjects_comparisonPushforward`), so it carries an
injective resolution of the `ε_*`-acyclic module `ℱ` to an injective resolution of `ε_*ℱ`
(`Stacks.RightDerivedComp.objIsoOfIso`, `Stacks.RightDerivedComp.homotopyCategoryObjIsoOfIso`).

## Main results

* `AlgebraicGeometry.Stack.globalCohomologyIsoEtale`,
  `AlgebraicGeometry.Stack.objectCohomologyIsoEtale`: `H^n_{fppf}(𝒳, ℱ) ≅ H^n_{étale}(𝒳, ε_*ℱ)`
  and `H^n_{fppf}(x, ℱ) ≅ H^n_{étale}(x, ε_*ℱ)`.
* `AlgebraicGeometry.Stack.globalDerivedSectionsIsoEtale`,
  `AlgebraicGeometry.Stack.objectDerivedSectionsIsoEtale`: the same for the derived sections,
  as complexes up to homotopy.
* `AlgebraicGeometry.Stack.nonempty_fppfCohomologyIso_etaleCohomology_lqcFbcModule`:
  **Stacks 075R (2)**.

## Implementation notes

The source identifies `ℱ` with `ε_*ℱ`, "and this is the sense in which part (2) of the lemma
should be understood"; the statements compare the fppf cohomology of `ℱ` with the étale
cohomology of `ε_*ℱ`. The derived sections `RΓ` are the complexes of sections of an injective
resolution, `CategoryTheory.Functor.rightDerivedToHomotopyCategory`, and they are compared by an
isomorphism in the homotopy category, which gives the isomorphism in the derived category after
localization. The seating — `𝒳` with morphisms in the universe of the schemes and essentially
small — is that of
`AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule`.

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall

/-- The `𝒪_𝒳`-modules on the étale site of an essentially small category fibred in groupoids have
enough injectives: they form a Grothendieck abelian category. -/
theorem enoughInjectives_etaleSiteModules_of_essentiallySmall :
    EnoughInjectives (SheafOfModules.{u} (etaleSiteRingSheaf B S hS p hp)) :=
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (etaleSiteRingSheaf B S hS p hp)) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (etaleSiteRingSheaf B S hS p hp)
  inferInstance

attribute [local instance] enoughInjectives_etaleSiteModules_of_essentiallySmall

attribute [local instance] preservesInjectiveObjects_etaleComparisonPushforward
  preservesFiniteLimits_etaleComparisonPushforward

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive

/-- Global sections on the fppf site of `𝒳` are global sections on the étale site of the direct
image `ε_*`: both are the compatible families of sections of the same presheaf of modules. -/
def globalSectionsIsoEtaleComparisonPushforward :
    Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (fppfSiteRingSheaf B S hS p hp) ≅
      etaleComparisonPushforward B S hS p hp ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
          (etaleSiteRingSheaf B S hS p hp) :=
  Stacks.SheafOfModules.globalSectionsIsoComparisonPushforward
    (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp)

/-- Sections over an object `x` on the fppf site of `𝒳` are sections over `x` on the étale site
of the direct image `ε_*`. -/
def evaluationIsoEtaleComparisonPushforward (x : 𝒳) :
    SheafOfModules.evaluation.{u} (fppfSiteRingSheaf B S hS p hp) (op x) ≅
      etaleComparisonPushforward B S hS p hp ⋙
        SheafOfModules.evaluation.{u} (etaleSiteRingSheaf B S hS p hp) (op x) :=
  Stacks.SheafOfModules.evaluationIsoComparisonPushforward
    (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp) (op x)

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F)

/-- `H^n_{fppf}(𝒳, ℱ) ≅ H^n_{étale}(𝒳, ε_*ℱ)` for the module `ℱ` of Stacks 075R. -/
def globalCohomologyIsoEtale (n : ℕ) :
    ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (fppfSiteRingSheaf B S hS p hp)).rightDerived n).obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (etaleSiteRingSheaf B S hS p hp)).rightDerived n).obj
        ((etaleComparisonPushforward B S hS p hp).obj (lqcFbcModule B E h S hS p hp F hlqc hbc)) :=
  @Stacks.RightDerivedComp.objIsoOfIso _ _ _ _ _ _ _ _ _ _ _
    (etaleComparisonPushforward B S hS p hp) _ _ _
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
      (etaleSiteRingSheaf B S hS p hp)) _ _
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor_additive _)
    (globalSectionsIsoEtaleComparisonPushforward B S hS p hp) _
    (isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule B E h S hS p hp F hlqc hbc) n

/-- `H^n_{fppf}(x, ℱ) ≅ H^n_{étale}(x, ε_*ℱ)` for the module `ℱ` of Stacks 075R and an object
`x` of `𝒳`. -/
def objectCohomologyIsoEtale (x : 𝒳) (n : ℕ) :
    ((SheafOfModules.evaluation.{u} (fppfSiteRingSheaf B S hS p hp) (op x)).rightDerived n).obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      ((SheafOfModules.evaluation.{u} (etaleSiteRingSheaf B S hS p hp) (op x)).rightDerived n).obj
        ((etaleComparisonPushforward B S hS p hp).obj (lqcFbcModule B E h S hS p hp F hlqc hbc)) :=
  @Stacks.RightDerivedComp.objIsoOfIso _ _ _ _ _ _ _ _ _ _ _
    (etaleComparisonPushforward B S hS p hp) _ _ _
    (SheafOfModules.evaluation.{u} (etaleSiteRingSheaf B S hS p hp) (op x)) _ _
    (Stacks.Cohomology.AcyclicCover.evaluation_additive _ _)
    (evaluationIsoEtaleComparisonPushforward B S hS p hp x) _
    (isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule B E h S hS p hp F hlqc hbc) n

/-- `RΓ_{fppf}(𝒳, ℱ) ≅ RΓ_{étale}(𝒳, ε_*ℱ)` for the module `ℱ` of Stacks 075R, as complexes up
to homotopy: each side is global sections of an injective resolution. -/
def globalDerivedSectionsIsoEtale :
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (fppfSiteRingSheaf B S hS p hp)).rightDerivedToHomotopyCategory.obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (etaleSiteRingSheaf B S hS p hp)).rightDerivedToHomotopyCategory.obj
        ((etaleComparisonPushforward B S hS p hp).obj (lqcFbcModule B E h S hS p hp F hlqc hbc)) :=
  @Stacks.RightDerivedComp.homotopyCategoryObjIsoOfIso _ _ _ _ _ _ _ _ _ _ _
    (etaleComparisonPushforward B S hS p hp) _ _ _
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
      (etaleSiteRingSheaf B S hS p hp)) _ _
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor_additive _)
    (globalSectionsIsoEtaleComparisonPushforward B S hS p hp) _
    (isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule B E h S hS p hp F hlqc hbc)

/-- `RΓ_{fppf}(x, ℱ) ≅ RΓ_{étale}(x, ε_*ℱ)` for the module `ℱ` of Stacks 075R and an object `x`
of `𝒳`, as complexes up to homotopy. -/
def objectDerivedSectionsIsoEtale (x : 𝒳) :
    (SheafOfModules.evaluation.{u} (fppfSiteRingSheaf B S hS p hp)
        (op x)).rightDerivedToHomotopyCategory.obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      (SheafOfModules.evaluation.{u} (etaleSiteRingSheaf B S hS p hp)
          (op x)).rightDerivedToHomotopyCategory.obj
        ((etaleComparisonPushforward B S hS p hp).obj (lqcFbcModule B E h S hS p hp F hlqc hbc)) :=
  @Stacks.RightDerivedComp.homotopyCategoryObjIsoOfIso _ _ _ _ _ _ _ _ _ _ _
    (etaleComparisonPushforward B S hS p hp) _ _ _
    (SheafOfModules.evaluation.{u} (etaleSiteRingSheaf B S hS p hp) (op x)) _ _
    (Stacks.Cohomology.AcyclicCover.evaluation_additive _ _)
    (evaluationIsoEtaleComparisonPushforward B S hS p hp x) _
    (isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule B E h S hS p hp F hlqc hbc)

include hlqc hbc in
/-- **Stacks 075R, clause (2).** Let `ℱ` be a presheaf of `𝒪_𝒳`-modules satisfying (a) and (b) of
Stacks 075R, so an `𝒪_𝒳`-module (`AlgebraicGeometry.Stack.lqcFbcModule`), and let
`ε : 𝒳_{fppf} ⟶ 𝒳_{étale}` be the comparison morphism. The cohomology of `ℱ` computed in the
fppf topology agrees with the cohomology of `ε_*ℱ`, the same presheaf of modules, computed in the
étale topology:

* `H^n_{fppf}(𝒳, ℱ) ≅ H^n_{étale}(𝒳, ε_*ℱ)` for all `n`;
* `H^n_{fppf}(x, ℱ) ≅ H^n_{étale}(x, ε_*ℱ)` for every object `x` of `𝒳` and all `n`;
* `RΓ_{fppf}(𝒳, ℱ) ≅ RΓ_{étale}(𝒳, ε_*ℱ)` and `RΓ_{fppf}(x, ℱ) ≅ RΓ_{étale}(x, ε_*ℱ)`, the
  derived sections being the complexes of sections of injective resolutions, up to homotopy.

As in the source this follows formally from clause (1): `ε_*` is left exact and preserves
injectives, and `ℱ` is `ε_*`-acyclic by
`AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule`, so `ε_*`
carries an injective resolution of `ℱ` to one of `ε_*ℱ`, and both cohomologies are computed by
the same complex of sections. -/
@[stacks 075R "clause (2): fppf cohomology `H^p(𝒳, ℱ)`, `H^p(x, ℱ)` and the derived sections \
`RΓ(𝒳, ℱ)`, `RΓ(x, ℱ)` of a module satisfying (a) and (b) agree with those computed in the \
étale topology"]
theorem nonempty_fppfCohomologyIso_etaleCohomology_lqcFbcModule :
    (∀ n : ℕ, Nonempty (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (fppfSiteRingSheaf B S hS p hp)).rightDerived n).obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (etaleSiteRingSheaf B S hS p hp)).rightDerived n).obj
        ((etaleComparisonPushforward B S hS p hp).obj
          (lqcFbcModule B E h S hS p hp F hlqc hbc)))) ∧
    (∀ (x : 𝒳) (n : ℕ), Nonempty
      (((SheafOfModules.evaluation.{u} (fppfSiteRingSheaf B S hS p hp) (op x)).rightDerived n).obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      ((SheafOfModules.evaluation.{u} (etaleSiteRingSheaf B S hS p hp) (op x)).rightDerived n).obj
        ((etaleComparisonPushforward B S hS p hp).obj
          (lqcFbcModule B E h S hS p hp F hlqc hbc)))) ∧
    Nonempty ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (fppfSiteRingSheaf B S hS p hp)).rightDerivedToHomotopyCategory.obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{v, u, u, u}
        (etaleSiteRingSheaf B S hS p hp)).rightDerivedToHomotopyCategory.obj
        ((etaleComparisonPushforward B S hS p hp).obj
          (lqcFbcModule B E h S hS p hp F hlqc hbc))) ∧
    (∀ x : 𝒳, Nonempty
      ((SheafOfModules.evaluation.{u} (fppfSiteRingSheaf B S hS p hp)
          (op x)).rightDerivedToHomotopyCategory.obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      (SheafOfModules.evaluation.{u} (etaleSiteRingSheaf B S hS p hp)
          (op x)).rightDerivedToHomotopyCategory.obj
        ((etaleComparisonPushforward B S hS p hp).obj
          (lqcFbcModule B E h S hS p hp F hlqc hbc)))) :=
  ⟨fun n => ⟨globalCohomologyIsoEtale B E h S hS p hp F hlqc hbc n⟩,
    fun x n => ⟨objectCohomologyIsoEtale B E h S hS p hp F hlqc hbc x n⟩,
    ⟨globalDerivedSectionsIsoEtale B E h S hS p hp F hlqc hbc⟩,
    fun x => ⟨objectDerivedSectionsIsoEtale B E h S hS p hp F hlqc hbc x⟩⟩

end AlgebraicGeometry.Stack
