module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LqcFbcModuleFppfEtaleCohomology
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# Fppf and étale higher direct images of a locally quasi-coherent module with flat base change

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}` and let
`ℱ` be a presheaf of `𝒪_𝒳`-modules which is locally quasi-coherent and whose comparison maps
`c_φ` are isomorphisms along the arrows lying over flat morphisms locally of finite presentation.
By **Stacks 075R** `ℱ` is an `𝒪_𝒳`-module with `Rε_*ℱ = ε_*ℱ` for the comparison morphism
`ε : 𝒳_{fppf} ⟶ 𝒳_{étale}`.

This file proves clause (3) of **Stacks 075R**: `R^i f_*ℱ`, computed in the fppf topology, is the
fppf sheafification of the higher direct image computed in the étale topology, and similarly for
the derived direct image. The direct image of sheaves of `𝒪`-modules along `f` is
`AlgebraicGeometry.Stack.moduleDirectImageSmall`, right adjoint to restriction along `f`
(`AlgebraicGeometry.Stack.moduleInverseImageDirectImageAdjunction`). Its underlying presheaf of
modules does not depend on the topology, so `ε_* ∘ f_{fppf,*} = f_{étale,*} ∘ ε_*`, and since fppf
sheafification `ε⁻¹` undoes `ε_*`,

`f_{fppf,*} ≅ ε⁻¹ ∘ f_{étale,*} ∘ ε_*`.

Clause (1) makes `ℱ` acyclic for `ε_*`, which is left exact and preserves injectives, and `ε⁻¹`
is exact; so the derived functors of the right hand side at `ℱ` are `ε⁻¹(R^i f_{étale,*}(ε_*ℱ))`
(`Stacks.RightDerivedComp.objIsoOfIsoComp`).

## Main definitions

* `AlgebraicGeometry.Stack.moduleDirectImageSmall`: the direct image `f_*` of sheaves of
  `𝒪`-modules, for each of the associated topologies.
* `AlgebraicGeometry.Stack.etaleComparisonPullback`: the inverse image `ε⁻¹` on `𝒴`, fppf
  sheafification of étale `𝒪_𝒴`-modules.

## Main results

* `AlgebraicGeometry.Stack.moduleDirectImageIsoEtale`: `f_{fppf,*} ≅ ε⁻¹ ∘ f_{étale,*} ∘ ε_*`.
* `AlgebraicGeometry.Stack.higherDirectImageIsoEtale` and
  `AlgebraicGeometry.Stack.derivedDirectImageIsoEtale`: the comparison of higher and derived
  direct images of `ℱ`.
* `AlgebraicGeometry.Stack.nonempty_higherDirectImageIso_sheafify_etale_lqcFbcModule`:
  **Stacks 075R (3)**.

## Implementation notes

The source proves (3) through Stacks 075G, computing both higher direct images as sheafified
cohomology of the 2-fibre products `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳` and comparing them by (2). The
argument here needs neither: it uses only clause (1) and the compatibility of the direct images
with `ε`. The categories `𝒳` and `𝒴` have their morphisms in the universe of the schemes and are
essentially small, the seating of
`AlgebraicGeometry.Stack.isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule`; the direct
image is `SheafOfModules.directImageSmall`, which exists in that universe. The derived direct
images are the direct images of injective resolutions, compared in the homotopy category, and
the source's "derived pullback" in (3) is read as the derived direct image `Rf_*`.

## References

* [Stacks Project, Tag 075R](https://stacks.math.columbia.edu/tag/075R)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v₁ v₂

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{u} 𝒳] {𝒴 : Type v₂} [Category.{u} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)

include hp hq hf in
/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}` is continuous for each of
the associated topologies (**Stacks 06NW**). -/
theorem isContinuous_associatedTopology_of_comp_eq (τ : SiteKind) :
    f.IsContinuous (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS q τ) :=
  let := hp.isFibered
  let := hq.isFibered
  ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).1

include hp hq hf in
/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}` is cocontinuous for each
of the associated topologies (**Stacks 06NW**). -/
theorem isCocontinuous_associatedTopology_of_comp_eq (τ : SiteKind) :
    f.IsCocontinuous (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS q τ) :=
  let := hp.isFibered
  let := hq.isFibered
  ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS τ)).2

include hf in
/-- The structure presheaf of rings of `𝒳` is that of `𝒴` restricted along a 1-morphism. -/
theorem ringStructureSheafCore_obj_eq_of_comp_eq (τ : SiteKind) :
    (FibredSite.ringStructureSheafCore B S hS p hp τ).obj =
      f.op ⋙ (FibredSite.ringStructureSheafCore B S hS q hq τ).obj := by
  subst hf
  rfl

variable [EssentiallySmall.{u} 𝒳]

/-- **The direct image `f_*` of sheaves of `𝒪`-modules along a 1-morphism `f : 𝒳 ⟶ 𝒴` of
categories fibred in groupoids**, for an associated topology `τ` and an essentially small `𝒳`. -/
def moduleDirectImageSmall (τ : SiteKind) :
    SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp τ) ⥤
      SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS q hq τ) :=
  letI := isContinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf τ
  letI := isCocontinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf τ
  SheafOfModules.directImageSmall f _ _ _
    (ringStructureSheafCore_obj_eq_of_comp_eq B S hS p q hp hq f hf τ)

/-- The direct image `f_*` is right adjoint to the inverse image `f⁻¹`, restriction along `f`
(**Stacks 06WE**). -/
def moduleInverseImageDirectImageAdjunction (τ : SiteKind) :
    letI := isContinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf τ
    SheafOfModules.inverseImageOfObjEq f _ _ _
        (ringStructureSheafCore_obj_eq_of_comp_eq B S hS p q hp hq f hf τ) ⊣
      moduleDirectImageSmall B S hS p q hp hq f hf τ :=
  letI := isContinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf τ
  letI := isCocontinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf τ
  SheafOfModules.inverseImageDirectImageSmallAdjunction f _ _ _ _

/-- The direct image `f_*` is additive. -/
theorem additive_moduleDirectImage (τ : SiteKind) :
    (moduleDirectImageSmall B S hS p q hp hq f hf τ).Additive :=
  let := isContinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf τ
  let := isCocontinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf τ
  SheafOfModules.additive_directImageSmall f _ _ _ _

/-- The étale direct image is the direct image for the étale topologies read off the fppf
structure sheaves. -/
theorem moduleDirectImage_etale_eq :
    moduleDirectImageSmall B S hS p q hp hq f hf .etale =
      letI := isContinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf .etale
      letI := isCocontinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf .etale
      SheafOfModules.directImageSmall f _ _
        (Stacks.SheafOfModules.ringOfLe (BigFppfOver.associatedTopology_le_fppf B S hS q .etale)
          (fppfSiteRingSheaf B S hS q hq))
        (T := Stacks.SheafOfModules.ringOfLe
          (BigFppfOver.associatedTopology_le_fppf B S hS p .etale) (fppfSiteRingSheaf B S hS p hp))
        (ringStructureSheafCore_obj_eq_of_comp_eq B S hS p q hp hq f hf .fppf) :=
  rfl

/-- The direct images for the fppf and the étale topologies are compatible with the comparison
morphisms `ε` of `𝒳` and `𝒴`: `ε_* ∘ f_{fppf,*} = f_{étale,*} ∘ ε_*`, both being computed on the
same presheaf of modules. -/
def moduleDirectImageEtaleComparisonIso :
    moduleDirectImageSmall B S hS p q hp hq f hf .fppf ⋙ etaleComparisonPushforward B S hS q hq ≅
      etaleComparisonPushforward B S hS p hp ⋙
        moduleDirectImageSmall B S hS p q hp hq f hf .etale :=
  letI := isContinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf .fppf
  letI := isCocontinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf .fppf
  letI := isContinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf .etale
  letI := isCocontinuous_associatedTopology_of_comp_eq B S hS p q hp hq f hf .etale
  Functor.isoWhiskerLeft _
      (eqToIso (etaleComparisonPushforward_eq_comparisonPushforward B S hS q hq)) ≪≫
    SheafOfModules.directImageSmallCompComparisonIso f
      (BigFppfOver.associatedTopology_le_fppf B S hS p .etale)
      (BigFppfOver.associatedTopology_le_fppf B S hS q .etale) (fppfSiteRingSheaf B S hS q hq)
      (ringStructureSheafCore_obj_eq_of_comp_eq B S hS p q hp hq f hf .fppf) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (etaleComparisonPushforward_eq_comparisonPushforward B S hS p hp).symm) _ ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (moduleDirectImage_etale_eq B S hS p q hp hq f hf).symm)

section HigherDirectImages

variable [EssentiallySmall.{u} 𝒴] (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  enoughInjectives_etaleSiteModules_of_essentiallySmall
  preservesInjectiveObjects_etaleComparisonPushforward
  preservesFiniteLimits_etaleComparisonPushforward
  additive_moduleDirectImage

/-- Fppf sheafification of the étale `𝒪_𝒴`-modules, the inverse image `ε⁻¹` of the comparison
morphism `ε : 𝒴_{fppf} ⟶ 𝒴_{étale}`. -/
abbrev etaleComparisonPullback :
    SheafOfModules.{u} (etaleSiteRingSheaf B S hS q hq) ⥤ fppfSiteModules B S hS q hq :=
  Stacks.SheafOfModules.comparisonPullback.{v₂, u, u, u}
    (BigFppfOver.associatedTopology_le_fppf B S hS q .etale) (fppfSiteRingSheaf B S hS q hq)

/-- `ε⁻¹` is additive. -/
theorem additive_etaleComparisonPullback : (etaleComparisonPullback B S hS q hq).Additive :=
  Stacks.SheafOfModules.additive_comparisonPullback _ _

attribute [local instance] additive_etaleComparisonPullback

/-- `f_{fppf,*} ≅ ε⁻¹ ∘ f_{étale,*} ∘ ε_*`: the fppf direct image is recovered from the étale one
by reading modules for the étale topology on `𝒳` and sheafifying for the fppf topology on `𝒴`. -/
def moduleDirectImageIsoEtale :
    moduleDirectImageSmall B S hS p q hp hq f hf .fppf ≅
      etaleComparisonPushforward B S hS p hp ⋙ moduleDirectImageSmall B S hS p q hp hq f hf .etale ⋙
        etaleComparisonPullback B S hS q hq :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.SheafOfModules.comparisonPushforwardCompPullbackIso.{v₂, u, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS q .etale)
        (fppfSiteRingSheaf B S hS q hq)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
      (eqToIso (etaleComparisonPushforward_eq_comparisonPushforward B S hS q hq).symm)) _ ≪≫
    Functor.isoWhiskerRight (moduleDirectImageEtaleComparisonIso B S hS p q hp hq f hf) _ ≪≫
    Functor.associator _ _ _

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)
  (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
  (hbc : HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) F)

/-- `R^i f_{fppf,*} ℱ ≅ ε⁻¹(R^i f_{étale,*}(ε_*ℱ))` for the module `ℱ` of Stacks 075R. -/
def higherDirectImageIsoEtale (i : ℕ) :
    ((moduleDirectImageSmall B S hS p q hp hq f hf .fppf).rightDerived i).obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      (etaleComparisonPullback B S hS q hq).obj
        (((moduleDirectImageSmall B S hS p q hp hq f hf .etale).rightDerived i).obj
          ((etaleComparisonPushforward B S hS p hp).obj
            (lqcFbcModule B E h S hS p hp F hlqc hbc))) :=
  @Stacks.RightDerivedComp.objIsoOfIsoComp _ _ _ _ _ _ _ _ _ _ _
    (etaleComparisonPushforward B S hS p hp) _ _ _
    (moduleDirectImageSmall B S hS p q hp hq f hf .etale)
    (additive_moduleDirectImage B S hS p q hp hq f hf .etale) _
    (isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule B E h S hS p hp F hlqc hbc)
    _ _ _ (etaleComparisonPullback B S hS q hq) (additive_etaleComparisonPullback B S hS q hq) _
    (additive_moduleDirectImage B S hS p q hp hq f hf .fppf)
    (moduleDirectImageIsoEtale B S hS p q hp hq f hf)
    (Stacks.SheafOfModules.preservesHomology_comparisonPullback _ _) i

/-- `Rf_{fppf,*} ℱ ≅ ε⁻¹(Rf_{étale,*}(ε_*ℱ))` for the module `ℱ` of Stacks 075R, as complexes up
to homotopy: each side is a direct image of an injective resolution. -/
def derivedDirectImageIsoEtale :
    (moduleDirectImageSmall B S hS p q hp hq f hf .fppf).rightDerivedToHomotopyCategory.obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      ((etaleComparisonPullback B S hS q hq).mapHomotopyCategory (ComplexShape.up ℕ)).obj
        ((moduleDirectImageSmall B S hS p q hp hq f hf .etale).rightDerivedToHomotopyCategory.obj
          ((etaleComparisonPushforward B S hS p hp).obj
            (lqcFbcModule B E h S hS p hp F hlqc hbc))) :=
  @Stacks.RightDerivedComp.homotopyCategoryObjIsoOfIsoComp _ _ _ _ _ _ _ _ _ _ _
    (etaleComparisonPushforward B S hS p hp) _ _ _
    (moduleDirectImageSmall B S hS p q hp hq f hf .etale)
    (additive_moduleDirectImage B S hS p q hp hq f hf .etale) _
    (isZero_rightDerived_etaleComparisonPushforward_lqcFbcModule B E h S hS p hp F hlqc hbc)
    _ _ _ (etaleComparisonPullback B S hS q hq) (additive_etaleComparisonPullback B S hS q hq) _
    (additive_moduleDirectImage B S hS p q hp hq f hf .fppf)
    (moduleDirectImageIsoEtale B S hS p q hp hq f hf)

include hlqc hbc in
/-- **Stacks 075R, clause (3).** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids
over `(Sch/S)_{fppf}` and let `ℱ` be a presheaf of `𝒪_𝒳`-modules satisfying (a) and (b) of
Stacks 075R, so an `𝒪_𝒳`-module (`AlgebraicGeometry.Stack.lqcFbcModule`). Then

* `R^i f_*ℱ`, computed in the fppf topology, is the fppf sheafification of the higher direct image
  `R^i f_{étale,*}(ε_*ℱ)` computed in the étale topology, for every `i`;
* similarly for the derived direct image: `Rf_*ℱ` is `ε⁻¹(Rf_{étale,*}(ε_*ℱ))`, the direct images
  being those of injective resolutions, up to homotopy, and `ε⁻¹` the fppf sheafification of
  étale modules (`Stacks.SheafOfModules.comparisonPullbackIso`).

The source deduces this from (2) and Stacks 075G. Here it is deduced from (1) directly:
`f_{fppf,*} ≅ ε⁻¹ ∘ f_{étale,*} ∘ ε_*` (`AlgebraicGeometry.Stack.moduleDirectImageIsoEtale`),
`ε_*` carries an injective resolution of the `ε_*`-acyclic module `ℱ` to one of `ε_*ℱ`, and
`ε⁻¹` is exact. -/
@[stacks 075R "clause (3): for a 1-morphism `f : 𝒳 → 𝒴` of categories fibred in groupoids and a \
module `ℱ` satisfying (a) and (b), `R^if_*ℱ` is the fppf sheafification of the higher direct image \
computed in the étale topology, and similarly for the derived direct image"]
theorem nonempty_higherDirectImageIso_sheafify_etale_lqcFbcModule :
    (∀ i : ℕ, Nonempty (((moduleDirectImageSmall B S hS p q hp hq f hf .fppf).rightDerived i).obj
        (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
      (PresheafOfModules.sheafification.{u} (𝟙 (fppfSiteRingSheaf B S hS q hq).obj)).obj
        (((moduleDirectImageSmall B S hS p q hp hq f hf .etale).rightDerived i).obj
          ((etaleComparisonPushforward B S hS p hp).obj
            (lqcFbcModule B E h S hS p hp F hlqc hbc))).val)) ∧
    Nonempty
      ((moduleDirectImageSmall B S hS p q hp hq f hf .fppf).rightDerivedToHomotopyCategory.obj
          (lqcFbcModule B E h S hS p hp F hlqc hbc) ≅
        ((etaleComparisonPullback B S hS q hq).mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((moduleDirectImageSmall B S hS p q hp hq f hf .etale).rightDerivedToHomotopyCategory.obj
            ((etaleComparisonPushforward B S hS p hp).obj
              (lqcFbcModule B E h S hS p hp F hlqc hbc)))) :=
  ⟨fun i => ⟨higherDirectImageIsoEtale B S hS p q hp hq f hf E h F hlqc hbc i ≪≫
      (Stacks.SheafOfModules.comparisonPullbackIso.{v₂, u, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS q .etale)
        (fppfSiteRingSheaf B S hS q hq)).app _⟩,
    ⟨derivedDirectImageIsoEtale B S hS p q hp hq f hf E h F hlqc hbc⟩⟩

end HigherDirectImages

end AlgebraicGeometry.Stack
