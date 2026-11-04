module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRestrictionComputesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AV for abelian sheaves on the flat-fppf sites

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, `f'` its restriction to the flat-fppf
sites (**Stacks 07AT** (2)), and `g`, `g'` the comparison morphisms of **Stacks 0788** (2).
**Stacks 07AV** asserts, on the unbounded derived categories of abelian sheaves,

`g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹`  and  `L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!`.

Both are proved here with no hypothesis, exactly as in the lisse-étale case of
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleDerivedBaseChange.lean`: the first identity is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit` at the degree-zero square
`AlgebraicGeometry.Stack.FlatFppf.isIso_abelianSheafBaseChange` (**Stacks 07AT** (2)) and at
`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedPushforwardUnit_restriction` (restricted
K-injective complexes compute `Rf'_*`, by Stacks 07AK at the 2-fibre products `V ×_{y, 𝒴} 𝒳`);
the second is its conjugate under the derived adjunctions `Lg_! ⊣ g⁻¹`, `L(g')_! ⊣ (g')⁻¹` of
**Stacks 07AS** (3) and `f⁻¹ ⊣ Rf_*`, `(f')⁻¹ ⊣ Rf'_*`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.derivedRestrictionBaseChangeIso`: **Stacks 07AV**, first
  identity, for abelian sheaves on the flat-fppf sites.
* `AlgebraicGeometry.Stack.FlatFppf.derivedLowerShriekBaseChangeIso`: **Stacks 07AV**, second
  identity, for abelian sheaves on the flat-fppf sites.

## References

* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek
  (alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian)
open Stacks.Cohomology.SupportedComplexes (derivedAdjunctionOfExactLeftAdjoint)

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of abelian sheaves to the flat-fppf site is additive. -/
theorem additive_subsiteRestriction (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    haveI := isContinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
    (subsiteRestriction B S hS 𝒵.val.val.p B.topology
      (flatObject B S hS 𝒵.val)).Additive :=
  have := isContinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
  have := isCocontinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianRestriction.{u + 1, u, u + 1, u, u + 1}
    (inclusionTopology B S hS 𝒵)
    (associatedTopology B S hS 𝒵.val.val.p B.topology)
    (objectProperty B S hS 𝒵).ι

/-- Restriction of abelian sheaves to the flat-fppf site preserves finite colimits. -/
theorem preservesFiniteColimits_subsiteRestriction (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    haveI := isContinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
    PreservesFiniteColimits (subsiteRestriction B S hS 𝒵.val.val.p B.topology
      (flatObject B S hS 𝒵.val)) :=
  have := isContinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
  have := isCocontinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{u + 1, u,
      u + 1, u, u + 1}
    (inclusionTopology B S hS 𝒵)
    (associatedTopology B S hS 𝒵.val.val.p B.topology)
    (objectProperty B S hS 𝒵).ι

/-- Restriction of abelian sheaves to the flat-fppf site preserves finite limits, being a right
adjoint. -/
theorem preservesFiniteLimits_subsiteRestriction (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    haveI := isContinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
    PreservesFiniteLimits (subsiteRestriction B S hS 𝒵.val.val.p B.topology
      (flatObject B S hS 𝒵.val)) :=
  have := isContinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
  have := isCocontinuous_inclusion B S hS 𝒵 (closedUnderFlatMorphisms B S hS 𝒵)
  inferInstance

/-- **Stacks 07AV, first identity, for abelian sheaves on the flat-fppf sites:
`g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹`.** Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, `Rf_*`
and `Rf'_*` total right derived functors of the direct images along `f` and along its restriction
`f'` to the flat-fppf sites, and `g⁻¹`, `(g')⁻¹` restriction of abelian sheaves to the
flat-fppf sites of `𝒴` and `𝒳`. Then, on the unbounded derived categories,

`(g')⁻¹ ⋙ Rf'_* ≅ Rf_* ⋙ g⁻¹`.

No hypothesis is made beyond the right derived functor properties of `Rf_*` and `Rf'_*` (a right
derived functor being determined only up to unique isomorphism). The isomorphism is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit` at the degree-zero
identification `AlgebraicGeometry.Stack.FlatFppf.isIso_abelianSheafBaseChange` and at
`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedPushforwardUnit_restriction`. -/
@[stacks 07AV "the flat-fppf case for abelian sheaves, first identity: \
g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹ on the unbounded derived categories, as an isomorphism \
(g')⁻¹ ⋙ Rf'_* ≅ Rf_* ⋙ g⁻¹ for any total right derived functors Rf_*, Rf'_* of the two direct \
images, with no further hypothesis. The degree-zero square of Stacks 07AT (2) and the fact that \
restricted K-injective complexes compute Rf'_* (Stacks 07AK at the 2-fibre products V ×_y 𝒳, the \
content of Stacks 0GR3) are proved, not assumed"]
def derivedRestrictionBaseChangeIso
    (Rf : DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (associatedTopology B S hS 𝒴.val.val.p B.topology)
        AddCommGrpCat.{u + 1}))
    (Rf' : DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology B S hS 𝒴) AddCommGrpCat.{u + 1}))
    (αf : haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
      haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (associatedTopology B S hS 𝒳.val.val.p B.topology)
          (associatedTopology B S hS 𝒴.val.val.p B.topology)).Additive :=
        Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
      (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (associatedTopology B S hS 𝒳.val.val.p B.topology)
          (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
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
    [hRf : Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))]
    [hRf' : Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
      (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))] :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderFlatMorphisms B S hS 𝒴)
    haveI := additive_subsiteRestriction B S hS 𝒳
    haveI := additive_subsiteRestriction B S hS 𝒴
    haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒳
    haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒴
    haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒳
    haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒴
    (subsiteRestriction B S hS 𝒳.val.val.p B.topology
        (flatObject B S hS 𝒳.val)).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (subsiteRestriction B S hS 𝒴.val.val.p B.topology
        (flatObject B S hS 𝒴.val)).mapDerivedCategory :=
  haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderFlatMorphisms B S hS 𝒴)
  haveI := additive_subsiteRestriction B S hS 𝒳
  haveI := additive_subsiteRestriction B S hS 𝒴
  haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒳
  haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒴
  haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒳
  haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒴
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI := isCocontinuous_subsiteFunctor B S hS f hf
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
    (inclusionTopology B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit
    (subsiteRestriction B S hS 𝒳.val.val.p B.topology (flatObject B S hS 𝒳.val))
    (subsiteRestriction B S hS 𝒴.val.val.p B.topology (flatObject B S hS 𝒴.val))
    _ _ Rf Rf' αf αf' (@asIso _ _ _ _ _ (isIso_abelianSheafBaseChange B S hS f hf)).symm
    (fun I hI => isIso_derivedPushforwardUnit_restriction B S hS f hf Rf' αf' hRf' I hI)

attribute [local instance] hasPointwiseRightKanExtension_subsiteFunctor_ab
  hasPointwiseRightKanExtension_homFunctor_ab

/-- The total right derived direct image of abelian sheaves along a 1-morphism of algebraic
stacks, for the fppf sites. -/
abbrev derivedAbelianDirectImage :
    DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (associatedTopology B S hS 𝒴.val.val.p B.topology)
        AddCommGrpCat.{u + 1}) :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The total right derived direct image of abelian sheaves along the restriction of a flat
1-morphism of algebraic stacks to the flat-fppf sites. -/
abbrev derivedAbelianSubsiteDirectImage :
    DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology B S hS 𝒴) AddCommGrpCat.{u + 1}) :=
  haveI := isCocontinuous_subsiteFunctor B S hS f hf
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
    (inclusionTopology B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
        (inclusionTopology B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
        (inclusionTopology B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison exhibiting `derivedAbelianDirectImage` as a right derived functor. -/
abbrev derivedAbelianDirectImageUnit :
    haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
    haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology)).Additive :=
      Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
    (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianDirectImage B S hS f :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison exhibiting `derivedAbelianSubsiteDirectImage` as a right derived functor. -/
abbrev derivedAbelianSubsiteDirectImageUnit :
    haveI := isCocontinuous_subsiteFunctor B S hS f hf
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
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedAbelianSubsiteDirectImage B S hS f hf :=
  haveI := isCocontinuous_subsiteFunctor B S hS f hf
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
    (inclusionTopology B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
        (inclusionTopology B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
        (inclusionTopology B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The inverse image of abelian sheaves along a 1-morphism of algebraic stacks, for the fppf
sites, on the unbounded derived categories: it is restriction along the underlying functor of the
1-morphism, which is exact. -/
abbrev derivedAbelianInverseImage :
    DerivedCategory (Sheaf (associatedTopology B S hS 𝒴.val.val.p B.topology)
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p B.topology)
        AddCommGrpCat.{u + 1}) :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (associatedTopology B S hS 𝒴.val.val.p B.topology) f.hom.hom.toFunctor
  (f.hom.hom.toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapDerivedCategory

/-- The inverse image of abelian sheaves along the restriction of a flat 1-morphism to the
flat-fppf sites, on the unbounded derived categories. -/
abbrev derivedAbelianSubsiteInverseImage :
    DerivedCategory (Sheaf (inclusionTopology B S hS 𝒴) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) :=
  haveI := isContinuous_subsiteFunctor B S hS f hf
  haveI := isCocontinuous_subsiteFunctor B S hS f hf
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf))
  ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)).mapDerivedCategory

/-- **Stacks 07AV, second identity, for abelian sheaves on the flat-fppf sites:
`L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!`.** For a flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, with
`Lg_!` and `L(g')_!` the derived lower shrieks of **Stacks 07AS** (1) for `𝒴` and `𝒳`, and `f⁻¹`,
`(f')⁻¹` the inverse images along `f` and along its restriction `f'` to the flat-fppf sites,

`Lg_! ⋙ f⁻¹ ≅ (f')⁻¹ ⋙ L(g')_!`

on the unbounded derived categories of abelian sheaves. All four functors are the canonical ones
and no hypothesis is made. The isomorphism is the conjugate, under the composites of the derived
adjunctions `Lg_! ⊣ g⁻¹`, `L(g')_! ⊣ (g')⁻¹` of Stacks 07AS (3) and `f⁻¹ ⊣ Rf_*`,
`(f')⁻¹ ⊣ Rf'_*` (exact left adjoints), of the first identity
`AlgebraicGeometry.Stack.FlatFppf.derivedRestrictionBaseChangeIso`. -/
@[stacks 07AV "the flat-fppf case for abelian sheaves, second identity: \
L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_! on the unbounded derived categories, as an isomorphism \
Lg_! ⋙ f⁻¹ ≅ (f')⁻¹ ⋙ L(g')_! of the canonical functors, with no hypothesis: the derived \
lower shrieks are those of Stacks 07AS (3), and the four derived adjunctions are constructed"]
def derivedLowerShriekBaseChangeIso :
    derivedAbelianLowerShriekFunctor B S hS 𝒴 ⋙ derivedAbelianInverseImage B S hS f ≅
      derivedAbelianSubsiteInverseImage B S hS f hf ⋙ derivedAbelianLowerShriekFunctor B S hS 𝒳 :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI := isContinuous_subsiteFunctor B S hS f hf
  haveI := isCocontinuous_subsiteFunctor B S hS f hf
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (associatedTopology B S hS 𝒴.val.val.p B.topology) f.hom.hom.toFunctor
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf))
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
    (inclusionTopology B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
        (inclusionTopology B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  let adjf := derivedAdjunctionOfExactLeftAdjoint
    (f.hom.hom.toFunctor.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology))
    (derivedAbelianDirectImage B S hS f) (derivedAbelianDirectImageUnit B S hS f)
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian
  let adjf' := derivedAdjunctionOfExactLeftAdjoint
    ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (inclusionTopology B S hS 𝒳) (inclusionTopology B S hS 𝒴))
    (derivedAbelianSubsiteDirectImage B S hS f hf)
    (derivedAbelianSubsiteDirectImageUnit B S hS f hf)
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian
  (conjugateIsoEquiv (adjf'.comp (derivedAbelianLowerShriekFunctorAdjunction B S hS 𝒳))
    ((derivedAbelianLowerShriekFunctorAdjunction B S hS 𝒴).comp adjf)).symm
    (derivedRestrictionBaseChangeIso B S hS f hf (derivedAbelianDirectImage B S hS f)
      (derivedAbelianSubsiteDirectImage B S hS f hf) (derivedAbelianDirectImageUnit B S hS f)
      (derivedAbelianSubsiteDirectImageUnit B S hS f hf))

end AlgebraicGeometry.Stack.FlatFppf
