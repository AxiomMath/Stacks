module

public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleRestrictionComputesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteAbelianPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteAbelianSheafBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AV for abelian sheaves on the lisse-étale sites

Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks, `f'` its restriction to the
lisse-étale sites (**Stacks 07AT** (1)), and `g : Sh(𝒴_{lisse,étale}) ⟶ Sh(𝒴_{étale})`,
`g' : Sh(𝒳_{lisse,étale}) ⟶ Sh(𝒳_{étale})` the comparison morphisms of **Stacks 0788** (1).
**Stacks 07AV** asserts, on the unbounded derived categories of abelian sheaves,

`g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹`  and  `L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!`.

Both are proved here with no hypothesis.

## The first identity

It is the base change theorem
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit` for the square of `f`, `f'`
and the two restrictions, whose two inputs are

* the degree-zero identification `f'_*(g')⁻¹ ≅ g⁻¹ f_*` of **Stacks 07AT** (1) on abelian sheaves,
  `AlgebraicGeometry.Stack.LisseEtale.isIso_abelianSheafBaseChange`; and
* the statement that `(g')⁻¹ I` computes `Rf'_*` for every K-injective complex `I` on
  `𝒳_{étale}`, `AlgebraicGeometry.Stack.LisseEtale.isIso_derivedPushforwardUnit_restriction`.

The second input replaces the false assertion that `(g')⁻¹` preserves K-injectivity: that would
need `g'_!` to be exact, which it is not (for `𝒳 = 𝔸¹` the image under `g'_!` of the injective
map `t : 𝒪 ⟶ 𝒪` of the lisse-étale structure sheaf is multiplication by `t` on `𝒪_{𝒳_{étale}}`,
which is zero on the closed point). What is true, and is what the source's "the rest of the
proof is formal" rests on, is that the sheaves corepresenting the sections of `f'_*` have no
higher `Ext` into restricted injectives (Stacks 07AK at the 2-fibre products `V ×_{y, 𝒴} 𝒳`, which
is the content of Stacks 0GR3), so that restricted K-injective complexes compute `Rf'_*`.

## The second identity

The two sides are left adjoint to the two sides of the first, by composing the derived
adjunctions `Lg_! ⊣ g⁻¹`, `L(g')_! ⊣ (g')⁻¹` of **Stacks 07AS** (1)
(`AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekAdjunction`) with
`f⁻¹ ⊣ Rf_*`, `(f')⁻¹ ⊣ Rf'_*`, the derived adjunctions of exact left adjoints
(`derivedAdjunctionOfExactLeftAdjoint`); the second identity
is the conjugate of the first under `CategoryTheory.conjugateIsoEquiv`, exactly as the source
derives it. All four derived functors are the canonical ones: the derived lower shrieks of
Stacks 07AS and the total right derived direct images.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.derivedRestrictionBaseChangeIso`: **Stacks 07AV**, first
  identity, for abelian sheaves.
* `AlgebraicGeometry.Stack.LisseEtale.derivedLowerShriekBaseChangeIso`: **Stacks 07AV**, second
  identity, for abelian sheaves.

## References

* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0GR3](https://stacks.math.columbia.edu/tag/0GR3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedLowerShriek
  (alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian)
open Stacks.Cohomology.SupportedComplexes (derivedAdjunctionOfExactLeftAdjoint)

namespace CategoryTheory.Functor

universe u

/-- Restriction of abelian sheaves along a continuous and cocontinuous functor of sites preserves
finite colimits, being the left adjoint of the direct image along the cocontinuous functor. -/
theorem preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (v : C ⥤ D)
    [v.IsContinuous J K] [v.IsCocontinuous J K]
    [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, v.op.HasPointwiseRightKanExtension G] :
    PreservesFiniteColimits (v.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K) :=
  have h1 : PreservesColimitsOfSize.{u + 1, u + 1}
      (v.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K) :=
    (v.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1} J K).leftAdjoint_preservesColimits
  have h2 : PreservesColimitsOfSize.{0, 0}
      (v.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K) :=
    @preservesColimitsOfSize_shrink _ _ _ _ _ h1
  ⟨fun _ _ _ => @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _ h2 _ _⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of abelian sheaves to the lisse-étale site is additive. -/
theorem additive_subsiteRestriction (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
    (subsiteRestriction B S hS 𝒵.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒵)).Additive :=
  have := isContinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
  have := isCocontinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianRestriction.{u + 1, u, u + 1, u, u + 1}
    (inclusionTopology.{u, w} B S hS 𝒵)
    (associatedTopology B S hS 𝒵.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒵).ι

/-- Restriction of abelian sheaves to the lisse-étale site preserves finite colimits. -/
theorem preservesFiniteColimits_subsiteRestriction (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
    PreservesFiniteColimits (subsiteRestriction B S hS 𝒵.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒵)) :=
  have := isContinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
  have := isCocontinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{u + 1, u,
      u + 1, u, u + 1}
    (inclusionTopology.{u, w} B S hS 𝒵)
    (associatedTopology B S hS 𝒵.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒵).ι

/-- Restriction of abelian sheaves to the lisse-étale site preserves finite limits, being a right
adjoint. -/
theorem preservesFiniteLimits_subsiteRestriction (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
    PreservesFiniteLimits (subsiteRestriction B S hS 𝒵.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒵)) :=
  have := isContinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
  have := isCocontinuous_inclusion.{u, w} B S hS 𝒵 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒵)
  inferInstance

/-- **Stacks 07AV, first identity, for abelian sheaves on the lisse-étale sites:
`g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹`.** Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks, `Rf_*`
and `Rf'_*` total right derived functors of the direct images along `f` and along its restriction
`f'` to the lisse-étale sites, and `g⁻¹`, `(g')⁻¹` restriction of abelian sheaves to the
lisse-étale sites of `𝒴` and `𝒳`. Then, on the unbounded derived categories,

`(g')⁻¹ ⋙ Rf'_* ≅ Rf_* ⋙ g⁻¹`.

No hypothesis is made beyond the right derived functor properties of `Rf_*` and `Rf'_*` (a right
derived functor being determined only up to unique isomorphism). The isomorphism is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit` at the degree-zero
identification `AlgebraicGeometry.Stack.LisseEtale.isIso_abelianSheafBaseChange` and at
`AlgebraicGeometry.Stack.LisseEtale.isIso_derivedPushforwardUnit_restriction`. -/
@[stacks 07AV "the lisse-étale case for abelian sheaves, first identity, for every smooth \
1-morphism f : 𝒳 ⟶ 𝒴 of algebraic stacks (the setup of Stacks 07AT (1)): \
g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹ on the unbounded derived categories, as an isomorphism \
(g')⁻¹ ⋙ Rf'_* ≅ Rf_* ⋙ g⁻¹ for every pair of total right derived functors Rf_*, Rf'_* \
of the two direct images, the canonical ones included, with nothing assumed. \
The degree-zero square of Stacks 07AT (1) and the fact that \
restricted K-injective complexes compute Rf'_* (Stacks 07AK at the 2-fibre products V ×_y 𝒳, the \
content of Stacks 0GR3) are proved, not assumed"]
def derivedRestrictionBaseChangeIso
    (Rf : DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}))
    (Rf' : DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒴) AddCommGrpCat.{u + 1}))
    (αf : haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
        (etaleTopology B)).2
      haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).Additive :=
        Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
      (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
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
    [hRf : Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))]
    [hRf' : Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
      (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))] :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒴 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒴)
    haveI := additive_subsiteRestriction B S hS 𝒳
    haveI := additive_subsiteRestriction B S hS 𝒴
    haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒳
    haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒴
    haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒳
    haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒴
    (subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (subsiteRestriction B S hS 𝒴.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒴)).mapDerivedCategory :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒴 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒴)
  haveI := additive_subsiteRestriction B S hS 𝒳
  haveI := additive_subsiteRestriction B S hS 𝒴
  haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒳
  haveI := preservesFiniteLimits_subsiteRestriction B S hS 𝒴
  haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒳
  haveI := preservesFiniteColimits_subsiteRestriction B S hS 𝒴
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
    (inclusionTopology.{u, w} B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit
    (subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
    (subsiteRestriction B S hS 𝒴.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒴))
    _ _ Rf Rf' αf αf' (@asIso _ _ _ _ _ (isIso_abelianSheafBaseChange B S hS f hf)).symm
    (fun I hI => isIso_derivedPushforwardUnit_restriction B S hS f hf Rf' αf' hRf' I hI)

attribute [local instance] hasPointwiseRightKanExtension_subsiteFunctor_ab
  hasPointwiseRightKanExtension_homFunctor_ab

/-- The total right derived direct image of abelian sheaves along a 1-morphism of algebraic
stacks, for the étale sites. -/
abbrev derivedAbelianDirectImage :
    DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}) :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The total right derived direct image of abelian sheaves along the restriction of a smooth
1-morphism of algebraic stacks to the lisse-étale sites. -/
abbrev derivedAbelianSubsiteDirectImage :
    DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒴) AddCommGrpCat.{u + 1}) :=
  haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
    (inclusionTopology.{u, w} B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (inclusionTopology.{u, w} B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (inclusionTopology.{u, w} B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison exhibiting `derivedAbelianDirectImage` as a right derived functor. -/
abbrev derivedAbelianDirectImageUnit :
    haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      (etaleTopology B)).2
    haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).Additive :=
      Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
    (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedAbelianDirectImage B S hS f :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison exhibiting `derivedAbelianSubsiteDirectImage` as a right derived functor. -/
abbrev derivedAbelianSubsiteDirectImageUnit :
    haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
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
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedAbelianSubsiteDirectImage B S hS f hf :=
  haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
    (inclusionTopology.{u, w} B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (inclusionTopology.{u, w} B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (inclusionTopology.{u, w} B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The inverse image of abelian sheaves along a 1-morphism of algebraic stacks, for the étale
sites, on the unbounded derived categories: it is restriction along the underlying functor of the
1-morphism, which is exact. -/
abbrev derivedAbelianInverseImage :
    DerivedCategory (Sheaf (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}) :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) f.hom.hom.toFunctor
  (f.hom.hom.toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapDerivedCategory

/-- The inverse image of abelian sheaves along the restriction of a smooth 1-morphism to the
lisse-étale sites, on the unbounded derived categories. -/
abbrev derivedAbelianSubsiteInverseImage :
    DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒴) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}) :=
  haveI := isContinuous_subsiteFunctor.{u, w} B S hS f hf
  haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf))
  ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)).mapDerivedCategory

/-- **Stacks 07AV, second identity, for abelian sheaves on the lisse-étale sites:
`L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_!`.** For a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, with
`Lg_!` and `L(g')_!` the derived lower shrieks of **Stacks 07AS** (1) for `𝒴` and `𝒳`, and `f⁻¹`,
`(f')⁻¹` the inverse images along `f` and along its restriction `f'` to the lisse-étale sites,

`Lg_! ⋙ f⁻¹ ≅ (f')⁻¹ ⋙ L(g')_!`

on the unbounded derived categories of abelian sheaves. All four functors are the canonical ones
and no hypothesis is made. The isomorphism is the conjugate, under the composites of the derived
adjunctions `Lg_! ⊣ g⁻¹`, `L(g')_! ⊣ (g')⁻¹` of Stacks 07AS (1) and `f⁻¹ ⊣ Rf_*`,
`(f')⁻¹ ⊣ Rf'_*` (exact left adjoints), of the first identity
`AlgebraicGeometry.Stack.LisseEtale.derivedRestrictionBaseChangeIso`. -/
@[stacks 07AV "the lisse-étale case for abelian sheaves, second identity: \
L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_! on the unbounded derived categories, as an isomorphism \
Lg_! ⋙ f⁻¹ ≅ (f')⁻¹ ⋙ L(g')_! of the canonical functors, with nothing assumed: the derived \
lower shrieks are those of Stacks 07AS (1), and the four derived adjunctions are constructed"]
def derivedLowerShriekBaseChangeIso :
    derivedAbelianLowerShriek.{u, w} B S hS 𝒴 ⋙ derivedAbelianInverseImage B S hS f ≅
      derivedAbelianSubsiteInverseImage B S hS f hf ⋙ derivedAbelianLowerShriek.{u, w} B S hS 𝒳 :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  haveI := isContinuous_subsiteFunctor.{u, w} B S hS f hf
  haveI := isCocontinuous_subsiteFunctor.{u, w} B S hS f hf
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) f.hom.hom.toFunctor
  haveI := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous
    (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴)
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf))
  haveI : (f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI : ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
    AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
    (inclusionTopology.{u, w} B S hS 𝒴)).Additive :=
    Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, u + 1} _ _ _
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((f.hom.hom.toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
        (inclusionTopology.{u, w} B S hS 𝒴)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  let adjf := derivedAdjunctionOfExactLeftAdjoint
    (f.hom.hom.toFunctor.sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)))
    (derivedAbelianDirectImage B S hS f) (derivedAbelianDirectImageUnit B S hS f)
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian
  let adjf' := derivedAdjunctionOfExactLeftAdjoint
    ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
      (smoothObject_map.{u, w} B S hS f hf)).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳) (inclusionTopology.{u, w} B S hS 𝒴))
    (derivedAbelianSubsiteDirectImage B S hS f hf)
    (derivedAbelianSubsiteDirectImageUnit B S hS f hf)
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian
  (conjugateIsoEquiv (adjf'.comp (derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒳))
    ((derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒴).comp adjf)).symm
    (derivedRestrictionBaseChangeIso B S hS f hf (derivedAbelianDirectImage B S hS f)
      (derivedAbelianSubsiteDirectImage B S hS f hf) (derivedAbelianDirectImageUnit B S hS f)
      (derivedAbelianSubsiteDirectImageUnit B S hS f hf))

end AlgebraicGeometry.Stack.LisseEtale
