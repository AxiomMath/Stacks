module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceRankOneExtComparison
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceInjective
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjective

/-!
# The tangent space of the deformation category of an algebraic space

In the situation of Stacks 0E3Z let `X` be an algebraic space over the field `k`. This file
proves the second display of [Stacks Project, Tag 0E41]:

`T Def_X = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`,

as a `k`-linear equivalence from the tangent space of Stacks 06IH (with its canonical
vector-space structure) of the deformation category `Def_X` to `Ext¹` of the naive cotangent
complex `NL_{X/k}` of Stacks 0D0V.

The proof is the source's: an element of `T Def_X` is an isomorphism class of flat deformations
`X'` of `X` over `k[ε]`, and its structure sheaf read on `X` is an extension
`0 ⟶ 𝒪_X ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_{Spec k}`-algebras, whose class (Stacks 0GQ5) lies in
`Ext¹(NL_{X/k}, 𝒪_X)`. The classes are defined over every `k[V]`, natural in `V`
(`Deformation.Examples.spaceTangentExtClassAt_naturality`), and bijective at `V = k`
(`Deformation.Examples.spaceTangentExtClassAt_injective`: Stacks 05YZ and 05Z1;
`Deformation.Examples.surjective_spaceTangentExtClassAt`: Stacks 0GQ5 and 05ZT); the naturality
makes the bijection `k`-linear for the vector-space structure of Stacks 06IH
(`Deformation.tangentSpaceLinearEquivOfNaturalBijection`, Stacks 06IJ), and
`Deformation.Examples.spaceTangentExtRankOneLinearEquiv` reads the value at `k` as `Ext¹` of 0D0V.

## Main definitions

* `Deformation.Examples.spaceTangentSpaceLinearEquivExtModel`: `T Def_X` is the value at `k` of the
  receptacle `V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)` on the model of the small étale site.
* `Deformation.Examples.spaceTangentSpaceLinearEquivExt`: `T Def_X ≃ₗ[k] Ext¹(NL_{X/k}, 𝒪_X)`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **The class map at `V = k` is bijective**: injective by Stacks 05YZ and 05Z1, surjective by
Stacks 0GQ5 and 05ZT. -/
theorem spaceTangentExtClassAt_bijective :
    Function.Bijective (spaceTangentExtClassAt B hΛ hSpec X hX toK (FGModuleCat.of k k)) :=
  ⟨spaceTangentExtClassAt_injective B hΛ hSpec X hX toK,
    surjective_spaceTangentExtClassAt B hΛ hSpec X hX toK⟩

/-- **`T Def_X` is the value at `k` of the receptacle `V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)`** on the
model of the small étale site, `k`-linearly for the vector-space structure of Stacks 06IH: the
class map on isomorphism classes of deformations over `k[ε]`, made linear by its naturality in
`V`. -/
def spaceTangentSpaceLinearEquivExtModel :
    letI : Fact (IsPredeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK)).p) :=
      ⟨(isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
          toK).predeformation.cofibered))) :=
      ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK)⟩
    artinianTangentSpace Λ k (isomorphismClasses
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
          toK).predeformation.cofibered) ≃ₗ[k]
      (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj (FGModuleCat.of k k) :=
  tangentSpaceLinearEquivOfNaturalBijection
    (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
    (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation
    (Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK))
    (spaceTangentExtFunctor B hΛ hSpec X hX toK)
    (spaceTangentExtClassAt B hΛ hSpec X hX toK)
    (fun g z => spaceTangentExtClassAt_naturality B hΛ hSpec X hX toK g z)
    (spaceTangentExtClassAt_bijective B hΛ hSpec X hX toK)

/-- The model form of the second display is the class map. -/
theorem spaceTangentSpaceLinearEquivExtModel_apply
    (z : (associatedTangentSpaceSetFunctor (spaceDeformationBased B hΛ hSpec X hX toK)
      (spaceDeformation_cofibered B hΛ hSpec X hX toK)).obj (FGModuleCat.of k k)) :
    letI : Fact (IsPredeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK)).p) :=
      ⟨(isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
          toK).predeformation.cofibered))) :=
      ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK)⟩
    spaceTangentSpaceLinearEquivExtModel B hΛ hSpec X hX toK z =
      spaceTangentExtClassAt B hΛ hSpec X hX toK (FGModuleCat.of k k) z :=
  tangentSpaceLinearEquivOfNaturalBijection_apply
    (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
    (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation
    (Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK))
    (spaceTangentExtFunctor B hΛ hSpec X hX toK)
    (spaceTangentExtClassAt B hΛ hSpec X hX toK)
    (fun g z => spaceTangentExtClassAt_naturality B hΛ hSpec X hX toK g z)
    (spaceTangentExtClassAt_bijective B hΛ hSpec X hX toK) z

/-- **Stacks 0E41, second display.** In Example 0E3Z let `X` be an algebraic space over `k`. Then
`T Def_X = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`: the tangent space of the deformation category `Def_X` (the
isomorphism classes of flat deformations of `X` over `k[ε]`, with the vector-space structure of
Stacks 06IH) is `k`-linearly isomorphic to `Ext¹` of the naive cotangent complex `NL_{X/k}` of
Stacks 0D0V into `𝒪_X` (sections raised to the universe of `NL_{X/k}`, any model of the derived
category), `k` acting through the structure morphism `X ⟶ Spec k`. A deformation `X'` goes to the
class (Stacks 0GQ5) of the extension `0 ⟶ 𝒪_X ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0`
(`Deformation.Examples.spaceTangentSpaceLinearEquivExtModel_apply`). -/
@[stacks 0E41 "second display: for an algebraic space X over the field k, T Def_X = \
Ext^1(NL_{X/k}, O_X) as k-vector spaces, from the tangent space of the deformation category of X \
(isomorphism classes of flat deformations of X over k[eps], with the canonical vector space \
structure of 06IH) onto Ext^1_{O_X}(NL_{X/k}, O_X) of the naive cotangent complex of 0D0V, k \
acting through the structure morphism X -> Spec k; a deformation goes to the 0GQ5 class of the \
extension 0 -> O_X -> O_X' -> O_X -> 0. The first display is registered separately"]
def spaceTangentSpaceLinearEquivExt
    [HasDerivedCategory.{w} (Space.NaiveCotangentModules B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))] :
    letI : Fact (IsPredeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK)).p) :=
      ⟨(isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
          toK).predeformation.cofibered))) :=
      ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK)⟩
    letI := Space.naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    artinianTangentSpace Λ k (isomorphismClasses
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
          toK).predeformation.cofibered) ≃ₗ[k]
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (Space.naiveCotangentComplex B (Spec (.of Λ)) hΛ
          (spaceStructureMap B hΛ hSpec X hX toK)))
        ((DerivedCategory.singleFunctor _ 0).obj
          (Space.naiveCotangentCoefficient B (Spec (.of Λ)) hΛ
            (spaceStructureModule B hΛ (spaceOf B hΛ X hX)))) 1 :=
  letI : Fact (IsPredeformationCategory
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK)).p) :=
    ⟨(isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
        toK).predeformation.cofibered))) :=
    ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK)⟩
  letI := Space.naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
    (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
  (spaceTangentSpaceLinearEquivExtModel B hΛ hSpec X hX toK).trans
    (spaceTangentExtRankOneLinearEquiv B hΛ hSpec X hX toK)

/-- The second display is the class map followed by the comparison of `Ext¹` on the model with
`Ext¹` of Stacks 0D0V. -/
theorem spaceTangentSpaceLinearEquivExt_apply
    [HasDerivedCategory.{w} (Space.NaiveCotangentModules B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))]
    (z : (associatedTangentSpaceSetFunctor (spaceDeformationBased B hΛ hSpec X hX toK)
      (spaceDeformation_cofibered B hΛ hSpec X hX toK)).obj (FGModuleCat.of k k)) :
    letI : Fact (IsPredeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK)).p) :=
      ⟨(isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
          toK).predeformation.cofibered))) :=
      ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK)⟩
    letI := Space.naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    spaceTangentSpaceLinearEquivExt B hΛ hSpec X hX toK z =
      spaceTangentExtRankOneLinearEquiv B hΛ hSpec X hX toK
        (spaceTangentExtClassAt B hΛ hSpec X hX toK (FGModuleCat.of k k) z) :=
  congrArg (spaceTangentExtRankOneLinearEquiv B hΛ hSpec X hX toK)
    (spaceTangentSpaceLinearEquivExtModel_apply B hΛ hSpec X hX toK z)

end Deformation.Examples

end
