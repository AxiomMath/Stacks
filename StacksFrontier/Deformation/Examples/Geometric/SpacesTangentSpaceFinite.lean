module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceLinearEquivExt
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalExt

/-!
# The tangent space of the deformation category of a proper algebraic space is finite

In Example 0E3Z let `X` be an algebraic space over the field `k`, proper over `k`. The tangent
space `T Def_X` of its deformation category, with the vector-space structure of Stacks 06IH, is a
finite-dimensional `k`-vector space: the tangent-space clause of [Stacks Project, Tag 0E42].

The proof is the source's: by the second display of Stacks 0E41
(`Deformation.Examples.spaceTangentSpaceLinearEquivExt`) `T Def_X = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`,
which is finite dimensional because `NL_{X/k}` has coherent cohomology sheaves, zero outside
degrees `-1` and `0` (Stacks 0D0Z), and `X` is proper (Stacks 0D0T):
`Deformation.Examples.moduleFinite_spaceNaiveCotangentExt` at `i = 1`.

## Main results

* `Deformation.Examples.spaceTangentSpace_finiteDimensional`

## References

* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **Stacks 0E42, the tangent space.** In Lemma 0E41, if the algebraic space `X` is proper over
`k`, then `T Def_X` (with the vector-space structure of Stacks 06IH) is finite dimensional over
`k`. -/
@[stacks 0E42 "tangent space: for an algebraic space X proper over the field k, the tangent space \
T Def_X of its deformation category (isomorphism classes of flat deformations over k[eps], with \
the canonical vector space structure of 06IH) is finite dimensional over k. The clause on \
Inf(Def_X) is registered separately"]
theorem spaceTangentSpace_finiteDimensional (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK) :
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
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses
        (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
        (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
          toK).predeformation.cofibered)) := by
  let : Fact (IsPredeformationCategory
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK)).p) :=
    ⟨(isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
        toK).predeformation.cofibered))) :=
    ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK)⟩
  let := HasDerivedCategory.standard
    (Space.NaiveCotangentModules B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
  let := Space.naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
    (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
  have h := moduleFinite_spaceNaiveCotangentExt B hΛ hSpec X hX toK hproper 1
  exact Module.Finite.equiv (spaceTangentSpaceLinearEquivExt B hΛ hSpec X hX toK).symm

end Deformation.Examples

end
