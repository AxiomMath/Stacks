module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.Deformation.Examples.BaseCategoryOverItself
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverRings
public import StacksFrontier.Deformation.Examples.Geometric.SchemesUnobstructed
public import StacksFrontier.Deformation.Smooth.FullVertical

/-!
# Stacks Tag 0DZQ, with every input proved

In Example 0DY7 let `X` be a scheme over a field `k` which is separated and of finite type over
`k`, of dimension at most one, a local complete intersection over `k`, and smooth over `k`
outside finitely many points. Then the deformation category `Def_X` is unobstructed: its
structure morphism over `𝒞_Λ` is smooth.

`Deformation.Examples.isSmooth_baseProjection_schemeDeformationCategoryProjection` proves this
from four further inputs. Each of them is a theorem of this library, proved below, so the
statement here has exactly the source's hypotheses.

## Main results

* `Stacks.HQuasiProjectiveDimensionOne.ampleOfNoetherianSeparatedDimLEOne`: a Noetherian
  separated scheme of dimension at most one has an ample invertible module, which is Tag 09NZ as
  proved in
  `Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`
* `Deformation.Examples.smoothSectionsOfSmoothAffineOpen`: on an affine open on which a scheme
  over `k` is smooth, the sections form a smooth `k`-algebra.
* `Deformation.Examples.gluingComparisonSmooth`: in every gluing situation of Situation 0DYY the
  comparison `Def_X ⟶ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` is smooth, being an equivalence over
  `𝒞_Λ` by Tag 0DYZ (`Deformation.Examples.GluingSituation.ringDeformationEquivalenceOver`).
* `Deformation.Examples.isSmooth_baseProjection_schemeDeformationCategoryProjection_of_lci`:
  **Stacks 0DZQ**.

The Rim–Schlessinger condition for `𝒞_Λ` over itself is `Deformation.isDeformationCategory_id`.

## References

* [Stacks Project, Tag 0DZQ](https://stacks.math.columbia.edu/tag/0DZQ)
* [Stacks Project, Tag 0DYZ](https://stacks.math.columbia.edu/tag/0DYZ)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.HQuasiProjectiveDimensionOne

/-- Every Noetherian separated scheme of topological Krull dimension at most one has an ample
invertible module (Tag 09NZ). -/
theorem ampleOfNoetherianSeparatedDimLEOne : AmpleOfNoetherianSeparatedDimLEOne.{u} :=
  fun Y _ _ hdim =>
    Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
      Y hdim

end Stacks.HQuasiProjectiveDimensionOne

namespace Deformation.Examples

/-- On an affine open `U` of a scheme `X` over a field `k` on which the structure morphism is
smooth, the sections `Γ(X, U)` form a smooth `k`-algebra. -/
theorem smoothSectionsOfSmoothAffineOpen (k : Type u) [Field k] :
    SmoothSectionsOfSmoothAffineOpen.{u} k := by
  intro X f U hU hsm
  let := sectionsAlgebra f U
  have he : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.isoSpec.inv ≫ U.ι ≫ f := by
    rw [← isoSpec_hom_comp_specMap_algebraMap f hU, Iso.inv_hom_id_assoc]
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) := by
    rw [he]
    infer_instance
  exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff (P := @Smooth).mp h)

/-- In every gluing situation of Situation 0DYY the comparison morphism
`Def_X ⟶ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}` along the two restriction morphisms is smooth: it is an
equivalence over `𝒞_Λ` by Tag 0DYZ. -/
theorem gluingComparisonSmooth (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] :
    GluingComparisonSmooth Λ k := fun S =>
  ⟨GluingSituation.chartRestrictLeft S, GluingSituation.chartRestrictRight S,
    ⟨GluingSituation.ringComparisonFunctor S,
      GluingSituation.ringComparisonFunctor_comp_projection S⟩,
    isSmooth_of_equivalenceOver (GluingSituation.ringDeformationEquivalenceOver S) _ rfl⟩

/-- **[Stacks, Tag 0DZQ].** Let `X` be a scheme over a field `k` which is separated and of finite
type over `k`, of dimension at most one, a local complete intersection over `k`, and smooth over
`k` outside a finite set of points. Then the deformation category `Def_X` of Example 0DY7 is
unobstructed: its structure morphism over `𝒞_Λ` is smooth. -/
@[stacks 0DZQ, sga "7 VI 4.10" "(a)", sga "7 VI 4.13" "(b), special case"]
theorem isSmooth_baseProjection_schemeDeformationCategoryProjection_of_lci {Λ k : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (hdim : topologicalKrullDim (X.left : Type u) ≤ 1)
    (hlci : IsLocalCompleteIntersectionOverField X.hom)
    (hfinite : ((X.hom.smoothLocus : Set X.left)ᶜ).Finite) :
    IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)) :=
  isSmooth_baseProjection_schemeDeformationCategoryProjection
    Stacks.HQuasiProjectiveDimensionOne.ampleOfNoetherianSeparatedDimLEOne
    (isDeformationCategory_id.{u, u, u} Λ k) (gluingComparisonSmooth Λ k)
    (smoothSectionsOfSmoothAffineOpen k) X hdim hlci hfinite

end Deformation.Examples

end
