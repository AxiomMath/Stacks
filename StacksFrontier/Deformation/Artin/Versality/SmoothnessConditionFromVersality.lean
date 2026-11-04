module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.FieldPointImage
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension
public import StacksFrontier.Deformation.Artin.Versality.Openness

/-!
# The smoothness condition from versality at every finite type point

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian
scheme `S`, let `U` be a scheme locally of finite type over `S`, and let `x` be an object of
`𝒳` over `U`. If `x` is versal at every finite type point of `U` and `𝒳` satisfies the
Rim–Schlessinger condition (RS), then the 1-morphism `x : (Sch/U)_fppf ⟶ 𝒳` satisfies the
deformation-theoretic smoothness condition of Tag 07XS.

## Main results

* `Deformation.Artin.isSmoothOnPredeformationCategories_sliceFunctor_of_isVersalAt` —
  the statement above, Tag 07XT.

## Implementation notes

The condition of Tag 07XS quantifies over the field-valued points `Spec(l) ⟶ U` of finite
type over `S`. Such a point is locally of finite type over `U` as well, because its
composite with `U ⟶ S` is, so its image `u₀` is a finite type point of `U` and `l` is a
finite extension of the residue field `κ(u₀)`
(`AlgebraicGeometry.isFiniteTypePoint_of_locallyOfFiniteType` and
`AlgebraicGeometry.finite_fieldPointResidueEmbedding`, the content of Morphisms, Section
29.16 that the source cites). The point then factors through `Spec(κ(u₀))` by the canonical
embedding, which is exactly the hypothesis of Tag 07XG in
`Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt`; that lemma applied at
`u₀` is the conclusion.

The 1-morphism `x : (Sch/U)_fppf ⟶ 𝒳` is the 2-Yoneda functor
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` built from the chosen pullbacks of
`𝒳`, which is the form in which Tag 07XS is stated in this development. Neither the
quasi-compactness of `Spec(l) ⟶ S` nor the open immersion hypothesis that Tag 07XS carries
along is used.

## References

* [Stacks Project, Tag 07XT](https://stacks.math.columbia.edu/tag/07XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
variable (x : X)

/-- **Stacks 07XT.** Let `𝒳` be a category fibred in groupoids over the big fppf site of a
locally Noetherian scheme `S`, let `U` be a scheme locally of finite type over `S`, and let
`x` be an object of `𝒳` over `U`. If `x` is versal at every finite type point of `U` and
`𝒳` satisfies (RS), then the 1-morphism `x : (Sch/U)_fppf ⟶ 𝒳` satisfies the smoothness
condition of Tag 07XS on predeformation categories. -/
@[stacks 07XT]
public theorem isSmoothOnPredeformationCategories_sliceFunctor_of_isVersalAt
    [IsLocallyNoetherian S] (hp : p.IsFiberedInGroupoids)
    (hU : LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
    (hversal : ∀ u₀ : ((p ⋙ Over.post B.inclusion).obj x).left,
      AlgebraicGeometry.IsFiniteTypePoint u₀ →
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x)
          (p ⋙ Over.post B.inclusion) u₀ x rfl)
    (hRS : SatisfiesRS B S hS p hp) :
    letI : p.IsFibered := hp.isFibered
    IsSmoothOnPredeformationCategories B S hS (Over.forget (p.obj x)) p
      (p.chosenPullbacks.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (p.chosenPullbacks.sliceFunctor_comp (⟨x, rfl⟩ : p.Fiber (p.obj x))) := by
  let : p.IsFibered := hp.isFibered
  intro Λ' l' _ _ _ jΛ y₀ hy₀ hft _ _
  let U := (p ⋙ Over.post B.inclusion).obj x
  let g : Spec (.of l') ⟶ U.left := fieldPointMap B S hS p x jΛ y₀ hy₀
  have hgcomp : LocallyOfFiniteType (g ≫ U.hom) := by
    rwa [fieldPointMap_comp_hom B S hS p x jΛ y₀ hy₀]
  have hg : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g U.hom
  let u₀ : U.left := fieldPointImage g
  have hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀ :=
    isFiniteTypePoint_of_locallyOfFiniteType g hg
  let : Algebra (U.left.residueField u₀) l' :=
    (fieldPointResidueEmbedding g).hom.toAlgebra
  have : Module.Finite (U.left.residueField u₀) l' :=
    finite_fieldPointResidueEmbedding g hg
  exact isSmooth_mapPredeformationCategory_of_isVersalAt B S hS p x jΛ y₀ hy₀ hp hU u₀ hu₀
    (SpecMap_fieldPointResidueEmbedding_fromSpecResidueField g).symm (hversal u₀ hu₀) hRS

end Deformation.Artin

end
