module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.SmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ArtinianAtlas
import StacksCore.Tactic.StacksAttribute

/-!
# Finite-dimensionality of the tangent space and infinitesimal automorphisms

Let `S` be a locally Noetherian scheme, `𝒳` an algebraic stack over `S`, `U` a scheme locally of
finite type over `S` and `(Sch/U)_{fppf} ⟶ 𝒳` a smooth surjective 1-morphism. For every field `k`
of finite type over `S`, every affine open `Spec Λ ⊆ S` through which `Spec k ⟶ S` factors with
`Λ → k` finite (Section 07T2), and every object `x₀` of `𝒳` over `Spec k`, the tangent space
`T𝓕_{𝒳,k,x₀}` and the infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x₀})` are finite-dimensional over
`k`.

The vector-space structures are those of the deformation category `𝓕_{𝒳,k,x₀}`, and the
statement is made with `Deformation.IsFiniteDimensionalDeformationCategory`, which records the
deformation category together with the two finiteness assertions.

The smooth surjective 1-morphism is spelled out: it is representable by algebraic spaces, and
every algebraic space representing a base change along a scheme-valued point has surjective and
smooth structure morphism.

## Main results

* `Deformation.Artin.isFiniteDimensionalDeformationCategory_of_algebraicStack`: the tangent space
  and the infinitesimal automorphisms of `𝓕_{𝒳,k,x₀}` are finite-dimensional over `k`.

## References

* [Stacks Project, Tag 07X1](https://stacks.math.columbia.edu/tag/07X1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `S` be a locally Noetherian scheme, `𝒳` an algebraic stack over `S`, `U` a scheme locally
of finite type over `S` and `f : (Sch/U)_{fppf} ⟶ 𝒳` a smooth surjective 1-morphism. Then for every
`𝓕 = 𝓕_{𝒳,k,x₀}` as in Section 07T2 — `k` a field of finite type over `S`, `Spec Λ ⊆ S` an affine
open through which `Spec k ⟶ S` factors with `Λ → k` finite, `x₀` an object of `𝒳` over `Spec k`
— the tangent space `T𝓕` and the infinitesimal automorphisms `Inf(𝓕)` are finite-dimensional over
`k`, for the vector-space structures of the deformation category `𝓕`. -/
@[stacks 07X1]
theorem isFiniteDimensionalDeformationCategory_of_algebraicStack [IsLocallyNoetherian S]
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (f : Stack.schemeFibredCategory B S hS U ⟶ 𝒳.val)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsmoothsurj : ∀ (W : BigFppfOver B S hS)
      (yv : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
      (_hyv : yv ⋙ 𝒳.val.val.p = Over.map W.hom)
      (F : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B W.left.1 W.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W.hom) (Stack.schemeFibredCategory B S hS U).val.p
          𝒳.val.val.p yv (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS W
        ((spacesOverSmallerBaseFunctor B W.left.1 S W.left.2 hS W.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ) (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    letI := (predeformationCategory iΛ (𝒳.val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).category
    IsFiniteDimensionalDeformationCategory
      (predeformationCategory iΛ (𝒳.val.val.p ⋙ Over.post B.inclusion) x₀ hx₀).projection :=
  isFiniteDimensionalDeformationCategory_of_smoothChart 𝒳.val
    (satisfiesRS_of_isAlgebraicStack B S hS 𝒳) U f hf hsmoothsurj iΛ hiΛ x₀ hx₀ hfinite

end Deformation.Artin
