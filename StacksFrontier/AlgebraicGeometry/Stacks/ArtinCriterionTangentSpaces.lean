module

public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# The tangent-space hypothesis of Artin's criterion from finite-dimensional deformation categories

Artin's criterion (Stacks 07Y4), in the form
`AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`, asks for the tangent-space half
of axiom [3] as `AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces`: for every finite
type field `k` over `S`, every object `x₀` over `Spec(k)` and every presentation of the local ring
of `S` at the image point, the tangent space `T𝓕_{𝒳,k,x₀}` of the predeformation category, in the
unlifted model `Deformation.artinianTangentSpace` with its canonical vector space structure, is
finite dimensional.

The lemmas of the source verifying axiom [3] for a moduli stack (for instance Stacks 0D4S (1)
for polarized schemes) conclude instead that the predeformation category is a deformation
category with finite-dimensional tangent space and infinitesimal automorphisms, which is
`Deformation.IsFiniteDimensionalDeformationCategory`, phrased with the lifted model
`Deformation.tangentSpaceArtinian`. This file passes from the second form to the first: the two
models are `k`-linearly equivalent by `Deformation.tangentSpaceArtinianLinearEquivUnlifted`.

## Main results

* `Stack.hasFiniteDimensionalTangentSpaces_of_isFiniteDimensionalDeformationCategory`: if every
  predeformation category is a finite-dimensional deformation category, then
  `HasFiniteDimensionalTangentSpaces` holds.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07XJ](https://stacks.math.columbia.edu/tag/07XJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u uX

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The tangent-space half of axiom [3] from finite-dimensional deformation categories.** If,
for every field `k`, every factorization `Spec(k) ⟶ Spec(Λ) ⟶ S` of finite type and every object
`x₀` of `𝒳` over `Spec(k)`, the predeformation category `𝓕_{𝒳,k,x₀}` relative to `Λ` is a
deformation category with finite-dimensional tangent space and infinitesimal automorphisms, then
`𝒳` satisfies the tangent-space hypothesis of Artin's criterion. -/
theorem hasFiniteDimensionalTangentSpaces_of_isFiniteDimensionalDeformationCategory
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, uX} (AlgebraicGeometry.BigFppfOver B S hS))
    (h : ∀ (k : Type u) [Field k] (Λ : Type u) [CommRing Λ] [Algebra Λ k]
      (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳.val.obj)
      (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
      letI D := Deformation.Artin.predeformationCategory iΛ
        (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx₀
      letI : Category D.carrier := D.category
      Deformation.IsFiniteDimensionalDeformationCategory.{u, u, u} D.projection) :
    HasFiniteDimensionalTangentSpaces B S hS 𝒳 := by
  intro k _ i₀ x₀ hx₀ hlft hqc s _ Λ _ _ _ iΛ _ hbase hx D hD 𝓕 hS2
  intros
  have hlft' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    hbase ▸ hlft
  have hqc' : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    hbase ▸ hqc
  obtain ⟨hp, hfin, -⟩ := h k Λ iΛ x₀ hx hlft' hqc'
  have : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  have : Fact (Deformation.SchlessingerConditionS2 (Functor.Elements.π
      (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
  have : FiniteDimensional k (Deformation.tangentSpaceArtinian.{u, u, u} Λ k
      (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered)) := hfin
  exact (Deformation.tangentSpaceArtinianLinearEquivUnlifted 𝓕 hD.predeformation
    hS2).finiteDimensional

end AlgebraicGeometry.Stack

end
