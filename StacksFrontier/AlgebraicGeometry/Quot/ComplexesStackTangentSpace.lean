module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicityReduction
public import StacksFrontier.Deformation.Artin.TangentSpaceVectorStructure
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# Tangent spaces of `Complexes_{X/B}` (towards Stacks 0DLL)

Stacks 0DLL asserts that, in Situation 0DLE with `S` locally Noetherian and `B ⟶ S` locally of
finite presentation, for every field `k` of finite type over `S` and every object `x₀` of
`𝒳 = Complexes_{X/B}` over `Spec k`, the tangent space `T𝓕_{𝒳,k,x₀}` and the infinitesimal
automorphisms `Inf(𝓕_{𝒳,k,x₀})` of Artin's Axioms, Section 07WY, are finite dimensional.  In the
library the two vector spaces are `Deformation.Artin.tangentSpaceModuleOfSatisfiesRS` and
`Deformation.Artin.infinitesimalAutomorphismModuleOfSatisfiesRS` of Stacks 07WY, formed from (RS)
(Stacks 0DLK).  The packaged condition `Deformation.IsFiniteDimensionalDeformationCategory`
cannot be stated here: it fixes the hom universe of the category to be at most that of `k`,
and the morphisms of `Complexes_{X/B}` live one universe higher.

This file connects that form to the form in which Artin's criterion, Stacks 07Y4, consumes axiom
[3], at the stalks of the base: the hypothesis `h0DLL` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`.  Nothing here is
registered.

## Main results

* `Deformation.finiteDimensional_artinianTangentSpace_of_tangentSpaceArtinian`: finite
  dimensionality of the tangent space passes from the lifted model
  `Deformation.tangentSpaceArtinian` to the unlifted model `Deformation.artinianTangentSpace`.
* `Deformation.Artin.finiteDimensional_artinianTangentSpace_stalk_of_finiteDimensional`: for
  any category over the big fppf site of `S`, finite dimensionality of every
  `𝓕_{𝒳,k,x₀}` gives the axiom [3] clause of Stacks 07Y4 at the stalks of `S`.

At `p := complexesFunctor D` over `S = Spec Λ`, with `hp` from Stacks 0DLF and `hRS` from Stacks
0DLK, the conclusion of the second result is literally the hypothesis `h0DLL` of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_artinCriterion`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 07WY](https://stacks.math.columbia.edu/tag/07WY)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w u₁ v₁

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- If the tangent space of a predeformation category satisfying Schlessinger's condition (S2) is
finite dimensional in the lifted model `Deformation.tangentSpaceArtinian` (the form of Stacks
07WY and of `Deformation.IsFiniteDimensionalDeformationCategory`), then it is finite dimensional
in the unlifted model `Deformation.artinianTangentSpace` (the form of Stacks 07Y4), for the
vector-space structures of Stacks 06IH on both, by the comparison
`Deformation.tangentSpaceArtinianLinearEquivUnlifted`.  This is the converse of
`Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace`. -/
theorem finiteDimensional_artinianTangentSpace_of_tangentSpaceArtinian
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    (h : letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
         letI : Fact (SchlessingerConditionS2
           (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
         FiniteDimensional k
           (tangentSpaceArtinian.{u, w, w} Λ k (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)) := by
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
  let : FiniteDimensional k
    (tangentSpaceArtinian.{u, w, w} Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)) := h
  exact (tangentSpaceArtinianLinearEquivUnlifted 𝓖 h𝓖 hS2).finiteDimensional

end Deformation

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hRS : SatisfiesRS B S hS p hp)

/-- **Axiom [3] of Stacks 07Y4 at the stalks, from the vector spaces of Stacks 07WY.**  Let `p`
be fibred in groupoids over the big fppf site of `S` and satisfy (RS).  If the tangent space
`T𝓕_{𝒳,k,x₀}` of Stacks 07WY (`Deformation.Artin.tangentSpaceModuleOfSatisfiesRS`) is finite
dimensional for every field `k` of finite type over `S` presented through `Spec k ⟶ Spec Λ ⟶ S`
and every `x₀` over `Spec k`, then it is finite dimensional in the form Artin's criterion
consumes: at the presentation through the stalk `Λ = 𝒪_{S,s}` of `S` at the image `s` of the
point, for the tangent space `Deformation.artinianTangentSpace` of the functor of isomorphism
classes with the vector-space structure `Deformation.associatedTangentSpaceModuleUnlifted`, for
every witness `hD` that `𝓕_{𝒳,k,x₀}` is a deformation category. -/
theorem finiteDimensional_artinianTangentSpace_stalk_of_finiteDimensional
    (h : ∀ (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
      (x₀ : 𝒳) (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
      FiniteDimensional k (tangentSpaceModuleOfSatisfiesRS B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc)) :
    ∀ (k : Type u) [Field k] (i₀ : Spec (.of k) ⟶ S) (x₀ : 𝒳)
      (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀),
      LocallyOfFiniteType i₀ → QuasiCompact i₀ →
      ∀ (s : S), i₀ (IsLocalRing.closedPoint k) = s →
      ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
        (_hΛstalk : Λ' = S.presheaf.stalk s)
        (iΛ : Spec (.of Λ') ⟶ S)
        (_hiΛ : HEq iΛ (S.fromSpecStalk s))
        (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ = i₀),
        let hx : (p ⋙ Over.post B.inclusion).obj x₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ) :=
          hx₀.trans (congrArg Over.mk hbase.symm)
        let P := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx
        letI : Category P.carrier := P.category
        ∀ hD : IsDeformationCategory P.projection,
          let 𝓕 := BasedCategory.ofFunctor P.projection
          let hS2 := schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
          letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
          letI : Fact (SchlessingerConditionS2
            (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
          let F := isomorphismClasses 𝓕 hD.predeformation.cofibered
          let T := artinianTangentSpace Λ' k F
          letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
          letI : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
          FiniteDimensional k T := by
  intro k _ i₀ x₀ hx₀ hfin hqc s _ Λ' _ _ _ iΛ _ hbase hx P hD 𝓕 hS2
  intros
  exact Deformation.finiteDimensional_artinianTangentSpace_of_tangentSpaceArtinian 𝓕
    hD.predeformation hS2 (h Λ' k iΛ x₀ hx (hbase ▸ hfin) (hbase ▸ hqc))

end Deformation.Artin
