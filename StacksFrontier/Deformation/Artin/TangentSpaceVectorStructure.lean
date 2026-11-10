module

public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensor
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Tangent spaces of a category fibred in groupoids (Stacks Section 07WY)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, let `k` be a field of finite
type over `S` (with the affine open `Spec Λ ⊆ S` of Section 07T2) and let `x₀` be an object of
`𝒳` over `Spec k`. Section 07WY recalls the tangent space `T𝓕_{𝒳,k,x₀}` of the predeformation
category `𝓕 = 𝓕_{𝒳,k,x₀}` (display 07WZ: isomorphism classes of morphisms `x₀ ⟶ x` over
`Spec k ⟶ Spec k[ε]`) and its infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x₀})` (display 07X0),
and then states, in running text, that

* if `𝒳` satisfies (RS), `T𝓕_{𝒳,k,x₀}` carries a natural `k`-vector space structure, by
  Formal Deformation Theory, Lemma 06IH, whose assumptions hold by Lemma 07WU and Remark 07WV;
* `Inf(𝓕_{𝒳,k,x₀})` carries a natural `k`-vector space structure whose addition is composition
  of automorphisms, by Formal Deformation Theory, Lemma 06JX;
* a natural condition is to ask these vector spaces to be finite dimensional.

This file formalizes those three statements for the predeformation category
`Deformation.Artin.predeformationCategory`. The two displays carry their own tags and are
formalized elsewhere (`Deformation.Artin.squareZeroLiftClasses` for 07WZ and
`Deformation.Artin.infinitesimalAutomorphisms_equiv_restrictionKernel` for 07X0).

## Main definitions

* `Deformation.Artin.tangentSpaceModuleOfSatisfiesRS`: the `k`-vector space `T𝓕_{𝒳,k,x₀}` for
  `𝒳` satisfying (RS), with the structure of Stacks 06IH.
* `Deformation.Artin.infinitesimalAutomorphismModuleOfSatisfiesRS`: the `k`-vector space
  `Inf(𝓕_{𝒳,k,x₀})` at an object of `𝓕` over `k` and a choice of pushforwards of it, with the
  structure of Stacks 06JX.

## Main results

* `Deformation.Artin.tangentSpaceModuleOfSatisfiesRS_carrier`: the underlying set of
  `tangentSpaceModuleOfSatisfiesRS` is the set of isomorphism classes of the fibre of `𝓕` over
  the dual numbers.
* `Deformation.Artin.infinitesimalAutomorphismModuleOfSatisfiesRS_carrier`: the underlying set of
  `infinitesimalAutomorphismModuleOfSatisfiesRS` is the kernel of the restriction
  `Aut(x'₀) ⟶ Aut(x₀)`, addition is composition and scalar multiplication is transport along
  the scaling `ε ↦ cε`.
* `Deformation.Artin.isFiniteDimensionalDeformationCategory_predeformationCategory_iff`: for `𝒳`
  satisfying (RS), the condition `Deformation.IsFiniteDimensionalDeformationCategory` on
  `𝓕_{𝒳,k,x₀}` says exactly that these two vector spaces are finite dimensional.

## Implementation notes

The source assumes `S` locally Noetherian and `k` of finite type over `S`; what the
construction consumes is that `Spec k ⟶ Spec Λ ⟶ S` is locally of finite type and
quasi-compact, exactly the hypotheses of
`Deformation.Artin.isDeformationCategory_predeformationCategory` (Stacks 07WU), so local
Noetherianity is not assumed.

`Inf(𝓕)` is formed, as in Stacks 06JN, at an object `x` of `𝓕` over the residue field `k`
together with a choice `P` of pushforwards of `x`; the dual-number object `x'₀` is the chosen
pushforward of `x` to `k[ε]`. This is the form in which
`Deformation.IsFiniteDimensionalDeformationCategory` quantifies over `Inf`.

## References

* [Stacks Project, Tag 07WY](https://stacks.math.columbia.edu/tag/07WY)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 06JX](https://stacks.math.columbia.edu/tag/06JX)
* [Stacks Project, Tag 07WU](https://stacks.math.columbia.edu/tag/07WU)
* [Stacks Project, Tag 07WV](https://stacks.math.columbia.edu/tag/07WV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hRS : SatisfiesRS B S hS p hp)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- **The tangent space as a vector space.** For `𝒳` satisfying (RS), the tangent space
`T𝓕_{𝒳,k,x₀}` of the predeformation category, with the natural `k`-vector space structure of
Stacks 06IH. -/
@[stacks 07WY "if X satisfies (RS), TF_{X,k,x_0} has a natural k-vector space structure \
  (Lemma 06IH, assumptions by Lemma 07WU and Remark 07WV)"]
def tangentSpaceModuleOfSatisfiesRS : ModuleCat.{max (u + 1) v w} k :=
  let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  letI := D.category
  let hD := isDeformationCategory_predeformationCategory B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc
  letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor D.projection).p) :=
    ⟨hD.predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered))) :=
    ⟨tangentConditionS2 hD⟩
  ModuleCat.of k (tangentSpaceArtinian Λ k
    (isomorphismClasses (BasedCategory.ofFunctor D.projection) hD.predeformation.cofibered))

/-- The underlying set of the `k`-vector space `tangentSpaceModuleOfSatisfiesRS` is the tangent
space `T𝓕_{𝒳,k,x₀}`: the set of isomorphism classes of the fibre of `𝓕_{𝒳,k,x₀}` over the dual
numbers `k[ε]`, that is of morphisms `x₀ ⟶ x` of `𝒳` over `Spec k ⟶ Spec k[ε]`. -/
@[stacks 07WY "the underlying set of the k-vector space TF_{X,k,x_0} is the set of \
  isomorphism classes of objects of F_{X,k,x_0} over k[ε]"]
theorem tangentSpaceModuleOfSatisfiesRS_carrier :
    let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
    letI := D.category
    ((tangentSpaceModuleOfSatisfiesRS B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc : ModuleCat k) :
        Type _) =
      Quotient (isIsomorphicSetoid
        (D.projection.Fiber (artinianDualNumbers.{u, u, u} Λ k))) := by
  intro D
  let := D.category
  exact isomorphismClasses_obj (BasedCategory.ofFunctor D.projection)
    (predeformationCategory_isPredeformationCategory B hS iΛ p x₀ hx₀ hp).cofibered _

/-- **Infinitesimal automorphisms as a vector space.** For `𝒳` satisfying (RS), the
infinitesimal automorphisms `Inf(𝓕_{𝒳,k,x₀})` at an object `x` of `𝓕_{𝒳,k,x₀}` over `k` and a
choice `P` of pushforwards of `x`, with the natural `k`-vector space structure of Stacks 06JX (the
value at the rank-one module of the canonical linear lift of `M ↦ Inf(x[M]/x)`). -/
@[stacks 07WY "Inf(F_{X,k,x_0}) has a natural k-vector space structure (Lemma 06JX)"]
def infinitesimalAutomorphismModuleOfSatisfiesRS
    (x : (letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.Fiber
        (residueFieldObject.{u, u, u} Λ k)))
    (P : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      ChosenPushforwardsAt (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
        x.1) :
    ModuleCat.{max u w} k :=
  let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  letI := D.category
  let hD := isDeformationCategory_predeformationCategory B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc
  (infinitesimalAutomorphismLinearLift P hD.satisfiesRS).functor.obj
    (FGModuleCat.of k (ULift.{u} k))

/-- **Addition on `Inf` is composition.** The underlying set of
`infinitesimalAutomorphismModuleOfSatisfiesRS` is the kernel of the restriction homomorphism
`Aut(x'₀) ⟶ Aut(x)` from the automorphisms of the chosen dual-number pushforward `x'₀` of `x`
to those of `x` over `k`; under this identification addition is composition of automorphisms,
and multiplication by `c ∈ k` is transport along the scaling `ε ↦ cε` of the dual numbers. -/
@[stacks 07WY "the k-vector space structure on Inf(F_{X,k,x_0}) is such that addition agrees \
  with composition of automorphisms"]
theorem infinitesimalAutomorphismModuleOfSatisfiesRS_carrier
    (x : (letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection.Fiber
        (residueFieldObject.{u, u, u} Λ k)))
    (P : letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
      ChosenPushforwardsAt (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
        x.1) :
    letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
    ∃ h : ((infinitesimalAutomorphismModuleOfSatisfiesRS B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc
        x P : ModuleCat k) : Type _) =
        infinitesimalAutomorphismKernel P
          (squareZeroUnderRed (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀
            hx₀).projection x.1 (FGModuleCat.of k (ULift.{u} k))),
      (∀ a b, cast h (a + b) = cast h a * cast h b) ∧
        ∀ (c : k) a, (cast h (c • a)).1 =
          P.transportAutHom (squareZeroUnderMap
            (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection x.1
            (FGModuleCat.ofHom (c • LinearMap.id : ULift.{u} k →ₗ[k] ULift.{u} k)))
            (cast h a).1 := by
  let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := D.category
  let hD := isDeformationCategory_predeformationCategory B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc
  exact ⟨infinitesimalAutomorphismLinearLift_carrier P hD.satisfiesRS _,
    cast_lift_add P hD.satisfiesRS _, cast_lift_smul P hD.satisfiesRS _⟩

end

section FiniteDimensional

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hRS : SatisfiesRS B S hS p hp)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳)
  (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- **The finite-dimensionality condition.** For `𝒳` satisfying (RS), the condition
`Deformation.IsFiniteDimensionalDeformationCategory` on `𝓕_{𝒳,k,x₀}` holds exactly when the two
vector spaces `T𝓕_{𝒳,k,x₀}` and `Inf(𝓕_{𝒳,k,x₀})` (at every object over `k` and every choice of
pushforwards) are finite dimensional. -/
@[stacks 07WY "the natural condition: the vector spaces TF_{X,k,x_0} and Inf(F_{X,k,x_0}) \
  have finite dimension"]
theorem isFiniteDimensionalDeformationCategory_predeformationCategory_iff :
    letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).category
    IsFiniteDimensionalDeformationCategory.{u, u, u}
        (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection ↔
      FiniteDimensional k
          (tangentSpaceModuleOfSatisfiesRS B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc) ∧
        ∀ x P, FiniteDimensional k
          (infinitesimalAutomorphismModuleOfSatisfiesRS B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc
            x P) := by
  let D := predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let := D.category
  let hD := isDeformationCategory_predeformationCategory B S hS p hp hRS iΛ x₀ hx₀ hfinite hqc
  refine ⟨fun ⟨_, hT, hI⟩ => ⟨hT, fun x P => hI x.1 x.2 P⟩,
    fun ⟨hT, hI⟩ => ⟨hD, hT, fun x hx P => hI ⟨x, hx⟩ P⟩⟩

end FiniteDimensional

end Deformation.Artin
