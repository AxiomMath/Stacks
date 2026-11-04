module

public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceEquivSurjective
public import StacksFrontier.Deformation.Representation.TangentSelfExt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent space of the deformation category of a `k`-algebra (Stacks 0DY3)

Let `k` be a field and `P` a `k`-algebra. The deformation category `𝓓_P` of Stacks 0DY1 has a
tangent space `T𝓓_P = 𝓓_P(k[ε])`, a `k`-vector space by the canonical structure of
**Stacks 06IH**, and this file identifies it with `Ext¹_P(NL_{P/k}, P)` as a `k`-linear
equivalence, which is the tangent-space clause of **Stacks 0DY3**.

Everything mathematical is already in place. The family of extension classes
`Deformation.Examples.tangentExtClass` sends an isomorphism class of deformations of `P` over
`k ⊕ V` to a class in `Ext¹_P(NL_{P/k}, P ⊗[k] V)`; it is natural in `V`
(`Deformation.Examples.tangentExtClass_naturality`), injective
(`Deformation.Examples.tangentExtClass_injective`) and surjective
(`Deformation.Examples.surjective_tangentExtClass`). What this file adds is the passage from a
natural bijection to a linear equivalence, which is the same transport along the carrier
equality of Stacks 06IH that
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` performs for
finite-dimensionality: naturality against an additive `k`-linear receptacle functor makes the
family linear at the rank-one module, by **Stacks 06IJ** in the form
`Deformation.isLinearMap_of_natural_on_fgModules`, and the canonical vector-space structure is
the one transported from the linear lift of Stacks 06IA, so a linear bijection on the lift
becomes a linear equivalence on the tangent space itself.

## Main definitions

* `Deformation.tangentSpaceLinearEquivOfNaturalBijection`: a family of maps out of the
  tangent-space set functor `V ↦ 𝓕(k[V])`, natural in `V` and bijective at the rank-one module,
  into an additive `k`-linear functor `G`, is a `k`-linear equivalence of the canonical tangent
  space of Stacks 06IH with `G(k)`.
* `Deformation.Examples.ringDeformationTangentSpaceLinearEquivExtOne`: **the tangent-space
  clause of Stacks 0DY3**, `T𝓓_P ≃ₗ[k] Ext¹_P(NL_{P/k}, P)`.

## Main results

* `Deformation.tangentSpaceLinearEquivOfNaturalBijection_apply`: the linear equivalence is the
  given family at the rank-one module, so nothing about it is left to the transport.
* `Deformation.Examples.ringDeformationTangentSpaceLinearEquivExtOne_apply`: on the class of a
  point of the fibre over `k[ε]` the identification is the class of **Stacks 0GPT** of the
  square-zero extension of `P` by `P ⊗[k] k` that point determines, read through `P ⊗[k] k ≅ P`.

## Implementation notes

The attribute of Stacks 0DY3 is carried by
`Deformation.Examples.ringDeformationTangentSpaceLinearEquivExtOne` and its characterising
lemma here, together with
`Deformation.Examples.exists_infinitesimalAutomorphismGroupMulEquivDerivation` of
`StacksFrontier/Deformation/Examples/Geometric/RingsInfinitesimalAutomorphisms.lean`, which is the
infinitesimal-automorphism clause `Inf(𝓓_P) = Der_k(P, P)` of the same tag. The two attributes
together are the covering set of the tag: the source states the two identifications in one
displayed formula and neither declaration states the other's half.

The receptacle is `Deformation.Examples.naiveCotangentExtOneTensorFunctor`, which is `k`-linear
by `Deformation.Examples.naiveCotangentExtOneTensorFunctor_linear`; its value at the rank-one
module is `Ext¹_P(NL_{P/k}, P ⊗[k] k)`, carried to `Ext¹_P(NL_{P/k}, P)` by
`Deformation.Examples.naiveCotangentExtOneTensorFunctorObjRankOne`. The `k`-module structure on
the Ext groups is the restriction of scalars along `algebraMap k P`,
`Deformation.Examples.moduleBaseNaiveCotangentExtOne`, which is the structure that functor is
built with.

The transport of the vector-space structure of Stacks 06IH is
`Deformation.associatedTangentSpaceLiftEquiv` of
`StacksFrontier/Deformation/Representation/TangentSelfExt.lean`, which is why that
module is imported: it is the linear equivalence of the value of the linear lift at the
rank-one module with the tangent space, and it is the only thing needed here beyond the
criterion of `StacksFrontier/Deformation/TangentSpace/FiniteDimensional.lean`.

## References

* [Stacks Project, Tag 0DY3](https://stacks.math.columbia.edu/tag/0DY3)
* [Stacks Project, Tag 0DY1](https://stacks.math.columbia.edu/tag/0DY1)
* [Stacks Project, Tag 0GPT](https://stacks.math.columbia.edu/tag/0GPT)
* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 06IJ](https://stacks.math.columbia.edu/tag/06IJ)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct Stacks.Deformation

namespace Deformation

universe u w u₁ v₁ u₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### From a natural bijection to a linear equivalence -/

section Criterion

variable (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
  (h𝓕 : IsPredeformationCategory 𝓕.p)
  (hS2 : SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
  (G : FGModuleCat.{w} k ⥤ ModuleCat.{u₂} k) [G.Additive] [G.Linear k]

/-- The carrier of the value of the linear lift of Stacks 06IA is the value of the set-valued
functor `V ↦ 𝓕(k[V])`. -/
public theorem liftCarrierEq (V : FGModuleCat.{w} k) :
    (((associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).functor.obj V :
        ModuleCat.{u₁} k) : Type u₁)
      = (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V :=
  congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ ↦ H.obj V)
    (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).forget_comp

variable (t : ∀ V : FGModuleCat.{w} k,
  (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V → G.obj V)

/-- A family of maps out of the tangent-space set functor, read on the linear lift of
Stacks 06IA through `Deformation.liftCarrierEq`. -/
public def liftedFamily (V : FGModuleCat.{w} k) :
    ((associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).functor.obj V) → G.obj V :=
  fun x ↦ t V (cast (liftCarrierEq 𝓕 h𝓕 hS2 V) x)

omit [G.Additive] [Functor.Linear k G] in
/-- A family natural in `V` stays natural when read on the linear lift. -/
public theorem liftedFamily_natural
    (ht : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
        (x : (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V),
      t V' ((associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).map f x) = (G.map f) (t V x))
    {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
    (x : (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).functor.obj V) :
    liftedFamily 𝓕 h𝓕 hS2 G t V'
        (((associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).functor.map f) x)
      = (G.map f) (liftedFamily 𝓕 h𝓕 hS2 G t V x) := by
  rw [liftedFamily, liftedFamily, moduleFunctor_map_cast k
    (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).functor
    (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered)
    (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).forget_comp f x]
  exact ht f _

/-- **The family read on the linear lift is `k`-linear at the rank-one module.** This is
**Stacks 06IJ** in the form `Deformation.isLinearMap_of_natural_on_fgModules`: the linear lift
and `G` are additive and `k`-linear, so a natural family between them commutes with the two
projections of `k × k`, with their sum, and with `r • 𝟙`. -/
public theorem isLinearMap_liftedFamily
    (ht : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
        (x : (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V),
      t V' ((associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).map f x) = (G.map f) (t V x)) :
    IsLinearMap k (liftedFamily 𝓕 h𝓕 hS2 G t (FGModuleCat.of k k)) :=
  isLinearMap_of_natural_on_fgModules k
    (associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2).functor G
    (liftedFamily 𝓕 h𝓕 hS2 G t) fun f x ↦ liftedFamily_natural 𝓕 h𝓕 hS2 G t ht f x

omit [G.Additive] [Functor.Linear k G] in
/-- The family read on the linear lift is bijective at the rank-one module as soon as the
family is: the comparison of carriers is a transport along an equality of types. -/
public theorem bijective_liftedFamily
    (hbij : Function.Bijective (t (FGModuleCat.of k k))) :
    Function.Bijective (liftedFamily 𝓕 h𝓕 hS2 G t (FGModuleCat.of k k)) := by
  refine ⟨fun x y hxy ↦
    cast_inj_of_eq (liftCarrierEq 𝓕 h𝓕 hS2 (FGModuleCat.of k k)) (hbij.1 hxy), fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ := hbij.2 y
  refine ⟨cast (liftCarrierEq 𝓕 h𝓕 hS2 (FGModuleCat.of k k)).symm z, ?_⟩
  rwa [liftedFamily, cast_symm_cancel]

/-- **A natural family which is bijective at the rank-one module is a linear equivalence of the
canonical tangent space of Stacks 06IH with the value of the receptacle at `k`.**

Linearity is not visible on the tangent space itself: the vector-space structure of
Stacks 06IH is transported from the linear lift of Stacks 06IA, so it is only through
naturality in `V` that a map out of the tangent space is linear. The equivalence is therefore
assembled on the lift, where `Deformation.isLinearMap_liftedFamily` and
`Deformation.bijective_liftedFamily` apply, and carried across by
`Deformation.associatedTangentSpaceLiftEquiv`. -/
public def tangentSpaceLinearEquivOfNaturalBijection
    (ht : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
        (x : (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V),
      t V' ((associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).map f x) = (G.map f) (t V x))
    (hbij : Function.Bijective (t (FGModuleCat.of k k))) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
    artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered) ≃ₗ[k]
      G.obj (FGModuleCat.of k k) :=
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
  letI : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
  (associatedTangentSpaceLiftEquiv 𝓕 h𝓕 hS2).symm.trans
    (LinearEquiv.ofBijective (IsLinearMap.mk' _ (isLinearMap_liftedFamily 𝓕 h𝓕 hS2 G t ht))
      (bijective_liftedFamily 𝓕 h𝓕 hS2 G t hbij))

/-- **The linear equivalence is the given family.** The transport of the vector-space structure
of Stacks 06IH cancels against the transport of the family, so nothing about the identification
is hidden in the comparison of carriers. -/
public theorem tangentSpaceLinearEquivOfNaturalBijection_apply
    (ht : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
        (x : (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V),
      t V' ((associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).map f x) = (G.map f) (t V x))
    (hbij : Function.Bijective (t (FGModuleCat.of k k)))
    (y : (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj (FGModuleCat.of k k)) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
    tangentSpaceLinearEquivOfNaturalBijection 𝓕 h𝓕 hS2 G t ht hbij y
      = t (FGModuleCat.of k k) y := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
  have hsymm : (associatedTangentSpaceLiftEquiv 𝓕 h𝓕 hS2).symm y
      = cast (liftCarrierEq 𝓕 h𝓕 hS2 (FGModuleCat.of k k)).symm y :=
    (associatedTangentSpaceLiftEquiv 𝓕 h𝓕 hS2).symm_apply_eq.2
      ((castModuleEquiv_apply
          (associatedTangentSpaceModuleStructure_carrierUnlifted 𝓕 h𝓕 hS2)
          (cast (liftCarrierEq 𝓕 h𝓕 hS2 (FGModuleCat.of k k)).symm y)).trans
        (cast_symm_cancel (liftCarrierEq 𝓕 h𝓕 hS2 (FGModuleCat.of k k)) y)).symm
  show liftedFamily 𝓕 h𝓕 hS2 G t (FGModuleCat.of k k)
    ((associatedTangentSpaceLiftEquiv 𝓕 h𝓕 hS2).symm y) = _
  rw [hsymm, liftedFamily, cast_symm_cancel]

end Criterion

end Deformation

namespace Deformation.Examples

open Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] moduleBaseNaiveCotangentExtOne isScalarTowerBaseNaiveCotangentExtOne

universe u w

/-! ### The tangent-space clause of Stacks 0DY3 -/

section Clause

variable (Λ : Type u) (k P : Type w) [CommRing Λ] [Field k] [Algebra Λ k] [CommRing P]
  [Algebra k P]

/-- Schlessinger's condition (S2) for the functor of isomorphism classes of deformations of a
`k`-algebra, which is what the canonical vector-space structure of Stacks 06IH on the tangent
space is exposed by. It comes from the deformation category being one of Stacks 0DY2, hence
satisfying (RS). -/
public theorem schlessingerConditionS2_ringDeformation :
    SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection)) :=
  schlessingerConditionS2_of_isIsomorphismClasses (ringDeformationBasedCategory Λ k P)
    isCofiberedInGroupoids_ringDeformationProjection
    (schlessingerConditionS2_of_satisfiesRS
      (ringDeformationCategory_isDeformationCategory P).satisfiesRS)
    (.inl (ringDeformationCategory_isDeformationCategory P).predeformation)

/-- **The family of extension classes is natural against the receptacle functor.** This is
`Deformation.Examples.tangentExtClass_naturality` with the induced map read as the action of
`Deformation.Examples.naiveCotangentExtOneTensorFunctor` on morphisms, which is the shape
`Deformation.tangentSpaceLinearEquivOfNaturalBijection` consumes. -/
public theorem tangentExtClass_naturality_tensorFunctor {W W' : FGModuleCat.{w} k} (f : W ⟶ W')
    (z : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).obj W) :
    tangentExtClass W' ((associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection).map f z)
      = ((naiveCotangentExtOneTensorFunctor k P).map f) (tangentExtClass W z) :=
  (tangentExtClass_naturality f z).trans
    (naiveCotangentExtOneTensorFunctor_map_apply k P f (tangentExtClass W z)).symm

/-- **Stacks 0DY3, the tangent space.** Let `k` be a field and `P` a `k`-algebra. The tangent
space of the deformation category of `P` of Stacks 0DY1, with the canonical `k`-vector-space
structure of Stacks 06IH, is `Ext¹_P(NL_{P/k}, P)`:

`T𝓓_P = Ext¹_P(NL_{P/k}, P)`.

The identification is the family of extension classes
`Deformation.Examples.tangentExtClass`, which sends an isomorphism class of first-order flat
deformations of `P` over `k ⊕ V` to the class of **Stacks 0GPT** of the square-zero extension
of `P` by `P ⊗[k] V` it determines. That family is natural in `V`, injective by
`Deformation.Examples.tangentExtClass_injective` and surjective by
`Deformation.Examples.surjective_tangentExtClass`, so
`Deformation.tangentSpaceLinearEquivOfNaturalBijection` turns it into a `k`-linear equivalence
at `V = k`, and `Deformation.Examples.naiveCotangentExtOneTensorFunctorObjRankOne` replaces the
coefficients `P ⊗[k] k` by `P`.

The infinitesimal-automorphism clause `Inf(𝓓_P) = Der_k(P, P)` of the same tag is
`Deformation.Examples.exists_infinitesimalAutomorphismGroupMulEquivDerivation`; the two
declarations together cover the tag. -/
@[stacks 0DY3 "the tangent space", sga "7 VI 4.16" "(b), special case"]
public def ringDeformationTangentSpaceLinearEquivExtOne :
    letI : Fact (IsPredeformationCategory (ringDeformationBasedCategory Λ k P).p) :=
      ⟨(ringDeformationCategory_isDeformationCategory P).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection))) :=
      ⟨schlessingerConditionS2_ringDeformation Λ k P⟩
    artinianTangentSpace Λ k
        (isomorphismClasses (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection)
      ≃ₗ[k] naiveCotangentExtOne k P P :=
  letI : Fact (IsPredeformationCategory (ringDeformationBasedCategory Λ k P).p) :=
    ⟨(ringDeformationCategory_isDeformationCategory P).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection))) :=
    ⟨schlessingerConditionS2_ringDeformation Λ k P⟩
  (tangentSpaceLinearEquivOfNaturalBijection
      (𝓕 := ringDeformationBasedCategory Λ k P)
      (h𝓕 := (ringDeformationCategory_isDeformationCategory P).predeformation)
      (hS2 := schlessingerConditionS2_ringDeformation Λ k P)
      (G := naiveCotangentExtOneTensorFunctor k P) (t := tangentExtClass)
      (tangentExtClass_naturality_tensorFunctor Λ k P)
      (bijective_tangentExtClass (FGModuleCat.of k k))).trans
    ((naiveCotangentExtOneTensorFunctorObjRankOne k P).restrictScalars k)

/-- **The identification of Stacks 0DY3 is the classification of Stacks 0GPT.** On the
isomorphism class of a point of the fibre over the square-zero extension `k ⊕ k` of
Stacks 06IB, the tangent-space identification is the class in `Ext¹_P(NL_{P/k}, P ⊗[k] k)` of
the square-zero extension of `P` the point determines, read through `P ⊗[k] k ≅ P`.

This pins the identification down: no content is left in the transport of the vector-space
structure of Stacks 06IH. -/
@[stacks 0DY3 "the tangent space"]
public theorem ringDeformationTangentSpaceLinearEquivExtOne_apply
    (z : (associatedTangentSpaceSetFunctor (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection).obj (FGModuleCat.of k k)) :
    letI : Fact (IsPredeformationCategory (ringDeformationBasedCategory Λ k P).p) :=
      ⟨(ringDeformationCategory_isDeformationCategory P).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
      (isomorphismClasses (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection))) :=
      ⟨schlessingerConditionS2_ringDeformation Λ k P⟩
    ringDeformationTangentSpaceLinearEquivExtOne Λ k P z
      = naiveCotangentExtOneTensorFunctorObjRankOne k P
        (tangentExtClass (FGModuleCat.of k k) z) := by
  let : Fact (IsPredeformationCategory (ringDeformationBasedCategory Λ k P).p) :=
    ⟨(ringDeformationCategory_isDeformationCategory P).predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses (ringDeformationBasedCategory Λ k P)
      isCofiberedInGroupoids_ringDeformationProjection))) :=
    ⟨schlessingerConditionS2_ringDeformation Λ k P⟩
  exact congrArg (naiveCotangentExtOneTensorFunctorObjRankOne k P)
    (tangentSpaceLinearEquivOfNaturalBijection_apply (ringDeformationBasedCategory Λ k P)
      (ringDeformationCategory_isDeformationCategory P).predeformation
      (schlessingerConditionS2_ringDeformation Λ k P)
      (naiveCotangentExtOneTensorFunctor k P) tangentExtClass
      (tangentExtClass_naturality_tensorFunctor Λ k P)
      (bijective_tangentExtClass (FGModuleCat.of k k)) z)

end Clause

end Deformation.Examples

end
