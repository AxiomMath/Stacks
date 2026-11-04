module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.BaseIdealAdicSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CoherentAdicInternalHomAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.InternalHomSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHomAffine

/-!
# Stacks 08B9: completion is fully faithful on modules with proper support

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `X` be an algebraic
space locally of finite type over `Spec A`, and let `F`, `G` be coherent
`𝒪_X`-modules the intersection of whose supports is proper over `Spec A`.  Then completion
along `I 𝒪_X` (Stacks 08B4) is bijective on morphisms `F ⟶ G`; in particular the completion
functor between the categories of coherent modules and of coherent adic systems with support
proper over `Spec A` (Stacks 08B8) is fully faithful.

The proof is the source's: with `𝓗 = 𝓗om(F, G)`,
`Mor(F, G) = H⁰(X, 𝓗) = lim_n H⁰(X, 𝓗 / Iⁿ 𝓗) = Mor(F^∧, G^∧)`, the middle equality being the
theorem on formal functions in degree zero
(`AlgebraicGeometry.Space.C1573.sectionsFormal_of_hasProperSupport`), and the last Stacks 08B6.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Systems

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

end Systems

section Main

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

variable [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]

end Main

section Registered

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

/-- **Stacks 08B9, the bijection on morphisms.**  Let `A` be a Noetherian ring complete with
respect to an ideal `I`, let `X` be an algebraic space with a morphism
`f : X ⟶ Spec A` locally of finite type, and let `F`, `G` be coherent `𝒪_X`-modules such that the
intersection of their supports is proper over `Spec A`.  Then completion along `I 𝒪_X`
(Stacks 08B4) is a bijection
`Mor_{Coh(𝒪_X)}(F, G) ⟶ Mor_{Coh(X, I 𝒪_X)}(F^∧, G^∧)`.

The source's Situation 08B7 has `X` separated and of finite type over `Spec A`, so locally
Noetherian (`AlgebraicGeometry.Space.isLocallyNoetherian_of_isLocallyOfFiniteType` with
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_baseObject` supply the `Fact`
instance the completion functor of Stacks 08B4 is stated with); neither separatedness nor
quasi-compactness is used. -/
@[stacks 08B9 "the bijection on morphisms; the source's Situation 08B7 asks X separated of \
finite type over Spec A, of which only local finite type is used"]
theorem bijective_completionFunctor_map_of_isProperOver [IsNoetherianRing A] [IsAdicComplete I A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (F G : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hcl : IsClosed (supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj F.obj) ∩
      supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj G.obj)))
    (hp : IsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf _ hcl) :
    letI := C1573.fact_isLocallyNoetherian_of_baseObject X f hf
    Function.Bijective ((completionFunctor B (Spec (.of A)) hA X.1 X.2
      (C1573.baseIdealSubmodule X.1 X.2 I)
      (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).map
        (X := F) (Y := G)) :=
  by apply C1573.bijective_completionFunctor_map_of_isProperOver <;> assumption

/-- **Stacks 08B9, full faithfulness.**  In the situation of
`AlgebraicGeometry.Space.bijective_completionFunctor_map_of_isProperOver`, the completion functor
`Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, I 𝒪_X)` of Stacks 08B8 is
fully faithful. -/
@[stacks 08B9 "in particular, the completion functor of 08B8 is fully faithful"]
def completionFunctorProperOverFullyFaithful [IsNoetherianRing A] [IsAdicComplete I A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :
    letI := C1573.fact_isLocallyNoetherian_of_baseObject X f hf
    (completionFunctorProperOver B (Spec (.of A)) hA X.1
      (schemeSpace (baseObject A B hA)).1 X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      (C1573.baseIdealSubmodule X.1 X.2 I)
      (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).FullyFaithful :=
  by apply C1573.completionFunctorProperOverFullyFaithful

end Registered

end AlgebraicGeometry.Space

end
