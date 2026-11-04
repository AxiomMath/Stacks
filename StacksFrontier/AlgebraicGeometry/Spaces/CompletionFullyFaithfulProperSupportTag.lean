module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08B9: the whole lemma

Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `X` be an algebraic
space with a morphism `f : X ⟶ Spec A` locally of finite type.  Stacks 08B9 asserts that for
coherent `𝒪_X`-modules `F`, `G` the intersection of whose supports is proper over `Spec A`,
completion along `I 𝒪_X` (Stacks 08B4) is a bijection
`Mor_{Coh(𝒪_X)}(F, G) ⟶ Mor_{Coh(X, I 𝒪_X)}(F^∧, G^∧)`, and, in particular, that the completion
functor of Stacks 08B8 is fully faithful.

## Main results

* `AlgebraicGeometry.Space.bijective_completionFunctor_map_and_fullyFaithful_of_isProperOver`:
  **Stacks 08B9**, the whole lemma.

## Implementation notes

The bijection is stated as in
`AlgebraicGeometry.Space.C1573.bijective_completionFunctor_map_of_isProperOver`.  Full
faithfulness is the structure
`AlgebraicGeometry.Space.C1573.completionFunctorProperOverFullyFaithful`, which is data; the
proposition stated is that it is inhabited.  The source's Situation 08B7 has `X` separated and of
finite type over `Spec A`; neither separatedness nor quasi-compactness is used.

## References

* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
* [Stacks Project, Tag 08B7](https://stacks.math.columbia.edu/tag/08B7)
* [Stacks Project, Tag 08B8](https://stacks.math.columbia.edu/tag/08B8)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

/-- **Stacks 08B9.**  Let `A` be a Noetherian ring complete with respect to an ideal `I` and let
`X` be an algebraic space with a morphism `f : X ⟶ Spec A` locally of finite type.

1. For coherent `𝒪_X`-modules `F`, `G` such that the intersection of their supports is proper
   over `Spec A`, completion along `I 𝒪_X` (Stacks 08B4) is a bijection
   `Mor_{Coh(𝒪_X)}(F, G) ⟶ Mor_{Coh(X, I 𝒪_X)}(F^∧, G^∧)`.
2. In particular, the completion functor
   `Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, I 𝒪_X)` of Stacks 08B8 is
   fully faithful.

The source's Situation 08B7 has `X` separated and of finite type over `Spec A`, so locally
Noetherian (`AlgebraicGeometry.Space.C1573.fact_isLocallyNoetherian_of_baseObject` supplies the
`Fact` instance the completion functor of Stacks 08B4 is stated with); neither separatedness nor
quasi-compactness is used.  The properness of `Supp F ∩ Supp G` is stated in the curried form
`IsProperOver … hcl` of `AlgebraicGeometry.Space.IsProperOver`, which takes the closedness `hcl`
of the subset as an argument. -/
@[stacks 08B9]
theorem bijective_completionFunctor_map_and_fullyFaithful_of_isProperOver
    [IsNoetherianRing A] [IsAdicComplete I A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom) :
    letI := C1573.fact_isLocallyNoetherian_of_baseObject X f hf
    (∀ (F G : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
      (hcl : IsClosed
        (supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj F.obj) ∩
          supportOfSheaf B (Spec (.of A)) hA X.1 ((SheafOfModules.toSheaf _).obj G.obj))),
      IsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf _ hcl →
      Function.Bijective ((completionFunctor B (Spec (.of A)) hA X.1 X.2
        (C1573.baseIdealSubmodule X.1 X.2 I)
        (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).map
          (X := F) (Y := G))) ∧
    Nonempty (completionFunctorProperOver B (Spec (.of A)) hA X.1
      (schemeSpace (baseObject A B hA)).1 X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      (C1573.baseIdealSubmodule X.1 X.2 I)
      (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).FullyFaithful :=
  ⟨fun F G hcl hp => C1573.bijective_completionFunctor_map_of_isProperOver X I f hf F G hcl hp,
    ⟨C1573.completionFunctorProperOverFullyFaithful X I f hf⟩⟩

add_to_stacks 08B9 "the bijection on morphisms; the source's Situation 08B7 asks X separated of \
finite type over Spec A, of which only local finite type is used"
  AlgebraicGeometry.Space.C1573.bijective_completionFunctor_map_of_isProperOver

add_to_stacks 08B9 "in particular, the completion functor of 08B8 is fully faithful"
  AlgebraicGeometry.Space.C1573.completionFunctorProperOverFullyFaithful

end AlgebraicGeometry.Space

end
