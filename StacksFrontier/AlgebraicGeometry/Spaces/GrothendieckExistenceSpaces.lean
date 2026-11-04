module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.GrothendieckExistenceSpaces

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ExistenceChowReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated

/-!
# Grothendieck's existence theorem for algebraic spaces

In Situation 08B7 — `A` a Noetherian ring complete with respect to an ideal `I`,
`f : X ⟶ Spec A` a separated morphism of finite type of algebraic spaces — the completion functor
`Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, I𝒪_X)` of Stacks 08B8 is an
equivalence (`AlgebraicGeometry.Space.isEquivalence_completionFunctorProperOver`, Stacks 08BE).

Full faithfulness is Stacks 08B9.  Essential surjectivity is proved by Noetherian induction on
the closed set of points of a closed subspace of `X`: on an empty space every coherent adic system
is zero, and otherwise the Chow reduction
`AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_essSurj_closedSubspaces`
reduces to closed subspaces with strictly fewer points.  This is the source's induction over the
maximal quasi-coherent sheaf of ideals for which the statement fails, carried out on the closed
subsets of the Noetherian space `|X|` instead.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- **Stacks 08BE, Grothendieck's existence theorem for algebraic spaces.**  Let `A` be a
Noetherian ring complete with respect to an ideal `I`, and let `f : X ⟶ Spec A` be a separated
morphism of finite type of algebraic spaces (Situation 08B7, with `𝓘 = I 𝒪_X`).  Then the
completion functor

`Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, 𝓘)`

of Stacks 08B8 is an equivalence of categories. -/
@[stacks 08BE]
theorem isEquivalence_completionFunctorProperOver [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom) :
    letI := C1573.fact_isLocallyNoetherian_of_baseObject X f hf.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (C1573.baseIdealSubmodule X.1 X.2 I)
      (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).IsEquivalence :=
  by apply C1573.isEquivalence_completionFunctorProperOver <;> assumption

end AlgebraicGeometry.Space

end
