module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.TensorProductNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# Inverse image commutes with the total tensor complex

Let `B` be a big étale site, `f : T ⟶ S` a morphism of it and `Λ` a commutative ring. Inverse
image of sheaves of `Λ`-modules along `f` commutes with the tensor product
(`AlgebraicGeometry.smallEtaleSheafPullbackTensorIso`), naturally in each variable
(`AlgebraicGeometry.smallEtaleSheafPullbackTensorIso_naturality_left` and `_right`). This file
transports that to complexes: for any two cochain complexes `P` and `G` of sheaves of
`Λ`-modules on `S`,

`f^{-1} Tot(P ⊗_Λ G) ≅ Tot(f^{-1}P ⊗_Λ f^{-1}G)`.

This is the localization statement the derived tensor product of a bounded above complex needs on
an arbitrary scheme: the two sides are the restrictions to `T` of the two descriptions of
`K ⊗^L_Λ L`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSheafPullbackMapBifunctorIso` — **inverse image commutes with
  the total tensor complex.**

## Implementation notes

The transport is `CategoryTheory.Functor.mapBifunctorTotalIso`, which takes the degreewise
comparison together with its two naturality squares and additionally asks that the transporting
functor preserve the antidiagonal coproducts occurring in the total complex. The small étale
inverse image preserves every colimit, being left adjoint to the pushforward
(`CategoryTheory.Functor.sheafAdjunctionContinuous`), so that last condition is free.

## References

* [Stacks Project, Tag 095I](https://stacks.math.columbia.edu/tag/095I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

attribute [local instance] AlgebraicGeometry.SmallEtale.moduleSheafMonoidal
  AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.additive_smallEtaleSheafPullback_moduleCat

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ]
  [∀ (S S' : B.Scheme) (f : S' ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B S'.obj S'.property)).IsRightAdjoint]
  [∀ S : B.Scheme, (curriedTensor
      (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ (S : B.Scheme)
      (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ)),
    ((curriedTensor (Sheaf (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive]
  [∀ (S : B.Scheme) (P G : CochainComplex
      (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor
        (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ)))
      (ComplexShape.up ℤ)]

/-- **Inverse image along a morphism of a big étale site commutes with the total tensor complex**
of two cochain complexes of sheaves of `Λ`-modules:
`f^{-1} Tot(P ⊗_Λ G) ≅ Tot(f^{-1}P ⊗_Λ f^{-1}G)`.

Nothing is asked of either scheme, of `Λ`, or of the complexes. -/
public def smallEtaleSheafPullbackMapBifunctorIso {S T : B.Scheme} (f : T ⟶ S)
    (P G : CochainComplex (Sheaf (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ) :
    ((((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor P G (curriedTensor _) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B S.obj S.property)
            (SmallEtale.topology B T.obj T.property)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        ((((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
            (SmallEtale.topology B S.obj S.property)
            (SmallEtale.topology B T.obj T.property)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)
        (curriedTensor _) (ComplexShape.up ℤ)) :=
  letI : ∀ n : ℤ, PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n}))
      ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)) := fun _ =>
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous
      (ModuleCat.{max (u + 1) w} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj
        T.property)).leftAdjoint_preservesColimits).preservesColimitsOfShape
  CategoryTheory.Functor.mapBifunctorTotalIso
    (curriedTensor (Sheaf (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (curriedTensor (Sheaf (SmallEtale.topology B T.obj T.property)
      (ModuleCat.{max (u + 1) w} Λ))) _ _ _
    (fun a b => smallEtaleSheafPullbackTensorIso.{w} B f Λ a b)
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (smallEtaleSheafPullbackTensorIso_naturality_left.{u, w} B f Λ)
    (smallEtaleSheafPullbackTensorIso_naturality_right.{u, w} B f Λ) P G

end Stacks.EtaleCohomology

end
