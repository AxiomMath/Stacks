module

public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow

/-!
# Pulling de Rham classes back along a closed immersion

Let `f : X' ⟶ X` be a closed immersion sitting in a commutative square

```
X' --f--> X
|         |
S' --g--> S
```

The pullback `f^* : H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')` of
`StacksFrontier.AlgebraicGeometry.DeRham.Functoriality` is the composite of the map that the
canonical map of complexes `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` induces on hypercohomology over `X`
with the comparison `H^i(X, f_*Ω^•_{X'/S'}) ⟶ H^i(X, Rf_*Ω^•_{X'/S'}) = H^i(X', Ω^•_{X'/S'})`.
For a closed immersion `f_*` is exact on abelian sheaves (Stacks, Tag 01AX), so this comparison
is an isomorphism, and a class pulls back to zero on `X'` exactly when it is killed by the map of
complexes into `f_*Ω^•_{X'/S'}` on `X`. This is how the source reads the restriction of a de
Rham class to a divisor `Y ⊆ X` throughout Section 50.15, where `Ω^•_{Y/S}` is regarded as a
complex of sheaves on `X`.

## Main results

* `Stacks.ClosedImmersion.preservesHomology_abelianPushforward`: pushforward of abelian sheaves
  along a closed embedding preserves homology.
* `AlgebraicGeometry.Scheme.Hom.isIso_deRhamPushforwardToDerived`: for a closed immersion
  `f`, the comparison `f_*Ω^•_{X'/S'} ⟶ Rf_*Ω^•_{X'/S'}` is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback_apply_eq_zero_iff`: for a closed
  immersion `f`, `f^* b = 0` if and only if `b` maps to zero in `H^i(X, f_*Ω^•_{X'/S'})`.

## References

* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace Stacks.ClosedImmersion

/-- **Pushforward of abelian sheaves along a closed embedding preserves homology**: it is exact
(Stacks, Tag 01AX). -/
theorem preservesHomology_abelianPushforward {Z X : TopCat.{u}} (i : Z ⟶ X)
    (hi : IsClosedEmbedding i.hom) :
    (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} i).PreservesHomology := by
  have h := exactFunctor_closedInclusionPushforward i hi
  have : Limits.PreservesFiniteLimits
      (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} i) := h.1
  have : Limits.PreservesFiniteColimits
      (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} i) := h.2
  infer_instance

end Stacks.ClosedImmersion

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  [IsClosedImmersion f]

/-- **For a closed immersion `f`, the comparison `f_*Ω^•_{X'/S'} ⟶ Rf_*Ω^•_{X'/S'}` is an
isomorphism**: `f_*` is exact on abelian sheaves, so the unit of its right derived functor is
invertible. -/
instance isIso_deRhamPushforwardToDerived : IsIso (deRhamPushforwardToDerived f p') := by
  have := Stacks.ClosedImmersion.preservesHomology_abelianPushforward f.base
    f.isClosedEmbedding
  have := (abelianPushforward.{u, u} f.base).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hu : IsIso ((abelianPushforward.{u, u} f.base).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj
        (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))))) :=
    NatIso.isIso_app_of_isIso _ _
  unfold deRhamPushforwardToDerived
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hu inferInstance

/-- **A de Rham class pulls back to zero along a closed immersion `f` exactly when the canonical
map of complexes `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` kills it on hypercohomology over `X`.** The
pullback is that map followed by the comparison
`H^i(X, f_*Ω^•_{X'/S'}) ⟶ H^i(X', Ω^•_{X'/S'})`, which is an isomorphism for a closed
immersion. -/
theorem deRhamCohomologyPullback_apply_eq_zero_iff (hcomm : f ≫ p = p' ≫ g) (i : ℤ)
    (b : deRhamCohomology p i) :
    (deRhamCohomologyPullback f p p' g hcomm i).hom b = 0 ↔
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (deRhamAbelianPushforwardMapPlus f p p' g hcomm)))).hom b =
        0 := by
  set e := (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
    ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (deRhamPushforwardToDerived f p') ≫
      (derivedSectionsPushforwardIso f).inv.app
        (DerivedCategory.Plus.Q.obj
          (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
            (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))))
  have : IsIso e := by
    simp only [e]
    infer_instance
  have hfac : deRhamCohomologyPullback f p p' g hcomm i =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (deRhamAbelianPushforwardMapPlus f p p' g hcomm))) ≫ e := by
    simp only [e, deRhamCohomologyPullback, deRhamDerivedSectionsPullback, Functor.map_comp]
  rw [hfac, ConcreteCategory.comp_apply]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have h' := congrArg (inv e).hom h
  rwa [map_zero, ← ConcreteCategory.comp_apply, IsIso.hom_inv_id,
    ConcreteCategory.id_apply] at h'

end AlgebraicGeometry.Scheme.Hom

end
