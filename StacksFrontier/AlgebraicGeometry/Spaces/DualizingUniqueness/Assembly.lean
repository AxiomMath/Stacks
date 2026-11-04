module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingUniqueness.ChartShift

/-!
# Uniqueness of dualizing complexes on an algebraic space: the assembly

The step of the proof of Stacks 0E52 that takes place on the equi-universe model of the small
étale ringed site of `X`: two dualizing complexes `K`, `K'` are shifts of each other on a covering
of every étale chart (`AlgebraicGeometry.Space.isShiftOnChart_covering`), so `R𝓗om(K', K)` is
invertible on the model, and biduality for `K'` then gives `K' ≅ K ⊗^L L` with `L` invertible.

## Main definitions

* `AlgebraicGeometry.Space.modelRHom`: `R𝓗om(A, -)` on the derived category of the model.

## Main results

* `AlgebraicGeometry.Space.exists_isInvertibleObject_tensor_iso_of_dualizing_of_biduality`.

## References

* [Stacks Project, Tag 0E52](https://stacks.math.columbia.edu/tag/0E52)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- `RSheafHom(A, -)` on the equi-universe model, at the standard model of its derived
category. -/
abbrev modelRHom (A : @DerivedCategory (ModelModules B S hS X.1 X.2) _ _
    (HasDerivedCategory.standard _)) :
    @DerivedCategory (ModelModules B S hS X.1 X.2) _ _ (HasDerivedCategory.standard _) ⥤
      @DerivedCategory (ModelModules B S hS X.1 X.2) _ _ (HasDerivedCategory.standard _) :=
  (@RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2)
    (HasDerivedCategory.standard _)).obj (Opposite.op A)

/-- **Stacks 0E52 on the equi-universe model, from the two biduality inputs of its proof.** If
`R𝓗om(K, K) ≅ O` and `K' ≅ R𝓗om(R𝓗om(K', K), K)` on the model, then `R𝓗om(K', K)` is
invertible, because `K'` is a shift of `K` on a covering of every étale chart
(`AlgebraicGeometry.Space.isShiftOnChart_covering`), and `K' ≅ K ⊗^L L` with `L` its inverse. -/
theorem exists_isInvertibleObject_tensor_iso_of_dualizing_of_biduality
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K K' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hK : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K)
    (hK' : IsDualizingComplexOnSpace B S hS X.1 X.2 hN K')
    (hKK : Nonempty ((modelRHom B S hS X
        ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K.obj)).obj
        ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K.obj) ≅
      (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit _)))
    (hbid : Nonempty ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K'.obj ≅
      (modelRHom B S hS X ((modelRHom B S hS X
        ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K'.obj)).obj
        ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K.obj))).obj
          ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K.obj))) :
    letI := HasDerivedCategory.standard (ModelModules B S hS X.1 X.2)
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
      (smallEtaleModelRingedSite B S hS X.1 X.2).O
    ∃ L, RingedSite.InvertibleDerived.IsInvertibleObject
        (smallEtaleModelRingedSite B S hS X.1 X.2) L ∧
      Nonempty ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K'.obj ≅
        (modelDerivedEquivalence B S hS X.1 X.2).functor.obj K.obj ⊗ L) := by
  have hinv := RingedSite.InvertibleDerived.isInvertibleObject_derivedSheafHom_of_locallyShift
    (smallEtaleModelRingedSite B S hS X.1 X.2)
    (smallEtaleModelRingedSite_isLocallyRinged B S hS X.1 X.2) _ _ hKK
    (model_locallyShift (isShiftOnChart_covering B S hS X hN K K' hK hK'))
  exact RingedSite.InvertibleDerived.exists_isInvertibleObject_tensor_iso_of_iso_derivedSheafHom
    (smallEtaleModelRingedSite B S hS X.1 X.2) _ _ _ hinv hbid.some

end AlgebraicGeometry.Space
