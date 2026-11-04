module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaBaseChangeOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ModulePullback

/-!
# Invertibility of the projection formula map is local on the target

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi. For a sheaf `G` on `𝒟`,
localizing `f` at `G` ([Stacks, Tag 04IF]) gives a 2-commutative square

```
  (Sh(𝒞)/f⁻¹G, 𝒪_{f⁻¹G}) ⟶ (Sh(𝒞), 𝒪_𝒞)
           | f_G                  | f
           v                      v
     (Sh(𝒟)/G, 𝒪_G)    ⟶   (Sh(𝒟), 𝒪_𝒟)
```

and by [Stacks, Tag 0E48]
(`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_derivedPullback_map_projectionFormulaMap`)
the restriction of Equation 21.50.0.1 for `f` to `Sh(𝒟)/G` is Equation 21.50.0.1 for `f_G`, as soon
as the base change map of the square is invertible. This file records the resulting local
criterion, which is the first step of the proof of [Stacks, Tag 0944]: if a family of sheaves `G_k`
on `𝒟` is jointly conservative on `D(𝒪_𝒟)`, if the base change maps of the localization squares are
invertible, and if `K` restricted to each `Sh(𝒟)/G_k` is represented by a strictly perfect complex,
then Equation 21.50.0.1 is invertible at `K` for every `E`.

## Main results

* `Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_localizations`:
  the local criterion.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.ProjectionFormulaOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- The derived pullback along the localization of a ringed topos at a sheaf exists. Instance
search does not find `hasLeftDerivedFunctor_pullbackOnHomotopy` at a localization morphism on
its own. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_localizationMorphism (G : Y.Topos) :
    (DerivedPullbackOfToposHom.pullbackOnHomotopy (Y.localizationMorphism G)).HasLeftDerivedFunctor
      DerivedPullbackOfToposHom.quasiIsoTarget :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (Y.localizationMorphism G)

/-- **Invertibility of Equation 21.50.0.1 is local on the target.** Let `G_k` be a family of
sheaves on `𝒟` such that a morphism of `D(𝒪_𝒟)` is invertible as soon as its derived pullbacks
to all the localizations `Sh(𝒟)/G_k` are. If the base change maps of the localization squares of
`f` at the `G_k` ([Stacks, Tag 04IF]) are invertible, and if the derived pullback of `K` to each
`Sh(𝒟)/G_k` is represented by a strictly perfect complex, then Equation 21.50.0.1 is invertible
at `(E, K)` for every `E`. -/
theorem isIso_projectionFormulaMap_of_localizations {ι : Type*} (G : ι → Y.Topos)
    (hcons : ∀ {A B : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))} (φ : A ⟶ B),
      (∀ k, IsIso ((derivedPullback (Y.localizationMorphism (G k))).map φ)) → IsIso φ)
    (hb : ∀ k E, IsIso (squareBaseChangeMap (RingedToposHom.localizedRingedToposSquare f (G k)) E))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : ∀ k, ∃ P : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos (G k)).O)) ℤ,
      IsStrictlyPerfect
          (Stacks.SheafOfModules.Tensor.ringSheaf (Y.localizedRingedTopos (G k)).O) P ∧
        Nonempty ((derivedPullback (Y.localizationMorphism (G k))).obj K ≅ DerivedCategory.Q.obj P))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (projectionFormulaMap f E K) := by
  refine hcons _ fun k => ?_
  obtain ⟨P, hP, ⟨e⟩⟩ := hK k
  refine isIso_derivedPullback_map_projectionFormulaMap
    (RingedToposHom.localizedRingedToposSquare f (G k)) (hb k) E K ?_
  refine ((projectionFormulaNatTrans _ _).isIso_app_iff_of_iso
    (e ≪≫ (shiftFunctorZero _ ℤ).symm.app _)).2 ?_
  exact isIso_projectionFormulaMap_of_isStrictlyPerfect _ _ P hP 0

end Stacks.Cohomology.ProjectionFormulaOfToposHom

end
