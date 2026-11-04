module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaLocalOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.LocalizationAtRepresentableSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfLocalizedSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedSquareModuleBaseChange

/-!
# The projection formula for a perfect complex, for a morphism of ringed topoi

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi, `E ∈ D(𝒪_𝒞)` and
`K ∈ D(𝒪_𝒟)`. [Stacks, Tag 0944] says that if `K` is perfect then the canonical map of
[Stacks, Tag 0B56]

`Rf_*E ⊗^𝐋_{𝒪_𝒟} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)`

is an isomorphism.

The proof is the source's. Invertibility may be checked locally on `𝒟`: if `V_k` is a family of
objects covering the final object over each of which `K` has a strictly perfect model, the
derived pullbacks to the localizations of `Sh(𝒟)` at the sheaves `h_{V_k}^#` are jointly
conservative (`AlgebraicGeometry.RingedSite.isIso_of_isIso_derivedPullback_localizationMorphism`),
and by [Stacks, Tag 0E48] together with the invertibility of the base change map for a
localization square the restriction of the map to such a localization is the map for the
localized morphism (`ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_localizations`).
There `K` is represented by a strictly perfect complex
(`AlgebraicGeometry.RingedSite.exists_isStrictlyPerfect_derivedPullback_localizationMorphism`),
and for such a complex the map is invertible by dévissage to the structure sheaf in one degree
(`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_isStrictlyPerfect`).
The base change map of a localization square is invertible
(`RingedToposHom.isIso_derivedBaseChange_localizedRingedToposSquare_of_isIso_moduleBaseChange` and
`AlgebraicGeometry.RingedToposHom.isIso_moduleBaseChange_localizedRingedToposSquare`): the
pullbacks to the localizations are exact and keep K-injective complexes, so `Rf_*` may be
computed on a K-injective complex, where the base change map is the base change map of sheaves of
modules, which is invertible because it lies over the base change map of sheaves of sets of
[Stacks, Tag 04IF].

## Main results

* `ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_isPerfect_of_baseChange`: the
  projection formula map is invertible at a perfect complex as soon as the base change maps of
  the localization squares of `f` are invertible.
* `ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_isPerfect`: **[Stacks, Tag 0944]**.

## Implementation notes

The ringed topoi are taken in `AlgebraicGeometry.RingedTopos.{u, u, u}`, the generality in which
the derived pullback, the derived direct image and the derived tensor product of a morphism of
ringed topoi are available here; the sheafification and composition hypotheses that these
constructions carry hold for every such ringed topos and are supplied by instance search.
Perfectness is `AlgebraicGeometry.RingedSite.IsPerfect` of [Stacks, Tag 08G5], read on the site
presenting the target topos.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
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

section Reduction

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

/-- **The projection formula map is invertible at a perfect complex once base change holds for
the localization squares.** If, for every sheaf `G` on `𝒟`, the base change map of the
localization square of `f` at `G` ([Stacks, Tag 04IF]) is invertible, then Equation 21.50.0.1
is invertible at every perfect `K` and every `E`. -/
theorem isIso_projectionFormulaMap_of_isPerfect_of_baseChange
    (hb : ∀ (G : Y.Topos) E,
      IsIso (squareBaseChangeMap (RingedToposHom.localizedRingedToposSquare f G) E))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : RingedSite.IsPerfect Y.toRingedSite K) :
    IsIso (projectionFormulaMap f E K) := by
  obtain ⟨E₀, hE₀, ⟨e⟩⟩ := hK
  refine ((projectionFormulaNatTrans f E).isIso_app_iff_of_iso e).1 ?_
  obtain ⟨ι, V, hV, hmodels⟩ :=
    RingedSite.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex _ E₀ hE₀
  refine isIso_projectionFormulaMap_of_localizations f
    (fun k => RingedSite.representableSheaf Y.toRingedSite (V k))
    (fun φ h =>
      RingedSite.isIso_of_isIso_derivedPullback_localizationMorphism Y.toRingedSite V hV φ h)
    (fun k => hb _) _ (fun k => ?_) E
  obtain ⟨P, hP, ⟨q, hq⟩⟩ := hmodels k
  exact RingedSite.exists_isStrictlyPerfect_derivedPullback_localizationMorphism Y.toRingedSite
    (V k) E₀ P hP q

end Reduction

/-- **[Stacks, Tag 0944], the projection formula for a perfect complex.** Let
`f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi, `E ∈ D(𝒪_𝒞)` and
`K ∈ D(𝒪_𝒟)`. If `K` is perfect, then the canonical map of [Stacks, Tag 0B56]
`Rf_*E ⊗^𝐋_{𝒪_𝒟} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_𝒞} Lf^*K)` is an isomorphism. -/
@[stacks 0944]
theorem isIso_projectionFormulaMap_of_isPerfect {X Y : RingedTopos.{u, u, u}}
    (f : RingedToposHom X Y)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : RingedSite.IsPerfect Y.toRingedSite K) :
    IsIso (projectionFormulaMap f E K) :=
  isIso_projectionFormulaMap_of_isPerfect_of_baseChange f
    (fun G E =>
      RingedToposHom.isIso_derivedBaseChange_localizedRingedToposSquare_of_isIso_moduleBaseChange
        f G (RingedToposHom.isIso_moduleBaseChange_localizedRingedToposSquare f G) E) E K hK

end Stacks.Cohomology.ProjectionFormulaOfToposHom

end
