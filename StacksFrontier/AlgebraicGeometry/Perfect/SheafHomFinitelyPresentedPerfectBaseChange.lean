module

public import StacksFrontier.AlgebraicGeometry.Perfect.SheafHomFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomPerfectFlatPushforwardBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0A1J

Let `f : X ⟶ S` be a morphism of finite presentation, `E ∈ D(𝒪_X)` perfect and `𝒢^•` a bounded
complex of finitely presented `𝒪_X`-modules, flat over `S`, with support proper over `S`. Then
`K = Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•)` is a perfect object of `D(𝒪_S)` and its formation commutes with
arbitrary base change.

## Main results

* `isPerfect_derivedPushforward_derivedSheafHom_and_isIso_sheafHomFlatBaseChangeMap`: `K` is
  perfect and its formation commutes with arbitrary base change.

## Implementation notes

"Commutes with arbitrary base change" is read as the source's proof reads it, by
[Stacks, Tag 08IE]: for every cartesian square the canonical map

`Lg^*Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•) ⟶ Rf'_*R𝓗om_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢^•)`

of `AlgebraicGeometry.sheafHomFlatBaseChangeMap` is an isomorphism, with the ordinary pullback
of `𝒢^•` on the right. That is case (1) of [Stacks, Tag 08IE],
`AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_isPerfect`; finite presentation of `f`
supplies its quasi-compactness and quasi-separatedness, and
`AlgebraicGeometry.FlatProperSupportFinitelyPresented` supplies boundedness above,
quasi-coherence and flatness over `S` of the terms of `𝒢^•`.

The perfection of `K` is
`AlgebraicGeometry.isPerfect_derivedPushforward_derivedSheafHom_of_finitePresentation`, which
identifies `K` with `Rf_*(E^∨ ⊗^L 𝒢^•)` by [Stacks, Tag 08DQ] and applies [Stacks, Tag 0A1H] at
the perfect object `E^∨`; the Noetherian approximation of the source's proof is the one carried
out in the proof of [Stacks, Tag 0A1H].

## References

* [Stacks Project, Tag 0A1J](https://stacks.math.columbia.edu/tag/0A1J)
* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.SheafOfModules (derivedSheafHom)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0A1J].** Let `f : X ⟶ S` be a morphism of schemes of finite presentation, let
`E` be a perfect object of `D(𝒪_X)` and let `𝒢^•` be a bounded complex of finitely presented
`𝒪_X`-modules, flat over `S`, with support proper over `S`. Then
`K = Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•)` is a perfect object of `D(𝒪_S)`, and its formation commutes with
arbitrary base change: for every cartesian square the canonical map
`Lg^*Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•) ⟶ Rf'_*R𝓗om_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢^•)` of
`AlgebraicGeometry.sheafHomFlatBaseChangeMap` is an isomorphism. -/
@[stacks 0A1J]
theorem isPerfect_derivedPushforward_derivedSheafHom_and_isIso_sheafHomFlatBaseChangeMap
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (G : CochainComplex X.Modules ℤ)
    (hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      FlatProperSupportFinitelyPresented f G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
        ((derivedPushforward f.toLRSHom.toShHom).obj
          (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G))) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (hsq : IsPullback g' f' f g),
        IsIso (sheafHomFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G) :=
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  ⟨isPerfect_derivedPushforward_derivedSheafHom_of_finitePresentation f hf E hE G hG,
    fun g f' g' hsq =>
      isIso_sheafHomFlatBaseChangeMap_of_isPerfect f g f' g' hsq hf.quasiCompact
        hf.quasiSeparated _ E hE G hG.minus hG.isQuasicoherent hG.isFlatOver⟩

end AlgebraicGeometry

end
