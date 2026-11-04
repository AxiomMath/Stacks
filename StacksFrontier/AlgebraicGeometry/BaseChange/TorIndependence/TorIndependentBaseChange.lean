module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCompTransport
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparison
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentDerivedPullbackOpenImmersion

/-!
# Tor-independent base change for the derived direct image

Let `g : S' ⟶ S` be a morphism of schemes, let `f : X ⟶ S` be quasi-compact and quasi-separated,
and consider the base change diagram

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

If `X` and `S'` are Tor independent over `S`, then for every `E ∈ D_QCoh(𝒪_X)` the canonical
derived base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of Stacks 08HY is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_torIndependent`: the derived base change map
  is an isomorphism when `X` and `S'` are Tor independent over `S`.

## References

* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.BaseChangeCover

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- Let `g : S' ⟶ S` be a morphism of schemes, `f : X ⟶ S` quasi-compact and quasi-separated,
and `X' = X ×_S S'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ S'`. If `X` and `S'` are Tor
independent over `S`, then for every `E ∈ D_QCoh(𝒪_X)` the canonical arrow
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is an isomorphism. -/
@[stacks 08IB]
theorem isIso_derivedBaseChangeMap_of_torIndependent (sq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] (hTor : TorIndependent f g)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E).IsQuasicoherent) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w) E) := by
  have key := isIso_comp_of_affineOpens sq E ((derivedPullback g'.toLRSHom.toShHom).obj E) (𝟙 _)
    (fun V V' hV hV' hle U hU hUV => repGood_of_chart sq V V' hV hV' hle U hU hUV E _ (𝟙 _) (by
      intro ch
      have := ch.isOpenImmersion_incU
      have h₁ := isIso_derivedBaseChangeMap_specMap_of_torIndependent ch.isPushout
        (ch.torIndependent hTor) ((derivedPullback ch.incU.toLRSHom.toShHom).obj E)
        (isQuasicoherent_homology_derivedPullback_of_isOpenImmersion ch.incU E hE)
      have h₂ : IsIso (pullDatum (Spec.map ch.c).toLRSHom.toShHom ch.incU'.toLRSHom.toShHom
          ch.incU.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm ch.wU'U.symm) E
          ((derivedPullback g'.toLRSHom.toShHom).obj E) (𝟙 _)) := by
        rw [pullDatum_eq]
        infer_instance
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (Functor.map_isIso _ _)))
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using key

end AlgebraicGeometry
