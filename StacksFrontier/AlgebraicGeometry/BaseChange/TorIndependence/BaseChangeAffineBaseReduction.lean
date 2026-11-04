module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeLocalization
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.ReflectsIsomorphismsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08IB] over an affine base: the reduction along `Rg_*`

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes with `f` quasi-compact and quasi-separated and with `S` and
`S'` affine, and let `K` be a complex on `X` with quasi-coherent cohomology.  Both bases being
affine, the morphism `g` is affine, so the derived direct image `Rg_*` reflects isomorphisms
between complexes with quasi-coherent cohomology by [Stacks, Tag 08I8].  Both the source and
the target of the derived base-change map of [Stacks, Tag 08HY] have quasi-coherent cohomology:
the source by [Stacks, Tag 08D5] followed by [Stacks, Tag 08DW], the target the other way
round.  So the base-change map is invertible as soon as its derived direct image along `g` is.

This is the first step of the source's proof of [Stacks, Tag 08IB] after the localization on the
base, which is `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent_of_overAffineBase`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_derivedPullback_derivedPushforward` and
  `AlgebraicGeometry.isQuasicoherent_homology_derivedPushforward_derivedPullback`: the two sides
  of the base-change map have quasi-coherent cohomology.
* `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_derivedPushforward_map`: **the
  reduction along `Rg_*`**.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08I8](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {X' X S' S : Scheme.{u}}

/-- `Lg^*(Rf_*K)` has quasi-coherent cohomology sheaves when `f` is quasi-compact and
quasi-separated with affine target and `K` has quasi-coherent cohomology sheaves: this is
[Stacks, Tag 08D5] followed by [Stacks, Tag 08DW]. -/
theorem isQuasicoherent_homology_derivedPullback_derivedPushforward
    (f : X ⟶ S) (g : S' ⟶ S) [IsAffine S] [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) i).obj
      ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj K))).IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g _
    (fun j => isQuasicoherent_homologyFunctor_derivedPushforward f K hK j) i

/-- `Rf'_*(Lg'^*K)` has quasi-coherent cohomology sheaves when `f'` is quasi-compact and
quasi-separated with affine target and `K` has quasi-coherent cohomology sheaves: this is
[Stacks, Tag 08DW] followed by [Stacks, Tag 08D5]. -/
theorem isQuasicoherent_homology_derivedPushforward_derivedPullback
    (g' : X' ⟶ X) (f' : X' ⟶ S') [IsAffine S'] [QuasiCompact f'] [QuasiSeparated f']
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) i).obj
      ((derivedPushforward f'.toLRSHom.toShHom).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj K))).IsQuasicoherent :=
  isQuasicoherent_homologyFunctor_derivedPushforward f' _
    (fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g' K hK j) i

/-- **The reduction of [Stacks, Tag 08IB] over an affine base along `Rg_*`.**  For a Cartesian
square of schemes with `f` quasi-compact and quasi-separated and both bases affine, and for a
complex `K` on `X` with quasi-coherent cohomology, the derived base-change map of
[Stacks, Tag 08HY] is invertible as soon as its derived direct image along `g` is.

Both bases being affine, `g` is an affine morphism, so [Stacks, Tag 08I8] applies; its two
quasi-coherence hypotheses are
`AlgebraicGeometry.isQuasicoherent_homology_derivedPullback_derivedPushforward` and
`AlgebraicGeometry.isQuasicoherent_homology_derivedPushforward_derivedPullback`. -/
theorem isIso_derivedBaseChangeMap_of_isIso_derivedPushforward_map
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [IsAffine S] [IsAffine S'] (hsq : IsPullback g' f' f g)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (h : IsIso ((derivedPushforward g.toLRSHom.toShHom).map
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K))) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K) := by
  have := hqc
  have := hqs
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq hqc
  have : QuasiSeparated f' := MorphismProperty.of_isPullback (P := @QuasiSeparated) hsq hqs
  have : IsAffineHom g := isAffineHom_of_isAffine g
  exact Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isIso_of_isIso_derivedPushforward g
    (isQuasicoherent_homology_derivedPullback_derivedPushforward f g K hK)
    (isQuasicoherent_homology_derivedPushforward_derivedPullback g' f' K hK) _ h

end AlgebraicGeometry

end
