module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorInstance
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapDegenerate
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the higher direct images along a flat morphism survives base change

Let `f : X ⟶ S` be a flat, quasi-compact and quasi-separated morphism, let `ℱ` be a
quasi-coherent `𝒪_X`-module which is flat as an `𝒪_X`-module, and suppose `R ⁱ f_* ℱ = 0` for
every `i > 0`.  Then for every cartesian square

```
X' --g'--> X
|f'        |f
S' --g---> S
```

one has `R ⁱ f'_* ((g')^* ℱ) = 0` for every `i > 0`.

The base-change morphism `g` is **arbitrary**: no flatness, no finiteness and no Noetherian
hypothesis is placed on it.  What replaces them is flatness of `f`, which is what makes the
square Tor independent.

## Main results

* `AlgebraicGeometry.FlatBaseChangeVanishing.isZero_rightDerivedPlus_pushforward_modulePullback`:
  the statement above, with the pullback spelled
  `RingedSpaceModuleAdjunction.modulePullback`.
* `AlgebraicGeometry.FlatBaseChangeVanishing.isZero_rightDerivedPlus_pushforward_pullback`: the
  same with the pullback spelled `AlgebraicGeometry.Scheme.Modules.pullback`.

## The argument

Nothing is assumed beyond what is already proved; the point is only that for a *vanishing*
conclusion the base-change comparison need not be the canonical map, so the isomorphisms used
below may be arbitrary.

* **Tor independence.** `AlgebraicGeometry.torIndependent_of_flat_left` makes `X` and `S'` Tor
  independent over `S` as soon as `f` is flat, and [Stacks, Tag 08IB]
  (`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_torIndependent`) then makes the derived
  base-change map `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K` invertible for every `K` with quasi-coherent
  cohomology.  It is applied at `K = ℱ[0]`, whose cohomology sheaves are `ℱ` and zero objects
  (`AlgebraicGeometry.isQuasicoherent_homology_singleFunctor_obj`).
* **The source side is concentrated in degrees `≤ 0`.** The vanishing hypothesis puts
  `Rf_*(ℱ[0])` in `D^{≤0}` by
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPushforward_singleFunctor`, and the
  derived pullback is right t-exact
  (`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj`), so `Lg^*Rf_*(ℱ[0])`
  is in `D^{≤0}` as well.
* **The target side is the ordinary pullback.** `ℱ` is flat, so `ℱ[0]` is K-flat and
  `L(g')^*(ℱ[0]) ≅ ((g')^*ℱ)[0]`, which is
  `Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso`.  Hence `Rf'_*(((g')^*
  ℱ)[0])` is in `D^{≤0}`, which is the vanishing asked for, read back through
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward`.

## Implementation notes

`HasDerivedCategory.standard` is activated at priority `10000`, as in every file of this cluster:
the import closure contains the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` at a
lower universe, and [Stacks, Tag 08IB] and the t-exactness statements are all elaborated at the
standard model.

The flatness of `ℱ` is `AlgebraicGeometry.SheafOfModules.IsFlat` over `X.toRingedSpace.sheaf`,
which is the spelling
`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` asks for.

## References

* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry.FlatBaseChangeVanishing

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Vanishing of the higher direct images survives an arbitrary base change, for a flat
morphism and a flat quasi-coherent module.** -/
theorem isZero_rightDerivedPlus_pushforward_modulePullback
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (hFflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.toRingedSpace.sheaf) F)
    (hvan : ∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj
      ((modulePullback g'.toLRSHom.toShHom).obj F)) := by
  -- `ℱ[0]` has quasi-coherent cohomology sheaves.
  have hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsQuasicoherent :=
    isQuasicoherent_homology_singleFunctor_obj X F hFqc
  -- [Stacks, Tag 08IB]: the derived base-change map is invertible.
  have hbc := isIso_derivedBaseChangeMap_of_torIndependent sq
    (torIndependent_of_flat_left f g) ((DerivedCategory.singleFunctor X.Modules 0).obj F) hE
  -- `Rf_*(ℱ[0])` lies in `D^{≤0}`, hence so does its derived pullback.
  have h1 : DerivedCategory.TStructure.t.IsLE
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) 0 :=
    isLE_derivedPushforward_singleFunctor f.toLRSHom.toShHom F 0 (fun j hj => hvan j hj)
  have h2 : DerivedCategory.TStructure.t.IsLE
      ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))) 0 :=
    isLE_derivedPullback_obj g.toLRSHom.toShHom _ 0 h1
  -- So the degree-`i` cohomology of the source of the base-change map vanishes.
  have h3 : IsZero ((DerivedCategory.homologyFunctor S'.Modules i).obj
      ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)))) :=
    -- `h2` is passed positionally: instance search unifies only at reducible transparency,
    -- where `X.Modules` and `SheafOfModules (structureSheafRing X.toRingedSpace)` do not meet.
    @DerivedCategory.isZero_of_isLE _ _ _ _ _ 0 i hi h2
  -- Transport along the base-change isomorphism, then along `L(g')^*(ℱ[0]) ≅ ((g')^*ℱ)[0]`.
  have h4 := h3.of_iso (((DerivedCategory.homologyFunctor S'.Modules i).mapIso
    (@asIso _ _ _ _ (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)) hbc)).symm)
  have h5 := h4.of_iso ((DerivedCategory.homologyFunctor S'.Modules i).mapIso
    ((derivedPushforward f'.toLRSHom.toShHom).mapIso
      (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso
        g'.toLRSHom.toShHom F hFflat).symm))
  exact isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward f' _ i h5

/-- **Vanishing of the higher direct images survives an arbitrary base change**, with the
pullback spelled `AlgebraicGeometry.Scheme.Modules.pullback`.  The two spellings of the pullback
of modules are the same term. -/
theorem isZero_rightDerivedPlus_pushforward_pullback
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (hFflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.toRingedSpace.sheaf) F)
    (hvan : ∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj
      ((Scheme.Modules.pullback g').obj F)) :=
  isZero_rightDerivedPlus_pushforward_modulePullback sq F hFqc hFflat hvan i hi

end AlgebraicGeometry.FlatBaseChangeVanishing

end
