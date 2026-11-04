module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsProjectiveOfChartPullback
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Invertible and relatively ample modules, from a scheme to the algebraic space it represents

Let `T` be a scheme of the big fppf site over `S` and `schemeSpace T` the algebraic space it
represents. Write `Φ_T` for the passage from modules on the Zariski site of `T` to `𝒪`-modules on
the small étale site of `schemeSpace T`: the associated module `𝓕 ↦ 𝓕^a` of Stacks 03DU on the
small étale site of `T` (`AlgebraicGeometry.SmallEtale.associatedModule`), followed by the
identification of that site with the small étale site of `yoneda.obj T`
(`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`). On quasi-coherent modules it
is the equivalence of Stacks 03DX,
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.

The library already knows that `Φ_T` preserves invertibility (in the namespace
`AlgebraicGeometry.Space`,
`isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule`) and that it is
compatible with pullback along a morphism `g : T' ⟶ T` of the site:
`g^*(Φ_T 𝓕) ≅ Φ_{T'}(g^*𝓕)` (`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`).
This file adds the compatibility with relative ampleness, Stacks 0D31 against Stacks 01VH. The
reading `AlgebraicGeometry.Space.baseChangeModule` of `Φ_T L` on a scheme `U` over `T` is the
Zariski pullback of `L`. Stacks 0D32 then turns an `L` that is relatively ample for a morphism of
schemes `q : T ⟶ V` into a `Φ_T L` that is relatively ample for `schemeSpaceMap q`. The same
holds for an algebraic space presented by a scheme, through the presentation.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_associatedModule_schemeSpace`: `Φ_T` preserves
  quasi-coherence.
* `AlgebraicGeometry.Space.baseChangeModuleAssociatedModuleIso`: the reading of `Φ_T L` along
  `r : U ⟶ T` is `r^*L`, for `L` quasi-coherent.
* `AlgebraicGeometry.Space.isRelativelyAmple_of_baseChangeModule_iso`: clause (2) of Stacks 0D32
  implies clause (1), when the reading is given up to isomorphism.
* `AlgebraicGeometry.Space.isRelativelyAmple_schemeSpaceMap_associatedModule`: **`Φ_T` carries a
  module ample relative to `q : T ⟶ V` to one ample relative to `schemeSpaceMap q`.**
* `AlgebraicGeometry.Space.exists_isInvertibleModule_isRelativelyAmple_of_presentation`: **an
  algebraic space `X ⟶ Y` over a scheme, presented by a scheme `U` that carries an invertible
  module ample over the target, carries an invertible module ample relative to `X ⟶ Y`.**

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The `𝒪`-module on the small étale site of `schemeSpace T` attached to a quasi-coherent module
`L` on the scheme underlying `T` is quasi-coherent. -/
theorem isQuasicoherentOnSite_associatedModule_schemeSpace (T : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj T).Modules) (hL : L.IsQuasicoherent) :
    ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj L)).IsQuasicoherentOnSite :=
  ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj ⟨L, hL⟩).property

/-- **The reading of the transferred module on a scheme over `T` is the Zariski pullback.** For a
quasi-coherent module `L` on the scheme underlying `T` and a morphism `r : U ⟶ T` of the site,
the module `Φ_T L` read on `U` along `p = h_r` is `r^*L`.

The reading along a chart is the Zariski pullback of the restriction to that chart
(`AlgebraicGeometry.Space.baseChangeModuleIsoPullbackRestrictToChart`), taken at the self chart
of `yoneda.obj T`, and that restriction recovers `L`
(`AlgebraicGeometry.Space.restrictToChart_selfChart_representedQuasicoherentIso`). -/
def baseChangeModuleAssociatedModuleIso (T : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj T).Modules) (hL : L.IsQuasicoherent)
    {U : BigFppfOver B S hS} (r : U ⟶ T) (p : yoneda.obj U ⟶ (schemeSpace T).1)
    (hp : yoneda.map r = p) :
    baseChangeModule B S hS (X := schemeSpace T)
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj L)) U p ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj L :=
  eqToIso (by rw [← hp]; rfl) ≪≫
    (baseChangeModuleIsoPullbackRestrictToChart B S hS (X := schemeSpace T) _
      (isQuasicoherentOnSite_associatedModule_schemeSpace T L hL) (selfChart B S hS T) r).symm ≪≫
    (Scheme.Modules.pullback _).mapIso
      (restrictToChart_selfChart_representedQuasicoherentIso B S hS T L hL)

/-- **Stacks 0D32, clause (2) implies clause (1), up to isomorphism of the reading.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces, with `Y` presented by a scheme `V` and `X` by a
scheme `U`, and let `N` be an invertible `𝒪_X`-module whose reading on `U` is isomorphic to a
module `L` that is invertible and ample relative to the morphism `U ⟶ V` induced by `f`. Then
`N` is ample relative to `f`.

This is `AlgebraicGeometry.Space.isRelativelyAmple_of_exists_scheme`, with invertibility and
ampleness moved along the isomorphism. -/
theorem isRelativelyAmple_of_baseChangeModule_iso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property N)
    (V : BigFppfOver B S hS) (eY : Y.1 ≅ yoneda.obj V) (U : BigFppfOver B S hS)
    (eX : yoneda.obj U ≅ X.1) (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) L]
    (e : baseChangeModule B S hS N U eX.hom ≅ L)
    (hamp : Stacks.RelativeAmple.IsRelativelyAmple
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (eX.hom ≫ f.hom ≫ eY.hom))) L) :
    IsRelativelyAmple B S hS f N := by
  have hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS N U eX.hom) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
  exact isRelativelyAmple_of_exists_scheme f N hN V eY ⟨U, eX, hinv,
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e.symm).mp hamp⟩

/-- The reading of `Φ_T L` along `p = h_{𝟙 T}` is `L`, for an invertible module `L`. -/
private def baseChangeModuleAssociatedModuleIsoSelf (T : BigFppfOver B S hS)
    (L : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj T) L]
    (p : yoneda.obj T ⟶ (schemeSpace T).1) (hp : yoneda.map (𝟙 T) = p) :
    baseChangeModule B S hS (X := schemeSpace T)
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj L)) T p ≅ L :=
  baseChangeModuleAssociatedModuleIso T L
      (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L) (𝟙 T) p hp ≪≫
    (Scheme.Modules.pullbackCongr (by simp)).app L ≪≫ (Scheme.Modules.pullbackId _).app L

/-- **The transfer carries relative ampleness to relative ampleness.** Let `q : T ⟶ V` be a
morphism of the site and `L` an invertible module on the scheme underlying `T`, ample relative to
the underlying morphism of schemes in the sense of Stacks 01VH. Then `Φ_T L` is ample relative to
`schemeSpaceMap q` in the sense of Stacks 0D31.

The reading of `Φ_T L` on `T` itself is `L`
(`AlgebraicGeometry.Space.baseChangeModuleAssociatedModuleIso` at the identity), so clause (2) of
Stacks 0D32 holds at the identity presentations. -/
@[ega "II 4.6.13" "(iii)"]
theorem isRelativelyAmple_schemeSpaceMap_associatedModule {T V : BigFppfOver B S hS} (q : T ⟶ V)
    (L : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    [hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj T) L]
    (hamp : Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B S hS).map q) L) :
    IsRelativelyAmple B S hS (schemeSpaceMap q)
      ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj L)) := by
  have hq : yoneda.preimage ((Iso.refl (yoneda.obj T)).hom ≫ (schemeSpaceMap q).hom ≫
      (Iso.refl (yoneda.obj V)).hom) = q := by
    apply yoneda.map_injective
    simp only [Functor.map_preimage, Iso.refl_hom, Category.id_comp]
    rfl
  refine isRelativelyAmple_of_baseChangeModule_iso (schemeSpaceMap q) _
    (isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
      B S hS T L hL) V (Iso.refl _) T (Iso.refl _) L
    (baseChangeModuleAssociatedModuleIsoSelf T L _ (by simp)) ?_
  convert hamp
  exact hq

/-- **A relatively ample module on a scheme presenting an algebraic space gives one on the
space.** Let `f : X ⟶ Y` be a morphism of algebraic spaces, `eY : Y ≅ h_V` a presentation of `Y`
by a scheme `V` and `eX : h_U ≅ X` a presentation of `X` by a scheme `U`. Let `L` be an invertible
module on `U`, ample relative to the morphism `U ⟶ V` induced by `f`. Then `X` carries an
invertible module `N`, ample relative to `f`, whose reading on `U` along `eX` is `L`.

`N` is the pullback of `Φ_U L` along the inverse of the presentation. -/
theorem exists_isInvertibleModule_isRelativelyAmple_of_presentation
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (V : BigFppfOver B S hS) (eY : Y.1 ≅ yoneda.obj V)
    (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
    (L : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    [hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) L]
    (hamp : Stacks.RelativeAmple.IsRelativelyAmple
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (eX.hom ≫ f.hom ≫ eY.hom))) L) :
    ∃ N : Modules.{u, u} B S hS X.1 X.2, IsInvertibleModule X N ∧
      IsRelativelyAmple B S hS f N ∧ Nonempty (baseChangeModule B S hS N U eX.hom ≅ L) := by
  let p : X ⟶ schemeSpace U := ObjectProperty.homMk eX.inv
  have hN : IsInvertibleModule X ((modulePullback B S hS p).obj
      ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj L))) :=
    modulePullbackInvertible p _
      (isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule
        B S hS U L hL)
  let e := (baseChangeModuleCompIso B S hS p _ U eX.hom).symm ≪≫
    baseChangeModuleAssociatedModuleIsoSelf U L _ (by simp only [p]; exact eX.hom_inv_id.symm)
  exact ⟨_, hN, isRelativelyAmple_of_baseChangeModule_iso f _ hN V eY U eX L e hamp, ⟨e⟩⟩

end AlgebraicGeometry.Space
