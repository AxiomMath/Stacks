module

public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocus
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport

/-!
# Descending flatness of the base-changed module along a morphism of the base

For the family of Situation 05MP, an open `V` of the base change `X ×_S T` and a morphism
`T' ⟶ T` of schemes over `S`, the module on the preimage of `V` in `X ×_S T'` is the pullback of
the module on `V` along the fibre product `V ×_T T'`. This file records that identification in the
two forms needed to feed the approximation theorem for relative flatness, Stacks 05LY, with a
cofiltered system of affine schemes over the base: once to turn the hypothesis of that theorem
into a statement about the preimage of `V` in the base change to the limit, and once to turn its
conclusion into a statement about the preimage of `V` in the base change to a stage.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.isFlatOver_chart_iff`: flatness over the new base
  of the module on the fibre-product presentation of the preimage of `V` is flatness over the new
  base of the module on that preimage.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.isFlatOver_of_invertibleRank`: a base-changed
  module which is finite locally free of a fixed rank on an open of the base change is flat over
  the base there.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_isFlatOver_preimage`: **Stacks 05LY** for
  the base changes of a cofiltered system of affine schemes over the base, applied to an affine
  open of one stage.

## Implementation notes

The preimage of `V` is compared with the fibre product by `IsPullback.isoIsPullback`: the square
exhibiting the preimage of an open as a fibre product (`isPullback_morphismRestrict`) pastes onto
the square exhibiting a transition morphism of base changes as a base change
(`isPullback_transitionHom`), and both are fibre products of the same cospan. Flatness is then
carried across by `isFlatOver_pullback_iff_of_iso`, which replaces the source of a morphism by an
isomorphic scheme, and the two readings of the module are compared by the pullback-of-a-composite
isomorphism together with `transitionModuleIso`.

Stacks 05LY is stated for a morphism `X ⟶ Y` of schemes of finite presentation over a stage. It is
applied here with `X` the chosen affine open `V` of the base change, `Y` the stage itself, and the
morphism the restricted base change: `V` affine and the stage affine make that morphism of finite
presentation, which is why an *affine* open is chosen rather than merely a quasi-compact one — the
family of the situation is not assumed quasi-compact, so the base change itself is not of finite
presentation over the stage. The conclusion of Stacks 05LY is stated with the morphism of fibre
products induced by the structure morphism of `V`; composing with the projection of the fibre
product along the identity, which is an isomorphism and hence flat, turns that morphism into the
projection to the new base, which is the form `isFlatOver_chart_iff` consumes.

Flatness of a finite locally free module over the base uses only that the base change of the
family is flat, which it is because the family is smooth.

## References

* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01BQ** for a morphism of schemes: the pullback of a module of finite
presentation is of finite presentation. -/
instance pullbackObj_isFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) [hF : F.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj F).IsFinitePresentation :=
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ f.toLRSHom.toShHom F hF

/-- Finite presentation of a module on a scheme, read on the underlying ringed space. -/
private lemma isFinitePresentation_ringSheafOf {X : Scheme.{u}} (F : X.Modules)
    [hF : F.IsFinitePresentation] :
    SheafOfModules.IsFinitePresentation.{u, u, u} (R := structureSheafRing X.toRingedSpace) F := hF

namespace FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-- The preimage of an open of one base change in another, compared with the fibre product. -/
private noncomputable def chartIso {T T' : Over D.S} (g : T' ⟶ T)
    (V : (pullback D.f T.hom).Opens) :
    (D.transitionHom g ⁻¹ᵁ V).toScheme ≅ pullback (V.ι ≫ D.baseChangeMap T) g.left :=
  IsPullback.isoIsPullback _ _
    ((isPullback_morphismRestrict (D.transitionHom g) V).paste_vert
      (D.isPullback_transitionHom g))
    (IsPullback.of_hasPullback _ _)

@[simp]
private lemma chartIso_hom_fst {T T' : Over D.S} (g : T' ⟶ T) (V : (pullback D.f T.hom).Opens) :
    (D.chartIso g V).hom ≫ pullback.fst (V.ι ≫ D.baseChangeMap T) g.left =
      D.transitionHom g ∣_ V :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[simp]
private lemma chartIso_hom_snd {T T' : Over D.S} (g : T' ⟶ T) (V : (pullback D.f T.hom).Opens) :
    (D.chartIso g V).hom ≫ pullback.snd (V.ι ≫ D.baseChangeMap T) g.left =
      (D.transitionHom g ⁻¹ᵁ V).ι ≫ D.baseChangeMap T' :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The module on the preimage open, read through the fibre product. -/
private noncomputable def chartModuleIso {T T' : Over D.S} (g : T' ⟶ T)
    (V : (pullback D.f T.hom).Opens) :
    (Scheme.Modules.pullback (D.transitionHom g ∣_ V)).obj
        ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T)) ≅
      (Scheme.Modules.pullback (D.transitionHom g ⁻¹ᵁ V).ι).obj (D.baseChangeModule T') :=
  (Scheme.Modules.pullbackComp (D.transitionHom g ∣_ V) V.ι).app (D.baseChangeModule T) ≪≫
    eqToIso (congrArg (fun k : (D.transitionHom g ⁻¹ᵁ V).toScheme ⟶ pullback D.f T.hom =>
      (Scheme.Modules.pullback k).obj (D.baseChangeModule T))
      (morphismRestrict_ι (D.transitionHom g) V)) ≪≫
    ((Scheme.Modules.pullbackComp (D.transitionHom g ⁻¹ᵁ V).ι (D.transitionHom g)).app
      (D.baseChangeModule T)).symm ≪≫
    (Scheme.Modules.pullback (D.transitionHom g ⁻¹ᵁ V).ι).mapIso (D.transitionModuleIso g)

/-- Flatness over the base of the module on the fibre-product presentation of the preimage of an
open is flatness over the base of the module on that preimage. -/
theorem isFlatOver_chart_iff {T T' : Over D.S} (g : T' ⟶ T)
    (V : (pullback D.f T.hom).Opens) :
    IsFlatOver (pullback.snd (V.ι ≫ D.baseChangeMap T) g.left).toLRSHom.toShHom
        ((Scheme.Modules.pullback
          (pullback.fst (V.ι ≫ D.baseChangeMap T) g.left)).obj
          ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T))) ↔
      IsFlatOver ((D.transitionHom g ⁻¹ᵁ V).ι ≫ D.baseChangeMap T').toLRSHom.toShHom
        ((Scheme.Modules.pullback (D.transitionHom g ⁻¹ᵁ V).ι).obj
          (D.baseChangeModule T')) := by
  rw [isFlatOver_pullback_iff_of_iso _ _ (D.chartIso g V), D.chartIso_hom_fst g V,
    D.chartIso_hom_snd g V]
  exact isFlatOver_iff_of_moduleIso _ (D.chartModuleIso g V)

/-- A base-changed module which is finite locally free of rank `p` on an open of the base change
is flat over the base there: the base change of the family is flat. -/
theorem isFlatOver_of_invertibleRank (T : Over D.S) (V : (pullback D.f T.hom).Opens)
    (hV : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T)) p) :
    IsFlatOver (V.ι ≫ D.baseChangeMap T).toLRSHom.toShHom
      ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T)) := by
  have hrk : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T)) p :=
    { exists_isFiniteLocallyFreeOfRankData := hV.exists_isFiniteLocallyFreeOfRankData }
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T)) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule T)) p
  exact VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree _ _

/-- **Stacks Project, Tag 05LY** for the base changes of a cofiltered system of affine schemes
over the base: if the module on the preimage of an affine open of one stage is flat over the
limit, then it is flat over some later stage. -/
theorem exists_isFlatOver_preimage {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Over D.S) (c : Cone E) (hc : IsLimit ((Over.forget D.S).mapCone c))
    (hE : ∀ i, IsAffine ((Over.forget D.S).obj (E.obj i))) [D.F.IsFinitePresentation]
    (i : I) (V : (pullback D.f (E.obj i).hom).Opens) (hV : IsAffine V.toScheme)
    (hflat : IsFlatOver
      ((D.transitionHom (c.π.app i) ⁻¹ᵁ V).ι ≫ D.baseChangeMap c.pt).toLRSHom.toShHom
      ((Scheme.Modules.pullback (D.transitionHom (c.π.app i) ⁻¹ᵁ V).ι).obj
        (D.baseChangeModule c.pt))) :
    ∃ (j : I) (e : j ⟶ i), IsFlatOver
      ((D.transitionHom (E.map e) ⁻¹ᵁ V).ι ≫ D.baseChangeMap (E.obj j)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (D.transitionHom (E.map e) ⁻¹ᵁ V).ι).obj
        (D.baseChangeModule (E.obj j))) := by
  have hAff : ∀ k : I, IsAffine ((E ⋙ Over.forget D.S).obj k) := hE
  have hAffL : ∀ k : I, IsAffine (E.obj k).left := hE
  have hfpX : AlgebraicGeometry.FinitePresentation (V.ι ≫ D.baseChangeMap (E.obj i)) :=
    finitePresentation_of_compactSpace _ inferInstance
  have hfpY : AlgebraicGeometry.FinitePresentation (𝟙 ((E.obj i).left)) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hqc := AlgebraicGeometry.isQuasicoherent_ringSheaf
    ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule (E.obj i)))
  have hfp := isFinitePresentation_ringSheafOf
    ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule (E.obj i)))
  obtain ⟨j, e, hj⟩ := eventually_isFlatOver_modulePullback (E ⋙ Over.forget D.S)
    ((Over.forget D.S).mapCone c) hc i (Over.mk (V.ι ≫ D.baseChangeMap (E.obj i)))
    (Over.mk (𝟙 _)) hfpX hfpY (Over.homMk (V.ι ≫ D.baseChangeMap (E.obj i)) (by simp))
    ((Scheme.Modules.pullback V.ι).obj (D.baseChangeModule (E.obj i)))
    ((isFlatOver_overPullback_map_iff (Over.mk (V.ι ≫ D.baseChangeMap (E.obj i)))
      (c.π.app i).left _).mpr ((D.isFlatOver_chart_iff (c.π.app i) V).mpr hflat))
  exact ⟨j, e, (D.isFlatOver_chart_iff (E.map e) V).mp
    ((isFlatOver_overPullback_map_iff (Over.mk (V.ι ≫ D.baseChangeMap (E.obj i)))
      (E.map e).left _).mp hj)⟩

end FreeAtGenericPointsSituation
end AlgebraicGeometry
end
