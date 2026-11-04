module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackTrivial
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.CoefficientMap
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Pullback

/-!
# The difference from the trivial lift along a morphism of thickenings, from the classes

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` and `h₂ : T ⟶ T'₂`
split first order thickenings (retractions `r`, `r₂`), and `g : T'₂ ⟶ T'` a morphism under `T`.
The difference of a class of lifts from the trivial lift is the class on `X_T` of its extension
minus that of the trivial lift
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_mk`), and the trivial lift has
class zero (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_trivial`). So the
difference is natural along `g`, with the coefficient map
`AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientMap`, as soon as the class on `X_T`
of a lift is: the class of the pulled back lift is the class of the lift followed by the
coefficient map.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback_of_extClass`.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback_of_forall_extClass`:
  the same for all morphisms of split thickenings compatible with the retractions, in the shape
  of the hypothesis `hgen` of
  `AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifferencePullback_of_pullback`.

## Implementation notes

The naturality of the classes on `X_T` of lifts is taken as the explicit hypothesis `hA` of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback_of_extClass`: it is
proved separately, from the morphism of extensions given by the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, and
this module only does the reduction from differences to classes.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe e u

-- At default priority, `HasExt (SheafOfModules _)` gets stuck on a universe constraint
attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

section Fixed

variable {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
  (r : T' ⟶ ξ.T) (hr : h ≫ r = 𝟙 ξ.T)
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hfl : IsFlat B S hS (D.projection T').hom)
  (r₂ : T'₂ ⟶ ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

/-- **The difference from the trivial lift is natural along `g : T'₂ ⟶ T'` under `T`, as soon as
the class on `X_T` of a lift is.** The hypothesis `hA` is that naturality of classes: the class
of the pullback `L.pullback g hg` across `h₂` is the class of `L` across `h` followed by the
coefficient map `𝒢 ⊗ f_T^*𝒥 ⟶ 𝒢 ⊗ f_T^*𝒥₂`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientMap`). -/
theorem thickeningLiftDifference_pullback_of_extClass
    (hA : ∀ L : D.ThickeningLift ξ h,
      thickeningLiftExtClass h₂ r₂ hr₂ hh₂ hfl₂ (L.pullback g hg) =
        (thickeningLiftExtClass h r hr hh hfl L).comp
          (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1))
    (c : D.ThickeningLiftClass ξ h) :
    thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
      (thickeningLiftDifference h r hr hh hfl c).comp
        (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1) := by
  induction c using Quotient.ind with
  | _ L =>
    rw [ThickeningLiftClass.pullback_mk, thickeningLiftDifference_mk, thickeningLiftDifference_mk,
      thickeningLiftExtClass_trivial, thickeningLiftExtClass_trivial, sub_zero, sub_zero]
    exact hA L

end Fixed

/-- **The difference from the trivial lift is natural along every morphism of split first order
thickenings compatible with the retractions, as soon as the class on `X_T` of a lift is**: the
hypothesis `hA` is the naturality of classes for all such data, and the conclusion is the
naturality of the differences, with the binders in the same order, for all such data. -/
theorem thickeningLiftDifference_pullback_of_forall_extClass
    (hA : ∀ {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
      (r : T' ⟶ ξ.T) (hr : h ≫ r = 𝟙 ξ.T)
      (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
      (hfl : IsFlat B S hS (D.projection T').hom)
      (r₂ : T'₂ ⟶ ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
      (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
      (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
      (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (_ : r₂ = g ≫ r)
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
      (L : D.ThickeningLift ξ h),
      thickeningLiftExtClass h₂ r₂ hr₂ hh₂ hfl₂ (L.pullback g hg) =
        (thickeningLiftExtClass h r hr hh hfl L).comp
          (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1)) :
    ∀ {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
      (r : T' ⟶ ξ.T) (hr : h ≫ r = 𝟙 ξ.T)
      (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
      (hfl : IsFlat B S hS (D.projection T').hom)
      (r₂ : T'₂ ⟶ ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
      (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
      (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
      (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (_ : r₂ = g ≫ r)
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
      [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
      (c : D.ThickeningLiftClass ξ h),
      thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
        (thickeningLiftDifference h r hr hh hfl c).comp
          (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1) :=
  fun r hr hh hfl r₂ hr₂ hh₂ hfl₂ g hg hgr _ _ _ _ _ c =>
    thickeningLiftDifference_pullback_of_extClass r hr hh hfl r₂ hr₂ hh₂ hfl₂ g hg
      (hA r hr hh hfl r₂ hr₂ hh₂ hfl₂ g hg hgr) c

end AlgebraicGeometry.Space.CoherentSituation

end
