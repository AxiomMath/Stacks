module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces

/-!
# Change of source of an integral transform, as a functor of the kernel

Let `R` be a commutative ring and let `X`, `X'` and `Y` be schemes over `R`.  A morphism
`f : X' ⟶ X` over `R` induces `f × id_Y : X' ×_R Y ⟶ X ×_R Y`, and inverse image along it sends
a quasi-coherent kernel on `X ×_R Y` to one on `X' ×_R Y`.  This file records that assignment as
a functor and computes it on a composition of morphisms of sources and on the identity.

## Main definitions

* `AlgebraicGeometry.sourceChangeKernelFunctor` is inverse image along `f × id_Y`, on
  quasi-coherent modules.
* `AlgebraicGeometry.sourceChangeKernelFunctorComp` and
  `AlgebraicGeometry.sourceChangeKernelFunctorId`: the inverse images of kernels compose, and the
  identity induces the identity functor.

## Main results

* `AlgebraicGeometry.sourceChangeMap_comp` and `AlgebraicGeometry.sourceChangeMap_id`: the
  morphisms `f × id_Y` compose, and the identity induces the identity.
* `AlgebraicGeometry.sourceChangeKernelFunctor_obj`: on objects the functor is
  `AlgebraicGeometry.sourceChangeKernel`.

## References

* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (X X' X'' Y : Over (Spec (.of R)))

/-- The morphisms `f × id_Y` of Tag 0FZF compose. -/
theorem sourceChangeMap_comp (f : X' ⟶ X) (g : X'' ⟶ X') :
    sourceChangeMap R X' X'' Y g ≫ sourceChangeMap R X X' Y f =
      sourceChangeMap R X X'' Y (g ≫ f) := by
  rw [sourceChangeMap, sourceChangeMap, sourceChangeMap, pullback.map_comp]
  congr 1

/-- The identity of `X` induces the identity of `X ×_R Y`. -/
@[simp]
theorem sourceChangeMap_id : sourceChangeMap R X X Y (𝟙 X) = 𝟙 (pullback X.hom Y.hom) := by
  rw [sourceChangeMap]
  convert pullback.map_id (f := X.hom) (g := Y.hom) using 2

/-- Inverse image along `f × id_Y`, on quasi-coherent modules: the change of source of Tag 0FZF,
as a functor of the kernel. -/
def sourceChangeKernelFunctor (f : X' ⟶ X) :
    Scheme.QuasicoherentModules (pullback X.hom Y.hom) ⥤
      Scheme.QuasicoherentModules (pullback X'.hom Y.hom) :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent (pullback X'.hom Y.hom).ringCatSheaf)
    ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι ⋙
      Scheme.Modules.pullback (sourceChangeMap R X X' Y f))
    (fun K =>
      have : K.obj.IsQuasicoherent := K.property
      @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
        (sourceChangeMap R X X' Y f).toLRSHom.toShHom K.obj (by assumption))

/-- On objects, `sourceChangeKernelFunctor` is `sourceChangeKernel`. -/
@[simp]
theorem sourceChangeKernelFunctor_obj (f : X' ⟶ X)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    (sourceChangeKernelFunctor R X X' Y f).obj K = sourceChangeKernel R X X' Y f K := rfl

/-- The inverse images of kernels compose: changing the source along `g` and then along `f`
is changing it along `g ≫ f`. -/
def sourceChangeKernelFunctorComp (f : X' ⟶ X) (g : X'' ⟶ X') :
    sourceChangeKernelFunctor R X X' Y f ⋙ sourceChangeKernelFunctor R X' X'' Y g ≅
      sourceChangeKernelFunctor R X X'' Y (g ≫ f) :=
  ((SheafOfModules.isQuasicoherent
      (pullback X''.hom Y.hom).ringCatSheaf).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft
      (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι
      (Scheme.Modules.pullbackComp (sourceChangeMap R X' X'' Y g)
          (sourceChangeMap R X X' Y f) ≪≫
        Scheme.Modules.pullbackCongr (sourceChangeMap_comp R X X' X'' Y f g)))

/-- The identity induces the identity functor on quasi-coherent kernels. -/
def sourceChangeKernelFunctorId :
    sourceChangeKernelFunctor R X X Y (𝟙 X) ≅
      𝟭 (Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :=
  ((SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft
      (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).ι
      (Scheme.Modules.pullbackCongr (sourceChangeMap_id R X Y) ≪≫
        Scheme.Modules.pullbackId (pullback X.hom Y.hom)))

end AlgebraicGeometry

end
