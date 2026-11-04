module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.Extension
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernels
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic

/-!
# Coherent kernels with support finite over the target

Let `k` be a field and let `X` and `Y` be schemes over `k`. This file names the two categories
compared in [Stacks, Tag 0FZN]:

* the `k`-linear exact functors `Coh(𝒪_X) ⥤ Coh(𝒪_Y)`, and
* the coherent `𝒪_{X ×_k Y}`-modules `𝒦` which are flat over `X` and whose support is finite
  over `Y`.

## Main definitions

* `AlgebraicGeometry.CoherentKernels.coherentModulesLinear`: the `k`-linear structure on
  `Coh(𝒪_X)`, the full subcategory of the `k`-linear category of `𝒪_X`-modules.
* `AlgebraicGeometry.CoherentKernels.exactLinearCoherentFunctor`: the `k`-linear exact functors
  `Coh(𝒪_X) ⥤ Coh(𝒪_Y)`.
* `AlgebraicGeometry.CoherentKernels.HasFiniteSupportOver`: a quasi-coherent module of finite
  type on `X ×_k Y` whose scheme-theoretic support is finite over `Y`.
* `AlgebraicGeometry.CoherentKernels.finiteFlatCoherentKernel`: the coherent kernels flat over
  `X` with support finite over `Y`.

## Implementation notes

The support of a coherent module is read as its scheme-theoretic support
`AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport`, the closed subscheme cut out by the
annihilator; "finite over `Y`" is finiteness of the composite of its closed immersion with the
second projection. This is the closed subscheme the source's proof shows to be finite over `Y`.

## References

* [Stacks Project, Tag 0FZN](https://stacks.math.columbia.edu/tag/0FZN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (CoherentModules)

universe u

namespace AlgebraicGeometry.CoherentKernels

/-- The `R`-linear structure on the coherent `𝒪_X`-modules of a scheme over `R`: the full
subcategory of the `R`-linear category of all `𝒪_X`-modules. -/
@[instance_reducible]
def coherentModulesLinear (R : Type u) [CommRing R] (X : Over (Spec (.of R))) :
    Linear R (CoherentModules X.left.ringCatSheaf) :=
  letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  Linear.fullSubcategory _

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k)))

/-- **Category (1) of Tag 0FZN.** The property of a functor `Coh(𝒪_X) ⥤ Coh(𝒪_Y)` of being
`k`-linear and exact. -/
def exactLinearCoherentFunctor :
    ObjectProperty (CoherentModules X.left.ringCatSheaf ⥤ CoherentModules Y.left.ringCatSheaf) :=
  fun F =>
    letI := coherentModulesLinear k X
    letI := coherentModulesLinear k Y
    F.Linear k ∧ exactFunctor _ _ F

/-- A quasi-coherent module of finite type on `X ×_k Y` **has support finite over `Y`** when its
scheme-theoretic support is finite over `Y`. -/
def HasFiniteSupportOver (K : (pullback X.hom Y.hom).Modules) [K.IsQuasicoherent]
    [K.IsFiniteType] : Prop :=
  IsFinite ((Scheme.Modules.schemeTheoreticSupport K).subschemeι ≫ pullback.snd X.hom Y.hom)

/-- **Category (2) of Tag 0FZN.** The property of a quasi-coherent module `𝒦` on `X ×_k Y` of
being coherent, flat over `X`, and of having support finite over `Y`. -/
def finiteFlatCoherentKernel :
    ObjectProperty
      ((SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :=
  fun K =>
    ∃ h : K.obj.IsCoherent,
      IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj ∧
        letI : K.obj.IsQuasicoherent := K.property
        letI : K.obj.IsFiniteType := h.isFiniteType
        HasFiniteSupportOver k X Y K.obj

end AlgebraicGeometry.CoherentKernels

end
