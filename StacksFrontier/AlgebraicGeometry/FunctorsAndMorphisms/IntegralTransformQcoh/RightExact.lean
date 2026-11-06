module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Right exactness of an integral transform with affine source

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with `X` **affine**, and let
`K` be a quasi-coherent module on `X ×_R Y`.  The integral transform
`AlgebraicGeometry.quasicoherentIntegralTransform` attached to `K` is then right exact.

## Main definitions

* `AlgebraicGeometry.rightExactLinearCoproductFunctor` is the property of a functor between the
  categories of quasi-coherent modules of being `R`-linear, right exact, and commuting with
  arbitrary direct sums.

## Main results

* `AlgebraicGeometry.isAffineHom_pullback_snd`: the second projection of `X ×_R Y` is an affine
  morphism when `X` is affine, being the base change of the affine `X ⟶ Spec R`.
* `AlgebraicGeometry.preservesFiniteColimits_quasicoherentIntegralTransform`: the integral
  transform attached to a quasi-coherent kernel is right exact when `X` is affine.
* `AlgebraicGeometry.rightExactLinearCoproductFunctor_quasicoherentIntegralTransform`: the
  integral transform lies in the full subcategory cut out by the property above.

## Implementation notes

Right exactness is preservation of finite colimits.  **Affineness of `X` is not a convenience
hypothesis here**: the direct image along the second projection is the one factor of the
pullback--tensor--pushforward formula that is not right exact for formal reasons, and
`Stacks.AlgebraicGeometry.AffineQcohExactness` records a counterexample showing that it is
genuinely not right exact on all sheaves of modules.  What makes the composite right exact is
that `X` affine makes `X ⟶ Spec R` affine, hence the second projection affine as its base
change, and that every module appearing in the formula applied to a quasi-coherent module is
again quasi-coherent; the direct image along an affine morphism *is* right exact on
quasi-coherent modules.

Finite colimits are assembled from coequalizers and finite coproducts by
`CategoryTheory.Limits.preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts`.
The coequalizer half has to be proved one diagram at a time, not one shape at a time: the shape
statement `PreservesColimitsOfShape WalkingParallelPair (Scheme.Modules.pushforward _)` is false,
and only the diagrams whose two objects are quasi-coherent are available, which is exactly the
diagrams arising from the category of quasi-coherent modules.  The coproduct half is
`AlgebraicGeometry.quasicoherentIntegralTransform_preservesDirectSums`, whose index type ranges
over `Type u` while `CategoryTheory.Limits.PreservesFiniteCoproducts` asks for `Fin n` in
`Type 0`; the two are connected by the shape equivalence `Discrete (ULift (Fin n)) ≌
Discrete (Fin n)` rather than by instance search, which cannot cross that universe gap.

## References

* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

set_option synthInstance.maxHeartbeats 400000 in
/-- Quasi-coherent modules on a scheme have finite coproducts.  The coproducts are built here
from the ones indexed by `Type u` rather than left to instance search, which does not
find them in this file: `inferInstance` closes this statement in a file importing only
`StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic`
and **fails** as soon as
`StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact` is also imported, which this
file needs.  `HasFiniteColimits` of the same category is not synthesizable either way. -/
private theorem hasFiniteCoproducts_isQuasicoherent (X : Scheme.{u}) :
    HasFiniteCoproducts
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := by
  refine ⟨fun n => ?_⟩
  let : HasColimitsOfShape (Discrete (ULift.{u} (Fin n)))
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := inferInstance
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{u})

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- For `X` affine, the second projection of `X ×_R Y` is an affine morphism: the structure
morphism `X ⟶ Spec R` is a morphism of affine schemes, hence affine, and affineness of
morphisms is stable under base change. -/
@[sga "3 III 0.1.7" "(a), special case"]
theorem isAffineHom_pullback_snd [IsAffine X.left] :
    IsAffineHom (pullback.snd X.hom Y.hom) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback X.hom Y.hom) inferInstance

variable (K : (SheafOfModules.isQuasicoherent
  (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)

/-- Tensoring the pullback of a quasi-coherent module along the first projection with a
quasi-coherent kernel gives a quasi-coherent module.  This is the middle stage of the
pullback--tensor--pushforward formula. -/
theorem isQuasicoherent_tensorLeftFunctor_pullback
    (M : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨(pullback X.hom Y.hom).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
      (K.obj))).obj
      ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj))).IsQuasicoherent := by
  show ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((pullback X.hom
    Y.hom).toRingedSpace)).presheaf, (((pullback X.hom
    Y.hom).toRingedSpace)).IsSheaf⟩).obj (K.obj)).obj
    (((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).obj M.obj)))).IsQuasicoherent
  exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent _ K.obj _ K.property
    (@AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (pullback.fst X.hom Y.hom).toLRSHom.toShHom M.obj M.property)

/-- The pullback--tensor--pushforward formula preserves the colimit of a parallel pair of
quasi-coherent modules, when `X` is affine.  Each of the first three functors preserves all
colimits, and the direct image along the second projection preserves this one because the
projection is affine and the two modules in the diagram are quasi-coherent. -/
theorem preservesColimitsOfShape_walkingParallelPair_integralTransformFormula [IsAffine X.left] :
    PreservesColimitsOfShape WalkingParallelPair (integralTransformFormula R X Y K.obj) := by
  let P₁ := SheafOfModules.isQuasicoherent X.left.ringCatSheaf
  let ι₁ : P₁.FullSubcategory ⥤ X.left.Modules := ObjectProperty.ι P₁
  let PB := Scheme.Modules.pullback (pullback.fst X.hom Y.hom)
  let J := Opens.grothendieckTopology (pullback X.hom Y.hom).carrier
  let R' : Sheaf J CommRingCat :=
    ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩
  let ten : (pullback X.hom Y.hom).Modules ⥤ (pullback X.hom Y.hom).Modules :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨(pullback X.hom Y.hom).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
      (K.obj))
  let pf := Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)
  let : P₁.IsClosedUnderColimitsOfShape WalkingParallelPair :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape
      (K := WalkingParallelPair) X.left
  let : HasColimitsOfShape WalkingParallelPair P₁.FullSubcategory := inferInstance
  let : CreatesColimitsOfShape WalkingParallelPair (ObjectProperty.ι P₁) := inferInstance
  let : PreservesColimitsOfShape WalkingParallelPair ι₁ :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (ObjectProperty.ι P₁))
  let : PreservesColimitsOfSize.{u, u} ten :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits J R' K.obj
  let : PreservesColimitsOfShape (AsSmall.{u} WalkingParallelPair) ten := inferInstance
  let e : WalkingParallelPair ≌ AsSmall.{u} WalkingParallelPair := AsSmall.equiv
  let : PreservesColimitsOfShape WalkingParallelPair ten :=
    preservesColimitsOfShape_of_equiv e.symm ten
  let : IsAffineHom (pullback.snd X.hom Y.hom) := isAffineHom_pullback_snd R X Y
  refine ⟨fun {D} => ?_⟩
  let : PreservesColimit (D ⋙ ι₁ ⋙ PB ⋙ ten) pf :=
    Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_walkingParallelPair
      (pullback.snd X.hom Y.hom) (D ⋙ ι₁ ⋙ PB ⋙ ten)
      (isQuasicoherent_tensorLeftFunctor_pullback R X Y K (D.obj .zero))
      (isQuasicoherent_tensorLeftFunctor_pullback R X Y K (D.obj .one))
  exact inferInstanceAs (PreservesColimit D ((ι₁ ⋙ PB ⋙ ten) ⋙ pf))

/-- **Stacks Project, Tag 0FZD (right exactness).** For `X` affine, the integral transform
attached to a quasi-coherent kernel on `X ×_R Y` is right exact. -/
theorem preservesFiniteColimits_quasicoherentIntegralTransform [IsAffine X.left] :
    PreservesFiniteColimits (quasicoherentIntegralTransform R X Y K) := by
  let P₂ := SheafOfModules.isQuasicoherent Y.left.ringCatSheaf
  let T := quasicoherentIntegralTransformData R X Y K
  let : HasFiniteCoproducts
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory :=
    hasFiniteCoproducts_isQuasicoherent X.left
  let : HasCoequalizers
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory := inferInstance
  have hcoeq : PreservesColimitsOfShape WalkingParallelPair
      (quasicoherentIntegralTransform R X Y K) := by
    let : PreservesColimitsOfShape WalkingParallelPair (T.functor ⋙ ObjectProperty.ι P₂) :=
      @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _ T.comparison.symm
        (preservesColimitsOfShape_walkingParallelPair_integralTransformFormula R X Y K)
    exact preservesColimitsOfShape_of_reflects_of_preserves T.functor (ObjectProperty.ι P₂)
  have hcoprod : PreservesFiniteCoproducts (quasicoherentIntegralTransform R X Y K) := by
    refine ⟨fun n => ?_⟩
    let : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin n)))
        (quasicoherentIntegralTransform R X Y K) :=
      quasicoherentIntegralTransform_preservesDirectSums R X Y K (ULift.{u} (Fin n))
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  exact preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    (quasicoherentIntegralTransform R X Y K)

/-- The property of a functor between quasi-coherent module categories of being `R`-linear,
right exact, and commuting with arbitrary direct sums. -/
def rightExactLinearCoproductFunctor :
    ObjectProperty
      ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory) :=
  fun F =>
    let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
    (F.Additive ∧ F.Linear R) ∧ PreservesFiniteColimits F ∧
      ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F

/-- **Stacks Project, Tag 0FZD (the functor is in the subcategory).** For `X` affine, the
integral transform attached to a quasi-coherent kernel on `X ×_R Y` is `R`-linear, right exact
and commutes with arbitrary direct sums. -/
theorem rightExactLinearCoproductFunctor_quasicoherentIntegralTransform [IsAffine X.left] :
    rightExactLinearCoproductFunctor R X Y (quasicoherentIntegralTransform R X Y K) :=
  ⟨⟨quasicoherentIntegralTransform_additive R X Y K,
      quasicoherentIntegralTransform_isLinearOverBase R X Y K⟩,
    preservesFiniteColimits_quasicoherentIntegralTransform R X Y K,
    fun I => quasicoherentIntegralTransform_preservesDirectSums R X Y K I⟩

end AlgebraicGeometry

end
