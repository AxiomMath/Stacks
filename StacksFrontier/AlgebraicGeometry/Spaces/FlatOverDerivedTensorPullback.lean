module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverTensorPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationBounds

/-!
# Derived tensor product with the derived pullback of a module, against a module flat over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `𝒢` an `𝒪_X`-module flat over `Y` at every
geometric point (Stacks 05VU (2)) and `ℱ` an `𝒪_Y`-module. Then
`𝒢 ⊗^L_{𝒪_X} Lf^*ℱ ≅ (𝒢 ⊗_{𝒪_X} f^*ℱ)[0]`, because `𝒩 ↦ 𝒢 ⊗ f^*𝒩` is exact
(`AlgebraicGeometry.Space.preservesFiniteLimits_tensorPullbackFunctor`).

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorPullbackSingleIso`: the isomorphism.
* `AlgebraicGeometry.Space.isGE_smallEtaleDerivedTensor_pullback_of_isFlatOver`: for a bounded
  complex `𝒢^•` of modules flat over `Y` vanishing below `a`, `𝒢^• ⊗^L Lf^*ℱ ∈ D^{≥ a}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **`𝒢 ⊗^L Lf^*ℱ ≅ (𝒢 ⊗ f^*ℱ)[0]` for `𝒢` flat over `Y`.** -/
def smallEtaleDerivedTensorPullbackSingleIso
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hG : ∀ x, IsFlatOverAtGeometricPoint B S hS f G x)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    ((smallEtaleDerivedTensor B S hS X).obj ((DerivedCategory.singleFunctor _ 0).obj G)).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((tensorPullbackFunctor f G).obj F) :=
  haveI : PreservesFiniteLimits (Stacks.Cohomology.DerivedPullbackOfToposHom.tensorPullback
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f) G) :=
    preservesFiniteLimits_tensorPullbackFunctor f G hG
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedTensorPullbackSingleIso
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f) (smallEtaleDerivedTensorProduct B S hS X) G F

/-- **A bounded complex of modules flat over `Y` vanishing below `a`, derived tensored with the
derived pullback of a module, has no cohomology below `a`.** Along the stupid filtration this
reduces to the terms, where `𝒢ⁱ ⊗^L Lf^*ℱ = (𝒢ⁱ ⊗ f^*ℱ)[0]`. -/
theorem isGE_smallEtaleDerivedTensor_pullback_of_isFlatOver
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (a : ℤ) (hGa : ∀ i, i < a → IsZero (G.X i))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).IsGE a := by
  let L :=
    (smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  refine @StacksDraft.ExtremalDegrees.isGE_map_Q_of_terms _ _ _ _ _ _
    ((smallEtaleDerivedTensor B S hS X).flip.obj L)
    ((smallEtaleDerivedTensorProduct B S hS X).commShift_left L)
    ((smallEtaleDerivedTensorProduct B S hS X).exact_left L) G hGb a fun i hi => ?_
  have hai : a ≤ i := not_lt.1 fun h => hi (hGa i h)
  have key : ∀ M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X),
      ((DerivedCategory.singleFunctor _ 0).obj M).IsGE 0 := fun M => inferInstance
  have := key ((tensorPullbackFunctor f (G.X i)).obj F)
  have : (((smallEtaleDerivedTensor B S hS X).obj
      ((DerivedCategory.singleFunctor _ 0).obj (G.X i))).obj L).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (smallEtaleDerivedTensorPullbackSingleIso f (G.X i) (hG i) F).symm 0
  exact DerivedCategory.TStructure.t.isGE_of_ge (((smallEtaleDerivedTensor B S hS X).obj
    ((DerivedCategory.singleFunctor _ 0).obj (G.X i))).obj L) (a - i) 0 (by omega)

end AlgebraicGeometry.Space

end
