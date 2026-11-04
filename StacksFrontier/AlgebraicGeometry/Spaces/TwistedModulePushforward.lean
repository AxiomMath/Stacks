module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# Twists commute with direct images along a morphism of algebraic spaces

Let `h : Y ⟶ X` be a morphism of algebraic spaces and `L₁, …, L_r` invertible `𝒪_X`-modules.
For an `𝒪_Y`-module `𝒩` and an integral tuple `n`,

`h_*(𝒩 ⊗ h^*L₁^{⊗ n₁} ⊗ ⋯ ⊗ h^*L_r^{⊗ n_r}) ≅ h_*𝒩 ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}`,

and the same holds for every higher direct image `R^q h_*`.  This is the projection formula of
Stacks 01E8 for the invertible modules `L_j^{⊗ n_j}`, which
`StacksFrontier/AlgebraicGeometry/Spaces/HigherDirectImageTensorInvertible.lean` proves for a single
invertible module, together with the comparison `h^*(L^{⊗ m}) ≅ (h^*L)^{⊗ m}` of the inverse
image of an integer tensor power with the integer power of the inverse image (Stacks 01CU),
which is the transport of tensor powers along a functor compatible with the tensor product,
`Stacks.SheafOfModules.TensorPower.mapTensorPowerIso`, applied to the inverse image and the
comparison of Stacks 03EL.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackInvertibleTensorPowerIso`:
  `h^*(L^{⊗ m}) ≅ (h^*L)^{⊗ m}` for every `m : ℤ`.
* `AlgebraicGeometry.Space.modulePushforwardTwistedModuleIso`: the twist of `h_*𝒩` by the `L_j`
  is the direct image of the twist of `𝒩` by the `h^*L_j`.
* `AlgebraicGeometry.Space.rightDerivedModulePushforwardTwistedModuleIso`: the same for every
  higher direct image.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **The inverse image of an integer tensor power of an invertible module is the integer power
of its inverse image** (Stacks 01CU): the inverse image is compatible with the tensor product by
Stacks 03EL and carries the structure sheaf to the structure sheaf, and a tensor power is the
image of the structure sheaf under an integer iterate of tensoring with `L`. -/
def modulePullbackInvertibleTensorPowerIso (h : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (m : ℤ) :
    haveI := stacksIsInvertible_modulePullback_obj B S hS h L
    (modulePullback B S hS h).obj (invertibleTensorPower B S hS X.1 X.2 L m) ≅
      invertibleTensorPower B S hS Y.1 Y.2 ((modulePullback B S hS h).obj L) m := by
  haveI := stacksIsInvertible_modulePullback_obj B S hS h L
  haveI : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  haveI : HasWeakSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
  haveI : (smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS Y.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  haveI : HasWeakSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u})
  letI hLX : AlgebraicGeometry.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL
  letI hLY : AlgebraicGeometry.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
      ((modulePullback B S hS h).obj L) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (stacksIsInvertible_modulePullback_obj B S hS h L)
  haveI := @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible.{u, u + 1, u}
    (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
    (structurePresheaf B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
    _ _ L hLX
  haveI := @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible.{u, u + 1, u}
    (smallEtaleRingedSite B S hS Y.1 Y.2).C _ (smallEtaleRingedSite B S hS Y.1 Y.2).J
    (structurePresheaf B S hS Y.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
    _ _ _ hLY
  exact (modulePullback B S hS h).mapIso (eqToIso
      (@Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower.{u, u + 1, u}
        (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
        (structurePresheaf B S hS X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        _ _ L hLX m)) ≪≫
    Stacks.SheafOfModules.TensorPower.mapTensorPowerIso.{u, u + 1, u, u + 1, u}
      (J := (smallEtaleRingedSite B S hS X.1 X.2).J) (K := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
      (modulePullback B S hS h) L
      (fun M => (Stacks.SheafOfModules.pullbackTensorIso
        (smallEtaleRingedToposModulesHom B S hS h)).app (M, L))
      (modulePullbackUnitIso B S hS h) m ≪≫
    eqToIso (@Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower.{u, u + 1, u}
        (smallEtaleRingedSite B S hS Y.1 Y.2).C _ (smallEtaleRingedSite B S hS Y.1 Y.2).J
        (structurePresheaf B S hS Y.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
        _ _ ((modulePullback B S hS h).obj L) hLY m).symm

/-- **An integer tensor power of an invertible module is invertible**, in the predicate
`Stacks.SheafOfModules.IsInvertible` that the twists and the projection formula read. -/
theorem stacksIsInvertible_invertibleTensorPower (Z : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS Z.1 Z.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property L]
    (m : ℤ) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property
      (invertibleTensorPower B S hS Z.1 Z.2 L m) :=
  let := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ L m)

/-- **The projection formula for one twisting step**, at an arbitrary integer exponent:
`h_*(𝒩 ⊗ (h^*L)^{⊗ m}) ≅ h_*𝒩 ⊗ L^{⊗ m}`.  The power of the inverse image is the inverse image
of the power (`AlgebraicGeometry.Space.modulePullbackInvertibleTensorPowerIso`), and the
projection formula for the invertible module `L^{⊗ m}` is
`AlgebraicGeometry.Space.pushforwardTensorRightIso`. -/
def modulePushforwardTwistStepIso (h : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (m : ℤ) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    haveI := stacksIsInvertible_modulePullback_obj B S hS h L
    (modulePushforward B S hS h).obj
        (twistStep B S hS Y.1 Y.2 ((modulePullback B S hS h).obj L) m N) ≅
      twistStep B S hS X.1 X.2 L m ((modulePushforward B S hS h).obj N) :=
  haveI := stacksIsInvertible_modulePullback_obj B S hS h L
  haveI := stacksIsInvertible_invertibleTensorPower B S hS X L m
  (modulePushforward B S hS h).mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
        N).mapIso (modulePullbackInvertibleTensorPowerIso B S hS h L m).symm) ≪≫
    (pushforwardTensorRightIso B S hS h (invertibleTensorPower B S hS X.1 X.2 L m)).app N

/-- **The projection formula for one twisting step, in every degree**:
`R^q h_*(𝒩 ⊗ (h^*L)^{⊗ m}) ≅ R^q h_*𝒩 ⊗ L^{⊗ m}`. -/
def rightDerivedModulePushforwardTwistStepIso (h : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (m : ℤ) (q : ℕ) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    haveI := stacksIsInvertible_modulePullback_obj B S hS h L
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS h).rightDerived q).obj
        (twistStep B S hS Y.1 Y.2 ((modulePullback B S hS h).obj L) m N) ≅
      twistStep B S hS X.1 X.2 L m (((modulePushforward B S hS h).rightDerived q).obj N) :=
  haveI := stacksIsInvertible_modulePullback_obj B S hS h L
  haveI := stacksIsInvertible_invertibleTensorPower B S hS X L m
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  ((modulePushforward B S hS h).rightDerived q).mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
        N).mapIso (modulePullbackInvertibleTensorPowerIso B S hS h L m).symm) ≪≫
    rightDerivedModulePushforwardSheafTensorIso B S hS h (invertibleTensorPower B S hS X.1 X.2 L m)
      N q

/-- **Twists commute with direct images**: the direct image of the twist of `𝒩` by the inverse
images `h^*L_j` is the twist of `h_*𝒩` by the `L_j`. -/
def modulePushforwardTwistedModuleIso {r : ℕ} (h : Y ⟶ X)
    (L : Fin r → Modules.{u, u} B S hS X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        (L j)]
    (n : Fin r → ℤ) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    haveI := fun j => stacksIsInvertible_modulePullback_obj B S hS h (L j)
    (modulePushforward B S hS h).obj
        (twistedModule B S hS Y.1 Y.2 N (fun j => (modulePullback B S hS h).obj (L j)) n) ≅
      twistedModule B S hS X.1 X.2 ((modulePushforward B S hS h).obj N) L n :=
  haveI := fun j => stacksIsInvertible_modulePullback_obj B S hS h (L j)
  twistedModuleMapIso B S hS (modulePushforward B S hS h) _ L n
    (fun j N => modulePushforwardTwistStepIso B S hS h (L j) (n j) N) N

/-- **Twists commute with higher direct images**: `R^q h_*` of the twist of `𝒩` by the inverse
images `h^*L_j` is the twist of `R^q h_*𝒩` by the `L_j`. -/
def rightDerivedModulePushforwardTwistedModuleIso {r : ℕ} (h : Y ⟶ X)
    (L : Fin r → Modules.{u, u} B S hS X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        (L j)]
    (n : Fin r → ℤ) (q : ℕ) (N : Modules.{u, u} B S hS Y.1 Y.2) :
    haveI := fun j => stacksIsInvertible_modulePullback_obj B S hS h (L j)
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS h).rightDerived q).obj
        (twistedModule B S hS Y.1 Y.2 N (fun j => (modulePullback B S hS h).obj (L j)) n) ≅
      twistedModule B S hS X.1 X.2 (((modulePushforward B S hS h).rightDerived q).obj N) L n :=
  haveI := fun j => stacksIsInvertible_modulePullback_obj B S hS h (L j)
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  twistedModuleMapIso B S hS ((modulePushforward B S hS h).rightDerived q) _ L n
    (fun j N => rightDerivedModulePushforwardTwistStepIso B S hS h (L j) (n j) q N) N

end AlgebraicGeometry.Space

end
