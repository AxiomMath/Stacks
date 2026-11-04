module

public import Mathlib.Geometry.RingedSpace.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Homology.DualAssemblyOfComplexes

/-!
# The dual of a complex of modules whose terms are locally finite free summands

Let `(C, 𝒪)` be a ringed site and let `ℱ^•` be a complex of `𝒪`-modules each of whose terms is,
locally on the site, a direct summand of a finite free `𝒪`-module. Write
`𝒢^m = SheafHom(ℱ^{-m}, 𝒪)` for the termwise dual. If `ℱ^•` vanishes outside a finite set of
degrees, then `η = ∑ ηₙ` and `ε = ∑ εₙ`, built out of the degreewise pairings
`Stacks.SheafOfModules.exactPairingDualSheafOfLocalSummand`, exhibit the graded object `𝒢^•` as a
left dual of `ℱ^•`.

## Main definitions

* `Stacks.SheafOfModules.Strict.gradedMonoidalCategoryRingSheaf`: the monoidal structure on
  graded `𝒪`-modules built on `Stacks.SheafOfModules.Strict.monoidalCategory`.
* `Stacks.SheafOfModules.Strict.dualGradedObject`: the graded object of termwise duals,
  `𝒢^m = SheafHom(ℱ^{-m}, 𝒪)`.

## Main results

* `Stacks.SheafOfModules.Strict.exactPairingDualGradedObject`: for a bounded complex, `𝒢^•` is a
  left dual of `ℱ^•` as a graded `𝒪`-module.
* `Stacks.SheafOfModules.OnSpace.exactPairingDualGradedObject`: the same on a ringed space.
* `Stacks.SheafOfModules.Strict.dualGradedObject_neg`: the degree `-n` of the termwise dual is
  the dual sheaf of the term `ℱ^n`.

## References

* [Stacks Project, Tag 0FP9](https://stacks.math.columbia.edu/tag/0FP9)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.GradedObject CategoryTheory.GradedObject.Monoidal

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

/-- The monoidal structure on graded `𝒪`-modules built on
`Stacks.SheafOfModules.Strict.monoidalCategory`. -/
@[instance_reducible]
def gradedMonoidalCategoryRingSheaf : MonoidalCategory (GradedObject ℤ (Mod R)) :=
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  inferInstance

variable (K : CochainComplex (Mod R) ℤ)

/-- The graded object of termwise duals of a complex of `𝒪`-modules: in degree `m` it is
`SheafHom(ℱ^{-m}, 𝒪)`. -/
def dualGradedObject : GradedObject ℤ (Mod R) :=
  fun m => dualSheaf R.obj (isSheaf_ringSheaf R) (K.X (-m))

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- In degree `-n` the termwise dual is the dual sheaf of the term `ℱ^n`. -/
theorem dualGradedObject_neg (n : ℤ) :
    dualGradedObject R K (-n) = dualSheaf R.obj (isSheaf_ringSheaf R) (K.X n) := by
  rw [dualGradedObject, neg_neg]

/-- Let `ℱ^•` be a complex of `𝒪`-modules vanishing outside a finite set of degrees, each of
whose terms is locally a direct summand of a finite free `𝒪`-module. Then the termwise dual
`𝒢^m = SheafHom(ℱ^{-m}, 𝒪)` is a left dual of `ℱ^•` as a graded `𝒪`-module, with coevaluation
`η = ∑ ηₙ` and evaluation `ε = ∑ εₙ` assembled from the degreewise pairings. -/
@[instance_reducible]
def exactPairingDualGradedObject (s : Finset ℤ)
    (hbd : ∀ m : ℤ, m ∉ s → IsZero (K.X m))
    (hK : ∀ n : ℤ, IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n)) :
    @ExactPairing _ _ (gradedMonoidalCategoryRingSheaf R)
      (K.X : GradedObject ℤ (Mod R)) (dualGradedObject R K) := by
  letI : MonoidalCategory (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory R.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf R).property
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  exact exactPairingOfDegreewiseOfIsZero (K.X : GradedObject ℤ (Mod R)) (dualGradedObject R K) s
    (fun n => by
      rw [dualGradedObject_neg R K n]
      exact exactPairingDualSheafOfLocalSummand R.obj (isSheaf_ringSheaf R) (K.X n) (hK n))
    hbd

end Stacks.SheafOfModules.Strict

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- On a ringed space, let `ℱ^•` be a complex of `𝒪_X`-modules vanishing outside a finite set of
degrees, each of whose terms is locally a direct summand of a finite free `𝒪_X`-module. Then the
termwise dual is a left dual of `ℱ^•` as a graded `𝒪_X`-module. -/
@[instance_reducible]
def exactPairingDualGradedObject
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (s : Finset ℤ)
    (hbd : ∀ m : ℤ, m ∉ s → IsZero (F.X m))
    (hF : ∀ n : ℤ, Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.sheaf.obj
      (Strict.isSheaf_ringSheaf X.sheaf) (F.X n)) :
    @ExactPairing _ _ (Strict.gradedMonoidalCategoryRingSheaf X.sheaf)
      (F.X : GradedObject ℤ (Strict.Mod X.sheaf)) (Strict.dualGradedObject X.sheaf F) :=
  Strict.exactPairingDualGradedObject X.sheaf F s hbd hF

end Stacks.SheafOfModules.OnSpace

end

end
