module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSourceMonoidal

/-!
# Homomorphisms between inverse images of sheaves of graded algebras on algebraic spaces

For morphisms `r : G ⟶ X` and `ι : G ⟶ Y` of algebraic spaces and sheaves of `ℤ`-graded algebras
`𝒜` on `X` and `𝒜'` on `Y`, a family of morphisms of `𝒪_G`-modules `θ_n : r^*𝒜_n ⟶ ι^*𝒜'_n`
which carries the inverse image along `r` of the multiplication of `𝒜`, read through Stacks 03EL,
to the inverse image along `ι` of the multiplication of `𝒜'`, is a homomorphism of sheaves of
graded algebras `r^*𝒜 ⟶ ι^*𝒜'` between the inverse images of Stacks 0FQX.

## Main definitions

* `AlgebraicGeometry.Space.PullMulCompat`: morphisms `θ_n : r^*M_n ⟶ ι^*N_n` carry the
  pulled-back multiplications to one another.
* `AlgebraicGeometry.Space.gradedPullHomOfMul`: the homomorphism of sheaves of graded algebras
  `r^*𝒜 ⟶ ι^*𝒜'` with components `θ_n`.
* `AlgebraicGeometry.Space.gradedPullHomApp`: the components of a homomorphism `r^*𝒜 ⟶ ι^*𝒜'`,
  as morphisms `r^*𝒜_n ⟶ ι^*𝒜'_n`.

## Main results

* `AlgebraicGeometry.Space.mulSheaf_gradedPull_comp_of_mul`: the same compatibility, read on the
  multiplications of the inverse images as morphisms out of the tensor product sheaves.
* `AlgebraicGeometry.Space.eq_gradedPullHomOfMul`: it is the only homomorphism with these
  components.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

open scoped TensorProduct

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G X Y : AlgebraicSpaces B S hS} (r : G ⟶ X) (ι : G ⟶ Y)

/-- **Morphisms `θ_n : r^*M_n ⟶ ι^*N_n` carry the inverse image along `r` of a multiplication
`μ` of the `M_n` to the inverse image along `ι` of a multiplication `μ'` of the `N_n`**, both
read through Stacks 03EL: `r^*(M_i) ⊗ r^*(M_j) ≅ r^*(M_i ⊗ M_j) ⟶ r^*M_{i+j} ⟶ ι^*N_{i+j}` is
`θ_i ⊗ θ_j` followed by `ι^*(N_i) ⊗ ι^*(N_j) ≅ ι^*(N_i ⊗ N_j) ⟶ ι^*N_{i+j}`. -/
def PullMulCompat (M : ℤ → Modules.{u, u} B S hS X.1 X.2) (N : ℤ → Modules.{u, u} B S hS Y.1 Y.2)
    (θ : ∀ n : ℤ, (modulePullback B S hS r).obj (M n) ⟶ (modulePullback B S hS ι).obj (N n))
    (μ : ∀ i j : ℤ, MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS X.1 X.2)
      (M i) (M j) ⟶ M (i + j))
    (μ' : ∀ i j : ℤ, MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS Y.1 Y.2)
      (N i) (N j) ⟶ N (i + j)) : Prop :=
  ∀ i j : ℤ, (modulePullbackTensorIso B S hS r (M i) (M j)).inv ≫
      (modulePullback B S hS r).map (μ i j) ≫ θ (i + j) =
    (θ i ⊗ₘ θ j) ≫ (modulePullbackTensorIso B S hS ι (N i) (N j)).inv ≫
      (modulePullback B S hS ι).map (μ' i j)

variable (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y))
  (θ : ∀ n : ℤ, (modulePullback B S hS r).obj (A.piece n) ⟶
    (modulePullback B S hS ι).obj (A'.piece n))

variable (μ : ∀ i j : ℤ, MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS X.1 X.2)
    (A.piece i) (A.piece j) ⟶ A.piece (i + j))
  (μ' : ∀ i j : ℤ, MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS Y.1 Y.2)
    (A'.piece i) (A'.piece j) ⟶ A'.piece (i + j))
  (hμ : ∀ i j : ℤ, (modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
    SheafOfModules.GradedAlgebra.mulSheaf A i j = μ i j)
  (hμ' : ∀ i j : ℤ, (modulesTensorObjIso B S hS Y.1 Y.2 (A'.piece i) (A'.piece j)).hom ≫
    SheafOfModules.GradedAlgebra.mulSheaf A' i j = μ' i j)

include hμ hμ' in
/-- **A family `θ_n : r^*𝒜_n ⟶ ι^*𝒜'_n` carrying the pulled-back multiplications to one another
commutes with the multiplications of the inverse images**, as morphisms out of the tensor product
sheaves; `μ`, `μ'` are the multiplications of `𝒜`, `𝒜'` out of the tensor products of
`𝒪`-modules. -/
theorem mulSheaf_gradedPull_comp_of_mul (i j : ℤ)
    (h : (modulePullbackTensorIso B S hS r (A.piece i) (A.piece j)).inv ≫
        (modulePullback B S hS r).map (μ i j) ≫ θ (i + j) =
      (θ i ⊗ₘ θ j) ≫ (modulePullbackTensorIso B S hS ι (A'.piece i) (A'.piece j)).inv ≫
        (modulePullback B S hS ι).map (μ' i j)) :
    SheafOfModules.GradedAlgebra.mulSheaf
        ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS r)).obj A) i j ≫ θ (i + j) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS G.1 G.2)).map (θ i)).app _ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS G.1 G.2)).obj _).map (θ j)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS ι)).obj A') i j := by
  have h1 := modulePullbackTensorIso_inv_comp_map_mulSheaf B S hS A r i j
  have h2 := modulePullbackTensorIso_inv_comp_map_mulSheaf B S hS A' ι i j
  rw [hμ i j] at h1
  rw [hμ' i j] at h2
  have hn := modulesTensorObjIso_hom_naturality B S hS (θ i) (θ j)
  refine (Iso.cancel_iso_hom_left (modulesTensorObjIso B S hS G.1 G.2
    ((modulePullback B S hS r).obj (A.piece i)) ((modulePullback B S hS r).obj (A.piece j)))
    _ _).1 ?_
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ θ (i + j)) h1.symm).trans <|
    (Category.assoc _ _ _).trans <| h.trans <| (congrArg ((θ i ⊗ₘ θ j) ≫ ·) h2).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ SheafOfModules.GradedAlgebra.mulSheaf
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS ι)).obj A') i j) hn).trans
    (Category.assoc _ _ _)

include hμ hμ' in
/-- **A family `θ_n : r^*𝒜_n ⟶ ι^*𝒜'_n` carrying the inverse image along `r` of the
multiplication of `𝒜` to the inverse image along `ι` of the multiplication of `𝒜'`, both read
through Stacks 03EL, is a homomorphism of sheaves of graded algebras `r^*𝒜 ⟶ ι^*𝒜'`** between
the inverse images of Stacks 0FQX; `μ`, `μ'` are the multiplications of `𝒜`, `𝒜'` out of the
tensor products of `𝒪`-modules. -/
def gradedPullHomOfMul
    (h : PullMulCompat r ι A.piece A'.piece θ μ μ') :
    SheafOfModules.GradedAlgebra.Hom
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS r)).obj A)
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS ι)).obj A') where
  app := θ
  map_mul i j U x y := by
    have e := congrArg (fun φ => PresheafOfModules.Hom.app (SheafOfModules.Hom.val φ) U
        ((PresheafOfModules.tensorSheafUnit
          (((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS r)).obj A).piece i)
          (((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS X)
            (smallEtaleRingedToposHom B S hS r)).obj A).piece j)).app U (x ⊗ₜ y)))
      (mulSheaf_gradedPull_comp_of_mul r ι A A' θ μ μ' hμ hμ' i j (h i j))
    refine (congrArg (PresheafOfModules.Hom.app (SheafOfModules.Hom.val (θ (i + j))) U)
      (SheafOfModules.GradedAlgebra.mulSheaf_unit
        ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS r)).obj A) i j U x y).symm).trans (e.trans ?_)
    refine (congrArg (PresheafOfModules.Hom.app (SheafOfModules.Hom.val
        (SheafOfModules.GradedAlgebra.mulSheaf
          ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS ι)).obj A') i j)) U)
      (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
        (structureSheaf B S hS G.1 G.2) _ _ (θ i) (θ j) U x y)).trans ?_
    exact SheafOfModules.GradedAlgebra.mulSheaf_unit
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS ι)).obj A') i j U _ _

/-- The components of `AlgebraicGeometry.Space.gradedPullHomOfMul` are the given morphisms. -/
theorem gradedPullHomOfMul_app
    (h : PullMulCompat r ι A.piece A'.piece θ μ μ') (n : ℤ) :
    (gradedPullHomOfMul r ι A A' θ μ μ' hμ hμ' h).app n = θ n :=
  rfl

/-- The degree-`n` component `r^*𝒜_n ⟶ ι^*𝒜'_n` of a homomorphism of sheaves of graded algebras
`r^*𝒜 ⟶ ι^*𝒜'` between inverse images, as a morphism between the inverse images of the
homogeneous pieces. -/
def gradedPullHomApp
    (φ : SheafOfModules.GradedAlgebra.Hom
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS r)).obj A)
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS ι)).obj A')) (n : ℤ) :
    (modulePullback B S hS r).obj (A.piece n) ⟶ (modulePullback B S hS ι).obj (A'.piece n) :=
  φ.app n

/-- The components of `AlgebraicGeometry.Space.gradedPullHomOfMul`, read between the inverse
images of the homogeneous pieces, are the given morphisms. -/
theorem gradedPullHomApp_gradedPullHomOfMul (h : PullMulCompat r ι A.piece A'.piece θ μ μ')
    (n : ℤ) :
    gradedPullHomApp r ι A A' (gradedPullHomOfMul r ι A A' θ μ μ' hμ hμ' h) n = θ n :=
  rfl

/-- A homomorphism `r^*𝒜 ⟶ ι^*𝒜'` with the components `θ_n` is
`AlgebraicGeometry.Space.gradedPullHomOfMul`. -/
theorem eq_gradedPullHomOfMul
    (h : PullMulCompat r ι A.piece A'.piece θ μ μ')
    (θ' : SheafOfModules.GradedAlgebra.Hom
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS r)).obj A)
      ((gradedPull (X := smallEtaleRingedTopos B S hS G) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS ι)).obj A'))
    (hθ' : ∀ n : ℤ, gradedPullHomApp r ι A A' θ' n = θ n) :
    θ' = gradedPullHomOfMul r ι A A' θ μ μ' hμ hμ' h :=
  SheafOfModules.GradedAlgebra.Hom.ext hθ'

end AlgebraicGeometry.Space

end
