module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPresentation
public import StacksCore.Tactic.StacksAttribute

/-! # Precomposition on the internal hom of a differential graded bimodule

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let
`f : M → N` be a homomorphism of differential graded `(A, B)`-bimodules. For every right
differential graded `B`-module `P`, precomposition with `f` carries a homogeneous right
`B`-linear map `N → P` to one `M → P` of the same degree, and does so compatibly with the
differential of the Hom complex and with the right `A`-action. It is therefore a homomorphism
`Hom^•_B(N, P) ⟶ Hom^•_B(M, P)` of right differential graded `A`-modules.

This is the underived half of Tag 0BYV.

## Main definitions

* `DifferentialGradedModule.homogeneousMapPrecompₗ`: precomposition with a closed degree-zero
  homogeneous map, as an `R`-linear map on homogeneous maps of a fixed degree.
* `DifferentialGraded.Bimodule.precompHom`: precomposition with a bimodule homomorphism, as a
  homomorphism of the internal homs.

## Main results

* `DifferentialGraded.Bimodule.precompHom_homogeneousEquiv`: the characterizing property — the
  homogeneous map attached to the image is the composite of the one attached to the argument
  with `f`.
* `DifferentialGraded.Bimodule.precompHom_unique`: that property determines the homomorphism.

## Implementation notes

The construction follows `DifferentialGradedModule.HomModuleData.compareHom`: the underlying
linear map is assembled from its graded pieces with `DirectSum.toModule`, and every obligation
is reduced to the degreewise formula by `DirectSum.Decomposition.inductionOn`. As there,
compatibility with the right `A`-action needs `DifferentialGradedModule.homogeneousMap_ext`,
because a presentation records the action only through the values of the associated homogeneous
maps on homogeneous elements.

The internal hom is characterized rather than named, so the two presentations
`HM` and `HN` of `Hom^•_B(M, P)` and `Hom^•_B(N, P)` are arguments; the resulting homomorphism
is natural in both, by `DifferentialGradedModule.HomModuleData.compareHom_unique`.

## References

* [Stacks Project, Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV); the internal hom is
  [Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR) and bimodules are
  [Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- Precomposition with a closed degree-zero homogeneous map `φ : X → Y`, as an `R`-linear map
from the degree-`n` homogeneous right `B`-linear maps `Y → P` to those `X → P`. -/
def homogeneousMapPrecompₗ {X Y P : DifferentialGradedModule B}
    (φ : HomogeneousMap B X Y 0) (n : ℤ) :
    HomogeneousMap B Y P n →ₗ[R] HomogeneousMap B X P n where
  toFun g := homogeneousMapComp B (add_zero n) g φ
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

/-- The underlying linear map of the precomposite `g ∘ φ` is the composite of the underlying
linear maps. -/
@[simp] theorem homogeneousMapPrecompₗ_val {X Y P : DifferentialGradedModule B}
    (φ : HomogeneousMap B X Y 0) (n : ℤ) (g : HomogeneousMap B Y P n) :
    (homogeneousMapPrecompₗ (P := P) φ n g).1 = g.1 ∘ₗ φ.1 := rfl

/-- Precomposition with a homomorphism of differential graded modules commutes with the
differential of the Hom complex: the homomorphism is closed of degree zero, so no sign
intervenes. -/
theorem homogeneousMapPrecompₗ_differential {X Y P : DifferentialGradedModule B}
    (φ : X ⟶ Y) (n : ℤ) (g : HomogeneousMap B Y P n) :
    homogeneousMapDifferential B (homogeneousMapPrecompₗ (P := P) (cocycleOfHom B φ).1 n g) =
      homogeneousMapPrecompₗ (P := P) (cocycleOfHom B φ).1 (n + 1)
        (homogeneousMapDifferential B g) := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  simp only [homogeneousMapDifferential_val, homogeneousMapPrecompₗ_val,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  rw [show (cocycleOfHom B φ).1.1 (X.d x) = Y.d ((cocycleOfHom B φ).1.1 x) from
    LinearMap.congr_fun φ.map_d x]

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}
  {M N : Bimodule A B} (f : M ⟶ N) {P : DifferentialGradedModule B}
  (HN : HomModuleData A B N.rightModule P N.leftAction)
  (HM : HomModuleData A B M.rightModule P M.leftAction)

/-- The graded piece of precomposition: read a degree-`n` element of a presentation of
`Hom^•_B(N, P)` as a homogeneous map, compose it with `f`, and read the result back through a
presentation of `Hom^•_B(M, P)`. -/
def precompGraded (n : ℤ) : HN.module.grading n →ₗ[R] HM.module.grading n :=
  (HM.homogeneousEquiv n).symm.toLinearMap ∘ₗ
    homogeneousMapPrecompₗ (P := P) (cocycleOfHom B f.rightHom).1 n ∘ₗ
      (HN.homogeneousEquiv n).toLinearMap

/-- The homogeneous map attached to the image of `g` under `precompGraded` is the composite with
`f` of the homogeneous map attached to `g`. -/
@[simp] theorem homogeneousEquiv_precompGraded (n : ℤ) (g : HN.module.grading n) :
    HM.homogeneousEquiv n (precompGraded f HN HM n g) =
      homogeneousMapComp B (add_zero n) (HN.homogeneousEquiv n g)
        (cocycleOfHom B f.rightHom).1 :=
  (HM.homogeneousEquiv n).apply_symm_apply _

/-- The value of the homogeneous map attached to the image of `g` under precomposition. -/
theorem precompGraded_apply (n : ℤ) (g : HN.module.grading n) (z : M.rightModule.M) :
    (HM.homogeneousEquiv n (precompGraded f HN HM n g)).1 z =
      (HN.homogeneousEquiv n g).1 (f.rightHom.toFun z) := by
  rw [homogeneousEquiv_precompGraded]
  rfl

/-- The underlying linear map of precomposition, assembled from its graded pieces. -/
def precompLinearMap : HN.module.M →ₗ[R] HM.module.M :=
  (DirectSum.toModule R ℤ HM.module.M
      (fun n => (HM.module.grading n).subtype ∘ₗ precompGraded f HN HM n)).comp
    (DirectSum.decomposeLinearEquiv HN.module.grading).toLinearMap

/-- On a homogeneous element of degree `n`, `precompLinearMap` is the graded piece
`precompGraded` in degree `n`. -/
theorem precompLinearMap_apply_grading (n : ℤ) (g : HN.module.grading n) :
    precompLinearMap f HN HM (g : HN.module.M) =
      (precompGraded f HN HM n g : HM.module.M) := by
  have hdec : DirectSum.decomposeLinearEquiv HN.module.grading (g : HN.module.M) =
      DirectSum.lof R ℤ (fun i => HN.module.grading i) n g := by simp
  simp only [precompLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hdec,
    DirectSum.toModule_lof, Submodule.coe_subtype]

/-- `precompLinearMap` sends `x` to `y` as soon as the homogeneous map attached to `y` is the
composite with `f` of the one attached to `x`. -/
private theorem precompLinearMap_eq_of_homogeneousEquiv {n : ℤ} (x : HN.module.grading n)
    (y : HM.module.grading n)
    (h : HM.homogeneousEquiv n y = homogeneousMapComp B (add_zero n) (HN.homogeneousEquiv n x)
      (cocycleOfHom B f.rightHom).1) :
    precompLinearMap f HN HM (x : HN.module.M) = (y : HM.module.M) := by
  rw [precompLinearMap_apply_grading]
  exact congrArg Subtype.val
    ((HM.homogeneousEquiv n).injective (by rw [homogeneousEquiv_precompGraded, h]))

/-- `precompLinearMap` preserves the grading. -/
theorem precompLinearMap_mem_grading (n : ℤ) (x : HN.module.M) (hx : x ∈ HN.module.grading n) :
    precompLinearMap f HN HM x ∈ HM.module.grading n := by
  rw [show x = ((⟨x, hx⟩ : HN.module.grading n) : HN.module.M) from rfl,
    precompLinearMap_apply_grading]
  exact (precompGraded f HN HM n ⟨x, hx⟩).property

/-- `precompLinearMap` commutes with the differentials of the two presentations. -/
theorem precompLinearMap_d (x : HN.module.M) :
    precompLinearMap f HN HM (HN.module.d x) =
      HM.module.d (precompLinearMap f HN HM x) := by
  induction x using DirectSum.Decomposition.inductionOn HN.module.grading with
  | zero => simp
  | @homogeneous n g =>
    rw [precompLinearMap_apply_grading]
    exact precompLinearMap_eq_of_homogeneousEquiv f HN HM (HN.module.gradedDifferential n g)
      (HM.module.gradedDifferential n (precompGraded f HN HM n g)) (by
        rw [HM.map_d, HN.map_d, homogeneousEquiv_precompGraded]
        exact homogeneousMapPrecompₗ_differential f.rightHom n (HN.homogeneousEquiv n g))
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `precompLinearMap` commutes with the right action of `A`. -/
theorem precompLinearMap_op_smul (x : HN.module.M) (a : A.A) :
    precompLinearMap f HN HM (MulOpposite.op a • x) =
      MulOpposite.op a • precompLinearMap f HN HM x := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | @homogeneous m a =>
    induction x using DirectSum.Decomposition.inductionOn HN.module.grading with
    | zero => simp
    | @homogeneous n g =>
      have hmemN : MulOpposite.op (a : A.A) • (g : HN.module.M) ∈ HN.module.grading (n + m) :=
        HN.module.smul_mem n m (g : HN.module.M) (a : A.A) g.property a.property
      have hmemM : MulOpposite.op (a : A.A) • (precompGraded f HN HM n g : HM.module.M) ∈
          HM.module.grading (n + m) :=
        HM.module.smul_mem n m _ (a : A.A) (precompGraded f HN HM n g).property a.property
      rw [precompLinearMap_apply_grading]
      exact precompLinearMap_eq_of_homogeneousEquiv f HN HM ⟨_, hmemN⟩ ⟨_, hmemM⟩ (by
        apply homogeneousMap_ext
        intro p x
        rw [HM.map_smul n m p (precompGraded f HN HM n g) a x, precompGraded_apply,
          f.map_left m p a x]
        exact (HN.map_smul n m p g a (f.rightHom.gradedMap p x)).symm)
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  | add a b ha hb =>
    rw [MulOpposite.op_add, add_smul, map_add, ha, hb, add_smul]

/-- Precomposition with a homomorphism `f : M ⟶ N` of differential graded `(A, B)`-bimodules, as
a homomorphism `Hom^•_B(N, P) ⟶ Hom^•_B(M, P)` of right differential graded `A`-modules. -/
def precompHom : HN.module ⟶ HM.module where
  toFun := precompLinearMap f HN HM
  map_smul x a := precompLinearMap_op_smul f HN HM x a
  map_grading n x hx := precompLinearMap_mem_grading f HN HM n x hx
  map_d := LinearMap.ext (precompLinearMap_d f HN HM)

/-- On a homogeneous element of degree `n`, `precompHom` is the graded piece `precompGraded` in
degree `n`. -/
@[simp] theorem precompHom_apply_grading (n : ℤ) (g : HN.module.grading n) :
    (precompHom f HN HM).toFun (g : HN.module.M) =
      (precompGraded f HN HM n g : HM.module.M) :=
  precompLinearMap_apply_grading f HN HM n g

/-- The characterizing property of precomposition: the homogeneous map attached to the image is
the composite with `f` of the homogeneous map attached to the argument. -/
theorem precompHom_homogeneousEquiv (n : ℤ) (g : HN.module.grading n) :
    HM.homogeneousEquiv n ⟨(precompHom f HN HM).toFun (g : HN.module.M),
        (precompHom f HN HM).map_grading n _ g.property⟩ =
      homogeneousMapComp B (add_zero n) (HN.homogeneousEquiv n g)
        (cocycleOfHom B f.rightHom).1 := by
  rw [show (⟨(precompHom f HN HM).toFun (g : HN.module.M),
      (precompHom f HN HM).map_grading n _ g.property⟩ : HM.module.grading n) =
      precompGraded f HN HM n g from Subtype.ext (precompHom_apply_grading f HN HM n g)]
  exact homogeneousEquiv_precompGraded f HN HM n g

/-- Precomposition is determined by its characterizing property. -/
theorem precompHom_unique (φ : HN.module ⟶ HM.module)
    (hφ : ∀ (n : ℤ) (g : HN.module.grading n),
      HM.homogeneousEquiv n ⟨φ.toFun (g : HN.module.M), φ.map_grading n _ g.property⟩ =
        homogeneousMapComp B (add_zero n) (HN.homogeneousEquiv n g)
          (cocycleOfHom B f.rightHom).1) :
    φ = precompHom f HN HM := by
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
  induction x using DirectSum.Decomposition.inductionOn HN.module.grading with
  | zero => simp
  | @homogeneous n g =>
    exact (precompLinearMap_eq_of_homogeneousEquiv f HN HM g
      ⟨φ.toFun (g : HN.module.M), φ.map_grading n _ g.property⟩ (hφ n g)).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end DifferentialGraded.Bimodule

end
