module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedOppositeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorBifunctor

/-!
# The relative tensor product of differential graded modules in its second variable

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of differential graded
`O`-algebras and let `P` be a right differential graded `A`-module. A homomorphism `f : N ⟶ N'`
of left differential graded `A`-modules induces a map of complexes `P ⊗_A N ⟶ P ⊗_A N'`,
`x ⊗ y ↦ x ⊗ f y`, natural in `P`. When `N` and `N'` are differential graded `(A, B)`-bimodules
and `f` is a homomorphism of bimodules, the map commutes with the right action of `B`, so the
tensor products with `N` and `N'` are related by a natural transformation
`- ⊗_A N ⟶ - ⊗_A N'` of functors to right differential graded `B`-modules. This is the
functoriality of the tensor construction in the bimodule used in
[Stacks, Tag 0FTJ](https://stacks.math.columbia.edu/tag/0FTJ).

## Main definitions

* `SheafOfModules.RelativeTensor.dgTensorMapLeft`: the map of complexes `P ⊗_A N ⟶ P ⊗_A N'`
  induced by a homomorphism of left differential graded modules.
* `SheafOfModules.RelativeTensor.dgTensorRightMapLeft`: the homomorphism `M ⊗_A N ⟶ M ⊗_A N'`
  of right differential graded `B`-modules induced by a homomorphism of bimodules.
* `SheafOfModules.RelativeTensor.dgTensorRightFunctorMap`: the natural transformation
  `- ⊗_A N ⟶ - ⊗_A N'`.
* `SheafOfModules.LeftDifferentialGradedModule.Hom.opRight` and
  `SheafOfModules.DifferentialGradedModule.Hom.unopLeftMap`: a homomorphism of left
  differential graded `A`-modules read as one of right `A.op`-modules, and conversely.

## Main results

* `SheafOfModules.RelativeTensor.dgTensorFunctor_map_comp_dgTensorMapLeft`: the map is natural
  in the first variable.
* `SheafOfModules.RelativeTensor.opSwap_naturality`: the interchange
  `P ⊗_{A^{opp}} M = M ⊗_A P` of the two factors is natural in `P`, which carries the map in
  the second variable to a map in the first one.

## Implementation notes

Each compatibility is checked on local sections `x ⊗ y`, which determine a morphism out of a
relative tensor product (`SheafOfModules.RelativeTensor.gradedTensor_hom_ext`); the compatibility
with the right action of `B`, a bilinear map, is reduced to the presheaf level along the locally
surjective sheafification unit, as for the functoriality in the first variable.

## References

* [Stacks Project, Tag 0FTJ](https://stacks.math.columbia.edu/tag/0FTJ)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t m v u

attribute [local implicit_reducible] SheafOfModules.DifferentialGradedAlgebra.op
  SheafOfModules.GradedModule.ofDifferentialGraded
  SheafOfModules.LeftGradedModule.ofDifferentialGraded
  SheafOfModules.DifferentialGradedModule.opLeft
  SheafOfModules.DifferentialGradedModule.unopLeft
  SheafOfModules.LeftDifferentialGradedModule.opRight

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

section MapLeft

variable (P : DifferentialGradedModule.{t, m, m} A)
  {N N' : LeftDifferentialGradedModule.{t, m, m} A}

/-- The homomorphism of underlying left graded modules of a homomorphism of left differential
graded modules. -/
noncomputable abbrev gMapLeft (f : N ⟶ N') : gN N ⟶ gN N' :=
  LeftGradedModule.ofDifferentialGradedMap f

/-- The map `P ⊗_A N ⟶ P ⊗_A N'` induced by a homomorphism of left differential graded modules
commutes with the differentials. -/
theorem gradedTensorMap_comm_d (f : N ⟶ N') (n : ℤ) :
    gradedTensorMap (gP P) (gMapLeft f) n ≫ dgTensorD P N' n =
      dgTensorD P N n ≫ gradedTensorMap (gP P) (gMapLeft f) (n + 1) := by
  refine gradedTensor_hom_ext (gP P) (gN N) fun q X u w ↦ ?_
  have hd : PresheafOfModules.Hom.app ((gMapLeft f).app (q.1.2 + 1)).val X
        ((N.complex.d q.1.2 (q.1.2 + 1)).val.app X w) =
      (N'.complex.d q.1.2 (q.1.2 + 1)).val.app X
        (PresheafOfModules.Hom.app ((gMapLeft f).app q.1.2).val X w) :=
    (congrArg (fun φ : N.complex.X q.1.2 ⟶ N'.complex.X (q.1.2 + 1) ↦
      (SheafOfModules.Hom.val φ).app X w)
        (f.toHomologicalComplex.comm q.1.2 (q.1.2 + 1))).symm
  change PresheafOfModules.Hom.app (dgTensorD P N' n).val X
      (PresheafOfModules.Hom.app (gradedTensorMap (gP P) (gMapLeft f) n).val X
        (tmul (gP P) (gN N) n q X u w)) =
    PresheafOfModules.Hom.app (gradedTensorMap (gP P) (gMapLeft f) (n + 1)).val X
      (PresheafOfModules.Hom.app (dgTensorD P N n).val X (tmul (gP P) (gN N) n q X u w))
  rw [gradedTensorMap_tmul, dgTensorD_tmul, dgTensorD_tmul, hom_val_app_add, hom_val_app_zsmul,
    gradedTensorMap_tmul, gradedTensorMap_tmul, hd]

/-- **The map `P ⊗_A N ⟶ P ⊗_A N'`, `x ⊗ y ↦ x ⊗ f y`**, of cochain complexes of sheaves of
modules, induced by a homomorphism `f : N ⟶ N'` of left differential graded `A`-modules. -/
noncomputable def dgTensorMapLeft (f : N ⟶ N') : dgTensor P N ⟶ dgTensor P N' where
  f n := gradedTensorMap (gP P) (gMapLeft f) n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact gradedTensorMap_comm_d P f i

/-- The component in degree `n` of `dgTensorMapLeft P f` is the map of graded tensor products
induced by `f` in degree `n`. -/
@[simp]
theorem dgTensorMapLeft_f (f : N ⟶ N') (n : ℤ) :
    (dgTensorMapLeft P f).f n = gradedTensorMap (gP P) (gMapLeft f) n := rfl

/-- The map `P ⊗_A N ⟶ P ⊗_A N'` on a local section: it sends `x ⊗ y` to `x ⊗ f y`. -/
theorem dgTensorMapLeft_tmul (f : N ⟶ N') (n : ℤ) (q : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gP P).piece q.1.1).val.obj X) (y : ((gN N).piece q.1.2).val.obj X) :
    PresheafOfModules.Hom.app ((dgTensorMapLeft P f).f n).val X (tmul (gP P) (gN N) n q X x y) =
      tmul (gP P) (gN N') n q X x
        (PresheafOfModules.Hom.app (f.toHomologicalComplex.f q.1.2).val X y) :=
  gradedTensorMap_tmul (gP P) (gMapLeft f) n q X x y

/-- **The map in the second variable is natural in the first one**: tensoring a homomorphism
of right modules and a homomorphism of left modules in either order gives the same map. -/
theorem dgTensorFunctor_map_comp_dgTensorMapLeft {P P' : DifferentialGradedModule.{t, m, m} A}
    (h : P ⟶ P') (f : N ⟶ N') :
    (dgTensorFunctor N).map h ≫ dgTensorMapLeft P' f =
      dgTensorMapLeft P f ≫ (dgTensorFunctor N').map h := by
  ext n : 1
  exact gradedTensorMapRight_gradedTensorMap (gMap h) (gMapLeft f) n

end MapLeft

end RelativeTensor

/-! ### Homomorphisms read across the opposite algebra -/

section Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} R}

/-- A degreewise morphism of cochain complexes carries a section heterogeneously equal to a
multiple `ε • z` in a degree `k = k'` to the multiple `ε • φ z`. -/
private theorem hom_f_app_heq_zsmul {M N : CochainComplex (SheafOfModules.{m} R) ℤ} (φ : M ⟶ N)
    {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (ε : ℤ) {x : (M.X k).val.obj U} {z : (M.X k').val.obj U}
    (hx : x ≍ ε • z) : (φ.f k).val.app U x ≍ ε • (φ.f k').val.app U z :=
  (heq_dependent_apply (fun k (y : (M.X k).val.obj U) ↦ (φ.f k).val.app U y) h hx).trans
    (heq_of_eq (hom_f_app_zsmul φ k' U ε z))

namespace LeftDifferentialGradedModule

/-- A homomorphism of left differential graded `A`-modules commutes with the interchanged right
actions of `A.op`. -/
theorem Hom.opRight_map_mul {N N' : LeftDifferentialGradedModule.{t, m, m} A} (f : N ⟶ N')
    (p n : ℤ) (U : Cᵒᵖ) (x : (N.complex.X p).val.obj U) (α : (A.complex.X n).val.obj U) :
    (f.toHomologicalComplex.f (p + n)).val.app U ((N.opRightMul p n).app U x α) =
      (N'.opRightMul p n).app U ((f.toHomologicalComplex.f p).val.app U x) α := by
  refine eq_of_heq ((hom_f_app_heq_zsmul f.toHomologicalComplex (Int.add_comm p n) U _
    (N.opRightMul_app_heq p n U x α)).trans ?_)
  refine HEq.trans (heq_of_eq (congrArg (fun z ↦ (Int.negOnePow (n * p) : ℤ) • z)
    (f.map_mul n p U α x))) ?_
  exact (N'.opRightMul_app_heq p n U ((f.toHomologicalComplex.f p).val.app U x) α).symm

/-- **A homomorphism of left differential graded `A`-modules, read as a homomorphism of right
differential graded `A.op`-modules.** The underlying morphism of cochain complexes is
unchanged. -/
noncomputable def Hom.opRight {N N' : LeftDifferentialGradedModule.{t, m, m} A} (f : N ⟶ N') :
    N.opRight ⟶ N'.opRight where
  toHomologicalComplex := f.toHomologicalComplex
  map_mul := Hom.opRight_map_mul f

/-- The morphism of cochain complexes underlying `Hom.opRight f` is that of `f`. -/
@[simp]
theorem Hom.opRight_toHomologicalComplex {N N' : LeftDifferentialGradedModule.{t, m, m} A}
    (f : N ⟶ N') : (Hom.opRight f).toHomologicalComplex = f.toHomologicalComplex := rfl

end LeftDifferentialGradedModule

namespace DifferentialGradedModule

/-- A homomorphism of right differential graded `A.op`-modules commutes with the interchanged
left actions of `A`. -/
theorem Hom.unopLeftMap_map_mul {P P' : DifferentialGradedModule.{t, m, m} A.op} (g : P ⟶ P')
    (n p : ℤ) (U : Cᵒᵖ) (α : (A.complex.X n).val.obj U) (x : (P.complex.X p).val.obj U) :
    (g.toHomologicalComplex.f (n + p)).val.app U ((P.unopLeftMul n p).app U α x) =
      (P'.unopLeftMul n p).app U α ((g.toHomologicalComplex.f p).val.app U x) := by
  refine eq_of_heq ((hom_f_app_heq_zsmul g.toHomologicalComplex (Int.add_comm n p) U _
    (P.unopLeftMul_app_heq n p U α x)).trans ?_)
  refine HEq.trans (heq_of_eq (congrArg (fun z ↦ (Int.negOnePow (n * p) : ℤ) • z)
    (g.map_mul p n U x α))) ?_
  exact (P'.unopLeftMul_app_heq n p U α ((g.toHomologicalComplex.f p).val.app U x)).symm

/-- **A homomorphism of right differential graded `A.op`-modules, read as a homomorphism of left
differential graded `A`-modules.** The underlying morphism of cochain complexes is
unchanged. -/
noncomputable def Hom.unopLeftMap {P P' : DifferentialGradedModule.{t, m, m} A.op}
    (g : P ⟶ P') : P.unopLeft ⟶ P'.unopLeft where
  toHomologicalComplex := g.toHomologicalComplex
  map_mul := Hom.unopLeftMap_map_mul g

/-- The morphism of cochain complexes underlying `Hom.unopLeftMap g` is that of `g`. -/
@[simp]
theorem Hom.unopLeftMap_toHomologicalComplex {P P' : DifferentialGradedModule.{t, m, m} A.op}
    (g : P ⟶ P') : (Hom.unopLeftMap g).toHomologicalComplex = g.toHomologicalComplex := rfl

end DifferentialGradedModule

end Opposite

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- **The interchange of the two factors is natural.** For a homomorphism `g : P ⟶ P'` of right
differential graded `A.op`-modules, the map `g ⊗ 1 : P ⊗_{A.op} M ⟶ P' ⊗_{A.op} M` in the first
variable is carried by the interchange to the map `1 ⊗ g : M ⊗_A P ⟶ M ⊗_A P'` in the second
one. -/
theorem opSwap_naturality (M : DifferentialGradedModule.{t, m, m} A)
    {P P' : DifferentialGradedModule.{t, m, m} A.op} (g : P ⟶ P') (n : ℤ) :
    gradedTensorMapRight (gMap g) (gN M.opLeft) n ≫ opSwap M P' n =
      opSwap M P n ≫
        gradedTensorMap (gP M) (gMapLeft (DifferentialGradedModule.Hom.unopLeftMap g)) n := by
  refine gradedTensor_hom_ext (gP P) (gN M.opLeft) fun q X u w ↦ ?_
  change PresheafOfModules.Hom.app (opSwap M P' n).val X
      (PresheafOfModules.Hom.app (gradedTensorMapRight (gMap g) (gN M.opLeft) n).val X
        (tmul (gP P) (gN M.opLeft) n q X u w)) =
    PresheafOfModules.Hom.app
      (gradedTensorMap (gP M) (gMapLeft (DifferentialGradedModule.Hom.unopLeftMap g)) n).val X
      (PresheafOfModules.Hom.app (opSwap M P n).val X (tmul (gP P) (gN M.opLeft) n q X u w))
  rw [gradedTensorMapRight_tmul, opSwap_tmul, opSwap_tmul, hom_val_app_zsmul,
    gradedTensorMap_tmul]
  rfl

end RelativeTensor

/-! ### Homomorphisms of bimodules -/

namespace DifferentialGradedBimodule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, m} R}

/-- The homomorphism of left differential graded `A`-modules underlying a homomorphism of
differential graded `(A, B)`-bimodules. -/
def Hom.toLeft {N N' : DifferentialGradedBimodule.{t, m, m} A B} (ν : N ⟶ N') :
    N.toLeftDifferentialGradedModule ⟶ N'.toLeftDifferentialGradedModule where
  toHomologicalComplex := ν.toHomologicalComplex
  map_mul := ν.map_leftMul

/-- The morphism of cochain complexes underlying `Hom.toLeft ν` is that of `ν`. -/
@[simp]
theorem Hom.toLeft_toHomologicalComplex {N N' : DifferentialGradedBimodule.{t, m, m} A B}
    (ν : N ⟶ N') : (Hom.toLeft ν).toHomologicalComplex = ν.toHomologicalComplex := rfl

end DifferentialGradedBimodule

namespace RelativeTensor

open Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, max u v} (toRingCat J Osharp)}
  (M : DifferentialGradedModule.{t, max u v, max u v} A)
  {N N' : DifferentialGradedBimodule.{t, max u v, max u v} A B}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]

section BimoduleMap

/-- The homomorphism of underlying left graded modules of a homomorphism of bimodules. -/
noncomputable abbrev bMapLeft (ν : N ⟶ N') :
    N.toGradedBimodule.toLeftGradedModule ⟶ N'.toGradedBimodule.toLeftGradedModule :=
  gMapLeft (DifferentialGradedBimodule.Hom.toLeft ν)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}] in
/-- The map in the second variable of the presheaf-level tensor product, on a local section
`x ⊗ y`. -/
theorem mapPre_tmulPre (ν : N ⟶ N') (m : ℤ) (q : TensorIndex m) (X : Cᵒᵖ)
    (x : ((gP M).piece q.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece q.1.2).val.obj X) :
    PresheafOfModules.Hom.app (gradedTensorMapPre (gP M) (bMapLeft ν) m) X
        (tmulPre (gP M) N.toGradedBimodule m q X x y) =
      tmulPre (gP M) N'.toGradedBimodule m q X x
        (PresheafOfModules.Hom.app ((bMapLeft ν).app q.1.2).val X y) :=
  Eq.trans (PresheafOfModules.hom_congr_apply'
      (cokernel.π_desc _ _ _ : gradedTensorπ (gP M) N.toGradedBimodule.toLeftGradedModule m ≫
        gradedTensorMapPre (gP M) (bMapLeft ν) m = _) X _)
    (congrArg (PresheafOfModules.Hom.app
        (gradedTensorπ (gP M) N'.toGradedBimodule.toLeftGradedModule m) X)
      (tensorSumMap_tensorSumι_apply (gP M) (bMapLeft ν) q X x y))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}] in
/-- **The map in the second variable of the presheaf-level tensor product commutes with the
right action of `B`**, because a homomorphism of bimodules does. -/
theorem actPre_comp_mapPre (ν : N ⟶ N') (m i : ℤ) :
    actPre.{t, v, u, max u v} (gP M) N.toGradedBimodule m i (m + i) rfl ≫
        bilinHomMap (B.complex.X i).val (gradedTensorMapPre (gP M) (bMapLeft ν) (m + i)) =
      gradedTensorMapPre (gP M) (bMapLeft ν) m ≫
        actPre.{t, v, u, max u v} (gP M) N'.toGradedBimodule m i (m + i) rfl := by
  refine (cancel_epi (gradedTensorπ (gP M) N.toGradedBimodule.toLeftGradedModule m)).mp
    (Limits.Sigma.hom_ext _ _ fun q => ?_)
  refine PresheafOfModules.tensorObj_hom_ext fun X x y => ?_
  refine hApp_ext fun V f b => ?_
  change PresheafOfModules.Hom.app (gradedTensorMapPre (gP M) (bMapLeft ν) (m + i)) V
      (hApp (PresheafOfModules.Hom.app
        (actPre.{t, v, u, max u v} (gP M) N.toGradedBimodule m i (m + i) rfl) X
        (tmulPre (gP M) N.toGradedBimodule m q X x y)) f b) =
    hApp (PresheafOfModules.Hom.app
      (actPre.{t, v, u, max u v} (gP M) N'.toGradedBimodule m i (m + i) rfl) X
      (PresheafOfModules.Hom.app (gradedTensorMapPre (gP M) (bMapLeft ν) m) X
        (tmulPre (gP M) N.toGradedBimodule m q X x y))) f b
  rw [actPre_tmulPre, mapPre_tmulPre, mapPre_tmulPre, actPre_tmulPre,
    ← Stacks.restr_app ((bMapLeft ν).app q.1.2).val f y]
  exact congrArg (tmulPre (gP M) N'.toGradedBimodule (m + i) (actIndex q i (m + i) rfl) V
    (restr ((gP M).piece q.1.1).val f x)) (ν.map_rightMul q.1.2 i V _ b)

/-- The map in the second variable of the tensor product, on a local section coming from the
presheaf level. -/
theorem gradedTensorMap_unit (ν : N ⟶ N') (m : ℤ) (X : Cᵒᵖ)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m).obj X) :
    PresheafOfModules.Hom.app (gradedTensorMap (gP M) (bMapLeft ν) m).val X
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) X w) =
      PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N'.toGradedBimodule.toLeftGradedModule m) X
        (PresheafOfModules.Hom.app (gradedTensorMapPre (gP M) (bMapLeft ν) m) X w) :=
  PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (φ := gradedTensorMapPre (gP M) (bMapLeft ν) m) X w

/-- **The map in the second variable of `M ⊗_A N` commutes with the right action of `B`**. -/
theorem gradedTensorMap_smul (ν : N ⟶ N') (m i : ℤ) (X : Cᵒᵖ)
    (s : (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule m).val.obj X)
    (b : (B.complex.X i).val.obj X) :
    PresheafOfModules.Hom.app (gradedTensorMap (gP M) (bMapLeft ν) (m + i)).val X
        ((gradedTensorRight (gP M) N.toGradedBimodule).smul m i X s b) =
      (gradedTensorRight (gP M) N'.toGradedBimodule).smul m i X
        (PresheafOfModules.Hom.app (gradedTensorMap (gP M) (bMapLeft ν) m).val X s) b := by
  have hsurj : PresheafOfModules.IsLocallySurjective J
      (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
      (α := 𝟙 (toRingCat J Osharp).obj) _
  refine Stacks.BilinearMap.app_eq_of_isLocallySurjective
    (gradedTensor (gP M) N'.toGradedBimodule.toLeftGradedModule (m + i)).isSheaf.isSeparated
    (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m)
    (((gradedTensorRight (gP M) N.toGradedBimodule).smulBil m i).postcomp
      (gradedTensorMap (gP M) (bMapLeft ν) (m + i)).val)
    (((gradedTensorRight (gP M) N'.toGradedBimodule).smulBil m i).compLeft
      (gradedTensorMap (gP M) (bMapLeft ν) m).val) ?_ X s b
  intro W z b'
  change PresheafOfModules.Hom.app (gradedTensorMap (gP M) (bMapLeft ν) (m + i)).val W
      ((gradedTensorRight (gP M) N.toGradedBimodule).smul m i W
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) W z) b') =
    (gradedTensorRight (gP M) N'.toGradedBimodule).smul m i W
      (PresheafOfModules.Hom.app (gradedTensorMap (gP M) (bMapLeft ν) m).val W
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) W z)) b'
  rw [gradedTensorRight_smul_unit M N m i W z b', gradedTensorMap_unit,
    gradedTensorMap_unit, gradedTensorRight_smul_unit M N' m i W _ b']
  exact congrArg (PresheafOfModules.Hom.app
      (gradedTensorUnit (gP M) N'.toGradedBimodule.toLeftGradedModule (m + i)) W)
    (congrArg (fun w => hApp w (𝟙 W) b')
      (PresheafOfModules.hom_congr_apply (actPre_comp_mapPre M ν m i) W z))

/-- **The homomorphism `M ⊗_A N ⟶ M ⊗_A N'` of right differential graded `B`-modules**,
`x ⊗ y ↦ x ⊗ ν y`, induced by a homomorphism `ν : N ⟶ N'` of differential graded
`(A, B)`-bimodules. -/
noncomputable def dgTensorRightMapLeft (ν : N ⟶ N') : dgTensorRight M N ⟶ dgTensorRight M N' where
  toHomologicalComplex := dgTensorMapLeft M (DifferentialGradedBimodule.Hom.toLeft ν)
  map_mul m i X x y := gradedTensorMap_smul M ν m i X x y

/-- The morphism of cochain complexes underlying `dgTensorRightMapLeft M ν` is the map
`dgTensorMapLeft M (Hom.toLeft ν)` induced by the underlying homomorphism of left modules. -/
@[simp]
theorem dgTensorRightMapLeft_toHomologicalComplex (ν : N ⟶ N') :
    (dgTensorRightMapLeft M ν).toHomologicalComplex =
      dgTensorMapLeft M (DifferentialGradedBimodule.Hom.toLeft ν) := rfl

/-- The map in the bimodule is natural in the right differential graded module. -/
theorem dgTensorRightMap_comp_dgTensorRightMapLeft
    {M M' : DifferentialGradedModule.{t, max u v, max u v} A} (h : M ⟶ M') (ν : N ⟶ N') :
    dgTensorRightMap M N h ≫ dgTensorRightMapLeft M' ν =
      dgTensorRightMapLeft M ν ≫ dgTensorRightMap M N' h :=
  DifferentialGradedModule.Hom.ext fun n =>
    gradedTensorMapRight_gradedTensorMap (gMap h) (bMapLeft ν) n

/-- **The natural transformation `- ⊗_A N ⟶ - ⊗_A N'`** of functors from right differential
graded `A`-modules to right differential graded `B`-modules induced by a homomorphism of
differential graded `(A, B)`-bimodules. -/
noncomputable def dgTensorRightFunctorMap (ν : N ⟶ N') :
    dgTensorRightFunctor N ⟶ dgTensorRightFunctor N' where
  app M := dgTensorRightMapLeft M ν
  naturality _ _ h := dgTensorRightMap_comp_dgTensorRightMapLeft h ν

/-- The component of `dgTensorRightFunctorMap ν` at `M` is `dgTensorRightMapLeft M ν`. -/
@[simp]
theorem dgTensorRightFunctorMap_app (ν : N ⟶ N') :
    (dgTensorRightFunctorMap ν).app M = dgTensorRightMapLeft M ν := rfl

end BimoduleMap

end RelativeTensor

end SheafOfModules

end
