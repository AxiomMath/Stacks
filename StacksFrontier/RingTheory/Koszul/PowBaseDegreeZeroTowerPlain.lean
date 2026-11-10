module

public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitTriangulatedTower
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedProducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorNatTransCommShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorQuasiIsoDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedCellFiltration
public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic
public import StacksFrontier.RingTheory.Koszul.PowKoszulDerivedLimit

/-!
# The tower `n ↦ P_n ⊗_R^𝐋 K_t` has zero derived limit when `n ↦ P_n` does

Let `R` be a commutative ring, `f₁, …, f_r ∈ R`, `t ≥ 1`, and let `K_t` be the Koszul algebra on
`f₁ ^ t, …, f_r ^ t`, read as a differential graded module over `R` placed in degree zero. For an
inverse system `(P_n)` of differential graded bimodules over the Koszul algebras the right-hand
tower of Tag 0GZJ is `n ↦ P_n ⊗_R^𝐋 K_t` (`Koszul.powBaseDegreeZeroDerivedTensorTower`). This file
proves that **if the tower `n ↦ P_n` of `D(B, d)` has derived limit zero, so does the tower
`n ↦ P_n ⊗_R^𝐋 K_t`**, which is the step `0 = R lim M_n ⇒ 0 = R lim (M_n ⊗_R^𝐋 K_t)` of the proof
of Proposition 0GZK.

The argument is a dévissage in the variable `K_t`. Each `X ↦ P_n ⊗_R^𝐋 X` is a triangulated functor
on `D(R)` and the transition maps of the bimodules induce transformations of these functors which
commute with the shift, so the objects `X` of `D(R)` for which `n ↦ P_n ⊗_R^𝐋 X` has derived limit
zero form a triangulated subcategory
(`CategoryTheory.Pretriangulated.TriangulatedTower.rlimZero_isTriangulated`). It contains `R`,
because `R ⊗_R^𝐋 P_n = P_n`, and therefore every finite direct sum of shifts of `R`; and `K_t` is
built out of those by finitely many distinguished triangles, those of its filtration by exterior
degree (`Koszul.gradedCellDataBaseModule`).

## Main definitions

* `DifferentialGraded.absBaseBimoduleMap`: a semilinear homomorphism of bimodules over a
  homomorphism of differential graded algebras, read as a homomorphism of bimodules over `R`
  placed in degree zero.
* `Koszul.powBaseDegreeZeroTensorFunctor` and `Koszul.powBaseDegreeZeroTensorNatTrans`: the
  functors `- ⊗_R^𝐋 P_n` and their transition transformations.

## Main results

* `DifferentialGradedModule.prop_of_gradedCellData`: a triangulated subcategory of `D(A, d)`
  containing the images of the graded pieces of a triangular cell decomposition contains the image
  of the module.
* `Koszul.powBaseDegreeZeroDerivedTensorTower_tower_eq`: the tower of Tag 0GZJ is the tower of the
  functors `- ⊗_R^𝐋 P_n` at `K_t`.
* `Koszul.isZero_of_isDerivedLimit_powBaseDegreeZeroDerivedTensorTower`: **if `n ↦ P_n` has
  derived limit zero, so does `n ↦ P_n ⊗_R^𝐋 K_t`.**

## References

* [Stacks Project, Tag 0GZK](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
* [Stacks Project, Tag 09S3](https://stacks.math.columbia.edu/tag/09S3) for the transformation
  `1 ⊗ f` of derived tensor functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'


universe u

/-! ### Dévissage along a triangular cell decomposition -/

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- **A triangulated subcategory of `D(A, d)` containing the class of `A` contains the classes of
the finite direct sums of shifts of `A`.** -/
theorem prop_directSumShifts (P : ObjectProperty (derivedCategory' A)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (hA : P ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))
    {ι : Type u} [Finite ι] [DecidableEq ι] (k : ι → ℤ) :
    P ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (directSumShifts A k)) := by
  let Q := toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q
  have : P.IsClosedUnderFiniteCoproducts :=
    ⟨fun _ _ => P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩
  have hshift : ∀ i, P (Q.obj (shift (regularModule A) (k i))) := fun i =>
    P.prop_of_iso ((Q.commShiftIso (k i)).app (regularModule A)).symm (P.le_shift (k i) _ hA)
  exact P.prop_of_iso (Q.mapIso ((directSumObjIsoSigma _).symm ≪≫
    directSumObjIsoDirectSumShifts A k)) (P.prop_of_isColimit_cofan
      (isColimitCofanMkObjOfIsColimit Q (fun i => shift (regularModule A) (k i)) _
        (coproductIsCoproduct fun i => shift (regularModule A) (k i))) hshift)

/-- **Dévissage along a triangular cell decomposition.** A triangulated subcategory of `D(A, d)`
containing the classes of the graded pieces of a triangular cell decomposition of `M` contains
the class of `M`: the steps of the filtration are admissible short exact sequences, whose
triangles are distinguished. -/
theorem prop_of_gradedCellData (P : ObjectProperty (derivedCategory' A)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] {M : DifferentialGradedModule.{u, u, u} A}
    (D : GradedCellData M)
    (hD : ∀ m, P ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (D.layer m))) :
    P ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj M) := by
  let Q := toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q
  have key (k : ℕ) : P (Q.obj (D.stage (k + 1)).obj) := by
    induction k with
    | zero => exact P.prop_of_iso (Q.mapIso D.stageOneIso.symm) (hD 0)
    | succ k ih =>
      have hdist := ((quasiIsomorphisms' A).Q).map_distinguished _
        (associatedTriangle_mem_distTriang A _ _
          (D.isAdmissibleShortExact_stageIncl_layerHom (k + 1)))
      exact P.ext_of_isTriangulatedClosed₂ _ hdist ih (hD (k + 1))
  exact P.prop_of_iso (Q.mapIso D.topStageIso) (key D.bound)

end DifferentialGradedModule

/-! ### The comparison with the plain tensor product, natural in the bimodule -/

namespace CategoryTheory

/-- If `τ ≫ κ' = κ ≫ q ≫ m ≫ p'` and `p' ≫ q' = 𝟙`, then `τ ≫ κ' ≫ q' = (κ ≫ q) ≫ m`. -/
theorem comp_comp_eq_of_eq_comp {D : Type*} [Category D] {W X Y V U T : D} (τ : W ⟶ X)
    (κ' : X ⟶ Y) (q' : Y ⟶ T) (κ : W ⟶ V) (q : V ⟶ U) (m : U ⟶ T) (p' : T ⟶ Y)
    (h : τ ≫ κ' = κ ≫ q ≫ m ≫ p') (hp : p' ≫ q' = 𝟙 T) :
    τ ≫ κ' ≫ q' = (κ ≫ q) ≫ m := by
  rw [← Category.assoc, h]
  simp only [Category.assoc, hp, Category.comp_id]

end CategoryTheory

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **`1 ⊗ g` is computed by the plain tensor product.** At a module `X` orthogonal on the left to
the acyclic modules, the transformation `1 ⊗ g` of derived tensor functors induced by a
homomorphism `g : N ⟶ N'` of bimodules is, through the identifications of both derived tensor
products with the plain ones, the plain map `X ⊗_A N ⟶ X ⊗_A N'`. -/
@[reassoc]
theorem derivedTensorNatTrans_app_comp_derivedTensorObjIsoPlain_hom {N N' : Bimodule A B}
    (g : N ⟶ N') (X : DifferentialGradedModule.{u, u, u} A)
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X)) :
    (derivedTensorNatTrans g).app ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X)) ≫
        (derivedTensorObjIsoPlain N' X hX).hom =
      (derivedTensorObjIsoPlain N X hX).hom ≫
        (quasiIsomorphisms' B).Q.map
          ((toHomotopyCategory B).map ((tensorModuleNatTrans g).app X)) := by
  rw [derivedTensorObjIsoPlain_hom, derivedTensorObjIsoPlain_hom]
  have h := derivedTensorNatTrans_app_comp_counit g ((toHomotopyCategory A).obj X)
  rw [ordinaryTensorNatTrans_app, tensorHomotopyNatTrans_app, Functor.map_comp,
    Functor.map_comp] at h
  exact comp_comp_eq_of_eq_comp _ _ _ _ _ _ _ h
    (((quasiIsomorphisms' B).Q.map_comp _ _).symm.trans
      ((congrArg (quasiIsomorphisms' B).Q.map
        ((tensorCompFunctor_quotient N').hom_inv_id_app X)).trans
          ((quasiIsomorphisms' B).Q.map_id _)))

/-- **The unit isomorphism `A ⊗_A N ≅ N` is natural in the bimodule.** -/
theorem tensorRegularIso_naturality {N N' : Bimodule A B} (g : N ⟶ N') :
    (tensorModuleNatTrans g).app (regularModule A) ≫ (tensorRegularIso N').1.hom =
      (tensorRegularIso N).1.hom ≫ g.rightHom := by
  refine tensorObj_hom_ext' N (regularModule A) _ _ fun x y => ?_
  change (tensorRegularIso N').1.hom.toFun
      ((tensorHomOfBimoduleHom g (regularModule A)).toFun _) =
    g.rightHom.toFun ((tensorRegularIso N).1.hom.toFun _)
  rw [tensorHomOfBimoduleHom_pure, (tensorRegularIso N').2, (tensorRegularIso N).2,
    Hom.map_leftActionTotal' g x y]

/-- **The derived unit isomorphism `A ⊗_A^𝐋 N ≅ N`**, built from the identification of the derived
tensor product at the regular module with the plain one. -/
def derivedTensorRegularIso' (N : Bimodule A B) :
    (derivedTensorFunctor N).obj
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A))) ≅
      (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N.rightModule) :=
  derivedTensorObjIsoPlain N (regularModule A)
      (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A) ≪≫
    (quasiIsomorphisms' B).Q.mapIso ((toHomotopyCategory B).mapIso (tensorRegularIso N).1)

/-- **The derived unit isomorphism is natural in the bimodule.** -/
theorem derivedTensorNatTrans_app_comp_derivedTensorRegularIso'_hom {N N' : Bimodule A B}
    (g : N ⟶ N') :
    (derivedTensorNatTrans g).app
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A))) ≫
        (derivedTensorRegularIso' N').hom =
      (derivedTensorRegularIso' N).hom ≫
        (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map g.rightHom) := by
  have h' : (quasiIsomorphisms' B).Q.map
        ((toHomotopyCategory B).map ((tensorModuleNatTrans g).app (regularModule A))) ≫
      (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map (tensorRegularIso N').1.hom) =
      (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map (tensorRegularIso N).1.hom) ≫
        (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map g.rightHom) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (((toHomotopyCategory B).map_comp _ _).symm.trans
      (congrArg _ (tensorRegularIso_naturality g)))
  simp only [derivedTensorRegularIso', Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [derivedTensorNatTrans_app_comp_derivedTensorObjIsoPlain_hom_assoc]
  exact (Category.assoc _ _ _).trans
    (congrArg ((derivedTensorObjIsoPlain N (regularModule A) _).hom ≫ ·) h')

end DifferentialGraded.Bimodule

/-! ### Semilinear homomorphisms of bimodules over the base ring in degree zero -/

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, u} R)

/-- **A semilinear homomorphism of bimodules, read over the base ring placed in degree zero.** A
`σ`-semilinear homomorphism `g : P₂ ⟶ P₁|_σ` is an honest homomorphism of the differential graded
`(R, B)`-bimodules `DifferentialGraded.absBaseBimodule`, because `σ` is a homomorphism of
`R`-algebras. -/
def absBaseBimoduleMap {A₁ A₂ : DifferentialGradedAlgebra.{u, u} R} (σ : A₂.Hom A₁)
    {P₁ : Bimodule A₁ B} {P₂ : Bimodule A₂ B} (g : P₂ ⟶ Bimodule.restrictLeft σ P₁) :
    absBaseBimodule A₂ B P₂ ⟶ absBaseBimodule A₁ B P₁ where
  rightHom := g.rightHom
  map_left n p a x := by
    have hact : σ.gradingMap n ((baseHom A₂).gradingMap n a) = (baseHom A₁).gradingMap n a :=
      Subtype.ext (σ.toAlgebraHom.commutes _)
    have h := g.map_left n p ((baseHom A₂).gradingMap n a) x
    rw [Bimodule.restrictLeft_action σ P₁ n ((baseHom A₂).gradingMap n a), hact] at h
    exact h

/-- The underlying right module map of `absBaseBimoduleMap B σ g` is that of `g`. -/
@[simp] theorem absBaseBimoduleMap_rightHom {A₁ A₂ : DifferentialGradedAlgebra.{u, u} R}
    (σ : A₂.Hom A₁) {P₁ : Bimodule A₁ B} {P₂ : Bimodule A₂ B}
    (g : P₂ ⟶ Bimodule.restrictLeft σ P₁) : (absBaseBimoduleMap B σ g).rightHom = g.rightHom :=
  rfl

end DifferentialGraded

/-! ### The Koszul tower -/

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule
  DifferentialGraded.Bimodule TriangulatedTower

variable {R : Type u} [CommRing R] {r : ℕ} {B : DifferentialGradedAlgebra.{u, u} R}
  (f : Fin r → R) (t : ℕ) {b : ℕ} (hb : 1 ≤ b)
  (bimod : ∀ k : ℕ, Bimodule (oppAlgebra (powAlgebra f (b + k))) B)
  (bimodTrans : ∀ k : ℕ,
    bimod (k + 1) ⟶ Bimodule.restrictLeft (powSuccTransition f hb k) (bimod k))

/-- The bimodule `P_k`, read over `R` placed in degree zero. -/
abbrev powBaseBimod (k : ℕ) : Bimodule (degreeZero R R) B :=
  absBaseBimodule (oppAlgebra (powAlgebra f (b + k))) B (bimod k)

/-- The transition `P_{k+1} ⟶ P_k`, read over `R` placed in degree zero. -/
def powBaseBimodMap (k : ℕ) : powBaseBimod f bimod (k + 1) ⟶ powBaseBimod f bimod k :=
  absBaseBimoduleMap B (powSuccTransition f hb k) (bimodTrans k)

/-- The functor `- ⊗_R^𝐋 P_k : D(R) ⥤ D(B, d)`. -/
abbrev powBaseDegreeZeroTensorFunctor (k : ℕ) :
    derivedCategory' (degreeZero R R) ⥤ derivedCategory' B :=
  derivedTensorFunctor (powBaseBimod f bimod k)

/-- The transition `- ⊗_R^𝐋 P_{k+1} ⟶ - ⊗_R^𝐋 P_k` of the functors. -/
abbrev powBaseDegreeZeroTensorNatTrans (k : ℕ) :
    powBaseDegreeZeroTensorFunctor f bimod (k + 1) ⟶ powBaseDegreeZeroTensorFunctor f bimod k :=
  derivedTensorNatTrans (powBaseBimodMap f hb bimod bimodTrans k)

/-- The plain transition of the tower `powBaseDegreeZeroDerivedTensorTower` is `1 ⊗ g` for the
transition `g` of the bimodules. -/
theorem powBaseDegreeZeroDerivedTensorTower_plainMap (k : ℕ) :
    (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).plainMap k =
      (tensorModuleNatTrans (powBaseBimodMap f hb bimod bimodTrans k)).app
        (baseModule (seqDual fun i => f i ^ t)) := by
  refine tensorObj_hom_ext' _ _ _ _ fun x y => ?_
  change ((tensorCompNatTransOfSemilinear _ _ _ _).app _).toFun
      (((tensorCompFunctor _).map _).toFun _) =
    (tensorHomOfBimoduleHom _ _).toFun _
  refine (congrArg _ (tensorCompFunctor_map_pure' _ _ x y)).trans ?_
  refine (tensorCompNatTransOfSemilinear_app_pure _ _ _ _ _ _ _).trans ?_
  exact (tensorHomOfBimoduleHom_pure _ _ x y).symm

/-- **The tower of Tag 0GZJ is the tower of the functors `- ⊗_R^𝐋 P_k` at `K_t`**: its transition
maps are the transformations `1 ⊗ g` at `K_t`. -/
theorem powBaseDegreeZeroDerivedTensorTower_towerMap (k : ℕ) :
    (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).towerMap k =
      (powBaseDegreeZeroTensorNatTrans f hb bimod bimodTrans k).app
        ((quasiIsomorphisms' (degreeZero R R)).Q.obj
          ((toHomotopyCategory (degreeZero R R)).obj (baseModule (seqDual fun i => f i ^ t)))) := by
  let T := powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans
  refine (cancel_mono (T.objIsoPlain k).hom).1 ?_
  rw [T.towerMap_objIsoPlain k, powBaseDegreeZeroDerivedTensorTower_plainMap]
  exact (derivedTensorNatTrans_app_comp_derivedTensorObjIsoPlain_hom _ _ _).symm


/-! ### The dévissage -/

/-- The graded pieces of the filtration of `K_t` by exterior degree are direct sums of shifts of
`R` placed in degree zero. -/
theorem gradedCellDataBaseModule_layer (φ : Module.Dual R (Fin r → R)) (m : ℕ) :
    (gradedCellDataBaseModule φ).layer m =
      directSumShifts (degreeZero R R) (fun _ : exteriorCellIndex.{u} r m => (m : ℤ)) :=
  rfl

/-- The plain transitions of the bimodules, read over `R` placed in degree zero, commute with the
derived unit isomorphisms `R ⊗_R^𝐋 P_n ≅ P_n`. -/
theorem powBaseDegreeZeroTensorNatTrans_app_regularModule (n : ℕ) :
    (derivedTensorRegularIso' (powBaseBimod f bimod (n + 1))).hom ≫
      (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map
        (powBaseBimodMap f hb bimod bimodTrans n).rightHom) =
    (powBaseDegreeZeroTensorNatTrans f hb bimod bimodTrans n).app
        ((quasiIsomorphisms' (degreeZero R R)).Q.obj
          ((toHomotopyCategory (degreeZero R R)).obj (regularModule (degreeZero R R)))) ≫
      (derivedTensorRegularIso' (powBaseBimod f bimod n)).hom :=
  (derivedTensorNatTrans_app_comp_derivedTensorRegularIso'_hom
      (powBaseBimodMap f hb bimod bimodTrans n)).symm

section Devissage

variable [HasProductsOfShape ℕ (derivedCategory' B)]

/-- **`R` lies in the subcategory**: the tower `n ↦ R ⊗_R^𝐋 P_n` is the tower `n ↦ P_n`, so if the
difference map of the latter is invertible, so is that of the former. -/
theorem rlimZero_powBaseDegreeZeroTensor_regularModule
    (hP : IsIso (familyDifference
      (fun n => (quasiIsomorphisms' B).Q.obj
        ((toHomotopyCategory B).obj (powBaseBimod f bimod n).rightModule))
      fun n => (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map
        (powBaseBimodMap f hb bimod bimodTrans n).rightHom))) :
    rlimZero (powBaseDegreeZeroTensorFunctor f bimod)
      (powBaseDegreeZeroTensorNatTrans f hb bimod bimodTrans)
      ((quasiIsomorphisms' (degreeZero R R)).Q.obj
        ((toHomotopyCategory (degreeZero R R)).obj (regularModule (degreeZero R R)))) :=
  isIso_familyDifference_of_iso (fun n => derivedTensorRegularIso' (powBaseBimod f bimod n))
    (fun n => powBaseDegreeZeroTensorNatTrans_app_regularModule f hb bimod bimodTrans n) hP

/-- **`K_t` lies in the subcategory**, by dévissage along its filtration by exterior degree. -/
theorem rlimZero_powBaseDegreeZeroTensor_baseModule
    (hP : IsIso (familyDifference
      (fun n => (quasiIsomorphisms' B).Q.obj
        ((toHomotopyCategory B).obj (powBaseBimod f bimod n).rightModule))
      fun n => (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map
        (powBaseBimodMap f hb bimod bimodTrans n).rightHom))) :
    rlimZero (powBaseDegreeZeroTensorFunctor f bimod)
      (powBaseDegreeZeroTensorNatTrans f hb bimod bimodTrans)
      ((quasiIsomorphisms' (degreeZero R R)).Q.obj
        ((toHomotopyCategory (degreeZero R R)).obj (baseModule (seqDual fun i => f i ^ t)))) := by
  have := rlimZero_isTriangulated (F := powBaseDegreeZeroTensorFunctor f bimod)
    (τ := powBaseDegreeZeroTensorNatTrans f hb bimod bimodTrans)
  refine prop_of_gradedCellData _ (gradedCellDataBaseModule (seqDual fun i => f i ^ t))
    fun m => ?_
  rw [gradedCellDataBaseModule_layer]
  exact prop_directSumShifts _
    (rlimZero_powBaseDegreeZeroTensor_regularModule f hb bimod bimodTrans hP) _

/-- **If the tower `n ↦ P_n` of `D(B, d)` has invertible difference map, the tower
`n ↦ P_n ⊗_R^𝐋 K_t` of Tag 0GZJ has derived limit zero.** The difference map of `n ↦ P_n` is
invertible exactly when that tower has derived limit zero
(`CategoryTheory.Pretriangulated.IsDerivedLimit.isZero_iff_isIso_difference`). -/
theorem isZero_of_isDerivedLimit_powBaseDegreeZeroDerivedTensorTower
    (hP : IsIso (familyDifference
      (fun n => (quasiIsomorphisms' B).Q.obj
        ((toHomotopyCategory B).obj (powBaseBimod f bimod n).rightModule))
      fun n => (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map
        (powBaseBimodMap f hb bimod bimodTrans n).rightHom)))
    [HasProduct fun n : ℕ =>
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower.obj (op n)]
    {K : derivedCategory' B}
    (hK : IsDerivedLimit (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower K) :
    IsZero K := by
  refine hK.isZero_of_isIso_difference ?_
  have heq : familyDifference
      (fun n : ℕ => (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower.obj ⟨n⟩)
      (fun n => (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower.map
        (homOfLE (Nat.le_succ n)).op) =
      familyDifference
        (fun n => (powBaseDegreeZeroTensorFunctor f bimod n).obj
          ((quasiIsomorphisms' (degreeZero R R)).Q.obj
            ((toHomotopyCategory (degreeZero R R)).obj (baseModule (seqDual fun i => f i ^ t)))))
        fun n => (powBaseDegreeZeroTensorNatTrans f hb bimod bimodTrans n).app _ :=
    congrArg (familyDifference (fun n : ℕ =>
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower.obj ⟨n⟩))
      (funext fun n => ((powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower_map_succ
        n).trans (powBaseDegreeZeroDerivedTensorTower_towerMap f t hb bimod bimodTrans n))
  rw [heq]
  exact rlimZero_powBaseDegreeZeroTensor_baseModule f t hb bimod bimodTrans hP

end Devissage

end Koszul

end
