module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.WedgeDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationKFlatSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CochainEvaluationLocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSingleSourceLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.AssociatorOnLocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomBijectionNatural
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints

/-!
# The tensor–internal-Hom adjunction on maps into an internal Hom complex

Let `(C, 𝒪)` be a ringed site, `A`, `B`, `C` complexes of `𝒪`-modules with `A` and `B` K-flat,
and `u : A ⟶ SheafHom(B, C)` a map into the internal Hom complex of [Stacks, Tag 0A8Z]. Then
under the tensor–internal-Hom adjunction of [Stacks, Tag 08J8] the map
`A ⟶ SheafHom(B, C) ⟶ RSheafHom(B, C)` corresponds to the pairing

`A ⊗^L B ⟶ Tot(A ⊗ B) ⟶ C`,

the canonical map of [Stacks, Tag 06YU] followed by the transpose of `u` under the currying
isomorphism of [Stacks, Tag 0A90].

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorObjIso_hom_comp_toTensor_of_kFlat`: the two
  canonical derived tensor products have the same canonical map on K-flat complexes.
* `AlgebraicGeometry.RingedSite.homEquiv_Q_map_comp_strictlyPerfectHomComparison`: the
  statement above.
* `AlgebraicGeometry.RingedSite.applyHomSection_sheafHomComplexSingleIso_inv`: evaluation of
  degree-zero Hom sections between sheaves placed in degree zero.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, u, u})

/-- A degree-zero section of the internal Hom complex between two sheaves placed in degree zero,
read as a section of the internal Hom sheaf, evaluates as that internal Hom section does. -/
theorem applyHomSection_sheafHomComplexSingleIso_inv
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (W : Z.C)
    (ψ : (internalHomSheaf Z A B).val.obj (op W)) (y : A.val.obj (op W)) (h : (0 : ℤ) + 0 = 0) :
    applyHomSection Z (sheafHomComplex Z (sgl Z A) (sgl Z B)) W 0 0 0 h
        (((sheafHomComplexSingleIso Z A B).inv.f 0).val.app (op W) ψ) y =
      ψ.app (op (Over.mk (𝟙 W))) y := by
  have e : (homComponent Z (E := sgl Z A) (F := sgl Z B) 0 0).val.app (op W)
      (((sheafHomComplexSingleIso Z A B).inv.f 0).val.app (op W) ψ) = ψ :=
    congrArg (fun φ => φ.val.app (op W) ψ)
      (HomologicalComplex.congr_hom (sheafHomComplexSingleIso Z A B).inv_hom_id 0)
  exact congrArg (fun φ => φ.app (op (Over.mk (𝟙 W))) y) e

/-- A sheaf placed in degree zero has only zero sections in the other degrees. -/
theorem eq_zero_of_isZero_sgl_X
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    {p : ℤ} (hp : p ≠ 0) {W : Z.Cᵒᵖ} (x : ((sgl Z M).X p).val.obj W) : x = 0 :=
  congrArg (fun φ : (sgl Z M).X p ⟶ (sgl Z M).X p => φ.val.app W x)
    ((isZero_sgl_X Z M p hp).eq_of_src (𝟙 _) 0)

/-- The local pure tensor with a zero section of the right complex is zero. -/
theorem tensorComplexSection_zero_right
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (t r c : ℤ) (htr : t + r = c) {W : Z.C} (k : (K.X t).val.obj (op W)) :
    tensorComplexSection Z t r c htr k (0 : (L.X r).val.obj (op W)) = 0 := by
  simpa using tensorComplexSection_add_right Z t r c htr k (0 : (L.X r).val.obj (op W)) 0

/-- The local pure tensor with a zero section of the left complex is zero. -/
theorem tensorComplexSection_zero_left
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    (t r c : ℤ) (htr : t + r = c) {W : Z.C} (l : (L.X r).val.obj (op W)) :
    tensorComplexSection Z t r c htr (0 : (K.X t).val.obj (op W)) l = 0 := by
  simpa using tensorComplexSection_add_left Z t r c htr (0 : (K.X t).val.obj (op W)) 0 l

/-- **The comparison of the two derived tensor products on K-flat complexes**: on two K-flat
complexes `K`, `L` the comparison `derivedTensorObjIso` carries the canonical map
`K ⊗^L L ⟶ Tot(K ⊗ L)` of one derived tensor product to that of the other. Both are the K-flat
comparison of `CochainComplex.KFlatBifunctor.derivedBifunctor` read through the identification
of that bifunctor with each of them. -/
theorem derivedTensorObjIso_hom_comp_toTensor_of_kFlat
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Z.O K) (hL : Stacks.SheafOfModules.KFlat Z.O L) :
    (derivedTensorObjIso Z (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.O).toTensor K L =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z).toTensor K L := by
  have h2 := Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_comp_comparison Z.O
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.O) K L hK hL
  have h1 := Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_comp_comparison Z.O
    (derivedTensorProductDatumOfSite Z (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z))
    K L hK hL
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.O).toTensor_eq_comparison
    K L hK hL, (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z).toTensor_eq_comparison
    K L hK hL]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h2.trans h1.symm)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.id_comp _))
  refine congrArg (· ≫ _) ?_
  exact congrArg (fun φ => (φ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L))
    (Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso Z.O
      (derivedTensorProductDatumOfSite Z
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z))).inv_hom_id

/-- **The pairing determined by a map into the internal Hom complex, at a K-flat source.** Let
`A`, `B`, `C` be complexes of `𝒪`-modules with `A` and `B` K-flat and `u : A ⟶ SheafHom(B, C)`.
Under the tensor–internal-Hom adjunction of [Stacks, Tag 08J8], the composite of `u` with the
comparison `SheafHom(B, C) ⟶ RSheafHom(B, C)` of [Stacks, Tag 08DM] corresponds to the pairing
`A ⊗^L B ⟶ Tot(A ⊗ B) ⟶ C`: the canonical map of [Stacks, Tag 06YU] followed by the class of the
transpose of `u` under the currying of [Stacks, Tag 0A90]. -/
theorem homEquiv_Q_map_comp_strictlyPerfectHomComparison
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hA : Stacks.SheafOfModules.KFlat Z.O A) (hB : Stacks.SheafOfModules.KFlat Z.O B)
    (u : A ⟶ (sheafHomComplex Z B C).obj) :
    (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        Z).homEquiv _ _ _
      (DerivedCategory.Q.map u ≫
        strictlyPerfectHomComparison Z (derivedInternalHomOfBifunctor Z) B C) =
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.O).toTensor A B ≫
        DerivedCategory.Q.map (curryHomEquiv Z A B C u) := by
  have e1 := derivedCurryHomEquiv_naturality_source Z (DerivedCategory.Q.map u)
    (strictlyPerfectHomComparison Z (derivedInternalHomOfBifunctor Z) B C)
  have e2 := derivedCurryHomEquiv_strictlyPerfectHomComparison Z B C hB
  have e3 := (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z).toTensor_naturality u (𝟙 B)
  have e4 := curryHomEquiv_eq_tensor_evaluation Z _ _ _ u
  have e6 := derivedTensorObjIso_hom_comp_toTensor_of_kFlat Z _ _ hA hB
  have hid : ((Stacks.SheafOfModules.canonicalDerivedTensorProduct Z).tensor.obj
        (DerivedCategory.Q.obj (sheafHomComplex Z B C).obj)).map (DerivedCategory.Q.map (𝟙 B)) =
      𝟙 _ := by simp
  have e3' := (congrArg (_ ≫ ·) ((Category.id_comp _).symm.trans
    (congrArg (· ≫ _) hid.symm))).trans e3
  have e0 := (congrArg (fun F => F _ _ _ (DerivedCategory.Q.map u ≫
      strictlyPerfectHomComparison Z (derivedInternalHomOfBifunctor Z) B C))
    (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction_homEquiv
      Z)).trans
    (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorCurryHomEquiv_apply
      Z _ _ _ _)
  refine e0.trans ?_
  rw [e1, e2]
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e3').trans
    (Category.assoc _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans (congrArg₂ (· ≫ ·) ?_ ?_)
  · exact (congrArg (_ ≫ ·) e6.symm).trans (Iso.inv_hom_id_assoc _ _)
  · exact (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg _ e4.symm)

end AlgebraicGeometry.RingedSite

end
