module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.HomBimodule
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.UnitPure

/-!
# The comparison `M ⊗_A Hom(L, K) ⟶ Hom(L, M ⊗_A K)`

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, and let `K`, `L` be complexes of `O`-modules with endomorphism
differential graded `R`-algebras `A = End(K)` and `B = End(L)`. Let `Ω' = Hom(L, K)`, the
differential graded `(A, B)`-bimodule of `AlgebraicGeometry.RingedSite.homBimodule`. For a
differential graded `A`-module `M` there is a homomorphism of differential graded `B`-modules

`M ⊗_A Hom(L, K) ⟶ Hom(L, M ⊗_A K)`, `x ⊗ φ ↦ (x ⊗ -) ∘ φ`,

natural in `M`; here `x ⊗ - : K → M ⊗_A K` is the image of `x` under the unit of the tensor-Hom
adjunction of Tag 09LV (`AlgebraicGeometry.RingedSite.tensorWithComplexDG_unit_pure`). It is the
comparison through which the composite `D(A) → D(O) → D(B)` of Remark 09SU is identified with
`- ⊗_A^𝐋 Hom(L, K)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.homComp`: composition `Hom(K, Y) × Hom(L, K) → Hom(L, Y)`.
* `AlgebraicGeometry.RingedSite.tensorHomBalanced`: the balanced bilinear map
  `(x, φ) ↦ (x ⊗ -) ∘ φ`.
* `AlgebraicGeometry.RingedSite.tensorHomComparison`: the homomorphism
  `M ⊗_A Hom(L, K) ⟶ Hom(L, M ⊗_A K)`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorHomComparison_pure`: its value on a pure tensor.
* `AlgebraicGeometry.RingedSite.tensorHomComparison_naturality`: its naturality in `M`.

## References

* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type u) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, u} X R]
  (K L : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-! ### Composition with `Hom(L, K)` -/

/-- Composition `Hom(K, Y)^p × Hom(L, K) → Hom(L, Y)`, on the degree-`p` part of the first
factor: `z ↦ (φ ↦ z ∘ φ)`, through the representable functor `Hom(L, -)`. -/
def homCompHom (Y : (CompDG.{u, u, u, u, u, u} X R).Obj) (p : ℤ) :
    ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).grading p →ₗ[R]
      ((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)).M →ₗ[R]
        ((Rep.{u, u, u, u, u, u} X R L).functor.obj Y).M :=
  (Submodule.subtype _).comp
    ({ toFun := fun f => (Rep.{u, u, u, u, u, u} X R L).functor.map f
       map_add' := (Rep.{u, u, u, u, u, u} X R L).functor.map_add
       map_smul' := (Rep.{u, u, u, u, u, u} X R L).functor.map_smul } ∘ₗ
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom Y p).toLinearMap)

/-- Composition `Hom(K, Y) × Hom(L, K) → Hom(L, Y)`, extended to the whole of `Hom(K, Y)` along
its decomposition into homogeneous parts. -/
def homComp (Y : (CompDG.{u, u, u, u, u, u} X R).Obj) :
    ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).M →ₗ[R]
      ((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)).M →ₗ[R]
        ((Rep.{u, u, u, u, u, u} X R L).functor.obj Y).M :=
  (DirectSum.toModule R ℤ _ (homCompHom X R K L Y)).comp
    (DirectSum.decomposeLinearEquiv
      ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).grading).toLinearMap

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- On a homogeneous element, `homComp` is the composition of its degree. -/
theorem homComp_of_mem (Y : (CompDG.{u, u, u, u, u, u} X R).Obj) {p : ℤ}
    (z : ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).M)
    (hz : z ∈ ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).grading p) :
    homComp X R K L Y z = homCompHom X R K L Y p ⟨z, hz⟩ := by
  change DirectSum.toModule R ℤ _ (homCompHom X R K L Y)
    (DirectSum.decompose ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).grading z) = _
  rw [DirectSum.decompose_of_mem _ hz, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- Composition is right `B`-linear in its second factor. -/
theorem homComp_smul_right (Y : (CompDG.{u, u, u, u, u, u} X R).Obj)
    (z : ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).M)
    (φ : ((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)).M)
    (b : (Rep.{u, u, u, u, u, u} X R L).algebra.A) :
    homComp X R K L Y z (MulOpposite.op b • φ) = MulOpposite.op b • homComp X R K L Y z φ := by
  induction z using DirectSum.Decomposition.inductionOn
    ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).grading with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', smul_add]
  | @homogeneous p z =>
    rw [homComp_of_mem X R K L Y _ z.property]
    exact ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom Y p z)).2.2 b φ

/-! ### The unit of the tensor-Hom adjunction -/

/-- The unit `M → Hom(K, M ⊗_A K)` of the tensor-Hom adjunction of Tag 09LV, as a linear map. -/
abbrev tensorUnitₗ (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) :
    M.M →ₗ[R] ((Rep.{u, u, u, u, u, u} X R K).functor.obj
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)).M :=
  ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).adjunction.unit.app M).1.1

/-- The unit preserves degrees. -/
theorem tensorUnitₗ_mem
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) (p : ℤ)
    (x : M.grading p) :
    tensorUnitₗ X R K M x ∈ ((Rep.{u, u, u, u, u, u} X R K).functor.obj
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)).grading p :=
  tensorWithComplexDG_unit_mem X R K M p x

/-- Composition with the image of a homogeneous element under the unit. -/
theorem homComp_tensorUnitₗ
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) (p : ℤ)
    (x : M.grading p) :
    homComp X R K L _ (tensorUnitₗ X R K M x) =
      homCompHom X R K L _ p ⟨_, tensorUnitₗ_mem X R K M p x⟩ :=
  homComp_of_mem X R K L _ _ _

/-- The unit commutes with the differentials: it is a closed morphism. -/
theorem tensorUnitₗ_d
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) (x : M.M) :
    ((Rep.{u, u, u, u, u, u} X R K).functor.obj
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)).d
        (tensorUnitₗ X R K M x) = tensorUnitₗ X R K M (M.d x) := by
  have h := congrArg (fun f : HomogeneousMap (Rep.{u, u, u, u, u, u} X R K).algebra M
      ((Rep.{u, u, u, u, u, u} X R K).functor.obj
        ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)) (0 + 1) => f.1 x)
    ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).adjunction.unit.app M).2
  change ((Rep.{u, u, u, u, u, u} X R K).functor.obj
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)).d
        (tensorUnitₗ X R K M x) -
      DifferentialGraded.gradedSign R 0 • tensorUnitₗ X R K M (M.d x) = 0 at h
  rw [DifferentialGraded.gradedSign_zero, one_smul, sub_eq_zero] at h
  exact h

/-- The unit is right `A`-linear. -/
theorem tensorUnitₗ_smul
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) (x : M.M)
    (a : (Rep.{u, u, u, u, u, u} X R K).algebra.A) :
    tensorUnitₗ X R K M (MulOpposite.op a • x) = MulOpposite.op a • tensorUnitₗ X R K M x :=
  ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).adjunction.unit.app M).1.2.2 a x

/-! ### The balanced bilinear map -/

/-- **The balanced bilinear map `(x, φ) ↦ (x ⊗ -) ∘ φ`** from a differential graded `A`-module
`M` and the bimodule `Hom(L, K)` to `Hom(L, M ⊗_A K)`. -/
def tensorHomBalanced
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) :
    DifferentialGraded.Bimodule.BalancedBilinearMap M (homBimodule X R K L)
      ((Rep.{u, u, u, u, u, u} X R L).functor.obj
        ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)) where
  toLinearMap := (homComp X R K L _).comp (tensorUnitₗ X R K M)
  map_grading p q x y := by
    change homComp X R K L _ (tensorUnitₗ X R K M x) y ∈ _
    rw [homComp_tensorUnitₗ]
    exact mem_grading_congr (add_comm q p) (((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom _ p
        ⟨_, tensorUnitₗ_mem X R K M p x⟩)).2.1 q (y : _) y.property)
  map_d p x y := by
    change ((Rep.{u, u, u, u, u, u} X R L).functor.obj _).d
        (homComp X R K L _ (tensorUnitₗ X R K M x) y) =
      homComp X R K L _ (tensorUnitₗ X R K M (M.d x)) y +
        (p.negOnePow : ℤ) • homComp X R K L _ (tensorUnitₗ X R K M x)
          (((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)).d y)
    have hdx := ((Rep.{u, u, u, u, u, u} X R K).functor.obj
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)).d_mem p _
        (tensorUnitₗ_mem X R K M p x)
    rw [← tensorUnitₗ_d, homComp_tensorUnitₗ, homComp_of_mem X R K L _ _ hdx]
    change _ = ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom _ (p + 1) ⟨_, hdx⟩)).1 y + _
    rw [(Rep.{u, u, u, u, u, u} X R K).module_d _ p ⟨_, tensorUnitₗ_mem X R K M p x⟩,
      (Rep.{u, u, u, u, u, u} X R L).functor.map_d]
    set f := (Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom _ p ⟨_, tensorUnitₗ_mem X R K M p x⟩) with hf
    change ((Rep.{u, u, u, u, u, u} X R L).functor.obj _).d (f.1 y) =
      (((Rep.{u, u, u, u, u, u} X R L).functor.obj _).d (f.1 y) -
        DifferentialGraded.gradedSign R p • f.1
          (((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)).d y)) +
      (p.negOnePow : ℤ) • f.1
        (((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)).d y)
    rw [← DifferentialGraded.intCast_negOnePow, Int.cast_smul_eq_zsmul]
    abel
  balance p q n x y a := by
    change homComp X R K L _ (tensorUnitₗ X R K M _) (y : _) =
      homComp X R K L _ (tensorUnitₗ X R K M x) _
    rw [tensorUnitₗ_smul, homComp_tensorUnitₗ]
    obtain ⟨c, hc, he⟩ := (Rep.{u, u, u, u, u, u} X R K).module_action _ p n (p + n) rfl
      ⟨_, tensorUnitₗ_mem X R K M p x⟩ a
    rw [← hc, homComp_of_mem X R K L _ _ c.property]
    change ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom _ (p + n) c)).1 (y : _) = _
    rw [he, (Rep.{u, u, u, u, u, u} X R L).functor.map_comp]
    rfl
  map_right x y b := homComp_smul_right X R K L _ (tensorUnitₗ X R K M x) y b

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- Composition is compatible with postcomposition by a homogeneous morphism `Y ⟶ Y'`:
`(g ∘ z) ∘ φ = g ∘ (z ∘ φ)`. -/
theorem homComp_map {Y Y' : (CompDG.{u, u, u, u, u, u} X R).Obj} {m : ℤ}
    (g : (CompDG.{u, u, u, u, u, u} X R).Hom Y Y' m)
    (z : ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).M)
    (φ : ((Rep.{u, u, u, u, u, u} X R L).functor.obj (liftComplex.{u, u, u, u, u} X K)).M) :
    homComp X R K L Y' (((Rep.{u, u, u, u, u, u} X R K).functor.map g).1 z) φ =
      ((Rep.{u, u, u, u, u, u} X R L).functor.map g).1 (homComp X R K L Y z φ) := by
  induction z using DirectSum.Decomposition.inductionOn
    ((Rep.{u, u, u, u, u, u} X R K).functor.obj Y).grading with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
  | @homogeneous p z =>
    obtain ⟨c, hc, he⟩ := (Rep.{u, u, u, u, u, u} X R K).map_comp Y Y' m p (m + p) rfl g z
    rw [← hc, homComp_of_mem X R K L _ _ c.property, homComp_of_mem X R K L _ _ z.property]
    change ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom Y' (m + p) c)).1 φ = _
    rw [he, (Rep.{u, u, u, u, u, u} X R L).functor.map_comp]
    rfl

/-! ### The comparison homomorphism -/

/-- **The comparison `M ⊗_A Hom(L, K) ⟶ Hom(L, M ⊗_A K)`**, `x ⊗ φ ↦ (x ⊗ -) ∘ φ`: the
homomorphism of differential graded `B`-modules induced by
`AlgebraicGeometry.RingedSite.tensorHomBalanced` through the universal property of the relative
tensor product (Tag 09LM). -/
def tensorHomComparison
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) :
    (DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).obj M ⟶
      (homWithComplexOver.{u, u, u, u, u, u} X R L).obj
        ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj M) :=
  ((DifferentialGraded.Bimodule.tensorDGFunctor (homBimodule X R K L)).universal M _
    (tensorHomBalanced X R K L M)).exists.choose

/-- The comparison on a pure tensor: `x ⊗ φ ↦ (x ⊗ -) ∘ φ`. -/
theorem tensorHomComparison_pure
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra)
    (x : M.M) (φ : (homBimodule X R K L).rightModule.M) :
    (tensorHomComparison X R K L M).toFun
        (((DifferentialGraded.Bimodule.tensorDGFunctor (homBimodule X R K L)).pure M).toLinearMap
          x φ) =
      homComp X R K L _ (tensorUnitₗ X R K M x) φ :=
  ((DifferentialGraded.Bimodule.tensorDGFunctor (homBimodule X R K L)).universal M _
    (tensorHomBalanced X R K L M)).exists.choose_spec x φ

/-- The unit of the tensor-Hom adjunction is natural in the module: `η_{M'} ∘ f = (F f)_* ∘ η_M`
for a homomorphism `f : M ⟶ M'`. -/
theorem tensorUnitₗ_naturality
    {M M' : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra}
    (f : M ⟶ M') (x : M.M) :
    tensorUnitₗ X R K M' (f.toFun x) =
      ((Rep.{u, u, u, u, u, u} X R K).functor.map
        ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map
          (cocycleOfHom _ f).1)).1 (tensorUnitₗ X R K M x) := by
  have h := congrArg (fun g => g.1.1 x)
    ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).adjunction.unit.naturality
      (show (show (dgCategory (Rep.{u, u, u, u, u, u} X R K).algebra).Comp from M) ⟶
        (show (dgCategory (Rep.{u, u, u, u, u, u} X R K).algebra).Comp from M') from
        cocycleOfHom _ f))
  exact h

/-- **The comparison is natural in the module.** -/
theorem tensorHomComparison_naturality
    {M M' : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra}
    (f : M ⟶ M') :
    (DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).map f ≫
        tensorHomComparison X R K L M' =
      tensorHomComparison X R K L M ≫
        (homWithComplexOver.{u, u, u, u, u, u} X R L).map
          ((dgFunctorToComplexes
            (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).map f) := by
  refine DifferentialGraded.Bimodule.tensorObj_hom_ext' _ M _ _ fun x φ => ?_
  change (tensorHomComparison X R K L M').toFun
      (((DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).map f).toFun _) =
    ((homWithComplexOver.{u, u, u, u, u, u} X R L).map _).toFun
      ((tensorHomComparison X R K L M).toFun _)
  rw [DifferentialGraded.Bimodule.tensorCompFunctor_map_pure', tensorHomComparison_pure,
    tensorHomComparison_pure, tensorUnitₗ_naturality, homComp_map]
  refine congrArg (fun c : (CompDG.{u, u, u, u, u, u} X R).Hom
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M)
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj M') 0 =>
    ((Rep.{u, u, u, u, u, u} X R L).functor.map c).1
      (homComp X R K L _ (tensorUnitₗ X R K M x) φ)) ?_
  exact (congrArg Subtype.val (Cocycle.ofHom_homOf_eq_self
    (Cocycle.mk ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map
      (cocycleOfHom _ f).1) 1 rfl
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map_cocycle
        (cocycleOfHom _ f))))).symm

end AlgebraicGeometry.RingedSite

end
