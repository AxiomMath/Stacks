module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEndAlgebra
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.Algebra.DGA.CentralAction

/-!
# Beilinson's equivalence is `A`-linear

Let `A` be a ring, `X = P^n_A = Proj A[T₀, …, Tₙ]`, `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` and
`R = Hom_{𝒪_X}(P, P)` ([Stacks, Equation 0CS9]). As in the source, `R = Hom_{Comp^dg(𝒪_X)}(P, P)`
for `P` placed in degree zero, read as a differential graded algebra with zero differential
concentrated in degree zero, and `D(R)` is the derived category of differential graded `R`-modules
of Tag 09LX: here `R` is `Stacks.AlgebraicGeometry.Beilinson.endAlgebra`, whose differential
vanishes (`Stacks.AlgebraicGeometry.Beilinson.endAlgebra_d_eq_zero`), which has no nonzero elements
outside degree zero (`Stacks.AlgebraicGeometry.Beilinson.endAlgebra_grading_eq_bot`), and whose
ring is `End P = Hom_{𝒪_X}(P, P)` (`Stacks.AlgebraicGeometry.Beilinson.endAlgebraRingEquiv`).

This file proves [Stacks, Tag 0BQU]: `- ⊗_R^𝐋 P : D(R) ⥤ D_QCoh(𝒪_X)` is an `A`-linear
equivalence of triangulated categories sending `R` to `P`.

The `A`-linear structures are the natural ones. On `D_QCoh(𝒪_X)` a scalar `a` acts through
`A → Γ(X, 𝒪_X)` (`AlgebraicGeometry.modulesLinear`). The element `a · 1` of `R` is central, of
degree zero and closed, so right multiplication by it is an endomorphism of every differential
graded `R`-module; this is the action of `A ⊂ center(R)` on `D(R)`
(`DifferentialGradedModule.derivedLinearOfCentral`).

## Main definitions

* `Stacks.AlgebraicGeometry.Beilinson.scalarRingHom`: `A → R`, `a ↦ a · 1`.
* `Stacks.AlgebraicGeometry.Beilinson.derivedCategoryRLinear`: the `A`-linear structure of `D(R)`.
* `Stacks.AlgebraicGeometry.Beilinson.quasiCoherentDerivedCategoryLinear`: the `A`-linear
  structure of `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.AlgebraicGeometry.Beilinson.tensorWithGenerator_linear`: `- ⊗_R^𝐋 P` is `A`-linear.
* `Stacks.AlgebraicGeometry.Beilinson.beilinson_equivalence`: [Stacks, Tag 0BQU].

## References

* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex.HomComplex
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ExampleGenerator (twistSumModule twistSumQCoh)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

namespace Stacks.AlgebraicGeometry.Beilinson

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The `A`-linear structure of the ambient category of `𝒪_X`-modules of Tag 09LX: a scalar acts
through `A → Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def tensorModOLinear : Linear A (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) :=
  AlgebraicGeometry.modulesLinear A (Over.mk (projToSpecCoeff A n))

/-- The `A`-linear structure of `X.Modules`: a scalar acts through `A → Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def projectiveSpaceModulesLinear : Linear A (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  AlgebraicGeometry.modulesLinear A (Over.mk (projToSpecCoeff A n))

attribute [local instance] tensorModOLinear projectiveSpaceModulesLinear

/-- **The `A`-linear structure of `D_QCoh(𝒪_X)`**: a scalar `a` acts through `A → Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def quasiCoherentDerivedCategoryLinear :
    Linear A
      (Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n))) :=
  inferInstance

/-! ### The central elements `a · 1` of `R` -/

/-- The element `a · 1` of `R = Hom^dg(P, P)`, as a homogeneous element of degree zero. -/
def scalarHom (a : A) : (endAlgebra A n).grading 0 :=
  ((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0).symm
    (a • Cochain.ofHom (𝟙 (liftedGenerator A n)) :
      Cochain (liftedGenerator A n) (liftedGenerator A n) 0)

/-- Under the identification of `R` in degree zero with degree-zero cochains, `scalarHom A n a`
is the cochain `a • 𝟙`. -/
theorem algebraHom_scalarHom (a : A) :
    ((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0
      (scalarHom A n a) : Cochain (liftedGenerator A n) (liftedGenerator A n) 0) =
      a • Cochain.ofHom (𝟙 (liftedGenerator A n)) :=
  LinearEquiv.apply_symm_apply _ _

/-- `a • 𝟙` as a cochain of degree zero. -/
theorem ofHom_smul_id (a : A)
    (P : CochainComplex (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) ℤ) :
    Cochain.ofHom (a • 𝟙 P) = a • Cochain.ofHom (𝟙 P) :=
  Cochain.ext₀ _ _ fun p => by
    rw [Cochain.ofHom_v, Cochain.smul_v, Cochain.ofHom_v, HomologicalComplex.smul_f_apply]

/-- **`A → R`, `a ↦ a · 1`.** -/
def scalarRingHom : A →+* (endAlgebra A n).A where
  toFun a := (scalarHom A n a).1
  map_one' := by
    obtain ⟨e, he1, he⟩ :=
      (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebra_one
    have h : scalarHom A n 1 = e :=
      ((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0).injective
        (by
          rw [algebraHom_scalarHom, he, one_smul]
          rfl)
    rw [h, he1]
  map_mul' a b := by
    obtain ⟨d, hd1, hd⟩ :=
      (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebra_mul 0 0 0
        (add_zero 0) (scalarHom A n a) (scalarHom A n b)
    have h : scalarHom A n (a * b) = d :=
      ((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0).injective (by
        rw [algebraHom_scalarHom, hd]
        change _ = Cochain.comp
          ((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0
            (scalarHom A n b) : Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
          ((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0
            (scalarHom A n a) : Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
          (add_zero 0)
        rw [algebraHom_scalarHom, algebraHom_scalarHom, Cochain.smul_comp, Cochain.comp_smul,
          Cochain.comp_id, smul_smul, mul_comm])
    rw [h, hd1]
  map_zero' := by
    change (((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0).symm
      ((0 : A) • Cochain.ofHom (𝟙 (liftedGenerator A n)) :
        Cochain (liftedGenerator A n) (liftedGenerator A n) 0)).1 = 0
    rw [zero_smul, map_zero]
    rfl
  map_add' a b := by
    change (((RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).algebraHom 0).symm
      ((a + b) • Cochain.ofHom (𝟙 (liftedGenerator A n)) :
        Cochain (liftedGenerator A n) (liftedGenerator A n) 0)).1 = (scalarHom A n a).1 +
          (scalarHom A n b).1
    rw [add_smul, map_add]
    rfl

/-- **`a · 1` is central in `R`, of degree zero and closed.** -/
theorem isCentralCocycle_scalarRingHom (a : A) :
    DifferentialGradedModule.IsCentralCocycle (scalarRingHom A n a) where
  comm b := by
    let H := RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)
    let b' : (endAlgebra A n).grading 0 := ⟨b, endAlgebra_mem_grading_zero A n b⟩
    obtain ⟨d₁, h₁, h₁'⟩ := H.algebra_mul 0 0 0 (add_zero 0) (scalarHom A n a) b'
    obtain ⟨d₂, h₂, h₂'⟩ := H.algebra_mul 0 0 0 (add_zero 0) b' (scalarHom A n a)
    have h : d₁ = d₂ := (H.algebraHom 0).injective (by
      rw [h₁', h₂']
      change Cochain.comp
          (H.algebraHom 0 b' : Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
          (H.algebraHom 0 (scalarHom A n a) :
            Cochain (liftedGenerator A n) (liftedGenerator A n) 0) (add_zero 0) =
        Cochain.comp (H.algebraHom 0 (scalarHom A n a) :
            Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
          (H.algebraHom 0 b' : Cochain (liftedGenerator A n) (liftedGenerator A n) 0) (add_zero 0)
      rw [algebraHom_scalarHom, Cochain.comp_smul, Cochain.comp_id, Cochain.smul_comp,
        Cochain.id_comp])
    change (scalarHom A n a).1 * b = b * (scalarHom A n a).1
    rw [← h₁, ← h₂, h]
  mem := (scalarHom A n a).2
  d_eq := by
    rw [endAlgebra_d_eq_zero]
    rfl

/-- **The `A`-linear structure of `D(R)`**: `a ∈ A` acts on a differential graded `R`-module by
right multiplication by the central element `a · 1` of `R`, that is, through `A ⊂ center(R)`. -/
@[instance_reducible]
def derivedCategoryRLinear : Linear A (derivedCategoryR A n) :=
  DifferentialGradedModule.derivedLinearOfCentral (scalarRingHom A n)
    (isCentralCocycle_scalarRingHom A n)

/-! ### `- ⊗_R P` carries `a · 1` to `a` -/

/-- `Hom^•(P, -)` carries `a` to right multiplication by `a · 1`. -/
theorem homWithComplex_map_smul_id (a : A)
    (Q : CochainComplex (RingedSite.TensorModO.{u, u, u, u, u} (site A n)) ℤ) :
    (RingedSite.homWithComplex.{u, u, u, u, u} (site A n) (generator A n)).map (a • 𝟙 Q) =
      DifferentialGradedModule.centralSMul (isCentralCocycle_scalarRingHom A n a) _ := by
  let H := RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)
  let M := (RingedSite.homWithComplex.{u, u, u, u, u} (site A n) (generator A n)).obj Q
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
  refine DirectSum.Decomposition.inductionOn M.grading (by rw [map_zero, map_zero])
    (fun {i} y => ?_) (fun y y' hy hy' => by rw [map_add, map_add, hy, hy']) x
  obtain ⟨c₁, hc₁, hc₁'⟩ := H.map_comp Q Q 0 i i (zero_add i) (Cochain.ofHom (a • 𝟙 Q)) y
  obtain ⟨c₂, hc₂, hc₂'⟩ := H.module_action Q i 0 i (add_zero i) y (scalarHom A n a)
  have h : c₁ = c₂ := (H.moduleHom Q i).injective (by
    rw [hc₁', hc₂']
    change Cochain.comp (H.moduleHom Q i y : Cochain (liftedGenerator A n) Q i)
        (Cochain.ofHom (a • 𝟙 Q)) (add_zero i) =
      Cochain.comp (H.algebraHom 0 (scalarHom A n a) :
          Cochain (liftedGenerator A n) (liftedGenerator A n) 0)
        (H.moduleHom Q i y : Cochain (liftedGenerator A n) Q i) (zero_add i)
    rw [algebraHom_scalarHom, ofHom_smul_id, Cochain.comp_smul, Cochain.comp_id,
      Cochain.smul_comp, Cochain.id_comp])
  change (H.functor.map (Cochain.ofHom (a • 𝟙 Q))).1 y.1 =
    MulOpposite.op (scalarHom A n a).1 • y.1
  exact hc₁.symm.trans ((congrArg Subtype.val h).trans hc₂)

/-- A linear functor carries `a • 𝟙 X` to `a • 𝟙 (F.obj X)`. -/
private theorem map_smul_id {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear A C] [Linear A D]
    (F : C ⥤ D) [F.Additive] [F.Linear A] (a : A) (X : C) :
    F.map (a • 𝟙 X) = a • 𝟙 (F.obj X) := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- **Tensoring with `P` carries right multiplication by `a · 1` to `a`**, on complexes. -/
theorem tensorWithComplex_map_centralSMul (a : A)
    (M : DifferentialGradedModule (RingedSite.Rep.{u, u, u, u, u, 0} (site A n) ℤ
      (generator A n)).algebra) :
    (DifferentialGradedModule.dgFunctorToComplexes
        (RingedSite.tensorWithComplexDG.{u, u, u, u, u, 0} (site A n) ℤ
          (generator A n)).functor).map
      (DifferentialGradedModule.centralSMul (isCentralCocycle_scalarRingHom A n a) M) =
      a • 𝟙 _ := by
  let adj := RingedSite.tensorWithComplexComplexes_adj_homWithComplex.{u, u, u, u, u} (site A n)
    (generator A n)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, homWithComplex_map_smul_id]
  have h := adj.unit.naturality
    (DifferentialGradedModule.centralSMul (isCentralCocycle_scalarRingHom A n a) M)
  have h' := (DifferentialGradedModule.centralSMulCenter
    (isCentralCocycle_scalarRingHom A n a)).naturality (adj.unit.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
    DifferentialGradedModule.centralSMulCenter_app] at h h'
  rw [← h]
  exact h'.symm

/-- **Tensoring with `P` carries `a · 1` to `a`**, from the homotopy category of differential
graded `R`-modules to `D(𝒪_X)`. -/
theorem tensorWithComplexToDerivedCategory_map_center (a : A)
    (Y : DifferentialGradedModule.HomotopyCategory (endAlgebra A n)) :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    (RingedSite.tensorWithComplexToDerivedCategory.{u, u, u, u, u, 0} (site A n) ℤ
        (generator A n)).map
      ((DifferentialGradedModule.homotopyCenterRingHom (scalarRingHom A n)
        (isCentralCocycle_scalarRingHom A n) a).app Y) =
      (Linear.toCatCenter A _ a).app _ := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  obtain ⟨M⟩ := Y
  change DerivedCategory.Qh.map ((RingedSite.tensorWithComplexHomotopy.{u, u, u, u, u, 0}
      (site A n) ℤ (generator A n)).map ((DifferentialGradedModule.toHomotopyCategory _).map
        (DifferentialGradedModule.centralSMul (isCentralCocycle_scalarRingHom A n a) M))) =
    a • 𝟙 _
  rw [RingedSite.tensorWithComplexHomotopy_map, tensorWithComplex_map_centralSMul]
  rw [map_smul_id]
  exact map_smul_id A _ _ _

/-- **`- ⊗_R^𝐋 P` carries `a · 1` to `a`.** -/
theorem tensorWithComplexDerived_map_center (a : A) (Y : derivedCategoryR A n) :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    (RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).map
      ((DifferentialGradedModule.derivedCenterRingHom (scalarRingHom A n)
        (isCentralCocycle_scalarRingHom A n) a).app Y) = a • 𝟙 _ := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  exact CatCenter.map_localization_app_of_isLeftDerivedFunctor _
    (RingedSite.tensorWithComplexDerivedCounit.{u, u, u, u, u, 0} (site A n) ℤ (generator A n))
    (DifferentialGradedModule.quasiIsomorphisms _) _ (Linear.toCatCenter A _ a)
    (tensorWithComplexToDerivedCategory_map_center A n a) Y

/-- **`- ⊗_R^𝐋 P` is `A`-linear**, before restriction to `D_QCoh(𝒪_X)`. -/
theorem tensorWithComplexDerived_linear :
    letI := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
    letI := derivedCategoryRLinear A n
    (RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ
      (generator A n)).Linear A := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  let := derivedCategoryRLinear A n
  rw [Functor.linear_iff]
  intro Y a
  change (RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).map
    ((DifferentialGradedModule.derivedCenterRingHom (scalarRingHom A n)
      (isCentralCocycle_scalarRingHom A n) a).app Y ≫ 𝟙 Y) = _
  rw [Category.comp_id]
  exact tensorWithComplexDerived_map_center A n a Y

/-- **`- ⊗_R^𝐋 P : D(R) ⥤ D_QCoh(𝒪_X)` is `A`-linear**, for the action of `A ⊂ center(R)` on
`D(R)` (`Stacks.AlgebraicGeometry.Beilinson.derivedCategoryRLinear`) and the action of `A` through
`Γ(X, 𝒪_X)` on `D_QCoh(𝒪_X)`
(`Stacks.AlgebraicGeometry.Beilinson.quasiCoherentDerivedCategoryLinear`). -/
theorem tensorWithGenerator_linear :
    letI := derivedCategoryRLinear A n
    letI := quasiCoherentDerivedCategoryLinear A n
    (tensorWithGenerator A n).Linear A := by
  let := HasDerivedCategory.standard (RingedSite.TensorModO.{u, u, u, u, u} (site A n))
  let := derivedCategoryRLinear A n
  have hF := tensorWithComplexDerived_linear A n
  have : (modulesEquivalence A n).functor.Linear A := ⟨fun _ _ => rfl⟩
  have hΨ : (modelEquivalence A n).functor.Linear A :=
    (inferInstance : (modulesEquivalence A n).functor.mapDerivedCategory.Linear A)
  rw [Functor.linear_iff]
  intro Y a
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  change (modelEquivalence A n).functor.map ((CategoryTheory.signTwist _).map
    ((RingedSite.tensorWithComplexDerived.{u, u, u, u, u, 0} (site A n) ℤ (generator A n)).map
      (a • 𝟙 Y))) = a • 𝟙 _
  rw [CategoryTheory.signTwist_map, map_smul_id]
  exact map_smul_id A _ _ _

/-- **[Stacks, Tag 0BQU] (Beilinson).** Let `A` be a ring, `X = P^n_A = Proj A[T₀, …, Tₙ]`,
`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` and `R = Hom_{𝒪_X}(P, P)`, read as in the source as the
differential graded algebra `Hom_{Comp^dg(𝒪_X)}(P, P)` with zero differential. Then
`- ⊗_R^𝐋 P : D(R) ⥤ D_QCoh(𝒪_X)` is an `A`-linear equivalence of triangulated categories sending
`R` to `P`. -/
@[stacks 0BQU]
theorem beilinson_equivalence :
    (tensorWithGenerator A n).IsEquivalence ∧ (tensorWithGenerator A n).IsTriangulated ∧
      Nonempty ((tensorWithGenerator A n).obj (regular A n) ≅ twistSumQCoh A n) ∧
      letI := derivedCategoryRLinear A n
      letI := quasiCoherentDerivedCategoryLinear A n
      (tensorWithGenerator A n).Linear A :=
  ⟨tensorWithGenerator_isEquivalence A n, tensorWithGenerator_isTriangulated A n,
    ⟨tensorWithGeneratorObjRegularIso A n⟩, tensorWithGenerator_linear A n⟩

end Stacks.AlgebraicGeometry.Beilinson
