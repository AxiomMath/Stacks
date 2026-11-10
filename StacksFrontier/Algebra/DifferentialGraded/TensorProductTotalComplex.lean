module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.TensorProduct

/-!
# The tensor product of differential graded algebras is a total complex

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`. Forgetting
the multiplications, `A` and `B` are cochain complexes of `R`-modules, and so is their tensor
product `A ⊗_R B`. The degree-`n` part of `A ⊗_R B` is `⨁_{p + q = n} A^p ⊗_R B^q` and its
differential is `d_A ⊗ 1 + (-1)^p (1 ⊗ d_B)` on the summand `A^p ⊗_R B^q`, which is exactly the
differential of the total complex of the double complex `A^• ⊗_R B^•`. Hence
`(A ⊗_R B)^• = Tot(A^• ⊗_R B^•)` as cochain complexes of `R`-modules.

## Main definitions

* `DifferentialGradedAlgebra.toCochainComplex`: the cochain complex of `R`-modules underlying a
  differential graded algebra.
* `DifferentialGradedAlgebra.totSummandMap`: the map `A^p ⊗_R B^q → (A ⊗_R B)^{p+q}` of a
  summand of the total complex into the tensor product algebra.

## Main results

* `DifferentialGradedAlgebra.tensorToCochainComplexIso`: the identification
  `(A ⊗_R B)^• = Tot(A^• ⊗_R B^•)` of Tag 065X.
* `DifferentialGradedAlgebra.totSummandMap_tmul`: on homogeneous pure tensors the identification
  is `a ⊗ b ↦ a ⊗ b`, which is what makes it the canonical one.

## Implementation notes

The total complex is Mathlib's `HomologicalComplex.tensorObj`, the total complex of the double
complex obtained by tensoring two cochain complexes; its differential on the summand of
bidegree `(p, q)` is `ComplexShape.ε₁ • d₁ + ComplexShape.ε₂ • d₂` with `ε₁ = 1` and
`ε₂ (p, q) = (-1)^p` for the shape `ComplexShape.up ℤ`, so Mathlib's sign convention is the one
of Tag 065X.

The degreewise identification is the isomorphism
`DifferentialGradedAlgebra.componentEquiv` already used to decompose `A ⊗_R B` into its
homogeneous pieces, transported along the inclusions of the summands of the total complex; the
content of Tag 065X is that this family of isomorphisms commutes with the two differentials.

## References

* [Stacks Project, Tag 065X](https://stacks.math.columbia.edu/tag/065X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory DifferentialGradedModule
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra.{u, u} R)

/-- The cochain complex of `R`-modules underlying a differential graded algebra `(A, d)`: its
degree-`n` term is the homogeneous piece `A^n` and its differential is the restriction of `d`. -/
noncomputable abbrev toCochainComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (regularModule A).toCochainComplex

/-- The index set of the summands of the total complex in degree `n`: the pairs `(p, q)` of
integers with `p + q = n`. -/
abbrev TotIndex (n : ℤ) : Type := {pq : ℤ × ℤ // pq.1 + pq.2 = n}

/-- The summand `A^p ⊗_R B^q` of the total complex, as a family indexed by `TotIndex n`. -/
abbrev TotSummand (n : ℤ) (pq : TotIndex n) : Type u :=
  A.grading pq.val.1 ⊗[R] B.grading pq.val.2

/-- The map `A^p ⊗_R B^q → (A ⊗_R B)^n` sending `a ⊗ b` to the pure tensor `a ⊗ b`, for
`p + q = n`. It is the inclusion of a summand of the total complex of `A^• ⊗_R B^•` into the
degree-`n` part of the tensor product algebra. -/
noncomputable def totSummandMap (p q n : ℤ) (h : p + q = n) :
    (A.grading p ⊗[R] B.grading q) →ₗ[R] tensorProductGrading A B n :=
  (componentEquiv A B n).toLinearMap ∘ₗ
    DirectSum.lof R (TotIndex n) (TotSummand A B n) ⟨(p, q), h⟩

/-- The summand map is the component equivalence applied to the inclusion of a summand. -/
private lemma componentEquiv_lof_eq_totSummandMap (p q n : ℤ) (h : p + q = n)
    (t : A.grading p ⊗[R] B.grading q) :
    componentEquiv A B n (DirectSum.lof R (TotIndex n) (TotSummand A B n) ⟨(p, q), h⟩ t) =
      totSummandMap A B p q n h t := rfl

/-- On a pure tensor of homogeneous elements the summand map is `a ⊗ b ↦ a ⊗ b`. -/
@[stacks 065X "the identification on a homogeneous pure tensor"]
lemma totSummandMap_tmul (p q n : ℤ) (h : p + q = n)
    (a : A.grading p) (b : B.grading q) :
    ((totSummandMap A B p q n h (a ⊗ₜ[R] b) : tensorProductGrading A B n) :
      A.grading ᵍ⊗[R] B.grading) = (a : A.A) ᵍ⊗ₜ[R] (b : B.A) := by
  rw [← componentEquiv_lof_eq_totSummandMap, componentEquiv_coe, fiberMap_lof_tmul]

/-- The degreewise map from the total complex of `A^• ⊗_R B^•` to `(A ⊗_R B)^•`, assembled from
the summand maps. -/
noncomputable def totToTensor (n : ℤ) :
    (HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B)).X n ⟶
      (toCochainComplex (tensorProduct A B)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (fun p q (h : p + q = n) => ModuleCat.ofHom (totSummandMap A B p q n h))

/-- The degreewise map out of the total complex restricts to the summand map on the summand of
bidegree `(p, q)`. -/
lemma ι_totToTensor (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιMapBifunctor (toCochainComplex A) (toCochainComplex B)
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) p q n h ≫ totToTensor A B n =
      ModuleCat.ofHom (totSummandMap A B p q n h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ p q h

/-- The degreewise map from `(A ⊗_R B)^•` back to the total complex of `A^• ⊗_R B^•`. -/
noncomputable def tensorToTotLinear (n : ℤ) :
    tensorProductGrading A B n →ₗ[R]
      ↥((HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B)).X n) :=
  DirectSum.toModule R (TotIndex n)
      (↥((HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B)).X n))
      (fun pq : TotIndex n ↦ show TotSummand A B n pq →ₗ[R]
          ↥((HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B)).X n) from
        (HomologicalComplex.ιTensorObj (toCochainComplex A) (toCochainComplex B)
          pq.val.1 pq.val.2 n pq.property).hom) ∘ₗ
    (componentEquiv A B n).symm.toLinearMap

/-- The map back to the total complex sends the image of the summand of bidegree `(p, q)` into
that summand. -/
lemma tensorToTotLinear_totSummandMap (p q n : ℤ) (h : p + q = n)
    (t : A.grading p ⊗[R] B.grading q) :
    tensorToTotLinear A B n (totSummandMap A B p q n h t) =
      (HomologicalComplex.ιTensorObj (toCochainComplex A) (toCochainComplex B) p q n h).hom t := by
  rw [tensorToTotLinear, ← componentEquiv_lof_eq_totSummandMap]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact DirectSum.toModule_lof (R := R) (ι := TotIndex n) (M := TotSummand A B n) ⟨(p, q), h⟩ t

/-- The degreewise map from `(A ⊗_R B)^•` back to the total complex, as a morphism of
`R`-modules. -/
noncomputable def tensorToTot (n : ℤ) :
    (toCochainComplex (tensorProduct A B)).X n ⟶
      (HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B)).X n :=
  ModuleCat.ofHom (tensorToTotLinear A B n)

/-- Going from the total complex to `A ⊗_R B` and back is the identity. -/
lemma totToTensor_tensorToTot (n : ℤ) :
    totToTensor A B n ≫ tensorToTot A B n = 𝟙 _ := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h ↦ ?_
  rw [Category.comp_id, ← Category.assoc, ι_totToTensor]
  ext t
  exact tensorToTotLinear_totSummandMap A B p q n h t

/-- The round trip through the total complex is the identity on each homogeneous piece of
`A ⊗_R B`, written on the direct-sum decomposition of that piece. -/
private lemma roundTrip_eq (n : ℤ) :
    (totToTensor A B n).hom ∘ₗ (tensorToTotLinear A B n ∘ₗ
        (componentEquiv A B n).toLinearMap) =
      (componentEquiv A B n).toLinearMap := by
  refine DirectSum.linearMap_ext R fun ⟨⟨p, q⟩, h⟩ ↦ LinearMap.ext fun t ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [componentEquiv_lof_eq_totSummandMap, tensorToTotLinear_totSummandMap]
  exact congrFun (congrArg (fun f : _ ⟶ _ ↦ (ModuleCat.Hom.hom f).toFun)
    (ι_totToTensor A B p q n h)) t

/-- Going from `A ⊗_R B` to the total complex and back is the identity. -/
lemma tensorToTot_totToTensor (n : ℤ) :
    tensorToTot A B n ≫ totToTensor A B n = 𝟙 _ := by
  ext x
  obtain ⟨y, rfl⟩ := (componentEquiv A B n).surjective x
  exact LinearMap.congr_fun (roundTrip_eq A B n) y

/-- The degreewise identification `Tot(A^• ⊗_R B^•)^n ≅ (A ⊗_R B)^n`. -/
noncomputable def totToTensorIso (n : ℤ) :
    (HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B)).X n ≅
      (toCochainComplex (tensorProduct A B)).X n where
  hom := totToTensor A B n
  inv := tensorToTot A B n
  hom_inv_id := totToTensor_tensorToTot A B n
  inv_hom_id := tensorToTot_totToTensor A B n

/-- The degreewise identification commutes with the differentials: the differential of the total
complex is `d_A ⊗ 1 + (-1)^p (1 ⊗ d_B)` on the summand of bidegree `(p, q)`, which is the
differential of `A ⊗_R B`. -/
lemma totToTensor_comm (n : ℤ) :
    (HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B)).d n (n + 1) ≫
        totToTensor A B (n + 1) =
      totToTensor A B n ≫ (toCochainComplex (tensorProduct A B)).d n (n + 1) := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h ↦ ?_
  conv_rhs => rw [← Category.assoc, ι_totToTensor]
  conv_lhs => rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have h0 : p + q = n := h
  have h1 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p + 1, q)
      = n + 1 := show p + 1 + q = n + 1 by omega
  have h2 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q + 1)
      = n + 1 := show p + (q + 1) = n + 1 by omega
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (n + 1) h1,
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (n + 1) h2]
  simp only [Linear.units_smul_comp, Category.assoc, ι_totToTensor,
    ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, one_smul]
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' (fun (a : A.grading p) (b : B.grading q) => ?_)
  simp only [DifferentialGradedModule.toCochainComplex_d]
  have hA : A.d (a : A.A) ∈ A.grading (p + 1) := A.d_mem p a a.property
  have hB : B.d (b : B.A) ∈ B.grading (q + 1) := B.d_mem q b b.property
  change (totSummandMap A B (p + 1) q (n + 1) h1
          ((⟨A.d (a : A.A), hA⟩ : A.grading (p + 1)) ⊗ₜ[R] b)
        + p.negOnePow • totSummandMap A B p (q + 1) (n + 1) h2
          (a ⊗ₜ[R] (⟨B.d (b : B.A), hB⟩ : B.grading (q + 1))))
      = (regularModule (tensorProduct A B)).gradedDifferential n
          (totSummandMap A B p q n h (a ⊗ₜ[R] b))
  refine Subtype.ext ?_
  rw [Submodule.coe_add, Units.smul_def, Submodule.coe_smul_of_tower,
    totSummandMap_tmul A B (p + 1) q (n + 1) h1 ⟨A.d (a : A.A), hA⟩ b,
    totSummandMap_tmul A B p (q + 1) (n + 1) h2 a ⟨B.d (b : B.A), hB⟩,
    DifferentialGradedModule.gradedDifferential_apply,
    totSummandMap_tmul A B p q n h a b]
  exact (tensorProductDifferential_tmul A B p a (b : B.A)).symm

/-- **Stacks Tag 065X.** For differential graded algebras `(A, d)` and `(B, d)` over a
commutative ring `R`, the cochain complex of `R`-modules underlying `A ⊗_R B` is the total
complex of the double complex `A^• ⊗_R B^•`. -/
@[stacks 065X]
noncomputable def tensorToCochainComplexIso :
    toCochainComplex (tensorProduct A B) ≅
      HomologicalComplex.tensorObj (toCochainComplex A) (toCochainComplex B) :=
  (HomologicalComplex.Hom.isoOfComponents (totToTensorIso A B)
    (fun i j (hij : i + 1 = j) => by
      obtain rfl : j = i + 1 := hij.symm
      exact (totToTensor_comm A B i).symm)).symm

end DifferentialGradedAlgebra

end
