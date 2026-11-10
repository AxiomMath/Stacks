module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.RelativeLinearAction

/-!
# A family of linear automorphisms of a projective space, and its fibres

Let `k` be a commutative ring, `R` a `k`-algebra and `V` a `k`-module. An invertible
`R`-linear endomorphism `G` of `R ⊗_k V` is a family of linear automorphisms of `𝐏(V)`
parametrised by `Spec R`: it acts on `𝐏_R(R ⊗_k V) = Spec R ×_k 𝐏(V)` by an automorphism over
`Spec R`, `AlgebraicGeometry.ProjectiveSpaceOfModule.map`. This file computes the fibres of that
automorphism over the `k`-points of `Spec R`.

A `k`-point is a `k`-algebra homomorphism `λ : R → k`. It specialises `G` to the `k`-linear
endomorphism `G(λ)` of `V`, `v ↦ (λ ⊗ id)(G(1 ⊗ v))`, and it gives a section
`σ_λ : 𝐏(V) ⟶ 𝐏_R(R ⊗_k V)` of the base-change morphism to `𝐏(V)` lying over `λ`, namely `Proj`
of the graded homomorphism `Sym_R(R ⊗_k V) = R ⊗_k Sym_k(V) → Sym_k(V)` given by `λ ⊗ id`. The
result is

`σ_λ ≫ map G = map G(λ) ≫ σ_λ`,

that is, the fibre over `λ` of the family of automorphisms is the automorphism of `𝐏(V)` given by
the specialised linear map.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.specializeEnd`: the specialisation `G(λ)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.specializeGL`: the same as a homomorphism of groups
  of invertible maps.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSection`: the section `σ_λ`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSection_comp_baseChangeMap`: `σ_λ` is a section
  of the base-change morphism `𝐏_R(R ⊗_k V) ⟶ 𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSection_comp_toSpec`: `σ_λ` lies over the point
  `λ` of `Spec R`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSection_comp_map`: **the fibre of the family
  `map G` over `λ` is `map G(λ)`.**

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

variable {k : Type u} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {V : Type u} [AddCommGroup V] [Module k V]

/-! ### Specialising a linear map at a point -/

/-- **Evaluation of `R ⊗_k V` at a `k`-point `λ` of `R`**, the `k`-linear map
`r ⊗ v ↦ λ(r) v`. -/
public def evalTensor (lam : R →ₐ[k] k) : R ⊗[k] V →ₗ[k] V :=
  TensorProduct.lid k V ∘ₗ LinearMap.rTensor V lam.toLinearMap

/-- Evaluation at `λ` sends a pure tensor `r ⊗ v` to `λ(r) • v`. -/
@[simp]
public theorem evalTensor_tmul (lam : R →ₐ[k] k) (r : R) (v : V) :
    evalTensor lam (r ⊗ₜ[k] v) = lam r • v := by
  simp [evalTensor]

/-- Evaluation at a point is semilinear over the point. -/
public theorem evalTensor_smul (lam : R →ₐ[k] k) (r : R) (x : R ⊗[k] V) :
    evalTensor lam (r • x) = lam r • evalTensor lam x := by
  induction x with
  | tmul s v =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp only [evalTensor_tmul, _root_.map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **The specialisation of an `R`-linear endomorphism of `R ⊗_k V` at a `k`-point `λ`**: the
`k`-linear endomorphism `v ↦ (λ ⊗ id)(G(1 ⊗ v))` of `V`. -/
public def specializeEnd (lam : R →ₐ[k] k) (G : R ⊗[k] V →ₗ[R] R ⊗[k] V) : V →ₗ[k] V :=
  evalTensor lam ∘ₗ (G.restrictScalars k) ∘ₗ TensorProduct.mk k R V 1

/-- The specialisation `G(λ)` sends `v` to the evaluation at `λ` of `G(1 ⊗ v)`. -/
public theorem specializeEnd_apply (lam : R →ₐ[k] k) (G : R ⊗[k] V →ₗ[R] R ⊗[k] V) (v : V) :
    specializeEnd lam G v = evalTensor lam (G (1 ⊗ₜ[k] v)) := rfl

/-- Evaluating after applying `G` is applying the specialisation after evaluating. -/
public theorem evalTensor_apply_map (lam : R →ₐ[k] k) (G : R ⊗[k] V →ₗ[R] R ⊗[k] V)
    (x : R ⊗[k] V) : evalTensor lam (G x) = specializeEnd lam G (evalTensor lam x) := by
  induction x with
  | tmul r v =>
    have h : r ⊗ₜ[k] v = r • ((1 : R) ⊗ₜ[k] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, evalTensor_smul, evalTensor_smul, map_smul, specializeEnd_apply,
      evalTensor_tmul, _root_.map_one, one_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The specialisation of the identity is the identity. -/
@[simp]
public theorem specializeEnd_id (lam : R →ₐ[k] k) :
    specializeEnd lam (LinearMap.id : R ⊗[k] V →ₗ[R] R ⊗[k] V) = LinearMap.id := by
  ext v
  simp [specializeEnd_apply]

/-- Specialisation at a point is multiplicative: `(G ∘ H)(λ) = G(λ) ∘ H(λ)`. -/
public theorem specializeEnd_comp (lam : R →ₐ[k] k) (G H : R ⊗[k] V →ₗ[R] R ⊗[k] V) :
    specializeEnd lam (G ∘ₗ H) = specializeEnd lam G ∘ₗ specializeEnd lam H := by
  ext v
  rw [LinearMap.comp_apply, specializeEnd_apply, specializeEnd_apply, LinearMap.comp_apply,
    evalTensor_apply_map]
  rfl

/-- Specialisation at a point is additive: `(G + H)(λ) = G(λ) + H(λ)`. -/
public theorem specializeEnd_add (lam : R →ₐ[k] k) (G H : R ⊗[k] V →ₗ[R] R ⊗[k] V) :
    specializeEnd lam (G + H) = specializeEnd lam G + specializeEnd lam H := by
  ext v
  simp [specializeEnd_apply]

/-- Specialisation at a point is semilinear over the point: `(r • G)(λ) = λ(r) • G(λ)`. -/
public theorem specializeEnd_smul (lam : R →ₐ[k] k) (r : R) (G : R ⊗[k] V →ₗ[R] R ⊗[k] V) :
    specializeEnd lam (r • G) = lam r • specializeEnd lam G := by
  ext v
  simp [specializeEnd_apply, evalTensor_smul]

/-- The specialisation of a base-changed endomorphism is the endomorphism itself. -/
@[simp]
public theorem specializeEnd_baseChange (lam : R →ₐ[k] k) (E : V →ₗ[k] V) :
    specializeEnd lam (E.baseChange R) = E := by
  ext v
  simp [specializeEnd_apply]

/-- **Specialisation at a point, as a homomorphism of groups of invertible linear maps.** -/
public def specializeGL (lam : R →ₐ[k] k) :
    LinearMap.GeneralLinearGroup R (R ⊗[k] V) →* LinearMap.GeneralLinearGroup k V :=
  Units.map
    { toFun := specializeEnd lam
      map_one' := specializeEnd_id lam
      map_mul' := specializeEnd_comp lam }

/-- The underlying linear map of `specializeGL λ G` is the specialisation of `G` at `λ`. -/
@[simp]
public theorem coe_specializeGL (lam : R →ₐ[k] k)
    (G : LinearMap.GeneralLinearGroup R (R ⊗[k] V)) :
    ((specializeGL lam G : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) =
      specializeEnd lam (G : R ⊗[k] V →ₗ[R] R ⊗[k] V) := rfl

/-! ### The section of the base change at a point -/

/-- Evaluation of `R ⊗_k Sym_k(V)` at a `k`-point of `R`, `r ⊗ x ↦ λ(r) x`. -/
public def tensorEval (lam : R →ₐ[k] k) :
    R ⊗[k] SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V :=
  Algebra.TensorProduct.lift ((Algebra.ofId k (SymmetricAlgebra k V)).comp lam)
    (AlgHom.id k _) fun _ _ => Commute.all _ _

/-- Evaluation at `λ` sends a pure tensor `r ⊗ x` to `λ(r) * x`. -/
@[simp]
public theorem tensorEval_tmul (lam : R →ₐ[k] k) (r : R) (x : SymmetricAlgebra k V) :
    tensorEval lam (r ⊗ₜ[k] x) = algebraMap k (SymmetricAlgebra k V) (lam r) * x := by
  simp [tensorEval]

/-- **Evaluation of `Sym_R(R ⊗_k V)` at a `k`-point `λ` of `R`**, as a ring homomorphism to
`Sym_k(V)`: the base-change comparison `Sym_R(R ⊗_k V) ≅ R ⊗_k Sym_k(V)` followed by `λ ⊗ id`. -/
public def symEval (lam : R →ₐ[k] k) : SymmetricAlgebra R (R ⊗[k] V) →+* SymmetricAlgebra k V :=
  (tensorEval lam).toRingHom.comp (SymPow.symAlgBaseChangeEquiv (A := k) R V).symm.toRingHom

/-- `symEval λ` is the inverse base-change comparison followed by `tensorEval λ`. -/
public theorem symEval_apply (lam : R →ₐ[k] k) (x : SymmetricAlgebra R (R ⊗[k] V)) :
    symEval lam x = tensorEval lam ((SymPow.symAlgBaseChangeEquiv (A := k) R V).symm x) := rfl

/-- The inverse base-change comparison on a degree-one generator. -/
public theorem symAlgBaseChangeEquiv_symm_ι (x : R ⊗[k] V) :
    (SymPow.symAlgBaseChangeEquiv (A := k) R V).symm (SymmetricAlgebra.ι R (R ⊗[k] V) x) =
      LinearMap.baseChange R (SymmetricAlgebra.ι k V) x := by
  rw [AlgEquiv.symm_apply_eq]
  induction x with
  | tmul r v =>
    rw [LinearMap.baseChange_tmul, SymPow.symAlgBaseChangeEquiv_apply,
      SymPow.symAlgBaseChangeHom_tmul, SymmetricAlgebra.lift_ι_apply,
      SymPow.toSymBaseChange_apply, ← Algebra.smul_def, ← map_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- Evaluation of `R ⊗_k Sym_k(V)` on the image of `R ⊗_k V`. -/
public theorem tensorEval_baseChange_ι (lam : R →ₐ[k] k) (x : R ⊗[k] V) :
    tensorEval lam (LinearMap.baseChange R (SymmetricAlgebra.ι k V) x) =
      SymmetricAlgebra.ι k V (evalTensor lam x) := by
  induction x with
  | tmul r v =>
    rw [LinearMap.baseChange_tmul, tensorEval_tmul, evalTensor_tmul, map_smul,
      Algebra.smul_def]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The evaluation of a degree-one generator `ι(x)` is `ι` of the evaluation of `x`. -/
public theorem symEval_ι (lam : R →ₐ[k] k) (x : R ⊗[k] V) :
    symEval lam (SymmetricAlgebra.ι R (R ⊗[k] V) x) =
      SymmetricAlgebra.ι k V (evalTensor lam x) := by
  rw [symEval_apply, symAlgBaseChangeEquiv_symm_ι, tensorEval_baseChange_ι]

/-- The evaluation of a scalar `r` is the scalar `λ(r)`. -/
public theorem symEval_algebraMap (lam : R →ₐ[k] k) (r : R) :
    symEval lam (algebraMap R (SymmetricAlgebra R (R ⊗[k] V)) r) =
      algebraMap k (SymmetricAlgebra k V) (lam r) := by
  rw [symEval_apply, AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply,
    tensorEval_tmul, Algebra.algebraMap_self, RingHom.id_apply, mul_one]

/-- The evaluation undoes the inclusion `x ↦ 1 ⊗ x` of `Sym_k(V)`. -/
public theorem symEval_symBaseChangeGraded (lam : R →ₐ[k] k) (x : SymmetricAlgebra k V) :
    symEval lam (Stacks.ProjectiveSpaceBaseChange.symBaseChangeGraded k R V x) = x := by
  change tensorEval lam ((SymPow.symAlgBaseChangeEquiv (A := k) R V).symm
    (SymPow.symAlgBaseChangeEquiv (A := k) R V ((1 : R) ⊗ₜ[k] x))) = x
  rw [AlgEquiv.symm_apply_apply, tensorEval_tmul, _root_.map_one, _root_.map_one, one_mul]

/-- The evaluation carries the degree-`n` symmetric power into the degree-`n` symmetric
power. -/
public theorem symEval_mem (lam : R →ₐ[k] k) {n : ℕ} {x : SymmetricAlgebra R (R ⊗[k] V)}
    (hx : x ∈ SymPow.symmetricPower n R (R ⊗[k] V)) :
    symEval lam x ∈ SymPow.symmetricPower n k V := by
  have hy := (Stacks.ProjectiveSpaceBaseChange.symBaseChangeGradedInv k R V).map_mem hx
  change (SymPow.symAlgBaseChangeEquiv (A := k) R V).symm x ∈ _ at hy
  rw [symEval_apply]
  generalize (SymPow.symAlgBaseChangeEquiv (A := k) R V).symm x = y at hy
  rw [Submodule.baseChange_eq_span] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨z, hz, rfl⟩ := hz
    rw [TensorProduct.mk_apply, tensorEval_tmul, _root_.map_one, _root_.map_one, one_mul]
    exact hz
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have : r • a = (r ⊗ₜ[k] (1 : SymmetricAlgebra k V)) * a := by
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    rw [this, _root_.map_mul, tensorEval_tmul, mul_one, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ha

/-- **The evaluation at a point, as a homomorphism of graded rings.** -/
public def gradedSymEval (lam : R →ₐ[k] k) :
    (fun n => SymPow.symmetricPower n R (R ⊗[k] V)) →+*ᵍ
      (fun n => SymPow.symmetricPower n k V) where
  __ := symEval lam
  map_mem := fun hx => symEval_mem lam hx

/-- The graded evaluation `gradedSymEval λ` acts as `symEval λ`. -/
public theorem gradedSymEval_apply (lam : R →ₐ[k] k) (x : SymmetricAlgebra R (R ⊗[k] V)) :
    gradedSymEval lam x = symEval lam x := rfl

/-- The graded evaluation at a point is a left inverse of the graded homomorphism
`Sym_k(V) → Sym_R(R ⊗_k V)`, `x ↦ 1 ⊗ x`. -/
public theorem gradedSymEval_comp_symBaseChangeGraded (lam : R →ₐ[k] k) :
    (gradedSymEval lam).comp (Stacks.ProjectiveSpaceBaseChange.symBaseChangeGraded k R V) =
      GradedRingHom.id (fun n => SymPow.symmetricPower n k V) :=
  GradedRingHom.ext fun x => symEval_symBaseChangeGraded lam x

/-- **The section of `𝐏_R(R ⊗_k V) ⟶ 𝐏(V)` at a `k`-point `λ` of `R`**: `Proj` of the evaluation
at `λ`. -/
public def pointSection (lam : R →ₐ[k] k) :
    projectiveSpaceOfModule k V ⟶ projectiveSpaceOfModule R (R ⊗[k] V) :=
  Proj.map (gradedSymEval lam)
    (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id
      (gradedSymEval_comp_symBaseChangeGraded lam))

/-- **`σ_λ` is a section of the base-change morphism to `𝐏(V)`.** -/
@[reassoc]
public theorem pointSection_comp_baseChangeMap (lam : R →ₐ[k] k) :
    pointSection (V := V) lam ≫ Stacks.ProjectiveSpaceBaseChange.map k R V = 𝟙 _ := by
  rw [pointSection, Stacks.ProjectiveSpaceBaseChange.map, ← Proj.map_comp]
  rw [← Proj.map_id]
  exact Stacks.ProjectiveCohomology.Proj_map_congr _ _ _ _
    (gradedSymEval_comp_symBaseChangeGraded lam)

/-- **`σ_λ` lies over the point `λ` of `Spec R`.** -/
@[reassoc]
public theorem pointSection_comp_toSpec (lam : R →ₐ[k] k) :
    pointSection (V := V) lam ≫ projectiveSpaceOfModuleToSpec R (R ⊗[k] V) =
      projectiveSpaceOfModuleToSpec k V ≫ Spec.map (CommRingCat.ofHom lam.toRingHom) := by
  rw [projectiveSpaceOfModuleToSpec, projectiveSpaceOfModuleToSpec, pointSection,
    ← Category.assoc, Proj.map_toSpecZero, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine RingHom.ext fun r => Subtype.ext ?_
  change symEval lam (algebraMap R (SymmetricAlgebra R (R ⊗[k] V)) r) =
    algebraMap k (SymmetricAlgebra k V) (lam r)
  exact symEval_algebraMap lam r

/-- The evaluation intertwines `Sym G` with `Sym G(λ)`. -/
public theorem symEval_symAlgMap (lam : R →ₐ[k] k) (G : R ⊗[k] V →ₗ[R] R ⊗[k] V)
    (x : SymmetricAlgebra R (R ⊗[k] V)) :
    symEval lam (SymPow.symAlgMap (R := R) G x) =
      SymPow.symAlgMap (R := k) (specializeEnd lam G) (symEval lam x) := by
  obtain ⟨y, rfl⟩ := (SymPow.symAlgBaseChangeEquiv (A := k) R V).surjective x
  set e := SymPow.symAlgBaseChangeEquiv (A := k) R V with he
  set Φ : R ⊗[k] SymmetricAlgebra k V →ₐ[R] R ⊗[k] SymmetricAlgebra k V :=
    (e.symm.toAlgHom.comp (SymPow.symAlgMap G)).comp e.toAlgHom with hΦ
  have key : (tensorEval lam).comp (Φ.restrictScalars k) =
      (SymPow.symAlgMap (R := k) (specializeEnd lam G)).comp (tensorEval lam) := by
    refine Algebra.TensorProduct.ext ?_ ?_
    · ext r
      change tensorEval lam (e.symm (SymPow.symAlgMap G (e (r ⊗ₜ[k] 1)))) =
        SymPow.symAlgMap (R := k) (specializeEnd lam G) (tensorEval lam (r ⊗ₜ[k] 1))
      have h1 : e (r ⊗ₜ[k] (1 : SymmetricAlgebra k V)) =
          algebraMap R (SymmetricAlgebra R (R ⊗[k] V)) r := by
        rw [he, SymPow.symAlgBaseChangeEquiv_apply, SymPow.symAlgBaseChangeHom_tmul,
          _root_.map_one, mul_one]
      rw [h1, AlgHom.commutes, AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, tensorEval_tmul, mul_one, AlgHom.commutes]
    · refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun v => ?_)
      change tensorEval lam (e.symm (SymPow.symAlgMap G (e (1 ⊗ₜ[k] SymmetricAlgebra.ι k V v)))) =
        SymPow.symAlgMap (R := k) (specializeEnd lam G)
          (tensorEval lam (1 ⊗ₜ[k] SymmetricAlgebra.ι k V v))
      have h1 : e ((1 : R) ⊗ₜ[k] SymmetricAlgebra.ι k V v) =
          SymmetricAlgebra.ι R (R ⊗[k] V) ((1 : R) ⊗ₜ[k] v) := by
        rw [he, SymPow.symAlgBaseChangeEquiv_apply, SymPow.symAlgBaseChangeHom_tmul,
          _root_.map_one, one_mul, SymmetricAlgebra.lift_ι_apply, SymPow.toSymBaseChange_apply]
      rw [h1, SymPow.symAlgMap_ι]
      change symEval lam (SymmetricAlgebra.ι R (R ⊗[k] V) (G (1 ⊗ₜ[k] v))) = _
      rw [symEval_ι, tensorEval_tmul, _root_.map_one, _root_.map_one, one_mul,
        SymPow.symAlgMap_ι, specializeEnd_apply]
  have := DFunLike.congr_fun key y
  change tensorEval lam (e.symm (SymPow.symAlgMap G (e y))) = _ at this
  rw [symEval_apply, symEval_apply, AlgEquiv.symm_apply_apply]
  exact this

/-- **The fibre of the family of automorphisms `map G` over the point `λ` is `map G(λ)`.** -/
@[reassoc]
public theorem pointSection_comp_map (lam : R →ₐ[k] k)
    (G : LinearMap.GeneralLinearGroup R (R ⊗[k] V)) :
    pointSection lam ≫ map R (R ⊗[k] V) G = map k V (specializeGL lam G) ≫ pointSection lam := by
  rw [pointSection, map, map, ← Proj.map_comp, ← Proj.map_comp]
  refine Stacks.ProjectiveCohomology.Proj_map_congr _ _ _ _ (GradedRingHom.ext fun x => ?_)
  exact symEval_symAlgMap lam (G : R ⊗[k] V →ₗ[R] R ⊗[k] V) x

/-- The automorphism attached to an invertible map lies over the base. -/
@[reassoc]
public theorem map_comp_toSpec' (G : LinearMap.GeneralLinearGroup R (R ⊗[k] V)) :
    map R (R ⊗[k] V) G ≫ projectiveSpaceOfModuleToSpec R (R ⊗[k] V) =
      projectiveSpaceOfModuleToSpec R (R ⊗[k] V) :=
  projectiveSpaceOfModuleMap_comp_toSpec G

/-- The automorphism attached to an invertible map composed with the one attached to its inverse
is the identity. -/
@[reassoc]
public theorem map_comp_map_inv {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    (G : LinearMap.GeneralLinearGroup S M) :
    map S M G ≫ map S M G⁻¹ = 𝟙 _ := by
  rw [← map_mul, mul_inv_cancel, map_one]

/-- The automorphism attached to the inverse of an invertible map composed with the one attached
to the map is the identity. -/
@[reassoc]
public theorem map_inv_comp_map {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    (G : LinearMap.GeneralLinearGroup S M) :
    map S M G⁻¹ ≫ map S M G = 𝟙 _ := by
  rw [← map_mul, inv_mul_cancel, map_one]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
