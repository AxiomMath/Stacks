module

public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.Algebra.Module.Projective.Determinant.Graded

/-!
# Base change of the determinant line

Let `R` be a commutative ring, `A` a commutative `R`-algebra and `M` a finite projective
`R`-module. This file proves that forming the determinant line commutes with base change along
`R → A`:

```
A ⊗_R det(M) ≅ det(A ⊗_R M)
```

compatibly with the inclusions into the exterior algebras, and degreewise on the rank strata: the
base-change equivalence of exterior algebras carries the degree-`n` rank-stratum summand
`ProjectiveDeterminant.component A (A ⊗_R M) n` of `det(A ⊗_R M)` onto the base change of
`ProjectiveDeterminant.component R M n`.

## Main definitions

* `ProjectiveDeterminant.exteriorAlgebraBaseChange`: the base-change comparison of exterior
  algebras `⋀_A(A ⊗_R M) ≃ A ⊗_R ⋀_R(M)`.
* `ProjectiveDeterminant.baseChangeEquiv`: the comparison `A ⊗_R det(M) ≃ det(A ⊗_R M)`.

## Main results

* `ProjectiveDeterminant.rankIdempotent_baseChange`: the rank idempotents of `A ⊗_R M` are the
  images of those of `M`.
* `ProjectiveDeterminant.component_baseChange_map`: the base-change comparison carries
  `component A (A ⊗_R M) n` onto the base change of `component R M n`.
* `ProjectiveDeterminant.annihilatorPart_baseChange_map`: the same for the degree-`n` part of the
  annihilator of the degree-one elements, read inside the exterior algebra.
* `ProjectiveDeterminant.submodule_baseChange_map`: the same for the whole determinant line.
* `ProjectiveDeterminant.coe_baseChangeEquiv_tmul`: the comparison computed on a pure tensor.

## References

* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
* [Stacks Project, Tag 0C6F](https://stacks.math.columbia.edu/tag/0C6F)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ProjectiveDeterminant

universe u v

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (M : Type*) [AddCommGroup M] [Module R M]

/-! ### Pure tensors in the exterior powers of a base change -/

/-- The pure tensors `1 ⊗ₜ m` span the base change `A ⊗_R M` as an `A`-module. -/
theorem tensorProduct_span_one_tmul :
    Submodule.span A (Set.range (TensorProduct.mk R A M 1)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      have h : (1 : A) ⊗ₜ[R] m ∈ Submodule.span A (Set.range (TensorProduct.mk R A M 1)) :=
        Submodule.subset_span ⟨m, rfl⟩
      simpa [TensorProduct.smul_tmul'] using Submodule.smul_mem (Submodule.span A _) a h
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- The wedges of pure tensors span the degree-`n` exterior power of a base change. -/
theorem exteriorPower_span_pure_baseChange (n : ℕ) :
    Submodule.span A (Set.range (fun v : Fin n → M =>
      ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] v i))) = ⋀[A]^n (A ⊗[R] M) := by
  have hs : Set.range (fun v : Fin n → M =>
        ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] v i)) =
      ExteriorAlgebra.ιMulti A n ''
        {a : Fin n → A ⊗[R] M | Set.range a ⊆ Set.range (TensorProduct.mk R A M 1)} := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨fun i => (1 : A) ⊗ₜ[R] v i, ?_, rfl⟩
      rintro y ⟨i, rfl⟩
      exact ⟨v i, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      classical
      have h (i : Fin n) : ∃ m : M, (1 : A) ⊗ₜ[R] m = a i := ha ⟨i, rfl⟩
      choose v hv using h
      exact ⟨v, congrArg (ExteriorAlgebra.ιMulti A n) (funext hv)⟩
  rw [hs]
  exact exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top
    (R := A) (M := A ⊗[R] M) (n := n) (tensorProduct_span_one_tmul R A M)

/-! ### The base-change comparison of exterior algebras -/

/-- A base-change comparison for the exterior algebra, `⋀_A(A ⊗_R M) ≃ A ⊗_R ⋀_R(M)`, sending
`ι (1 ⊗ₜ m)` to `1 ⊗ₜ ι m`. -/
def exteriorAlgebraBaseChange :
    ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M :=
  (ExteriorAlgebra.exists_algEquiv_baseChange R A M).choose

/-- The specification of `ProjectiveDeterminant.exteriorAlgebraBaseChange` on degree-one
generators. -/
theorem exteriorAlgebraBaseChange_ι (m : M) :
    exteriorAlgebraBaseChange R A M (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m :=
  (ExteriorAlgebra.exists_algEquiv_baseChange R A M).choose_spec m

/-- The base-change comparison carries a wedge of pure tensors to the pure tensor of the
wedge. -/
theorem exteriorAlgebraBaseChange_ιMulti (n : ℕ) (m : Fin n → M) :
    exteriorAlgebraBaseChange R A M
        (ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ιMulti R n m := by
  have hl (l : List M) :
      (l.map (fun x => (1 : A) ⊗ₜ[R] ExteriorAlgebra.ι R x)).prod =
        ((1 : A) ⊗ₜ[R] (l.map (ExteriorAlgebra.ι R)).prod : A ⊗[R] ExteriorAlgebra R M) := by
    induction l with
    | nil => simp [Algebra.TensorProduct.one_def]
    | cons x xs ih => simp [ih, Algebra.TensorProduct.tmul_mul_tmul]
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod]
  simpa only [List.map_ofFn, Function.comp_def, exteriorAlgebraBaseChange_ι]
    using hl (List.ofFn m)

/-- The base-change comparison carries the degree-`n` exterior power onto the base change of
the degree-`n` exterior power. -/
theorem exteriorPower_baseChange_map (n : ℕ) :
    Submodule.map (exteriorAlgebraBaseChange R A M).toLinearEquiv.toLinearMap
        (⋀[A]^n (A ⊗[R] M)) =
      Submodule.baseChange A (⋀[R]^n M) := by
  rw [← exteriorPower_span_pure_baseChange R A M n, Submodule.map_span,
    ← ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := M) n, Submodule.baseChange_span]
  congr 1
  rw [← Set.range_comp, ← Set.range_comp]
  exact congrArg _ (funext fun v => exteriorAlgebraBaseChange_ιMulti R A M n v)

/-! ### Transport of the rank idempotents along a linear equivalence -/

/-- Linearly equivalent modules have the same rank strata. -/
theorem rankLocus_eq_of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) : rankLocus (R := R) M n = rankLocus (R := R) N n :=
  congrArg (fun f => {p : PrimeSpectrum R | f p = n}) (Module.rankAtStalk_eq_of_equiv e)

/-- Linearly equivalent finite projective modules have the same rank idempotents. -/
theorem rankIdempotent_eq_of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) (n : ℕ) :
    rankIdempotent (R := R) (M := M) n = rankIdempotent (R := R) (M := N) n :=
  (Classical.choose_spec (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
    (rankLocus_isClopen (R := R) (M := N) n))).2 _
    ⟨(rankIdempotent_spec (R := R) (M := M) n).1,
      ((rankLocus_eq_of_linearEquiv R M e n).symm.trans
        (rankIdempotent_spec (R := R) (M := M) n).2)⟩

/-! ### Base change of the rank idempotents -/

variable [Module.Finite R M] [Module.Projective R M]

/-- The rank idempotents of `A ⊗_R M` are the images under `R → A` of the rank idempotents of
`M`. -/
theorem rankIdempotent_baseChange (n : ℕ) :
    algebraMap R A (rankIdempotent (R := R) (M := M) n) =
      rankIdempotent (R := A) (M := A ⊗[R] M) n := by
  apply (Classical.choose_spec (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
    (rankLocus_isClopen (R := A) (M := A ⊗[R] M) n))).2
  refine ⟨(rankIdempotent_spec (R := R) (M := M) n).1.map _, ?_⟩
  ext p
  change Module.rankAtStalk (A ⊗[R] M) p = n ↔ _
  rw [Module.rankAtStalk_baseChange]
  exact Set.ext_iff.mp (rankIdempotent_spec (R := R) (M := M) n).2
    (PrimeSpectrum.comap (algebraMap R A) p)

/-! ### Base change of the determinant line -/

/-- The base-change comparison carries the degree-`n` rank-stratum summand of `det(A ⊗_R M)`
onto the base change of the degree-`n` rank-stratum summand of `det(M)`. -/
theorem component_baseChange_map (n : ℕ) :
    Submodule.map (exteriorAlgebraBaseChange R A M).toLinearEquiv.toLinearMap
        (component (R := A) (M := A ⊗[R] M) n) =
      Submodule.baseChange A (component (R := R) (M := M) n) := by
  unfold component
  rw [← exteriorPower_span_pure_baseChange R A M n,
    ← ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := M) n,
    Submodule.map_span, Submodule.map_span, Submodule.map_span, Submodule.baseChange_span]
  congr 1
  simp only [← Set.range_comp]
  refine congrArg _ (funext fun v => ?_)
  simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
    TensorProduct.mk_apply]
  rw [map_smul (exteriorAlgebraBaseChange R A M), ← rankIdempotent_baseChange R A M,
    exteriorAlgebraBaseChange_ιMulti R A M n v, ← TensorProduct.smul_tmul]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [Algebra.smul_def, mul_one]

/-- The base-change comparison of exterior algebras carries the determinant line of `A ⊗_R M`
onto the base change of the determinant line of `M`. -/
theorem submodule_baseChange_map :
    Submodule.map (exteriorAlgebraBaseChange R A M).toLinearEquiv.toLinearMap
        (submodule (R := A) (M := A ⊗[R] M)) =
      Submodule.baseChange A (submodule (R := R) (M := M)) := by
  unfold submodule
  rw [Submodule.map_iSup]
  simp_rw [component_baseChange_map R A M]
  refine le_antisymm (iSup_le fun n => Submodule.baseChange_mono A (le_iSup _ n)) ?_
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro x ⟨y, hy, rfl⟩
  refine Submodule.iSup_induction _ (motive := fun y =>
    (1 : A) ⊗ₜ[R] y ∈ ⨆ n, Submodule.baseChange A (component (R := R) (M := M) n)) hy
    ?_ ?_ ?_
  · intro n y hy
    refine le_iSup (fun n => Submodule.baseChange A (component (R := R) (M := M) n)) n ?_
    rw [Submodule.baseChange_eq_span]
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  · simp
  · intro x y hx hy
    simpa [TensorProduct.tmul_add] using add_mem hx hy

/-- The determinant line commutes with base change: `A ⊗_R det(M) ≃ det(A ⊗_R M)`. -/
def baseChangeEquiv {R : Type u} {A : Type u} {M : Type v}
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    A ⊗[R] module (R := R) (M := M) ≃ₗ[A] module (R := A) (M := A ⊗[R] M) := by
  let E := (exteriorAlgebraBaseChange R A M).toLinearEquiv.ofSubmodules
    (submodule (R := A) (M := A ⊗[R] M))
    (Submodule.baseChange A (submodule (R := R) (M := M)))
    (submodule_baseChange_map R A M)
  let F := E.symm.toLinearMap.comp
    (Submodule.toBaseChange A (submodule (R := R) (M := M)))
  letI := invertible (R := R) (M := M)
  letI := invertible (R := A) (M := A ⊗[R] M)
  exact LinearEquiv.ofBijective F (Module.Invertible.bijective_of_surjective
    (E.symm.surjective.comp (Submodule.toBaseChange_surjective A _)))

/-- The base-change comparison of exterior algebras carries the degree-`n` part of the
annihilator of the degree-one elements of `A ⊗_R M` onto the base change of the degree-`n` part
of the annihilator of the degree-one elements of `M`, both read inside the exterior algebra
through the inclusion of the degree-`n` exterior power. -/
theorem annihilatorPart_baseChange_map (n : ℕ) :
    Submodule.map (exteriorAlgebraBaseChange R A M).toLinearEquiv.toLinearMap
        (Submodule.map (⋀[A]^n (A ⊗[R] M)).subtype
          ((⨅ m : A ⊗[R] M,
              LinearMap.ker (LinearMap.mulLeft A (ExteriorAlgebra.ι A m))).comap
            (⋀[A]^n (A ⊗[R] M)).subtype)) =
      Submodule.baseChange A
        (Submodule.map (⋀[R]^n M).subtype
          ((⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
            (⋀[R]^n M).subtype)) := by
  rw [map_annihilatorPart_eq_component (R := A) (M := A ⊗[R] M) n,
    map_annihilatorPart_eq_component (R := R) (M := M) n, component_baseChange_map R A M n]

/-- `ProjectiveDeterminant.baseChangeEquiv` on a pure tensor: inside the exterior algebra it is
the inverse of the exterior-algebra comparison. -/
theorem coe_baseChangeEquiv_tmul {R : Type u} {A : Type u} {M : Type v}
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (a : A) (x : module (R := R) (M := M)) :
    (baseChangeEquiv (R := R) (A := A) (M := M) (a ⊗ₜ[R] x) :
        ExteriorAlgebra A (A ⊗[R] M)) =
      (exteriorAlgebraBaseChange R A M).symm (a ⊗ₜ[R] (x : ExteriorAlgebra R M)) := rfl

end ProjectiveDeterminant

end
