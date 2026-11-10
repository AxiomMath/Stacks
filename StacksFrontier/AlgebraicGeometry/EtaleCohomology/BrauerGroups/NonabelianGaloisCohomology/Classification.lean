module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.SplitCocycle
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.Basic
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.SplitCocycle

/-!
# The classification of central simple algebras by nonabelian Galois cohomology

Galois descent for the twisted action shows that its invariants form a central simple algebra of
degree `d` over `K`, which gives the map from `PGLH1` back to `CentralSimpleAlgebraClass`. The two
maps are mutually inverse, proving `centralSimpleAlgebraClassEquivPGLH1`.
-/

open scoped MatrixGroups TensorProduct

universe u v

@[expose] public section

private noncomputable def finiteGaloisMatrixRepresentation (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    Representation K (L ≃ₐ[K] L) (Matrix (Fin d) (Fin d) L) :=
  (AlgEquiv.toLinearMapHom K (Matrix (Fin d) (Fin d) L)).comp
    (finiteGaloisMatrixActionHom K Ksep d f L hfactor hcoeff)

private theorem finiteGaloisMatrixRepresentation_restrict_apply (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) (M : Matrix (Fin d) (Fin d) L) :
    finiteGaloisMatrixRepresentation K Ksep d f L hfactor hcoeff
        (σ.restrictNormalHom L) M =
      finiteGaloisMatrixAction K Ksep d f L hcoeff σ M := by
  simp [finiteGaloisMatrixRepresentation, finiteGaloisMatrixActionHom_restrict,
    finiteGaloisMatrixActionHomRaw]
  rfl

private theorem finiteGaloisMatrixRepresentation_semilinear (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (γ : L ≃ₐ[K] L) (a : L) (M : Matrix (Fin d) (Fin d) L) :
    finiteGaloisMatrixRepresentation K Ksep d f L hfactor hcoeff γ (a • M) =
      γ a • finiteGaloisMatrixRepresentation K Ksep d f L hfactor hcoeff γ M := by
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ksep γ
  apply finiteGaloisMatrixInclusion_injective K Ksep d L
  rw [finiteGaloisMatrixRepresentation_restrict_apply,
    finiteGaloisMatrixRepresentation_restrict_apply,
    finiteGaloisMatrixAction_apply]
  have hsmul (b : L) (N : Matrix (Fin d) (Fin d) L) :
      finiteGaloisMatrixInclusion K Ksep d L (b • N) =
        (b : Ksep) • finiteGaloisMatrixInclusion K Ksep d L N := by
    ext i j
    rfl
  rw [hsmul a M,
    hsmul ((σ.restrictNormalHom L) a)
      (finiteGaloisMatrixAction K Ksep d f L hcoeff σ M),
    cocycleMatrixGaloisAut_smul,
    finiteGaloisMatrixAction_apply]
  congr 1
  exact (AlgEquiv.restrictNormalHom_apply L.toIntermediateField σ a).symm

private theorem finiteGalois_span_invariants_eq_top
    {k L V : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [Module L V]
    [Finite (L ≃ₐ[k] L)]
    {ρ : Representation k (L ≃ₐ[k] L) V}
    (hsemi : ∀ (σ : L ≃ₐ[k] L) (a : L) (v : V),
      ρ σ (a • v) = σ a • ρ σ v) :
    Submodule.span L (ρ.invariants : Set V) = ⊤ := by
  classical
  let := Fintype.ofFinite (L ≃ₐ[k] L)
  by_contra hspan
  obtain ⟨f, hf, hker⟩ :=
    (Submodule.span L (ρ.invariants : Set V)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hspan)
  apply hf
  ext v
  have horbit (a : L) : ∑ σ : L ≃ₐ[k] L, ρ σ (a • v) ∈ ρ.invariants := by
    rw [Representation.mem_invariants]
    intro τ
    simpa only [Representation.norm, LinearMap.sum_apply] using
      ρ.self_norm_apply τ (a • v)
  have hsum : ∑ σ : L ≃ₐ[k] L, f (ρ σ v) • σ.toAlgHom.toLinearMap = 0 := by
    ext a
    have hz := hker (Submodule.subset_span (horbit a))
    have hz' : f (∑ σ : L ≃ₐ[k] L, ρ σ (a • v)) = 0 := hz
    simpa only [map_sum, hsemi, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
      smul_eq_mul, mul_comm, LinearMap.zero_apply] using hz'
  have hli := (linearIndependent_algHom_toLinearMap k L L).comp
    (fun σ : L ≃ₐ[k] L => σ.toAlgHom) AlgEquiv.coe_toAlgHom_injective
  have hz := (Fintype.linearIndependent_iff.mp hli _ hsum) (1 : L ≃ₐ[k] L)
  simpa using hz

private theorem finiteGalois_liftBaseChange_injective_of_invariant
    {k L V W : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
    [AddCommGroup W] [Module k W]
    [FiniteDimensional k L] [IsGalois k L]
    {ρ : Representation k (L ≃ₐ[k] L) V}
    {f : W →ₗ[k] V} (hf : Function.Injective f)
    (hsemi : ∀ (σ : L ≃ₐ[k] L) (a : L) (w : W),
      ρ σ (a • f w) = σ a • f w) :
    Function.Injective (f.liftBaseChange L) := by
  classical
  let b := Module.finBasis k L
  have hnorm (a : L) (w : W) :
      ρ.norm (a • f w) = Algebra.trace k L a • f w := by
    simp only [Representation.norm, LinearMap.sum_apply, hsemi]
    rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms,
      IsScalarTower.algebraMap_smul]
  let p : V →ₗ[k] L ⊗[k] V := ∑ i,
    (TensorProduct.mk k L V (b i)).comp
      (ρ.norm.comp ((LinearMap.lsmul L V (b.traceDual i)).restrictScalars k))
  have hp : p.comp ((f.liftBaseChange L).restrictScalars k) = f.lTensor L := by
    apply TensorProduct.ext'
    intro a w
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, p,
      LinearMap.sum_apply, LinearMap.lsmul_apply, smul_smul, hnorm,
      TensorProduct.mk_apply]
    have hcoeff (i) : Algebra.trace k L (b.traceDual i * a) = b.repr a i := by
      rw [← b.traceDual_traceDual, Module.Basis.traceDual_repr_apply]
      simp [Algebra.traceForm, mul_comm]
    simp only [hcoeff, ← TensorProduct.smul_tmul]
    rw [← TensorProduct.sum_tmul, b.sum_repr]
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := L) f hf
  have h' := congrArg p h
  simpa only [← hp, LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h'

private noncomputable def finiteGaloisFixedMatrixAlgebra (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    Subalgebra K (Matrix (Fin d) (Fin d) L) := by
  let ρ := finiteGaloisMatrixRepresentation K Ksep d f L hfactor hcoeff
  refine ρ.invariants.toSubalgebra ?_ ?_
  · rw [Representation.mem_invariants]
    intro γ
    change (finiteGaloisMatrixActionHom K Ksep d f L hfactor hcoeff γ) 1 = 1
    exact map_one _
  · intro M N hM hN
    rw [Representation.mem_invariants] at hM hN ⊢
    intro γ
    change (finiteGaloisMatrixActionHom K Ksep d f L hfactor hcoeff γ) (M * N) = M * N
    rw [map_mul]
    exact congrArg₂ (· * ·) (hM γ) (hN γ)

private noncomputable def finiteGaloisFixedMatrixBaseChangeHom (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    L ⊗[K] finiteGaloisFixedMatrixAlgebra K Ksep d f L hfactor hcoeff →ₐ[L]
      Matrix (Fin d) (Fin d) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (Subalgebra.val _)
    (fun _ _ => Algebra.commutes _ _)

private theorem finiteGaloisFixedMatrixAlgebra_toSubmodule (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    (finiteGaloisFixedMatrixAlgebra K Ksep d f L hfactor hcoeff).toSubmodule =
      (finiteGaloisMatrixRepresentation K Ksep d f L hfactor hcoeff).invariants := by
  unfold finiteGaloisFixedMatrixAlgebra
  exact Submodule.toSubalgebra_toSubmodule _ _ _

private theorem finiteGaloisFixedMatrixBaseChangeHom_bijective (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    Function.Bijective (finiteGaloisFixedMatrixBaseChangeHom K Ksep d f L hfactor hcoeff) := by
  let B := finiteGaloisFixedMatrixAlgebra K Ksep d f L hfactor hcoeff
  let ρ := finiteGaloisMatrixRepresentation K Ksep d f L hfactor hcoeff
  let inc : B →ₗ[K] Matrix (Fin d) (Fin d) L := (Subalgebra.val B).toLinearMap
  have hB : B.toSubmodule = ρ.invariants :=
    finiteGaloisFixedMatrixAlgebra_toSubmodule K Ksep d f L hfactor hcoeff
  have hinc : inc.range = ρ.invariants := by
    change B.toSubmodule.subtype.range = ρ.invariants
    rw [Submodule.range_subtype]
    exact hB
  have hsemi := finiteGaloisMatrixRepresentation_semilinear K Ksep d f L hfactor hcoeff
  have hinj : Function.Injective (inc.liftBaseChange L) := by
    apply finiteGalois_liftBaseChange_injective_of_invariant
      (ρ := ρ) (f := inc) (by intro x y h; exact Subtype.ext h)
    intro γ a w
    rw [hsemi]
    congr 1
    exact (Representation.mem_invariants _ _).mp (hB ▸ w.property) γ
  have hsurj : Function.Surjective (inc.liftBaseChange L) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, hinc]
    exact finiteGalois_span_invariants_eq_top (ρ := ρ) hsemi
  have hlin :
      (finiteGaloisFixedMatrixBaseChangeHom K Ksep d f L hfactor hcoeff).toLinearMap =
        inc.liftBaseChange L := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
        simp only [AlgHom.toLinearMap_apply, LinearMap.liftBaseChange_tmul]
        exact (Algebra.TensorProduct.lift_tmul _ _ _ a b).trans
          (by simp [inc, Algebra.smul_def])
  change Function.Bijective
    (finiteGaloisFixedMatrixBaseChangeHom K Ksep d f L hfactor hcoeff).toLinearMap
  rw [hlin]
  exact ⟨hinj, hsurj⟩

private theorem cocycleFixedMatrixAlgebra_mem_finiteGalois (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (M : cocycleFixedMatrixAlgebra K Ksep d f) (i j : Fin d) :
    (M : Matrix (Fin d) (Fin d) Ksep) i j ∈ L.toIntermediateField := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField,
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hres : σ.restrictNormalHom L = (1 : Ksep ≃ₐ[K] Ksep).restrictNormalHom L := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    simpa [AlgEquiv.restrictNormalHom_apply] using
      (IntermediateField.mem_fixingSubgroup_iff L.toIntermediateField σ).mp hσ x x.property
  have hf : f.toFun σ = 1 := by
    rw [← pglCocycle_map_one K Ksep d f]
    exact hfactor σ 1 hres
  have hfix := (mem_cocycleFixedMatrixAlgebra_iff K Ksep d f M.1).mp M.2 σ
  have hentry := congrArg (fun N : Matrix (Fin d) (Fin d) Ksep => N i j) hfix
  simpa [cocycleMatrixGaloisAut, hf, matrixGaloisAut_apply] using hentry

/-- A matrix over `L` is Galois-invariant iff its image in `Ksep` lies in the fixed algebra. -/
private theorem finiteGaloisMatrixInclusion_mem_fixed_iff (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (N : Matrix (Fin d) (Fin d) L) :
    finiteGaloisMatrixInclusion K Ksep d L N ∈ cocycleFixedMatrixAlgebra K Ksep d f ↔
      N ∈ finiteGaloisFixedMatrixAlgebra K Ksep d f L hfactor hcoeff := by
  rw [mem_cocycleFixedMatrixAlgebra_iff, ← Subalgebra.mem_toSubmodule,
    finiteGaloisFixedMatrixAlgebra_toSubmodule, Representation.mem_invariants]
  constructor
  · intro h γ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ksep γ
    apply finiteGaloisMatrixInclusion_injective K Ksep d L
    rw [finiteGaloisMatrixRepresentation_restrict_apply, finiteGaloisMatrixAction_apply]
    exact h σ
  · intro h σ
    have hfix := h (σ.restrictNormalHom L)
    rw [finiteGaloisMatrixRepresentation_restrict_apply] at hfix
    rw [← finiteGaloisMatrixAction_apply K Ksep d f L hcoeff σ]
    exact congrArg _ hfix

private noncomputable def finiteGaloisFixedMatrixToFixed (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    finiteGaloisFixedMatrixAlgebra K Ksep d f L hfactor hcoeff →ₐ[K]
      cocycleFixedMatrixAlgebra K Ksep d f := by
  apply AlgHom.codRestrict
    ((finiteGaloisMatrixInclusion K Ksep d L).comp
      (Subalgebra.val (finiteGaloisFixedMatrixAlgebra K Ksep d f L hfactor hcoeff)))
    (cocycleFixedMatrixAlgebra K Ksep d f)
  exact fun M => (finiteGaloisMatrixInclusion_mem_fixed_iff K Ksep d f L hfactor hcoeff _).2
    M.property

private theorem finiteGaloisFixedMatrixToFixed_bijective (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    Function.Bijective (finiteGaloisFixedMatrixToFixed K Ksep d f L hfactor hcoeff) := by
  let B := finiteGaloisFixedMatrixAlgebra K Ksep d f L hfactor hcoeff
  let j := finiteGaloisMatrixInclusion K Ksep d L
  constructor
  · exact fun M N h => Subtype.ext
      (finiteGaloisMatrixInclusion_injective K Ksep d L (congrArg Subtype.val h))
  · intro M
    let N : Matrix (Fin d) (Fin d) L :=
      fun i j => ⟨(M : Matrix (Fin d) (Fin d) Ksep) i j,
        cocycleFixedMatrixAlgebra_mem_finiteGalois K Ksep d f L hfactor M i j⟩
    have hN : N ∈ B :=
      (finiteGaloisMatrixInclusion_mem_fixed_iff K Ksep d f L hfactor hcoeff N).1 M.property
    refine ⟨⟨N, hN⟩, ?_⟩
    apply Subtype.ext
    ext i j
    rfl

private noncomputable def cocycleFixedMatrix_splitEquiv (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    L ⊗[K] cocycleFixedMatrixAlgebra K Ksep d f ≃ₐ[L]
      Matrix (Fin d) (Fin d) L :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := L))
    (AlgEquiv.ofBijective (finiteGaloisFixedMatrixToFixed K Ksep d f L hfactor hcoeff)
      (finiteGaloisFixedMatrixToFixed_bijective K Ksep d f L hfactor hcoeff)).symm).trans
    (AlgEquiv.ofBijective
      (finiteGaloisFixedMatrixBaseChangeHom K Ksep d f L hfactor hcoeff)
      (finiteGaloisFixedMatrixBaseChangeHom_bijective K Ksep d f L hfactor hcoeff))

private noncomputable def cocycleCentralSimpleAlgebraOfDegree (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : d ≠ 0) (f : PGLCocycle K Ksep d) :
    CentralSimpleAlgebraOfDegree.{u, v} K d := by
  classical
  let A := cocycleFixedMatrixAlgebra K Ksep d f
  let hw := pglCocycle_exists_finiteGalois_basis_field K Ksep d f
  let L := Classical.choose hw
  let hfactor := (Classical.choose_spec hw).1
  let hcoeff := (Classical.choose_spec hw).2
  let e := cocycleFixedMatrix_splitEquiv K Ksep d f L hfactor hcoeff
  have hs : Algebra.IsSplit K A L := ⟨d, hd, ⟨e⟩⟩
  have hc := hs.finite_central_simple L
  let C : CSA.{u, v} K :=
    { toAlgCat := AlgCat.of K A
      isCentral := hc.2.1
      isSimple := hc.2.2
      fin_dim := hc.1 }
  exact ⟨C, (Algebra.IsSplit.matrix_size_eq_degree L e).symm⟩

private def cocycleFixedMatrixBaseChangeHom (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d) :
    Ksep ⊗[K] cocycleFixedMatrixAlgebra K Ksep d f →ₐ[Ksep]
      Matrix (Fin d) (Fin d) Ksep :=
  Algebra.TensorProduct.lift (Algebra.ofId Ksep _)
    (Subalgebra.val (cocycleFixedMatrixAlgebra K Ksep d f))
    (fun _ _ => Algebra.commutes _ _)

private theorem cocycleFixedMatrixBaseChangeHom_bijective (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : d ≠ 0) (f : PGLCocycle K Ksep d) :
    Function.Bijective (cocycleFixedMatrixBaseChangeHom K Ksep d f) := by
  classical
  let A := cocycleFixedMatrixAlgebra K Ksep d f
  let C := cocycleCentralSimpleAlgebraOfDegree K Ksep d hd f
  let e : Ksep ⊗[K] A ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep :=
    Classical.choice (centralSimpleAlgebraOfDegree_splitEquiv K Ksep d C)
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  let : FiniteDimensional Ksep (Ksep ⊗[K] A) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have hsimp : IsSimpleRing (Ksep ⊗[K] A) :=
    IsSimpleRing.of_ringEquiv e.symm.toRingEquiv
      (IsSimpleRing.matrix (Fin d) Ksep)
  let h := cocycleFixedMatrixBaseChangeHom K Ksep d f
  have hinj : Function.Injective h := RingHom.injective h.toRingHom
  have hdim : Module.finrank Ksep (Ksep ⊗[K] A) =
      Module.finrank Ksep (Matrix (Fin d) (Fin d) Ksep) := e.toLinearEquiv.finrank_eq
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

private theorem cocycleFixedMatrixBaseChangeHom_tmul (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d)
    (a : Ksep) (M : cocycleFixedMatrixAlgebra K Ksep d f) :
    cocycleFixedMatrixBaseChangeHom K Ksep d f (a ⊗ₜ[K] M) = a • M.1 :=
  (Algebra.TensorProduct.lift_tmul _ _ _ a M).trans (by simp [Algebra.smul_def])

private theorem cocycleFixedMatrixBaseChangeHom_intertwines (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d) (σ : Ksep ≃ₐ[K] Ksep)
    (z : Ksep ⊗[K] cocycleFixedMatrixAlgebra K Ksep d f) :
    cocycleFixedMatrixBaseChangeHom K Ksep d f
        (tensorGaloisAut K Ksep (cocycleFixedMatrixAlgebra K Ksep d f) σ z) =
      cocycleMatrixGaloisAut K Ksep d f σ
        (cocycleFixedMatrixBaseChangeHom K Ksep d f z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a M =>
      rw [tensorGaloisAut_tmul, cocycleFixedMatrixBaseChangeHom_tmul,
        cocycleFixedMatrixBaseChangeHom_tmul,
        cocycleMatrixGaloisAut_smul,
        (mem_cocycleFixedMatrixAlgebra_iff K Ksep d f M.1).mp M.property σ]

private theorem splitPGLCocycle_fixedMatrix_cohomologous (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : d ≠ 0) (f : PGLCocycle K Ksep d) :
    PGLCocycle.IsCohomologous f
      (splitPGLCocycle K Ksep d hd (cocycleFixedMatrixAlgebra K Ksep d f)
        (AlgEquiv.ofBijective (cocycleFixedMatrixBaseChangeHom K Ksep d f)
          (cocycleFixedMatrixBaseChangeHom_bijective K Ksep d hd f))) := by
  let A := cocycleFixedMatrixAlgebra K Ksep d f
  let e : Ksep ⊗[K] A ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep :=
    AlgEquiv.ofBijective (cocycleFixedMatrixBaseChangeHom K Ksep d f)
      (cocycleFixedMatrixBaseChangeHom_bijective K Ksep d hd f)
  have he (z : Ksep ⊗[K] A) : e z = cocycleFixedMatrixBaseChangeHom K Ksep d f z := rfl
  have ht (σ : Ksep ≃ₐ[K] Ksep) :
      splitTransportAlgAut K Ksep A d e σ = pglToMatrixAlgAut Ksep d (f.toFun σ) := by
    apply AlgEquiv.ext
    intro M
    obtain ⟨z, hz⟩ := e.surjective ((matrixGaloisAut K Ksep d σ).symm M)
    have hM : M = matrixGaloisAut K Ksep d σ (e z) := by
      rw [hz]
      simp
    rw [hM]
    change splitTransportAut K Ksep A d e σ
      (matrixGaloisAut K Ksep d σ (e z)) = _
    simp only [splitTransportAut, AlgEquiv.trans_apply,
      AlgEquiv.restrictScalars_apply, AlgEquiv.symm_restrictScalars,
      AlgEquiv.symm_apply_apply]
    simp only [he]
    simpa only [cocycleMatrixGaloisAut, AlgEquiv.mul_apply,
      AlgEquiv.restrictScalars_apply] using
      cocycleFixedMatrixBaseChangeHom_intertwines K Ksep d f σ z
  refine ⟨1, ?_⟩
  intro σ
  simp only [inv_one, one_mul, map_one, mul_one]
  apply (pglToMatrixAlgAutEquiv Ksep d hd).injective
  simpa only [splitPGLCocycle, splitTransportPGL,
    (pglToMatrixAlgAutEquiv Ksep d hd).apply_symm_apply,
    pglToMatrixAlgAutEquiv_apply] using ht σ

private theorem cocycleMatrixGaloisAut_splitPGLCocycle (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    (A : Type*) [Ring A] [Algebra K A] (d : ℕ) (hd : d ≠ 0)
    (e : Ksep ⊗[K] A ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ : Ksep ≃ₐ[K] Ksep) :
    cocycleMatrixGaloisAut K Ksep d (splitPGLCocycle K Ksep d hd A e) σ =
      (AlgEquiv.restrictScalars K e.symm).trans
        ((tensorGaloisAut K Ksep A σ).trans (AlgEquiv.restrictScalars K e)) := by
  apply AlgEquiv.ext
  intro M
  have hpgl : pglToMatrixAlgAut Ksep d
      (splitTransportPGL K Ksep d hd A e σ) =
      splitTransportAlgAut K Ksep A d e σ :=
    (pglToMatrixAlgAutEquiv Ksep d hd).apply_symm_apply _
  simp only [cocycleMatrixGaloisAut, splitPGLCocycle, hpgl,
    AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.trans_apply]
  change splitTransportAut K Ksep A d e σ (matrixGaloisAut K Ksep d σ M) = _
  simp only [splitTransportAut, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.symm_restrictScalars,
    AlgEquiv.symm_apply_apply]

private noncomputable def splitToFixedMatrixHom (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    (A : Type v) [Ring A] [Algebra K A] (d : ℕ) (hd : d ≠ 0)
    (e : Ksep ⊗[K] A ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep) :
    A →ₐ[K] cocycleFixedMatrixAlgebra K Ksep d (splitPGLCocycle K Ksep d hd A e) := by
  let j : A →ₐ[K] Ksep ⊗[K] A := Algebra.TensorProduct.includeRight
  let h : A →ₐ[K] Matrix (Fin d) (Fin d) Ksep :=
    (e.restrictScalars K).toAlgHom.comp j
  apply AlgHom.codRestrict h
    (cocycleFixedMatrixAlgebra K Ksep d (splitPGLCocycle K Ksep d hd A e))
  intro a
  rw [mem_cocycleFixedMatrixAlgebra_iff]
  intro σ
  rw [cocycleMatrixGaloisAut_splitPGLCocycle]
  have ha : h a = e (1 ⊗ₜ[K] a) := rfl
  rw [ha]
  simp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.symm_apply_apply]
  rw [tensorGaloisAut_tmul]
  simp

private theorem splitToFixedMatrixHom_bijective (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (A : Type v) [Ring A] [Algebra K A] [IsSimpleRing A]
    [FiniteDimensional K A] (d : ℕ) (hd : d ≠ 0)
    (e : Ksep ⊗[K] A ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep) :
    Function.Bijective (splitToFixedMatrixHom K Ksep A d hd e) := by
  classical
  let f := splitPGLCocycle K Ksep d hd A e
  let B := cocycleFixedMatrixAlgebra K Ksep d f
  let eB : Ksep ⊗[K] B ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep :=
    AlgEquiv.ofBijective (cocycleFixedMatrixBaseChangeHom K Ksep d f)
      (cocycleFixedMatrixBaseChangeHom_bijective K Ksep d hd f)
  let C := cocycleCentralSimpleAlgebraOfDegree K Ksep d hd f
  let : FiniteDimensional K B := C.1.fin_dim
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  let h := splitToFixedMatrixHom K Ksep A d hd e
  have hinj : Function.Injective h := RingHom.injective h.toRingHom
  have hdim : Module.finrank K A = Module.finrank K B := by
    calc
      Module.finrank K A = Module.finrank Ksep (Ksep ⊗[K] A) :=
        (Module.finrank_baseChange (R := Ksep) (S := K) (M' := A)).symm
      _ = Module.finrank Ksep (Matrix (Fin d) (Fin d) Ksep) :=
        e.toLinearEquiv.finrank_eq
      _ = Module.finrank Ksep (Ksep ⊗[K] B) :=
        eB.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K B :=
        Module.finrank_baseChange (R := Ksep) (S := K) (M' := B)
  have hsurj : Function.Surjective h.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨hinj, hsurj⟩

private theorem cocycleMatrixGaloisAut_cohomologous (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f g : PGLCocycle K Ksep d) (b : PGL(Fin d, Ksep))
    (hb : ∀ σ : Ksep ≃ₐ[K] Ksep,
      g.toFun σ = b⁻¹ * f.toFun σ *
        Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b)
    (σ : Ksep ≃ₐ[K] Ksep) :
    cocycleMatrixGaloisAut K Ksep d g σ =
      (AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b)).symm *
        cocycleMatrixGaloisAut K Ksep d f σ *
        AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b) := by
  let B := AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b)
  let F := AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d (f.toFun σ))
  let M := matrixGaloisAut K Ksep d σ
  have hrestrict (x y : Matrix (Fin d) (Fin d) Ksep ≃ₐ[Ksep]
      Matrix (Fin d) (Fin d) Ksep) :
      AlgEquiv.restrictScalars K (x * y) =
        AlgEquiv.restrictScalars K x * AlgEquiv.restrictScalars K y := by
    apply AlgEquiv.ext
    intro N
    rfl
  have hB : AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b⁻¹) = B.symm := by
    apply AlgEquiv.ext
    intro N
    simp [B]
  have hmap := pglToMatrixAlgAut_map K Ksep d σ b
  rw [cocycleMatrixGaloisAut, hb σ, map_mul, hrestrict,
    map_mul, hrestrict, hB, hmap]
  change (B.symm * F * (M * B * M⁻¹)) * M =
    B.symm * (F * M) * B
  group

/-- Conjugation by `b` matches the fixed algebras of cohomologous cocycles. -/
private theorem mem_cocycleFixedMatrixAlgebra_iff_symm (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f g : PGLCocycle K Ksep d) (b : PGL(Fin d, Ksep))
    (hb : ∀ σ : Ksep ≃ₐ[K] Ksep,
      g.toFun σ = b⁻¹ * f.toFun σ *
        Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b)
    (M : Matrix (Fin d) (Fin d) Ksep) :
    M ∈ cocycleFixedMatrixAlgebra K Ksep d f ↔
      (AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b)).symm M ∈
        cocycleFixedMatrixAlgebra K Ksep d g := by
  simp only [mem_cocycleFixedMatrixAlgebra_iff,
    cocycleMatrixGaloisAut_cohomologous K Ksep d f g b hb, AlgEquiv.mul_apply,
    AlgEquiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]

private noncomputable def cohomologousFixedMatrixHom (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f g : PGLCocycle K Ksep d) (b : PGL(Fin d, Ksep))
    (hb : ∀ σ : Ksep ≃ₐ[K] Ksep,
      g.toFun σ = b⁻¹ * f.toFun σ *
        Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b) :
    cocycleFixedMatrixAlgebra K Ksep d f →ₐ[K]
      cocycleFixedMatrixAlgebra K Ksep d g :=
  AlgHom.codRestrict
    ((AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b)).symm.toAlgHom.comp
      (Subalgebra.val (cocycleFixedMatrixAlgebra K Ksep d f)))
    (cocycleFixedMatrixAlgebra K Ksep d g)
    fun M => (mem_cocycleFixedMatrixAlgebra_iff_symm K Ksep d f g b hb M.1).1 M.property

private theorem cohomologousFixedMatrixHom_bijective (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f g : PGLCocycle K Ksep d) (b : PGL(Fin d, Ksep))
    (hb : ∀ σ : Ksep ≃ₐ[K] Ksep,
      g.toFun σ = b⁻¹ * f.toFun σ *
        Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b) :
    Function.Bijective (cohomologousFixedMatrixHom K Ksep d f g b hb) := by
  let B := AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b)
  constructor
  · exact fun M N h => Subtype.ext (B.symm.injective (congrArg Subtype.val h))
  · intro N
    have hmem : B N.1 ∈ cocycleFixedMatrixAlgebra K Ksep d f :=
      (mem_cocycleFixedMatrixAlgebra_iff_symm K Ksep d f g b hb _).2
        (by rw [B.symm_apply_apply]; exact N.property)
    exact ⟨⟨B N.1, hmem⟩, Subtype.ext (B.symm_apply_apply N.1)⟩

@[sga "4½ Arcata 3.1.2"]
private noncomputable def pglH1ToCentralSimpleAlgebraClass (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : d ≠ 0) :
    PGLH1 K Ksep d → CentralSimpleAlgebraClass.{u, v} K d :=
  Quotient.lift
    (fun f => Quotient.mk _ (cocycleCentralSimpleAlgebraOfDegree K Ksep d hd f))
    (by
      intro f g hfg
      obtain ⟨b, hb⟩ := (pglH1_relation_iff K Ksep d f g).mp hfg
      apply Quotient.sound
      apply Relation.EqvGen.rel
      change Nonempty ((cocycleFixedMatrixAlgebra K Ksep d f) ≃ₐ[K]
        (cocycleFixedMatrixAlgebra K Ksep d g))
      exact ⟨AlgEquiv.ofBijective (cohomologousFixedMatrixHom K Ksep d f g b hb)
        (cohomologousFixedMatrixHom_bijective K Ksep d f g b hb)⟩)

end

/-- Central simple algebras of degree `d` are classified by nonabelian
`PGL_d`-valued Galois cohomology. -/
@[stacks 03R6, sga "4½ Arcata 3.1.2" "θ_n bijection"]
public noncomputable def centralSimpleAlgebraClassEquivPGLH1
    (K : Type u) [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (d : ℕ) (hd : d ≠ 0) :
    CentralSimpleAlgebraClass.{u, v} K d ≃ PGLH1 K Ksep d :=
  { toFun := centralSimpleAlgebraClassToPGLH1 K Ksep d hd
    invFun := pglH1ToCentralSimpleAlgebraClass K Ksep d hd
    left_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ A =>
          apply (centralSimpleAlgebraClass_mk_eq_iff K d _ _).mpr
          let e := Classical.choice (centralSimpleAlgebraOfDegree_splitEquiv K Ksep d A)
          change Nonempty ((cocycleFixedMatrixAlgebra K Ksep d
            (splitPGLCocycle K Ksep d hd A.1 e)) ≃ₐ[K] A.1)
          exact ⟨(AlgEquiv.ofBijective (splitToFixedMatrixHom K Ksep A.1 d hd e)
            (splitToFixedMatrixHom_bijective K Ksep A.1 d hd e)).symm⟩
    right_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | _ f =>
          apply (pglH1_mk_eq_iff K Ksep d _ _).mpr
          let B := cocycleCentralSimpleAlgebraOfDegree K Ksep d hd f
          let e : Ksep ⊗[K] B.1 ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep :=
            AlgEquiv.ofBijective (cocycleFixedMatrixBaseChangeHom K Ksep d f)
              (cocycleFixedMatrixBaseChangeHom_bijective K Ksep d hd f)
          have h₁ := centralSimpleAlgebraOfDegree_cocycle_changeSplit K Ksep d hd B e
          have h₂ := splitPGLCocycle_fixedMatrix_cohomologous K Ksep d hd f
          let hrel := pglCocycle_isCohomologous_equivalence K Ksep d
          exact hrel.trans h₁ (hrel.symm h₂) }
