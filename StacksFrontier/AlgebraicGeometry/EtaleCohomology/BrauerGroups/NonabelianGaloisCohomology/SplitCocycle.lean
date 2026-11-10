module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.Basic
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.NonabelianGaloisCohomology.Basic

/-!
# The cocycle of a split central simple algebra and the twisted Galois action

Given a central simple algebra `A` of degree `d` over `K` and a splitting
`Ksep ⊗[K] A ≃ M_d(Ksep)`, transporting the Galois action on the first tensor factor gives a
continuous crossed homomorphism with values in `PGL_d(Ksep)`. Changing the splitting or the
algebra up to isomorphism changes it by a coboundary, which yields the map from
`CentralSimpleAlgebraClass` to the cohomology set `PGLH1`.

Conversely, a cocycle `f` twists the coefficientwise Galois action on `M_d(Ksep)`; the cocycle
factors through the Galois group of a finite Galois subextension `L`, over which the twisted
action restricts to an action on `M_d(L)`.
-/

open scoped MatrixGroups TensorProduct

universe u v

@[expose] public section

private noncomputable def splitTransportPGL (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A : Type*) [Ring A] [Algebra K A]
    (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ : Ksep ≃ₐ[K] Ksep) : PGL(Fin d, Ksep) :=
  (pglToMatrixAlgAutEquiv Ksep d hd).symm
    (splitTransportAlgAut K Ksep A d e σ)

private theorem pglToMatrixAlgAutEquiv_map_restrict (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) (hd : d ≠ 0)
    (σ : Ksep ≃ₐ[K] Ksep) (b : PGL(Fin d, Ksep)) :
    AlgEquiv.restrictScalars K
        ((pglToMatrixAlgAutEquiv Ksep d hd)
          (Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b)) =
      matrixGaloisAut K Ksep d σ *
        AlgEquiv.restrictScalars K (pglToMatrixAlgAutEquiv Ksep d hd b) *
        (matrixGaloisAut K Ksep d σ).symm := by
  change AlgEquiv.restrictScalars K
      (pglToMatrixAlgAut Ksep d
        (Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b)) = _
  exact pglToMatrixAlgAut_map K Ksep d σ b

private theorem splitTransportPGL_map_mul (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A : Type*) [Ring A] [Algebra K A]
    (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ τ : Ksep ≃ₐ[K] Ksep) :
    splitTransportPGL K Ksep d hd A e (σ * τ) =
      splitTransportPGL K Ksep d hd A e σ *
        Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom
          (splitTransportPGL K Ksep d hd A e τ) := by
  apply (pglToMatrixAlgAutEquiv Ksep d hd).injective
  rw [(pglToMatrixAlgAutEquiv Ksep d hd).map_mul]
  simp only [splitTransportPGL,
    (pglToMatrixAlgAutEquiv Ksep d hd).apply_symm_apply]
  apply AlgEquiv.ext
  intro M
  have hcompat := pglToMatrixAlgAutEquiv_map_restrict K Ksep d hd σ
    (splitTransportPGL K Ksep d hd A e τ)
  have hcoc := DFunLike.congr_fun (splitTransportAut_cocycle K Ksep A d e σ τ) M
  simp only [splitTransportPGL,
    (pglToMatrixAlgAutEquiv Ksep d hd).apply_symm_apply,
    splitTransportAlgAut] at hcompat
  have hprod := congrArg (fun f : Matrix (Fin d) (Fin d) Ksep ≃ₐ[K]
      Matrix (Fin d) (Fin d) Ksep =>
        splitTransportAut K Ksep A d e σ * f) hcompat
  have hval := DFunLike.congr_fun hprod M
  calc
    (splitTransportAlgAut K Ksep A d e (σ * τ)) M =
        (splitTransportAut K Ksep A d e σ * matrixGaloisAut K Ksep d σ *
          splitTransportAut K Ksep A d e τ *
          (matrixGaloisAut K Ksep d σ).symm) M := hcoc
    _ = (splitTransportAlgAut K Ksep A d e σ *
        pglToMatrixAlgAutEquiv Ksep d hd
          (Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom
            (splitTransportPGL K Ksep d hd A e τ))) M := by
      simpa [splitTransportPGL, splitTransportAlgAut,
        AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, mul_assoc] using hval.symm

private theorem splitTransportPGL_continuous (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A : Type*) [Ring A] [Algebra K A]
    (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep) :
    ∃ S : Finset Ksep, ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      (∀ x ∈ S, σ x = τ x) →
        splitTransportPGL K Ksep d hd A e σ = splitTransportPGL K Ksep d hd A e τ := by
  classical
  let Sfun (ij : Fin d × Fin d) := Classical.choose <|
    tensorGaloisAut_eq_of_agree K Ksep A (e.symm (Matrix.stdBasis Ksep (Fin d) (Fin d) ij))
  have hSfun (ij : Fin d × Fin d) := Classical.choose_spec <|
    tensorGaloisAut_eq_of_agree K Ksep A (e.symm (Matrix.stdBasis Ksep (Fin d) (Fin d) ij))
  refine ⟨Finset.univ.biUnion Sfun, ?_⟩
  intro σ τ hστ
  apply (pglToMatrixAlgAutEquiv Ksep d hd).injective
  apply AlgEquiv.toLinearEquiv_injective
  apply (Matrix.stdBasis Ksep (Fin d) (Fin d)).ext'
  intro ij
  have hcoeff := hSfun ij σ τ (fun x hx =>
    hστ x (Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, hx⟩))
  have hρ (ρ : Ksep ≃ₐ[K] Ksep) : splitTransportAlgAut K Ksep A d e ρ
      (Matrix.stdBasis Ksep (Fin d) (Fin d) ij) =
        e (tensorGaloisAut K Ksep A ρ
          (e.symm (Matrix.stdBasis Ksep (Fin d) (Fin d) ij))) := by
    have hunit : (matrixGaloisAut K Ksep d ρ).symm
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij) =
          Matrix.stdBasis Ksep (Fin d) (Fin d) ij := by
      rw [Matrix.stdBasis_eq_single (R := Ksep) (m := Fin d) (n := Fin d) ij.1 ij.2]
      simp [matrixGaloisAut_symm, matrixGaloisAut_apply]
    simp [splitTransportAlgAut, splitTransportAut, AlgEquiv.trans_apply,
      AlgEquiv.restrictScalars_apply, hunit]
  simp only [splitTransportPGL,
    (pglToMatrixAlgAutEquiv Ksep d hd).apply_symm_apply]
  change splitTransportAlgAut K Ksep A d e σ
      (Matrix.stdBasis Ksep (Fin d) (Fin d) ij) =
    splitTransportAlgAut K Ksep A d e τ
      (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)
  rw [hρ σ, hρ τ]
  exact congrArg e hcoeff

private noncomputable def splitPGLCocycle (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A : Type*) [Ring A] [Algebra K A]
    (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep) :
    PGLCocycle K Ksep d where
  toFun := splitTransportPGL K Ksep d hd A e
  map_mul := splitTransportPGL_map_mul K Ksep d hd A e
  continuous := splitTransportPGL_continuous K Ksep d hd A e

private def tensorAlgEquivOfAlgEquiv (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    (A B : Type*) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f : A ≃ₐ[K] B) : (Ksep ⊗[K] A) ≃ₐ[Ksep] (Ksep ⊗[K] B) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl (R := Ksep) (A₁ := Ksep)) f

private theorem tensorAlgEquivOfAlgEquiv_commutes_galois (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (A B : Type*)
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A ≃ₐ[K] B)
    (σ : Ksep ≃ₐ[K] Ksep) :
    (AlgEquiv.restrictScalars K (tensorAlgEquivOfAlgEquiv K Ksep A B f)).trans
        (tensorGaloisAut K Ksep B σ) =
      (tensorGaloisAut K Ksep A σ).trans
        (AlgEquiv.restrictScalars K (tensorAlgEquivOfAlgEquiv K Ksep A B f)) := by
  apply AlgEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  | tmul x a => simp [tensorAlgEquivOfAlgEquiv, tensorGaloisAut]

private theorem splitTransportPGL_congr (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A B : Type*) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f : A ≃ₐ[K] B)
    (e : (Ksep ⊗[K] B) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ : Ksep ≃ₐ[K] Ksep) :
    splitTransportPGL K Ksep d hd A
        ((tensorAlgEquivOfAlgEquiv K Ksep A B f).trans e) σ =
      splitTransportPGL K Ksep d hd B e σ := by
  let ψ := tensorAlgEquivOfAlgEquiv K Ksep A B f
  have hn := tensorAlgEquivOfAlgEquiv_commutes_galois K Ksep A B f σ
  have hAut : splitTransportAlgAut K Ksep A d (ψ.trans e) σ =
      splitTransportAlgAut K Ksep B d e σ := by
    apply AlgEquiv.ext
    intro M
    simp [splitTransportAlgAut, splitTransportAut, ψ,
      AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
    have hnat := congrArg
      (fun g : (Ksep ⊗[K] A) ≃ₐ[K] (Ksep ⊗[K] B) =>
        g (ψ.symm (e.symm ((matrixGaloisAut K Ksep d σ).symm M))) ) hn
    simpa [ψ, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
      AlgEquiv.restrictScalars_apply] using hnat.symm
  apply (pglToMatrixAlgAutEquiv Ksep d hd).injective
  simpa [splitTransportPGL] using hAut

private theorem splitTransportAlgAut_changeBasis (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (A : Type*) [Ring A] [Algebra K A]
    (e₁ e₂ : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (b : PGL(Fin d, Ksep))
    (hb : e₂ = e₁.trans (pglToMatrixAlgAut Ksep d b))
    (σ : Ksep ≃ₐ[K] Ksep) :
    splitTransportAlgAut K Ksep A d e₂ σ =
      pglToMatrixAlgAut Ksep d b * splitTransportAlgAut K Ksep A d e₁ σ *
        pglToMatrixAlgAut Ksep d
          (Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b⁻¹) := by
  have hswap (M : Matrix (Fin d) (Fin d) Ksep) :
      (pglToMatrixAlgAut Ksep d b).symm
          ((matrixGaloisAut K Ksep d σ).symm M) =
        (matrixGaloisAut K Ksep d σ).symm
          ((pglToMatrixAlgAut Ksep d
            (Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b)).symm M) := by
    have heq :
        (AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b)).symm *
            (matrixGaloisAut K Ksep d σ).symm =
          (matrixGaloisAut K Ksep d σ).symm *
            (AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d
              (Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b))).symm := by
      simp_rw [← AlgEquiv.aut_inv]
      rw [pglToMatrixAlgAut_map]
      simp_rw [← AlgEquiv.aut_inv]
      group
    simpa [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using DFunLike.congr_fun heq M
  apply AlgEquiv.ext
  intro M
  simp [splitTransportAlgAut, splitTransportAut, hb, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.mul_apply, hswap, mul_assoc]

private theorem splitPGLCocycle_changeBasis (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A : Type*) [Ring A] [Algebra K A]
    (e₁ e₂ : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep) :
    PGLCocycle.IsCohomologous (splitPGLCocycle K Ksep d hd A e₁)
      (splitPGLCocycle K Ksep d hd A e₂) := by
  obtain ⟨b, hb, -⟩ :=
    centralSimpleAlgebra_splitEquiv_change_basis Ksep d hd (Ksep ⊗[K] A) e₁ e₂
  refine ⟨b⁻¹, ?_⟩
  intro σ
  change splitTransportPGL K Ksep d hd A e₂ σ =
    (b⁻¹)⁻¹ * splitTransportPGL K Ksep d hd A e₁ σ *
      Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom (b⁻¹)
  apply (pglToMatrixAlgAutEquiv Ksep d hd).injective
  rw [(pglToMatrixAlgAutEquiv Ksep d hd).map_mul,
    (pglToMatrixAlgAutEquiv Ksep d hd).map_mul]
  simp only [splitTransportPGL,
    (pglToMatrixAlgAutEquiv Ksep d hd).apply_symm_apply,
    pglToMatrixAlgAutEquiv_apply, inv_inv, map_inv]
  change splitTransportAlgAut K Ksep A d e₂ σ =
    pglToMatrixAlgAut Ksep d b * (splitTransportAlgAut K Ksep A d e₁ σ *
      (pglToMatrixAlgAut Ksep d
        (Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b))⁻¹)
  simpa [map_inv, mul_assoc] using splitTransportAlgAut_changeBasis K Ksep d A e₁ e₂ b hb σ

private theorem centralSimpleAlgebraOfDegree_splits (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (A : CentralSimpleAlgebraOfDegree.{u, v} K d) :
    Algebra.IsSplit K A.1 Ksep := by
  let Kbar := AlgebraicClosure K
  let Ksep' := separableClosure K Kbar
  have hTFAE := Algebra.isCentralSimple_tfae K A.1 Kbar
  have hCSA : Module.Finite K A.1 ∧ Algebra.IsCentral K A.1 ∧ IsSimpleRing A.1 :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hsplit : Algebra.IsSplit K A.1 Ksep' := (hTFAE.out 1 4).mp hCSA
  let e : Ksep' ≃ₐ[K] Ksep := IsSepClosure.equiv K Ksep' Ksep
  exact Algebra.IsSplit.of_algEquiv' Ksep' Ksep hsplit e

private theorem centralSimpleAlgebraOfDegree_splitEquiv (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (A : CentralSimpleAlgebraOfDegree.{u, v} K d) :
    Nonempty ((Ksep ⊗[K] A.1) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := centralSimpleAlgebraOfDegree_splits K Ksep d A
  have hsize : n = d := by
    rw [Algebra.IsSplit.matrix_size_eq_degree Ksep e]
    exact A.2
  exact ⟨e.trans (Matrix.reindexAlgEquiv Ksep Ksep (Fin.castOrderIso hsize).toEquiv)⟩

private noncomputable def centralSimpleAlgebraOfDegree_cocycle (K : Type u)
    [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A : CentralSimpleAlgebraOfDegree.{u, v} K d) : PGLCocycle K Ksep d :=
  splitPGLCocycle K Ksep d hd A.1
    (Classical.choice (centralSimpleAlgebraOfDegree_splitEquiv K Ksep d A))

private theorem centralSimpleAlgebraOfDegree_cocycle_changeSplit (K : Type u)
    [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A : CentralSimpleAlgebraOfDegree.{u, v} K d)
    (e : (Ksep ⊗[K] A.1) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep) :
    PGLCocycle.IsCohomologous
      (centralSimpleAlgebraOfDegree_cocycle K Ksep d hd A)
      (splitPGLCocycle K Ksep d hd A.1 e) :=
  splitPGLCocycle_changeBasis K Ksep d hd A.1
    (Classical.choice (centralSimpleAlgebraOfDegree_splitEquiv K Ksep d A)) e

private theorem centralSimpleAlgebraOfDegree_cocycle_isomorphic (K : Type u)
    [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (d : ℕ) (hd : d ≠ 0)
    (A B : CentralSimpleAlgebraOfDegree.{u, v} K d)
    (f : A.1 ≃ₐ[K] B.1) :
    PGLCocycle.IsCohomologous
      (centralSimpleAlgebraOfDegree_cocycle K Ksep d hd A)
      (centralSimpleAlgebraOfDegree_cocycle K Ksep d hd B) := by
  classical
  let eB := Classical.choice (centralSimpleAlgebraOfDegree_splitEquiv K Ksep d B)
  let ψ := tensorAlgEquivOfAlgEquiv K Ksep A.1 B.1 f
  let eA := ψ.trans eB
  have hA := centralSimpleAlgebraOfDegree_cocycle_changeSplit K Ksep d hd A eA
  have hAB : PGLCocycle.IsCohomologous
      (splitPGLCocycle K Ksep d hd A.1 eA)
      (splitPGLCocycle K Ksep d hd B.1 eB) := by
    refine ⟨1, ?_⟩
    intro σ
    simp only [splitPGLCocycle]
    rw [splitTransportPGL_congr]
    simp
  have hB := centralSimpleAlgebraOfDegree_cocycle_changeSplit K Ksep d hd B eB
  let hrel := pglCocycle_isCohomologous_equivalence K Ksep d
  exact hrel.trans (hrel.trans hA hAB) (hrel.symm hB)

/-- The pointed set `H¹(Gal(Ksep/K), PGL_d(Ksep))`, presented as continuous
crossed homomorphisms modulo coboundaries. -/
@[sga "3 XVII 5.1.1" "special case", sga "4½ Arcata 3.1.2" "the pointed set H¹(G"]
def PGLH1 (K : Type u) [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    (d : ℕ) :=
  Quotient (Relation.EqvGen.setoid (PGLCocycle.IsCohomologous (K := K) (Ksep := Ksep)
    (d := d)))

@[sga "4½ Arcata 3.1.2"]
private noncomputable def centralSimpleAlgebraClassToPGLH1 (K : Type u)
    [Field K] (Ksep : Type v) [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (d : ℕ) (hd : d ≠ 0) :
    CentralSimpleAlgebraClass.{u, v} K d → PGLH1 K Ksep d :=
  Quotient.lift
    (fun A => Quotient.mk _ (centralSimpleAlgebraOfDegree_cocycle K Ksep d hd A))
    (by
      intro A B h
      have hiso := (centralSimpleAlgebraClass_relation_iff K d A B).mp h
      obtain ⟨f⟩ := hiso
      apply Quotient.sound
      exact @Relation.EqvGen.rel (PGLCocycle K Ksep d)
        (PGLCocycle.IsCohomologous (K := K) (Ksep := Ksep) (d := d))
        (centralSimpleAlgebraOfDegree_cocycle K Ksep d hd A)
        (centralSimpleAlgebraOfDegree_cocycle K Ksep d hd B)
        (centralSimpleAlgebraOfDegree_cocycle_isomorphic K Ksep d hd A B f))

private def cocycleMatrixGaloisAut (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d) (σ : Ksep ≃ₐ[K] Ksep) :
    Matrix (Fin d) (Fin d) Ksep ≃ₐ[K] Matrix (Fin d) (Fin d) Ksep :=
  AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d (f.toFun σ)) *
    matrixGaloisAut K Ksep d σ

private theorem cocycleMatrixGaloisAut_algebraMap (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d) (σ : Ksep ≃ₐ[K] Ksep) (x : Ksep) :
    cocycleMatrixGaloisAut K Ksep d f σ
        (algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) x) =
      algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) (σ x) := by
  rw [cocycleMatrixGaloisAut, AlgEquiv.mul_apply,
    AlgEquiv.restrictScalars_apply, matrixGaloisAut_algebraMap]
  exact (pglToMatrixAlgAut Ksep d (f.toFun σ)).commutes (σ x)

private theorem cocycleMatrixGaloisAut_smul (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d) (σ : Ksep ≃ₐ[K] Ksep)
    (a : Ksep) (M : Matrix (Fin d) (Fin d) Ksep) :
    cocycleMatrixGaloisAut K Ksep d f σ (a • M) =
      σ a • cocycleMatrixGaloisAut K Ksep d f σ M := by
  rw [Algebra.smul_def a M,
    Algebra.smul_def (σ a) (cocycleMatrixGaloisAut K Ksep d f σ M), map_mul,
    cocycleMatrixGaloisAut_algebraMap]

private theorem cocycleMatrixGaloisAut_mul (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d) (σ τ : Ksep ≃ₐ[K] Ksep) :
    cocycleMatrixGaloisAut K Ksep d f (σ * τ) =
      cocycleMatrixGaloisAut K Ksep d f σ *
        cocycleMatrixGaloisAut K Ksep d f τ := by
  have hmap := pglToMatrixAlgAut_map K Ksep d σ (f.toFun τ)
  have hrestrict (a b : Matrix (Fin d) (Fin d) Ksep ≃ₐ[Ksep]
      Matrix (Fin d) (Fin d) Ksep) :
      AlgEquiv.restrictScalars K (a * b) =
        AlgEquiv.restrictScalars K a * AlgEquiv.restrictScalars K b := by
    apply AlgEquiv.ext
    intro x
    rfl
  simp only [cocycleMatrixGaloisAut, f.map_mul,
    map_mul, hrestrict, matrixGaloisAut_mul]
  rw [hmap]
  simp only [← AlgEquiv.aut_inv]
  group

private theorem cocycleMatrixGaloisAut_one (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d) :
    cocycleMatrixGaloisAut K Ksep d f 1 = 1 := by
  apply AlgEquiv.ext
  intro M
  refine Matrix.ext fun i j => ?_
  simp [cocycleMatrixGaloisAut, pglCocycle_map_one,
    AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, matrixGaloisAut_apply]

private def cocycleFixedMatrixAlgebra (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d) :
    Subalgebra K (Matrix (Fin d) (Fin d) Ksep) where
  carrier := { M | ∀ σ : Ksep ≃ₐ[K] Ksep,
    cocycleMatrixGaloisAut K Ksep d f σ M = M }
  mul_mem' := by
    intro a b ha hb σ
    rw [map_mul, ha σ, hb σ]
  add_mem' := by
    intro a b ha hb σ
    rw [map_add, ha σ, hb σ]
  algebraMap_mem' := by
    intro a σ
    exact (cocycleMatrixGaloisAut K Ksep d f σ).commutes a

private theorem mem_cocycleFixedMatrixAlgebra_iff (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d) (M : Matrix (Fin d) (Fin d) Ksep) :
    M ∈ cocycleFixedMatrixAlgebra K Ksep d f ↔
      ∀ σ : Ksep ≃ₐ[K] Ksep,
        cocycleMatrixGaloisAut K Ksep d f σ M = M := Iff.rfl

/-- Automorphisms with the same restriction to `L` agree on any finite set contained in `L`. -/
private theorem agree_of_restrictNormalHom_eq (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (L : FiniteGaloisIntermediateField K Ksep) (S : Finset Ksep)
    (hSL : (S : Set Ksep) ⊆ L.toIntermediateField) {σ τ : Ksep ≃ₐ[K] Ksep}
    (heq : σ.restrictNormalHom L = τ.restrictNormalHom L) : ∀ x ∈ S, σ x = τ x := by
  intro x hx
  have h := congrArg (fun e : L ≃ₐ[K] L => (e ⟨x, hSL hx⟩).1) heq
  simpa [AlgEquiv.restrictNormalHom_apply] using h

private theorem pglCocycle_finite_range (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d) : (Set.range f.toFun).Finite := by
  classical
  obtain ⟨S, hS⟩ := f.continuous
  let : Finite (S : Set Ksep) := S.finite_toSet
  let L := FiniteGaloisIntermediateField.adjoin K (S : Set Ksep)
  let r : (Ksep ≃ₐ[K] Ksep) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let lift (γ : L ≃ₐ[K] L) : Ksep ≃ₐ[K] Ksep :=
    Classical.choose (AlgEquiv.restrictNormalHom_surjective Ksep γ)
  have hlift (γ : L ≃ₐ[K] L) : r (lift γ) = γ :=
    Classical.choose_spec (AlgEquiv.restrictNormalHom_surjective Ksep γ)
  have hfactor (σ τ : Ksep ≃ₐ[K] Ksep) (heq : r σ = r τ) :
      f.toFun σ = f.toFun τ := by
    exact hS σ τ (agree_of_restrictNormalHom_eq K Ksep L S
      (FiniteGaloisIntermediateField.subset_adjoin K (S : Set Ksep)) heq)
  apply (Set.finite_range (fun γ : L ≃ₐ[K] L => f.toFun (lift γ))).subset
  rintro y ⟨σ, rfl⟩
  exact ⟨r σ, (hfactor σ (lift (r σ)) (hlift _).symm).symm⟩

private theorem pglCocycle_exists_finiteGalois_basis_field (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (f : PGLCocycle K Ksep d) :
    ∃ L : FiniteGaloisIntermediateField K Ksep,
      (∀ σ τ : Ksep ≃ₐ[K] Ksep,
        σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ) ∧
      (∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
        (pglToMatrixAlgAut Ksep d (f.toFun σ)
          (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) := by
  classical
  obtain ⟨S, hS⟩ := f.continuous
  let R : Set (PGL(Fin d, Ksep)) := Set.range f.toFun
  have hR : R.Finite := pglCocycle_finite_range K Ksep d f
  let C : Set Ksep := Set.range (fun p :
      ((R × (Fin d × Fin d)) × (Fin d × Fin d)) =>
        (pglToMatrixAlgAut Ksep d p.1.1.1
          (Matrix.stdBasis Ksep (Fin d) (Fin d) p.1.2)) p.2.1 p.2.2)
  let : Finite R := hR
  have hC : C.Finite := Set.finite_range _
  have hSC : ((S : Set Ksep) ∪ C).Finite := S.finite_toSet.union hC
  let : Finite (↥((S : Set Ksep) ∪ C)) := hSC
  let L := FiniteGaloisIntermediateField.adjoin K ((S : Set Ksep) ∪ C)
  have hSL : (S : Set Ksep) ⊆ L.toIntermediateField :=
    Set.Subset.trans Set.subset_union_left
      (FiniteGaloisIntermediateField.subset_adjoin K ((S : Set Ksep) ∪ C))
  have hCL : C ⊆ L.toIntermediateField :=
    Set.Subset.trans Set.subset_union_right
      (FiniteGaloisIntermediateField.subset_adjoin K ((S : Set Ksep) ∪ C))
  refine ⟨L, ?_, ?_⟩
  · intro σ τ heq
    exact hS σ τ (agree_of_restrictNormalHom_eq K Ksep L S hSL heq)
  · intro σ ij kl
    apply hCL
    exact ⟨(((⟨f.toFun σ, ⟨σ, rfl⟩⟩ : R), ij), kl), rfl⟩

private theorem cocycleMatrixGaloisAut_preserves_finiteGalois_matrix (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) (M : Matrix (Fin d) (Fin d) Ksep)
    (hM : ∀ i j, M i j ∈ L.toIntermediateField) :
    ∀ i j, (cocycleMatrixGaloisAut K Ksep d f σ M) i j ∈ L.toIntermediateField := by
  classical
  have hdecomp : M = ∑ i : Fin d, ∑ j : Fin d,
      M i j • Matrix.stdBasis Ksep (Fin d) (Fin d) (i, j) := by
    ext i j
    simpa [Matrix.sum_apply, Matrix.stdBasis_eq_single] using
      congrFun (congrFun (Matrix.matrix_eq_sum_single M) i) j
  rw [hdecomp]
  intro a b
  simp only [map_sum, Matrix.sum_apply, cocycleMatrixGaloisAut_smul,
    Matrix.smul_apply]
  apply L.toIntermediateField.sum_mem
  intro i _
  apply L.toIntermediateField.sum_mem
  intro j _
  apply L.toIntermediateField.mul_mem
  · have hx := ((σ.restrictNormalHom L) ⟨M i j, hM i j⟩).2
    simpa [AlgEquiv.restrictNormalHom_apply] using hx
  · simpa [cocycleMatrixGaloisAut, AlgEquiv.mul_apply,
      AlgEquiv.restrictScalars_apply, matrixGaloisAut_apply,
      Matrix.stdBasis_eq_single] using hcoeff σ (i, j) (a, b)

private def finiteGaloisMatrixInclusion (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (L : FiniteGaloisIntermediateField K Ksep) :
    Matrix (Fin d) (Fin d) L →ₐ[K] Matrix (Fin d) (Fin d) Ksep :=
  (IsScalarTower.toAlgHom K L Ksep).mapMatrix

private theorem finiteGaloisMatrixInclusion_injective (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (L : FiniteGaloisIntermediateField K Ksep) :
    Function.Injective (finiteGaloisMatrixInclusion K Ksep d L) := by
  intro M N h
  ext i j
  have hij := congrArg (fun X : Matrix (Fin d) (Fin d) Ksep => X i j) h
  simpa [finiteGaloisMatrixInclusion] using hij

private def finiteGaloisMatrixActionFun (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) (M : Matrix (Fin d) (Fin d) L) :
    Matrix (Fin d) (Fin d) L :=
  fun i j => ⟨(cocycleMatrixGaloisAut K Ksep d f σ
    (finiteGaloisMatrixInclusion K Ksep d L M)) i j,
      cocycleMatrixGaloisAut_preserves_finiteGalois_matrix K Ksep d f L hcoeff σ _
        (fun a b => (M a b).2) i j⟩

private theorem finiteGaloisMatrixInclusion_actionFun (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) (M : Matrix (Fin d) (Fin d) L) :
    finiteGaloisMatrixInclusion K Ksep d L
        (finiteGaloisMatrixActionFun K Ksep d f L hcoeff σ M) =
      cocycleMatrixGaloisAut K Ksep d f σ
        (finiteGaloisMatrixInclusion K Ksep d L M) := by
  ext i j
  rfl

private def finiteGaloisMatrixAction (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) :
    Matrix (Fin d) (Fin d) L →ₐ[K] Matrix (Fin d) (Fin d) L where
  toFun := finiteGaloisMatrixActionFun K Ksep d f L hcoeff σ
  map_one' := by
    apply finiteGaloisMatrixInclusion_injective K Ksep d L
    simp [finiteGaloisMatrixInclusion_actionFun]
  map_mul' M N := by
    apply finiteGaloisMatrixInclusion_injective K Ksep d L
    simp [finiteGaloisMatrixInclusion_actionFun]
  map_zero' := by
    apply finiteGaloisMatrixInclusion_injective K Ksep d L
    simp [finiteGaloisMatrixInclusion_actionFun]
  map_add' M N := by
    apply finiteGaloisMatrixInclusion_injective K Ksep d L
    simp [finiteGaloisMatrixInclusion_actionFun]
  commutes' a := by
    apply finiteGaloisMatrixInclusion_injective K Ksep d L
    simp [finiteGaloisMatrixInclusion_actionFun]

private theorem finiteGaloisMatrixAction_apply (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) (M : Matrix (Fin d) (Fin d) L) :
    finiteGaloisMatrixInclusion K Ksep d L
        (finiteGaloisMatrixAction K Ksep d f L hcoeff σ M) =
      cocycleMatrixGaloisAut K Ksep d f σ
        (finiteGaloisMatrixInclusion K Ksep d L M) :=
  finiteGaloisMatrixInclusion_actionFun K Ksep d f L hcoeff σ M

private theorem finiteGaloisMatrixAction_mul (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ τ : Ksep ≃ₐ[K] Ksep) :
    finiteGaloisMatrixAction K Ksep d f L hcoeff (σ * τ) =
      (finiteGaloisMatrixAction K Ksep d f L hcoeff σ).comp
        (finiteGaloisMatrixAction K Ksep d f L hcoeff τ) := by
  apply AlgHom.ext
  intro M
  apply finiteGaloisMatrixInclusion_injective K Ksep d L
  simp only [finiteGaloisMatrixAction_apply, AlgHom.comp_apply]
  rw [cocycleMatrixGaloisAut_mul]
  rfl

private theorem finiteGaloisMatrixAction_one (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    finiteGaloisMatrixAction K Ksep d f L hcoeff 1 = AlgHom.id K _ := by
  apply AlgHom.ext
  intro M
  apply finiteGaloisMatrixInclusion_injective K Ksep d L
  simp [finiteGaloisMatrixAction_apply, cocycleMatrixGaloisAut_one]

private noncomputable def finiteGaloisMatrixActionEquiv (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) :
    Matrix (Fin d) (Fin d) L ≃ₐ[K] Matrix (Fin d) (Fin d) L :=
  AlgEquiv.ofBijective (finiteGaloisMatrixAction K Ksep d f L hcoeff σ) (by
    constructor
    · intro M N h
      apply finiteGaloisMatrixInclusion_injective K Ksep d L
      apply (cocycleMatrixGaloisAut K Ksep d f σ).injective
      simpa only [finiteGaloisMatrixAction_apply] using
        congrArg (finiteGaloisMatrixInclusion K Ksep d L) h
    · intro N
      refine ⟨finiteGaloisMatrixAction K Ksep d f L hcoeff σ⁻¹ N, ?_⟩
      simpa [finiteGaloisMatrixAction_one] using
        (DFunLike.congr_fun (finiteGaloisMatrixAction_mul K Ksep d f L hcoeff σ σ⁻¹) N).symm)

private theorem finiteGaloisMatrixAction_congr (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ τ : Ksep ≃ₐ[K] Ksep)
    (hστ : σ.restrictNormalHom L = τ.restrictNormalHom L) :
    finiteGaloisMatrixAction K Ksep d f L hcoeff σ =
      finiteGaloisMatrixAction K Ksep d f L hcoeff τ := by
  apply AlgHom.ext
  intro M
  apply finiteGaloisMatrixInclusion_injective K Ksep d L
  simp only [finiteGaloisMatrixAction_apply]
  have hmat : matrixGaloisAut K Ksep d σ
        (finiteGaloisMatrixInclusion K Ksep d L M) =
      matrixGaloisAut K Ksep d τ
        (finiteGaloisMatrixInclusion K Ksep d L M) := by
    ext i j
    have h := congrArg (fun e : L ≃ₐ[K] L =>
      (e (M i j)).1) hστ
    simpa [finiteGaloisMatrixInclusion, matrixGaloisAut_apply,
      AlgEquiv.restrictNormalHom_apply] using h
  simp only [cocycleMatrixGaloisAut, AlgEquiv.mul_apply,
    AlgEquiv.restrictScalars_apply, hfactor σ τ hστ, hmat]

private noncomputable def finiteGaloisMatrixActionHomRaw (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    (Ksep ≃ₐ[K] Ksep) →* (Matrix (Fin d) (Fin d) L ≃ₐ[K]
      Matrix (Fin d) (Fin d) L) where
  toFun := finiteGaloisMatrixActionEquiv K Ksep d f L hcoeff
  map_one' := by
    apply AlgEquiv.ext
    intro M
    exact DFunLike.congr_fun (finiteGaloisMatrixAction_one K Ksep d f L hcoeff) M
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro M
    exact DFunLike.congr_fun (finiteGaloisMatrixAction_mul K Ksep d f L hcoeff σ τ) M

private noncomputable def finiteGaloisMatrixActionHom (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField) :
    (L ≃ₐ[K] L) →* (Matrix (Fin d) (Fin d) L ≃ₐ[K]
      Matrix (Fin d) (Fin d) L) := by
  let r : (Ksep ≃ₐ[K] Ksep) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let lift (γ : L ≃ₐ[K] L) : Ksep ≃ₐ[K] Ksep :=
    Classical.choose (AlgEquiv.restrictNormalHom_surjective Ksep γ)
  have hlift : Function.RightInverse lift r := fun γ =>
    Classical.choose_spec (AlgEquiv.restrictNormalHom_surjective Ksep γ)
  let g := finiteGaloisMatrixActionHomRaw K Ksep d f L hcoeff
  have hker : r.ker ≤ g.ker := by
    intro σ hσ
    change r σ = 1 at hσ
    change g σ = 1
    have hσ' : σ.restrictNormalHom L = (1 : Ksep ≃ₐ[K] Ksep).restrictNormalHom L := by
      simpa [r] using hσ
    have hc := finiteGaloisMatrixAction_congr K Ksep d f L hfactor hcoeff σ 1 hσ'
    apply AlgEquiv.ext
    intro M
    change (finiteGaloisMatrixAction K Ksep d f L hcoeff σ) M = M
    simpa [finiteGaloisMatrixAction_one] using DFunLike.congr_fun hc M
  exact r.liftOfRightInverseAux lift hlift g hker

private theorem finiteGaloisMatrixActionHom_restrict (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ)
    (f : PGLCocycle K Ksep d)
    (L : FiniteGaloisIntermediateField K Ksep)
    (hfactor : ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      σ.restrictNormalHom L = τ.restrictNormalHom L → f.toFun σ = f.toFun τ)
    (hcoeff : ∀ σ : Ksep ≃ₐ[K] Ksep, ∀ ij kl : Fin d × Fin d,
      (pglToMatrixAlgAut Ksep d (f.toFun σ)
        (Matrix.stdBasis Ksep (Fin d) (Fin d) ij)) kl.1 kl.2 ∈ L.toIntermediateField)
    (σ : Ksep ≃ₐ[K] Ksep) :
    finiteGaloisMatrixActionHom K Ksep d f L hfactor hcoeff
        (σ.restrictNormalHom L) =
      finiteGaloisMatrixActionHomRaw K Ksep d f L hcoeff σ := by
  simp [finiteGaloisMatrixActionHom]

end
