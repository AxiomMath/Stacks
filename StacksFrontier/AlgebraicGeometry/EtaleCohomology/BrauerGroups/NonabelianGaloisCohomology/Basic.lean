module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Algebra.Split.CentralSimple
public import StacksCore.RingTheory.SkolemNoether
public import StacksCore.Tactic.StacksAttribute

/-!
# Central simple algebras of fixed degree and `PGL_d`-valued Galois cocycles

This file defines the type `CentralSimpleAlgebraOfDegree` of central simple algebras of a fixed
degree and its set of isomorphism classes `CentralSimpleAlgebraClass`, the type `PGLCocycle` of
continuous crossed homomorphisms with values in a projective general linear group with the
coboundary relation `PGLCocycle.IsCohomologous`, and identifies `PGL_d(L)` with the automorphism
group of the matrix algebra `M_d(L)` via Skolem–Noether. It also sets up the Galois actions on
`Ksep ⊗[K] A` and on `M_d(Ksep)`, and their transport along a splitting of `A`.
-/

open scoped MatrixGroups TensorProduct

universe u v

@[expose] public section

/-- A central simple algebra over `K` whose degree is `d`. -/
def CentralSimpleAlgebraOfDegree (K : Type u) [Field K] (d : ℕ) :=
  { A : CSA.{u, v} K // Algebra.IsCentralSimple.degree K A = d }

/-- Isomorphism of central simple algebras of a fixed degree. -/
def CentralSimpleAlgebraOfDegree.IsIsomorphic {K : Type u} [Field K] {d : ℕ}
    (A B : CentralSimpleAlgebraOfDegree.{u, v} K d) : Prop :=
  Nonempty (A.1 ≃ₐ[K] B.1)

/-- The set of isomorphism classes of degree-`d` central simple `K`-algebras. -/
@[sga "4½ Arcata 3.1.2"]
def CentralSimpleAlgebraClass (K : Type u) [Field K] (d : ℕ) :=
  Quotient (Relation.EqvGen.setoid
    (CentralSimpleAlgebraOfDegree.IsIsomorphic (K := K) (d := d)))

private theorem centralSimpleAlgebraOfDegree_isIsomorphic_equivalence
    (K : Type u) [Field K] (d : ℕ) :
    Equivalence (CentralSimpleAlgebraOfDegree.IsIsomorphic (K := K) (d := d)) where
  refl _A := ⟨AlgEquiv.refl⟩
  symm h := h.elim fun e => ⟨e.symm⟩
  trans h₁ h₂ := h₁.elim fun e₁ => h₂.elim fun e₂ => ⟨e₁.trans e₂⟩

private theorem centralSimpleAlgebraClass_relation_iff
    (K : Type u) [Field K] (d : ℕ)
    (A B : CentralSimpleAlgebraOfDegree.{u, v} K d) :
    Relation.EqvGen (CentralSimpleAlgebraOfDegree.IsIsomorphic (K := K) (d := d)) A B ↔
      CentralSimpleAlgebraOfDegree.IsIsomorphic A B :=
  (centralSimpleAlgebraOfDegree_isIsomorphic_equivalence K d).eqvGen_iff

private theorem centralSimpleAlgebraClass_mk_eq_iff
    (K : Type u) [Field K] (d : ℕ)
    (A B : CentralSimpleAlgebraOfDegree.{u, v} K d) :
    (Quotient.mk (Relation.EqvGen.setoid
      (CentralSimpleAlgebraOfDegree.IsIsomorphic (K := K) (d := d))) A =
        Quotient.mk (Relation.EqvGen.setoid
          (CentralSimpleAlgebraOfDegree.IsIsomorphic (K := K) (d := d))) B) ↔
      CentralSimpleAlgebraOfDegree.IsIsomorphic A B := by
  rw [Quotient.eq]
  exact centralSimpleAlgebraClass_relation_iff K d A B

/-- A continuous nonabelian `1`-cocycle of the absolute Galois group of `K`
with values in `PGL_d(Ksep)`.  Continuity is for the Krull topology on the
Galois group and the discrete topology on `PGL_d(Ksep)`. -/
structure PGLCocycle (K : Type u) [Field K] (Ksep : Type v) [Field Ksep]
    [Algebra K Ksep] (d : ℕ) where
  /-- The underlying map from the absolute Galois group. -/
  toFun : (Ksep ≃ₐ[K] Ksep) → PGL(d, Ksep)
  /-- The crossed-homomorphism identity. -/
  map_mul : ∀ σ τ,
    toFun (σ * τ) = toFun σ * Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom (toFun τ)
  /-- The map is locally constant for the Krull topology. -/
  continuous : ∃ S : Finset Ksep, ∀ σ τ : Ksep ≃ₐ[K] Ksep,
    (∀ x ∈ S, σ x = τ x) → toFun σ = toFun τ

private theorem pglCocycle_map_one (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (d : ℕ) (f : PGLCocycle K Ksep d) :
    f.toFun 1 = 1 := by
  have h := f.map_mul 1 1
  have hId : (1 : Ksep ≃ₐ[K] Ksep).toRingHom = RingHom.id Ksep := by
    ext x
    rfl
  rw [hId, Matrix.ProjGenLinGroup.map_id] at h
  have h' : f.toFun 1 = f.toFun 1 * f.toFun 1 := by simpa using h
  have h'' : f.toFun 1 * 1 = f.toFun 1 * f.toFun 1 := by simpa using h'
  exact (mul_left_cancel h'').symm

/-- The elementary coboundary relation between `PGL_d`-valued Galois cocycles. -/
def PGLCocycle.IsCohomologous {K : Type u} [Field K] {Ksep : Type v} [Field Ksep]
    [Algebra K Ksep] {d : ℕ} (f g : PGLCocycle K Ksep d) : Prop :=
  ∃ b : PGL(d, Ksep), ∀ σ : Ksep ≃ₐ[K] Ksep,
    g.toFun σ = b⁻¹ * f.toFun σ * Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b

private theorem pglCocycle_isCohomologous_equivalence (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ) :
    Equivalence (PGLCocycle.IsCohomologous (K := K) (Ksep := Ksep) (d := d)) := by
  constructor
  · exact fun f => ⟨1, fun σ => by simp⟩
  · rintro f g ⟨b, hb⟩
    refine ⟨b⁻¹, fun σ => ?_⟩
    calc
      f.toFun σ = b * (b⁻¹ * f.toFun σ *
          Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b) *
          Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom b⁻¹ := by simp [mul_assoc]
      _ = (b⁻¹)⁻¹ * g.toFun σ *
          Matrix.ProjGenLinGroup.map σ.toRingEquiv.toRingHom (b⁻¹) := by
        rw [← hb σ]
        simp [mul_assoc]
  · rintro f g h ⟨b, hb⟩ ⟨c, hc⟩
    refine ⟨b * c, fun σ => ?_⟩
    rw [hc σ, hb σ]
    simp [mul_assoc]

private theorem pglH1_relation_iff (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (d : ℕ) (f g : PGLCocycle K Ksep d) :
    Relation.EqvGen (PGLCocycle.IsCohomologous (K := K) (Ksep := Ksep) (d := d)) f g ↔
      PGLCocycle.IsCohomologous f g :=
  (pglCocycle_isCohomologous_equivalence K Ksep d).eqvGen_iff

private theorem pglH1_mk_eq_iff (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (d : ℕ) (f g : PGLCocycle K Ksep d) :
    (Quotient.mk (Relation.EqvGen.setoid
      (PGLCocycle.IsCohomologous (K := K) (Ksep := Ksep) (d := d))) f =
        Quotient.mk (Relation.EqvGen.setoid
          (PGLCocycle.IsCohomologous (K := K) (Ksep := Ksep) (d := d))) g) ↔
      PGLCocycle.IsCohomologous f g := by
  rw [Quotient.eq]
  exact pglH1_relation_iff K Ksep d f g

private def pglToMatrixAlgAut (L : Type*) [Field L] (d : ℕ) :
    PGL(Fin d, L) →* (Matrix (Fin d) (Fin d) L ≃ₐ[L] Matrix (Fin d) (Fin d) L) := by
  let A := Matrix (Fin d) (Fin d) L
  let f : GL (Fin d) L →* (A ≃ₐ[L] A) :=
    (MulSemiringAction.toAlgAut (ConjAct Aˣ) L A).comp ConjAct.toConjAct.toMonoidHom
  have hf : f.comp (Matrix.GeneralLinearGroup.scalar (Fin d)) = 1 := by
    apply MonoidHom.ext
    intro u
    apply AlgEquiv.ext
    intro x
    change (ConjAct.toConjAct ((Matrix.GeneralLinearGroup.scalar (Fin d)) u) • x) = x
    rw [ConjAct.units_smul_def]
    simp only [ConjAct.ofConjAct_toConjAct]
    rw [Matrix.GeneralLinearGroup.coe_inv]
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change Matrix.diagonal (fun _ : Fin d => (u : L)) * x *
      (Matrix.diagonal (fun _ : Fin d => (u : L)))⁻¹ = x
    have hc : Commute (Matrix.scalar (Fin d) (u : L)) x :=
      Matrix.scalar_commute _ (fun y => Commute.all _ y) x
    have hprod : Matrix.scalar (Fin d) (u : L) *
        (Matrix.scalar (Fin d) (u : L))⁻¹ = 1 := by
      simp [Matrix.scalar_apply]
    calc
      Matrix.scalar (Fin d) (u : L) * x * (Matrix.scalar (Fin d) (u : L))⁻¹ =
          x * Matrix.scalar (Fin d) (u : L) * (Matrix.scalar (Fin d) (u : L))⁻¹ := by
        rw [hc.eq]
      _ = x := by rw [mul_assoc, hprod, mul_one]
  exact Matrix.ProjGenLinGroup.lift f hf

private theorem pglToMatrixAlgAut_surjective (L : Type*) [Field L] (d : ℕ)
    (hd : d ≠ 0) : Function.Surjective (pglToMatrixAlgAut L d) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  intro e
  obtain ⟨u, hu⟩ := skolemNoether' L (Matrix (Fin d) (Fin d) L) e
  refine ⟨Matrix.ProjGenLinGroup.mk u, ?_⟩
  apply AlgEquiv.ext
  intro x
  rw [pglToMatrixAlgAut, Matrix.ProjGenLinGroup.lift_mk]
  exact (hu x).symm

private theorem pglToMatrixAlgAut_mk_apply (L : Type*) [Field L] (d : ℕ)
    (g : GL (Fin d) L) (x : Matrix (Fin d) (Fin d) L) :
    pglToMatrixAlgAut L d (Matrix.ProjGenLinGroup.mk g) x =
      (g : Matrix (Fin d) (Fin d) L) * x * (g⁻¹ : Matrix (Fin d) (Fin d) L) := by
  simp [pglToMatrixAlgAut, Matrix.ProjGenLinGroup.lift_mk, ConjAct.units_smul_def]

private theorem pglToMatrixAlgAut_injective (L : Type*) [Field L] (d : ℕ) :
    Function.Injective (pglToMatrixAlgAut L d) := by
  intro a b hab
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  obtain ⟨h, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective b
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff'.2
  have heq (x : Matrix (Fin d) (Fin d) L) :
      (g : Matrix (Fin d) (Fin d) L) * x * (g⁻¹ : Matrix (Fin d) (Fin d) L) =
        (h : Matrix (Fin d) (Fin d) L) * x * (h⁻¹ : Matrix (Fin d) (Fin d) L) := by
    have hx := congrArg (fun e : Matrix (Fin d) (Fin d) L ≃ₐ[L] _ => e x) hab
    simpa only [pglToMatrixAlgAut_mk_apply] using hx
  have hz : g⁻¹ * h ∈ Subgroup.center (GL (Fin d) L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Units.ext
    calc
      w * (↑(g⁻¹ * h) : Matrix (Fin d) (Fin d) L) =
          (↑g⁻¹ : Matrix (Fin d) (Fin d) L) *
            ((g : Matrix (Fin d) (Fin d) L) * w * (g⁻¹ : Matrix (Fin d) (Fin d) L)) * h := by
              simp [mul_assoc]
      _ = (↑g⁻¹ : Matrix (Fin d) (Fin d) L) *
            ((h : Matrix (Fin d) (Fin d) L) * w * (h⁻¹ : Matrix (Fin d) (Fin d) L)) * h := by
              rw [heq]
      _ = (↑g⁻¹ : Matrix (Fin d) (Fin d) L) * h * w *
          (((h : Matrix (Fin d) (Fin d) L)⁻¹) * h) := by
            simp only [mul_assoc]
      _ = (↑(g⁻¹ * h) : Matrix (Fin d) (Fin d) L) * w := by
            simp [mul_assoc]
  exact ⟨g⁻¹ * h, hz, by simp⟩

@[sga "4½ Arcata 3.1.2" "more general"]
private noncomputable def pglToMatrixAlgAutEquiv (L : Type*) [Field L] (d : ℕ)
    (hd : d ≠ 0) :
    PGL(Fin d, L) ≃* (Matrix (Fin d) (Fin d) L ≃ₐ[L] Matrix (Fin d) (Fin d) L) :=
  MulEquiv.ofBijective (pglToMatrixAlgAut L d)
    ⟨pglToMatrixAlgAut_injective L d, pglToMatrixAlgAut_surjective L d hd⟩

private theorem pglToMatrixAlgAutEquiv_apply (L : Type*) [Field L] (d : ℕ)
    (hd : d ≠ 0) (b : PGL(Fin d, L)) :
    pglToMatrixAlgAutEquiv L d hd b = pglToMatrixAlgAut L d b := rfl

private theorem centralSimpleAlgebra_splitEquiv_change_basis (L : Type*) [Field L]
    (d : ℕ) (hd : d ≠ 0) (T : Type*) [Ring T] [Algebra L T]
    (e₁ e₂ : T ≃ₐ[L] Matrix (Fin d) (Fin d) L) :
    ∃! b : PGL(Fin d, L), e₂ = e₁.trans (pglToMatrixAlgAut L d b) := by
  let b := (pglToMatrixAlgAutEquiv L d hd).symm (e₁.symm.trans e₂)
  have hb : pglToMatrixAlgAut L d b = e₁.symm.trans e₂ :=
    (pglToMatrixAlgAutEquiv L d hd).apply_symm_apply _
  refine ⟨b, ?_, ?_⟩
  · apply AlgEquiv.ext
    intro x
    have hx := congrArg (fun f : Matrix (Fin d) (Fin d) L ≃ₐ[L]
        Matrix (Fin d) (Fin d) L => f (e₁ x)) hb
    simpa using hx.symm
  · intro c hc
    apply pglToMatrixAlgAut_injective L d
    have h₁ : e₁.symm.trans e₂ = pglToMatrixAlgAut L d b := by rw [hb]
    have h₂ : e₁.symm.trans e₂ = pglToMatrixAlgAut L d c := by
      calc
        e₁.symm.trans e₂ = e₁.symm.trans (e₁.trans (pglToMatrixAlgAut L d c)) := by rw [hc]
        _ = pglToMatrixAlgAut L d c := by
          apply AlgEquiv.ext
          intro x
          simp
    calc
      pglToMatrixAlgAut L d c = e₁.symm.trans e₂ := h₂.symm
      _ = pglToMatrixAlgAut L d b := h₁

private def tensorGaloisAut (K : Type u) [Field K] (Ksep : Type v) [Field Ksep]
    [Algebra K Ksep] (A : Type*) [Ring A] [Algebra K A]
    (σ : Ksep ≃ₐ[K] Ksep) :
    (Ksep ⊗[K] A) ≃ₐ[K] (Ksep ⊗[K] A) :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := K) (A₁ := A))

@[simp] private theorem tensorGaloisAut_tmul (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A]
    [Algebra K A] (σ : Ksep ≃ₐ[K] Ksep) (x : Ksep) (a : A) :
    tensorGaloisAut K Ksep A σ (x ⊗ₜ[K] a) = σ x ⊗ₜ[K] a := by
  simp [tensorGaloisAut]

@[simp] private theorem tensorGaloisAut_algebraMap (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A]
    [Algebra K A] (σ : Ksep ≃ₐ[K] Ksep) (x : Ksep) :
    tensorGaloisAut K Ksep A σ (algebraMap Ksep (Ksep ⊗[K] A) x) =
      algebraMap Ksep (Ksep ⊗[K] A) (σ x) := by
  simp [tensorGaloisAut, Algebra.TensorProduct.algebraMap_apply]

private theorem tensorGaloisAut_mul (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A] [Algebra K A]
    (σ τ : Ksep ≃ₐ[K] Ksep) :
    tensorGaloisAut K Ksep A (σ * τ) =
      tensorGaloisAut K Ksep A σ * tensorGaloisAut K Ksep A τ := by
  apply AlgEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y => simp [tensorGaloisAut]

private theorem tensorGaloisAut_eq_of_agree (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A]
    [Algebra K A] (z : Ksep ⊗[K] A) :
    ∃ S : Finset Ksep, ∀ σ τ : Ksep ≃ₐ[K] Ksep,
      (∀ x ∈ S, σ x = τ x) →
        tensorGaloisAut K Ksep A σ z = tensorGaloisAut K Ksep A τ z := by
  classical
  induction z using TensorProduct.induction_on with
  | zero =>
      refine ⟨∅, ?_⟩
      intro σ τ h
      simp
  | add x y hx hy =>
      obtain ⟨Sx, hSx⟩ := hx
      obtain ⟨Sy, hSy⟩ := hy
      refine ⟨Sx ∪ Sy, ?_⟩
      intro σ τ h
      rw [map_add, map_add]
      rw [hSx σ τ (fun z hz => h z (Finset.mem_union_left _ hz)),
        hSy σ τ (fun z hz => h z (Finset.mem_union_right _ hz))]
  | tmul x a =>
      refine ⟨{x}, ?_⟩
      intro σ τ h
      have hx := h x (Finset.mem_singleton_self x)
      simp [tensorGaloisAut, hx]

private def matrixGaloisAut (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (d : ℕ) (σ : Ksep ≃ₐ[K] Ksep) :
    Matrix (Fin d) (Fin d) Ksep ≃ₐ[K] Matrix (Fin d) (Fin d) Ksep :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv.mapMatrix) (by
    intro c
    simp only [RingEquiv.mapMatrix_apply, Matrix.algebraMap_eq_diagonal]
    change (Matrix.diagonal ((algebraMap K (Fin d → Ksep)) c)).map
      (σ : Ksep → Ksep) = _
    rw [Matrix.diagonal_map (f := σ) (map_zero σ)]
    congr 1
    funext i
    exact σ.commutes c)

@[simp] private theorem matrixGaloisAut_apply (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (σ : Ksep ≃ₐ[K] Ksep) (M : Matrix (Fin d) (Fin d) Ksep) :
    matrixGaloisAut K Ksep d σ M = M.map σ := by
  simp [matrixGaloisAut, AlgEquiv.ofRingEquiv_apply, RingEquiv.mapMatrix_apply]

private theorem matrixGaloisAut_mul (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (d : ℕ) (σ τ : Ksep ≃ₐ[K] Ksep) :
    matrixGaloisAut K Ksep d (σ * τ) =
      matrixGaloisAut K Ksep d σ * matrixGaloisAut K Ksep d τ := by
  apply AlgEquiv.ext
  intro M
  ext i j
  simp [AlgEquiv.mul_apply]

private theorem matrixGaloisAut_symm (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (d : ℕ) (σ : Ksep ≃ₐ[K] Ksep) :
    (matrixGaloisAut K Ksep d σ).symm = matrixGaloisAut K Ksep d σ.symm := by
  apply AlgEquiv.ext
  intro M
  ext i j
  simp [matrixGaloisAut, AlgEquiv.ofRingEquiv_apply, RingEquiv.mapMatrix_apply]

private theorem matrixGaloisAut_mul_symm (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (σ τ : Ksep ≃ₐ[K] Ksep) :
    (matrixGaloisAut K Ksep d σ * matrixGaloisAut K Ksep d τ).symm =
      (matrixGaloisAut K Ksep d τ).symm * (matrixGaloisAut K Ksep d σ).symm := by
  apply AlgEquiv.ext
  intro M
  apply (matrixGaloisAut K Ksep d σ * matrixGaloisAut K Ksep d τ).injective
  simp [AlgEquiv.mul_apply]

@[simp] private theorem matrixGaloisAut_algebraMap (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (σ : Ksep ≃ₐ[K] Ksep) (x : Ksep) :
    matrixGaloisAut K Ksep d σ (algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) x) =
      algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) (σ x) := by
  ext i j
  by_cases hij : i = j <;> simp [matrixGaloisAut_apply, Matrix.algebraMap_eq_diagonal,
    Pi.algebraMap_apply, hij]

private theorem matrixGaloisAut_symm_algebraMap (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (d : ℕ)
    (σ : Ksep ≃ₐ[K] Ksep) (x : Ksep) :
    (matrixGaloisAut K Ksep d σ).symm
        (algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) x) =
      algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) (σ.symm x) := by
  apply (matrixGaloisAut K Ksep d σ).injective
  calc
    matrixGaloisAut K Ksep d σ
        ((matrixGaloisAut K Ksep d σ).symm
          (algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) x)) =
        algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) x := by simp
    _ = matrixGaloisAut K Ksep d σ
        (algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) (σ.symm x)) := by
      rw [matrixGaloisAut_algebraMap]
      simp

private theorem pglToMatrixAlgAut_map (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (d : ℕ) (σ : Ksep ≃ₐ[K] Ksep)
    (b : PGL(Fin d, Ksep)) :
    AlgEquiv.restrictScalars K
        (pglToMatrixAlgAut Ksep d (Matrix.ProjGenLinGroup.map σ.toRingHom b)) =
      matrixGaloisAut K Ksep d σ *
        AlgEquiv.restrictScalars K (pglToMatrixAlgAut Ksep d b) *
        (matrixGaloisAut K Ksep d σ).symm := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective b
  have hinv : ((g⁻¹ : GL (Fin d) Ksep) : Matrix (Fin d) (Fin d) Ksep).map σ =
      (((Matrix.GeneralLinearGroup.map σ.toRingHom g : GL (Fin d) Ksep) :
        Matrix (Fin d) (Fin d) Ksep)⁻¹) := by
    have hmapval : ((g⁻¹ : GL (Fin d) Ksep) : Matrix (Fin d) (Fin d) Ksep).map σ =
        ((Matrix.GeneralLinearGroup.map σ.toRingHom g⁻¹ : GL (Fin d) Ksep) :
          Matrix (Fin d) (Fin d) Ksep) := by
      rfl
    have hunit : Matrix.GeneralLinearGroup.map σ.toRingHom g⁻¹ =
        (Matrix.GeneralLinearGroup.map σ.toRingHom g)⁻¹ :=
      map_inv (Matrix.GeneralLinearGroup.map σ.toRingHom) g
    calc
      _ = ((Matrix.GeneralLinearGroup.map σ.toRingHom g⁻¹ : GL (Fin d) Ksep) :
          Matrix (Fin d) (Fin d) Ksep) := hmapval
      _ = (((Matrix.GeneralLinearGroup.map σ.toRingHom g)⁻¹ : GL (Fin d) Ksep) :
          Matrix (Fin d) (Fin d) Ksep) := congrArg (fun u : GL (Fin d) Ksep =>
            (u : Matrix (Fin d) (Fin d) Ksep)) hunit
      _ = _ :=
        Matrix.GeneralLinearGroup.coe_inv (Matrix.GeneralLinearGroup.map σ.toRingHom g)
  apply AlgEquiv.ext
  intro x
  simp only [AlgEquiv.restrictScalars_apply, pglToMatrixAlgAut_mk_apply,
    Matrix.ProjGenLinGroup.map_mk, AlgEquiv.mul_apply,
    matrixGaloisAut_apply, matrixGaloisAut_symm]
  simp only [Matrix.map_mul]
  rw [← hinv]
  simp [Function.comp_def]

private def splitTransportAut (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A] [Algebra K A]
    (d : ℕ) (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ : Ksep ≃ₐ[K] Ksep) :
    Matrix (Fin d) (Fin d) Ksep ≃ₐ[K] Matrix (Fin d) (Fin d) Ksep :=
  ((AlgEquiv.restrictScalars K (matrixGaloisAut K Ksep d σ)).symm).trans <|
    (AlgEquiv.restrictScalars K e.symm).trans <|
      (tensorGaloisAut K Ksep A σ).trans (AlgEquiv.restrictScalars K e)

private theorem splitTransportAut_algebraMap (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A]
    [Algebra K A] (d : ℕ)
    (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ : Ksep ≃ₐ[K] Ksep) (x : Ksep) :
    splitTransportAut K Ksep A d e σ
        (algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) x) =
      algebraMap Ksep (Matrix (Fin d) (Fin d) Ksep) x := by
  simp only [splitTransportAut, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.symm_restrictScalars]
  rw [matrixGaloisAut_symm_algebraMap, (e.symm).commutes,
    tensorGaloisAut_algebraMap, AlgEquiv.apply_symm_apply]
  exact e.commutes x

private def splitTransportAlgAut (K : Type u) [Field K] (Ksep : Type v)
    [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A] [Algebra K A]
    (d : ℕ) (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ : Ksep ≃ₐ[K] Ksep) :
    Matrix (Fin d) (Fin d) Ksep ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep :=
  AlgEquiv.ofRingEquiv (f := (splitTransportAut K Ksep A d e σ).toRingEquiv)
    (splitTransportAut_algebraMap K Ksep A d e σ)

private theorem splitTransportAut_cocycle (K : Type u) [Field K]
    (Ksep : Type v) [Field Ksep] [Algebra K Ksep] (A : Type*) [Ring A]
    [Algebra K A] (d : ℕ)
    (e : (Ksep ⊗[K] A) ≃ₐ[Ksep] Matrix (Fin d) (Fin d) Ksep)
    (σ τ : Ksep ≃ₐ[K] Ksep) :
    splitTransportAut K Ksep A d e (σ * τ) =
      splitTransportAut K Ksep A d e σ * matrixGaloisAut K Ksep d σ *
        splitTransportAut K Ksep A d e τ * (matrixGaloisAut K Ksep d σ).symm := by
  apply AlgEquiv.ext
  intro M
  simp [splitTransportAut, AlgEquiv.mul_apply, tensorGaloisAut_mul,
    matrixGaloisAut_mul, matrixGaloisAut_symm,
    matrixGaloisAut_mul_symm, AlgEquiv.symm_restrictScalars,
    Function.comp_def, mul_assoc]

end
