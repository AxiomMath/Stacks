module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SemisimpleBlockDiagonal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AbsolutelyIrreducible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Linear algebra for the decomposition into stable constituents

Three facts of linear algebra about the decomposition of the pullback of an absolutely
irreducible representation to `π₁(𝔸¹_{k₀})` into constituents which stay absolutely irreducible.

## Main definitions

* `Stacks.EtaleCohomology.restrictScalarsLinearMap`: restriction of scalars of square matrices,
  as an `F`-linear map.
* `Stacks.EtaleCohomology.blockDiagRep`: a diagonal block of a block diagonal representation.
* `Stacks.EtaleCohomology.conjReindexHom`: the representation `g ↦ Q · reindex(ρ g) · Q⁻¹`.

## Main results

* `Stacks.EtaleCohomology.finrank_span_range_conj`: the dimension of the span of a family of
  matrices is invariant under conjugation.
* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_of_linearMap`: a representation obtained
  from a continuous one through a linear map of matrices has continuous restriction of scalars.
* `Stacks.EtaleCohomology.exists_intermediateField_blockDiagonal`: a family of matrices over `E`
  which is semisimple over the algebraic closure `Ē` of `E` in an algebraically closed `K` is
  conjugate, over a finite extension `E' ⊆ K` of `E`, to a block diagonal family whose blocks are
  irreducible over `K`.

## References

* Kedlaya, *Fourier transforms and p-adic Weil II*, §6.4.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece L7.
-/

@[expose] public noncomputable section

open Matrix Module

namespace Stacks.EtaleCohomology

section Conj

variable {E : Type*} [Field E] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*}

/-- **Conjugation does not change the dimension of the span of a family of matrices.** -/
public theorem finrank_span_range_conj (M : A → Matrix ι ι E) (P : GL ι E) :
    finrank E (Submodule.span E (Set.range fun a =>
      (P : Matrix ι ι E) * M a * ((P⁻¹ : GL ι E) : Matrix ι ι E))) =
      finrank E (Submodule.span E (Set.range M)) := by
  let c : Matrix ι ι E ≃ₗ[E] Matrix ι ι E :=
    { toFun := fun X => (P : Matrix ι ι E) * X * ((P⁻¹ : GL ι E) : Matrix ι ι E)
      invFun := fun X => ((P⁻¹ : GL ι E) : Matrix ι ι E) * X * (P : Matrix ι ι E)
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a X => by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        rfl
      left_inv := fun X => by
        show ((P⁻¹ : GL ι E) : Matrix ι ι E) * ((P : Matrix ι ι E) * X *
          ((P⁻¹ : GL ι E) : Matrix ι ι E)) * (P : Matrix ι ι E) = X
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      right_inv := fun X => by
        show (P : Matrix ι ι E) * (((P⁻¹ : GL ι E) : Matrix ι ι E) * X *
          (P : Matrix ι ι E)) * ((P⁻¹ : GL ι E) : Matrix ι ι E) = X
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] }
  have h : (Set.range fun a => (P : Matrix ι ι E) * M a * ((P⁻¹ : GL ι E) : Matrix ι ι E)) =
      (c : Matrix ι ι E →ₗ[E] Matrix ι ι E) '' Set.range M := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, LinearEquiv.finrank_map_eq]

end Conj

section Continuity

variable {F : Type*} [NontriviallyNormedField F] [CompleteSpace F] {E E' : Type*} [Field E]
  [Field E'] [Algebra F E] [Algebra F E'] {d d' : ℕ} (b : Module.Basis (Fin d) F E)
  (b' : Module.Basis (Fin d') F E')

/-- Restriction of scalars of square matrices, as an `F`-linear map. -/
def restrictScalarsLinearMap (m : ℕ) :
    Matrix (Fin m) (Fin m) E →ₗ[F] Matrix (Fin (m * d)) (Fin (m * d)) F where
  toFun := restrictScalarsMatrix b
  map_add' X Y := by
    ext p q
    obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
    simp only [restrictScalarsMatrix_apply, Matrix.add_apply, map_add]
  map_smul' c X := by
    ext p q
    obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
    simp only [restrictScalarsMatrix_apply, Matrix.smul_apply, map_smul, RingHom.id_apply]

omit [CompleteSpace F] in
/-- Restriction of scalars of square matrices is injective. -/
theorem restrictScalarsLinearMap_injective (m : ℕ) :
    Function.Injective (restrictScalarsLinearMap (F := F) b m) := by
  intro X Y h
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext l l'
  have := congrFun (congrFun h (finProdFinEquiv (i, l))) (finProdFinEquiv (j, l'))
  simpa only [restrictScalarsLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    restrictScalarsMatrix_apply] using this

/-- **A representation obtained from a continuous one through a linear map of matrices has
continuous restriction of scalars**: if `τ(g) = T(σ(g))` for an `F`-linear `T`, then
`Res_{b'} τ = L ∘ Res_b σ` for an `F`-linear (hence continuous) `L` between finite-dimensional
spaces. -/
public theorem continuous_restrictScalarsRep_of_linearMap {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {m n : ℕ} {σ : G →* GL (Fin m) E}
    (hσ : Continuous (restrictScalarsRep b σ)) (τ : G →* GL (Fin n) E')
    (T : Matrix (Fin m) (Fin m) E →ₗ[F] Matrix (Fin n) (Fin n) E')
    (hT : ∀ g, (τ g).val = T (σ g).val) : Continuous (restrictScalarsRep b' τ) := by
  obtain ⟨Rinv, hRinv⟩ := LinearMap.exists_leftInverse_of_injective
    (restrictScalarsLinearMap (F := F) b m)
    (LinearMap.ker_eq_bot.mpr (restrictScalarsLinearMap_injective b m))
  let L := restrictScalarsLinearMap b' n ∘ₗ T ∘ₗ Rinv
  refine continuous_restrictScalarsRep b' τ ?_
  have h : (fun g => restrictScalarsMatrix b' (τ g).val) =
      L ∘ fun g => (restrictScalarsRep b σ g).val := by
    funext g
    show restrictScalarsMatrix b' (τ g).val =
      restrictScalarsLinearMap b' n (T (Rinv (restrictScalarsLinearMap b m (σ g).val)))
    rw [← LinearMap.comp_apply Rinv, hRinv, LinearMap.id_apply, ← hT]
    rfl
  rw [h]
  exact L.continuous_of_finiteDimensional.comp (Units.continuous_val.comp hσ)

end Continuity

section BlockRep

variable {G : Type*} [Monoid G] {R : Type*} [CommRing R] {r : ℕ} {ms : Fin r → ℕ}

/-- **A diagonal block of a block diagonal representation**, as a representation. -/
def blockDiagRep (ρ : G →* Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) R)
    (hρ : ∀ g, ρ g = blockDiagonal' (blockDiag' (ρ g))) (i : Fin r) :
    G →* Matrix (Fin (ms i)) (Fin (ms i)) R where
  toFun g := blockDiag' (ρ g) i
  map_one' := by rw [map_one, blockDiag'_one]; rfl
  map_mul' g h := by
    rw [map_mul]
    conv_lhs => rw [hρ g, hρ h, ← blockDiagonal'_mul, blockDiag'_blockDiagonal']

/-- The block `i` of a block diagonal representation, at `g`, is the block `i` of `ρ g`. -/
theorem blockDiagRep_apply (ρ : G →* Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) R)
    (hρ : ∀ g, ρ g = blockDiagonal' (blockDiag' (ρ g))) (i : Fin r) (g : G) :
    blockDiagRep ρ hρ i g = blockDiag' (ρ g) i :=
  rfl

end BlockRep

section ConjHom

variable {G : Type*} [Monoid G] {R : Type*} [CommRing R] {m : ℕ} {κ : Type*} [Fintype κ]
  [DecidableEq κ]

/-- The representation `g ↦ Q · reindex(ρ g) · Q⁻¹`. -/
def conjReindexHom (ρ : G →* Matrix (Fin m) (Fin m) R) (eqv : Fin m ≃ κ) (Q : GL κ R) :
    G →* Matrix κ κ R where
  toFun g := (Q : Matrix κ κ R) * reindex eqv eqv (ρ g) * ((Q⁻¹ : GL κ R) : Matrix κ κ R)
  map_one' := by
    rw [map_one, reindex_apply, submatrix_one_equiv, Matrix.mul_one, Units.mul_inv]
  map_mul' g h := by
    rw [map_mul, ← Matrix.reindexAlgEquiv_apply R R, map_mul, Matrix.reindexAlgEquiv_apply,
      Matrix.reindexAlgEquiv_apply]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((Q⁻¹ : GL κ R) : Matrix κ κ R) (Q : Matrix κ κ R), Units.inv_mul,
      Matrix.one_mul]

/-- The value of `conjReindexHom ρ eqv Q` at `g` is `Q · reindex(ρ g) · Q⁻¹`. -/
theorem conjReindexHom_apply (ρ : G →* Matrix (Fin m) (Fin m) R) (eqv : Fin m ≃ κ) (Q : GL κ R)
    (g : G) : conjReindexHom ρ eqv Q g =
      (Q : Matrix κ κ R) * reindex eqv eqv (ρ g) * ((Q⁻¹ : GL κ R) : Matrix κ κ R) :=
  rfl

end ConjHom

section Descent

variable {E K : Type*} [Field E] [Field K] [Algebra E K] [IsAlgClosed K] {A : Type*} {m : ℕ}

/-- **A block diagonal form over a finite extension with blocks irreducible over `K`.** If a
family `X : A → Matrix (Fin m) (Fin m) E` is semisimple over the algebraic closure `Ē` of `E` in
an algebraically closed `K`, there are a finite extension `E'` of `E` in `K`, a decomposition
`Fin m ≃ Σ i, Fin (ms i)` and an invertible `Q` over `E'` such that every `Q (X a) Q⁻¹` is block
diagonal, with blocks irreducible over `K`. -/
public theorem exists_intermediateField_blockDiagonal (X : A → Matrix (Fin m) (Fin m) E)
    (hss : ∀ W : Submodule (algebraicClosure E K) (Fin m → algebraicClosure E K),
      (∀ a, ∀ v ∈ W, (X a).map (algebraMap E (algebraicClosure E K)) *ᵥ v ∈ W) →
      ∃ W', IsCompl W W' ∧
        ∀ a, ∀ v ∈ W', (X a).map (algebraMap E (algebraicClosure E K)) *ᵥ v ∈ W') :
    ∃ (E' : IntermediateField E K) (_ : FiniteDimensional E E') (r : ℕ) (ms : Fin r → ℕ)
      (eqv : Fin m ≃ Σ i, Fin (ms i)) (Q : GL (Σ i, Fin (ms i)) E'),
      (∀ a, (Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
          reindex eqv eqv ((X a).map (algebraMap E E')) *
          ((Q⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') =
        blockDiagonal' (blockDiag' ((Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
          reindex eqv eqv ((X a).map (algebraMap E E')) *
            ((Q⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E')))) ∧
      ∀ i (W : Submodule K (Fin (ms i) → K)),
        (∀ a, ∀ v ∈ W, (blockDiag' ((Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
          reindex eqv eqv ((X a).map (algebraMap E E')) *
            ((Q⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E'))
              i).map (algebraMap E' K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  set Fb := algebraicClosure E K with hFb
  have : IsAlgClosure E Fb := algebraicClosure.isAlgClosure E K
  have : IsAlgClosed Fb := IsAlgClosure.isAlgClosed E
  obtain ⟨r, ms, eqv, Qb, hblkb, hirrb⟩ :=
    exists_blockDiagonal'_conj_irreducible (fun a => (X a).map (algebraMap E Fb)) hss
  set Pm : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) Fb :=
    (Qb : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) Fb) with hPm
  set Qm : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) Fb :=
    ((Qb⁻¹ : GL (Σ i, Fin (ms i)) Fb) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) Fb) with hQm
  set S : Set K :=
    Set.range (fun ij : (Σ i, Fin (ms i)) × (Σ i, Fin (ms i)) => ((Pm ij.1 ij.2 : Fb) : K)) ∪
      Set.range (fun ij : (Σ i, Fin (ms i)) × (Σ i, Fin (ms i)) => ((Qm ij.1 ij.2 : Fb) : K))
    with hS
  set E' := IntermediateField.adjoin E S with hE'
  have hint : ∀ x ∈ S, IsIntegral E x := by
    rintro x (⟨ij, rfl⟩ | ⟨ij, rfl⟩)
    · exact (mem_algebraicClosure_iff.mp (Pm ij.1 ij.2).2).isIntegral
    · exact (mem_algebraicClosure_iff.mp (Qm ij.1 ij.2).2).isIntegral
  have : Finite S := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  have hfin : FiniteDimensional E E' := IntermediateField.finiteDimensional_adjoin hint
  let PE : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E' := fun i j =>
    ⟨((Pm i j : Fb) : K), IntermediateField.subset_adjoin E S (Or.inl ⟨(i, j), rfl⟩)⟩
  let QE : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E' := fun i j =>
    ⟨((Qm i j : Fb) : K), IntermediateField.subset_adjoin E S (Or.inr ⟨(i, j), rfl⟩)⟩
  have hPE : PE.map (algebraMap E' K) = Pm.map (algebraMap Fb K) := rfl
  have hQE : QE.map (algebraMap E' K) = Qm.map (algebraMap Fb K) := rfl
  have hinj := Matrix.map_injective (m := Σ i, Fin (ms i)) (n := Σ i, Fin (ms i))
    (algebraMap E' K).injective
  have h1 : PE * QE = 1 := by
    apply hinj
    show (PE * QE).map (algebraMap E' K) =
      (1 : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E').map (algebraMap E' K)
    rw [Matrix.map_mul, hPE, hQE, ← Matrix.map_mul, hPm, hQm, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : QE * PE = 1 := mul_eq_one_comm.mp h1
  let Q : GL (Σ i, Fin (ms i)) E' := ⟨PE, QE, h1, h2⟩
  set YE : A → Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E' := fun a =>
    (Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
      reindex eqv eqv ((X a).map (algebraMap E E')) *
      ((Q⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') with hYE
  set Yb : A → Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) Fb := fun a =>
    Pm * reindex eqv eqv ((X a).map (algebraMap E Fb)) * Qm with hYb
  have hreindex : ∀ {R₁ R₂ : Type _} [CommRing R₁] [CommRing R₂] (f : R₁ →+* R₂)
      (Z : Matrix (Fin m) (Fin m) R₁), (reindex eqv eqv Z).map f = reindex eqv eqv (Z.map f) :=
    fun f Z => by ext i j; rfl
  have hT : ∀ a, (YE a).map (algebraMap E' K) = (Yb a).map (algebraMap Fb K) := by
    intro a
    show (PE * reindex eqv eqv ((X a).map (algebraMap E E')) * QE).map (algebraMap E' K) = _
    rw [Matrix.map_mul, Matrix.map_mul, hQE, hPE, hYb, Matrix.map_mul, Matrix.map_mul,
      hreindex, hreindex, Matrix.map_map, Matrix.map_map, ← RingHom.coe_comp, ← RingHom.coe_comp,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hblk : ∀ a, Yb a = blockDiagonal' (blockDiag' (Yb a)) := hblkb
  refine ⟨E', hfin, r, ms, eqv, Q, fun a => ?_, fun i W hW => ?_⟩
  · apply hinj
    show (YE a).map (algebraMap E' K) = (blockDiagonal' (blockDiag' (YE a))).map (algebraMap E' K)
    rw [blockDiagonal'_map _ _ (map_zero _), ← blockDiag'_map, hT, hblk a,
      blockDiagonal'_map _ _ (map_zero _), blockDiag'_blockDiagonal']
  · exact eq_bot_or_eq_top_of_forall_mulVec_map_mem (K := K)
      (fun a => blockDiag' (Yb a) i) (hirrb i) W fun a v hv => by
        have e : (blockDiag' ((Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
            reindex eqv eqv ((X a).map (algebraMap E E')) *
              ((Q⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E'))
                i).map (algebraMap E' K) = (blockDiag' (Yb a) i).map (algebraMap Fb K) := by
          show (blockDiag' (YE a) i).map _ = _
          rw [← congrFun (blockDiag'_map (YE a) _) i, hT, blockDiag'_map]
        have := hW a v hv
        rwa [e] at this

end Descent

end Stacks.EtaleCohomology

end
