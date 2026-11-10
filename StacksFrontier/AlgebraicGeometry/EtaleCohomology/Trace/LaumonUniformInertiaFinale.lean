module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.InertiaTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCharacterAdd
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueField

/-!
# One element `h` with `ρ(h) - 1` invertible kills invariants and coinvariants

For a matrix representation `ρ` of a group and a subgroup `H` containing an element `h` with
`ρ(h) - 1` invertible, the restriction of `ρ` to `H` fixes no nonzero vector and has trivial
coinvariants. If the restriction of scalars of `ρ(h)` minus `1` is invertible, so is that of the
contragredient. Points of the Artin–Schreier cover over the geometric generic point of `Spec R`
induce on `R` the canonical map `R → κ(η) → Ω`. These close the uniform inertia argument of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.invariants_eq_bot_and_subsingleton_coinvariants_of_isUnit`: an element
  `h ∈ H` with `ρ(h) - 1` invertible kills the invariants and the coinvariants of `H`.
* `Stacks.EtaleCohomology.isUnit_restrictScalarsMatrix_contragredient_sub_one`: if
  `Res_b(ρ g) - 1` is invertible, so is `Res_b(ρ^∨ g) - 1`.
* `Stacks.ArtinSchreier.fiberRingHom_algebraMap_genericPoint`: a point of the Artin–Schreier
  cover over the geometric generic point induces on `R` the map `R → κ(η) → Ω`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **An element `h ∈ H` with `ρ(h) - 1` invertible kills invariants and coinvariants of `H`.** -/
theorem invariants_eq_bot_and_subsingleton_coinvariants_of_isUnit {Γ : Type*} [Group Γ]
    {R : Type*} [CommRing R] {n : ℕ} (ρ : Γ →* GL (Fin n) R) (H : Subgroup Γ) (h : H)
    (hu : IsUnit ((ρ h : Matrix (Fin n) (Fin n) R) - 1)) :
    Representation.invariants ((matrixRepresentation ρ).comp H.subtype) = ⊥ ∧
      Subsingleton (Representation.Coinvariants ((matrixRepresentation ρ).comp H.subtype)) := by
  let M : Matrix (Fin n) (Fin n) R := ρ h
  have hρh : ∀ v, ((matrixRepresentation ρ).comp H.subtype) h v = M.mulVec v :=
    fun v => matrixRepresentation_apply _ _ v
  obtain ⟨U, hU⟩ := id hu
  have hinv : ∀ w, (M - 1).mulVec ((↑U⁻¹ : Matrix (Fin n) (Fin n) R).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← hU, Units.mul_inv, Matrix.one_mulVec]
  have hinj : ∀ v, (M - 1).mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.mulVec_injective_of_isUnit hu (hv.trans (Matrix.mulVec_zero _).symm)
  constructor
  · refine eq_bot_iff.2 fun v hv => (Submodule.mem_bot R).2 (hinj v ?_)
    rw [Representation.mem_invariants] at hv
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hρh, hv h, sub_self]
  · have h0 : ∀ w, Representation.Coinvariants.mk _ w = (0 : Representation.Coinvariants
        ((matrixRepresentation ρ).comp H.subtype)) := by
      intro w
      rw [Representation.Coinvariants.mk_eq_zero]
      refine Representation.Coinvariants.mem_ker_of_eq h
        ((↑U⁻¹ : Matrix (Fin n) (Fin n) R).mulVec w) w ?_
      rw [hρh]
      have := hinv w
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at this
    constructor
    intro x y
    obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
    rw [h0 x, h0 y]

section RestrictScalars

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- `Res_b(N) - 1` is invertible when `N - 1` is. -/
theorem isUnit_restrictScalarsMatrix_sub_one {m : ℕ} {N : Matrix (Fin m) (Fin m) E}
    (h : IsUnit (N - 1)) : IsUnit (restrictScalarsMatrix b N - 1) := by
  rw [← restrictScalarsMatrix_one b, ← restrictScalarsMatrix_sub]
  exact h.map (restrictScalarsMonoidHom b m)

/-- `N - 1` is invertible when `Res_b(N) - 1` is. -/
theorem isUnit_sub_one_of_isUnit_restrictScalarsMatrix {m : ℕ} {N : Matrix (Fin m) (Fin m) E}
    (h : IsUnit (restrictScalarsMatrix b N - 1)) : IsUnit (N - 1) := by
  rw [← restrictScalarsMatrix_one b, ← restrictScalarsMatrix_sub] at h
  exact isUnit_of_isUnit_restrictScalarsMatrix b h

/-- **If `Res_b(ρ g) - 1` is invertible, so is `Res_b(ρ^∨ g) - 1`.** -/
theorem isUnit_restrictScalarsMatrix_contragredient_sub_one {G : Type*} [Group G] {m : ℕ}
    (ρ : G →* GL (Fin m) E) (g : G)
    (h : IsUnit (restrictScalarsMatrix b ((ρ g : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1)) :
    IsUnit (restrictScalarsMatrix b
      ((contragredient ρ g : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) := by
  apply isUnit_restrictScalarsMatrix_sub_one
  have hM := isUnit_sub_one_of_isUnit_restrictScalarsMatrix b h
  rw [contragredient_val, ← Matrix.transpose_one, ← Matrix.transpose_sub]
  have heq : (((ρ g)⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1 =
      (((ρ g)⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *
        -((ρ g : Matrix (Fin m) (Fin m) E) - 1) := by
    rw [mul_neg, Matrix.mul_sub, Matrix.mul_one, Units.inv_mul, neg_sub]
  rw [heq, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
  exact (Units.isUnit _).mul hM.neg

end RestrictScalars

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

variable {k : Type u} [Field k] [Fintype k] {R : Type u} [CommRing R] [Algebra k R]
  [IrreducibleSpace (Spec (.of R))] {Ω : Type u} [Field Ω]
  [Algebra ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω] [IsAlgClosed Ω]

/-- **A point of the Artin–Schreier cover over the geometric generic point induces on `R` the
canonical map `R → κ(η) → Ω`.** -/
theorem fiberRingHom_algebraMap_genericPoint {g : R}
    (p : (finiteEtaleFiberFunctor ((algebraicClosureGeometricPoint
      ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω).map
        ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))))).obj (cover k R g))
    (r : R) :
    (fiberRingHom p).hom (algebraMap R (Ring k g) r) =
      algebraMap ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω
        (((Scheme.ΓSpecIso (.of R)).inv ≫
          (Spec (.of R)).Γevaluation (genericPoint (Spec (.of R)))).hom r) := by
  rw [fiberRingHom_algebraMap_eq]
  let := specResidueFieldAlgebra (.of R) (genericPoint (Spec (.of R)))
  have h : Spec.preimage (GeometricPoint.map (algebraicClosureGeometricPoint
      ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω)
        ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R))))).hom =
      CommRingCat.ofHom (algebraMap R ((Spec (.of R)).residueField (genericPoint (Spec (.of R))))) ≫
        CommRingCat.ofHom (algebraMap
          ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω) := by
    apply Spec.map_injective
    rw [Spec.map_preimage]
    change Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω)) ≫
          (Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R
        ((Spec (.of R)).residueField (genericPoint (Spec (.of R))))) ≫
          CommRingCat.ofHom (algebraMap
            ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) Ω))
    rw [Spec.map_comp, fromSpecResidueField_eq_specMap]
  rw [h]
  rfl

end Stacks.ArtinSchreier

end
