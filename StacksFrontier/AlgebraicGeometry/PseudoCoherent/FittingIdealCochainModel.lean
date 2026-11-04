module

public import StacksFrontier.Algebra.Homology.DerivedCategory.QuasiIsoFromDerivedIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealFreeComplex

/-!
# The cochain complex of `𝒪`-modules presented by the numerical data of a Fitting complex

`Stacks.FittingComplex.FreeData R` records a bounded-above complex of finite free `R`-modules by
its ranks and the matrices of its differentials, and deliberately does not record the complex
condition, the ideals of minors that `Stacks.FittingComplex.FreeData.fittingIdeal` extracts from it
not depending on it. This file turns such data, once the complex condition is supplied, into an
honest cochain complex of `R`-modules, so that the homological statements the proof of
[Stacks, Tag 0ESP] needs — being K-projective, receiving a homotopy equivalence from another such
complex — can be made about it.

## Main definitions

* `Stacks.FittingComplex.FreeData.toCochain`: the cochain complex of `R`-modules with
  `R^{rank i}` in degree `i` and the matrices of the `FreeData` as differentials.

## Main results

* `Stacks.FittingComplex.FreeData.matrixOfHom_toCochain_d`: the matrix of the differential in
  degree `i` of `toCochain` is `d i`.
* `Stacks.FittingComplex.FreeData.isStrictlyLE_toCochain` and
  `Stacks.FittingComplex.FreeData.projective_toCochain_X`: the complex is bounded above by `top`
  and its terms are projective, hence it is K-projective
  (`Stacks.FittingComplex.FreeData.isKProjective_toCochain`).
* `Stacks.FittingComplex.FreeData.matrixOfHom_d_comm` and
  `Stacks.FittingComplex.FreeData.matrixOfHom_comp_eq`: the matrix form of the two identities a
  morphism of such complexes and a homotopy between morphisms carry.
* `Stacks.FittingComplex.FreeData.matrixOfHom_comp` and
  `Stacks.FittingComplex.FreeData.matrixOfHom_add`: reading a morphism of free modules
  `R^a → R^b` as a matrix turns composition into multiplication and addition into addition. This
  is the dictionary in which the identities carried by a homotopy equivalence become matrix
  identities.

## Implementation notes

The differential of `toCochain` in degrees `(i, j)` is defined by a case distinction on
`i + 1 = j`, and in the positive case the matrix `d i`, whose rows are indexed by
`Fin (rank (i + 1))`, has to land in `R^{rank j}`. The resulting reindexing along
`finCongr` is invisible at `j = i + 1`, where the equality is `rfl` and the reindexing is the
identity; that is the content of `toCochain_d`, and it is the only form in which the
differential is used below.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Matrix

namespace Stacks.FittingComplex.FreeData

universe u

variable {R : Type u} [CommRing R]

/-- Reading a morphism `R^a → R^b` of free modules as a `b × a` matrix. -/
noncomputable def matrixOfHom {a b : ℕ}
    (f : ModuleCat.of R (Fin a → R) ⟶ ModuleCat.of R (Fin b → R)) :
    Matrix (Fin b) (Fin a) R :=
  LinearMap.toMatrix' f.hom

/-- The morphism `R^a → R^b` of free modules given by a `b × a` matrix. -/
noncomputable def homOfMatrix {a b : ℕ} (A : Matrix (Fin b) (Fin a) R) :
    ModuleCat.of R (Fin a → R) ⟶ ModuleCat.of R (Fin b → R) :=
  ModuleCat.ofHom (Matrix.toLin' A)

/-- The matrix of the morphism given by a matrix `A` is `A`. -/
@[simp]
theorem matrixOfHom_homOfMatrix {a b : ℕ} (A : Matrix (Fin b) (Fin a) R) :
    matrixOfHom (homOfMatrix A) = A := by
  simp [matrixOfHom, homOfMatrix]

/-- Reading morphisms of free modules as matrices turns composition into multiplication. -/
theorem matrixOfHom_comp {a b c : ℕ}
    (f : ModuleCat.of R (Fin a → R) ⟶ ModuleCat.of R (Fin b → R))
    (g : ModuleCat.of R (Fin b → R) ⟶ ModuleCat.of R (Fin c → R)) :
    matrixOfHom (f ≫ g) = matrixOfHom g * matrixOfHom f := by
  simp [matrixOfHom, ← LinearMap.toMatrix'_comp]

/-- Reading morphisms of free modules as matrices is additive. -/
theorem matrixOfHom_add {a b : ℕ}
    (f g : ModuleCat.of R (Fin a → R) ⟶ ModuleCat.of R (Fin b → R)) :
    matrixOfHom (f + g) = matrixOfHom f + matrixOfHom g := by
  simp [matrixOfHom]

/-- The matrix of the identity of `R^a` is the identity matrix. -/
@[simp]
theorem matrixOfHom_id {a : ℕ} :
    matrixOfHom (𝟙 (ModuleCat.of R (Fin a → R))) = 1 := by
  simp [matrixOfHom]

/-- The cochain complex of `R`-modules presented by a bounded-above Fitting complex together with
the complex condition: the term in degree `i` is `R^{rank i}` and the differential out of degree
`i` is the matrix `d i`. -/
noncomputable def toCochain (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (Fin (C.rank i) → R)
  d i j := if h : i + 1 = j then
      homOfMatrix ((C.d i).submatrix (Fin.cast (congrArg C.rank h).symm) id) else 0
  shape i j hij := dif_neg hij
  d_comp_d' i j k hij hjk := by
    obtain rfl : j = i + 1 := hij.symm
    obtain rfl : k = i + 1 + 1 := hjk.symm
    rw [dif_pos rfl, dif_pos rfl]
    apply ModuleCat.hom_ext
    have : (C.d (i + 1)).submatrix
          (Fin.cast (congrArg C.rank (rfl : i + 1 + 1 = i + 1 + 1)).symm) id *
        (C.d i).submatrix (Fin.cast (congrArg C.rank (rfl : i + 1 = i + 1)).symm) id = 0 := by
      simpa using hdd i
    simpa [homOfMatrix, ← Matrix.toLin'_mul, this] using congrArg Matrix.toLin' this

/-- The term of `toCochain` in degree `i` is `R^{rank i}`. -/
@[simp]
theorem toCochain_X (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) (i : ℤ) :
    (C.toCochain hdd).X i = ModuleCat.of R (Fin (C.rank i) → R) := rfl

/-- The differential of `toCochain` out of degree `i` is the morphism given by the matrix
`d i`: at `j = i + 1` the reindexing in the definition is the identity. -/
theorem toCochain_d (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) (i : ℤ) :
    (C.toCochain hdd).d i (i + 1) = homOfMatrix (C.d i) := by
  show (if h : i + 1 = i + 1 then
      homOfMatrix ((C.d i).submatrix (Fin.cast (congrArg C.rank h).symm) id) else 0) = _
  rw [dif_pos rfl]
  congr 1

/-- The matrix of the differential of `toCochain` out of degree `i` is `d i`. -/
@[simp]
theorem matrixOfHom_toCochain_d (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0)
    (i : ℤ) : matrixOfHom ((C.toCochain hdd).d i (i + 1)) = C.d i := by
  rw [toCochain_d, matrixOfHom_homOfMatrix]

/-- The terms of `toCochain` are projective, being finite free. -/
instance projective_toCochain_X (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0)
    (i : ℤ) : Projective ((C.toCochain hdd).X i) :=
  inferInstanceAs (Projective (ModuleCat.of R (Fin (C.rank i) → R)))

/-- `toCochain` is bounded above by the degree `top` of the Fitting complex. -/
instance isStrictlyLE_toCochain (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) :
    (C.toCochain hdd).IsStrictlyLE C.top := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have h0 : C.rank i = 0 := C.rank_eq_zero_of_top_lt i hi
  let : Subsingleton (Fin (C.rank i) → R) :=
    ⟨fun x y => funext fun a => by rw [h0] at a; exact a.elim0⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin (C.rank i) → R))

/-- Precomposing a morphism of free modules with the differential of `toCochain` multiplies its
matrix on the right by `d i`. -/
private theorem matrixOfHom_toCochain_d_comp (C : FreeData R)
    (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) (i : ℤ) {a : ℕ}
    (φ : ModuleCat.of R (Fin (C.rank (i + 1)) → R) ⟶ ModuleCat.of R (Fin a → R)) :
    matrixOfHom ((C.toCochain hdd).d i (i + 1) ≫ φ) = matrixOfHom φ * C.d i :=
  (matrixOfHom_comp _ _).trans (congrArg _ (matrixOfHom_toCochain_d C hdd i))

/-- Postcomposing a morphism of free modules with the differential of `toCochain` multiplies its
matrix on the left by `d i`. -/
private theorem matrixOfHom_comp_toCochain_d (C : FreeData R)
    (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) (i : ℤ) {a : ℕ}
    (φ : ModuleCat.of R (Fin a → R) ⟶ ModuleCat.of R (Fin (C.rank i) → R)) :
    matrixOfHom (φ ≫ (C.toCochain hdd).d i (i + 1)) = C.d i * matrixOfHom φ :=
  (matrixOfHom_comp _ _).trans (congrArg (· * _) (matrixOfHom_toCochain_d C hdd i))

/-- The matrix form of the compatibility of a morphism of cochain models with the
differentials. -/
theorem matrixOfHom_d_comm (C₁ C₂ : FreeData R) (hdd₁ : ∀ i : ℤ, C₁.d (i + 1) * C₁.d i = 0)
    (hdd₂ : ∀ i : ℤ, C₂.d (i + 1) * C₂.d i = 0)
    (f : C₁.toCochain hdd₁ ⟶ C₂.toCochain hdd₂) (i : ℤ) :
    C₂.d i * matrixOfHom (f.f i) = matrixOfHom (f.f (i + 1)) * C₁.d i :=
  (matrixOfHom_comp_toCochain_d C₂ hdd₂ i (f.f i)).symm.trans <|
    (congrArg matrixOfHom (f.comm i (i + 1))).trans (matrixOfHom_toCochain_d_comp C₁ hdd₁ i _)

/-- The matrix form, in one degree, of the identity carried by a homotopy between
`f ≫ g` and the identity: the two matrices are mutually inverse up to the two differentials
adjacent to that degree. -/
theorem matrixOfHom_comp_eq (C₁ C₂ : FreeData R) (hdd₁ : ∀ i : ℤ, C₁.d (i + 1) * C₁.d i = 0)
    (hdd₂ : ∀ i : ℤ, C₂.d (i + 1) * C₂.d i = 0)
    (f : C₁.toCochain hdd₁ ⟶ C₂.toCochain hdd₂) (g : C₂.toCochain hdd₂ ⟶ C₁.toCochain hdd₁)
    (h : Homotopy (f ≫ g) (𝟙 (C₁.toCochain hdd₁))) (j : ℤ) :
    matrixOfHom (g.f (j + 1)) * matrixOfHom (f.f (j + 1)) =
      matrixOfHom (h.hom (j + 1 + 1) (j + 1)) * C₁.d (j + 1)
        + C₁.d j * matrixOfHom (h.hom (j + 1) j) + 1 := by
  have hd := (congrArg matrixOfHom (dNext_eq h.hom
    (show (ComplexShape.up ℤ).Rel (j + 1) (j + 1 + 1) from rfl))).trans
    (matrixOfHom_toCochain_d_comp C₁ hdd₁ (j + 1) _)
  have hp := (congrArg matrixOfHom (prevD_eq h.hom
    (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl))).trans
    (matrixOfHom_comp_toCochain_d C₁ hdd₁ j _)
  refine (matrixOfHom_comp _ _).symm.trans ((congrArg matrixOfHom (h.comm (j + 1))).trans ?_)
  exact (matrixOfHom_add _ _).trans (congrArg₂ (· + ·)
    ((matrixOfHom_add _ _).trans (congrArg₂ (· + ·) hd hp)) matrixOfHom_id)

/-- A bounded-above complex of finite free modules is K-projective. -/
theorem isKProjective_toCochain (C : FreeData R) (hdd : ∀ i : ℤ, C.d (i + 1) * C.d i = 0) :
    CochainComplex.IsKProjective (C.toCochain hdd) :=
  CochainComplex.isKProjective_of_projective _ C.top

end Stacks.FittingComplex.FreeData

end
