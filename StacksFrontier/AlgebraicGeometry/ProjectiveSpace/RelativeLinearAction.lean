module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.GeneralLinearGroup

/-!
# The linear action on projective space over a ring, and the action of `GL₂` on `ℙ¹`

A linear change of homogeneous coordinates acts on projective space. This file carries the action
`AlgebraicGeometry.ProjectiveSpaceOfModule.map` on `𝐏(V) = Proj (Sym_k V)` over to
`AlgebraicGeometry.projectiveSpaceOverRing n R`, as an action by automorphisms over `Spec R`, and
instantiates it at the generic invertible matrix over the coordinate ring of `GL₂`. This gives the
action morphism

`GL₂ ×_{Spec k} ℙ¹_k ⟶ ℙ¹_k`

over `Spec k`, and likewise the action morphism of `(GL₂)^m` on `(ℙ¹_k)^m`.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceOfModuleIso`: a basis of `V` indexed by `Fin (n + 1)`
  identifies `𝐏(V)` with `ℙⁿ_R`, as schemes.
* `AlgebraicGeometry.projectiveSpaceLinearToAut`: the action of the general linear group of `V` by
  automorphisms of `ℙⁿ_R`, transported along such a basis.
* `AlgebraicGeometry.projectiveSpaceMatrixToAut`: the same for the general linear group of
  `(n + 1) × (n + 1)` matrices.
* `AlgebraicGeometry.genericGeneralLinearTwo`: the generic invertible two-by-two matrix, over the
  coordinate ring of `GL₂`.
* `AlgebraicGeometry.projectiveLineGeneralLinearAction`: the action morphism of `GL₂` on `ℙ¹`,
  as a morphism `ℙ¹_{Γ(GL₂)} ⟶ ℙ¹_k` over `Spec k`.
* `AlgebraicGeometry.projectiveSpaceMatrixToAutOver`: the same action read in `Over (Spec R)`, as a
  homomorphism of groups.
* `AlgebraicGeometry.projectiveSpacePowerMatrixAut`: the action of the `m`-th power of the general
  linear group on the `m`-fold self-product of `ℙⁿ_R` over `Spec R`, the `i`-th matrix acting on
  the `i`-th factor.
* `AlgebraicGeometry.generalLinearTwoPowerCoordinateRing`: the coordinate ring of `(GL₂)^m`.
* `AlgebraicGeometry.genericGeneralLinearTwoPower`: the `i`-th of the `m` generic invertible
  two-by-two matrices over it.
* `AlgebraicGeometry.projectiveLinePowerGenericAut`: the automorphism of `(ℙ¹)^m` over `(GL₂)^m`
  given by the `m` generic matrices.
* `AlgebraicGeometry.projectiveSpacePowerPullbackIso`: the `m`-fold self-product of `ℙⁿ` is stable
  under base change of the coefficient ring.
* `AlgebraicGeometry.projectiveLinePowerOverGeneralLinearTwoPower`:
  `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m`, as an object over `(GL₂)^m`.
* `AlgebraicGeometry.projectiveLinePowerGeneralLinearAction`: the action morphism
  `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m ⟶ (ℙ¹_k)^m`, `(g, x) ↦ g · x`.
* `AlgebraicGeometry.generalLinearTwoPowerPoint`: the `k`-point of `(GL₂)^m` named by `m`
  invertible two-by-two matrices over `k`, as a retraction of the structure map of the
  coordinate ring.

## Main results

* `AlgebraicGeometry.projectiveSpaceMatrixToAut_hom_comp_structureMorphism`: the action is by
  automorphisms over the base.
* `AlgebraicGeometry.projectiveLineGeneralLinearAction_comp_structureMorphism`: the action morphism
  lies over `Spec k`.
* `AlgebraicGeometry.isPullback_projectiveLineOverGeneralLinearTwo`: the source of the action
  morphism is `GL₂ ×_{Spec k} ℙ¹_k`.
* `AlgebraicGeometry.isUnit_det_genericMatrixTwoPower`: each of the `m` generic two-by-two matrices
  is invertible over the coordinate ring of `(GL₂)^m`.
* `AlgebraicGeometry.projectiveSpacePowerMatrixAut_hom_π`: the `i`-th coordinate of the power
  action is the action of the `i`-th matrix.
* `AlgebraicGeometry.projectiveLinePowerGeneralLinearAction_comp_structureMorphism`: the action
  morphism of `(GL₂)^m` on `(ℙ¹_k)^m` lies over `Spec k`.
* `AlgebraicGeometry.generalLinearTwoPowerPoint_comp_algebraMap` and
  `AlgebraicGeometry.generalLinearTwoPowerPoint_map_genericGeneralLinearTwoPower`: every
  `m`-tuple of invertible two-by-two matrices over `k` is the value of the generic family at a
  `k`-point of `(GL₂)^m`.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section Module

variable {k V : Type u} [CommRing k] [AddCommGroup V] [Module k V]

/-- The graded homomorphism of symmetric algebras induced by a linear endomorphism is the identity
on the coefficient ring sitting in degree zero. -/
theorem gradedZeroRingHom_gradedSymAlgMap_comp_algebraMap (g : V →ₗ[k] V) :
    (SymPow.gradedSymAlgMap g).gradedZeroRingHom.comp
        (algebraMap k ↥(SymPow.symmetricPower 0 k V)) =
      algebraMap k ↥(SymPow.symmetricPower 0 k V) :=
  RingHom.ext fun r ↦ Subtype.ext ((SymPow.symAlgMap g).commutes r)

/-- The automorphism of `𝐏(V)` attached to an invertible linear map commutes with the structure
morphism to `Spec k`. -/
theorem projectiveSpaceOfModuleMap_comp_toSpec (g : LinearMap.GeneralLinearGroup k V) :
    ProjectiveSpaceOfModule.map k V g ≫ projectiveSpaceOfModuleToSpec k V =
      projectiveSpaceOfModuleToSpec k V := by
  rw [projectiveSpaceOfModuleToSpec, ProjectiveSpaceOfModule.map, ← Category.assoc,
    Proj.map_toSpecZero, Category.assoc, ← Spec.map_comp, ← ofHom_comp,
    gradedZeroRingHom_gradedSymAlgMap_comp_algebraMap]

variable {n : ℕ} (b : Module.Basis (Fin (n + 1)) k V)

/-- The isomorphism of schemes `𝐏(V) ≅ ℙⁿ_k` given by a basis of `V` indexed by `Fin (n + 1)`:
the underlying isomorphism of `AlgebraicGeometry.basisProjectiveSpaceOfModuleIso`. -/
def projectiveSpaceOfModuleIso :
    projectiveSpaceOfModule k V ≅ projectiveSpaceOverRing n (.of k) :=
  (Over.forget (Spec (.of k))).mapIso (basisProjectiveSpaceOfModuleIso b)

/-- The identification of `𝐏(V)` with `ℙⁿ_k` is a morphism over `Spec k`. -/
theorem projectiveSpaceOfModuleIso_hom_comp_structureMorphism :
    (projectiveSpaceOfModuleIso b).hom ≫
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) =
      projectiveSpaceOfModuleToSpec k V :=
  Over.w (basisProjectiveSpaceOfModuleIso b).hom

/-- The identification of `ℙⁿ_k` with `𝐏(V)` is a morphism over `Spec k`. -/
theorem projectiveSpaceOfModuleIso_inv_comp_toSpec :
    (projectiveSpaceOfModuleIso b).inv ≫ projectiveSpaceOfModuleToSpec k V =
      projectiveSpaceOverRing n (.of k) ↘ Spec (.of k) :=
  Over.w (basisProjectiveSpaceOfModuleIso b).inv

/-- The action of the general linear group of `V` by automorphisms of `ℙⁿ_k`, for `V` with a
basis indexed by `Fin (n + 1)`: the action on `𝐏(V)` conjugated by the identification of `𝐏(V)`
with `ℙⁿ_k`. -/
def projectiveSpaceLinearToAut :
    LinearMap.GeneralLinearGroup k V →* Aut (projectiveSpaceOverRing n (.of k)) :=
  (Aut.autMulEquivOfIso (projectiveSpaceOfModuleIso b)).toMonoidHom.comp
    (ProjectiveSpaceOfModule.generalLinearToAut k V)

/-- The automorphism of `ℙⁿ_k` attached to `g` is `AlgebraicGeometry.ProjectiveSpaceOfModule.map`
of `g⁻¹`, conjugated by the identification of `𝐏(V)` with `ℙⁿ_k`. -/
theorem projectiveSpaceLinearToAut_hom (g : LinearMap.GeneralLinearGroup k V) :
    (projectiveSpaceLinearToAut b g).asIso.hom =
      (projectiveSpaceOfModuleIso b).inv ≫ ProjectiveSpaceOfModule.map k V g⁻¹ ≫
        (projectiveSpaceOfModuleIso b).hom :=
  rfl

/-- The automorphisms of `ℙⁿ_k` attached to invertible linear maps commute with the structure
morphism to `Spec k`. -/
theorem projectiveSpaceLinearToAut_hom_comp_structureMorphism
    (g : LinearMap.GeneralLinearGroup k V) :
    (projectiveSpaceLinearToAut b g).asIso.hom ≫
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) =
      projectiveSpaceOverRing n (.of k) ↘ Spec (.of k) := by
  rw [projectiveSpaceLinearToAut_hom, Category.assoc, Category.assoc,
    projectiveSpaceOfModuleIso_hom_comp_structureMorphism,
    projectiveSpaceOfModuleMap_comp_toSpec, projectiveSpaceOfModuleIso_inv_comp_toSpec]

end Module

section Matrix

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The action of the general linear group of `(n + 1) × (n + 1)` matrices by automorphisms of
`ℙⁿ_k`: the action of invertible linear endomorphisms of `Fin (n + 1) → k`, transported along its
standard basis. -/
def projectiveSpaceMatrixToAut :
    Matrix.GeneralLinearGroup (Fin (n + 1)) k →*
      Aut (projectiveSpaceOverRing n (.of k)) :=
  (projectiveSpaceLinearToAut (Pi.basisFun k (Fin (n + 1)))).comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

/-- The automorphisms of `ℙⁿ_k` attached to invertible matrices commute with the structure
morphism to `Spec k`. -/
theorem projectiveSpaceMatrixToAut_hom_comp_structureMorphism
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) k) :
    (projectiveSpaceMatrixToAut k n M).asIso.hom ≫
        (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) =
      projectiveSpaceOverRing n (.of k) ↘ Spec (.of k) :=
  projectiveSpaceLinearToAut_hom_comp_structureMorphism _ _

end Matrix

section Generic

variable (k : Type u) [CommRing k]

/-- The generic two-by-two matrix, over the coordinate ring of `GL₂`. -/
def genericMatrixTwo : Matrix (Fin 2) (Fin 2) (generalLinearTwoCoordinateRing k) :=
  Matrix.of fun i j ↦ generalLinearTwoCoordinate k i j

/-- The generic two-by-two matrix is the generic matrix of indeterminates, read in the coordinate
ring of `GL₂`. -/
theorem genericMatrixTwo_eq_map :
    genericMatrixTwo k =
      (algebraMap (MvPolynomial (Fin 2 × Fin 2) k)
          (generalLinearTwoCoordinateRing k)).mapMatrix
        (Matrix.mvPolynomialX (Fin 2) (Fin 2) k) := by
  ext i j
  rfl

/-- The determinant of the generic two-by-two matrix is a unit in the coordinate ring of
`GL₂`. -/
theorem isUnit_det_genericMatrixTwo : IsUnit (genericMatrixTwo k).det := by
  rw [genericMatrixTwo_eq_map, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (generalLinearTwoDeterminant k)

/-- The generic invertible two-by-two matrix, as an element of the general linear group over
the coordinate ring of `GL₂`: its entries are the four coordinates of `GL₂`. -/
def genericGeneralLinearTwo :
    Matrix.GeneralLinearGroup (Fin 2) (generalLinearTwoCoordinateRing k) :=
  ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_genericMatrixTwo k)).unit

/-- The action morphism of `GL₂` on the projective line: the automorphism of `ℙ¹` over the
coordinate ring of `GL₂` given by the generic invertible matrix, followed by the projection to
`ℙ¹_k`. -/
def projectiveLineGeneralLinearAction :
    projectiveSpaceOverRing 1 (.of (generalLinearTwoCoordinateRing k)) ⟶
      projectiveSpaceOverRing 1 (.of k) :=
  (projectiveSpaceMatrixToAut (generalLinearTwoCoordinateRing k) 1
      (genericGeneralLinearTwo k)).asIso.hom ≫
    projectiveSpaceOverRingMap 1 (ofHom (algebraMap k (generalLinearTwoCoordinateRing k)))

/-- The projective line over the coordinate ring of `GL₂` is `GL₂ ×_{Spec k} ℙ¹_k`. -/
theorem isPullback_projectiveLineOverGeneralLinearTwo :
    IsPullback
      (projectiveSpaceOverRingMap 1 (ofHom (algebraMap k (generalLinearTwoCoordinateRing k))))
      (projectiveSpaceOverRing 1 (.of (generalLinearTwoCoordinateRing k)) ↘
        Spec (.of (generalLinearTwoCoordinateRing k)))
      (projectiveSpaceOverRing 1 (.of k) ↘ Spec (.of k))
      (Spec.map (ofHom (algebraMap k (generalLinearTwoCoordinateRing k)))) :=
  isPullback_projectiveSpaceOverMap 1
    (Spec.map (ofHom (algebraMap k (generalLinearTwoCoordinateRing k))))

/-- The action morphism of `GL₂` on `ℙ¹` lies over `Spec k`, the structure morphism of its source
being the projection to `GL₂` followed by the structure morphism of `GL₂`. -/
theorem projectiveLineGeneralLinearAction_comp_structureMorphism :
    projectiveLineGeneralLinearAction k ≫ (projectiveSpaceOverRing 1 (.of k) ↘ Spec (.of k)) =
      (projectiveSpaceOverRing 1 (.of (generalLinearTwoCoordinateRing k)) ↘
          Spec (.of (generalLinearTwoCoordinateRing k))) ≫
        Spec.map (ofHom (algebraMap k (generalLinearTwoCoordinateRing k))) := by
  rw [projectiveLineGeneralLinearAction, Category.assoc,
    (isPullback_projectiveLineOverGeneralLinearTwo k).w,
    ← Category.assoc, projectiveSpaceMatrixToAut_hom_comp_structureMorphism]

end Generic

section Power

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The matrix action on `ℙⁿ_R` by automorphisms of `ℙⁿ_R` as a scheme over `Spec R`. -/
def projectiveSpaceMatrixToAutOver :
    Matrix.GeneralLinearGroup (Fin (n + 1)) k →*
      Aut ((projectiveSpaceOverRing n (.of k)).asOver (Spec (.of k))) where
  toFun M := .of (Over.isoMk (projectiveSpaceMatrixToAut k n M).asIso
    (projectiveSpaceMatrixToAut_hom_comp_structureMorphism k n M))
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply Over.OverMorphism.ext
    change (projectiveSpaceMatrixToAut k n 1).asIso.hom = _
    rw [map_one]
    rfl
  map_mul' M N := by
    apply Aut.ext
    apply Iso.ext
    apply Over.OverMorphism.ext
    change (projectiveSpaceMatrixToAut k n (M * N)).asIso.hom = _
    rw [map_mul]
    rfl

/-- The `m`-fold self-product of `ℙⁿ_R` over `Spec R`. -/
abbrev projectiveSpacePowerOver (m : ℕ) : Over (Spec (.of k)) :=
  ∏ᶜ fun _ : Fin m => (projectiveSpaceOverRing n (.of k)).asOver (Spec (.of k))

/-- The action of the `m`-th power of the general linear group on the `m`-fold self-product of
`ℙⁿ_R` over `Spec R`: the `i`-th matrix acts on the `i`-th factor. -/
def projectiveSpacePowerMatrixAut (m : ℕ)
    (M : Fin m → Matrix.GeneralLinearGroup (Fin (n + 1)) k) :
    Aut (projectiveSpacePowerOver k n m) :=
  .of (Pi.mapIso fun i => (projectiveSpaceMatrixToAutOver k n (M i)).asIso)

/-- The `i`-th coordinate of the power action is the action of the `i`-th matrix. -/
theorem projectiveSpacePowerMatrixAut_hom_π (m : ℕ)
    (M : Fin m → Matrix.GeneralLinearGroup (Fin (n + 1)) k) (i : Fin m) :
    (projectiveSpacePowerMatrixAut k n m M).asIso.hom ≫
        Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of k)).asOver (Spec (.of k))) i =
      Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of k)).asOver (Spec (.of k))) i ≫
        (projectiveSpaceMatrixToAutOver k n (M i)).asIso.hom :=
  Pi.mapIso_hom_π (fun i => (projectiveSpaceMatrixToAutOver k n (M i)).asIso) i

end Power

section GenericPower

variable (k : Type u) [CommRing k] (m : ℕ)

/-- The determinant of the `i`-th of `m` generic two-by-two matrices of indeterminates. -/
def genericTwoPowerDeterminant (i : Fin m) : MvPolynomial (Fin m × Fin 2 × Fin 2) k :=
  Matrix.det (Matrix.of fun a b ↦
    (MvPolynomial.X (i, a, b) : MvPolynomial (Fin m × Fin 2 × Fin 2) k))

/-- The coordinate ring of `(GL₂)^m` over `k`: the polynomial ring on `m` generic two-by-two
matrices, with the product of their determinants inverted. -/
abbrev generalLinearTwoPowerCoordinateRing : Type u :=
  Localization.Away (∏ i : Fin m, genericTwoPowerDeterminant k m i)

/-- The `i`-th of `m` generic two-by-two matrices, over the coordinate ring of `(GL₂)^m`. -/
def genericMatrixTwoPower (i : Fin m) :
    Matrix (Fin 2) (Fin 2) (generalLinearTwoPowerCoordinateRing k m) :=
  (algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
      (generalLinearTwoPowerCoordinateRing k m)).mapMatrix
    (Matrix.of fun a b ↦ MvPolynomial.X (i, a, b))

/-- Each of the `m` generic two-by-two matrices is invertible over the coordinate ring of
`(GL₂)^m`. -/
theorem isUnit_det_genericMatrixTwoPower (i : Fin m) :
    IsUnit (genericMatrixTwoPower k m i).det := by
  have hprod : IsUnit (algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
      (generalLinearTwoPowerCoordinateRing k m)
      (∏ j : Fin m, genericTwoPowerDeterminant k m j)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hsplit : IsUnit (algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
      (generalLinearTwoPowerCoordinateRing k m) (genericTwoPowerDeterminant k m i) *
      algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
        (generalLinearTwoPowerCoordinateRing k m)
        (∏ j ∈ Finset.univ.erase i, genericTwoPowerDeterminant k m j)) := by
    rw [← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact hprod
  rw [genericMatrixTwoPower, ← RingHom.map_det]
  exact isUnit_of_mul_isUnit_left hsplit

/-- The `i`-th generic invertible two-by-two matrix, as an element of the general linear group
over the coordinate ring of `(GL₂)^m`. -/
def genericGeneralLinearTwoPower (i : Fin m) :
    Matrix.GeneralLinearGroup (Fin 2) (generalLinearTwoPowerCoordinateRing k m) :=
  ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_genericMatrixTwoPower k m i)).unit

/-- The automorphism of `(ℙ¹)^m` over `(GL₂)^m` given by the `m` generic matrices, whose fibre
over a point of `(GL₂)^m` is the automorphism that point names. -/
def projectiveLinePowerGenericAut :
    Aut (projectiveSpacePowerOver (generalLinearTwoPowerCoordinateRing k m) 1 m) :=
  projectiveSpacePowerMatrixAut (generalLinearTwoPowerCoordinateRing k m) 1 m
    (genericGeneralLinearTwoPower k m)

/-! ### The `k`-points of `(GL₂)^m` -/

/-- The `(i, a, b)` entry of the `i`-th generic matrix is the image of the indeterminate. -/
theorem genericMatrixTwoPower_apply (i : Fin m) (a b : Fin 2) :
    genericMatrixTwoPower k m i a b =
      algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
        (generalLinearTwoPowerCoordinateRing k m) (MvPolynomial.X (i, a, b)) :=
  rfl

/-- The evaluation of the polynomial coordinates of `(GL₂)^m` at `m` two-by-two matrices over
`k`. -/
def genericTwoPowerEval (M : Fin m → Matrix (Fin 2) (Fin 2) k) :
    MvPolynomial (Fin m × Fin 2 × Fin 2) k →+* k :=
  (MvPolynomial.aeval fun p : Fin m × Fin 2 × Fin 2 ↦ M p.1 p.2.1 p.2.2).toRingHom

/-- The evaluation sends the polynomial coordinate `X (i, a, b)` to the `(a, b)` entry of the
`i`-th matrix. -/
@[simp]
theorem genericTwoPowerEval_X (M : Fin m → Matrix (Fin 2) (Fin 2) k)
    (p : Fin m × Fin 2 × Fin 2) :
    genericTwoPowerEval k m M (MvPolynomial.X p) = M p.1 p.2.1 p.2.2 := by
  simp [genericTwoPowerEval]

/-- The evaluation fixes the coefficients. -/
@[simp]
theorem genericTwoPowerEval_algebraMap (M : Fin m → Matrix (Fin 2) (Fin 2) k) (r : k) :
    genericTwoPowerEval k m M
        (algebraMap k (MvPolynomial (Fin m × Fin 2 × Fin 2) k) r) = r := by
  simp [genericTwoPowerEval]

/-- The evaluation sends the determinant of the `i`-th generic matrix to the determinant of the
`i`-th given matrix. -/
theorem genericTwoPowerEval_genericTwoPowerDeterminant
    (M : Fin m → Matrix (Fin 2) (Fin 2) k) (i : Fin m) :
    genericTwoPowerEval k m M (genericTwoPowerDeterminant k m i) = (M i).det := by
  rw [genericTwoPowerDeterminant, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun a b ↦ ?_)
  simp

/-- The evaluation at `m` invertible matrices sends the product of the `m` generic determinants
to a unit. -/
theorem isUnit_genericTwoPowerEval_prod
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    IsUnit (genericTwoPowerEval k m (fun i => (M i : Matrix (Fin 2) (Fin 2) k))
      (∏ i : Fin m, genericTwoPowerDeterminant k m i)) := by
  rw [map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun i _ ↦ ?_
  rw [genericTwoPowerEval_genericTwoPowerDeterminant]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (M i).isUnit

/-- The `k`-point of `(GL₂)^m` named by `m` invertible two-by-two matrices over `k`: the
homomorphism from the coordinate ring of `(GL₂)^m` to `k` evaluating the indeterminates at their
entries. -/
noncomputable def generalLinearTwoPowerPoint
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    generalLinearTwoPowerCoordinateRing k m →+* k :=
  Localization.awayLift (genericTwoPowerEval k m fun i => (M i : Matrix (Fin 2) (Fin 2) k))
    (∏ i : Fin m, genericTwoPowerDeterminant k m i) (isUnit_genericTwoPowerEval_prod k m M)

/-- The `k`-point attached to `m` matrices restricts to the evaluation on polynomials. -/
theorem generalLinearTwoPowerPoint_algebraMap
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)
    (x : MvPolynomial (Fin m × Fin 2 × Fin 2) k) :
    generalLinearTwoPowerPoint k m M
        (algebraMap (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
          (generalLinearTwoPowerCoordinateRing k m) x) =
      genericTwoPowerEval k m (fun i => (M i : Matrix (Fin 2) (Fin 2) k)) x :=
  IsLocalization.Away.lift_eq _ (isUnit_genericTwoPowerEval_prod k m M) x

/-- A `k`-point of `(GL₂)^m` is a retraction of the structure map of its coordinate ring. -/
theorem generalLinearTwoPowerPoint_comp_algebraMap
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    (generalLinearTwoPowerPoint k m M).comp
        (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) = RingHom.id k := by
  refine RingHom.ext fun r ↦ ?_
  change generalLinearTwoPowerPoint k m M
      (algebraMap k (generalLinearTwoPowerCoordinateRing k m) r) = r
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m × Fin 2 × Fin 2) k)
      (generalLinearTwoPowerCoordinateRing k m) r,
    generalLinearTwoPowerPoint_algebraMap, genericTwoPowerEval_algebraMap]

/-- The generic matrices specialize, at the `k`-point named by `m` invertible matrices over `k`,
to those matrices. -/
theorem generalLinearTwoPowerPoint_map_genericGeneralLinearTwoPower
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) (i : Fin m) :
    Matrix.GeneralLinearGroup.map (generalLinearTwoPowerPoint k m M)
        (genericGeneralLinearTwoPower k m i) = M i := by
  have hU : (genericGeneralLinearTwoPower k m i :
      Matrix (Fin 2) (Fin 2) (generalLinearTwoPowerCoordinateRing k m)) =
      genericMatrixTwoPower k m i := IsUnit.unit_spec _
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, hU, genericMatrixTwoPower_apply,
    generalLinearTwoPowerPoint_algebraMap, genericTwoPowerEval_X]

end GenericPower

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (n m : ℕ)

/-- `ℙⁿ_B` is the base change of `ℙⁿ_A` along `Spec B ⟶ Spec A`, as an object over `Spec B`. -/
def projectiveSpacePullbackIso :
    (Over.pullback (Spec.map (ofHom φ))).obj
        ((projectiveSpaceOverRing n (.of A)).asOver (Spec (.of A))) ≅
      (projectiveSpaceOverRing n (.of B)).asOver (Spec (.of B)) :=
  Over.isoMk (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback.symm
    (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback_inv_snd

/-- The `m`-fold self-product of `ℙⁿ` is stable under base change along `Spec B ⟶ Spec A`. -/
def projectiveSpacePowerPullbackIso :
    (Over.pullback (Spec.map (ofHom φ))).obj (projectiveSpacePowerOver A n m) ≅
      projectiveSpacePowerOver B n m :=
  Limits.PreservesProduct.iso (Over.pullback (Spec.map (ofHom φ))) _ ≪≫
    Pi.mapIso fun _ => projectiveSpacePullbackIso φ n

end BaseChange

section PowerActionMorphism

variable (k : Type u) [CommRing k] (m : ℕ)

/-- The structure morphism of the coordinate ring of `(GL₂)^m` over `k`. -/
abbrev generalLinearTwoPowerStructureMap : CommRingCat.of k ⟶
    CommRingCat.of (generalLinearTwoPowerCoordinateRing k m) :=
  ofHom (algebraMap k (generalLinearTwoPowerCoordinateRing k m))

/-- `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m`, as an object over `(GL₂)^m`: the base change of the `m`-fold
self-product of the projective line along the structure morphism of `(GL₂)^m`. -/
abbrev projectiveLinePowerOverGeneralLinearTwoPower : Over
    (Spec (CommRingCat.of (generalLinearTwoPowerCoordinateRing k m))) :=
  (Over.pullback (Spec.map (generalLinearTwoPowerStructureMap k m))).obj
    (projectiveSpacePowerOver k 1 m)

/-- The automorphism of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over `(GL₂)^m` given by the `m` generic
matrices: `AlgebraicGeometry.projectiveLinePowerGenericAut` transported along
`AlgebraicGeometry.projectiveSpacePowerPullbackIso`. -/
def projectiveLinePowerGenericAutBaseChange :
    Aut (projectiveLinePowerOverGeneralLinearTwoPower k m) :=
  (Aut.autMulEquivOfIso (projectiveSpacePowerPullbackIso
      (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) 1 m)).symm
    (projectiveLinePowerGenericAut k m)

/-- The action morphism `(g, x) ↦ g · x` of `(GL₂)^m` on `(ℙ¹_k)^m`: the generic automorphism of
`(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over `(GL₂)^m`, followed by the projection to `(ℙ¹_k)^m`. -/
def projectiveLinePowerGeneralLinearAction :
    (projectiveLinePowerOverGeneralLinearTwoPower k m).left ⟶
      (projectiveSpacePowerOver k 1 m).left :=
  (projectiveLinePowerGenericAutBaseChange k m).asIso.hom.left ≫
    pullback.fst (projectiveSpacePowerOver k 1 m).hom
      (Spec.map (generalLinearTwoPowerStructureMap k m))

/-- The action morphism of `(GL₂)^m` on `(ℙ¹_k)^m` lies over `Spec k`, the structure morphism of
its source being the projection to `(GL₂)^m` followed by the structure morphism of `(GL₂)^m`. -/
theorem projectiveLinePowerGeneralLinearAction_comp_structureMorphism :
    projectiveLinePowerGeneralLinearAction k m ≫ (projectiveSpacePowerOver k 1 m).hom =
      pullback.snd (projectiveSpacePowerOver k 1 m).hom
          (Spec.map (generalLinearTwoPowerStructureMap k m)) ≫
        Spec.map (generalLinearTwoPowerStructureMap k m) := by
  rw [projectiveLinePowerGeneralLinearAction, Category.assoc, pullback.condition,
    ← Category.assoc]
  exact congrArg (fun u ↦ u ≫ Spec.map (generalLinearTwoPowerStructureMap k m))
    (Over.w (projectiveLinePowerGenericAutBaseChange k m).asIso.hom)

end PowerActionMorphism

end AlgebraicGeometry

end
