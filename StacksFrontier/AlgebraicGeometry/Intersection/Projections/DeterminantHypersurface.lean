module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ProjectiveLinearGroup
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksCore.Tactic.StacksAttribute

/-!
# The determinant hypersurface in the parameter space of projective transformations

The parameter space of the projective transformations of `𝐏(V)` is
`𝐏 = 𝐏((End V)ᵛ) = Proj (Sym ((End V)ᵛ))`, whose closed points are the projective classes of
endomorphisms of `V`. The determinant is a form of degree `dim V` on `End V`, that is an element
of the degree-`dim V` part of `Sym ((End V)ᵛ)`; its non-vanishing locus is a basic open subset
`G ⊆ 𝐏` whose closed points are exactly the classes with an invertible representative, and its
vanishing locus is the complementary closed subset `Z = 𝐏 ∖ G`, the determinant hypersurface.
Over an algebraically closed field with `dim V ≥ 2` that hypersurface is irreducible, because the
determinant of a generic matrix is an irreducible polynomial.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.determinantForm`: the determinant, as an element of
  `Sym ((End V)ᵛ)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.invertibleLocus`: the open subscheme `G ⊆ 𝐏` where
  the determinant does not vanish.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.determinantHypersurface`: the closed subset
  `Z = 𝐏 ∖ G`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.determinantForm_mem_symmetricPower`: the
  determinant form is homogeneous of degree `dim V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.lift_eval_determinantForm`: evaluating it at an
  endomorphism gives that endomorphism's determinant.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.coe_mem_invertibleLocus_iff`: the closed points of
  `G` are exactly the classes of endomorphisms admitting an invertible representative.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_determinantHypersurface` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.determinantHypersurface_eq_zeroLocus`: `Z` is
  closed, and is the projective zero locus of the determinant form.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_determinantHypersurface`: for
  `dim V ≥ 2` the determinant hypersurface is irreducible.

## Implementation notes

A basis of `V` indexed by `Fin (dim V)` makes the matrix coefficients a basis of `(End V)ᵛ`; the
determinant form is the determinant of the matrix of the corresponding degree-one elements of
the symmetric algebra. The basis used is `Module.finBasis k V`, so the form is a definite
element; the characterizations of `G` and `Z` are basis-free.

The bridge from the form to the geometry is that membership of a homogeneous element in the
homogeneous prime of the point cut out by a nonzero functional `f` on `(End V)ᵛ` can be tested by
the algebra map `Sym ((End V)ᵛ) → k` that `f` lifts to, rather than by the map
`Sym ((End V)ᵛ) → Sym k` of `AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint_mem`:
the degree-`n` part of `Sym_k k` is a line, on which the two tests agree.

Irreducibility transports the irreducibility of the generic determinant,
`MvPolynomial.irreducible_det_genericMatrix`, along the isomorphism of `Sym ((End V)ᵛ)` with a
polynomial ring given by the basis of matrix coefficients: the determinant form is then a prime
element, so it spans a homogeneous prime ideal, and that ideal is a point of `𝐏` whose closure is
the hypersurface. That the ideal does not contain the irrelevant ideal is checked by evaluating:
for `dim V ≥ 2` there is a nonzero endomorphism of zero determinant, and a linear form on
`End V` not vanishing on it is then not a multiple of the determinant form. For `dim V = 1`
every nonzero endomorphism is invertible, `Z` is empty and the statement fails, which is why the
hypothesis is there.

No `@[stacks 0B2V]` attribute is attached here: the statement of that tag is the irreducibility
of the determinant of a generic matrix, which is
`MvPolynomial.irreducible_det_genericMatrix`; this file carries the geometric reading used in
its proof, not the tag's statement.

## References

* [Stacks Project, Tag 0B2V](https://stacks.math.columbia.edu/tag/0B2V)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace SymPow

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Evaluating a linear functional on the symmetric algebra factors through the induced map to
`Sym_R R`: both algebra homomorphisms send a degree-one generator `m` to `f m`. -/
public theorem lift_id_symAlgMap (f : Module.Dual R M) (z : SymmetricAlgebra R M) :
    SymmetricAlgebra.lift (LinearMap.id : R →ₗ[R] R) (symAlgMap f z) =
      SymmetricAlgebra.lift f z := by
  have h : (SymmetricAlgebra.lift (LinearMap.id : R →ₗ[R] R)).comp (symAlgMap f) =
      SymmetricAlgebra.lift f := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [symAlgMap_ι, SymmetricAlgebra.lift_ι_apply]
  exact DFunLike.congr_fun h z

/-- **The two tests for vanishing at a point agree on a homogeneous element.** On the degree-`n`
part of `Sym_R M` the map induced by a functional `f` kills an element exactly when the algebra
map that `f` lifts to does, because the degree-`n` part of `Sym_R R` is a line. -/
public theorem symAlgMap_eq_zero_iff_lift_eq_zero {n : ℕ} (f : Module.Dual R M)
    {z : SymmetricAlgebra R M} (hz : z ∈ symmetricPower n R M) :
    symAlgMap f z = 0 ↔ SymmetricAlgebra.lift f z = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← lift_id_symAlgMap f z, h, map_zero]
  · exact eq_zero_of_mem_symmetricPower_of_lift_id_eq_zero R n
      (symAlgMap_mapsTo n f z hz) (by rw [lift_id_symAlgMap]; exact h)

end SymPow

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

section Coefficients

variable {k V} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of an endomorphism in a basis, read as a family of scalars. -/
public def endMatrixEquiv (b : Module.Basis ι k V) :
    (V →ₗ[k] V) ≃ₗ[k] (ι × ι → k) :=
  (LinearMap.toMatrix b b).trans
    ((Matrix.ofLinearEquiv k).symm.trans (LinearEquiv.curry k k ι ι).symm)

/-- The coordinate of `endMatrixEquiv b g` at `(i, j)` is the matrix entry of `g` at `(i, j)`. -/
public theorem endMatrixEquiv_apply (b : Module.Basis ι k V) (g : V →ₗ[k] V) (p : ι × ι) :
    endMatrixEquiv b g p = LinearMap.toMatrix b b g p.1 p.2 := rfl

/-- The basis of `End V` of elementary matrices in a basis of `V`. -/
public def endBasis (b : Module.Basis ι k V) : Module.Basis (ι × ι) k (V →ₗ[k] V) :=
  (Pi.basisFun k (ι × ι)).map (endMatrixEquiv b).symm

/-- The coordinates of an endomorphism in `endBasis b` are its matrix entries in the basis `b`. -/
public theorem endBasis_repr (b : Module.Basis ι k V) (g : V →ₗ[k] V) (p : ι × ι) :
    (endBasis b).repr g p = LinearMap.toMatrix b b g p.1 p.2 := by
  simp [endBasis, endMatrixEquiv_apply]

/-- The basis of `(End V)ᵛ` of matrix coefficients in a basis of `V`.

Public because the determinant form is `@[no_expose]`: a consumer that needs to evaluate
`SymmetricAlgebra.lift` on it has to compare matrix coefficients, and cannot do so without this
basis and `lift_determinantForm` below. -/
public def coeffBasis (b : Module.Basis ι k V) :
    Module.Basis (ι × ι) k (Module.Dual k (V →ₗ[k] V)) :=
  (endBasis b).dualBasis

/-- The `(i, j)`-th element of `coeffBasis b` reads off the matrix entry at `(i, j)` in the basis
`b`. -/
public theorem coeffBasis_apply (b : Module.Basis ι k V) (p : ι × ι) (g : V →ₗ[k] V) :
    coeffBasis b p g = LinearMap.toMatrix b b g p.1 p.2 := by
  rw [coeffBasis, Module.Basis.dualBasis_apply, endBasis_repr]

end Coefficients

section Form

variable [Module.Finite k V]

/-- **A minor, as a form on `End V`.** The determinant of the square submatrix with rows `s` and
columns `t` of the matrix of degree-one elements of `Sym ((End V)ᵛ)` given by the matrix
coefficients in the basis `Module.finBasis k V` of `V`. The determinant form is the full-size
case `s = t = id`. -/
@[no_expose] public def minorForm {m : ℕ} (s t : Fin m → Fin (Module.finrank k V)) :
    SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V)) :=
  (Matrix.of fun i j : Fin m =>
    SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V))
      (coeffBasis (Module.finBasis k V) (s i, t j))).det

/-- An algebra map sends a minor form to the determinant of the images of its degree-one entries. -/
private theorem map_minorForm {A : Type*} [CommRing A] [Algebra k A] {m : ℕ}
    (s t : Fin m → Fin (Module.finrank k V))
    (ψ : SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V)) →ₐ[k] A) :
    ψ (minorForm k V s t) =
      (Matrix.of fun i j : Fin m =>
        ψ (SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V))
          (coeffBasis (Module.finBasis k V) (s i, t j)))).det :=
  ψ.map_det _

/-- A minor form evaluated at a point, as the determinant of the matrix of coefficients.

Public because `minorForm` and `determinantForm` are `@[no_expose]`: this is the only way a
consumer can evaluate `SymmetricAlgebra.lift` on either of them. -/
public theorem lift_minorForm {A : Type*} [CommRing A] [Algebra k A] {m : ℕ}
    (s t : Fin m → Fin (Module.finrank k V))
    (f : Module.Dual k (V →ₗ[k] V) →ₗ[k] A) :
    SymmetricAlgebra.lift f (minorForm k V s t) =
      (Matrix.of fun i j : Fin m =>
        f (coeffBasis (Module.finBasis k V) (s i, t j))).det := by
  simp [map_minorForm, SymmetricAlgebra.lift_ι_apply]

/-- **A minor form evaluates to the corresponding minor.** The algebra map
`Sym ((End V)ᵛ) → k` that evaluation at an endomorphism `g` lifts to sends the minor form to
that minor of the matrix of `g`. -/
public theorem lift_eval_minorForm {m : ℕ} (s t : Fin m → Fin (Module.finrank k V))
    (g : V →ₗ[k] V) :
    SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g) (minorForm k V s t) =
      ((LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).submatrix s t).det := by
  rw [lift_minorForm]
  congr 1
  ext i j
  simp [Module.Dual.eval_apply, coeffBasis_apply]

/-- **A minor form is homogeneous of degree the size of the minor.** It is a sum of signed
products of that many degree-one elements. -/
public theorem minorForm_mem_symmetricPower {m : ℕ} (s t : Fin m → Fin (Module.finrank k V)) :
    minorForm k V s t ∈ SymPow.symmetricPower m k (Module.Dual k (V →ₗ[k] V)) := by
  classical
  rw [minorForm, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have h := SetLike.prod_mem_graded
    (A := fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
    (F := (Finset.univ : Finset (Fin m)))
    (g := fun i => SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V))
      (coeffBasis (Module.finBasis k V) (s (σ i), t i)))
    (fun _ => 1) (fun i _ => ι_mem_symmetricPower_one k _ _)
  simpa using h

/-- **The determinant, as a form on `End V`:** the full-size minor. -/
@[no_expose] public def determinantForm : SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V)) :=
  minorForm k V id id

/-- The determinant form evaluated at a point, as the determinant of the matrix of coefficients.

This is `lift_minorForm` at the full-size minor, stated separately because `determinantForm` is
`@[no_expose]`: without it a consumer cannot unfold `determinantForm` to reach `minorForm`. -/
public theorem lift_determinantForm {A : Type*} [CommRing A] [Algebra k A]
    (f : Module.Dual k (V →ₗ[k] V) →ₗ[k] A) :
    SymmetricAlgebra.lift f (determinantForm k V) =
      (Matrix.of fun i j : Fin (Module.finrank k V) =>
        f (coeffBasis (Module.finBasis k V) (i, j))).det :=
  lift_minorForm k V id id f

/-- **The determinant form evaluates to the determinant.** The algebra map
`Sym ((End V)ᵛ) → k` that evaluation at an endomorphism `g` lifts to sends the determinant form
to the determinant of `g`. -/
public theorem lift_eval_determinantForm (g : V →ₗ[k] V) :
    SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g) (determinantForm k V) =
      LinearMap.det g := by
  rw [determinantForm, lift_eval_minorForm, Matrix.submatrix_id_id, LinearMap.det_toMatrix]

/-- **The determinant form is homogeneous of degree `dim V`.** -/
public theorem determinantForm_mem_symmetricPower :
    determinantForm k V ∈
      SymPow.symmetricPower (Module.finrank k V) k (Module.Dual k (V →ₗ[k] V)) :=
  minorForm_mem_symmetricPower k V id id

/-- **`G`: the invertible locus of the parameter space.** The basic open subset of
`𝐏 = 𝐏((End V)ᵛ)` on which the determinant form does not vanish. -/
@[no_expose] public def invertibleLocus :
    (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))).Opens :=
  Proj.basicOpen (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
    (determinantForm k V)

/-- **`Z`: the determinant hypersurface.** The complement in `𝐏 = 𝐏((End V)ᵛ)` of the invertible
locus. -/
@[no_expose] public def determinantHypersurface :
    Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) :=
  (invertibleLocus k V : Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))))ᶜ

/-- Membership in `Z` is non-membership in `G`. The definition is `@[no_expose]`, so this is how
a consumer passes between the two spellings; without it they drift into two notions. -/
public theorem mem_determinantHypersurface_iff
    {q : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))} :
    q ∈ determinantHypersurface k V ↔
      q ∉ (invertibleLocus k V :
        Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V)))) :=
  Iff.rfl

/-- **`Z` is closed**, being the complement of an open subscheme. -/
public theorem isClosed_determinantHypersurface :
    IsClosed (determinantHypersurface k V) :=
  (invertibleLocus k V).isOpen.isClosed_compl

/-- **`Z` is the determinant hypersurface:** the projective zero locus of the determinant
form. -/
public theorem determinantHypersurface_eq_zeroLocus :
    determinantHypersurface k V =
      ProjectiveSpectrum.zeroLocus
        (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
        {determinantForm k V} := by
  have h : ((invertibleLocus k V :
        (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))).Opens) :
      Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V)))) =
      (ProjectiveSpectrum.zeroLocus
        (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
        {determinantForm k V})ᶜ :=
    ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl _ (determinantForm k V)
  rw [determinantHypersurface, h]
  exact compl_compl _

end Form

section Locus

variable [IsAlgClosed k] [Module.Finite k V]

omit [IsAlgClosed k] in
/-- Evaluation at a nonzero endomorphism is a nonzero functional on `(End V)ᵛ`. -/
public theorem eval_ne_zero {r : V →ₗ[k] V} (hr : r ≠ 0) :
    Module.Dual.eval k (V →ₗ[k] V) r ≠ 0 := fun h =>
  hr (Module.eval_apply_injective k (h.trans (map_zero _).symm))

/-- A closed point of the parameter space is the point cut out by evaluation at any
endomorphism representing it: the two have the same degree-one forms. -/
public theorem val_eq_linearFunctionalPoint
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg) :
    p.val = linearFunctionalPoint k (Module.Dual k (V →ₗ[k] V))
      (Module.Dual.eval k (V →ₗ[k] V) g) (eval_ne_zero k V hg) := by
  have hdeg : ∀ φ : Module.Dual k (V →ₗ[k] V),
      SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V)) φ ∈ p.val.asHomogeneousIdeal ↔
        φ g = 0 := by
    intro φ
    rw [dualEndClosedPointsEquiv_apply k V p φ, hpg]
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k g hg
    rw [← hc]
    simp [Units.smul_def, c.ne_zero]
  refine eq_of_asHomogeneousIdeal_le k (Module.Dual k (V →ₗ[k] V))
    (linearFunctionalPoint_isClosed k _ _ (eval_ne_zero k V hg)) ?_
  rw [← span_range_ι_ker_eq k (Module.Dual k (V →ₗ[k] V)) _ (eval_ne_zero k V hg), Ideal.span_le]
  rintro _ ⟨w, rfl⟩
  exact (hdeg (w : Module.Dual k (V →ₗ[k] V))).mpr (LinearMap.mem_ker.mp w.2)

/-- **The invertible locus is the non-vanishing locus of the determinant.** A closed point of
`𝐏` lies in `G` exactly when any endomorphism representing it has nonzero determinant. -/
public theorem coe_mem_invertibleLocus_iff_det_ne_zero
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈ invertibleLocus k V ↔
      LinearMap.det g ≠ 0 := by
  rw [invertibleLocus, Proj.mem_basicOpen, val_eq_linearFunctionalPoint k V p g hg hpg]
  refine not_congr ?_
  rw [linearFunctionalPoint_mem, SymPow.symAlgMap_eq_zero_iff_lift_eq_zero _
    (determinantForm_mem_symmetricPower k V), lift_eval_determinantForm]

omit [IsAlgClosed k] in
/-- A nonzero endomorphism has nonzero determinant exactly when its projective class has an
invertible representative: a scalar multiple of an invertible map is invertible. -/
private theorem det_ne_zero_iff_exists_invertibleClass (g : V →ₗ[k] V) (hg : g ≠ 0) :
    LinearMap.det g ≠ 0 ↔
      ∃ q : InvertibleEndomorphismClasses k V, q.val = Projectivization.mk k g hg := by
  constructor
  · intro hdet
    have hu : IsUnit g := (LinearMap.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hval : (hu.unit : V →ₗ[k] V) = g := hu.unit_spec
    have hne : (hu.unit : V →ₗ[k] V) ≠ 0 := by rw [hval]; exact hg
    exact ⟨⟨Projectivization.mk k g hg, hu.unit, hne,
      (Projectivization.mk_eq_mk_iff k _ _ hg hne).mpr ⟨1, by simp⟩⟩, rfl⟩
  · rintro ⟨q, hq⟩
    obtain ⟨g', hg', hq'⟩ := q.property
    rw [hq'] at hq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k _ _ hg' hg).mp hq
    have hdet' : LinearMap.det (g' : V →ₗ[k] V) ≠ 0 :=
      (LinearMap.isUnit_det (g' : V →ₗ[k] V) g'.isUnit).ne_zero
    intro hdet
    rw [← hc, Units.smul_def, LinearMap.det_smul, hdet, mul_zero] at hdet'
    exact hdet' rfl

/-- **The closed points of `G` are the invertible classes.** A closed point of the parameter
space lies in the invertible locus exactly when the class of endomorphisms it names admits an
invertible representative. -/
public theorem coe_mem_invertibleLocus_iff
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈ invertibleLocus k V ↔
      ∃ q : InvertibleEndomorphismClasses k V, dualEndClosedPointsEquiv k V p = q.val := by
  set r := (dualEndClosedPointsEquiv k V p).rep with hr
  have hrne : r ≠ 0 := Projectivization.rep_nonzero _
  have hpr : dualEndClosedPointsEquiv k V p = Projectivization.mk k r hrne :=
    (Projectivization.mk_rep _).symm
  rw [coe_mem_invertibleLocus_iff_det_ne_zero k V p r hrne hpr,
    det_ne_zero_iff_exists_invertibleClass k V r hrne]
  exact ⟨fun ⟨q, hq⟩ => ⟨q, by rw [hpr, hq]⟩, fun ⟨q, hq⟩ => ⟨q, by rw [← hq, hpr]⟩⟩

/-- **The closed points of `Z` are the non-invertible classes.** -/
public theorem coe_mem_determinantHypersurface_iff
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈
        determinantHypersurface k V ↔
      ∀ q : InvertibleEndomorphismClasses k V, dualEndClosedPointsEquiv k V p ≠ q.val := by
  constructor
  · intro hmem q hq
    exact hmem ((coe_mem_invertibleLocus_iff k V p).mpr ⟨q, hq⟩)
  · intro h hmem
    obtain ⟨q, hq⟩ := (coe_mem_invertibleLocus_iff k V p).mp hmem
    exact h q hq

end Locus

section Irreducible

variable [Module.Finite k V]

/-- Under the isomorphism with a polynomial ring given by the matrix coefficients, the
determinant form is the determinant of the matrix of the variables. -/
private theorem equivMvPolynomial_determinantForm :
    SymmetricAlgebra.equivMvPolynomial (coeffBasis (Module.finBasis k V))
        (determinantForm k V) =
      (Matrix.of fun i j : Fin (Module.finrank k V) =>
        MvPolynomial.X ((i, j) : Fin (Module.finrank k V) × Fin (Module.finrank k V))).det := by
  rw [determinantForm]
  exact (map_minorForm k V id id
    (SymmetricAlgebra.equivMvPolynomial (coeffBasis (Module.finBasis k V))).toAlgHom).trans
    (congrArg Matrix.det (Matrix.ext fun i j =>
      SymmetricAlgebra.equivMvPolynomial_ι_apply (coeffBasis (Module.finBasis k V)) (i, j)))

/-- **The determinant form is prime.** The matrix coefficients identify `Sym ((End V)ᵛ)` with a
polynomial ring carrying the determinant form to the determinant of a generic matrix, which is
irreducible, hence prime in that unique factorization domain. -/
private theorem prime_determinantForm (hV : 0 < Module.finrank k V) :
    Prime (determinantForm k V) := by
  have hirr : Irreducible (SymmetricAlgebra.equivMvPolynomial
      (coeffBasis (Module.finBasis k V)) (determinantForm k V)) := by
    rw [equivMvPolynomial_determinantForm]
    exact MvPolynomial.irreducible_det_genericMatrix k _ hV
  exact (MulEquiv.prime_iff
      (SymmetricAlgebra.equivMvPolynomial (coeffBasis (Module.finBasis k V)))).mp
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)

/-- The ideal generated by the determinant form is homogeneous: the form is. -/
private theorem isHomogeneous_span_determinantForm :
    (Ideal.span {determinantForm k V}).IsHomogeneous
      (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V))) := by
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  rw [Set.mem_singleton_iff] at hx
  exact ⟨Module.finrank k V, hx ▸ determinantForm_mem_symmetricPower k V⟩

/-- A nonzero endomorphism of zero determinant exists once `dim V ≥ 2`: the elementary matrix at
a diagonal position has a zero row. -/
private theorem exists_ne_zero_det_eq_zero (h2 : 2 ≤ Module.finrank k V) :
    ∃ g : V →ₗ[k] V, g ≠ 0 ∧ LinearMap.det g = 0 := by
  have hi0 : (0 : ℕ) < Module.finrank k V := by omega
  have hi1 : (1 : ℕ) < Module.finrank k V := by omega
  set i0 : Fin (Module.finrank k V) := ⟨0, hi0⟩ with hi0def
  set i1 : Fin (Module.finrank k V) := ⟨1, hi1⟩ with hi1def
  have hne : i0 ≠ i1 := by
    rw [hi0def, hi1def, Ne, Fin.mk.injEq]
    omega
  set b := Module.finBasis k V with hb
  refine ⟨(LinearMap.toMatrix b b).symm (Matrix.single i0 i0 1), ?_, ?_⟩
  · intro hzero
    have h1 : Matrix.single i0 i0 (1 : k) = 0 := by
      rw [← LinearEquiv.apply_symm_apply (LinearMap.toMatrix b b)
        (Matrix.single i0 i0 (1 : k)), hzero, map_zero]
    have := congrFun (congrFun h1 i0) i0
    rw [Matrix.single_apply_same] at this
    exact one_ne_zero this
  · rw [← LinearMap.det_toMatrix b, LinearEquiv.apply_symm_apply]
    refine Matrix.det_eq_zero_of_row_eq_zero i1 fun j => ?_
    exact Matrix.single_apply_of_row_ne hne i0 j 1

/-- The ideal generated by the determinant form does not contain the irrelevant ideal: a
degree-one form not vanishing at a singular endomorphism is not a multiple of the determinant. -/
private theorem not_irrelevant_le_span_determinantForm (h2 : 2 ≤ Module.finrank k V) :
    ¬ (HomogeneousIdeal.irrelevant
        (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))).toIdeal ≤
      Ideal.span {determinantForm k V} := by
  obtain ⟨g, hgne, hgdet⟩ := exists_ne_zero_det_eq_zero k V h2
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (V →ₗ[k] V), φ g ≠ 0 :=
    not_forall.mp fun h => hgne ((Module.forall_dual_apply_eq_zero_iff k g).mp h)
  intro hle
  have hmem : SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V)) φ ∈
      (HomogeneousIdeal.irrelevant
        (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (ι_mem_symmetricPower_one k _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hle hmem)
  have h := congrArg (SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g)) ha
  rw [_root_.map_mul, lift_eval_determinantForm, hgdet, mul_zero,
    SymmetricAlgebra.lift_ι_apply, Module.Dual.eval_apply] at h
  exact hφ h.symm

/-- The generic point of the determinant hypersurface: the homogeneous prime generated by the
determinant form. -/
private def hypersurfaceGenericPoint (h2 : 2 ≤ Module.finrank k V) :
    ProjectiveSpectrum
      (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V))) where
  asHomogeneousIdeal :=
    ⟨Ideal.span {determinantForm k V}, isHomogeneous_span_determinantForm k V⟩
  isPrime :=
    (Ideal.span_singleton_prime (prime_determinantForm k V (by omega)).ne_zero).mpr
      (prime_determinantForm k V (by omega))
  not_irrelevant_le hi := not_irrelevant_le_span_determinantForm k V h2 fun _ hz => hi hz

/-- **`Z` is irreducible** once `dim V ≥ 2`: it is the closure of the point cut out by the
determinant form, which is a prime element. -/
public theorem isIrreducible_determinantHypersurface (h2 : 2 ≤ Module.finrank k V) :
    IsIrreducible (determinantHypersurface k V) := by
  have key : ProjectiveSpectrum.zeroLocus
      (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
      {determinantForm k V} =
      closure ({hypersurfaceGenericPoint k V h2} :
        Set (ProjectiveSpectrum
          fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))) := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    exact (ProjectiveSpectrum.zeroLocus_span _ _).symm
  have hirr : IsIrreducible (ProjectiveSpectrum.zeroLocus
      (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
      {determinantForm k V}) := by
    rw [key]
    exact isIrreducible_singleton.closure
  rw [determinantHypersurface_eq_zeroLocus]
  exact hirr

end Irreducible

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
