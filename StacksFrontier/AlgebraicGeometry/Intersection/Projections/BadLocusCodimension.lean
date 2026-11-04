module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CorankLocus
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LineThroughIdentityDomain
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLinesOfClosedSubset

/-!
# The codimension of the locus where a subvariety leaves the domain of definition

Let `X ⊊ 𝐏(V)` be a closed subset of the projective space of a finite-dimensional vector space
over an algebraically closed field and let `𝐏 = 𝐏((End V)ᵛ)` be the parameter space of the
projective transformations of `𝐏(V)`. Clause (1) of Tag 0B1S asks for `X ⊆ U(g)` along a general
line of the parameter space through `[id_V]`, and what the genericity of Tag 0B2T consumes is a
*closed* subset of `𝐏`, of codimension at least two at each of its points, containing every
class `[g]` at which the clause fails. This file produces one.

A closed point of `𝐏(V)` is cut out by a nonzero functional `f` on `V`, and it leaves `U(g)`
exactly when `f ∘ g = 0`; such an `f` forces `g` to be singular. If the rank of `g` drops by two
or more then `[g]` lies in the leading-minor locus of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CorankLocus`, which already has
codimension at least two. Otherwise the rank drops by exactly one, so the image of `g` is the
hyperplane `ker f`; since `adjugate G * G = det G • 1 = 0`, every row of the adjugate of the
matrix of `g` is then a functional vanishing on `ker f`, hence a multiple of `f`. So a
homogeneous form `h` vanishing on `X` vanishes when a row of the adjugate is substituted into
it. The entries of the adjugate are forms of degree `dim V - 1` on `End V`, so that substitution
is again a form on `𝐏`, and the subset of `Z = 𝐏 ∖ PGL(V)` it cuts out is *proper*, because the
endomorphism `v ↦ v - (f₀ v / f₀ w) • w` has image `ker f₀` and the diagonal entry of the
adjugate of its matrix at the row of `w` is `1`, so the substituted form is a nonzero multiple of
the value of `h` at `f₀` — which is nonzero for an `f₀` cutting out a point off `X`. A proper
closed subset of the irreducible `Z`, itself a proper closed subset of `𝐏`, has codimension at
least two at each of its points.

No elimination theory and no family of projective transformations over `𝐏` is used: the adjugate
provides the rational map `Z ⇢ 𝐏(V)` sending a corank-one class to its omitted point in closed
form, as a tuple of forms of degree `dim V - 1`, and substituting into a form cutting out `X` is
the preimage of `X` under it.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.adjugateForm`: the `(i, j)` entry of the adjugate of
  the matrix of degree-one elements of `Sym ((End V)ᵛ)`, a form of degree `dim V - 1`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.adjugateRow`: the functional on `V` whose
  coordinates are the entries of a row of the adjugate of the matrix of an endomorphism.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.adjugateSubstForm`: a form on `V` composed with a
  row of the adjugate, as a form on the parameter space.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.adjugateSubstLocus`: the subset of `Z` on which such
  a form vanishes.

## Main results

* `SymmetricAlgebra.lift_smul_of_mem_symmetricPower`: on `Symⁿ` the algebra map lifting `c • f`
  is `cⁿ` times the one lifting `f`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.eq_smul_of_forall_apply_eq_zero`: a functional
  vanishing on the kernel of a nonzero functional is a multiple of it.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.adjugateRow_apply_apply`: a row of the adjugate
  composed with the endomorphism is the determinant times a coordinate, so for a singular
  endomorphism the row is killed by it.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_mem_symmetricPower_forall_lift_eq_zero`: a
  closed subset missing a closed point has a homogeneous form of positive degree vanishing on it
  but not at that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_notMem_endDomain`:
  **clause (1) of Tag 0B1S — the locus where `X` leaves the domain of definition is contained in
  a closed subset of `Z` of codimension at least two at each of its points.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_clauseTwo`:
  Tag 0B1S with that clause discharged, so that only the clause-(2) half of the source's
  intermediate claim is carried.

## Implementation notes

**What is still carried, and why.** Tag 0B1S is not registered here. Its proof bounds the
codimension of the whole bad locus, and the half about clause (2) — that `r_g(X)` meets `Y`
properly for a general `[g]` — is the source's incidence variety
`T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` together with the non-jumping of fibre dimensions
in codimension one, Tag 0B2L. That needs `T` as a scheme, which the library does not have: it
would be cut out of `𝐏(V) × 𝐏(V) × 𝐏` by the `2 × 2` minors of the pair `(f', f ∘ g)`, which are
sections of `𝒪(1, 1, 1)` exactly as the determinant sections of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus` are, but that module
builds them only for three copies of one and the same projective space. The fibre of `T` over a
pair of closed points is a *linear* subspace of `𝐏` of dimension `(dim V)² - dim V`, so the
dimension of `T` does not need the source's locally trivial fibration and its double
transitivity; what is missing is the scheme `T` and the irreducibility that Tag 0B2L's
hypotheses ask of its source.

The clause-(2) half is therefore carried, in the shape the reducible form of Tag 0B2T consumes:
a closed subset `B₂` with the pointwise codimension bound, rather than an irreducible closed
subset of codimension at least two whose closed points are exactly the bad ones. That shape is
also the correct one: the bad locus is *not* irreducible in general. Its clause-(1) part lies in
`Z`, while its clause-(2) part meets `PGL(V)` — for `X` and `Y` two distinct lines in `𝐏²` the
latter contains the classes with `r_g(X) = Y`, which are invertible — so the Zariski closure of
the bad locus has a component inside `Z` and a component meeting the complement of `Z`, and no
irreducible closed subset has exactly the bad closed points.

**Which row of the adjugate.** Only one is used, chosen so that `f₀` does not vanish on the
corresponding basis vector. Any row of the adjugate of a singular matrix is killed by it, and a
row that happens to vanish is harmless because the substituted form has positive degree, so it
also vanishes at the zero functional; the proper-inclusion witness is the one place where a
specific row has to be nonzero, and there it is made so by construction.

**Positive degree.** The form cutting out `X` is taken of degree at least one by multiplying a
homogeneous component of an element of the vanishing ideal by a degree-one form not vanishing at
`f₀`. Without that the substituted form could be a nonzero constant, which vanishes nowhere.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace SymmetricAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Rescaling a linear map rescales its lift on a homogeneous element.** On the `n`-th
symmetric power the algebra map lifting `c • f` is `c ^ n` times the one lifting `f`, because
both are determined by their values on products of `n` degree-one generators.

Stated for a lift to an arbitrary commutative `R`-algebra and not only to `R` itself: the
case of a functional is what the codimension bound below uses, and the case of a lift to
another symmetric algebra is what the scalar-invariance of the projective transformation
`r_g` uses. -/
public theorem lift_smul_of_mem_symmetricPower {A : Type*} [CommRing A] [Algebra R A] (c : R)
    (f : M →ₗ[R] A) {n : ℕ} {z : SymmetricAlgebra R M}
    (hz : z ∈ SymPow.symmetricPower n R M) :
    SymmetricAlgebra.lift (c • f) z = c ^ n • SymmetricAlgebra.lift f z := by
  rw [symmetricPower_eq_span_prod_ι] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [map_prod, map_prod]
    simp only [SymmetricAlgebra.lift_ι_apply, LinearMap.smul_apply, Algebra.smul_def]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      map_pow]
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy, smul_add]
  | smul a x _ ih =>
    rw [Algebra.smul_def, map_mul, map_mul, ih, AlgHom.commutes, AlgHom.commutes,
      Algebra.smul_def, Algebra.smul_def]
    ring

/-- The algebra map lifting a functional is linear over the base ring. -/
private theorem lift_smul_scalar {A : Type*} [CommRing A] [Algebra R A] (ψ : M →ₗ[R] A) (a : R)
    (z : SymmetricAlgebra R M) :
    SymmetricAlgebra.lift ψ (a • z) = a • SymmetricAlgebra.lift ψ z := by
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.smul_def]

end SymmetricAlgebra

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- Subtracting from `v` the multiple of `w` with the same value under `f` lands in `ker f`. -/
private theorem apply_sub_smul_eq_zero {f : Module.Dual k V} {w : V} (hw : f w ≠ 0) (v : V) :
    f (v - ((f w)⁻¹ * f v) • w) = 0 := by
  rw [map_sub, map_smul, smul_eq_mul, mul_comm ((f w)⁻¹) (f v), mul_assoc,
    inv_mul_cancel₀ hw, mul_one, sub_self]

/-- **A functional vanishing on the kernel of a nonzero functional is a multiple of it.** -/
public theorem eq_smul_of_forall_apply_eq_zero {f φ : Module.Dual k V} {w : V} (hw : f w ≠ 0)
    (hφ : ∀ v, f v = 0 → φ v = 0) : φ = ((f w)⁻¹ * φ w) • f := by
  refine LinearMap.ext fun v => ?_
  have h := hφ _ (apply_sub_smul_eq_zero k V hw v)
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
  rw [LinearMap.smul_apply, smul_eq_mul, h]
  ring

section Form

variable [Module.Finite k V]

/-- The matrix of degree-one elements of `Sym ((End V)ᵛ)` given by the matrix coefficients in the
basis `Module.finBasis k V` of `V`. -/
private def coeffMatrix :
    Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V))
      (SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V))) :=
  Matrix.of fun a b => SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V))
    (coeffBasis (Module.finBasis k V) (a, b))

/-- **A cofactor, as a form on `End V`.** The `(i, j)` entry of the adjugate of the matrix of
degree-one elements of `Sym ((End V)ᵛ)`: a form of degree `dim V - 1` whose value at an
endomorphism is the corresponding entry of the adjugate of its matrix. -/
@[no_expose] public def adjugateForm (i j : Fin (Module.finrank k V)) :
    SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V)) :=
  ((coeffMatrix k V).updateRow j (Pi.single i 1)).det

/-- An adjugate form evaluated at a point, as the adjugate of the matrix of coefficients.

Public because `adjugateForm` is `@[no_expose]`: this is the only way a consumer can evaluate
`SymmetricAlgebra.lift` on it. -/
public theorem lift_adjugateForm {A : Type*} [CommRing A] [Algebra k A]
    (i j : Fin (Module.finrank k V)) (f : Module.Dual k (V →ₗ[k] V) →ₗ[k] A) :
    SymmetricAlgebra.lift f (adjugateForm k V i j) =
      (Matrix.of fun a b : Fin (Module.finrank k V) =>
        f (coeffBasis (Module.finBasis k V) (a, b))).adjugate i j := by
  classical
  rw [adjugateForm, Matrix.adjugate_apply]
  refine (RingHom.map_det (SymmetricAlgebra.lift f).toRingHom _).trans ?_
  congr 1
  ext a b
  rcases eq_or_ne a j with rfl | hne
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self,
      Matrix.updateRow_self, Pi.single_apply, Pi.single_apply]
    split <;> simp
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne hne,
      Matrix.updateRow_ne hne, coeffMatrix]
    simp [SymmetricAlgebra.lift_ι_apply]

/-- **An adjugate form evaluates to the corresponding entry of the adjugate.** -/
public theorem lift_eval_adjugateForm (i j : Fin (Module.finrank k V)) (g : V →ₗ[k] V) :
    SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g) (adjugateForm k V i j) =
      (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).adjugate i j := by
  rw [lift_adjugateForm]
  congr 1
  ext a b
  simp [Module.Dual.eval_apply, coeffBasis_apply]

/-- **An adjugate form is homogeneous of degree `dim V - 1`.** Expanding the determinant, every
permutation contributes a product of one degree-zero entry, coming from the row of constants,
and `dim V - 1` degree-one entries. -/
public theorem adjugateForm_mem_symmetricPower (i j : Fin (Module.finrank k V)) :
    adjugateForm k V i j ∈
      SymPow.symmetricPower (Module.finrank k V - 1) k (Module.Dual k (V →ₗ[k] V)) := by
  classical
  rw [adjugateForm, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have hdeg : ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank k V))),
      ((coeffMatrix k V).updateRow j (Pi.single i 1)) (σ a) a ∈
        SymPow.symmetricPower (if σ a = j then 0 else 1) k
          (Module.Dual k (V →ₗ[k] V)) := by
    intro a _
    by_cases ha : σ a = j
    · rw [if_pos ha, ha, Matrix.updateRow_self, Pi.single_apply]
      split
      · exact SetLike.one_mem_graded _
      · exact zero_mem _
    · rw [if_neg ha, Matrix.updateRow_ne ha, coeffMatrix]
      exact ι_mem_symmetricPower_one k _ _
  have h := SetLike.prod_mem_graded
    (A := fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
    (F := (Finset.univ : Finset (Fin (Module.finrank k V))))
    (g := fun a => ((coeffMatrix k V).updateRow j (Pi.single i 1)) (σ a) a)
    (fun a => if σ a = j then 0 else 1) hdeg
  have hsum : ∑ a : Fin (Module.finrank k V), (if σ a = j then 0 else 1) =
      Module.finrank k V - 1 := by
    have hiff : ∀ a : Fin (Module.finrank k V), (if σ a = j then 0 else 1) =
        (if a = σ.symm j then 0 else 1) := by
      intro a
      congr 1
      simp [Equiv.eq_symm_apply]
    rw [Finset.sum_congr rfl fun a _ => hiff a,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (σ.symm j))]
    rw [if_pos rfl, zero_add]
    rw [Finset.sum_congr rfl (fun a ha => if_neg (Finset.ne_of_mem_erase ha)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  rwa [hsum] at h

/-- **The functional cut out by a row of the adjugate.** Its coordinates in the basis dual to
`Module.finBasis k V` are the entries of the `i`-th row of the adjugate of the matrix of `g`. -/
public def adjugateRow (g : V →ₗ[k] V) (i : Fin (Module.finrank k V)) : Module.Dual k V :=
  ∑ j, (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).adjugate i j •
    (Module.finBasis k V).coord j

/-- The value of `adjugateRow k V g i` at `v` is the sum over `j` of the `(i, j)` entry of the
adjugate times the `j`-th coordinate of `v` in `Module.finBasis k V`. -/
public theorem adjugateRow_apply (g : V →ₗ[k] V) (i : Fin (Module.finrank k V)) (v : V) :
    adjugateRow k V g i v =
      ∑ j, (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).adjugate i j *
        (Module.finBasis k V).repr v j := by
  simp [adjugateRow, Module.Basis.coord_apply]

/-- **A row of the adjugate composed with the endomorphism is the determinant.** This is
`adjugate A * A = det A • 1` read on one row, so for a singular `g` every row of the adjugate of
its matrix is a functional killed by `g`. -/
public theorem adjugateRow_apply_apply (g : V →ₗ[k] V) (i : Fin (Module.finrank k V)) (v : V) :
    adjugateRow k V g i (g v) =
      LinearMap.det g * (Module.finBasis k V).repr v i := by
  classical
  have hmv : ∀ (M : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k)
      (x : Fin (Module.finrank k V) → k) (a : Fin (Module.finrank k V)),
      Matrix.mulVec M x a = ∑ j, M a j * x j := fun _ _ _ => rfl
  rw [adjugateRow_apply, ← hmv,
    ← LinearMap.toMatrix_mulVec_repr (Module.finBasis k V) (Module.finBasis k V) g v,
    Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul,
    LinearMap.det_toMatrix]

/-- The `k`-linear map `V → Sym ((End V)ᵛ)` substituting the `i`-th row of the adjugate for a
vector: it sends `v` to the combination of the adjugate forms with the coordinates of `v`. -/
private def adjugateSubst (i : Fin (Module.finrank k V)) :
    V →ₗ[k] SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V)) :=
  ∑ j, LinearMap.smulRight ((Module.finBasis k V).coord j) (adjugateForm k V i j)

/-- **A form on `𝐏(V)` substituted along a row of the adjugate.** Composing a form `h` on `V`
with the `i`-th row of the adjugate gives a form on the parameter space whose value at an
endomorphism `g` is the value of `h` at the functional
`AlgebraicGeometry.ProjectiveSpaceOfModule.adjugateRow`. -/
@[no_expose] public def adjugateSubstForm (i : Fin (Module.finrank k V))
    (h : SymmetricAlgebra k V) : SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V)) :=
  SymmetricAlgebra.lift (adjugateSubst k V i) h

/-- **The substituted form evaluates to the value of the original at the adjugate row.**

Public because `adjugateSubstForm` is `@[no_expose]`: this is the only way a consumer can
evaluate `SymmetricAlgebra.lift` on it. -/
public theorem lift_eval_adjugateSubstForm (i : Fin (Module.finrank k V)) (g : V →ₗ[k] V)
    (h : SymmetricAlgebra k V) :
    SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g) (adjugateSubstForm k V i h) =
      SymmetricAlgebra.lift (adjugateRow k V g i) h := by
  have hcomp : (SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g)).comp
      (SymmetricAlgebra.lift (adjugateSubst k V i)) =
      SymmetricAlgebra.lift (adjugateRow k V g i) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun v => ?_)
    simp only [LinearMap.comp_apply]
    show SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g)
        (SymmetricAlgebra.lift (adjugateSubst k V i) (SymmetricAlgebra.ι k V v)) =
      SymmetricAlgebra.lift (adjugateRow k V g i) (SymmetricAlgebra.ι k V v)
    rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.lift_ι_apply, adjugateSubst,
      LinearMap.sum_apply, map_sum, adjugateRow_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smulRight_apply, SymmetricAlgebra.lift_smul_scalar, smul_eq_mul,
      lift_eval_adjugateForm, Module.Basis.coord_apply, mul_comm]
  exact DFunLike.congr_fun hcomp h

/-- On the `j`-th vector of `Module.finBasis k V`, `adjugateRow k V g i` takes the value of the
`(i, j)` entry of the adjugate of the matrix of `g`. -/
public theorem adjugateRow_apply_basis (g : V →ₗ[k] V) (i j : Fin (Module.finrank k V)) :
    adjugateRow k V g i (Module.finBasis k V j) =
      (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V) g).adjugate i j := by
  classical
  rw [adjugateRow_apply]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- **An endomorphism whose image is a given hyperplane.** It subtracts from a vector the
multiple of `w` with the same value under `f`, so it is the identity on the kernel of `f` and
its image is that kernel. Its matrix differs from the identity in the row of `w` alone, so the
diagonal entry of its adjugate at that row is `1`.

Public because the analysis of the determinant hypersurface in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.SingularGoodEndomorphism` uses the very
same endomorphism: it is the retraction of `𝐏(V)` onto the hyperplane `𝐏(Im g)` away from the
point cut out by `f`, which is the projection the source's "Some details omitted" step
projects along. -/
public def hyperplaneProjection (f : Module.Dual k V) (w : V) : V →ₗ[k] V :=
  LinearMap.id - (f w)⁻¹ • LinearMap.smulRight f w

omit [Module.Finite k V] in
/-- `hyperplaneProjection k V f w` sends `v` to `v - ((f w)⁻¹ * f v) • w`. -/
public theorem hyperplaneProjection_apply (f : Module.Dual k V) (w v : V) :
    hyperplaneProjection k V f w v = v - ((f w)⁻¹ * f v) • w := by
  rw [hyperplaneProjection]
  simp [LinearMap.smulRight_apply, smul_smul]

omit [Module.Finite k V] in
/-- If `f w ≠ 0`, then `f` vanishes on the image of `hyperplaneProjection k V f w`. -/
public theorem comp_hyperplaneProjection_eq_zero {f : Module.Dual k V} {w : V} (hw : f w ≠ 0) :
    f ∘ₗ hyperplaneProjection k V f w = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, hyperplaneProjection_apply, apply_sub_smul_eq_zero k V hw]
  rfl

omit [Module.Finite k V] in
/-- `hyperplaneProjection k V f w` fixes every vector in the kernel of `f`. -/
public theorem hyperplaneProjection_apply_of_apply_eq_zero (f : Module.Dual k V) (w : V) {v : V}
    (hv : f v = 0) : hyperplaneProjection k V f w v = v := by
  rw [hyperplaneProjection_apply, hv, mul_zero, zero_smul, sub_zero]

omit [Module.Finite k V] in
/-- **The image of the endomorphism is the hyperplane cut out by `f`.** It is contained in that
kernel because `f` kills the endomorphism, and contains it because the endomorphism fixes it
pointwise. -/
public theorem range_hyperplaneProjection {f : Module.Dual k V} {w : V} (hw : f w ≠ 0) :
    LinearMap.range (hyperplaneProjection k V f w) = LinearMap.ker f := by
  refine le_antisymm ?_ fun v hv => ?_
  · rintro _ ⟨v, rfl⟩
    exact LinearMap.congr_fun (comp_hyperplaneProjection_eq_zero k V hw) v
  · exact ⟨v, hyperplaneProjection_apply_of_apply_eq_zero k V f w (LinearMap.mem_ker.mp hv)⟩

omit [Module.Finite k V] in
/-- **The kernel of the endomorphism is the line of `w`.** -/
public theorem ker_hyperplaneProjection {f : Module.Dual k V} {w : V} (hw : f w ≠ 0) :
    LinearMap.ker (hyperplaneProjection k V f w) = Submodule.span k {w} := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · have h := LinearMap.mem_ker.mp hv
    rw [hyperplaneProjection_apply, sub_eq_zero] at h
    exact h ▸ Submodule.mem_span_singleton.mpr ⟨(f w)⁻¹ * f v, rfl⟩
  · rintro _ rfl
    refine LinearMap.mem_ker.mpr ?_
    rw [hyperplaneProjection_apply, inv_mul_cancel₀ hw, one_smul, sub_self]

omit [Module.Finite k V] in
/-- **The endomorphism is nonzero** as soon as the kernel of `f` is nonzero: it fixes that
kernel pointwise. -/
public theorem hyperplaneProjection_ne_zero {f : Module.Dual k V}
    (hker : LinearMap.ker f ≠ ⊥) (w : V) : hyperplaneProjection k V f w ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro hzero
  exact hv0 (by
    rw [← hyperplaneProjection_apply_of_apply_eq_zero k V f w (LinearMap.mem_ker.mp hv), hzero,
      LinearMap.zero_apply])

private theorem toMatrix_hyperplaneProjection_of_ne (f : Module.Dual k V)
    (j₀ : Fin (Module.finrank k V)) {i : Fin (Module.finrank k V)} (hi : i ≠ j₀)
    (j : Fin (Module.finrank k V)) :
    LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
        (hyperplaneProjection k V f (Module.finBasis k V j₀)) i j =
      (1 : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k) i j := by
  classical
  rw [LinearMap.toMatrix_apply, hyperplaneProjection_apply]
  simp [Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply, hi, eq_comm]

/-- **The diagonal entry of the adjugate at the distinguished row is `1`.** Replacing that row of
the matrix by the corresponding standard basis vector turns it into the identity. -/
private theorem adjugate_toMatrix_hyperplaneProjection (f : Module.Dual k V)
    (j₀ : Fin (Module.finrank k V)) :
    (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
      (hyperplaneProjection k V f (Module.finBasis k V j₀))).adjugate j₀ j₀ = 1 := by
  classical
  rw [Matrix.adjugate_apply]
  have h1 : (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
      (hyperplaneProjection k V f (Module.finBasis k V j₀))).updateRow j₀
        (Pi.single j₀ 1) = 1 := by
    ext i j
    rcases eq_or_ne i j₀ with rfl | hi
    · rw [Matrix.updateRow_self, Pi.single_apply, Matrix.one_apply]
      simp [eq_comm]
    · rw [Matrix.updateRow_ne hi, toMatrix_hyperplaneProjection_of_ne k V f j₀ hi]
  rw [h1, Matrix.det_one]

/-- Each value of the substitution map is homogeneous of degree `dim V - 1`. -/
private theorem adjugateSubst_mem_symmetricPower (i : Fin (Module.finrank k V)) (v : V) :
    adjugateSubst k V i v ∈
      SymPow.symmetricPower (Module.finrank k V - 1) k (Module.Dual k (V →ₗ[k] V)) := by
  rw [adjugateSubst, LinearMap.sum_apply]
  simp only [LinearMap.smulRight_apply]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (adjugateForm_mem_symmetricPower k V i j)

/-- **The substituted form is homogeneous**, of degree `d * (dim V - 1)` for `h` of degree `d`:
the substitution replaces each degree-one generator by a form of degree `dim V - 1`. -/
public theorem adjugateSubstForm_mem_symmetricPower (i : Fin (Module.finrank k V)) {d : ℕ}
    {h : SymmetricAlgebra k V} (hh : h ∈ SymPow.symmetricPower d k V) :
    adjugateSubstForm k V i h ∈
      SymPow.symmetricPower (d * (Module.finrank k V - 1)) k
        (Module.Dual k (V →ₗ[k] V)) := by
  rw [SymmetricAlgebra.symmetricPower_eq_span_prod_ι] at hh
  rw [adjugateSubstForm]
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [map_prod]
    have h := SetLike.prod_mem_graded
      (A := fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
      (F := (Finset.univ : Finset (Fin d)))
      (g := fun l => SymmetricAlgebra.lift (adjugateSubst k V i)
        (SymmetricAlgebra.ι k V (s l)))
      (fun _ => Module.finrank k V - 1)
      (fun l _ => by
        rw [SymmetricAlgebra.lift_ι_apply]
        exact adjugateSubst_mem_symmetricPower k V i (s l))
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [SymmetricAlgebra.lift_smul_scalar]; exact Submodule.smul_mem _ _ ih

/-- The space of parameters has dimension `(dim V)²`. -/
private theorem finrank_dual_end :
    Module.finrank k (Module.Dual k (V →ₗ[k] V)) = Module.finrank k V * Module.finrank k V := by
  rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]

/-- The space of parameters is nontrivial as soon as `V` has positive dimension. -/
private theorem nontrivial_dual_end (h : 0 < Module.finrank k V) :
    Nontrivial (Module.Dual k (V →ₗ[k] V)) := by
  refine Module.nontrivial_of_finrank_pos (R := k) ?_
  rw [finrank_dual_end]
  exact Nat.mul_pos h h

/-- If a row of the adjugate of `g` vanishes on the kernel of `f`, the substituted form evaluates
at `g` to the `d`-th power of its normalized value at `w`, times the value of `h` at `f`. -/
private theorem lift_eval_adjugateSubstForm_of_forall_apply_eq_zero
    (i : Fin (Module.finrank k V)) (g : V →ₗ[k] V) {d : ℕ} {h : SymmetricAlgebra k V}
    (hh : h ∈ SymPow.symmetricPower d k V) {f : Module.Dual k V} {w : V} (hw : f w ≠ 0)
    (hvan : ∀ v, f v = 0 → adjugateRow k V g i v = 0) :
    SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g) (adjugateSubstForm k V i h) =
      ((f w)⁻¹ * adjugateRow k V g i w) ^ d * SymmetricAlgebra.lift f h := by
  rw [lift_eval_adjugateSubstForm]
  conv_lhs => rw [eq_smul_of_forall_apply_eq_zero k V hw hvan]
  rw [SymmetricAlgebra.lift_smul_of_mem_symmetricPower _ _ hh, smul_eq_mul]

end Form

section Vanishing

variable [IsAlgClosed k] [FiniteDimensional k V]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- **A closed subset of `𝐏(V)` missing a closed point has a homogeneous form of positive degree
vanishing on it but not at that point.** The subset is the zero locus of its vanishing ideal,
which is homogeneous, so one homogeneous component of an element not vanishing at the point
already fails to vanish there; multiplying by a degree-one form not vanishing at the point makes
the degree positive. -/
public theorem exists_mem_symmetricPower_forall_lift_eq_zero
    {S : Set (projectiveSpaceOfModule k V)} (hS : IsClosed S)
    (f₀ : Module.Dual k V) (hf₀ : f₀ ≠ 0)
    (hnot : linearFunctionalPoint k V f₀ hf₀ ∉ S) :
    ∃ (d : ℕ) (h : SymmetricAlgebra k V), 1 ≤ d ∧ h ∈ SymPow.symmetricPower d k V ∧
      (∀ (f : Module.Dual k V) (hf : f ≠ 0), linearFunctionalPoint k V f hf ∈ S →
        SymmetricAlgebra.lift f h = 0) ∧
      SymmetricAlgebra.lift f₀ h ≠ 0 := by
  classical
  set A : ℕ → Submodule k (SymmetricAlgebra k V) := fun n => SymPow.symmetricPower n k V with hA
  set T : Set (ProjectiveSpectrum A) := S with hT
  set q₀ := linearFunctionalPoint k V f₀ hf₀ with hq₀
  have hzero : ProjectiveSpectrum.zeroLocus A
      (ProjectiveSpectrum.vanishingIdeal T : Set (SymmetricAlgebra k V)) = T :=
    (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure A T).trans hS.closure_eq
  obtain ⟨z, hzI, hzq⟩ : ∃ z ∈ (ProjectiveSpectrum.vanishingIdeal T).toIdeal,
      z ∉ q₀.asHomogeneousIdeal.toIdeal :=
    Set.not_subset.mp fun hsub =>
      hnot (hzero ▸ (ProjectiveSpectrum.mem_zeroLocus A q₀ _).mpr hsub)
  obtain ⟨d, hd⟩ : ∃ d : ℕ,
      (DirectSum.decompose A z d : SymmetricAlgebra k V) ∉ q₀.asHomogeneousIdeal.toIdeal :=
    not_forall.mp fun hall =>
      hzq ((q₀.asHomogeneousIdeal.isHomogeneous.mem_iff).mpr hall)
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hf₀
  refine ⟨d + 1, (DirectSum.decompose A z d : SymmetricAlgebra k V) *
    SymmetricAlgebra.ι k V w, Nat.le_add_left 1 d, ?_, ?_, ?_⟩
  · exact SetLike.mul_mem_graded (SetLike.coe_mem _) (ι_mem_symmetricPower_one k V w)
  · intro f hf hfS
    have hmem : (DirectSum.decompose A z d : SymmetricAlgebra k V) *
        SymmetricAlgebra.ι k V w ∈ (linearFunctionalPoint k V f hf).asHomogeneousIdeal.toIdeal :=
      Ideal.mul_mem_right _ _
        ((ProjectiveSpectrum.mem_vanishingIdeal T _).mp
          (((ProjectiveSpectrum.vanishingIdeal T).isHomogeneous.mem_iff).mp hzI d)
          (linearFunctionalPoint k V f hf) hfS)
    rw [← SymPow.symAlgMap_eq_zero_iff_lift_eq_zero f
      (SetLike.mul_mem_graded (A := A) (SetLike.coe_mem _) (ι_mem_symmetricPower_one k V w))]
    exact (linearFunctionalPoint_mem k V f hf _).mp hmem
  · rw [_root_.map_mul, SymmetricAlgebra.lift_ι_apply]
    refine mul_ne_zero (fun hc => hd ?_) hw
    refine (linearFunctionalPoint_mem k V f₀ hf₀ _).mpr ?_
    exact (SymPow.symAlgMap_eq_zero_iff_lift_eq_zero f₀
      (SetLike.coe_mem (DirectSum.decompose A z d))).mpr hc

omit [IsAlgClosed k] in
/-- **An endomorphism killed by a nonzero functional is singular.** An invertible endomorphism is
surjective, so a functional vanishing on its image vanishes. -/
public theorem det_eq_zero_of_comp_eq_zero {f : Module.Dual k V} (hf : f ≠ 0) {g : V →ₗ[k] V}
    (hfg : f ∘ₗ g = 0) : LinearMap.det g = 0 := by
  by_contra hdet
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine hf (LinearMap.ext fun v => ?_)
  have hgv : g ((↑u⁻¹ : Module.End k V) v) = v := by
    have h : ((u : Module.End k V) * (↑u⁻¹ : Module.End k V)) v = v := by
      rw [u.mul_inv]; rfl
    rwa [Module.End.mul_apply, hu] at h
  rw [← hgv]
  exact LinearMap.congr_fun hfg _

omit [IsAlgClosed k] in
/-- The kernel of a nonzero functional is a hyperplane. -/
public theorem finrank_ker_add_one {f : Module.Dual k V} (hf : f ≠ 0) :
    Module.finrank k ↥(LinearMap.ker f) + 1 = Module.finrank k V := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hf
  have hsurj : Function.Surjective f := fun c =>
    ⟨(c / f v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩
  have hrange : Module.finrank k ↥(LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have h := LinearMap.finrank_range_add_finrank_ker f
  omega

end Vanishing

section Locus

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- **A closed point lies in the zero locus of a homogeneous form exactly when the form evaluates
to zero at any representative.** -/
public theorem coe_notMem_basicOpen_iff_lift_eval_eq_zero {m : ℕ}
    {z : SymmetricAlgebra k (Module.Dual k (V →ₗ[k] V))}
    (hz : z ∈ SymPow.symmetricPower m k (Module.Dual k (V →ₗ[k] V)))
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∉
        Proj.basicOpen (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V))) z ↔
      SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g) z = 0 := by
  rw [Proj.mem_basicOpen, not_not, val_eq_linearFunctionalPoint k V p g hg hpg,
    linearFunctionalPoint_mem, SymPow.symAlgMap_eq_zero_iff_lift_eq_zero _ hz]

/-- **The locus in `Z` cut out by a substituted form.** The points of the determinant
hypersurface at which the form obtained by substituting the `i`-th row of the adjugate into `h`
also vanishes. -/
@[no_expose] public def adjugateSubstLocus (i : Fin (Module.finrank k V))
    (h : SymmetricAlgebra k V) :
    Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) :=
  determinantHypersurface k V ∩
    ((Proj.basicOpen (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
        (adjugateSubstForm k V i h) :
      (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))).Opens) :
      Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))))ᶜ

omit [IsAlgClosed k] in
/-- The substituted locus `adjugateSubstLocus k V i h` is closed. -/
public theorem isClosed_adjugateSubstLocus (i : Fin (Module.finrank k V))
    (h : SymmetricAlgebra k V) : IsClosed (adjugateSubstLocus k V i h) :=
  (isClosed_determinantHypersurface k V).inter
    (Proj.basicOpen (fun n => SymPow.symmetricPower n k (Module.Dual k (V →ₗ[k] V)))
      (adjugateSubstForm k V i h)).isOpen.isClosed_compl

omit [IsAlgClosed k] in
/-- The substituted locus `adjugateSubstLocus k V i h` lies in the determinant hypersurface. -/
public theorem adjugateSubstLocus_subset_determinantHypersurface
    (i : Fin (Module.finrank k V)) (h : SymmetricAlgebra k V) :
    adjugateSubstLocus k V i h ⊆ determinantHypersurface k V := Set.inter_subset_left

/-- The class of a singular endomorphism lies in the determinant hypersurface. -/
private theorem coe_mem_determinantHypersurface_of_det_eq_zero
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg)
    (hdet : LinearMap.det g = 0) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈ determinantHypersurface k V :=
  (mem_determinantHypersurface_iff k V).mpr fun hmem =>
    (coe_mem_invertibleLocus_iff_det_ne_zero k V p g hg hpg).mp hmem hdet

/-- **A class of corank one whose omitted point lies in `X` lies in the substituted locus.** The
functional cut out by a row of the adjugate is killed by `g`, hence vanishes on the image of `g`;
for a corank-one `g` that image is the kernel of the functional `f` cutting out the omitted
point, so the row is a multiple of `f`, at which `h` vanishes. -/
public theorem coe_mem_adjugateSubstLocus (i : Fin (Module.finrank k V)) {d : ℕ}
    {h : SymmetricAlgebra k V} (hh : h ∈ SymPow.symmetricPower d k V)
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hpg : dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg)
    {f : Module.Dual k V} (hf : f ≠ 0) (hfg : f ∘ₗ g = 0)
    (hfh : SymmetricAlgebra.lift f h = 0)
    (hrank : ¬ Module.finrank k ↥(LinearMap.range g) + 2 ≤ Module.finrank k V) :
    (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈
      adjugateSubstLocus k V i h := by
  have hdet : LinearMap.det g = 0 := det_eq_zero_of_comp_eq_zero k V hf hfg
  have hle : LinearMap.range g ≤ LinearMap.ker f := by
    rintro _ ⟨u, rfl⟩
    exact LinearMap.congr_fun hfg u
  have hkerf := finrank_ker_add_one k V hf
  have hrange : Module.finrank k ↥(LinearMap.range g) =
      Module.finrank k ↥(LinearMap.ker f) :=
    le_antisymm (Submodule.finrank_mono hle) (by omega)
  have heq : LinearMap.range g = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle hrange
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hf
  have hvan : ∀ v : V, f v = 0 → adjugateRow k V g i v = 0 := by
    intro v hv
    obtain ⟨u, hu⟩ : ∃ u : V, g u = v := by
      rw [← LinearMap.mem_range, heq]
      exact hv
    rw [← hu, adjugateRow_apply_apply, hdet, zero_mul]
  have hzero : SymmetricAlgebra.lift (Module.Dual.eval k (V →ₗ[k] V) g)
      (adjugateSubstForm k V i h) = 0 := by
    rw [lift_eval_adjugateSubstForm_of_forall_apply_eq_zero k V i g hh hw hvan, hfh, mul_zero]
  exact ⟨coe_mem_determinantHypersurface_of_det_eq_zero k V p g hg hpg hdet,
    (coe_notMem_basicOpen_iff_lift_eval_eq_zero k V
      (adjugateSubstForm_mem_symmetricPower k V i hh) p g hg hpg).mpr hzero⟩

/-- **The substituted locus is a proper subset of the determinant hypersurface** as soon as `h`
does not vanish at the functional `f₀`: the endomorphism
`AlgebraicGeometry.ProjectiveSpaceOfModule.hyperplaneProjection` with image the kernel of `f₀`
is singular, and the chosen row of the adjugate of its matrix is a nonzero multiple of `f₀`. -/
public theorem adjugateSubstLocus_ne_determinantHypersurface {d : ℕ}
    {h : SymmetricAlgebra k V} (hh : h ∈ SymPow.symmetricPower d k V)
    (h2 : 2 ≤ Module.finrank k V) {f₀ : Module.Dual k V} (hf₀ : f₀ ≠ 0)
    (hf₀h : SymmetricAlgebra.lift f₀ h ≠ 0) (j₀ : Fin (Module.finrank k V))
    (hj₀ : f₀ (Module.finBasis k V j₀) ≠ 0) :
    adjugateSubstLocus k V j₀ h ≠ determinantHypersurface k V := by
  set g₀ := hyperplaneProjection k V f₀ (Module.finBasis k V j₀) with hg₀def
  have hfg₀ : f₀ ∘ₗ g₀ = 0 := comp_hyperplaneProjection_eq_zero k V hj₀
  have hdet₀ : LinearMap.det g₀ = 0 := det_eq_zero_of_comp_eq_zero k V hf₀ hfg₀
  have hfix : ∀ v : V, f₀ v = 0 → g₀ v = v := fun v hv =>
    hyperplaneProjection_apply_of_apply_eq_zero k V f₀ _ hv
  have hker₀ : LinearMap.ker f₀ ≠ ⊥ := by
    intro hbot
    have := finrank_ker_add_one k V hf₀
    rw [hbot, finrank_bot] at this
    omega
  have hg₀ne : g₀ ≠ 0 := hyperplaneProjection_ne_zero k V hker₀ _
  set p₀ := (dualEndClosedPointsEquiv k V).symm (Projectivization.mk k g₀ hg₀ne) with hp₀def
  have hp₀ : dualEndClosedPointsEquiv k V p₀ = Projectivization.mk k g₀ hg₀ne := by
    rw [hp₀def, Equiv.apply_symm_apply]
  have hZ := coe_mem_determinantHypersurface_of_det_eq_zero k V p₀ g₀ hg₀ne hp₀ hdet₀
  have hvan : ∀ v : V, f₀ v = 0 → adjugateRow k V g₀ j₀ v = 0 := by
    intro v hv
    rw [← hfix v hv, adjugateRow_apply_apply, hdet₀, zero_mul]
  have hrow : adjugateRow k V g₀ j₀ (Module.finBasis k V j₀) = 1 := by
    rw [adjugateRow_apply_basis, hg₀def, adjugate_toMatrix_hyperplaneProjection]
  have hnotW : (p₀ : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∉
      adjugateSubstLocus k V j₀ h := by
    intro hmem
    have hz := (coe_notMem_basicOpen_iff_lift_eval_eq_zero k V
      (adjugateSubstForm_mem_symmetricPower k V j₀ hh) p₀ g₀ hg₀ne hp₀).mp hmem.2
    rw [lift_eval_adjugateSubstForm_of_forall_apply_eq_zero k V j₀ g₀ hh hj₀ hvan, hrow,
      mul_one] at hz
    exact (mul_ne_zero (pow_ne_zero d (inv_ne_zero hj₀)) hf₀h) hz
  intro heq
  exact hnotW (heq ▸ hZ)

/-- **A nonempty proper closed subset of `𝐏(V)` forces `dim V ≥ 2`.** It contains a closed point
and misses one, and the closed points of `𝐏(V)` are the classes of nonzero functionals, of which
there is only one when `V` is a line. -/
public theorem two_le_finrank_of_isClosed_ne_univ [Nontrivial V]
    {X : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hXne : X ≠ Set.univ)
    (hXn : X.Nonempty) : 2 ≤ Module.finrank k V := by
  obtain ⟨f₁, hf₁, h₁⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k V hXc hXne
  obtain ⟨f₂, hf₂, h₂⟩ := exists_linearFunctionalPoint_mem_of_isClosed k V hXn hXc
  by_contra hlt
  have h1 : Module.finrank k V = 1 := by
    have := Module.finrank_pos (R := k) (M := V)
    omega
  have hdual : Module.finrank k (Module.Dual k V) = 1 := by
    rw [Subspace.dual_finrank_eq, h1]
  have hspan : Submodule.span k {f₁} = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hf₁, hdual])
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hspan ▸ (Submodule.mem_top : f₂ ∈ (⊤ : Submodule k (Module.Dual k V))))
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hf₂ hc.symm
  have hceq : (Units.mk0 c hc0) • f₁ = f₂ := by rw [Units.smul_def, Units.val_mk0, hc]
  refine h₁ ?_
  rw [← linearFunctionalPoint_units_smul k V (Units.mk0 c hc0) f₁ hf₁ (by rw [hceq]; exact hf₂)]
  rw [show linearFunctionalPoint k V ((Units.mk0 c hc0) • f₁) (by rw [hceq]; exact hf₂) =
    linearFunctionalPoint k V f₂ hf₂ from by congr 1]
  exact h₂

/-- **Clause (1) of Tag 0B1S: the locus where a proper closed subvariety leaves the domain of
definition has codimension at least two.** For a closed point `[g]` of the parameter space at
which some point of `X` fails to lie in `U(g)` the endomorphism `g` is singular. If its rank
drops by two or more its class lies in the leading-minor locus, of codimension at least two by
Tag 0B1S's own analysis of `Z`. Otherwise the rank drops by exactly one, the image of `g` is
the hyperplane cut out by the functional `f` naming the omitted point of `X`, every row of the
adjugate of the matrix of `g` is a multiple of `f`, and a form cutting out `X` therefore vanishes
when the chosen row is substituted into it. That substituted form cuts a proper closed subset out
of the irreducible `Z`, which is itself a proper closed subset of `𝐏`, so the closure of each of
its points is the bottom of a strict chain of length two. -/
public theorem exists_isClosed_two_le_codimension_notMem_endDomain
    (X : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hXne : X ≠ Set.univ)
    (h2 : 2 ≤ Module.finrank k V) :
    ∃ B : Set (projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))), IsClosed B ∧
      B ⊆ determinantHypersurface k V ∧
      (∀ (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (g : V →ₗ[k] V) (hg : g ≠ 0),
        dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg →
        ¬ X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)) →
        (p : projectiveSpaceOfModule k (Module.Dual k (V →ₗ[k] V))) ∈ B) ∧
      ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  have hntV : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hnt := nontrivial_dual_end k V (by omega)
  obtain ⟨f₀, hf₀, hf₀X⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k V hXc hXne
  obtain ⟨d, h, -, hhd, hhvan, hhne⟩ :=
    exists_mem_symmetricPower_forall_lift_eq_zero k V hXc f₀ hf₀ hf₀X
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, f₀ (Module.finBasis k V j₀) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf₀ ((Module.finBasis k V).ext fun j => by rw [hc j, LinearMap.zero_apply])
  refine ⟨adjugateSubstLocus k V j₀ h ∪ leadingMinorLocus k V,
    (isClosed_adjugateSubstLocus k V j₀ h).union (isClosed_leadingMinorLocus k V), ?_, ?_, ?_⟩
  · exact Set.union_subset (adjugateSubstLocus_subset_determinantHypersurface k V j₀ h)
      (leadingMinorLocus_subset_determinantHypersurface k V)
  · intro p g hg hpg hXg
    obtain ⟨f, hf, hfX, hfg⟩ : ∃ (f : Module.Dual k V) (hf : f ≠ 0),
        linearFunctionalPoint k V f hf ∈ X ∧ f ∘ₗ g = 0 := by
      by_contra hc
      exact hXg (subset_endDomain_of_forall_linearFunctionalPoint k V hXc g
        fun f hf hfX hfg => hc ⟨f, hf, hfX, hfg⟩)
    by_cases hrank : Module.finrank k ↥(LinearMap.range g) + 2 ≤ Module.finrank k V
    · exact Or.inr (coe_mem_leadingMinorLocus_of_finrank_range_add_two_le k V p g hg hpg hrank)
    · exact Or.inl (coe_mem_adjugateSubstLocus k V j₀ hhd p g hg hpg hf hfg
        (hhvan f hf hfX) hrank)
  · rintro x (hx | hx)
    · exact two_le_codimension_of_mem_of_isClosed_ssubset
        (isClosed_adjugateSubstLocus k V j₀ h) (isClosed_determinantHypersurface k V)
        (isIrreducible_determinantHypersurface k V h2)
        (adjugateSubstLocus_subset_determinantHypersurface k V j₀ h)
        (adjugateSubstLocus_ne_determinantHypersurface k V hhd h2 hf₀ hhne j₀ hj₀)
        (determinantHypersurface_ne_univ k V h2) hx
    · exact two_le_codimension_of_mem_leadingMinorLocus k V h2 x hx

/-- **Tag 0B1S with clause (1) of the bad locus discharged.** The hypotheses are the source's,
together with the clause-(2) half of the source's intermediate claim: a closed subset `B₂` of the
parameter space, of codimension at least two at each of its points, whose closed points are bad
and which contains every bad closed point at which clause (1) already holds. The clause-(1) half
is proved, not assumed: it is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_notMem_endDomain`.
The conclusion is that of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_codimension`:
along a general line through `[id_V]` every representative of every closed point is good for
`X, Y`. -/
public theorem exists_isOpen_closedPoint_line_isGood_of_clauseTwo [Nontrivial V]
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (_hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty)
    (B₂ : Set (projectiveSpaceOfModule k (ParameterModule k V))) (hB₂c : IsClosed B₂)
    (hB₂bad : ∀ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ B₂ →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V)))
    (hB₂sup : ∀ (p : ClosedPoints k (ParameterModule k V)) (g : V →ₗ[k] V),
      RepresentsParameterPoint k V p g →
      (X : Set (projectiveSpaceOfModule k V)) ⊆
        (endDomain k V g : Set (projectiveSpaceOfModule k V)) →
      ¬ IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
          (Y : Set (projectiveSpaceOfModule k V)) g →
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ B₂)
    (hB₂codim : ∀ x ∈ B₂, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        ∃ L : Submodule k (ParameterModule k V),
          Module.finrank k (ParameterModule k V ⧸ L) = 2 ∧
          identityParameterPoint k V ∈ linearSubspace k (ParameterModule k V) L ∧
          q ∈ linearSubspace k (ParameterModule k V) L ∧
          ∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              linearSubspace k (ParameterModule k V) L →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
              IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
                (Y : Set (projectiveSpaceOfModule k V)) g := by
  have h2 : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V X.isClosed' hXne X.isIrreducible'.nonempty
  have hnt := nontrivial_dual_end k V (by omega)
  have hV3 : 3 ≤ Module.finrank k (ParameterModule k V) := by
    have hfr : Module.finrank k (ParameterModule k V) =
        Module.finrank k V * Module.finrank k V := finrank_dual_end k V
    rw [hfr]
    calc (3 : ℕ) ≤ 2 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h2 h2
  obtain ⟨B₁, hB₁c, hB₁Z, hB₁sup, hB₁codim⟩ :=
    exists_isClosed_two_le_codimension_notMem_endDomain k V
      (X : Set (projectiveSpaceOfModule k V)) X.isClosed' hXne h2
  set pid : ClosedPoints k (ParameterModule k V) := (dualEndClosedPointsEquiv k V).symm
    (Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V)) with hpiddef
  have hpidc : (pid : projectiveSpaceOfModule k (ParameterModule k V)) =
      identityParameterPoint k V := rfl
  have hpid : dualEndClosedPointsEquiv k V pid =
      Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V) := by
    rw [hpiddef, Equiv.apply_symm_apply]
  have hid : identityParameterPoint k V ∉ B₁ ∪ B₂ := by
    rintro (h₁ | h₂)
    · refine (mem_determinantHypersurface_iff k V).mp (hB₁Z h₁) ?_
      refine (coe_mem_invertibleLocus_iff_det_ne_zero k V pid (LinearMap.id : V →ₗ[k] V)
        (linearMapId_ne_zero k V) hpid).mpr ?_
      simp
    · refine identityParameterPoint_notMem_badParameterLocus k V hXY ?_
      rw [← hpidc]
      exact hB₂bad pid (by rw [hpidc]; exact h₂)
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_subset_union_lines_disjoint_of_forall_codimension_ge_two k
      (ParameterModule k V) hV3 (B₁ ∪ B₂) (hB₁c.union hB₂c)
      (fun x hx => hx.elim (hB₁codim x) (hB₂codim x)) (identityParameterPoint k V)
      (isClosed_identityParameterPoint k V) hid
  refine ⟨U, hUopen, hUne, fun q hq hqc => ?_⟩
  obtain ⟨L, hL2, hidL, hqL, hdisj⟩ := hU q hq hqc
  refine ⟨L, hL2, hidL, hqL, fun p hpL g hg => ?_⟩
  by_contra hbad
  obtain ⟨hg0, hgeq⟩ := hg
  by_cases hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
      (endDomain k V g : Set (projectiveSpaceOfModule k V))
  · exact Set.disjoint_left.mp hdisj hpL (Or.inr (hB₂sup p g ⟨hg0, hgeq⟩ hdom hbad))
  · exact Set.disjoint_left.mp hdisj hpL (Or.inl (hB₁sup p g hg0 hgeq hdom))

end Locus

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
