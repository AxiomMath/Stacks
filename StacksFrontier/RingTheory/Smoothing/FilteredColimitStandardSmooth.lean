module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Smoothing.SyntomicCompleteIntersectionExtension

/-!
# Filtered colimits of smooth algebras are filtered colimits of standard smooth algebras

A *standard smooth* `R`-algebra is one admitting a presentation
`R[x_1, …, x_n]/(f_1, …, f_c)` whose `c × c` Jacobian minor `det(∂f_j/∂x_i)` is invertible;
every standard smooth algebra is smooth, but a smooth algebra need not be standard smooth. The
discrepancy disappears after passing to filtered colimits: if a ring map `R → Λ` exhibits `Λ` as
a filtered colimit of smooth `R`-algebras, then `Λ` is also a filtered colimit of standard
smooth `R`-algebras.

## Main results

* `Stacks.Smoothing.exists_smooth_retract_isStandardSmooth_of_smooth`: a smooth `R`-algebra
  admits a smooth extension with a retraction which is standard smooth over `R`.
* `Stacks.Smoothing.ind_isStandardSmooth_of_ind_smooth`: a filtered colimit of smooth
  `R`-algebras is a filtered colimit of standard smooth `R`-algebras.

## Implementation notes

Both classes of algebras are object properties on the category `Under (CommRingCat.of R)` of
`R`-algebras, via the ring-map predicates `RingHom.Smooth` and `RingHom.IsStandardSmooth`, and
"`Λ` is a filtered colimit of members of a class" is `CategoryTheory.ObjectProperty.ind`: a
colimit presentation of `Λ` by a filtered diagram of `R`-algebras. The reduction to a
factorization property of maps out of finitely presented algebras is
`CommRingCat.ind_under_iff_exists_factorization`.

The standard smooth retract is obtained without passing through étale neighbourhoods: enlarge
`A` to a relative global complete intersection `C = R[x_1, …, x_n]/(f_1, …, f_c)` retracting
onto `A`, split the conormal sequence of that presentation to obtain a left inverse `K` of its
Jacobian matrix, adjoin variables `y_1, …, y_c` together with the coordinates
`x_i - ∑_j K_{ji} y_j`, and invert the resulting Jacobian. The new Jacobian matrix has the block
shape `[[0, K], [J, 1]]` along the zero section, so the Schur complement formula exhibits its
determinant as a unit there.

The retraction is recorded as a ring homomorphism splitting the structure map `A → B`; it is
automatically a map of `R`-algebras, since `algebraMap R B` factors through `algebraMap A B`.

## References

* [Stacks Project, Tag 07CH](https://stacks.math.columbia.edu/tag/07CH)
* [Stacks Project, Tag 07CI](https://stacks.math.columbia.edu/tag/07CI)
-/

@[expose] public section

universe u v

namespace Stacks.Smoothing

section Retraction

open MvPolynomial

/-- For a presentation of a formally smooth algebra the Jacobian matrix of the relations has a
left inverse, obtained from a splitting of the conormal sequence of the presentation. -/
private theorem exists_jacobian_leftInverse
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq σ] [Algebra.FormallySmooth R S]
    (P : Algebra.Presentation R S ι σ)
    (b : Module.Basis σ S P.toExtension.Cotangent)
    (hb : ∀ j, b j = Algebra.Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩) :
    ∃ K : Matrix σ ι S,
      K * Matrix.of (fun i j ↦ aeval P.val (pderiv i (P.relation j))) = 1 := by
  obtain ⟨l, hl⟩ := ((P.toExtension.exact_cotangentComplex_toKaehler.split_tfae'.out
    1 2 rfl rfl).mp
      ⟨P.toExtension.subsingleton_h1Cotangent.mp
          (Algebra.Generators.H1Cotangent.equiv P.toGenerators
            (Algebra.Generators.self R S)).injective.subsingleton,
        Module.projective_lifting_property _ _ P.toExtension.toKaehler_surjective⟩).2
  refine ⟨Matrix.of fun j i ↦ b.repr (l (P.cotangentSpaceBasis i)) j, ?_⟩
  ext j k
  have heq := congrArg (fun x ↦ b.repr x j) (LinearMap.congr_fun hl (b k))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at heq
  rw [← P.cotangentSpaceBasis.sum_repr (P.toExtension.cotangentComplex (b k))] at heq
  have hrepr (i : ι) :
      P.cotangentSpaceBasis.repr (P.toExtension.cotangentComplex (b k)) i =
        aeval P.val (pderiv i (P.relation k)) := by
    rw [hb, Algebra.Extension.cotangentComplex_mk]
    exact P.cotangentSpaceBasis_repr_one_tmul _ _
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, hrepr, Module.Basis.repr_self, Finsupp.single_apply] at heq
  have hif : (if j = k then (1 : S) else 0) = if k = j then 1 else 0 :=
    if_congr eq_comm rfl rfl
  rw [Matrix.mul_apply, Matrix.one_apply, hif]
  simp only [Matrix.of_apply]
  exact (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _).trans heq

/-- Adjoining new generators `h k` together with the relations `h k - X k` to a presentation
again presents the same algebra. -/
private theorem span_relations_extend
    {R S ι σ κ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (h : κ → MvPolynomial ι R) :
    Ideal.span (Set.range (Sum.elim (fun j ↦ rename Sum.inl (P.relation j))
      (fun k ↦ rename Sum.inl (h k) - X (Sum.inr k)))) =
      (P.toGenerators.extend (fun k ↦ aeval P.val (h k))).ker := by
  let G := P.toGenerators.extend (fun k ↦ aeval P.val (h k))
  let I : Ideal (MvPolynomial (ι ⊕ κ) R) := Ideal.span (Set.range
    (Sum.elim (fun j ↦ rename Sum.inl (P.relation j))
      (fun k ↦ rename Sum.inl (h k) - X (Sum.inr k))))
  let f : MvPolynomial (ι ⊕ κ) R →ₐ[R] MvPolynomial ι R :=
    aeval (Sum.elim X h)
  have hf : (aeval P.val).comp f = aeval G.val := by
    ext i
    cases i <;> simp [f, G]
  have hker : P.ker ≤ I.comap (rename Sum.inl) := by
    rw [← P.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨Sum.inl j, rfl⟩
  have hquot : (Ideal.Quotient.mkₐ R I).comp ((rename Sum.inl).comp f) =
      Ideal.Quotient.mkₐ R I := by
    ext i
    cases i with
    | inl i => simp [f]
    | inr k =>
      simp only [AlgHom.comp_apply, f, aeval_X, Sum.elim_inr]
      exact Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨Sum.inr k, rfl⟩)
  apply le_antisymm
  · rw [Ideal.span_le, G.ker_eq_ker_aeval_val]
    rintro _ ⟨j | k, rfl⟩ <;> simp [G, aeval_rename, Function.comp_def]
  · intro p hp
    have hfp : f p ∈ P.ker := by
      rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker]
      change ((aeval P.val).comp f) p = 0
      rw [hf]
      exact hp
    have := Ideal.Quotient.eq_zero_iff_mem (I := I) |>.mpr (hker hfp)
    change (Ideal.Quotient.mkₐ R I).comp ((rename Sum.inl).comp f) p = 0 at this
    rw [hquot] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

/-- The presentation obtained from `P` by adjoining a new generator for each `h k` and the
relation expressing it. -/
private noncomputable def presentationExtend
    {R S ι σ κ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (h : κ → MvPolynomial ι R) :
    Algebra.Presentation R S (ι ⊕ κ) (σ ⊕ κ) where
  toGenerators := P.toGenerators.extend (fun k ↦ aeval P.val (h k))
  relation := Sum.elim (fun j ↦ rename Sum.inl (P.relation j))
    (fun k ↦ rename Sum.inl (h k) - X (Sum.inr k))
  span_range_relation_eq_ker := span_relations_extend P h

/-- A block matrix `[[0, K], [J, 1]]` has unit determinant as soon as `K * J = 1`. -/
private theorem isUnit_det_fromBlocks_of_mul_eq_one
    {S ι σ : Type*} [CommRing S] [Fintype ι] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ]
    (K : Matrix σ ι S) (J : Matrix ι σ S) (h : K * J = 1) :
    IsUnit (Matrix.fromBlocks 0 K J 1).det := by
  rw [Matrix.det_fromBlocks_one₂₂, h, zero_sub, Matrix.det_neg, Matrix.det_one, mul_one]
  exact (IsUnit.neg isUnit_one).pow _

/-- The presentation of a polynomial algebra `S[κ]` over `R` obtained by adjoining the variables
`κ` to a presentation of `S` over `R`. -/
private noncomputable def polynomialPresentation
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (κ : Type*) :
    Algebra.Presentation R (MvPolynomial κ S) (κ ⊕ ι) σ :=
  let Q : Algebra.Presentation S (MvPolynomial κ S) κ Empty :=
    { __ := Algebra.Generators.mvPolynomial S κ
      relation := Empty.elim
      span_range_relation_eq_ker := by simp [Algebra.Generators.ker_mvPolynomial] }
  { __ := Q.toGenerators.comp P.toGenerators
    relation := fun j ↦ rename Sum.inr (P.relation j)
    span_range_relation_eq_ker := by
      have hempty : Set.range (Q.compRelationAux P) = ∅ := by
        ext x
        simp
      simpa only [Algebra.Presentation.comp, Set.Sum.elim_range, hempty,
        Set.empty_union] using (Q.comp P).span_range_relation_eq_ker }

/-- A polynomial renamed along `Sum.inr` does not involve the variables indexed by `Sum.inl`. -/
private theorem pderiv_rename_inr_inl
    {R ι κ : Type*} [CommRing R] (p : MvPolynomial ι R) (k : κ) :
    pderiv (Sum.inl k) (rename Sum.inr p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The new coordinates `x_i - ∑_j K_{ji} y_j` used to turn a presentation with a left inverse
`K` of its Jacobian matrix into a submersive one. -/
private noncomputable def jacobianCoordinates
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype σ]
    (P : Algebra.Presentation R S ι σ) (K : Matrix σ ι S) (i : ι) :
    MvPolynomial (σ ⊕ ι) R :=
  X (Sum.inr i) + ∑ j, rename Sum.inr (P.σ (K j i)) * X (Sum.inl j)

/-- The presentation of `S[σ]` over `R` obtained from `P` by adjoining the variables `σ` and the
coordinates `jacobianCoordinates P K`, made pre-submersive by selecting the latter relations. -/
private noncomputable def jacobianPresentation
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype σ]
    (P : Algebra.Presentation R S ι σ) (K : Matrix σ ι S) :
    Algebra.PreSubmersivePresentation R (MvPolynomial σ S) ((σ ⊕ ι) ⊕ ι) (σ ⊕ ι) where
  __ := presentationExtend (polynomialPresentation P σ) (jacobianCoordinates P K)
  map := Sum.inl
  map_inj := Sum.inl_injective

/-- The partial derivative of a new coordinate in the direction of an adjoined variable. -/
private theorem jacobianCoordinates_pderiv_inl
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype σ]
    (P : Algebra.Presentation R S ι σ) (K : Matrix σ ι S) (j : σ) (i : ι) :
    pderiv (Sum.inl j) (jacobianCoordinates P K i) = rename Sum.inr (P.σ (K j i)) := by
  classical
  simp [jacobianCoordinates, pderiv_rename_inr_inl, Derivation.leibniz,
    Pi.single_apply, smul_eq_mul]

/-- The partial derivatives of the new coordinates in the directions of the original variables
form the identity matrix after setting the adjoined variables to zero. -/
private theorem jacobianCoordinates_pderiv_inr_eval
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype σ] [DecidableEq ι]
    (P : Algebra.Presentation R S ι σ) (K : Matrix σ ι S) (i k : ι) :
    aeval (Sum.elim (fun _ : σ ↦ (0 : S)) P.val)
      (pderiv (Sum.inr i) (jacobianCoordinates P K k)) = if i = k then 1 else 0 := by
  classical
  simp [jacobianCoordinates, Derivation.leibniz, Pi.single_apply, smul_eq_mul,
    eq_comm]

/-- The generators of `polynomialPresentation P κ` are the adjoined variables together with the
images of the generators of `P`. -/
private theorem polynomialPresentation_val
    {R S ι σ κ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (a : κ ⊕ ι) :
    (polynomialPresentation P κ).val a = Sum.elim X (fun i ↦ C (P.val i)) a := by
  cases a <;> rfl

/-- The relations of `polynomialPresentation P κ` are those of `P`, renamed. -/
private theorem polynomialPresentation_relation
    {R S ι σ κ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Presentation R S ι σ) (j : σ) :
    (polynomialPresentation P κ).relation j = rename Sum.inr (P.relation j) := rfl

/-- Setting the adjoined variables to zero, the Jacobian matrix of `jacobianPresentation P K`
has the block form `[[0, K], [J, 1]]`, where `J` is the Jacobian matrix of `P`. -/
private theorem jacobianPresentation_eval_jacobiMatrix
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]
    (P : Algebra.Presentation R S ι σ) (K : Matrix σ ι S) :
    ((aeval (R := S) (fun _ : σ ↦ (0 : S))).restrictScalars R).toRingHom.mapMatrix
      ((aeval (jacobianPresentation P K).val).toRingHom.mapMatrix
        (jacobianPresentation P K).jacobiMatrix) =
      Matrix.fromBlocks 0 K
        (Matrix.of (fun i j ↦ aeval P.val (pderiv i (P.relation j)))) 1 := by
  classical
  let e := (aeval (R := S) (fun _ : σ ↦ (0 : S))).restrictScalars R
  have he (a : σ ⊕ ι) :
      e ((polynomialPresentation P σ).val a) =
        Sum.elim (fun _ : σ ↦ (0 : S)) P.val a := by
    cases a <;> simp [e, polynomialPresentation_val]
  have hder (a : σ ⊕ ι) (p : MvPolynomial (σ ⊕ ι) R) :
      e (aeval (jacobianPresentation P K).val (pderiv (Sum.inl a) (rename Sum.inl p))) =
        aeval (Sum.elim (fun _ : σ ↦ (0 : S)) P.val) (pderiv a p) := by
    rw [pderiv_rename Sum.inl_injective, comp_aeval_apply, aeval_rename]
    congr 1
    exact congrArg MvPolynomial.aeval (funext he)
  have hcoord (a : σ ⊕ ι) (l : ι) :
      e (aeval (jacobianPresentation P K).val (pderiv (Sum.inl a)
        (rename Sum.inl (jacobianCoordinates P K l) - X (Sum.inr l)))) =
        aeval (Sum.elim (fun _ : σ ↦ (0 : S)) P.val) (pderiv a (jacobianCoordinates P K l)) := by
    simp only [map_sub, pderiv_X, Pi.single_apply, Sum.inr_ne_inl, ↓reduceIte, sub_zero, hder]
  ext (j | i) (k | l) <;>
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  · exact (hder _ (rename Sum.inr (P.relation k))).trans (by simp [pderiv_rename_inr_inl])
  · refine (hcoord (Sum.inl j) l).trans ?_
    rw [jacobianCoordinates_pderiv_inl, aeval_rename, Matrix.fromBlocks_apply₁₂]
    simpa only [Function.comp_def, Sum.elim_inr] using P.aeval_val_σ (K j l)
  · refine (hder _ (rename Sum.inr (P.relation k))).trans ?_
    rw [pderiv_rename Sum.inr_injective, aeval_rename]
    rfl
  · refine (hcoord (Sum.inr i) l).trans ?_
    rw [jacobianCoordinates_pderiv_inr_eval, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

/-- The Jacobian of `jacobianPresentation P K` becomes a unit after setting the adjoined
variables to zero. -/
private theorem jacobianPresentation_eval_jacobian_isUnit
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [Fintype σ] [DecidableEq σ]
    (P : Algebra.Presentation R S ι σ) (K : Matrix σ ι S)
    (hK : K * Matrix.of (fun i j ↦ aeval P.val (pderiv i (P.relation j))) = 1) :
    IsUnit ((aeval (R := S) (fun _ : σ ↦ (0 : S)))
      (jacobianPresentation P K).jacobian) := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.Generators.algebraMap_apply]
  have hunit := isUnit_det_fromBlocks_of_mul_eq_one K _ hK
  rw [← congrArg Matrix.det (jacobianPresentation_eval_jacobiMatrix P K)] at hunit
  simpa only [← RingHom.map_det] using! hunit

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- **A smooth algebra has a standard smooth retract.** For a smooth ring map `R → A` there is a
smooth `R`-algebra map `A → B` with a retraction such that `B` is standard smooth over `R`, that
is, `B ≅ R[x_1, …, x_n]/(f_1, …, f_c)` with `det(∂f_j/∂x_i)_{i, j = 1, …, c}` invertible in `B`. -/
@[stacks 07CH "`B` is produced as a type in the universe of `A`, carrying compatible `Algebra A B`
and `Algebra R B` instances with `IsScalarTower R A B`; \"`B` is standard smooth over `R`\" is
Mathlib's `Algebra.IsStandardSmooth`, whose submersive presentation is exactly the displayed
presentation with invertible `c × c` Jacobian minor. The retraction is a `RingHom`, which is
automatically an `R`-algebra map. See the module docstring."]
theorem exists_smooth_retract_isStandardSmooth_of_smooth :
    Algebra.Smooth R A →
      ∃ (B : Type v) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra R B),
        IsScalarTower R A B ∧ Algebra.Smooth A B ∧
          Algebra.IsStandardSmooth R B ∧
          ∃ (r : B →+* A),
            r.comp (algebraMap A B) = RingHom.id A := by
  classical
  intro _
  have : Algebra.Syntomic R A := Algebra.Smooth.syntomic R A
  obtain ⟨C, _, _, _, _, _, _, ρ, hρ, hGci⟩ :=
    exists_smooth_retract_isRelativeGlobalCompleteIntersection R A
  have : Algebra.Smooth R C := Algebra.Smooth.comp R A C
  obtain ⟨n, c, P, _⟩ := hGci.out
  obtain ⟨b, hb⟩ := P.exists_basis_cotangent_relation
  obtain ⟨K, hK⟩ := exists_jacobian_leftInverse P b hb
  let Q := jacobianPresentation P K
  let B := Localization.Away Q.jacobian
  let r : B →+* C :=
    IsLocalization.Away.lift Q.jacobian (jacobianPresentation_eval_jacobian_isUnit P K hK)
  have : Algebra.Smooth C (MvPolynomial (Fin c) C) := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth A (MvPolynomial (Fin c) C) :=
    Algebra.Smooth.comp A C (MvPolynomial (Fin c) C)
  have : Algebra.Smooth (MvPolynomial (Fin c) C) B :=
    Algebra.Smooth.of_isLocalization_Away Q.jacobian
  have hStandard : Algebra.IsStandardSmooth R B := by
    let Q' : Algebra.SubmersivePresentation R B _ _ :=
      { __ := (Algebra.PreSubmersivePresentation.localizationAway B Q.jacobian).comp Q
        jacobian_isUnit := by
          rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
            Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
          exact (IsLocalization.Away.algebraMap_isUnit _).mul
            (IsLocalization.Away.algebraMap_isUnit _) }
    exact Q'.isStandardSmooth
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.Smooth.comp A (MvPolynomial (Fin c) C) B,
    hStandard, ρ.comp r, ?_⟩
  ext a
  change ρ (r (algebraMap A B a)) = a
  rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin c) C) B,
    IsLocalization.Away.lift_eq,
    IsScalarTower.algebraMap_apply A C (MvPolynomial (Fin c) C)]
  simpa using DFunLike.congr_fun hρ a

end Retraction

section Colimit

open CategoryTheory

/-- **A filtered colimit of smooth algebras is a filtered colimit of standard smooth algebras.**
Let `R → Λ` be a ring map. If `Λ` is a filtered colimit of smooth `R`-algebras, then `Λ` is a
filtered colimit of standard smooth `R`-algebras. -/
@[stacks 07CI "\"`Λ` is a filtered colimit of smooth (resp. standard smooth) `R`-algebras\" is
`ObjectProperty.ind.{u}` of `RingHom.Smooth` (resp. `RingHom.IsStandardSmooth`) on the category
`Under (CommRingCat.of R)` of `R`-algebras, as in Lemma `07C3`. See the module docstring."]
theorem ind_isStandardSmooth_of_ind_smooth {R Λ : Type u} [CommRing R] [CommRing Λ]
    (f : R →+* Λ)
    (h : ObjectProperty.ind.{u}
      (fun B : Under (CommRingCat.of R) ↦ B.hom.hom.Smooth)
      (Under.mk (CommRingCat.ofHom f))) :
    ObjectProperty.ind.{u}
      (fun B : Under (CommRingCat.of R) ↦ B.hom.hom.IsStandardSmooth)
      (Under.mk (CommRingCat.ofHom f)) := by
  have hstd : (fun B : Under (CommRingCat.of R) ↦ B.hom.hom.IsStandardSmooth) ≤
      (fun B : Under (CommRingCat.of R) ↦ B.hom.hom.FinitePresentation) := by
    intro B hB
    let : Algebra R B.right := B.hom.hom.toAlgebra
    change Algebra.IsStandardSmooth R B.right at hB
    have : Algebra.IsStandardSmooth R B.right := hB
    exact RingHom.finitePresentation_algebraMap.mpr Algebra.IsStandardSmooth.finitePresentation
  refine (CommRingCat.ind_under_iff_exists_factorization
    (E := fun B : Under (CommRingCat.of R) ↦ B.hom.hom.IsStandardSmooth)
    (Λ := Under.mk (CommRingCat.ofHom f)) hstd).2 ?_
  intro A hA g
  obtain ⟨B, p, q, hpq, hB⟩ :=
    (CommRingCat.ind_under_iff_exists_factorization _
      (fun _ hB ↦ RingHom.Smooth.finitePresentation hB)).1 h A hA g
  let : Algebra R B.right := B.hom.hom.toAlgebra
  obtain ⟨C, _, _, _, htower, hBC, hC, r, hr⟩ :=
    exists_smooth_retract_isStandardSmooth_of_smooth R B.right hB
  let k : B.right →+* C := algebraMap B.right C
  have hr' (x : B.right) : r (k x) = x := by
    simpa [k] using congrArg (fun z : B.right →+* B.right ↦ z x) hr
  let P : A ⟶ Under.mk (CommRingCat.ofHom (k.comp B.hom.hom)) :=
    Under.homMk (CommRingCat.ofHom (k.comp p.right.hom)) (by
      ext x
      change k (p.right.hom (A.hom.hom x)) = k (B.hom.hom x)
      rw [← congrArg (fun z ↦ z.hom x) p.w]
      rfl)
  let Q : Under.mk (CommRingCat.ofHom (k.comp B.hom.hom)) ⟶
      Under.mk (CommRingCat.ofHom f) :=
    Under.homMk (CommRingCat.ofHom (q.right.hom.comp r)) (by
      ext x
      change q.right.hom (r (k (B.hom.hom x))) = f x
      rw [hr']
      exact congrArg (fun z ↦ z.hom x) q.w)
  refine ⟨Under.mk (CommRingCat.ofHom (k.comp B.hom.hom)), P, Q, ?_, ?_⟩
  · ext x
    change q.right.hom (r (k (p.right.hom x))) = g.right.hom x
    rw [hr']
    simpa using congrArg (fun z ↦ z.right.hom x) hpq
  · change ((algebraMap B.right C).comp (algebraMap R B.right)).IsStandardSmooth
    rw [← IsScalarTower.algebraMap_eq R B.right C]
    exact (RingHom.isStandardSmooth_algebraMap (R := R) (S := C)).2 hC

end Colimit

end Stacks.Smoothing
