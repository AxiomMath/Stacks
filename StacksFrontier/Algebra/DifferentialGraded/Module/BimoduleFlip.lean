module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleOfTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorAlgebraComparison

/-! # A right differential graded module as a bimodule over the graded opposite

Let `R` be a commutative ring and `(A, d)` a differential graded `R`-algebra. A right differential
graded `A`-module `M` is the same thing as a left differential graded `A^{opp}`-module: the
graded opposite algebra has the same underlying graded `R`-module as `A`, and the right action
`x a` becomes the left action `(-1)^{(deg a)(deg x)} a x`. Since every differential graded module
is in particular a right differential graded module over the base ring placed in degree zero,
`M` becomes a differential graded `(A^{opp}, R)`-bimodule in the sense of Tag 0FQJ.

## Main definitions

* `DifferentialGradedAlgebra.baseHom`: the base ring in degree zero maps to any differential
  graded algebra, `r ↦ r · 1`.
* `DifferentialGradedModule.oppLeftActionRingHom`: the left action of `A^{opp}` on a right
  differential graded `A`-module, as a ring homomorphism into its `R`-linear endomorphisms.
* `DifferentialGradedModule.oppLeftAction`: that action as a left differential graded action of
  `A^{opp}` on the complex underlying `M`.
* `DifferentialGraded.Bimodule.flip`: `M` as a differential graded `(A^{opp}, R)`-bimodule.
* `DifferentialGraded.Bimodule.flipMap` and `DifferentialGraded.Bimodule.flipFunctor`: its
  functoriality in `M`.

## Main results

* `DifferentialGradedModule.oppLeftActionRingHom_apply_mem`: the left action of a homogeneous
  element of `A^{opp}` on a homogeneous element of `M` is the right action with the Koszul sign
  `(-1)^{(deg a)(deg x)}`; this formula determines everything below.
* `DifferentialGraded.Bimodule.flip_leftAction_apply`: the same formula, read as the left action
  of the bimodule.

## Implementation notes

*Why the sign is forced.* The multiplication of `A^{opp}` is `a ·ᵒᵖᵖ b = (-1)^{(deg a)(deg b)} b a`
(Tag 09JG, `DifferentialGradedAlgebra.Opposite.map_mul_of_mem`), so the only `R`-bilinear rule
`a · x = ε(deg a, deg x) · x a` that is associative and satisfies the graded Leibniz rule is
`ε(m, p) = (-1)^{m p}`: associativity forces `ε(m, p + k) ε(k, p) = (-1)^{m k} ε(m + k, p)` and the
Leibniz rule forces `ε(m + 1, p) = (-1)^p ε(m, p)` and `ε(m, p) = (-1)^m ε(m, p + 1)`.

*How the sign is produced.* A sign depending on two degrees is not an endomorphism of either
factor, so it is not written out by hand: it is assembled from the quadratic sign twist
`DifferentialGraded.gradedSignTwist`, which is a single `R`-linear involution of a graded module,
through `(-1)^{m p} = q(m) q(p) q(m + p)` (`DifferentialGraded.koszulQuadraticSign_mul_add`). The
ring homomorphism below is therefore the right action transported along
`DifferentialGraded.gradedOppositeRingEquiv` and conjugated by that twist, as in
`DifferentialGraded.rightToLeftAction`, which performs the same translation in the opposite
direction (Tag 0FQ0, from left modules over `A` to right modules over `A^{opp}`).

*The left action as cochains.* A `DifferentialGradedModule.BimoduleStructure` is a
`DifferentialGradedAlgebra.LeftAction` on the underlying complex together with the right linearity
of each of its components. Each component here is a homogeneous right `R`-linear map, so the three
laws are `DifferentialGradedModule.homogeneousMapToCochain_id`,
`DifferentialGradedModule.homogeneousMapToCochain_comp` and
`DifferentialGradedModule.homogeneousMapToCochain_d`.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ) for differential graded
  bimodules, [Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI) for the criterion that a left
  action is a bimodule structure, [Tag 09JG](https://stacks.math.columbia.edu/tag/09JG) for the
  graded opposite algebra and [Tag 0FQ0](https://stacks.math.columbia.edu/tag/0FQ0) for the
  identification of left modules with right modules over the opposite.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **The base ring in degree zero maps to every differential graded algebra**, by `r ↦ r · 1`:
the image lies in degree zero because the unit does, and it is killed by the differential because
the unit is. -/
def baseHom (A : DifferentialGradedAlgebra.{u, u} R) : (degreeZero R R).Hom A where
  toAlgebraHom := Algebra.ofId R A.A
  map_grading n a ha := by
    by_cases hn : n = 0
    · subst n
      show algebraMap R A.A a ∈ A.grading 0
      rw [Algebra.algebraMap_eq_smul_one]
      exact (A.grading 0).smul_mem _ (SetLike.one_mem_graded A.grading)
    · have ha0 : a = 0 := by simpa [degreeZero, degreeZeroGrading, hn] using ha
      subst a
      simp
  map_d a := by
    rw [show (degreeZero R R).d a = 0 from rfl, map_zero]
    show (0 : A.A) = A.d (algebraMap R A.A a)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, DifferentialGradedAlgebra.d_one, smul_zero]

/-- The map `DifferentialGradedAlgebra.baseHom A` sends `r` to `algebraMap R A.A r`. -/
@[simp] theorem baseHom_toAlgebraHom_apply (A : DifferentialGradedAlgebra.{u, u} R) (r : R) :
    (baseHom A).toAlgebraHom r = algebraMap R A.A r := rfl

/-- The underlying algebra homomorphism of `DifferentialGradedAlgebra.baseHom A` is
`Algebra.ofId R A.A`. -/
@[simp] theorem baseHom_toAlgebraHom (A : DifferentialGradedAlgebra.{u, u} R) :
    (baseHom A).toAlgebraHom = Algebra.ofId R A.A := rfl

end DifferentialGradedAlgebra

namespace DifferentialGraded

variable {R : Type u} [CommRing R]

/-! ### The Koszul sign of two degrees through the quadratic sign twist -/

/-- **The Koszul sign of two degrees is a product of three quadratic signs**:
`q(m) q(p) q(m + p) = (-1)^{m p}`. -/
theorem koszulQuadraticSign_triple (m p : ℤ) :
    koszulQuadraticSign m * koszulQuadraticSign p * koszulQuadraticSign (m + p) =
      (m * p).negOnePow := by
  rw [← koszulQuadraticSign_mul_add, mul_right_comm, Int.units_mul_self, one_mul]

/-- The identity `q(m) q(p) q(m + p) = (-1)^{m p}` of
`DifferentialGraded.koszulQuadraticSign_triple`, cast to the ring `R`. -/
theorem koszulQuadraticSign_triple_cast (m p : ℤ) :
    ((koszulQuadraticSign m : ℤ) : R) * ((koszulQuadraticSign p : ℤ) : R) *
      ((koszulQuadraticSign (m + p) : ℤ) : R) = (((m * p).negOnePow : ℤ) : R) := by
  simpa only [Units.val_mul, Int.cast_mul] using
    congrArg (fun v : ℤˣ => ((v : ℤ) : R)) (koszulQuadraticSign_triple m p)

/-- **A bilinear map that adds degrees, conjugated by the quadratic sign twists, is the Koszul
sign.** If `t` sends degrees `p` and `q` to degree `p + q`, then twisting both arguments and the
value of `t x y` multiplies it by `(-1)^{p q}`. -/
theorem gradedSignTwist_bilinear {X Y Z : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (gX : ℤ → Submodule R X) [DirectSum.Decomposition gX]
    (gY : ℤ → Submodule R Y) [DirectSum.Decomposition gY]
    (gZ : ℤ → Submodule R Z) [DirectSum.Decomposition gZ]
    (t : X →ₗ[R] Y →ₗ[R] Z) {p q : ℤ} {x : X} {y : Y} (hx : x ∈ gX p) (hy : y ∈ gY q)
    (ht : t x y ∈ gZ (p + q)) :
    gradedSignTwist R Z gZ (t (gradedSignTwist R X gX x) (gradedSignTwist R Y gY y)) =
      (((p * q).negOnePow : ℤ) : R) • t x y := by
  have h1 : t (gradedSignTwist R X gX x) (gradedSignTwist R Y gY y) =
      (((koszulQuadraticSign p : ℤ) : R) * ((koszulQuadraticSign q : ℤ) : R)) • t x y := by
    rw [gradedSignTwist_apply_mem R X gX hx, gradedSignTwist_apply_mem R Y gY hy,
      map_smul t (((koszulQuadraticSign p : ℤ) : R)) x, LinearMap.smul_apply,
      map_smul (t x) (((koszulQuadraticSign q : ℤ) : R)) y, smul_smul]
  rw [h1, map_smul, gradedSignTwist_apply_mem R Z gZ ht, smul_smul,
    koszulQuadraticSign_triple_cast p q]

end DifferentialGraded

namespace DifferentialGradedModule

open DifferentialGraded DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### The right differential graded module over the base ring in degree zero -/

/-- **The right action of a scalar multiple of the unit is the action of the scalar**: if
`c = r • 1`, then `x c = r • x`. -/
theorem op_smul_eq_smul_of_smul_one {C : DifferentialGradedAlgebra.{u, u} R}
    (N : DifferentialGradedModule.{u, u, u} C) {c : C.A} {r : R} (h : c = r • (1 : C.A))
    (x : N.M) : MulOpposite.op c • x = r • x := by
  subst h
  rw [MulOpposite.op_smul, MulOpposite.op_one, IsScalarTower.smul_assoc, one_smul]

/-- A right differential graded `A`-module, read over the base ring placed in degree zero. Its
underlying module, grading and differential are those of `M`. -/
abbrev toBaseModule (M : DifferentialGradedModule.{u, u, u} A) :
    DifferentialGradedModule.{u, u, u} (degreeZero R R) :=
  restrictScalars (baseHom A) M

/-! ### The left action of the graded opposite algebra -/

/-- **The left action of `A^{opp}` on a right differential graded `A`-module.** It is the right
action of `A` transported along the identification
`DifferentialGraded.gradedOppositeRingEquiv` of the underlying ring of `A^{opp}` with the opposite
ring of `A`, conjugated by the quadratic sign twist of the grading; on homogeneous elements this
is the right action with the Koszul sign, which is
`DifferentialGradedModule.oppLeftActionRingHom_apply_mem`. -/
def oppLeftActionRingHom (M : DifferentialGradedModule.{u, u, u} A) :
    (Bimodule.oppAlgebra A).A →+* Module.End R M.M :=
  conjugatedModuleAction (gradedOppositeRingEquiv R A)
    (gradedSignTwistEquiv R M.M M.grading)
    (moduleActionRingHom (MulOpposite A.A) M.M)

/-- The left action of `a : A^{opp}` on `x` is the sign twist of the right action of
`DifferentialGraded.gradedOppositeRingEquiv R A a` on the sign twist of `x`. -/
theorem oppLeftActionRingHom_apply (M : DifferentialGradedModule.{u, u, u} A)
    (a : (Bimodule.oppAlgebra A).A) (x : M.M) :
    oppLeftActionRingHom M a x =
      gradedSignTwist R M.M M.grading
        (gradedOppositeRingEquiv R A a • gradedSignTwist R M.M M.grading x) := rfl

/-- `DifferentialGraded.gradedOppositeRingEquiv R A` is the sign twist followed by the
identification of the underlying module of `A^{opp}` with that of `A`. -/
private theorem gradedOppositeRingEquiv_apply (a : (Bimodule.oppAlgebra A).A) :
    gradedOppositeRingEquiv R A a = MulOpposite.op ((opposite R A).equiv
      (gradedSignTwist R (Bimodule.oppAlgebra A).A (Bimodule.oppAlgebra A).grading a)) := rfl

/-- The ring isomorphism `DifferentialGraded.gradedOppositeRingEquiv R A` is `R`-linear. -/
theorem gradedOppositeRingEquiv_smul (r : R) (a : (Bimodule.oppAlgebra A).A) :
    gradedOppositeRingEquiv R A (r • a) = r • gradedOppositeRingEquiv R A a := by
  simp only [gradedOppositeRingEquiv_apply, map_smul, MulOpposite.op_smul]

/-- The left action is `R`-linear in the acting element. -/
theorem oppLeftActionRingHom_smul (M : DifferentialGradedModule.{u, u, u} A) (r : R)
    (a : (Bimodule.oppAlgebra A).A) (x : M.M) :
    oppLeftActionRingHom M (r • a) x = r • oppLeftActionRingHom M a x := by
  rw [oppLeftActionRingHom_apply, oppLeftActionRingHom_apply, gradedOppositeRingEquiv_smul,
    IsScalarTower.smul_assoc, map_smul]

/-- The left action of `A^{opp}`, as an `R`-linear map into the `R`-linear endomorphisms. -/
def oppLeftActionLinear (M : DifferentialGradedModule.{u, u, u} A) :
    (Bimodule.oppAlgebra A).A →ₗ[R] Module.End R M.M where
  toFun a := oppLeftActionRingHom M a
  map_add' a b := map_add (oppLeftActionRingHom M) a b
  map_smul' r a := LinearMap.ext fun x => oppLeftActionRingHom_smul M r a x

/-- The `R`-linear map `DifferentialGradedModule.oppLeftActionLinear M` sends `a` to
`DifferentialGradedModule.oppLeftActionRingHom M a`. -/
@[simp] theorem oppLeftActionLinear_apply (M : DifferentialGradedModule.{u, u, u} A)
    (a : (Bimodule.oppAlgebra A).A) :
    oppLeftActionLinear M a = oppLeftActionRingHom M a := rfl

/-- **The left action of `A^{opp}` on homogeneous elements.** A homogeneous `a : (A^{opp})^m`
acts on a homogeneous `x : M^p` by the right action of `a`, read in `A`, with the Koszul sign
`(-1)^{m p}`. -/
theorem oppLeftActionRingHom_apply_mem (M : DifferentialGradedModule.{u, u, u} A) {m p : ℤ}
    {a : (Bimodule.oppAlgebra A).A} (ha : a ∈ (Bimodule.oppAlgebra A).grading m)
    {x : M.M} (hx : x ∈ M.grading p) :
    oppLeftActionRingHom M a x =
      (((m * p).negOnePow : ℤ) : R) •
        (MulOpposite.op ((opposite R A).equiv a) • x) := by
  set s : MulOpposite A.A := MulOpposite.op ((opposite R A).equiv a) with hs
  have haA : (opposite R A).equiv a ∈ A.grading m :=
    ((opposite R A).mem_grading_iff m a).1 ha
  have hmem : s • x ∈ M.grading (p + m) := M.smul_mem p m x _ hx haA
  have he : gradedOppositeRingEquiv R A a = ((koszulQuadraticSign m : ℤ) : R) • s := by
    rw [gradedOppositeRingEquiv_apply, gradedSignTwist_apply_mem R _ _ ha, map_smul,
      MulOpposite.op_smul]
  have hq : ((koszulQuadraticSign m : ℤ) : R) * ((koszulQuadraticSign p : ℤ) : R) *
      ((koszulQuadraticSign (p + m) : ℤ) : R) = (((m * p).negOnePow : ℤ) : R) := by
    rw [add_comm p m]
    exact koszulQuadraticSign_triple_cast m p
  rw [oppLeftActionRingHom_apply, gradedSignTwist_apply_mem R M.M M.grading hx, he,
    IsScalarTower.smul_assoc, ← smul_comm ((koszulQuadraticSign p : ℤ) : R) s x,
    map_smul, map_smul, gradedSignTwist_apply_mem R M.M M.grading hmem,
    smul_smul, smul_smul, hq]

/-! ### The graded Leibniz rule -/

/-- **The graded Leibniz rule for the left action of `A^{opp}`.** For a homogeneous
`a : (A^{opp})^n` the left action of `d a` is the graded commutator of the left action of `a` with
the differential of `M`. -/
theorem oppLeftActionRingHom_leibniz (M : DifferentialGradedModule.{u, u, u} A) {n p : ℤ}
    {a : (Bimodule.oppAlgebra A).A} (ha : a ∈ (Bimodule.oppAlgebra A).grading n)
    {x : M.M} (hx : x ∈ M.grading p) :
    oppLeftActionRingHom M ((Bimodule.oppAlgebra A).d a) x =
      M.d (oppLeftActionRingHom M a x) -
        ((n.negOnePow : ℤ) : R) • oppLeftActionRingHom M a (M.d x) := by
  have hda : (Bimodule.oppAlgebra A).d a ∈ (Bimodule.oppAlgebra A).grading (n + 1) :=
    (Bimodule.oppAlgebra A).d_mem n a ha
  have hdx : M.d x ∈ M.grading (p + 1) := M.d_mem p x hx
  have h2 : ((n.negOnePow : ℤˣ) * (n * (p + 1)).negOnePow) = (n * p).negOnePow := by
    rw [← Int.negOnePow_add, show n + n * (p + 1) = 2 * n + n * p by ring, Int.negOnePow_add,
      Int.negOnePow_two_mul, one_mul]
  have h1' : ((((n + 1) * p).negOnePow : ℤ) : R) =
      (((n * p).negOnePow : ℤ) : R) * ((p.negOnePow : ℤ) : R) := by
    rw [show (n + 1) * p = n * p + p by ring, Int.negOnePow_add, Units.val_mul, Int.cast_mul]
  have h2' : ((n.negOnePow : ℤ) : R) * (((n * (p + 1)).negOnePow : ℤ) : R) =
      (((n * p).negOnePow : ℤ) : R) := by
    rw [← Int.cast_mul, ← Units.val_mul, h2]
  rw [oppLeftActionRingHom_apply_mem M hda hx, oppLeftActionRingHom_apply_mem M ha hx,
    oppLeftActionRingHom_apply_mem M ha hdx, (opposite R A).map_d a, map_smul,
    leibniz_apply M p x hx ((opposite R A).equiv a),
    ← Int.cast_smul_eq_zsmul R (p.negOnePow : ℤ), smul_add, smul_smul, smul_smul, h1', h2']
  abel

/-! ### The left action as a bimodule structure -/

/-- The left action of a homogeneous element of `A^{opp}` is a homogeneous right `R`-linear
endomorphism of `M`: it shifts the degree by the degree of the element and it is `R`-linear. -/
theorem oppLeftAction_mem_homogeneousMap (M : DifferentialGradedModule.{u, u, u} A)
    {n : ℤ} (a : (Bimodule.oppAlgebra A).grading n) :
    (oppLeftActionLinear M (a : (Bimodule.oppAlgebra A).A) :
        (toBaseModule M).M →ₗ[R] (toBaseModule M).M) ∈
      homogeneousMapSubmodule (degreeZero R R) (toBaseModule M) (toBaseModule M) n := by
  refine ⟨fun i y hy => ?_, fun c y => ?_⟩
  · show oppLeftActionRingHom M (a : (Bimodule.oppAlgebra A).A) y ∈ M.grading (i + n)
    rw [oppLeftActionRingHom_apply_mem M a.property hy]
    exact Submodule.smul_mem _ _
      (M.smul_mem i n y _ hy (((opposite R A).mem_grading_iff n _).1 a.property))
  · have hc : c = c • (1 : (degreeZero R R).A) := by simp
    rw [op_smul_eq_smul_of_smul_one (toBaseModule M) hc y,
      op_smul_eq_smul_of_smul_one (toBaseModule M) hc
        (oppLeftActionLinear M (a : (Bimodule.oppAlgebra A).A) y)]
    exact (oppLeftActionRingHom M (a : (Bimodule.oppAlgebra A).A)).map_smul c y

/-- The left action of the degree-`n` part of `A^{opp}`, as homogeneous right `R`-linear
endomorphisms of `M`. -/
def oppActionHom (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    (Bimodule.oppAlgebra A).grading n →ₗ[R]
      HomogeneousMap (degreeZero R R) (toBaseModule M) (toBaseModule M) n :=
  LinearMap.codRestrict _
    ((oppLeftActionLinear M).comp ((Bimodule.oppAlgebra A).grading n).subtype)
    fun a => oppLeftAction_mem_homogeneousMap M a

/-- The homogeneous endomorphism `DifferentialGradedModule.oppActionHom M n a` sends `x` to the
left action of `a` on `x`. -/
theorem oppActionHom_val (M : DifferentialGradedModule.{u, u, u} A) {n : ℤ}
    (a : (Bimodule.oppAlgebra A).grading n) (x : M.M) :
    (oppActionHom M n a).1 x = oppLeftActionRingHom M (a : (Bimodule.oppAlgebra A).A) x := rfl

/-- The left action of `d a` is the Hom differential of the left action of `a` in the
differential graded category of right differential graded `R`-modules. -/
theorem oppActionHom_differential (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ)
    (a : (Bimodule.oppAlgebra A).grading n) :
    oppActionHom M (n + 1)
        ⟨(Bimodule.oppAlgebra A).d (a : (Bimodule.oppAlgebra A).A),
          (Bimodule.oppAlgebra A).d_mem n a a.property⟩ =
      homogeneousMapDifferential (degreeZero R R) (oppActionHom M n a) := by
  apply Subtype.ext
  refine LinearMap.ext fun x => ?_
  show oppLeftActionRingHom M ((Bimodule.oppAlgebra A).d (a : (Bimodule.oppAlgebra A).A)) x =
    M.d (oppLeftActionRingHom M (a : (Bimodule.oppAlgebra A).A) x) -
      DifferentialGraded.gradedSign R n •
        oppLeftActionRingHom M (a : (Bimodule.oppAlgebra A).A) (M.d x)
  rw [show DifferentialGraded.gradedSign R n = ((n.negOnePow : ℤ) : R) by
    simp [DifferentialGraded.gradedSign]]
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add y z hy hz =>
    rw [map_add, map_add, map_add, map_add, map_add, smul_add, hy, hz]
    abel
  | @homogeneous p y => exact oppLeftActionRingHom_leibniz M a.property y.property

/-- **The left differential graded action of `A^{opp}` on the complex underlying `M`.** The three
laws are those of `DifferentialGradedModule.homogeneousMapToCochain`: the unit acts by the
identity, a product acts by the composite and the differential acts by the graded commutator. -/
def oppLeftAction (M : DifferentialGradedModule.{u, u, u} A) :
    (Bimodule.oppAlgebra A).LeftAction (toBaseModule M).toCochainComplex where
  action n :=
    (homogeneousMapToCochainₗ (degreeZero R R) (toBaseModule M) (toBaseModule M) n).comp
      (oppActionHom M n)
  map_one := by
    simp only [LinearMap.comp_apply, homogeneousMapToCochainₗ_apply]
    rw [show oppActionHom M 0 ⟨1, SetLike.one_mem_graded (Bimodule.oppAlgebra A).grading⟩ =
        homogeneousMapId (degreeZero R R) (toBaseModule M) from
      Subtype.ext (show oppLeftActionRingHom M 1 = LinearMap.id by
        rw [map_one]; rfl)]
    exact homogeneousMapToCochain_id (degreeZero R R) (toBaseModule M)
  map_mul n m a b := by
    simp only [LinearMap.comp_apply, homogeneousMapToCochainₗ_apply]
    rw [show oppActionHom M (n + m)
          ⟨(a : (Bimodule.oppAlgebra A).A) * (b : (Bimodule.oppAlgebra A).A),
            SetLike.mul_mem_graded a.property b.property⟩ =
        homogeneousMapComp (degreeZero R R) (show n + m = n + m from rfl)
          (oppActionHom M n a) (oppActionHom M m b) from
      Subtype.ext (show oppLeftActionRingHom M
            ((a : (Bimodule.oppAlgebra A).A) * (b : (Bimodule.oppAlgebra A).A)) =
          (oppLeftActionRingHom M (a : (Bimodule.oppAlgebra A).A)).comp
            (oppLeftActionRingHom M (b : (Bimodule.oppAlgebra A).A)) by
        rw [map_mul]; rfl)]
    exact homogeneousMapToCochain_comp (degreeZero R R) (show n + m = n + m from rfl)
      (oppActionHom M n a) (oppActionHom M m b)
  map_d n a := by
    simp only [LinearMap.comp_apply, homogeneousMapToCochainₗ_apply]
    rw [oppActionHom_differential]
    exact homogeneousMapToCochain_d (degreeZero R R) (oppActionHom M n a)

/-- For a homogeneous `a : (A^{opp})^n`, the component from degree `p` to degree `q = p + n` of
the cochain by which `a` acts sends `x` to the left action of `a` on `x`. -/
theorem oppLeftAction_action_v (M : DifferentialGradedModule.{u, u, u} A) {n p q : ℤ}
    (hpq : p + n = q) (a : (Bimodule.oppAlgebra A).grading n)
    (x : (toBaseModule M).grading p) :
    ((show (toBaseModule M).grading q from ((oppLeftAction M).action n a).v p q hpq x) :
        (toBaseModule M).M) =
      oppLeftActionRingHom M (a : (Bimodule.oppAlgebra A).A) ((x : (toBaseModule M).M) : M.M) :=
  homogeneousMapToCochain_v (degreeZero R R) (oppActionHom M n a) p q hpq x

/-- **`M` as a differential graded `(A^{opp}, R)`-bimodule structure**: every homogeneous element
of `A^{opp}` acts by a homogeneous right `R`-linear endomorphism, which by Tag 0FQI is what makes
the left action a bimodule structure. -/
def oppBimoduleStructure (M : DifferentialGradedModule.{u, u, u} A) :
    BimoduleStructure (Bimodule.oppAlgebra A) (degreeZero R R) (toBaseModule M) :=
  ⟨oppLeftAction M, fun n a => isRightLinearCochain_homogeneousMapToCochain (degreeZero R R)
    (toBaseModule M) (oppActionHom M n a)⟩

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- **A right differential graded `A`-module as a differential graded `(A^{opp}, R)`-bimodule.**
The underlying right differential graded module over the base ring in degree zero is `M` itself,
and `A^{opp}` acts on the left by the right action of `A` with the Koszul sign.

`@[implicit_reducible]` so that `(flip M).rightModule.M` unfolds to `M.M` for unification: the two
are definitionally equal, but the structure fields of
`DifferentialGraded.Bimodule.BalancedBilinearMap` are stated at the first spelling while the right
action of `A` is only available at the second, and `rw` type-checks its results at `implicit`
transparency. -/
@[implicit_reducible]
def flip (M : DifferentialGradedModule.{u, u, u} A) :
    Bimodule (oppAlgebra A) (degreeZero R R) where
  rightModule := toBaseModule M
  leftAction := oppBimoduleStructure M

/-- **The left action of the flipped bimodule** is the left action of `A^{opp}` on `M`; on
homogeneous elements it is the right action of `A` with the Koszul sign, by
`DifferentialGradedModule.oppLeftActionRingHom_apply_mem`. -/
theorem flip_leftAction (M : DifferentialGradedModule.{u, u, u} A) {n p : ℤ}
    (a : (oppAlgebra A).grading n) (x : (flip M).rightModule.grading p) :
    ((show (flip M).rightModule.grading (p + n) from
          ((flip M).leftAction.1.action n a).v p (p + n) (by omega) x) :
        (flip M).rightModule.M) =
      oppLeftActionRingHom M (a : (oppAlgebra A).A) (x : (flip M).rightModule.M) :=
  oppLeftAction_action_v M (show p + n = p + n from rfl) a x

/-- **The flip is functorial.** A homomorphism of right differential graded `A`-modules is a
homomorphism of the flipped bimodules: it is `R`-linear and commutes with the right action of
`A`, hence with the signed left action of `A^{opp}`. -/
def flipMap {M M' : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ M') : flip M ⟶ flip M' where
  rightHom := restrictScalarsHom (baseHom A) f
  map_left n p a x := by
    show f.toFun (oppLeftActionRingHom M (a : (oppAlgebra A).A)
        (x : (flip M).rightModule.M)) =
      oppLeftActionRingHom M' (a : (oppAlgebra A).A) (f.toFun (x : (flip M).rightModule.M))
    rw [oppLeftActionRingHom_apply_mem M a.property x.property,
      oppLeftActionRingHom_apply_mem M' a.property
        (f.map_grading p ((x : (flip M).rightModule.M) : M.M) x.property),
      map_smul]
    exact congrArg (fun z : M'.M => (((n * p).negOnePow : ℤ) : R) • z)
      (f.map_smul ((x : (flip M).rightModule.M) : M.M)
        ((opposite R A).equiv (a : (oppAlgebra A).A)))

/-- The underlying function of `DifferentialGraded.Bimodule.flipMap f` is that of `f`. -/
@[simp] theorem flipMap_rightHom_toFun {M M' : DifferentialGradedModule.{u, u, u} A}
    (f : M ⟶ M') : (flipMap f).rightHom.toFun = f.toFun := rfl

/-- The flip, as a functor from right differential graded `A`-modules to differential graded
`(A^{opp}, R)`-bimodules. -/
def flipFunctor (A : DifferentialGradedAlgebra.{u, u} R) :
    DifferentialGradedModule.{u, u, u} A ⥤ Bimodule (oppAlgebra A) (degreeZero R R) where
  obj := flip
  map := flipMap
  map_id M := by
    refine Bimodule.Hom.ext ?_
    exact DifferentialGradedModule.Hom.ext rfl
  map_comp f g := by
    refine Bimodule.Hom.ext ?_
    exact DifferentialGradedModule.Hom.ext rfl

/-- The functor `DifferentialGraded.Bimodule.flipFunctor A` sends `M` to
`DifferentialGraded.Bimodule.flip M`. -/
@[simp] theorem flipFunctor_obj (M : DifferentialGradedModule.{u, u, u} A) :
    (flipFunctor A).obj M = flip M := rfl

/-- The functor `DifferentialGraded.Bimodule.flipFunctor A` sends `f` to
`DifferentialGraded.Bimodule.flipMap f`. -/
@[simp] theorem flipFunctor_map {M M' : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ M') :
    (flipFunctor A).map f = flipMap f := rfl

end DifferentialGraded.Bimodule

end
