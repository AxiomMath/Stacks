module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExact
public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCochainComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.RingTheory.Koszul.PowAlgebraKFlat
public import StacksFrontier.RingTheory.Koszul.Relations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weakly proregular sequences

Let `f₁, …, f_r` be a sequence of elements of a commutative ring `R` generating an ideal `I`,
and let `K_n` be the Koszul complex on `f₁ ^ n, …, f_r ^ n` viewed as a differential graded
`R`-algebra (`Koszul.powAlgebra`). Following Stacks 0H1E the sequence is a *weakly proregular
sequence* when for every `n` there is an `m > n` such that the transition homomorphism
`K_m → K_n` induces the zero map on cohomology in every degree other than `0`.

For such a sequence the Koszul augmentations `K_n → R / (f₁ ^ n, …, f_r ^ n)` exhibit the
inverse system of Koszul algebras as isomorphic, as a pro-object of the derived category
`D(R)`, to the inverse system of quotients. This is the comparison of the Koszul tower with
the quotient tower that the proof of Proposition 0GZK obtains from the Noetherian hypothesis
on `R`, and it is the sense in which weak proregularity takes the place of that hypothesis.

The ingredients are: the cohomology of `K_n` lives in the degrees `-r, …, 0`, because the
`k`-th exterior power of `Rʳ` vanishes for `k > r`; the augmentation is an isomorphism on
`H⁰`, because `H⁰(K_n)` is the cokernel of the degree-zero Koszul differential, whose image is
the ideal `(f₁ ^ n, …, f_r ^ n)`; and in the remaining degrees the quotient tower has no
cohomology while weak proregularity makes the cohomology of the Koszul tower pro-vanish.
Stacks 0G3D, which detects a pro-isomorphism in a derived category on cohomology, assembles
these.

## Main definitions

* `Koszul.powCochainSystem`: the Koszul algebras of the powers of `f`, as an inverse system of
  cochain complexes of `R`-modules.
* `Koszul.IsWeaklyProregular`: the condition above.
* `Koszul.powQuotientSystem`: the inverse system of the quotients `R / (f₁ ^ n, …, f_r ^ n)`.
* `Koszul.powAugmentation`, `Koszul.powAugmentationSystem`: the Koszul augmentation and its
  compatibility with the transition homomorphisms.
* `Koszul.powDerivedSystem`, `Koszul.powQuotientDerivedSystem` and
  `Koszul.powAugmentationDerived`: the two systems and the augmentations, read in `D(R)`.

## Main results

* `Koszul.quasiIsoAt_powAugmentation`: the Koszul augmentation is an isomorphism on `H⁰`.
* `Koszul.isZero_homology_powCochain`: the cohomology of `K_n` vanishes outside the degrees
  `-r, …, 0`.
* `Koszul.exists_proInverse_powAugmentationDerived`: for a weakly proregular sequence the
  Koszul system and the quotient system are isomorphic as pro-objects of `D(R)`, by way of the
  augmentations. (Remark 0H1E itself is
  `Koszul.nonempty_qcIdealPow_linearTriangulatedEquivalence_derivedComplete`.)
* `Koszul.isWeaklyProregular_of_isZero_homology` and `Koszul.isWeaklyProregular_of_isEmpty`:
  a sequence whose Koszul complexes are acyclic away from degree `0`, the empty sequence in
  particular, is weakly proregular.

## Implementation notes

The inverse systems are indexed by `ℕᵒᵖ` with the stage `n` carrying `K_{n + 1}`, because the
Koszul transition homomorphisms are defined for `1 ≤ n ≤ m`. `Koszul.IsWeaklyProregular` keeps
the indexing of the source, and `Koszul.IsWeaklyProregular.exists_zero_homologyMap` reads it
on the system.

The underlying type of `K_n` and its grading are reached through the projections of a
structure literal, so instance search has to be allowed to unfold `Koszul.powAlgebra`: a
submodule of `K_n` and the same submodule of the exterior algebra otherwise carry instances
that agree only after unfolding, and `LinearEquiv.trans` across the two fails to elaborate.

Being an isomorphism of pro-objects is spelled out, as in Stacks 0G3C, as the existence below
every index of a single morphism whose two round trips with the given comparison are the
transition morphisms; this puts no size condition on the index category.

## References

* [Stacks Project, Tag 0H1E](https://stacks.math.columbia.edu/tag/0H1E)
* [Stacks Project, Tag 0GZK](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/- The Koszul algebra and its degree-zero piece are reached through the projections of a
structure literal, so instance search must be allowed to unfold them: without this a submodule
of `K_n` and the same submodule of the exterior algebra carry instances that are equal only by
unfolding. -/
attribute [local implicit_reducible] powAlgebra cohomologicalDifferentialGradedAlgebra
  DifferentialGradedModule.toCochainComplex

/-- The transition homomorphism from `K_n` to itself is the identity on the underlying cochain
complex. -/
theorem powTransition_toCochainMap_self (f : Fin r → R) {n : ℕ} (hn : 1 ≤ n) :
    (powTransition f hn (le_refl n)).toCochainMap = 𝟙 _ :=
  DifferentialGradedAlgebra.Hom.toCochainMap_eq_id _ fun a =>
    congrFun (congrArg (fun φ : _ →ₐ[R] _ => (φ : _ → _))
      (powTransition_self_toAlgebraHom f hn)) a

/-- The inverse system `(K_{n+1})_{n}` of cochain complexes of `R`-modules underlying the
Koszul differential graded algebras on the powers of `f`. -/
def powCochainSystem (f : Fin r → R) : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj n := (regularModule (powAlgebra f (n.unop + 1))).toCochainComplex
  map {_ _} g := (powTransition f (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_succ (leOfHom g.unop))).toCochainMap
  map_id _ := powTransition_toCochainMap_self f _
  map_comp {_ _ _} _ _ := (DifferentialGradedAlgebra.Hom.toCochainMap_comp_eq _ _ _
    (fun a => powTransition_comp_apply f _ _ _ a)).symm

/-- **A weakly proregular sequence**, Stacks 0H1E: for every `n` there is an `m > n` such that
the transition homomorphism `K_m → K_n` of Koszul algebras induces the zero map on cohomology
in every degree other than `0`. -/
def IsWeaklyProregular (f : Fin r → R) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∃ (m : ℕ) (hm : n < m), ∀ i : ℤ, i ≠ 0 →
    HomologicalComplex.homologyMap (powTransition f hn hm.le).toCochainMap i = 0

/-- The inverse system `(R / (f₁ ^ (n+1), …, f_r ^ (n+1)))_n` of quotients. -/
def powQuotientSystem (f : Fin r → R) : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (R ⧸ powIdeal f (n.unop + 1))
  map {_ _} g := ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id
    (powIdeal_le f (Nat.succ_le_succ (leOfHom g.unop))))
  map_id _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  map_comp {_ _ _} _ _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- The piece of `K_n` in cohomological degree `0` is the zeroth exterior power. -/
theorem powAlgebra_grading_zero (f : Fin r → R) (n : ℕ) :
    (powAlgebra f n).grading 0 = ⋀[R]^0 (Fin r → R) := by
  simpa using powAlgebra_grading_neg_natCast f n 0

/-- The piece of `K_n` in cohomological degree `-1` is the first exterior power. -/
theorem powAlgebra_grading_neg_one (f : Fin r → R) (n : ℕ) :
    (powAlgebra f n).grading (-1) = ⋀[R]^1 (Fin r → R) := by
  simpa using powAlgebra_grading_neg_natCast f n 1

/-- The degree-zero piece of the Koszul algebra `K_n` is the base ring. -/
def gradeZeroEquiv (f : Fin r → R) (n : ℕ) : (powAlgebra f n).grading 0 ≃ₗ[R] R :=
  (LinearEquiv.ofEq ((powAlgebra f n).grading 0) (⋀[R]^0 (Fin r → R))
    (powAlgebra_grading_zero f n)).trans (exteriorPower.zeroEquiv R (Fin r → R))

/-- A degree-zero element of `K_n` written as the image of `a : R` has `a` as its value. -/
theorem gradeZeroEquiv_eq_of_coe (f : Fin r → R) (n : ℕ) {z : (powAlgebra f n).grading 0}
    {a : R} (hz : z.val = algebraMap R (ExteriorAlgebra R (Fin r → R)) a) :
    gradeZeroEquiv f n z = a := by
  simp only [gradeZeroEquiv, LinearEquiv.trans_apply]
  exact zeroEquiv_eq_of_coe hz

/-- The differential of `K_n` from degree `-1` to degree `0` is contraction. -/
theorem coe_gradedDifferential_neg_one (f : Fin r → R) (n : ℕ)
    (x : (powAlgebra f n).grading (-1)) :
    ((regularModule (powAlgebra f n)).gradedDifferential (-1) x).val
      = contraction (seqDual fun i => f i ^ n) x.val := rfl

/-- The linear form of the sequence of `n`-th powers takes values in the ideal they
generate. -/
theorem seqDual_mem_powIdeal (f : Fin r → R) (n : ℕ) (v : Fin r → R) :
    seqDual (fun i => f i ^ n) v ∈ powIdeal f n := by
  rw [seqDual_apply, powIdeal]
  exact Submodule.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The degree-zero component of the Koszul augmentation: the quotient map `K_n^0 = R → R/I_n`
where `I_n = (f₁ ^ n, …, f_r ^ n)`. -/
def powAugmentationZero (f : Fin r → R) (n : ℕ) :
    ((powAlgebra f n).grading 0) →ₗ[R] (R ⧸ powIdeal f n) :=
  (powIdeal f n).mkQ ∘ₗ (gradeZeroEquiv f n).toLinearMap

/-- The augmentation kills the image of the differential arriving in degree `0`. -/
theorem powAugmentationZero_gradedDifferential (f : Fin r → R) (n : ℕ)
    (x : (powAlgebra f n).grading (-1)) :
    powAugmentationZero f n ((regularModule (powAlgebra f n)).gradedDifferential (-1) x) = 0 := by
  have hy : x.val ∈ ⋀[R]^1 (Fin r → R) := by
    rw [← powAlgebra_grading_neg_one f n]
    exact x.2
  have hz : ((regularModule (powAlgebra f n)).gradedDifferential (-1) x).val
      = algebraMap R (ExteriorAlgebra R (Fin r → R))
          (seqDual (fun i => f i ^ n)
            (exteriorPower.oneEquiv R (Fin r → R) ⟨x.val, hy⟩)) := by
    rw [coe_gradedDifferential_neg_one]
    have h := coe_d_zero (fun i => f i ^ n) (⟨x.val, hy⟩ : ⋀[R]^1 (Fin r → R))
    rw [d_apply_coe] at h
    exact h
  show (powIdeal f n).mkQ (gradeZeroEquiv f n _) = 0
  rw [gradeZeroEquiv_eq_of_coe f n hz, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact seqDual_mem_powIdeal f n _

/-- **The Koszul augmentation** `K_n → R / (f₁ ^ n, …, f_r ^ n)`, with the quotient placed in
degree `0`. -/
def powAugmentation (f : Fin r → R) (n : ℕ) :
    (regularModule (powAlgebra f n)).toCochainComplex ⟶
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R (R ⧸ powIdeal f n)) :=
  HomologicalComplex.mkHomToSingle (ModuleCat.ofHom (powAugmentationZero f n)) (fun i hi => by
    obtain rfl : i = -1 := by
      have h : i + 1 = 0 := hi
      omega
    have hd : (regularModule (powAlgebra f n)).toCochainComplex.d (-1) 0
        = ModuleCat.ofHom ((regularModule (powAlgebra f n)).gradedDifferential (-1)) :=
      toCochainComplex_d (regularModule (powAlgebra f n)) (-1)
    rw [hd]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact powAugmentationZero_gradedDifferential f n x)

/-- A degree-zero element of `K_n` is the image of its value under the structure map. -/
theorem coe_eq_algebraMap_gradeZeroEquiv (f : Fin r → R) (n : ℕ)
    (z : (powAlgebra f n).grading 0) :
    z.val = algebraMap R (ExteriorAlgebra R (Fin r → R)) (gradeZeroEquiv f n z) := by
  have h : ((LinearEquiv.ofEq ((powAlgebra f n).grading 0) (⋀[R]^0 (Fin r → R))
      (powAlgebra_grading_zero f n)) z)
      = (exteriorPower.zeroEquiv R (Fin r → R)).symm (gradeZeroEquiv f n z) := by
    simp [gradeZeroEquiv]
  have h2 := congrArg Subtype.val h
  rw [coe_zeroEquiv_symm] at h2
  exact h2

/-- The transition homomorphisms preserve the value of a degree-zero element. -/
theorem gradeZeroEquiv_powTransition (f : Fin r → R) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m)
    (x : (powAlgebra f m).grading 0) (y : (powAlgebra f n).grading 0)
    (hy : y.val = (powTransition f hn hnm).toAlgebraHom x.val) :
    gradeZeroEquiv f n y = gradeZeroEquiv f m x := by
  refine gradeZeroEquiv_eq_of_coe f n ?_
  rw [hy, coe_eq_algebraMap_gradeZeroEquiv f m x]
  exact AlgHom.commutes _ _

/-- The transition cochain maps preserve the value of a degree-zero element. -/
theorem gradeZeroEquiv_toCochainMap_f_zero (f : Fin r → R) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m)
    (x : ((regularModule (powAlgebra f m)).toCochainComplex).X 0) :
    gradeZeroEquiv f n (((powTransition f hn hnm).toCochainMap.f 0).hom x)
      = gradeZeroEquiv f m x :=
  gradeZeroEquiv_powTransition f hn hnm x _ rfl

attribute [local implicit_reducible] powCochainSystem powQuotientSystem powAugmentation

/-- The augmentations are compatible with the transition homomorphisms. -/
def powAugmentationSystem (f : Fin r → R) :
    powCochainSystem f ⟶ powQuotientSystem f ⋙
      HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0 where
  app n := powAugmentation f (n.unop + 1)
  naturality {m n} g := by
    have key : ((powCochainSystem f).map g).f 0 ≫
          ModuleCat.ofHom (powAugmentationZero f (n.unop + 1))
        = ModuleCat.ofHom (powAugmentationZero f (m.unop + 1)) ≫
          (powQuotientSystem f).map g := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      exact congrArg (fun a : R => (Submodule.Quotient.mk a : R ⧸ powIdeal f (n.unop + 1)))
        (gradeZeroEquiv_toCochainMap_f_zero f (Nat.succ_le_succ (Nat.zero_le _))
          (Nat.succ_le_succ (leOfHom g.unop)) x)
    refine HomologicalComplex.to_single_hom_ext ?_
    simp only [HomologicalComplex.comp_f, powAugmentation, HomologicalComplex.mkHomToSingle_f,
      Functor.comp_map, HomologicalComplex.single_map_f_self, Category.assoc]
    rw [← Category.assoc, key, Category.assoc]
    simp [powQuotientSystem]

/-- An element of the zeroth exterior power is the image of its value under the structure
map. -/
theorem coe_eq_algebraMap_zeroEquiv (w : ⋀[R]^0 (Fin r → R)) :
    w.val = algebraMap R (ExteriorAlgebra R (Fin r → R))
      (exteriorPower.zeroEquiv R (Fin r → R) w) := by
  conv_lhs => rw [← (exteriorPower.zeroEquiv R (Fin r → R)).symm_apply_apply w]
  exact coe_zeroEquiv_symm _

/-- A degree-zero element of `K_n` whose value in `R` lies in `(f₁ ^ n, …, f_r ^ n)` is a
boundary. -/
theorem exists_gradedDifferential_eq (f : Fin r → R) (n : ℕ)
    (z : (powAlgebra f n).grading 0) (hz : gradeZeroEquiv f n z ∈ powIdeal f n) :
    ∃ x : (powAlgebra f n).grading (-1),
      (regularModule (powAlgebra f n)).gradedDifferential (-1) x = z := by
  rw [powIdeal, ← range_d_zero (fun i => f i ^ n)] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  obtain ⟨x', rfl⟩ := hw
  have hx : (x' : ExteriorAlgebra R (Fin r → R)) ∈ (powAlgebra f n).grading (-1) := by
    rw [powAlgebra_grading_neg_one f n]
    exact x'.2
  refine ⟨⟨x'.val, hx⟩, Subtype.ext ?_⟩
  rw [coe_gradedDifferential_neg_one, coe_eq_algebraMap_gradeZeroEquiv f n z, ← hwz]
  exact (d_apply_coe (seqDual fun i => f i ^ n) 0 x').symm.trans
    (coe_eq_algebraMap_zeroEquiv _)

/-- The degree-zero component of the Koszul augmentation is surjective. -/
theorem surjective_powAugmentationZero (f : Fin r → R) (n : ℕ) :
    Function.Surjective (powAugmentationZero f n) :=
  (Submodule.mkQ_surjective _).comp (gradeZeroEquiv f n).surjective

/-- The Koszul augmentation in degree `0`. -/
theorem powAugmentation_f_zero (f : Fin r → R) (n : ℕ) :
    (powAugmentation f n).f 0 = ModuleCat.ofHom (powAugmentationZero f n) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R (R ⧸ powIdeal f n))).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- The differential of the complex underlying `K_n` from degree `-1` to degree `0`. -/
theorem powCochain_d_neg_one (f : Fin r → R) (n : ℕ) :
    (regularModule (powAlgebra f n)).toCochainComplex.d (-1) 0
      = ModuleCat.ofHom ((regularModule (powAlgebra f n)).gradedDifferential (-1)) :=
  toCochainComplex_d (regularModule (powAlgebra f n)) (-1)

/-- The Koszul augmentation in degree `0`, read in the quotient itself. -/
theorem powAugmentation_f_zero_comp (f : Fin r → R) (n : ℕ) :
    (powAugmentation f n).f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of R (R ⧸ powIdeal f n))).hom
      = ModuleCat.ofHom (powAugmentationZero f n) := by
  rw [powAugmentation_f_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A degree-zero element killed by the augmentation has its value in the ideal of the
`n`-th powers. -/
theorem gradeZeroEquiv_mem_powIdeal_of_augmentation (f : Fin r → R) (n : ℕ)
    (x : ((regularModule (powAlgebra f n)).toCochainComplex).X 0)
    (hx : ((powAugmentation f n).f 0).hom x = 0) :
    gradeZeroEquiv f n x ∈ powIdeal f n := by
  have hx' : powAugmentationZero f n x = 0 := by
    show (ModuleCat.ofHom (powAugmentationZero f n)).hom x = 0
    rw [← powAugmentation_f_zero_comp f n, ModuleCat.hom_comp, LinearMap.comp_apply, hx]
    exact map_zero _
  rw [← Submodule.Quotient.mk_eq_zero]
  exact hx'

/-- **The Koszul augmentation is an isomorphism on `H⁰`**: the degree-zero cohomology of `K_n`
is `R / (f₁ ^ n, …, f_r ^ n)`. -/
theorem quasiIsoAt_powAugmentation (f : Fin r → R) (n : ℕ) :
    QuasiIsoAt (powAugmentation f n) 0 := by
  have hzero1 : Limits.IsZero ((regularModule (powAlgebra f n)).toCochainComplex.X 1) :=
    isZero_powAlgebra_toCochainComplex_X f n (by norm_num)
  refine (quasiIsoAt_iff' (powAugmentation f n) (-1) 0 1 (by simp) (by simp)).2 ?_
  refine (ShortComplex.quasiIso_iff_of_zeros' _ (hzero1.eq_of_tgt _ _)
      (by simp; rfl) (by simp; rfl)).2 ⟨?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hmem := gradeZeroEquiv_mem_powIdeal_of_augmentation f n x hx
    obtain ⟨y, hy⟩ := exists_gradedDifferential_eq f n x hmem
    refine ⟨y, ?_⟩
    show (ModuleCat.Hom.hom ((regularModule (powAlgebra f n)).toCochainComplex.d (-1) 0)) y = x
    rw [powCochain_d_neg_one]
    exact hy
  · show Epi ((powAugmentation f n).f 0)
    rw [powAugmentation_f_zero]
    exact @epi_comp _ _ _ _ _ _
      ((ModuleCat.epi_iff_surjective _).2 (surjective_powAugmentationZero f n)) _ inferInstance

/-! ### Vanishing outside the degrees `-r, …, 0` -/

/-- `K_n` vanishes in cohomological degrees below `-r`: there the graded piece is an exterior
power of `Rʳ` above the rank. -/
@[sga "6 VII 4.1" "finite free affine case"]
theorem subsingleton_powAlgebra_grading_of_lt (f : Fin r → R) (n : ℕ) {i : ℤ}
    (hi : i < -(r : ℤ)) : Subsingleton ((powAlgebra f n).grading i) := by
  have h : (powAlgebra f n).grading i = ⋀[R]^((-i).toNat) (Fin r → R) := by
    rw [powAlgebra_grading, cohomologicalExteriorGrade_of_nonpos R (Fin r → R) (by omega)]
  rw [h]
  exact Stacks.ExteriorPower.subsingleton_exteriorPower_of_lt (Pi.basisFun R (Fin r)) (by omega)

/-- The complex underlying `K_n` vanishes in cohomological degrees below `-r`. -/
theorem isZero_powAlgebra_toCochainComplex_X_of_lt (f : Fin r → R) (n : ℕ) {i : ℤ}
    (hi : i < -(r : ℤ)) :
    Limits.IsZero ((regularModule (powAlgebra f n)).toCochainComplex.X i) := by
  rw [toCochainComplex_X, ModuleCat.isZero_of_iff_subsingleton]
  exact subsingleton_powAlgebra_grading_of_lt f n hi

/-- A cochain complex with a zero term has zero cohomology in that degree. -/
theorem isZero_homology_of_isZero_X {K : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (h : Limits.IsZero (K.X i)) : Limits.IsZero (K.homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ (S := K.sc i) h

/-- The cohomology of `K_n` vanishes outside the degrees `-r, …, 0`. -/
theorem isZero_homology_powCochain (f : Fin r → R) (n : ℕ) {i : ℤ}
    (hi : i < -(r : ℤ) ∨ 0 < i) :
    Limits.IsZero ((regularModule (powAlgebra f n)).toCochainComplex.homology i) := by
  refine isZero_homology_of_isZero_X ?_
  rcases hi with hi | hi
  · exact isZero_powAlgebra_toCochainComplex_X_of_lt f n hi
  · exact isZero_powAlgebra_toCochainComplex_X f n hi

/-- Weak proregularity, read on the inverse system: every index is refined by one along which
the transition map of Koszul complexes is zero on cohomology outside degree `0`. -/
theorem IsWeaklyProregular.exists_zero_homologyMap {f : Fin r → R}
    (hf : IsWeaklyProregular f) (n : ℕ) :
    ∃ (m : ℕ) (hm : n ≤ m), ∀ i : ℤ, i ≠ 0 →
      HomologicalComplex.homologyMap ((powCochainSystem f).map (homOfLE hm).op) i = 0 := by
  obtain ⟨M, hM, hzero⟩ := hf (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  exact ⟨M', by omega, hzero⟩

/-- A sequence whose Koszul complexes are acyclic outside degree `0` is weakly proregular. -/
theorem isWeaklyProregular_of_isZero_homology (f : Fin r → R)
    (h : ∀ (n : ℕ) (i : ℤ), i ≠ 0 →
      Limits.IsZero ((regularModule (powAlgebra f n)).toCochainComplex.homology i)) :
    IsWeaklyProregular f :=
  fun n _ => ⟨n + 1, by omega, fun i hi => (h n i hi).eq_of_tgt _ _⟩

/-- The empty sequence is weakly proregular. -/
theorem isWeaklyProregular_of_isEmpty (f : Fin 0 → R) : IsWeaklyProregular f := by
  refine isWeaklyProregular_of_isZero_homology f fun n i hi => ?_
  refine isZero_homology_powCochain f n ?_
  rcases lt_or_gt_of_ne hi with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr h

/-! ### The pro-isomorphism in the derived category -/

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The Koszul algebras of the powers of `f` as an inverse system in the derived category of
`R`-modules. -/
abbrev powDerivedSystem (f : Fin r → R) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  powCochainSystem f ⋙ DerivedCategory.Q

/-- The quotients `R / (f₁ ^ (n+1), …, f_r ^ (n+1))` as an inverse system in the derived
category of `R`-modules. -/
abbrev powQuotientDerivedSystem (f : Fin r → R) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (powQuotientSystem f ⋙ HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0) ⋙
    DerivedCategory.Q

/-- The Koszul augmentations as a morphism of inverse systems of the derived category. -/
def powAugmentationDerived (f : Fin r → R) :
    powDerivedSystem f ⟶ powQuotientDerivedSystem f :=
  Functor.whiskerRight (powAugmentationSystem f) DerivedCategory.Q

/-- The cohomology of a complex in the derived category is its cohomology. -/
theorem isZero_homologyFunctor_obj_Q_obj {K : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (h : Limits.IsZero (K.homology i)) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (DerivedCategory.Q.obj K)) :=
  h.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K)

/-- A cochain map which is zero on cohomology in a degree is zero on the cohomology of the
derived category in that degree. -/
theorem homologyFunctor_map_Q_map_eq_zero {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : K ⟶ L) (i : ℤ) (h : HomologicalComplex.homologyMap φ i = 0) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map (DerivedCategory.Q.map φ) = 0 := by
  have hn := DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat.{u} R) φ i
  refine (cancel_mono
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).hom.app L)).1 (hn.trans ?_)
  simp only [h, Limits.zero_comp]
  exact Limits.comp_zero

/-- A cochain map which is invertible on cohomology in a degree is invertible on the cohomology
of the derived category in that degree. -/
theorem isIso_homologyFunctor_map_Q_map {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : K ⟶ L) (i : ℤ) (h : IsIso (HomologicalComplex.homologyMap φ i)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      (DerivedCategory.Q.map φ)) := by
  have := h
  have hn := DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat.{u} R) φ i
  have h2 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      (DerivedCategory.Q.map φ) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).hom.app L) := by
    rw [hn]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _) h
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).hom.app L)

/-- **The Koszul tower of a weakly proregular sequence is pro-isomorphic to the quotient tower.**
Let `f₁, …, f_r` be a weakly proregular sequence (Stacks 0H1E) in a commutative ring `R`. Then
the Koszul augmentations exhibit the inverse system of the Koszul differential graded algebras
`K_n` on `f₁ ^ n, …, f_r ^ n` as isomorphic, as a pro-object of the derived category of
`R`-modules, to the inverse system of the quotients `R / (f₁ ^ n, …, f_r ^ n)`: every index `j`
admits an arrow `g : k ⟶ j` and a morphism `s` from the quotient system at `k` to the Koszul
system at `j` whose two round trips with the augmentations are the transition morphisms of the
two systems. -/
theorem exists_proInverse_powAugmentationDerived (f : Fin r → R)
    (hf : IsWeaklyProregular f) (j : ℕᵒᵖ) :
    ∃ (k : ℕᵒᵖ) (g : k ⟶ j)
      (s : (powQuotientDerivedSystem f).obj k ⟶ (powDerivedSystem f).obj j),
      (powAugmentationDerived f).app k ≫ s = (powDerivedSystem f).map g ∧
        s ≫ (powAugmentationDerived f).app j = (powQuotientDerivedSystem f).map g := by
  refine DerivedCategory.exists_proInverse_of_proInverse_homology
    (powAugmentationDerived f) (-(r : ℤ)) 0 ?_ ?_ ?_ j
  · intro i hi k
    exact isZero_homologyFunctor_obj_Q_obj (isZero_homology_powCochain f (k.unop + 1) hi)
  · intro i hi k
    have hi0 : i ≠ 0 := by rcases hi with h | h <;> omega
    exact isZero_homologyFunctor_obj_Q_obj
      (HomologicalComplex.isZero_single_obj_homology _ 0 _ i hi0)
  · intro i k
    rcases eq_or_ne i 0 with rfl | hi
    · have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
          ((powAugmentationDerived f).app k)) :=
        isIso_homologyFunctor_map_Q_map _ 0
          ((quasiIsoAt_iff_isIso_homologyMap _ 0).1 (quasiIsoAt_powAugmentation f (k.unop + 1)))
      exact ⟨k, 𝟙 k, inv ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((powAugmentationDerived f).app k)), by simp, by simp⟩
    · obtain ⟨m, hm, hzero⟩ := hf.exists_zero_homologyMap k.unop
      refine ⟨Opposite.op m, (homOfLE hm).op, 0, ?_, ?_⟩
      · rw [Limits.comp_zero]
        exact (homologyFunctor_map_Q_map_eq_zero _ i (hzero i hi)).symm
      · rw [Limits.zero_comp]
        refine ((isZero_homologyFunctor_obj_Q_obj
          (HomologicalComplex.isZero_single_obj_homology _ 0 _ i hi)).eq_of_src _ _).symm

end Koszul

end
