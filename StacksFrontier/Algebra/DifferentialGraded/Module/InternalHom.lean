module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTotalization
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomTotal

/-!
# The internal hom of a differential graded bimodule

Let `A` and `B` be differential graded algebras over a commutative ring `R`, let `N` be a right
differential graded `B`-module carrying a compatible left differential graded `A`-action, and let
`P` be a right differential graded `B`-module. The graded right-`B`-linear maps `N → P` then form
a right differential graded `A`-module `Hom^•_B(N, P)`, the algebra `A` acting by precomposition
with its left action on `N`. This is the internal hom of Section 22.30.

The main result is that this construction commutes with shifting: the shift of `Hom^•_B(N, P)` is
isomorphic, with no intervening sign, to `Hom^•_B(N, P[k])`.

## Main definitions

* `DifferentialGradedModule.HomModuleData`: data presenting the internal hom — a right
  differential graded `A`-module whose degree-`n` piece is the degree-`n` homogeneous
  right-`B`-linear maps `N → P`, compatibly with the differential and with the `A`-action.

## Main results

* `DifferentialGradedModule.shiftHomModuleIso`: the canonical sign-free isomorphism
  `Hom^•_B(N, P)[k] ≅ Hom^•_B(N, P[k])` of right differential graded `A`-modules.

## Implementation notes

*The internal hom is characterized, not named.* The graded Hom module has no single canonical
presentation: its degree-`n` piece is only identified with `Hom^n_B(N, P)` up to the chosen
equivalence. `HomModuleData` records a module together with those identifications and the two
formulas they satisfy, and `shiftHomModuleIso` asserts the existence of such data on both sides
together with the isomorphism between them. The construction realizing the data is built here but
kept private: every consumer should take a `HomModuleData` as input, so that nothing depends on
the particular direct sum used to build one.

*The underlying module is the tautologically graded direct sum.* The module is
`⨁_n Hom^n_B(N, P)` with the grading `DirectSum.rangeGrading` and the differential
`DifferentialGradedModule.homTotalDifferential`; what this file adds is the right `A`-action and
the Leibniz rule relating it to that differential.

*The left action is taken from the totalization API.* The left action of a homogeneous `a : A^m`
on the whole of `N` is `DifferentialGraded.leftActionTotal`, together with its multiplicativity,
unitality, Leibniz rule and commutation with the right `B`-action; only the commutation needs
generalizing here, from a homogeneous element of `B` to an arbitrary one, which is
`DifferentialGradedModule.leftActionTotal_op_smul`.

*No elaboration-budget raise is needed.* Building the differential graded module from the direct
sum requires checking that the `A`-action respects the grading and obeys the Leibniz rule; both
obligations are discharged by separate private lemmas phrased through the action map rather than
through the `MulOpposite` scalar action, so that the module itself elaborates within the default
budget.

## References

* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]
variable (A B : DifferentialGradedAlgebra.{u, u} R)
variable (N P : DifferentialGradedModule.{u, u, u} B)
variable (L : BimoduleStructure A B N)

/-! ### The left action of `A` on `N`, totalized -/

/-- The left action of a homogeneous element of `A` on `N` commutes with the right action of an
arbitrary element of `B`. This is `DifferentialGraded.leftActionTotal_commutes` with the
homogeneity hypothesis on the element of `B` removed. -/
private theorem leftActionTotal_op_smul {m : ℤ} (a : A.grading m) (b : B.A) (y : N.M) :
    DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) (MulOpposite.op b • y) =
      MulOpposite.op b • DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) y := by
  induction b using DirectSum.Decomposition.inductionOn B.grading with
  | zero => simp
  | @homogeneous q b => exact DifferentialGraded.leftActionTotal_commutes A B N L.1 L.2 a b y
  | add b c hb hc =>
    simp only [MulOpposite.op_add, add_smul, map_add, hb, hc]

private theorem leftActionTotal_mul_comp {m n : ℤ} (a : A.grading m) (b : A.grading n) :
    DifferentialGraded.leftActionTotal A B N L.1 ((a : A.A) * (b : A.A)) =
      (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A)).comp
        (DifferentialGraded.leftActionTotal A B N L.1 (b : A.A)) := by
  rw [DifferentialGraded.leftActionTotal_mul A B N L.1 a b,
    DifferentialGraded.leftActionTotal_apply A B N L.1 m a,
    DifferentialGraded.leftActionTotal_apply A B N L.1 n b, Module.End.mul_eq_comp]

/-! ### The right action of `A` on the graded Hom module -/

/-- Precomposition with the left action of a homogeneous `a : A^m`, as an `R`-linear map from
degree-`n` to degree-`n + m` homogeneous right-`B`-linear maps. -/
private noncomputable def homPrecomp (n m : ℤ) (a : A.grading m) :
    HomogeneousMap B N P n →ₗ[R] HomogeneousMap B N P (n + m) where
  toFun f := ⟨f.1.comp (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A)), by
    refine ⟨fun i x hx => ?_, fun b x => ?_⟩
    · change f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) x) ∈
        P.grading (i + (n + m))
      have hdeg : i + m + n = i + (n + m) := by omega
      simpa only [hdeg] using
        f.2.1 (i + m) _ (DifferentialGraded.leftActionTotal_apply_mem A B N L.1 a ⟨x, hx⟩)
    · change f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A)
          (MulOpposite.op b • x)) =
        MulOpposite.op b • f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) x)
      rw [leftActionTotal_op_smul A B N L a b x, f.2.2 b]⟩
  map_add' f g := by
    apply Subtype.ext
    ext x
    simp [LinearMap.comp_apply]
  map_smul' r f := by
    apply Subtype.ext
    ext x
    simp [LinearMap.comp_apply]

private noncomputable def homPrecompₗ (n m : ℤ) :
    A.grading m →ₗ[R] (HomogeneousMap B N P n →ₗ[R] HomogeneousMap B N P (n + m)) where
  toFun a := homPrecomp A B N P L n m a
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext x
    change f.1 (DifferentialGraded.leftActionTotal A B N L.1 ((a + b : A.grading m) : A.A) x) =
      f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) x) +
        f.1 (DifferentialGraded.leftActionTotal A B N L.1 (b : A.A) x)
    rw [Submodule.coe_add, map_add]
    simp
  map_smul' r a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext x
    change f.1 (DifferentialGraded.leftActionTotal A B N L.1 ((r • a : A.grading m) : A.A) x) =
      r • f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) x)
    rw [SetLike.val_smul, map_smul]
    simp

private noncomputable def homActionHomogeneous (m : ℤ) (a : A.grading m) :
    HomTotal B N P →ₗ[R] HomTotal B N P :=
  DirectSum.toModule R ℤ (HomTotal B N P) fun n =>
    (DirectSum.lof R ℤ (fun n => HomogeneousMap B N P n) (n + m)).comp
      (homPrecomp A B N P L n m a)

private theorem homActionHomogeneous_of (n m : ℤ) (a : A.grading m)
    (f : HomogeneousMap B N P n) :
    homActionHomogeneous A B N P L m a (DirectSum.of (fun n => HomogeneousMap B N P n) n f) =
      DirectSum.of (fun n => HomogeneousMap B N P n) (n + m)
        (homPrecomp A B N P L n m a f) := by
  show (DirectSum.toModule R ℤ (HomTotal B N P) fun i =>
    (DirectSum.lof R ℤ (fun j => HomogeneousMap B N P j) (i + m)).comp
      (homPrecomp A B N P L i m a))
      (DirectSum.lof R ℤ (fun i => HomogeneousMap B N P i) n f) = _
  rw [DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]

private noncomputable def homActionHomogeneousₗ (m : ℤ) :
    A.grading m →ₗ[R] (HomTotal B N P →ₗ[R] HomTotal B N P) where
  toFun := homActionHomogeneous A B N P L m
  map_add' a b := by
    apply LinearMap.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp [homActionHomogeneous]
    | add x y hx hy => simp [map_add, hx, hy]
    | of n f =>
      simp only [LinearMap.add_apply, homActionHomogeneous_of]
      calc
        _ = DirectSum.of (fun j => HomogeneousMap B N P j) (n + m)
            (homPrecomp A B N P L n m a f + homPrecomp A B N P L n m b f) := by
              congr 1
              exact LinearMap.congr_fun
                (LinearMap.map_add (homPrecompₗ A B N P L n m) a b) f
        _ = _ := (DirectSum.of _ (n + m)).map_add _ _
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp [homActionHomogeneous]
    | add x y hx hy => simp [hx, hy]
    | of n f =>
      simp only [LinearMap.smul_apply, RingHom.id_apply, homActionHomogeneous_of]
      calc
        _ = DirectSum.of (fun j => HomogeneousMap B N P j) (n + m)
            (r • homPrecomp A B N P L n m a f) := by
              congr 1
              exact LinearMap.congr_fun
                (LinearMap.map_smul (homPrecompₗ A B N P L n m) r a) f
        _ = _ := DirectSum.of_smul _ _ _ _

/-- The right action of `A` on `Hom^•_B(N, P)`, as an `R`-linear map into endomorphisms. -/
private noncomputable def homAction : A.A →ₗ[R] (HomTotal B N P →ₗ[R] HomTotal B N P) :=
  (DirectSum.toModule R ℤ (HomTotal B N P →ₗ[R] HomTotal B N P) fun m =>
    homActionHomogeneousₗ A B N P L m).comp
    (DirectSum.decomposeLinearEquiv A.grading).toLinearMap

private theorem homAction_of_grading (m : ℤ) (a : A.grading m) :
    homAction A B N P L (a : A.A) = homActionHomogeneous A B N P L m a := by
  apply LinearMap.ext
  intro x
  simp only [homAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  show (DirectSum.toModule R ℤ (HomTotal B N P →ₗ[R] HomTotal B N P)
    (fun i => homActionHomogeneousₗ A B N P L i)
    (DirectSum.lof R ℤ (fun i => A.grading i) m a)) x = _
  rw [DirectSum.toModule_lof R (φ := fun i => homActionHomogeneousₗ A B N P L i) m a]
  rfl

/-- Homogeneous maps of equal degrees with the same underlying map have equal images in the
direct sum. -/
private theorem of_eq_of_val_eq {i j : ℤ} (h : i = j) (f : HomogeneousMap B N P i)
    (g : HomogeneousMap B N P j) (hv : f.1 = g.1) :
    DirectSum.of (fun n => HomogeneousMap B N P n) i f =
      DirectSum.of (fun n => HomogeneousMap B N P n) j g :=
  DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext h (homogeneousMap_heq_of_val_eq h f g hv))

private theorem homAction_one : homAction A B N P L 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp [homAction]
  | add x y hx hy => simp [hx, hy]
  | of n f =>
    rw [homAction_of_grading A B N P L 0 ⟨1, SetLike.one_mem_graded A.grading⟩,
      homActionHomogeneous_of]
    refine of_eq_of_val_eq B N P (add_zero n) _ _ ?_
    ext x
    simp [homPrecomp, DifferentialGraded.leftActionTotal_one A B N L.1]

private theorem homAction_mul_homogeneous (m n : ℤ) (a : A.grading m) (b : A.grading n) :
    homAction A B N P L ((a : A.A) * (b : A.A)) =
      (homAction A B N P L (b : A.A)).comp (homAction A B N P L (a : A.A)) := by
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | of q f =>
    rw [homAction_of_grading A B N P L (m + n)
      ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩,
      homActionHomogeneous_of, homAction_of_grading A B N P L n b, LinearMap.comp_apply,
      homAction_of_grading A B N P L m a, homActionHomogeneous_of, homActionHomogeneous_of]
    refine of_eq_of_val_eq B N P (by omega) _ _ ?_
    apply LinearMap.ext
    intro x
    show (f.1.comp (DifferentialGraded.leftActionTotal A B N L.1
        ((⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ :
          A.grading (m + n)) : A.A))) x =
      ((f.1.comp (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A))).comp
        (DifferentialGraded.leftActionTotal A B N L.1 (b : A.A))) x
    rw [show ((⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ :
        A.grading (m + n)) : A.A) = (a : A.A) * (b : A.A) from rfl,
      leftActionTotal_mul_comp A B N L a b]
    simp [LinearMap.comp_assoc]

private theorem homAction_mul (a b : A.A) :
    homAction A B N P L (a * b) =
      (homAction A B N P L b).comp (homAction A B N P L a) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp [homAction]
  | add a₁ a₂ ha₁ ha₂ =>
    simp only [map_add, add_mul]
    rw [ha₁, ha₂]
    simp [LinearMap.comp_add]
  | homogeneous a =>
    induction b using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp [homAction]
    | add b₁ b₂ hb₁ hb₂ =>
      simp only [map_add, mul_add]
      rw [hb₁, hb₂]
      simp [LinearMap.add_comp]
    | homogeneous b => exact homAction_mul_homogeneous A B N P L _ _ a b

/-- The right action of `A` on `Hom^•_B(N, P)`, as a ring homomorphism from the opposite
algebra. -/
private noncomputable def homActionRingHom :
    MulOpposite A.A →+* Module.End R (HomTotal B N P) where
  toFun a := homAction A B N P L (MulOpposite.unop a)
  map_zero' := by simp [homAction]
  map_add' a b := by
    change homAction A B N P L (MulOpposite.unop (a + b)) = _
    rw [MulOpposite.unop_add]
    exact (homAction A B N P L).map_add _ _
  map_one' := by
    change homAction A B N P L (1 : A.A) = 1
    rw [homAction_one]
    rfl
  map_mul' a b := by
    change homAction A B N P L (MulOpposite.unop (a * b)) = _
    rw [MulOpposite.unop_mul]
    exact homAction_mul A B N P L (MulOpposite.unop b) (MulOpposite.unop a)

/-! ### The graded Leibniz rule -/

private theorem homPrecomp_differential (n m : ℤ) (a : A.grading m)
    (f : HomogeneousMap B N P n) :
    homogeneousMapCongr (show n + m + 1 = n + (m + 1) by omega)
        (homogeneousMapDifferential B (homPrecomp A B N P L n m a f)) =
      homogeneousMapCongr (show n + 1 + m = n + (m + 1) by omega)
          (homPrecomp A B N P L (n + 1) m a (homogeneousMapDifferential B f)) +
        DifferentialGraded.gradedSign R n •
          homogeneousMapCongr (show n + (m + 1) = n + (m + 1) from rfl)
            (homPrecomp A B N P L n (m + 1) ⟨A.d a, A.d_mem m a a.property⟩ f) := by
  apply Subtype.ext
  ext x
  show P.d (f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) x)) -
      DifferentialGraded.gradedSign R (n + m) •
        f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) (N.d x)) =
    (P.d (f.1 (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) x)) -
      DifferentialGraded.gradedSign R n •
        f.1 (N.d (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) x))) +
      DifferentialGraded.gradedSign R n •
        f.1 (DifferentialGraded.leftActionTotal A B N L.1 (A.d a) x)
  rw [DifferentialGraded.leftActionTotal_leibniz A B N L.1 a x, map_add, map_zsmul,
    DifferentialGraded.gradedSign_add, ← Int.cast_smul_eq_zsmul R,
    DifferentialGraded.intCast_negOnePow]
  module

private theorem homTotal_leibniz_of (n m : ℤ) (f : HomogeneousMap B N P n) (a : A.grading m) :
    homTotalDifferential N P (homAction A B N P L (a : A.A)
        (DirectSum.of (fun j => HomogeneousMap B N P j) n f)) =
      homAction A B N P L (a : A.A) (homTotalDifferential N P
          (DirectSum.of (fun j => HomogeneousMap B N P j) n f)) +
        (n.negOnePow : ℤ) • homAction A B N P L (A.d a)
          (DirectSum.of (fun j => HomogeneousMap B N P j) n f) := by
  have hda : ((⟨A.d a, A.d_mem m a a.property⟩ : A.grading (m + 1)) : A.A) = A.d a := rfl
  rw [← hda]
  simp only [homAction_of_grading A B N P L m a,
    homAction_of_grading A B N P L (m + 1) ⟨A.d a, A.d_mem m a a.property⟩,
    homActionHomogeneous_of, homTotalDifferential_of]
  have h := homPrecomp_differential A B N P L n m a f
  rw [← DifferentialGraded.intCast_negOnePow (R := R) n,
    homogeneousMap_intCast_smul (n.negOnePow : ℤ)] at h
  have hL : n + m + 1 = n + (m + 1) := by omega
  have hF : n + 1 + m = n + (m + 1) := by omega
  have hleft := of_eq_of_val_eq B N P hL.symm
    (homogeneousMapCongr hL (homogeneousMapDifferential B (homPrecomp A B N P L n m a f)))
    (homogeneousMapDifferential B (homPrecomp A B N P L n m a f)) rfl
  have hfirst := of_eq_of_val_eq B N P hF.symm
    (homogeneousMapCongr hF
      (homPrecomp A B N P L (n + 1) m a (homogeneousMapDifferential B f)))
    (homPrecomp A B N P L (n + 1) m a (homogeneousMapDifferential B f)) rfl
  calc
    _ = DirectSum.of (fun j => HomogeneousMap B N P j) (n + (m + 1))
        (homogeneousMapCongr hL
          (homogeneousMapDifferential B (homPrecomp A B N P L n m a f))) := hleft.symm
    _ = DirectSum.of (fun j => HomogeneousMap B N P j) (n + (m + 1))
          (homogeneousMapCongr hF
            (homPrecomp A B N P L (n + 1) m a (homogeneousMapDifferential B f))) +
        (n.negOnePow : ℤ) • DirectSum.of (fun j => HomogeneousMap B N P j) (n + (m + 1))
          (homogeneousMapCongr (show n + (m + 1) = n + (m + 1) from rfl)
            (homPrecomp A B N P L n (m + 1) ⟨A.d a, A.d_mem m a a.property⟩ f)) := by
      simpa only [map_add, DirectSum.of_smul] using
        congrArg (DirectSum.of (fun j => HomogeneousMap B N P j) (n + (m + 1))) h
    _ = _ := by rw [hfirst]; rfl

/-! ### The internal hom as a right differential graded `A`-module -/

private theorem homAction_mem (n m : ℤ) (x : HomTotal B N P) (a : A.A)
    (hx : x ∈ DirectSum.rangeGrading R (fun n => HomogeneousMap B N P n) n)
    (ha : a ∈ A.grading m) :
    homAction A B N P L a x ∈
      DirectSum.rangeGrading R (fun n => HomogeneousMap B N P n) (n + m) := by
  obtain ⟨f, rfl⟩ := hx
  have ha' : (((⟨a, ha⟩ : A.grading m) : A.A)) = a := rfl
  rw [DirectSum.lof_eq_of, ← ha', homAction_of_grading A B N P L m ⟨a, ha⟩,
    homActionHomogeneous_of]
  exact ⟨homPrecomp A B N P L n m ⟨a, ha⟩ f,
    DirectSum.lof_eq_of R ℤ (fun n => HomogeneousMap B N P n) (n + m) _⟩

private theorem homAction_leibniz (n m : ℤ) (x : HomTotal B N P) (a : A.A)
    (hx : x ∈ DirectSum.rangeGrading R (fun n => HomogeneousMap B N P n) n)
    (ha : a ∈ A.grading m) :
    homTotalDifferential N P (homAction A B N P L a x) =
      homAction A B N P L a (homTotalDifferential N P x) +
        (n.negOnePow : ℤ) • homAction A B N P L (A.d a) x := by
  obtain ⟨f, rfl⟩ := hx
  rw [DirectSum.lof_eq_of]
  exact homTotal_leibniz_of A B N P L n m f ⟨a, ha⟩

/-- The graded module `⨁_n Hom^n_B(N, P)` of homogeneous right-`B`-linear maps, as a right
differential graded `A`-module: `A` acts by precomposition with its left action on `N`. -/
@[implicit_reducible]
private noncomputable def homModule : DifferentialGradedModule.{u, u, u} A :=
  letI : Module (MulOpposite A.A) (HomTotal B N P) :=
    Module.compHom _ (homActionRingHom A B N P L)
  letI : IsScalarTower R (MulOpposite A.A) (HomTotal B N P) := by
    refine ⟨?_⟩
    intro r a x
    change homAction A B N P L (MulOpposite.unop (r • a)) x =
      r • homAction A B N P L (MulOpposite.unop a) x
    rw [show MulOpposite.unop (r • a) = r • MulOpposite.unop a by simp,
      (homAction A B N P L).map_smul]
    rfl
  { M := HomTotal B N P
    grading := DirectSum.rangeGrading R fun n => HomogeneousMap B N P n
    decomposition := DirectSum.rangeGradingDecomposition R _
    smul_mem := fun n m x a hx ha => homAction_mem A B N P L n m x a hx ha
    d := homTotalDifferential N P
    d_comp_d := homTotalDifferential_comp_self N P
    d_mem := fun n x hx => homTotalDifferential_mem n x hx
    leibniz := fun n m x a hx ha => homAction_leibniz A B N P L n m x a hx ha }

/-! ### The internal hom, presented by its homogeneous pieces -/

/-- Data presenting the internal hom `Hom^•_B(N, P)` as a right differential graded `A`-module:
a differential graded `A`-module whose degree-`n` piece is identified with the degree-`n`
homogeneous right-`B`-linear maps `N → P`, compatibly with the differential, and whose right
`A`-action is precomposition with the left action of `A` on `N`. -/
structure HomModuleData (A B : DifferentialGradedAlgebra.{u, u} R)
    (N P : DifferentialGradedModule.{u, u, u} B) (L : BimoduleStructure A B N) where
  /-- The underlying right differential graded `A`-module. -/
  module : DifferentialGradedModule.{u, u, u} A
  /-- Its degree-`n` piece is the degree-`n` homogeneous right-`B`-linear maps `N → P`. -/
  homogeneousEquiv (n : ℤ) : module.grading n ≃ₗ[R] HomogeneousMap B N P n
  /-- The differential is the differential of the differential graded category of right
  differential graded `B`-modules. -/
  map_d (n : ℤ) (f : module.grading n) :
    homogeneousEquiv (n + 1) (module.gradedDifferential n f) =
      homogeneousMapDifferential B (homogeneousEquiv n f)
  /-- The right action of a homogeneous element of `A` is precomposition with its left action
  on `N`. -/
  map_smul (n m p : ℤ) (f : module.grading n) (a : A.grading m) (x : N.grading p) :
    ((homogeneousEquiv (n + m)
        ⟨MulOpposite.op (a : A.A) • (f : module.M),
          module.smul_mem n m (f : module.M) (a : A.A) f.property a.property⟩).1 x) =
      (homogeneousEquiv n f).1
        ((show N.grading (p + m) from (L.1.action m a).v p (p + m) (by omega) x) : N.M)

private noncomputable abbrev homModuleEquiv (n : ℤ) :
    DirectSum.rangeGrading R (fun n => HomogeneousMap B N P n) n ≃ₗ[R]
      HomogeneousMap B N P n :=
  DirectSum.rangeGradingEquiv R (fun n => HomogeneousMap B N P n) n

/-- A degree-`n` element of the graded Hom module is the inclusion of its homogeneous map. -/
private theorem lof_homModuleEquiv (n : ℤ)
    (f : DirectSum.rangeGrading R (fun n => HomogeneousMap B N P n) n) :
    DirectSum.lof R ℤ (fun j => HomogeneousMap B N P j) n (homModuleEquiv B N P n f) = f.1 :=
  congrArg Subtype.val ((homModuleEquiv B N P n).symm_apply_apply f)

/-- An element of the graded Hom module has a given homogeneous map if its image in the direct
sum is the inclusion of that map. -/
private theorem homModuleEquiv_eq_of_val_eq_lof (n : ℤ)
    (x : DirectSum.rangeGrading R (fun n => HomogeneousMap B N P n) n)
    (g : HomogeneousMap B N P n)
    (h : x.1 = DirectSum.lof R ℤ (fun j => HomogeneousMap B N P j) n g) :
    homModuleEquiv B N P n x = g := by
  apply (homModuleEquiv B N P n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact Subtype.ext h

private noncomputable def homModuleData : HomModuleData A B N P L where
  module := homModule A B N P L
  homogeneousEquiv n := homModuleEquiv B N P n
  map_d := by
    intro n f
    change DirectSum.rangeGrading R (fun j => HomogeneousMap B N P j) n at f
    apply homModuleEquiv_eq_of_val_eq_lof
    change homTotalDifferential N P (f : HomTotal B N P) =
      DirectSum.lof R ℤ (fun j => HomogeneousMap B N P j) (n + 1)
        (homogeneousMapDifferential B (homModuleEquiv B N P n f))
    rw [← lof_homModuleEquiv B N P n f, DirectSum.lof_eq_of, homTotalDifferential_of,
      DirectSum.lof_eq_of]
  map_smul := by
    intro n m p f a x
    change DirectSum.rangeGrading R (fun j => HomogeneousMap B N P j) n at f
    let _ : Module (MulOpposite A.A) (HomTotal B N P) := (homModule A B N P L).rmodule
    have hAct : ∀ z : HomTotal B N P,
        MulOpposite.op (a : A.A) • z = homAction A B N P L (a : A.A) z := fun _ => rfl
    have hsmul :
        homModuleEquiv B N P (n + m)
            ⟨MulOpposite.op (a : A.A) • (f : HomTotal B N P),
              (homModule A B N P L).smul_mem n m (f : HomTotal B N P)
                (a : A.A) f.property a.property⟩ =
          homPrecomp A B N P L n m a (homModuleEquiv B N P n f) := by
      apply homModuleEquiv_eq_of_val_eq_lof
      change MulOpposite.op (a : A.A) • (f : HomTotal B N P) =
        DirectSum.lof R ℤ (fun j => HomogeneousMap B N P j) (n + m)
          (homPrecomp A B N P L n m a (homModuleEquiv B N P n f))
      rw [hAct, ← lof_homModuleEquiv B N P n f, DirectSum.lof_eq_of,
        homAction_of_grading A B N P L m a, homActionHomogeneous_of, DirectSum.lof_eq_of]
    change (homModuleEquiv B N P (n + m)
        ⟨MulOpposite.op (a : A.A) • (f : HomTotal B N P),
          (homModule A B N P L).smul_mem n m (f : HomTotal B N P)
            (a : A.A) f.property a.property⟩).1 x =
      (homModuleEquiv B N P n f).1
        ((show N.grading (p + m) from (L.1.action m a).v p (p + m) (by omega) x) : N.M)
    rw [hsmul]
    change (homModuleEquiv B N P n f).1
        (DifferentialGraded.leftActionTotal A B N L.1 (a : A.A) (x : N.M)) =
      (homModuleEquiv B N P n f).1
        ((show N.grading (p + m) from (L.1.action m a).v p (p + m) (by omega) x) : N.M)
    rw [DifferentialGraded.leftActionTotal_apply A B N L.1 m a,
      totalizeCochain_apply_of_eq B N m p (p + m) rfl (L.1.action m a) x]
    rfl

private theorem homogeneousEquiv_val_congr (H : HomModuleData A B N P L) {i j : ℤ} (h : i = j)
    (f : H.module.grading i) (g : H.module.grading j) (hfg : f.1 = g.1) :
    (H.homogeneousEquiv i f).1 = (H.homogeneousEquiv j g).1 := by
  subst j
  obtain rfl : f = g := Subtype.ext hfg
  rfl

/-- **Stacks 0FQR.** The canonical, sign-free isomorphism `Hom^•_B(N, P)[k] ≅ Hom^•_B(N, P[k])`
of right differential graded `A`-modules. The displayed equation says that the homogeneous maps
associated with corresponding elements take the same value on every homogeneous element of `N`. -/
@[stacks 0FQR]
theorem shiftHomModuleIso (k : ℤ) :
    ∃ (H : HomModuleData A B N P L)
      (Hk : HomModuleData A B N (shift P k) L)
      (e : shift H.module k ≅ Hk.module),
      ∀ (n p : ℤ) (f : (shift H.module k).grading n) (x : N.grading p),
        ((Hk.homogeneousEquiv n (e.hom.gradedMap n f)).1 x : P.M) =
          (H.homogeneousEquiv (n + k)
            ⟨(f.1 : H.module.M), by
              simpa only [shift_grading] using f.property⟩).1 x := by
  classical
  let H : HomModuleData A B N P L := homModuleData A B N P L
  let Hk : HomModuleData A B N (shift P k) L :=
    { module := shift H.module k
      homogeneousEquiv := fun n =>
        (H.homogeneousEquiv (n + k)).trans (homogeneousMapShiftEquiv k n).symm
      map_d := by
        intro n f
        change H.module.grading (n + k) at f
        apply (homogeneousMapShiftEquiv (M := P) k (n + 1)).injective
        show H.homogeneousEquiv (n + 1 + k) ((shift H.module k).gradedDifferential n f) =
          homogeneousMapShiftEquiv k (n + 1) (homogeneousMapDifferential B
            ((homogeneousMapShiftEquiv (M := P) k n).symm (H.homogeneousEquiv (n + k) f)))
        rw [homogeneousMapShiftEquiv_differential, LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        show (H.homogeneousEquiv (n + 1 + k) ⟨k.negOnePow • H.module.d f, _⟩).1 =
          (DifferentialGraded.gradedSign R k •
            homogeneousMapDifferential B (H.homogeneousEquiv (n + k) f)).1
        calc
          _ = (H.homogeneousEquiv (n + k + 1)
              ((k.negOnePow : ℤ) • H.module.gradedDifferential (n + k) f)).1 := by
            apply homogeneousEquiv_val_congr A B N P L H (by omega)
            rfl
          _ = _ := by
            rw [map_zsmul, H.map_d]
            show (k.negOnePow : ℤ) •
              (homogeneousMapDifferential B (H.homogeneousEquiv (n + k) f)).1 = _
            rw [← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow]
            rfl
      map_smul := by
        intro n m p f a x
        change H.module.grading (n + k) at f
        show ((homogeneousMapShiftEquiv (M := P) k (n + m)).symm
            (H.homogeneousEquiv (n + m + k)
              ⟨MulOpposite.op (a : A.A) • (f : H.module.M), by
                simpa [add_assoc, add_comm, add_left_comm] using
                  H.module.smul_mem (n + k) m (f : H.module.M) (a : A.A)
                    f.property a.property⟩)).1 x =
          ((homogeneousMapShiftEquiv (M := P) k n).symm (H.homogeneousEquiv (n + k) f)).1
            ((show N.grading (p + m) from
              (L.1.action m a).v p (p + m) (by omega) x) : N.M)
        simp only [homogeneousMapShiftEquiv_symm_val]
        calc
          _ = (H.homogeneousEquiv (n + k + m)
              ⟨MulOpposite.op (a : A.A) • (f : H.module.M),
                H.module.smul_mem (n + k) m _ _ f.property a.property⟩).1 x := by
            congr 1
            apply homogeneousEquiv_val_congr A B N P L H (by omega)
            rfl
          _ = _ := H.map_smul (n + k) m p f a x }
  refine ⟨H, Hk, Iso.refl _, ?_⟩
  intro n p f x
  show (Hk.homogeneousEquiv n ((Iso.refl (shift H.module k)).hom.gradedMap n f)).1 x =
    (H.homogeneousEquiv (n + k)
      ⟨(f.1 : H.module.M), by simpa only [shift_grading] using f.property⟩).1 x
  simp only [Hk, LinearEquiv.trans_apply, homogeneousMapShiftEquiv_symm_val]
  rfl

end DifferentialGradedModule
