module

public import StacksFrontier.Algebra.DifferentialGraded.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.Algebra.DifferentialGraded.NativeCover.SurjectiveCover
public import StacksFrontier.Algebra.DifferentialGraded.NativeCover.CocycleCover

/-!
# Covering a differential graded module by direct sums of shifts of the algebra

Let `R` be a commutative ring, let `(A, d)` be a differential graded `R`-algebra and let `M`
be a right differential graded `A`-module. This file assembles the surjective cover and the
cocycle cover of `M` into a differential graded `A`-module `P` and a homomorphism `f : P ⟶ M`
which is surjective, is surjective on cocycles in every degree, and sits in an admissible
short exact sequence `0 → P' → P → P'' → 0` whose two ends are isomorphic to direct sums of
shifts `A[k]` of the algebra (Tag 09KN). Such a cover is the basic step from which resolutions
with property (P) are built.

The direct sum of the two covers has both properties at once, and its admissible short exact
sequence has ends `P'` and `P'' ⊕ P₂`, still direct sums of shifts.

## Main definitions

* `DifferentialGraded.NativeCover.Native.algebra`, `DifferentialGraded.NativeCover.Native.module`,
  `DifferentialGraded.NativeCover.Native.ofModule`: the translation between the two
  presentations of the same differential graded data.

## Main results

* `DifferentialGraded.NativeCover.cover_combine`: the assembly of the two covers into one.
* `DifferentialGraded.NativeCover.exists_dgModule_surjective_cover`: the resulting cover
  (Tag 09KN), in the presentation of this file.
* `DifferentialGraded.NativeCover.exists_native_cover`: the resulting cover, stated for the bundled
  differential graded modules of `Stacks.DifferentialGraded`.

## Implementation notes

These covers are the steps of the filtration built for the property-(P) resolution; the
universe parameters of that filtration are independent of one another.

Two presentations of a differential graded module are used. The one of
`StacksFrontier.Algebra.DifferentialGraded.NativeCover.DirectSumOfShifts` takes the carrier, the
grading and the differential as parameters, which keeps the universes of the scalar ring, of the
algebra and of the module independent and makes the carrier universe of every construction
visibly `max v w`. The bundled presentation of `Stacks.DifferentialGraded` is the one in which
the final statement is phrased; the `Native` section translates between them without changing
any carrier or any algebraic operation.

## References

* [The Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace DifferentialGraded.NativeCover

universe u v w w' w₁ w₂ w₃ t

/-- **Assembly.** Combine a surjective cover (in an admissible SES with DSS ends)
with a cocycle cover (DSS) into a single cover satisfying all three properties.

*Argument.* Set `P := P₁ ⊕ P₂` (binary direct sum of DG `A`-modules: action,
grading and differential componentwise) and `φ := φ₁ ⊕ φ₂` (i.e.
`φ (p₁, p₂) = φ₁ p₁ + φ₂ p₂`), a DG-hom since `φ₁`, `φ₂` are.  Then:
* `φ` is surjective because already `φ₁` is (`φ (p₁, 0) = φ₁ p₁`).
* `φ` is graded surjective on cocycles: a degree-`n` cocycle `m` of `M` is
  `φ₂ x` for some degree-`n` cocycle `x` of `P₂` (by the cocycle cover), hence
  `m = φ (0, x)` with `(0, x)` a degree-`n` cocycle of `P`.
* The admissible SES `0 → P' → P → P'' ⊕ P₂ → 0`: extend `i : P' → P₁` to
  `P' → P` by `i' = (i, 0)`, and `p : P₁ → P''` to `p' : P → P'' ⊕ P₂`,
  `p'(p₁, p₂) = (p p₁, p₂)`.  Then `i'` is an injective DG-hom, `p'` a surjective
  DG-hom, `range i' = ker p'` (since `range i = ker p` and the `P₂` factor passes
  through identically), and the graded `A`-linear splitting `P ≅ P' ⊕ (P'' ⊕ P₂)`
  is built from the splitting `P₁ ≅ P' ⊕ P''` and the identity on `P₂`.  Finally
  `P'' ⊕ P₂` is a direct sum of shifts of `A` because both `P''` and `P₂` are
  (concatenate their index sets and shift functions). -/
theorem cover_combine
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    {M : Type w} [AddCommGroup M] [Module R M] (PM : DGModule R A 𝒜 dA M)
    (h₁ : ∃ (P₁ : Type (max v w)) (_ : AddCommGroup P₁) (_ : Module R P₁)
      (PP₁ : DGModule R A 𝒜 dA P₁) (φ₁ : DGModule.Hom PP₁ PM),
      φ₁.Surjective ∧
      (∃ (P' : Type (max v w)) (_ : AddCommGroup P') (_ : Module R P')
        (PP' : DGModule R A 𝒜 dA P')
        (P'' : Type (max v w)) (_ : AddCommGroup P'') (_ : Module R P'')
        (PP'' : DGModule R A 𝒜 dA P''),
        IsDirectSumOfShifts.{u, v, _, w} PP' ∧ IsDirectSumOfShifts.{u, v, _, w} PP'' ∧
        Nonempty (AdmissibleSES PP' PP₁ PP'')))
    (h₂ : ∃ (P₂ : Type (max v w)) (_ : AddCommGroup P₂) (_ : Module R P₂)
      (PP₂ : DGModule R A 𝒜 dA P₂) (φ₂ : DGModule.Hom PP₂ PM),
      IsDirectSumOfShifts.{u, v, _, w} PP₂ ∧ φ₂.GradedSurjectiveOnCocycles) :
    ∃ (P : Type (max v w)) (_ : AddCommGroup P) (_ : Module R P)
      (PP : DGModule R A 𝒜 dA P) (φ : DGModule.Hom PP PM),
      φ.Surjective ∧
      φ.GradedSurjectiveOnCocycles ∧
      (∃ (P' : Type (max v w)) (_ : AddCommGroup P') (_ : Module R P')
        (PP' : DGModule R A 𝒜 dA P')
        (P'' : Type (max v w)) (_ : AddCommGroup P'') (_ : Module R P'')
        (PP'' : DGModule R A 𝒜 dA P''),
        IsDirectSumOfShifts.{u, v, _, w} PP' ∧ IsDirectSumOfShifts.{u, v, _, w} PP'' ∧
        Nonempty (AdmissibleSES PP' PP PP'')) := by
  -- P = P₁ ⊕ P₂, φ = φ₁ ⊕ φ₂, SES `0 → P' → P → P'' ⊕ P₂ → 0`.
  classical
  obtain ⟨P₁, _, _, PP₁, φ₁, hφ₁surj, P', _, _, PP', P'', _, _, PP'',
    hP'dss, hP''dss, ⟨ses₁⟩⟩ := h₁
  obtain ⟨P₂, _, _, PP₂, φ₂, hP₂dss, hφ₂cocyc⟩ := h₂
  -- The combined cover module `P = P₁ × P₂`.
  refine ⟨P₁ × P₂, inferInstance, inferInstance, ProdDG.prodDG PP₁ PP₂, ?_⟩
  -- The combined DG-hom `φ (p, q) = φ₁ p + φ₂ q`.
  refine ⟨{
    toFun := (φ₁.toFun ∘ₗ LinearMap.fst R _ _) + (φ₂.toFun ∘ₗ LinearMap.snd R _ _)
    map_smul' := by
      intro pq a
      change φ₁.toFun ((ProdDG.smulProd PP₁ PP₂ pq a).1)
            + φ₂.toFun ((ProdDG.smulProd PP₁ PP₂ pq a).2)
          = PM.smul (φ₁.toFun pq.1 + φ₂.toFun pq.2) a
      rw [ProdDG.smulProd_apply]
      simp only []
      rw [φ₁.map_smul', φ₂.map_smul', map_add, LinearMap.add_apply]
    map_grade := by
      intro n pq hpq
      obtain ⟨h1, h2⟩ := hpq
      change φ₁.toFun pq.1 + φ₂.toFun pq.2 ∈ PM.grading n
      exact (PM.grading n).add_mem (φ₁.map_grade n pq.1 h1) (φ₂.map_grade n pq.2 h2)
    map_d := by
      intro pq
      change φ₁.toFun ((ProdDG.dProd PP₁ PP₂ pq).1)
            + φ₂.toFun ((ProdDG.dProd PP₁ PP₂ pq).2)
          = PM.d (φ₁.toFun pq.1 + φ₂.toFun pq.2)
      rw [ProdDG.dProd_apply]
      simp only []
      rw [φ₁.map_d, φ₂.map_d, map_add] }, ?_, ?_, ?_⟩
  · -- (1) Surjectivity, from `φ₁`.
    intro m
    obtain ⟨p, hp⟩ := hφ₁surj m
    refine ⟨(p, 0), ?_⟩
    change φ₁.toFun p + φ₂.toFun 0 = m
    rw [map_zero, add_zero, hp]
  · -- (2) Graded surjectivity on cocycles, from `φ₂`.
    intro n m hm
    obtain ⟨x, hxcoc, hxφ⟩ := hφ₂cocyc n m hm
    obtain ⟨hxk, hxg⟩ := hxcoc
    refine ⟨(0, x), ⟨?_, ?_⟩, ?_⟩
    · exact Prod.ext (map_zero PP₁.d) hxk
    · exact ⟨Submodule.zero_mem _, hxg⟩
    · change φ₁.toFun 0 + φ₂.toFun x = m
      rw [map_zero, zero_add, hxφ]
  · -- (3) The admissible SES `0 → P' → P → P'' × P₂ → 0`.
    refine ⟨P', inferInstance, inferInstance, PP',
      P'' × P₂, inferInstance, inferInstance, ProdDG.prodDG PP'' PP₂, hP'dss,
      isDirectSumOfShifts_prodDG hP''dss hP₂dss, ?_⟩
    refine ⟨{
      i := {
        toFun := (LinearMap.inl R P₁ P₂).comp ses₁.i.toFun
        map_smul' := by
          intro p' a
          change (ses₁.i.toFun (PP'.smul p' a), (0 : P₂))
              = ProdDG.smulProd PP₁ PP₂ (ses₁.i.toFun p', 0) a
          rw [ProdDG.smulProd_apply]
          exact Prod.ext (ses₁.i.map_smul' p' a) (by simp)
        map_grade := by
          intro n p' hp'
          exact ⟨ses₁.i.map_grade n p' hp', Submodule.zero_mem _⟩
        map_d := by
          intro p'
          change (ses₁.i.toFun (PP'.d p'), (0 : P₂))
              = ProdDG.dProd PP₁ PP₂ (ses₁.i.toFun p', 0)
          rw [ProdDG.dProd_apply]
          exact Prod.ext (ses₁.i.map_d p') (map_zero PP₂.d).symm }
      p := {
        toFun := (ses₁.p.toFun ∘ₗ LinearMap.fst R _ _).prod (LinearMap.snd R P₁ P₂)
        map_smul' := by
          intro pq a
          change (ses₁.p.toFun (ProdDG.smulProd PP₁ PP₂ pq a).1, (ProdDG.smulProd PP₁ PP₂ pq a).2)
              = ProdDG.smulProd PP'' PP₂ (ses₁.p.toFun pq.1, pq.2) a
          rw [ProdDG.smulProd_apply, ProdDG.smulProd_apply]
          exact Prod.ext (ses₁.p.map_smul' pq.1 a) rfl
        map_grade := by
          intro n pq hpq
          obtain ⟨h1, h2⟩ := hpq
          exact ⟨ses₁.p.map_grade n pq.1 h1, h2⟩
        map_d := by
          intro pq
          change (ses₁.p.toFun (ProdDG.dProd PP₁ PP₂ pq).1, (ProdDG.dProd PP₁ PP₂ pq).2)
              = ProdDG.dProd PP'' PP₂ (ses₁.p.toFun pq.1, pq.2)
          rw [ProdDG.dProd_apply, ProdDG.dProd_apply]
          exact Prod.ext (ses₁.p.map_d pq.1) rfl }
      i_inj := by
        intro p₁' p₂' h
        exact ses₁.i_inj (congrArg Prod.fst h)
      p_surj := by
        rintro ⟨c, b⟩
        obtain ⟨a, ha⟩ := ses₁.p_surj c
        refine ⟨(a, b), ?_⟩
        change (ses₁.p.toFun a, b) = (c, b)
        rw [ha]
      exact := by
        apply Submodule.ext
        rintro ⟨a, b⟩
        constructor
        · rintro ⟨p', hp'⟩
          change (a, b) ∈ LinearMap.ker
            ((ses₁.p.toFun ∘ₗ LinearMap.fst R P₁ P₂).prod (LinearMap.snd R P₁ P₂))
          have ha : (ses₁.i.toFun p', (0 : P₂)) = (a, b) := hp'
          have ha1 : ses₁.i.toFun p' = a := congrArg Prod.fst ha
          have hb1 : (0 : P₂) = b := congrArg Prod.snd ha
          change ((ses₁.p.toFun a, b) : P'' × P₂) = 0
          have hpi : ses₁.p.toFun (ses₁.i.toFun p') = 0 := by
            have hmem : ses₁.i.toFun p' ∈ LinearMap.range ses₁.i.toFun :=
              ⟨p', rfl⟩
            rw [ses₁.exact] at hmem
            exact hmem
          rw [← ha1, hpi, ← hb1]; rfl
        · intro hab
          have hab' : (ses₁.p.toFun a, b) = (0 : P'' × P₂) := hab
          have ha0 : ses₁.p.toFun a = 0 := congrArg Prod.fst hab'
          have hb0 : b = 0 := congrArg Prod.snd hab'
          have hmem : a ∈ LinearMap.ker ses₁.p.toFun := ha0
          rw [← ses₁.exact] at hmem
          obtain ⟨p', hp'⟩ := hmem
          refine ⟨p', ?_⟩
          change ((ses₁.i.toFun p', (0 : P₂)) : P₁ × P₂) = (a, b)
          rw [hp', hb0]
      splitEquiv :=
        (ses₁.splitEquiv.prodCongr (LinearEquiv.refl R P₂)).trans
          (LinearEquiv.prodAssoc R P' P'' P₂)
      splitEquiv_smul := by
        intro pq a
        change ((ses₁.splitEquiv ((ProdDG.smulProd PP₁ PP₂ pq a).1)).1,
              ((ses₁.splitEquiv ((ProdDG.smulProd PP₁ PP₂ pq a).1)).2,
                (ProdDG.smulProd PP₁ PP₂ pq a).2))
            = (PP'.smul ((ses₁.splitEquiv pq.1).1) a,
              ProdDG.smulProd PP'' PP₂
                ((ses₁.splitEquiv pq.1).2, pq.2) a)
        rw [ProdDG.smulProd_apply, ProdDG.smulProd_apply]
        simp only []
        rw [ses₁.splitEquiv_smul]
      splitEquiv_grade := by
        intro n pq hpq
        obtain ⟨h1, h2⟩ := hpq
        obtain ⟨hg1, hg2⟩ := ses₁.splitEquiv_grade n pq.1 h1
        exact ⟨hg1, ⟨hg2, h2⟩⟩
      splitEquiv_symm_grade := by
        intro n k x hk hx
        obtain ⟨x1, x2⟩ := x
        obtain ⟨hx1, hx2⟩ := hx
        change ((ses₁.splitEquiv.symm (k, x1)), x2) ∈ (ProdDG.prodDG PP₁ PP₂).grading n
        exact ⟨ses₁.splitEquiv_symm_grade n k x1 hk hx1, hx2⟩
      splitEquiv_i := by
        intro p'
        change ((ses₁.splitEquiv (ses₁.i.toFun p')).1,
              ((ses₁.splitEquiv (ses₁.i.toFun p')).2, (0 : P₂)))
            = (p', (0, 0))
        rw [ses₁.splitEquiv_i]
      splitEquiv_p := by
        intro pq
        change ((ses₁.splitEquiv pq.1).2, pq.2) = (ses₁.p.toFun pq.1, pq.2)
        rw [ses₁.splitEquiv_p] }⟩

/-! ## Transfer to the bundled differential graded modules

The constructions below preserve carriers and all algebraic data when converting between
the two presentations. The final statement assembles the two covers and presents the
resulting exact sequence using `Stacks.DifferentialGraded.DGModule.AdmissibleSES` and the
`directSum` and `shiftFree` of that presentation.
-/

namespace Native
open MulOpposite
variable {R : Type u} [CommRing R] (A : Stacks.DifferentialGraded.DGAlgebra.{u, v} R)

/-- The two encodings of the differential sign agree for every scalar ring. -/
lemma sign_smul {X : Type*} [AddCommGroup X] [Module R X] (n : ℤ) (x : X) :
    ((-1 : R) ^ n.natAbs) • x = ((-1 : ℤ) ^ n.natAbs) • x := by
  rw [← Int.cast_smul_eq_zsmul R]
  simp

/-- Convert the lawful native algebra to the construction's algebra, without changing
its carrier, grading, multiplication, or differential. -/
noncomputable def algebra (hA : A.IsLawful) : DGAlgebra R A.carrier A.grading where
  isInternal := DirectSum.Decomposition.isInternal A.grading
  d := A.d
  d_grade := hA.d_mem
  d_comp_d := hA.d_comp_d
  leibniz n a ha b := by
    classical
    rw [← DirectSum.sum_support_decompose A.grading b, Finset.mul_sum, map_sum,
      Finset.mul_sum, map_sum, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    simpa only [sign_smul] using hA.leibniz n m a _ ha (DirectSum.decompose A.grading b m).2

variable {A} (M : Stacks.DifferentialGraded.DGModule.{u, w, v} A)

/-- The native grading is closed under the scalar ring, even when that ring has a
larger universe than the algebra. -/
def grading (hM : M.IsLawful) (n : ℤ) : Submodule R M.carrier where
  __ := M.grading n
  smul_mem' r x hx := by
    rw [M.smul_def]
    change op (algebraMap R A.carrier r) • x ∈ M.grading n
    simpa only [add_zero] using
      hM.grading_smul n 0 x _ hx (SetLike.algebraMap_mem_graded A.grading r)

/-- The native right action, viewed as an `R`-bilinear map. -/
def action : M.carrier →ₗ[R] A.carrier →ₗ[R] M.carrier where
  toFun x := {
    toFun := fun a => op a • x
    map_add' := by intros; simp [add_smul]
    map_smul' := by
      intro r a
      simp only [Algebra.smul_def, op_mul, mul_smul, RingHom.id_apply]
      rw [M.smul_def]
      rw [← mul_smul, ← mul_smul]
      congr 1
      exact congrArg op (Algebra.commutes r a) }
  map_add' := by intros; ext; simp [smul_add]
  map_smul' := by
    intro r x
    ext a
    change op a • (r • x) = r • (op a • x)
    rw [M.smul_def, M.smul_def, ← mul_smul, ← mul_smul]
    congr 1
    exact congrArg op (Algebra.commutes r a)

/-- A lawful module of `Stacks.DifferentialGraded`, in the presentation of this file. -/
noncomputable def module (hA : A.IsLawful) (hM : M.IsLawful) :
    DGModule R A.carrier A.grading (algebra A hA) M.carrier where
  smul := action M
  grading := grading M hM
  isInternal := hM.isInternal
  smul_one x := one_smul _ x
  smul_smul x a b := (mul_smul (op b) (op a) x).symm
  smul_grade := hM.grading_smul
  d := M.d
  d_grade := hM.d_mem
  d_comp_d := hM.d_comp_d
  leibniz n x hx a := by
    classical
    change M.d (op a • x) = op a • M.d x +
      ((-1 : R) ^ n.natAbs) • (op (A.d a) • x)
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | homogeneous a =>
        simpa only [sign_smul] using hM.leibniz n _ x a hx a.2
    | add a b ha hb =>
        simp only [op_add, add_smul, map_add, smul_add, ha, hb]
        abel

variable {M}
variable {hA : A.IsLawful}
variable {X : Type w} [AddCommGroup X] [Module R X]

/-- A bilinear right action gives the usual module over the opposite algebra. -/
@[instance_reducible] def moduleOpposite (P : DGModule R A.carrier A.grading (algebra A hA) X) :
    Module A.carrierᵐᵒᵖ X where
  smul a x := P.smul x a.unop
  one_smul := P.smul_one
  mul_smul a b x := (P.smul_smul x b.unop a.unop).symm
  smul_add a x y := by
    change P.smul (x + y) a.unop = P.smul x a.unop + P.smul y a.unop
    simp
  smul_zero a := by
    change P.smul 0 a.unop = 0
    simp
  add_smul a b x := by
    change P.smul x (a.unop + b.unop) = P.smul x a.unop + P.smul x b.unop
    simp
  zero_smul x := by
    change P.smul x 0 = 0
    simp

/-- Convert back to a module of `Stacks.DifferentialGraded` on the same carrier. -/
def ofModule (P : DGModule R A.carrier A.grading (algebra A hA) X) :
    Stacks.DifferentialGraded.DGModule.{u, w, v} A where
  carrier := X
  moduleA := moduleOpposite P
  smul_def r x := by
    change r • x = P.smul x (algebraMap R A.carrier r)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, P.smul_one]
  grading n := (P.grading n).toAddSubgroup
  d := P.d

/-- All DG laws are preserved by the conversion back to the native model. -/
theorem ofModule_isLawful (P : DGModule R A.carrier A.grading (algebra A hA) X) :
    (ofModule P).IsLawful where
  isInternal := P.isInternal
  grading_smul := P.smul_grade
  d_mem := P.d_grade
  d_comp_d := P.d_comp_d
  leibniz n m x a hx ha := by
    change P.d (P.smul x a) = P.smul (P.d x) a +
      ((-1 : ℤ) ^ n.natAbs) • P.smul x (A.d a)
    rw [← sign_smul (R := R)]
    exact P.leibniz n x hx a

/-- Conversion preserves shifts, including the differential sign. -/
theorem ofModule_shift (P : DGModule R A.carrier A.grading (algebra A hA) X) (k : ℤ) :
    ofModule (P.shift k) = (ofModule P).shift k := by
  unfold ofModule DGModule.shift Stacks.DifferentialGraded.DGModule.shift
  congr 1
  ext x
  exact sign_smul k (P.d x)

variable {Y : Type w'} [AddCommGroup Y] [Module R Y]
variable {P : DGModule R A.carrier A.grading (algebra A hA) X}
variable {Q : DGModule R A.carrier A.grading (algebra A hA) Y}

/-- Convert a graded right-linear map to a native graded homomorphism. -/
def ofGradedMap (f : X →ₗ[R] Y)
    (hf : ∀ x a, f (P.smul x a) = Q.smul (f x) a)
    (hg : ∀ n x, x ∈ P.grading n → f x ∈ Q.grading n) :
    Stacks.DifferentialGraded.DGModule.GradedHom (ofModule P) (ofModule Q) where
  toFun := {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun a x => hf x a.unop }
  map_grading := hg

/-- Convert a DG homomorphism, preserving its underlying function exactly. -/
def ofHom (f : DGModule.Hom P Q) :
    Stacks.DifferentialGraded.DGModule.Hom (ofModule P) (ofModule Q) where
  toGradedHom := ofGradedMap f.toFun f.map_smul' f.map_grade
  commute_d := f.map_d

/-- Conversion back after converting a lawful native module changes no data. -/
theorem ofModule_module (M : Stacks.DifferentialGraded.DGModule.{u, w, v} A)
    (hA : A.IsLawful) (hM : M.IsLawful) : ofModule (module M hA hM) = M := by
  cases M
  rfl

/-- A homomorphism into `module M`, as a homomorphism of modules of `Stacks.DifferentialGraded`
into `M`. -/
def toHom (M : Stacks.DifferentialGraded.DGModule.{u, w', v} A) (hM : M.IsLawful)
    (f : DGModule.Hom P (module M hA hM)) : Stacks.DifferentialGraded.DGModule.Hom (ofModule P) M
      where
  toFun := {
    toFun := f.toFun
    map_add' := f.toFun.map_add
    map_smul' := fun a x => f.map_smul' x a.unop }
  map_grading := f.map_grade
  commute_d := f.map_d

/-- Conversion preserves the entire graded splitting, hence native admissibility. -/
theorem ofAdmissibleSES {Z : Type t} [AddCommGroup Z] [Module R Z]
    {T : DGModule R A.carrier A.grading (algebra A hA) Z}
    (s : AdmissibleSES P Q T) : Stacks.DifferentialGraded.DGModule.AdmissibleSES (ofHom s.i) (ofHom
      s.p) where
  injective := s.i_inj
  surjective := s.p_surj
  exact := by
    ext y
    exact SetLike.ext_iff.mp s.exact y
  admissibleMono := by
    refine ⟨s.i_inj, ofGradedMap ((LinearMap.fst R X Z).comp s.splitEquiv.toLinearMap)
      ?_ ?_, ?_⟩
    · intro y a
      exact congrArg Prod.fst (s.splitEquiv_smul y a)
    · intro n y hy
      exact (s.splitEquiv_grade n y hy).1
    · intro x
      exact congrArg Prod.fst (s.splitEquiv_i x)
  admissibleEpi := by
    refine ⟨s.p_surj, ofGradedMap (s.splitEquiv.symm.toLinearMap.comp (LinearMap.inr R X Z))
      ?_ ?_, ?_⟩
    · intro z a
      change s.splitEquiv.symm (0, T.smul z a) = Q.smul (s.splitEquiv.symm (0, z)) a
      apply s.splitEquiv.injective
      rw [s.splitEquiv_smul, s.splitEquiv.apply_symm_apply]
      simp
    · intro n z hz
      exact s.splitEquiv_symm_grade n 0 z (Submodule.zero_mem _) hz
    · intro z
      change s.p.toFun (s.splitEquiv.symm (0, z)) = z
      rw [← s.splitEquiv_p, s.splitEquiv.apply_symm_apply]

/-- A graded surjection is surjective separately in every degree. -/
theorem surjective_degreewise (f : DGModule.Hom P Q) (hf : f.Surjective)
    (n : ℤ) (y : Y) (hy : y ∈ Q.grading n) :
    ∃ x : X, x ∈ P.grading n ∧ f.toFun x = y := by
  classical
  let := P.isInternal.chooseDecomposition
  let := Q.isInternal.chooseDecomposition
  have component (x : X) : f.toFun (DirectSum.decompose P.grading x n) =
      (DirectSum.decompose Q.grading (f.toFun x) n : Y) := by
    induction x using DirectSum.Decomposition.inductionOn P.grading with
    | zero => simp [DirectSum.decompose_zero]
    | @homogeneous i x =>
        by_cases hi : i = n
        · subst i
          rw [DirectSum.decompose_of_mem_same P.grading x.2,
            DirectSum.decompose_of_mem_same Q.grading (f.map_grade n x x.2)]
        · rw [DirectSum.decompose_of_mem_ne P.grading x.2 hi,
            DirectSum.decompose_of_mem_ne Q.grading (f.map_grade i x x.2) hi, map_zero]
    | add x z hx hz =>
        simpa only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
          Submodule.coe_add] using congrArg₂ (· + ·) hx hz
  obtain ⟨x, hx⟩ := hf y
  refine ⟨DirectSum.decompose P.grading x n, (DirectSum.decompose P.grading x n).2, ?_⟩
  rw [component, hx, DirectSum.decompose_of_mem_same Q.grading hy]

/-- The native direct-sum differential acts componentwise. -/
theorem directSum_d_apply {ι : Type t} [DecidableEq ι]
    (N : ι → Stacks.DifferentialGraded.DGModule.{u, w, v} A)
    (x : DirectSum ι (fun i => (N i).carrier)) (j : ι) :
    (Stacks.DifferentialGraded.DGModule.directSumD N x) j = (N j).d (x j) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i a =>
      change (Stacks.DifferentialGraded.DGModule.directSumD N (DirectSum.lof R ι _ i a)) j = _
      rw [Stacks.DifferentialGraded.DGModule.directSumD, DirectSum.toModule_lof]
      change (DirectSum.of (fun i => (N i).carrier) i ((N i).d a)) j =
        (N j).d ((DirectSum.of (fun i => (N i).carrier) i a) j)
      by_cases h : i = j
      · subst j; simp
      · simp [DirectSum.of_eq_of_ne, Ne.symm h]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

/-- A direct sum of shifts in the construction is a direct sum of the `shiftFree` modules of
`Stacks.DifferentialGraded`. Cell indices are lifted only to the maximum of the algebra and cell
universes; the scalar ring never contributes to that bound. -/
theorem ofIsDirectSumOfShifts (h : IsDirectSumOfShifts.{u, v, w, t} P) :
    ∃ (ι : Type (max v t)) (dec : DecidableEq ι) (k : ι → ℤ),
      Nonempty (Stacks.DifferentialGraded.DGModule.Iso (ofModule P)
        (@Stacks.DifferentialGraded.DGModule.directSum _ _ _ ι dec
          (fun i => Stacks.DifferentialGraded.DGModule.shiftFree A (k i)))) := by
  classical
  obtain ⟨ι, k, S, _, _, PS, ⟨e, heact, hegr, hed⟩, f, g, hgf, hfg⟩ := h
  let e₀ : X ≃ₗ[R] S := {
    toLinearMap := f.toFun
    invFun := g.toFun
    left_inv := hgf
    right_inv := hfg }
  let reindex : DirectSum ι (fun _ => A.carrier) ≃ₗ[R]
      DirectSum (ULift.{v} ι) (fun _ => A.carrier) :=
    DirectSum.lequivCongrLeft R Equiv.ulift.symm
  let E := (e₀.trans e).trans reindex
  let N := Stacks.DifferentialGraded.DGModule.directSum
    (fun i : ULift.{v} ι => Stacks.DifferentialGraded.DGModule.shiftFree A (k i.down))
  have E_apply (x : X) (i : ULift.{v} ι) : E x i = e (f.toFun x) i.down := rfl
  have E_smul (a : A.carrierᵐᵒᵖ) (x : (ofModule P).carrier) :
      E (a • x) = a • (E x : N.carrier) := by
    ext i
    change e (f.toFun (P.smul x a.unop)) i.down = _
    rw [f.map_smul', heact]
    rfl
  let Eop : (ofModule P).carrier ≃ₗ[A.carrierᵐᵒᵖ] N.carrier := {
    E.toAddEquiv with map_smul' := E_smul }
  refine ⟨ULift.{v} ι, inferInstance, fun i => k i.down, ⟨{
    toFun := Eop.toLinearMap
    map_grading := ?_
    commute_d := ?_
    invFun := Eop.symm.toLinearMap
    left_inv := Eop.left_inv
    right_inv := Eop.right_inv }⟩⟩
  · intro n x hx i
    exact (hegr n (f.toFun x)).mp (f.map_grade n x hx) i.down
  · intro x
    apply DirectSum.ext
    intro i
    change E (P.d x) i =
      (Stacks.DifferentialGraded.DGModule.directSumD
        (fun i : ULift.{v} ι => Stacks.DifferentialGraded.DGModule.shiftFree A (k i.down)) (E x)) i
    rw [directSum_d_apply]
    change e (f.toFun (P.d x)) i.down =
      ((-1 : ℤ) ^ (k i.down).natAbs) • A.d (E x i)
    rw [f.map_d, hed, sign_smul]
    rfl

end Native

/-- A native DG cover as in Tag 09KN, with the sharp carrier bound needed to iterate
Tag 09KP. It is surjective in every degree and on cocycles in every degree, and its
admissible sequence has both ends isomorphic to native direct sums of shifts.

The scalar ring, algebra, and target module have independent universes `u`, `v`, `w`.
All new carriers and cell indices lie in `Type (max v w)`. -/
theorem exists_native_cover {R : Type u} [CommRing R]
    (A : Stacks.DifferentialGraded.DGAlgebra.{u, v} R) (hA : A.IsLawful)
    (M : Stacks.DifferentialGraded.DGModule.{u, w, v} A) (hM : M.IsLawful) :
    ∃ (P : Stacks.DifferentialGraded.DGModule.{u, max v w, v} A) (_ : P.IsLawful)
      (f : Stacks.DifferentialGraded.DGModule.Hom P M),
      Function.Surjective f.toFun ∧
      (∀ n y, y ∈ M.grading n → ∃ x, x ∈ P.grading n ∧ f.toFun x = y) ∧
      (∀ n y, y ∈ M.grading n → M.d y = 0 →
        ∃ x, x ∈ P.grading n ∧ P.d x = 0 ∧ f.toFun x = y) ∧
      ∃ (P' P'' : Stacks.DifferentialGraded.DGModule.{u, max v w, v} A)
        (_ : P'.IsLawful) (_ : P''.IsLawful)
        (i : Stacks.DifferentialGraded.DGModule.Hom P' P) (p :
          Stacks.DifferentialGraded.DGModule.Hom P P'')
        (ι' ι'' : Type (max v w)) (dec' : DecidableEq ι') (dec'' : DecidableEq ι'')
        (k' : ι' → ℤ) (k'' : ι'' → ℤ)
        (_ : Stacks.DifferentialGraded.DGModule.Iso P'
          (@Stacks.DifferentialGraded.DGModule.directSum _ _ _ ι' dec'
          (fun j => Stacks.DifferentialGraded.DGModule.shiftFree A (k' j))))
        (_ : Stacks.DifferentialGraded.DGModule.Iso P''
          (@Stacks.DifferentialGraded.DGModule.directSum _ _ _ ι'' dec''
          (fun j => Stacks.DifferentialGraded.DGModule.shiftFree A (k'' j)))),
        Stacks.DifferentialGraded.DGModule.AdmissibleSES i p := by
  obtain ⟨P, _, _, PP, f, hf, hc, P', _, _, PP', P'', _, _, PP'', hP', hP'', ⟨s⟩⟩ :=
    cover_combine (Native.algebra A hA) (Native.module M hA hM)
      (exists_surjective_cover (Native.algebra A hA) (Native.module M hA hM))
      (exists_cocycle_cover (Native.algebra A hA) (Native.module M hA hM))
  obtain ⟨ι', dec', k', ⟨e'⟩⟩ := Native.ofIsDirectSumOfShifts hP'
  obtain ⟨ι'', dec'', k'', ⟨e''⟩⟩ := Native.ofIsDirectSumOfShifts hP''
  refine ⟨Native.ofModule PP, Native.ofModule_isLawful PP, Native.toHom M hM f,
    hf, ?_, ?_, Native.ofModule PP', Native.ofModule PP'',
    Native.ofModule_isLawful PP', Native.ofModule_isLawful PP'', Native.ofHom s.i,
    Native.ofHom s.p, ι', ι'', dec', dec'', k', k'', e', e'', Native.ofAdmissibleSES s⟩
  · intro n y hy
    exact Native.surjective_degreewise f hf n y hy
  · intro n y hy hd
    obtain ⟨x, ⟨hxd, hxg⟩, hfx⟩ := hc n y ⟨hd, hy⟩
    exact ⟨x, hxg, hxd, hfx⟩

/-- **Theorem (Stacks Project, Tag 09KN, Lemma 22.20.3).**

Let `(A, d)` be a differential graded algebra over `R` and `M` a differential
graded `A`-module.  Then there exists a differential graded `A`-module `P` and a
homomorphism `φ : P → M` of differential graded `A`-modules such that:
1. `φ` is surjective;
2. the induced map on cocycles `Ker(d_P) → Ker(d_M)` is graded surjective, i.e.
   every degree-`n` cocycle of `M` is the image of a degree-`n` cocycle of `P`;
   and
3. `P` sits in an admissible short exact sequence `0 → P' → P → P'' → 0` of
   differential graded `A`-modules where both `P'` and `P''` are isomorphic to
   direct sums of shifts of `A`.

All objects live in a common universe `Type u`. -/
@[stacks 09KN]
theorem exists_dgModule_surjective_cover
    {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] (dA : DGAlgebra R A 𝒜)
    {M : Type u} [AddCommGroup M] [Module R M] (PM : DGModule R A 𝒜 dA M) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P)
      (PP : DGModule R A 𝒜 dA P) (φ : DGModule.Hom PP PM),
      -- (1) φ is surjective
      φ.Surjective ∧
      -- (2) the induced map on cocycles is graded surjective
      φ.GradedSurjectiveOnCocycles ∧
      -- (3) P sits in an admissible SES with both ends direct sums of shifts of A
      (∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module R P')
        (PP' : DGModule R A 𝒜 dA P')
        (P'' : Type u) (_ : AddCommGroup P'') (_ : Module R P'')
        (PP'' : DGModule R A 𝒜 dA P''),
        -- the shift index types live in `Type u` as well, which is what the
        -- single-universe reading of Tag 09KN asserts
        IsDirectSumOfShifts.{u, u, u, u} PP' ∧ IsDirectSumOfShifts.{u, u, u, u} PP'' ∧
        Nonempty (AdmissibleSES PP' PP PP'')) := by
  -- Assemble the surjective cover (properties (1), (3)) and the cocycle cover
  -- (property (2)) via `cover_combine`.
  exact cover_combine dA PM
    (exists_surjective_cover dA PM)
    (exists_cocycle_cover dA PM)

end DifferentialGraded.NativeCover

end
