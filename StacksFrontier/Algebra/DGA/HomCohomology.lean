module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.GradedAlgebra.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Stacks.DifferentialGraded.HomComplex

/-
# Problem Description

Throughout we fix a commutative ring `R` (with `1`) and a differential graded
algebra `(A, d)` over `R`.  We formalize the following notions from the Stacks
project (Section 22.4, tags 09JH-09JL, 09JN-09JQ):

* a differential graded `R`-algebra `(A, d)`;
* a right differential graded `A`-module `M` and homomorphisms between such;
* `A` regarded as a module over itself, and the `k`-shift `M[k]`;
* homotopies between homomorphisms and the homotopy category;
* the cohomology `H^n(M)` of the underlying cochain complex of `R`-modules.

The two main statements (Stacks Tag 09K1) are the natural isomorphisms
  `Hom_{Mod_{(A,d)}}(A[k], M) ≃ ker(d_M : M^{-k} → M^{-k+1})`,
  `Hom_{K(Mod_{(A,d)})}(A[k], M) ≃ H^{-k}(M)`,
both induced by `f ↦ f(1)`, and both `R`-linear and natural in `M`.

## Modelling choices

* A `ℤ`-grading on an `R`-module `N` is modelled by a family of `R`-submodules
  `grading : ℤ → Submodule R N` together with a `DirectSum.Decomposition`
  instance, exactly as Mathlib models graded algebras (`GradedAlgebra`).
* The right `A`-action on a module `M` is modelled as a left module structure
  over the opposite ring `A.carrierᵐᵒᵖ`.  We write `M.act x a` (`= op a • x`)
  for the right action of `a` on `x`.  Compatibility of the `R`- and `A`-actions
  is required in BOTH variables, via `IsScalarTower R A.carrierᵐᵒᵖ M.carrier`
  (linearity of `a ↦ x • a`) and `SMulCommClass R A.carrierᵐᵒᵖ M.carrier`
  (linearity of `x ↦ x • a`).  This guarantees that the inverse map
  `m ↦ (a ↦ m a)` of Statement 1 is `R`-linear, as required mathematically.
* The Koszul signs `(-1)^n`, `n : ℤ`, are modelled by `Int.negOnePow n : ℤˣ`
  acting on the relevant abelian group.
* `Hom M N` is the `R`-submodule of `R`-linear maps satisfying the morphism
  conditions, so it carries a canonical `R`-module structure.  The hom-set of
  the homotopy category is the quotient `R`-module `Hom M N ⧸ nullHomotopic`,
  where `nullHomotopic` is the `R`-submodule of null-homotopic morphisms; this
  quotient is exactly the quotient by the (additive/`R`-linear) homotopy
  equivalence relation.
-/

open scoped DirectSum

/-! ## Infrastructure: reindexing a `DirectSum.Decomposition` along a shift. -/

/-- Coercion commutes with transport along an index equality. -/
theorem coe_eqRec_submodule {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (𝒜 : ℤ → Submodule R M) {a b : ℤ} (h : a = b) (x : ↥(𝒜 a)) :
    (↑(h ▸ x : ↥(𝒜 b)) : M) = ↑x := by subst h; rfl

/-- The action of `DirectSum.equivCongrLeft (Equiv.subRight k)` on a generator
`DirectSum.of i x`. -/
theorem equivCongrLeft_subRight_of {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (𝒜 : ℤ → Submodule R M) (k i : ℤ) (x : ↥(𝒜 i)) :
    (DirectSum.equivCongrLeft (Equiv.subRight k)) ((DirectSum.of (fun i => ↥(𝒜 i)) i) x)
      = DirectSum.of (fun n => ↥(𝒜 (n + k))) (i - k)
          (⟨x.1, by rw [show i - k + k = i from by ring]; exact x.2⟩) := by
  apply DFinsupp.ext
  intro j
  rw [DirectSum.equivCongrLeft_apply]
  apply Subtype.ext
  have hs : (Equiv.subRight k).symm j = j + k := rfl
  rw [DirectSum.coe_of_apply (i := i) (j := (Equiv.subRight k).symm j) (x := x)]
  by_cases hj : i - k = j
  · subst hj
    rw [ite_eq_left (show i = (Equiv.subRight k).symm (i - k) by rw [hs]; ring)]
    exact (DirectSum.coe_of_apply (A := fun n => 𝒜 (n + k)) (i - k) (i - k) _).trans
      (by rw [ite_eq_left rfl]) |>.symm
  · rw [ite_eq_right (show ¬ i = (Equiv.subRight k).symm j by rw [hs]; omega)]
    refine ((DirectSum.coe_of_apply (A := fun n => 𝒜 (n + k)) (i - k) j _).trans
      (by rw [ite_eq_right hj]; simp)).symm

/-- The reindexing equivalence is compatible with the coercion to `M`
(commuting square at the level of `AddMonoidHom`s). -/
theorem coeAddMonoidHom_equivCongrLeft {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (𝒜 : ℤ → Submodule R M) (k : ℤ) :
    (DirectSum.coeAddMonoidHom (fun n => 𝒜 (n + k))).comp
        (DirectSum.equivCongrLeft (Equiv.subRight k)).toAddMonoidHom
      = DirectSum.coeAddMonoidHom 𝒜 := by
  apply DirectSum.addHom_ext
  intro i x
  calc (DirectSum.coeAddMonoidHom (fun n => 𝒜 (n + k)))
        ((DirectSum.equivCongrLeft (Equiv.subRight k)).toAddMonoidHom
          ((DirectSum.of (fun i => ↥(𝒜 i)) i) x))
      = (DirectSum.coeAddMonoidHom (fun n => 𝒜 (n + k)))
          (DirectSum.of (fun n => ↥(𝒜 (n + k))) (i - k)
            (⟨x.1, by rw [show i - k + k = i from by ring]; exact x.2⟩)) :=
        congrArg _ (equivCongrLeft_subRight_of 𝒜 k i x)
    _ = x := by rw [DirectSum.coeAddMonoidHom_of]
    _ = (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.of (fun i => ↥(𝒜 i)) i) x) := by
        rw [DirectSum.coeAddMonoidHom_of]

/-- Pointwise version of the commuting square. -/
theorem coeAddMonoidHom_equivCongrLeft_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R
    M]
    (𝒜 : ℤ → Submodule R M) (k : ℤ) (y : ⨁ i, ↥(𝒜 i)) :
    (DirectSum.coeAddMonoidHom (fun n => 𝒜 (n + k)))
        ((DirectSum.equivCongrLeft (Equiv.subRight k)) y)
      = (DirectSum.coeAddMonoidHom 𝒜) y :=
  DFunLike.congr_fun (coeAddMonoidHom_equivCongrLeft 𝒜 k) y

/-- `DirectSum.decompose` is a left inverse to the coercion map. -/
theorem decompose_coeAddMonoidHom {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (𝒜 : ℤ → Submodule R M) [DirectSum.Decomposition 𝒜] (z : ⨁ i, ↥(𝒜 i)) :
    (DirectSum.decompose 𝒜) ((DirectSum.coeAddMonoidHom 𝒜) z) = z := by
  have h1 : (DirectSum.coeAddMonoidHom 𝒜) z = (DirectSum.decomposeAddEquiv 𝒜).symm z := rfl
  rw [h1, show DirectSum.decompose 𝒜 = (DirectSum.decomposeAddEquiv 𝒜).toEquiv from rfl]
  simp

/-- Reindex a `ℤ`-grading decomposition along the shift `n ↦ n + k`. -/
@[reducible]
noncomputable def decompositionShift {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (𝒜 : ℤ → Submodule R M) [h : DirectSum.Decomposition 𝒜] (k : ℤ) :
    DirectSum.Decomposition (fun n => 𝒜 (n + k)) :=
  DirectSum.Decomposition.mk
    (decompose' := fun x => (DirectSum.equivCongrLeft (Equiv.subRight k)) (DirectSum.decompose 𝒜 x))
    (by
      intro x
      change (DirectSum.coeAddMonoidHom (fun n => 𝒜 (n + k)))
          ((DirectSum.equivCongrLeft (Equiv.subRight k)) (DirectSum.decompose 𝒜 x)) = x
      rw [coeAddMonoidHom_equivCongrLeft_apply]
      exact h.left_inv x)
    (by
      intro y
      change (DirectSum.equivCongrLeft (Equiv.subRight k))
          (DirectSum.decompose 𝒜 ((DirectSum.coeAddMonoidHom (fun n => 𝒜 (n + k))) y)) = y
      have hcoe : (DirectSum.coeAddMonoidHom (fun n => 𝒜 (n + k))) y
          = (DirectSum.coeAddMonoidHom 𝒜) ((DirectSum.equivCongrLeft (Equiv.subRight k)).symm
              y) := by
        rw [← coeAddMonoidHom_equivCongrLeft_apply 𝒜 k
              ((DirectSum.equivCongrLeft (Equiv.subRight k)).symm y),
            AddEquiv.apply_symm_apply]
      rw [hcoe, decompose_coeAddMonoidHom, AddEquiv.apply_symm_apply])

/-! ## Main Definition 1: differential graded algebra. -/

variable (R : Type*) [CommRing R]

/-- A *differential graded `R`-algebra* `(A, d)`: an associative unital
`R`-algebra with a `ℤ`-grading `A = ⊕ Aⁿ` by `R`-submodules (`GradedAlgebra`),
together with an `R`-linear differential `d` raising degree by `1`, squaring to
zero, and satisfying the graded Leibniz rule
`d (a b) = d a * b + (-1)ⁿ a * d b` for `a ∈ Aⁿ`. -/
structure DGA where
  /-- The underlying carrier type. -/
  carrier : Type*
  [ring : Ring carrier]
  [algebra : Algebra R carrier]
  /-- The `ℤ`-grading by `R`-submodules. -/
  grading : ℤ → Submodule R carrier
  [gradedAlgebra : GradedAlgebra grading]
  /-- The differential. -/
  d : carrier →ₗ[R] carrier
  /-- The differential raises degree by one. -/
  d_mem : ∀ (n : ℤ) (a : carrier), a ∈ grading n → d a ∈ grading (n + 1)
  /-- The differential squares to zero. -/
  d_d : ∀ a, d (d a) = 0
  /-- The graded Leibniz rule. -/
  leibniz : ∀ (n : ℤ) (a : carrier), a ∈ grading n → ∀ b : carrier,
      d (a * b) = d a * b + n.negOnePow • (a * d b)

attribute [instance] DGA.ring DGA.algebra DGA.gradedAlgebra

variable {R}

/-! ## Main Definition 2: right differential graded modules. -/

/-- A *right differential graded module* `M` over a DGA `A`: a graded right
`A`-module (modelled as a left module over `A.carrierᵐᵒᵖ`) with an `R`-linear
differential raising degree by one, squaring to zero, and satisfying the graded
Leibniz rule `d (x a) = d x * a + (-1)ⁿ x * d a` for `x ∈ Mⁿ`.

The `R`-compatibility of the right `A`-action is encoded by the scalar-tower and
commuting-class instances, which make `a ↦ x • a` and `x ↦ x • a` both
`R`-linear. -/
structure DGModule (A : DGA R) where
  /-- The underlying carrier type. -/
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [moduleR : Module R carrier]
  /-- The right `A`-action, encoded as a left module over `A.carrierᵐᵒᵖ`. -/
  [moduleA : Module A.carrierᵐᵒᵖ carrier]
  /-- `R`-linearity of the action in the algebra variable (`a ↦ x • a`). -/
  [isScalarTower : IsScalarTower R A.carrierᵐᵒᵖ carrier]
  /-- `R`-linearity of the action in the module variable (`x ↦ x • a`). -/
  [smulCommClass : SMulCommClass R A.carrierᵐᵒᵖ carrier]
  /-- The `ℤ`-grading by `R`-submodules. -/
  grading : ℤ → Submodule R carrier
  [decomposition : DirectSum.Decomposition grading]
  /-- The graded right-module condition `Mⁿ Aᵐ ⊂ Mⁿ⁺ᵐ`. -/
  smul_mem : ∀ (n m : ℤ) (x : carrier) (a : A.carrier),
      x ∈ grading n → a ∈ A.grading m → MulOpposite.op a • x ∈ grading (n + m)
  /-- The differential. -/
  d : carrier →ₗ[R] carrier
  /-- The differential raises degree by one. -/
  d_mem : ∀ (n : ℤ) (x : carrier), x ∈ grading n → d x ∈ grading (n + 1)
  /-- The differential squares to zero. -/
  d_d : ∀ x, d (d x) = 0
  /-- The graded Leibniz rule. -/
  leibniz : ∀ (n : ℤ) (x : carrier), x ∈ grading n → ∀ a : A.carrier,
      d (MulOpposite.op a • x)
        = MulOpposite.op a • d x + n.negOnePow • (MulOpposite.op (A.d a) • x)

attribute [instance] DGModule.addCommGroup DGModule.moduleR DGModule.moduleA
  DGModule.isScalarTower DGModule.smulCommClass DGModule.decomposition

namespace DGModule

variable {A : DGA R}

/-- The right action of `a : A` on `x : M`, written via the opposite-ring smul. -/
def act (M : DGModule A) (x : M.carrier) (a : A.carrier) : M.carrier :=
  MulOpposite.op a • x

/-- `R`-linearity of the right action in the algebra variable. -/
theorem act_smul_left (M : DGModule A) (r : R) (a : A.carrier) (x : M.carrier) :
    M.act x (r • a) = r • M.act x a := by
  unfold act; rw [MulOpposite.op_smul, smul_assoc]

/-- `R`-linearity of the right action in the module variable. -/
theorem act_smul_right (M : DGModule A) (r : R) (a : A.carrier) (x : M.carrier) :
    M.act (r • x) a = r • M.act x a := by
  unfold act; rw [smul_comm]

/-- The `R`-submodule of `R`-linear maps `M → N` that are right `A`-linear,
grading-preserving and commute with the differentials.  This is the hom-set
`Hom_{Mod_{(A,d)}}(M, N)` and carries a natural `R`-module structure. -/
def homSubmodule (M N : DGModule A) : Submodule R (M.carrier →ₗ[R] N.carrier) where
  carrier := {φ | (∀ (x : M.carrier) (a : A.carrier), φ (M.act x a) = N.act (φ x) a)
                ∧ (∀ (n : ℤ) (x : M.carrier), x ∈ M.grading n → φ x ∈ N.grading n)
                ∧ (∀ x, φ (M.d x) = N.d (φ x))}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x a; simp only [LinearMap.add_apply, h1, g1, act] at *; rw [smul_add]
    · intro n x hx; exact Submodule.add_mem _ (h2 n x hx) (g2 n x hx)
    · intro x; simp only [LinearMap.add_apply, h3, g3]; rw [map_add]
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro x a; simp [act]
    · intro n x _; simp
    · intro x; simp
  smul_mem' := by
    rintro r φ ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x a; simp only [LinearMap.smul_apply, h1, act] at *; rw [smul_comm]
    · intro n x hx; exact Submodule.smul_mem _ r (h2 n x hx)
    · intro x; simp only [LinearMap.smul_apply, h3]; rw [map_smul]

/-- A *homomorphism of differential graded `A`-modules* `M → N`.  As the
underlying type is `↥(homSubmodule M N)`, the hom-set `Hom M N` is an
`R`-module (in particular an abelian group). -/
abbrev Hom (M N : DGModule A) : Type _ := ↥(homSubmodule M N)

/-- The underlying `R`-linear map of a morphism. -/
def Hom.toFun {M N : DGModule A} (f : Hom M N) : M.carrier →ₗ[R] N.carrier := f.1

/-- A morphism commutes with the right action of `A`. -/
theorem Hom.map_act {M N : DGModule A} (f : Hom M N) (x : M.carrier) (a : A.carrier) :
    f.toFun (M.act x a) = N.act (f.toFun x) a := f.2.1 x a
/-- A morphism preserves the grading. -/
theorem Hom.map_grading {M N : DGModule A} (f : Hom M N) (n : ℤ) (x : M.carrier)
    (hx : x ∈ M.grading n) : f.toFun x ∈ N.grading n := f.2.2.1 n x hx
/-- A morphism commutes with the differentials. -/
theorem Hom.map_d {M N : DGModule A} (f : Hom M N) (x : M.carrier) :
    f.toFun (M.d x) = N.d (f.toFun x) := f.2.2.2 x

/-- Two morphisms with the same underlying function are equal. -/
@[ext] theorem Hom.ext {M N : DGModule A} {f g : Hom M N}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  apply Subtype.ext; ext x; exact h x

/-- The value `f.toFun` of the sum of two morphisms. -/
theorem Hom.add_toFun {M N : DGModule A} (f g : Hom M N) :
    (f + g).toFun = f.toFun + g.toFun := rfl

/-- The underlying linear map of the zero morphism. -/
theorem Hom.zero_toFun {M N : DGModule A} :
    (0 : Hom M N).toFun = 0 := rfl

/-- The underlying linear map of an `R`-scaled morphism. -/
theorem Hom.smul_toFun {M N : DGModule A} (r : R) (f : Hom M N) :
    (r • f).toFun = r • f.toFun := rfl

/-- The underlying linear map of the difference of two morphisms. -/
theorem Hom.sub_toFun {M N : DGModule A} (f g : Hom M N) :
    (f - g).toFun = f.toFun - g.toFun := rfl

/-- Composition of morphisms (functoriality, used to express naturality). -/
def Hom.comp {M N P : DGModule A} (g : Hom N P) (f : Hom M N) : Hom M P :=
  ⟨g.toFun.comp f.toFun, by
    refine ⟨?_, ?_, ?_⟩
    · intro x a
      simp only [LinearMap.comp_apply]
      rw [show f.toFun (M.act x a) = N.act (f.toFun x) a from f.map_act x a,
          show g.toFun (N.act (f.toFun x) a) = P.act (g.toFun (f.toFun x)) a from
            g.map_act (f.toFun x) a]
    · intro n x hx
      simp only [LinearMap.comp_apply]
      exact g.map_grading n _ (f.map_grading n x hx)
    · intro x
      simp only [LinearMap.comp_apply]
      rw [f.map_d x, g.map_d (f.toFun x)]⟩

/-- The underlying map of `g.comp f` sends `x` to `g (f x)`. -/
@[simp] theorem Hom.comp_toFun {M N P : DGModule A} (g : Hom N P) (f : Hom M N) (x : M.carrier) :
    (g.comp f).toFun x = g.toFun (f.toFun x) := rfl

end DGModule

/-! ## Main Definition 3: `A` as a module over itself, and the shift `M[k]`. -/

/-- The DGA `A` viewed as a right differential graded module over itself, via
right multiplication and the differential `d`. -/
def DGA.toDGModule (A : DGA R) : DGModule A where
  carrier := A.carrier
  grading := A.grading
  smul_mem := fun n m x a hx ha => by
    rw [op_smul_eq_mul]; exact SetLike.mul_mem_graded hx ha
  d := A.d
  d_mem := A.d_mem
  d_d := A.d_d
  leibniz := fun n x hx a => by
    rw [op_smul_eq_mul, op_smul_eq_mul, op_smul_eq_mul]
    exact A.leibniz n x hx a

namespace DGModule

variable {A : DGA R}

/-- The right `A`-action commutes with the integer-sign `ℤˣ`-action. -/
theorem units_smul_act_comm (M : DGModule A) (u : ℤˣ) (a : A.carrier) (y : M.carrier) :
    u • (MulOpposite.op a • y) = MulOpposite.op a • (u • y) := by
  rw [Units.smul_def, Units.smul_def]
  exact (map_zsmul (DistribSMul.toAddMonoidHom M.carrier (MulOpposite.op a)) (u : ℤ) y).symm

/-- The `k`-shifted module `M[k]`: same underlying module and right `A`-action,
with `M[k]ⁿ = Mⁿ⁺ᵏ`, differential `d_{M[k]} = (-1)ᵏ d_M`. -/
noncomputable def shift (M : DGModule A) (k : ℤ) : DGModule A where
  carrier := M.carrier
  grading := fun n => M.grading (n + k)
  decomposition := decompositionShift M.grading k
  smul_mem := fun n m x a hx ha => by
    have : n + k + m = n + m + k := by ring
    rw [← this]; exact M.smul_mem (n + k) m x a hx ha
  d := k.negOnePow • M.d
  d_mem := fun n x hx => by
    have hmem : M.d x ∈ M.grading (n + k + 1) := M.d_mem (n + k) x hx
    have heq : n + k + 1 = n + 1 + k := by ring
    rw [heq] at hmem
    change (k.negOnePow • M.d) x ∈ M.grading (n + 1 + k)
    rw [LinearMap.smul_apply, Units.smul_def]
    exact zsmul_mem hmem _
  d_d := fun x => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower, M.d_d, smul_zero,
      smul_zero]
  leibniz := fun n x hx a => by
    have hlb := M.leibniz (n + k) x hx a
    simp only [LinearMap.smul_apply]
    rw [hlb, smul_add]
    congr 1
    · change k.negOnePow • (MulOpposite.op a • M.d x)
          = MulOpposite.op a • (k.negOnePow • M.d x)
      exact M.units_smul_act_comm k.negOnePow a (M.d x)
    · rw [smul_smul]
      congr 1
      rw [Int.negOnePow_add, mul_comm, mul_assoc, Int.units_mul_self, mul_one]

end DGModule

/-! ## Main Definition 4: homotopies, null-homotopic morphisms, and the
homotopy category. -/

namespace DGModule

variable {A : DGA R}

/-- The full right-`A`-linearity of the null-homotopy map `x ↦ d_N (h x) +
h (d_M x)` for any degree-`(-1)`, right-`A`-linear `R`-map `h`.  (This is the
key computation behind: a homotopy operator induces a morphism of differential
graded `A`-modules.) -/
theorem nullhomotopy_act (M N : DGModule A) (h : M.carrier →ₗ[R] N.carrier)
    (hact : ∀ (x : M.carrier) (a : A.carrier), h (M.act x a) = N.act (h x) a)
    (hgr : ∀ (n : ℤ) (x : M.carrier), x ∈ M.grading n → h x ∈ N.grading (n - 1))
    (x : M.carrier) (a : A.carrier) :
    (N.d (h (M.act x a)) + h (M.d (M.act x a)))
      = N.act (N.d (h x) + h (M.d x)) a := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp [act]
  | add x y hx hy =>
      have hadd : M.act (x + y) a = M.act x a + M.act y a := by simp [act, smul_add]
      rw [hadd]
      simp only [map_add]
      have hRHS : N.act (N.d (h x) + N.d (h y) + (h (M.d x) + h (M.d y))) a
          = N.act (N.d (h x) + h (M.d x)) a + N.act (N.d (h y) + h (M.d y)) a := by
        simp only [act]; rw [← smul_add]; congr 1; abel
      rw [hRHS, ← hx, ← hy]; abel
  | homogeneous m =>
      obtain ⟨mv, hmv⟩ := m
      rename_i i
      simp only at *
      have hx : mv ∈ M.grading i := hmv
      have hdx : M.d (M.act mv a) = M.act (M.d mv) a + i.negOnePow • M.act mv (A.d a) :=
        M.leibniz i mv hx a
      have hhx : h mv ∈ N.grading (i - 1) := hgr i mv hx
      have hdN : N.d (N.act (h mv) a) = N.act (N.d (h mv)) a + (i-1).negOnePow • N.act (h mv) (A.d
          a) :=
        N.leibniz (i-1) (h mv) hhx a
      rw [hact mv a, hdN, hdx, map_add, LinearMap.map_smul_of_tower, hact (M.d mv) a, hact mv (A.d
          a)]
      have hsplit : N.act (N.d (h mv) + h (M.d mv)) a
          = N.act (N.d (h mv)) a + N.act (h (M.d mv)) a := by
        simp only [act]; rw [smul_add]
      rw [hsplit]
      have hcancel : (i-1).negOnePow • (N.act (h mv) (A.d a)) + i.negOnePow • (N.act (h mv) (A.d
          a)) = 0 := by
        have : (i -
            1).negOnePow = - i.negOnePow := by rw [Int.negOnePow_sub]; simp [Int.negOnePow_one]
        rw [this]; simp
      rw [add_assoc]
      rw [show (i-1).negOnePow • N.act (h mv) (A.d a) + (N.act (h (M.d mv)) a + i.negOnePow • N.act
          (h mv) (A.d a))
            = N.act (h (M.d mv)) a + ((i-1).negOnePow • N.act (h mv) (A.d a) + i.negOnePow • N.act
                (h mv) (A.d a)) from by abel]
      rw [hcancel, add_zero]

/-- A *homotopy* between two homomorphisms `f, g : M → N`: a right `A`-linear,
`R`-linear map `h` of degree `-1` (i.e. `h (Mⁿ) ⊆ Nⁿ⁻¹`) with
`f x - g x = d_N (h x) + h (d_M x)`. -/
structure Homotopy {M N : DGModule A} (f g : Hom M N) where
  /-- The underlying degree `-1` `R`-linear map. -/
  toFun : M.carrier →ₗ[R] N.carrier
  /-- Right `A`-linearity of the homotopy. -/
  map_act : ∀ (x : M.carrier) (a : A.carrier), toFun (M.act x a) = N.act (toFun x) a
  /-- The homotopy lowers degree by one. -/
  map_grading : ∀ (n : ℤ) (x : M.carrier), x ∈ M.grading n → toFun x ∈ N.grading (n - 1)
  /-- The homotopy relation `f - g = d_N h + h d_M`. -/
  homotopy : ∀ x, f.toFun x - g.toFun x = N.d (toFun x) + toFun (M.d x)

/-- The `R`-submodule of *null-homotopic* morphisms `M → N` (those homotopic to
the zero morphism). -/
def nullHomotopic (M N : DGModule A) : Submodule R (Hom M N) where
  carrier := {f | ∃ h : M.carrier →ₗ[R] N.carrier,
                (∀ (x : M.carrier) (a : A.carrier), h (M.act x a) = N.act (h x) a)
              ∧ (∀ (n : ℤ) (x : M.carrier), x ∈ M.grading n → h x ∈ N.grading (n - 1))
              ∧ (∀ x, f.toFun x = N.d (h x) + h (M.d x))}
  add_mem' := by
    rintro f g ⟨hf, hfa, hfg, hfh⟩ ⟨hg, hga, hgg, hgh⟩
    refine ⟨hf + hg, ?_, ?_, ?_⟩
    · intro x a
      rw [show (hf + hg) (M.act x a) = hf (M.act x a) + hg (M.act x a) from rfl, hfa, hga,
          show (hf + hg) x = hf x + hg x from rfl]
      simp only [act]; rw [smul_add]
    · intro n x hx; exact Submodule.add_mem _ (hfg n x hx) (hgg n x hx)
    · intro x
      rw [Hom.add_toFun, LinearMap.add_apply, hfh, hgh]
      simp only [LinearMap.add_apply, map_add]; abel
  zero_mem' := by
    refine ⟨0, ?_, ?_, ?_⟩
    · intro x a; simp [act]
    · intro n x _; simp
    · intro x; rw [Hom.zero_toFun]; simp
  smul_mem' := by
    rintro r f ⟨hf, hfa, hfg, hfh⟩
    refine ⟨r • hf, ?_, ?_, ?_⟩
    · intro x a
      rw [show (r • hf) (M.act x a) = r • hf (M.act x a) from rfl, hfa,
          show (r • hf) x = r • hf x from rfl]
      simp only [act]; rw [smul_comm]
    · intro n x hx; exact Submodule.smul_mem _ r (hfg n x hx)
    · intro x
      rw [Hom.smul_toFun, LinearMap.smul_apply, hfh]
      simp only [LinearMap.smul_apply, map_smul, smul_add]

/-- Two homomorphisms are *homotopic* iff their difference is null-homotopic
(equivalently, iff there exists a `Homotopy` between them).  As `nullHomotopic`
is a submodule, this is an additive/`R`-linear congruence; we package it as a
`Setoid` below. -/
def Homotopic {M N : DGModule A} (f g : Hom M N) : Prop :=
  f - g ∈ nullHomotopic M N

/-- `Homotopic` is the `Setoid` given by the submodule `nullHomotopic`; this is
an equivalence relation, compatible with the additive/`R`-module structure
(Stacks 22.4, tag 09JS). -/
instance homotopicSetoid (M N : DGModule A) : Setoid (Hom M N) :=
  QuotientAddGroup.leftRel (nullHomotopic M N).toAddSubgroup

/-- `f ≈ g` holds if and only if `-f + g` is null-homotopic. -/
theorem homotopic_iff {M N : DGModule A} (f g : Hom M N) :
    f ≈ g ↔ -f + g ∈ nullHomotopic M N :=
  QuotientAddGroup.leftRel_apply

/-- The hom-set of the homotopy category `K(Mod_{(A,d)})`: homotopy classes of
homomorphisms `M → N`.  This is the quotient `R`-module `Hom M N ⧸
nullHomotopic`, i.e. `Hom M N` modulo the homotopy equivalence relation; it is
canonically an `R`-module (in particular an abelian group). -/
abbrev HomotopyClass (M N : DGModule A) : Type _ := Hom M N ⧸ nullHomotopic M N

end DGModule

/-! ## Cohomology of a differential graded module. -/

namespace DGModule

variable {A : DGA R}

/-- The submodule of degree-`n` cocycles `Zⁿ(M) = ker(d_M) ∩ Mⁿ`. -/
noncomputable def cocyclesM (M : DGModule A) (n : ℤ) : Submodule R M.carrier :=
  M.grading n ⊓ LinearMap.ker M.d

/-- The submodule of degree-`n` coboundaries `Bⁿ(M) = d_M (Mⁿ⁻¹)`. -/
noncomputable def coboundariesM (M : DGModule A) (n : ℤ) : Submodule R M.carrier :=
  Submodule.map M.d (M.grading (n - 1))

/-- The coboundaries are contained in the cocycles. -/
theorem coboundariesM_le_cocyclesM (M : DGModule A) (n : ℤ) :
    M.coboundariesM n ≤ M.cocyclesM n := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨?_, ?_⟩
  · have := M.d_mem (n - 1) y hy
    rwa [show n - 1 + 1 = n from by ring] at this
  · simp [LinearMap.mem_ker, M.d_d]

/-- The *cohomology* `Hⁿ(M) = Zⁿ(M) / Bⁿ(M)` of the underlying cochain complex
of `R`-modules.  It is canonically an `R`-module. -/
noncomputable def cohomology (M : DGModule A) (n : ℤ) : Type _ :=
  (M.cocyclesM n) ⧸ (Submodule.comap (M.cocyclesM n).subtype (M.coboundariesM n))

/-- The abelian group structure on the cohomology `Hⁿ(M)`. -/
noncomputable instance (M : DGModule A) (n : ℤ) : AddCommGroup (M.cohomology n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

/-- The `R`-module structure on the cohomology `Hⁿ(M)`. -/
noncomputable instance (M : DGModule A) (n : ℤ) : Module R (M.cohomology n) :=
  inferInstanceAs (Module R (_ ⧸ _))

/-- The `R`-linear map on cocycles induced by a morphism `g : M → N`
(used to express naturality). -/
noncomputable def cocyclesMap {M N : DGModule A} (g : Hom M N) (n : ℤ) :
    M.cocyclesM n →ₗ[R] N.cocyclesM n :=
  LinearMap.restrict g.toFun (fun x hx => by
    obtain ⟨hgr, hker⟩ := hx
    refine ⟨g.map_grading n x hgr, ?_⟩
    have hx0 : M.d x = 0 := hker
    change g.toFun x ∈ LinearMap.ker N.d
    rw [LinearMap.mem_ker, ← g.map_d x, hx0, map_zero])

/-- `cocyclesMap g` sends coboundaries to coboundaries, hence descends to an
`R`-linear map `Hⁿ(M) → Hⁿ(N)` on cohomology (used to express naturality). -/
theorem cocyclesMap_coboundaries {M N : DGModule A} (g : Hom M N) (n : ℤ)
    (x : M.cocyclesM n)
    (hx : x ∈ Submodule.comap (M.cocyclesM n).subtype (M.coboundariesM n)) :
    cocyclesMap g n x ∈ Submodule.comap (N.cocyclesM n).subtype (N.coboundariesM n) := by
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨g.toFun y, g.map_grading (n - 1) y hy, ?_⟩
  have hval : (N.cocyclesM n).subtype (cocyclesMap g n x) = g.toFun (x : M.carrier) := rfl
  rw [hval, ← g.map_d y, hxy]
  rfl

/-- The induced `R`-linear map on cohomology `Hⁿ(M) → Hⁿ(N)` (used to express
naturality of Statement 2). -/
noncomputable def cohomologyMap {M N : DGModule A} (g : Hom M N) (n : ℤ) :
    M.cohomology n →ₗ[R] N.cohomology n :=
  Submodule.mapQ _ _ (cocyclesMap g n) (fun x hx => cocyclesMap_coboundaries g n x hx)

end DGModule

/-! ## Main Statements (Stacks Tag 09K1).

Let `(A, d)` be a differential graded algebra, `M` a right differential graded
`A`-module, and `k : ℤ`.  We write `A[k]` for `(A.toDGModule).shift k`.  Both
isomorphisms are induced by `f ↦ f(1)`, where `1 ∈ A⁰ = A[k]^{-k}` is the unit
of `A` regarded as an element of `A[k]` of degree `-k`.  The isomorphisms are
`R`-linear and natural in `M`. -/

namespace DGModule

variable {A : DGA R}

/-- The `R`-linear map `a ↦ op a • m`, where `m : M.carrier`. -/
def actRightMap (M : DGModule A) (m : M.carrier) : A.carrier →ₗ[R] M.carrier where
  toFun a := MulOpposite.op a • m
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' r a := by
    rw [RingHom.id_apply, MulOpposite.op_smul, smul_assoc]

/-- `M.actRightMap m` sends `a` to `op a • m`. -/
@[simp] theorem actRightMap_apply (M : DGModule A) (m : M.carrier) (a : A.carrier) :
    M.actRightMap m a = MulOpposite.op a • m := rfl

/-- The differential of a DGA kills `1`. -/
private theorem d_one (A : DGA R) : A.d 1 = 0 := by
  simpa using A.leibniz 0 1 (SetLike.one_mem_graded A.grading) 1

/-- The unit `1 : A` has degree `-k` in `A[k]`. -/
private theorem one_mem_shift_grading (A : DGA R) (k : ℤ) :
    (1 : A.carrier) ∈ ((A.toDGModule).shift k).grading (-k) := by
  change (1 : A.carrier) ∈ A.grading (-k + k)
  rw [neg_add_cancel]
  exact SetLike.one_mem_graded A.grading

/-- A morphism out of `A[k]` is determined by its value at `1`. -/
private theorem map_eq_op_smul_map_one (M : DGModule A) (k : ℤ)
    (f : Hom ((A.toDGModule).shift k) M) (y : A.carrier) :
    f.toFun y = MulOpposite.op y • f.toFun (1 : A.carrier) := by
  have hact : ((A.toDGModule).shift k).act (1 : A.carrier) y = y := by
    change MulOpposite.op y • (1 : A.carrier) = y
    rw [op_smul_eq_mul, one_mul]
  have hml := f.map_act (1 : A.carrier) y
  rw [hact] at hml
  rw [hml]
  rfl

/-- Given a cocycle `m ∈ Z^{-k}(M)`, the homomorphism `A[k] → M`, `a ↦ op a • m`. -/
noncomputable def homOfCocycle (M : DGModule A) (k : ℤ)
    (m : ↥(M.cocyclesM (-k))) : Hom ((A.toDGModule).shift k) M :=
  ⟨M.actRightMap (m : M.carrier), by
    refine ⟨?_, ?_, ?_⟩
    · -- right A-linearity
      intro x a
      -- view x as element of A.carrier
      let y : A.carrier := x
      change M.actRightMap (m : M.carrier) (MulOpposite.op a • y)
          = M.act (M.actRightMap (m : M.carrier) y) a
      simp only [actRightMap_apply, act]
      -- LHS: op (op a • y) • m, RHS: op a • (op y • m)
      rw [op_smul_eq_mul, MulOpposite.op_mul, mul_smul]
    · -- grading
      intro n x hx
      have := M.smul_mem (-k) (n + k) (m : M.carrier) x m.2.1 hx
      rwa [show -k + (n + k) = n by ring] at this
    · -- differential
      intro x
      have hdef : ((A.toDGModule).shift k).d x = k.negOnePow • A.d x := rfl
      change M.actRightMap (m : M.carrier) (((A.toDGModule).shift k).d x)
          = M.d (M.actRightMap (m : M.carrier) x)
      rw [hdef]
      simp only [actRightMap_apply]
      -- LHS: op (k.negOnePow • A.d x) • m
      rw [MulOpposite.op_smul, smul_assoc]
      -- RHS: M.d (op x • m)
      have hlb := M.leibniz (-k) (m : M.carrier) m.2.1 x
      have hdm : M.d (m : M.carrier) = 0 := LinearMap.mem_ker.mp m.2.2
      -- hlb : M.d (op x • m) = op x • M.d m + (-k).negOnePow • (op (A.d x) • m)
      rw [hlb, hdm, smul_zero, zero_add]
      -- goal: k.negOnePow • (op (A.d x) • m) = (-k).negOnePow • (op (A.d x) • m)
      rw [Int.negOnePow_neg]⟩

/-- The homomorphism `M.homOfCocycle k m` sends `a` to `op a • m`. -/
@[simp] theorem homOfCocycle_toFun (M : DGModule A) (k : ℤ)
    (m : ↥(M.cocyclesM (-k))) (a : A.carrier) :
    (M.homOfCocycle k m).toFun a = MulOpposite.op a • (m : M.carrier) := rfl

/-- The evaluation `f ↦ f(1)` lands in `Z^{-k}(M)`. -/
theorem homEval_mem (M : DGModule A) (k : ℤ) (f : Hom ((A.toDGModule).shift k) M) :
    f.toFun (1 : A.carrier) ∈ M.cocyclesM (-k) := by
  refine ⟨?_, ?_⟩
  · exact f.map_grading (-k) (1 : A.carrier) (one_mem_shift_grading A k)
  · change f.toFun (1 : A.carrier) ∈ LinearMap.ker M.d
    rw [LinearMap.mem_ker, ← f.map_d (1 : A.carrier)]
    have hd1 : ((A.toDGModule).shift k).d (1 : A.carrier) = k.negOnePow • A.d (1 : A.carrier) := rfl
    rw [hd1, d_one, smul_zero, map_zero]

/-- **Statement 1.**  Evaluation at the generator `1` gives a natural
`R`-linear isomorphism
`Hom_{Mod_{(A,d)}}(A[k], M) ≃ₗ[R] ker(d_M : M^{-k} → M^{-k+1}) = Z^{-k}(M)`,
sending `f` to `f(1)`.  The first conjunct records that the underlying map is
`f ↦ f(1)`; the second records naturality in `M`: for any morphism
`g : M → N`, the square with `cocyclesMap g` commutes. -/
@[stacks 09K1]
theorem hom_shift_equiv_cocycles (M : DGModule A) (k : ℤ) :
    ∃ e : Hom ((A.toDGModule).shift k) M ≃ₗ[R] ↥(M.cocyclesM (-k)),
      (∀ f : Hom ((A.toDGModule).shift k) M, ((e f : M.carrier)) = f.toFun (1 : A.carrier))
      ∧ (∀ (N : DGModule A) (g : Hom M N)
          (eN : Hom ((A.toDGModule).shift k) N ≃ₗ[R] ↥(N.cocyclesM (-k)))
          (_ : ∀ f', ((eN f' : N.carrier)) = f'.toFun (1 : A.carrier))
          (f : Hom ((A.toDGModule).shift k) M),
          eN (g.comp f) = cocyclesMap g (-k) (e f)) := by
  let fwd : Hom ((A.toDGModule).shift k) M →ₗ[R] ↥(M.cocyclesM (-k)) :=
    { toFun := fun f => ⟨f.toFun (1 : A.carrier), homEval_mem M k f⟩
      map_add' := fun f g => by
        apply Subtype.ext
        change (f + g).toFun (1 : A.carrier) = f.toFun (1 : A.carrier) + g.toFun (1 : A.carrier)
        rw [Hom.add_toFun]
        rfl
      map_smul' := fun r f => by
        apply Subtype.ext
        change (r • f).toFun (1 : A.carrier) = r • f.toFun (1 : A.carrier)
        rw [Hom.smul_toFun]
        rfl }
  let bwd : ↥(M.cocyclesM (-k)) →ₗ[R] Hom ((A.toDGModule).shift k) M :=
    { toFun := fun m => M.homOfCocycle k m
      map_add' := fun m m' => by
        apply Hom.ext
        intro x
        let y : A.carrier := x
        change (M.homOfCocycle k (m + m')).toFun y = (M.homOfCocycle k m + M.homOfCocycle k
            m').toFun y
        rw [Hom.add_toFun, homOfCocycle_toFun, LinearMap.add_apply, homOfCocycle_toFun,
            homOfCocycle_toFun]
        change MulOpposite.op y • ((m : M.carrier) + (m' : M.carrier))
            = MulOpposite.op y • (m : M.carrier) + MulOpposite.op y • (m' : M.carrier)
        rw [smul_add]
      map_smul' := fun r m => by
        apply Hom.ext
        intro x
        let y : A.carrier := x
        change (M.homOfCocycle k (r • m)).toFun y = ((RingHom.id R) r • M.homOfCocycle k m).toFun y
        rw [Hom.smul_toFun, homOfCocycle_toFun, LinearMap.smul_apply, homOfCocycle_toFun,
            RingHom.id_apply]
        change MulOpposite.op y • (r • (m : M.carrier))
            = r • (MulOpposite.op y • (m : M.carrier))
        rw [smul_comm] }
  have left_inv : Function.LeftInverse bwd fwd := by
    intro f
    apply Hom.ext
    intro x
    let y : A.carrier := x
    change (M.homOfCocycle k (fwd f)).toFun y = f.toFun y
    rw [homOfCocycle_toFun]
    exact (map_eq_op_smul_map_one M k f y).symm
  have right_inv : Function.RightInverse bwd fwd := by
    intro m
    apply Subtype.ext
    change (M.homOfCocycle k m).toFun (1 : A.carrier) = (m : M.carrier)
    rw [homOfCocycle_toFun, MulOpposite.op_one, one_smul]
  let e : Hom ((A.toDGModule).shift k) M ≃ₗ[R] ↥(M.cocyclesM (-k)) :=
    { fwd with
      invFun := bwd
      left_inv := left_inv
      right_inv := right_inv }
  refine ⟨e, fun _ => rfl, fun N g eN heN f => ?_⟩
  apply Subtype.ext
  rw [heN (g.comp f)]
  rfl

/-- **Statement 2.**  Passing to homotopy classes, the isomorphism of
Statement 1 descends to a natural `R`-linear isomorphism
`Hom_{K(Mod_{(A,d)})}(A[k], M) ≃ₗ[R] H^{-k}(M)`, sending the homotopy class
`[f]` to the cohomology class of `f(1)`.  Here `hf` is the membership
`f(1) ∈ Z^{-k}(M)` provided by Statement 1.  The second conjunct records
naturality in `M`: for any morphism `g : M → N`, the square with the induced
map `cohomologyMap g` commutes (where the action on homotopy classes is
`[f] ↦ [g ∘ f]`). -/
@[stacks 09K1]
theorem homotopyClasses_shift_equiv_cohomology (M : DGModule A) (k : ℤ) :
    ∃ e : HomotopyClass ((A.toDGModule).shift k) M ≃ₗ[R] M.cohomology (-k),
      (∀ (f : Hom ((A.toDGModule).shift k) M) (hf : f.toFun (1 : A.carrier) ∈ M.cocyclesM (-k)),
        e (Submodule.Quotient.mk f)
          = Submodule.Quotient.mk (⟨f.toFun (1 : A.carrier), hf⟩ : ↥(M.cocyclesM (-k))))
      ∧ (∀ (N : DGModule A) (g : Hom M N)
          (eN : HomotopyClass ((A.toDGModule).shift k) N ≃ₗ[R] N.cohomology (-k))
          (_ : ∀ (f' : Hom ((A.toDGModule).shift k) N)
                (hf' : f'.toFun (1 : A.carrier) ∈ N.cocyclesM (-k)),
              eN (Submodule.Quotient.mk f')
                = Submodule.Quotient.mk (⟨f'.toFun (1 : A.carrier), hf'⟩ : ↥(N.cocyclesM (-k))))
          (f : Hom ((A.toDGModule).shift k) M),
          eN (Submodule.Quotient.mk (g.comp f))
            = cohomologyMap g (-k) (e (Submodule.Quotient.mk f))) := by
  obtain ⟨e₁, he₁, -⟩ := hom_shift_equiv_cocycles.{_, _, _, 0} M k
  set Q : Submodule R (↥(M.cocyclesM (-k))) :=
    Submodule.comap (M.cocyclesM (-k)).subtype (M.coboundariesM (-k))
  set S : Submodule R (Hom ((A.toDGModule).shift k) M) := nullHomotopic ((A.toDGModule).shift k) M
  have key : ∀ f : Hom ((A.toDGModule).shift k) M, (e₁ f ∈ Q ↔ f ∈ S) := by
    intro f
    constructor
    · rintro ⟨w, hw, hwf⟩
      have hf1 : M.d w = f.toFun (1 : A.carrier) := by
        rw [← he₁ f]
        exact hwf
      refine ⟨M.actRightMap w, ?_, ?_, ?_⟩
      · intro x a
        let y : A.carrier := x
        change M.actRightMap w (MulOpposite.op a • y) = M.act (M.actRightMap w y) a
        simp only [actRightMap_apply, act]
        show MulOpposite.op (MulOpposite.op a • y) • w
            = MulOpposite.op a • (MulOpposite.op y • w)
        rw [op_smul_eq_mul, MulOpposite.op_mul, mul_smul]
      · intro n x hx
        have := M.smul_mem (-k - 1) (n + k) w x hw hx
        rwa [show -k - 1 + (n + k) = n - 1 by ring] at this
      · intro x
        let y : A.carrier := x
        change f.toFun y = M.d (M.actRightMap w y) + M.actRightMap w (((A.toDGModule).shift k).d y)
        have hdef : ((A.toDGModule).shift k).d y = k.negOnePow • A.d y := rfl
        rw [hdef]
        simp only [actRightMap_apply]
        have hterm : MulOpposite.op (k.negOnePow • A.d y) • w
            = k.negOnePow • (MulOpposite.op (A.d y) • w) := by
          rw [MulOpposite.op_smul, smul_assoc]
        rw [hterm, M.leibniz (-k - 1) w hw y, map_eq_op_smul_map_one M k f y, ← hf1]
        have hcancel : (-k - 1).negOnePow • (MulOpposite.op (A.d y) • w)
            + k.negOnePow • (MulOpposite.op (A.d y) • w) = 0 := by
          have hsign : (-k - 1).negOnePow = - k.negOnePow := by
            rw [show -k - 1 = -(k + 1) from by ring, Int.negOnePow_neg, Int.negOnePow_succ]
          rw [hsign, Units.neg_smul, neg_add_cancel]
        rw [add_assoc, hcancel, add_zero]
    · rintro ⟨h, -, hgr, hf⟩
      refine ⟨h (1 : A.carrier), hgr (-k) (1 : A.carrier) (one_mem_shift_grading A k), ?_⟩
      have hd1 : ((A.toDGModule).shift k).d (1 : A.carrier)
          = k.negOnePow • A.d (1 : A.carrier) := rfl
      have hf1 := hf (1 : A.carrier)
      rw [hd1, d_one, smul_zero, map_zero, add_zero] at hf1
      change M.d (h (1 : A.carrier)) = (e₁ f : M.carrier)
      rw [he₁ f, hf1]
  have hmap : Submodule.map (e₁ : Hom ((A.toDGModule).shift k) M →ₗ[R] ↥(M.cocyclesM
      (-k))) S = Q := by
    apply le_antisymm
    · rintro _ ⟨f, hfS, rfl⟩
      exact (key f).mpr hfS
    · intro y hy
      exact ⟨e₁.symm y, (key _).mp (by rwa [LinearEquiv.apply_symm_apply]), by simp⟩
  let e : HomotopyClass ((A.toDGModule).shift k) M ≃ₗ[R] M.cohomology (-k) :=
    Submodule.Quotient.equiv S Q e₁ hmap
  have h₁ : ∀ (f : Hom ((A.toDGModule).shift k) M)
      (hf : f.toFun (1 : A.carrier) ∈ M.cocyclesM (-k)),
      e (Submodule.Quotient.mk f)
        = Submodule.Quotient.mk (⟨f.toFun (1 : A.carrier), hf⟩ : ↥(M.cocyclesM (-k))) := by
    intro f hf
    change Submodule.Quotient.mk (e₁ f) = _
    congr 1
    exact Subtype.ext (he₁ f)
  refine ⟨e, h₁, fun N g eN heN f => ?_⟩
  rw [heN (g.comp f) (homEval_mem N k (g.comp f)), h₁ f (homEval_mem M k f)]
  rfl

end DGModule

end Stacks.DifferentialGraded.HomComplex
