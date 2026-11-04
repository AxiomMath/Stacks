module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ReesToAssociatedGraded

/-!
# The graded module of a tower of graded algebras

Let `𝓟` be a sheaf of graded algebras on a scheme `X` and let `C₀, C₁, C₂, …` be sheaves of graded
algebras under `𝓟` (unital homomorphisms `φₘ : 𝓟 ⟶ Cₘ`), with comparison homomorphisms
`cₘₖ : Cₘ ⟶ Cₖ` for `k ≤ m`, compatible with the `φ`, with each other and with the identity, and
**invertible in every degree `n ≤ k`**. This is the shape of the conormal algebras
`Cₘ = ⨁ₙ 𝒥ₘⁿ/𝒥ₘⁿ⁺¹` of the closed immersions `X₀ ⟶ Xₘ` of a tower of thickenings: the transition
`Xₖ ⟶ Xₘ` identifies `𝒥ₘⁿ/𝒥ₘⁿ⁺¹` with `𝒥ₖⁿ/𝒥ₖⁿ⁺¹` as long as `n ≤ k`.

From such a tower this file builds a single graded `𝓟`-module `M` with `Mₙ = (Cₙ)ₙ`: the diagonal
of the tower. A homogeneous section `y` of `𝓟` of degree `i` acts on `x ∈ Mₙ` by moving `x` into
`Cₙ₊ᵢ` along the inverse of `cₙ₊ᵢ,ₙ` and multiplying there by `φₙ₊ᵢ(y)`. This is how the proof of
[Stacks, Tag 089A] makes `⨁ₙ Iⁿ𝒪_{Xₙ₊₁}` into a graded module over `⨁ₙ Iⁿ/Iⁿ⁺¹` ("pick an `m`
larger than `n₁ + n₂` and multiply in `𝒪_{Xₘ}`").

## Main definitions

* `Stacks.GradedTower.Tower`: the data and axioms above.
* `Stacks.GradedTower.Tower.module`: the graded `𝓟`-module `M`.

## Main results

* `Stacks.GradedTower.Tower.isFiniteTypeOnAffine_module`: if every `φₙ` is surjective in degree
  `n` on the sections over affine opens, then `M` is of finite type, generated in degree zero by
  the unit.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.GradedTower

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] TopCat.Sheaf PresheafOfModules.presheaf
  SheafOfModules.toSheaf ModuleCat.restrictScalars

variable {X : Scheme.{u}}

/-- **A tower of graded algebras under `𝓟`** whose comparison maps are invertible in low
degrees. -/
structure Tower (P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) where
  /-- The graded algebras of the tower. -/
  alg : ℕ → SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf
  /-- The structure maps out of `𝓟`. -/
  φ : ∀ m, SheafOfModules.GradedAlgebra.UnitalHom P (alg m)
  /-- The comparison maps down the tower. -/
  c : ∀ m k, k ≤ m → SheafOfModules.GradedAlgebra.Hom (alg m) (alg k)
  c_φ : ∀ (m k : ℕ) (h : k ≤ m) (n : ℤ), (φ m).app n ≫ (c m k h).app n = (φ k).app n
  c_comp : ∀ (l m k : ℕ) (h₁ : m ≤ l) (h₂ : k ≤ m) (n : ℤ),
    (c l m h₁).app n ≫ (c m k h₂).app n = (c l k (h₂.trans h₁)).app n
  c_self : ∀ (k : ℕ) (n : ℤ), (c k k le_rfl).app n = 𝟙 _
  isIso_c : ∀ (m k : ℕ) (h : k ≤ m) (n : ℤ), n ≤ (k : ℤ) → IsIso ((c m k h).app n)
  alg_neg : ∀ (m : ℕ) (n : ℤ), n < 0 → IsZero ((alg m).piece n)

namespace Tower

variable {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

section OfSteps

variable (alg : ℕ → SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (step : ∀ m, SheafOfModules.GradedAlgebra.UnitalHom (alg (m + 1)) (alg m))

/-- The comparison maps of a sequence of steps, as a functor out of `ℕᵒᵖ`. -/
abbrev stepFunctor : ℕᵒᵖ ⥤ SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  Functor.ofOpSequence (X := alg) (fun m => ((step m).toHom : alg (m + 1) ⟶ alg m))

/-- The comparison map `Cₘ₊₁ ⟶ Cₖ` of `stepFunctor` is the step `Cₘ₊₁ ⟶ Cₘ` followed by the
comparison map `Cₘ ⟶ Cₖ`. -/
lemma stepFunctor_map_succ (m k : ℕ) (h : k ≤ m) :
    (stepFunctor alg step).map (homOfLE (h.trans (Nat.le_succ m))).op =
      (step m).toHom ≫ (stepFunctor alg step).map (homOfLE h).op := by
  have e := Functor.ofOpSequence_map_homOfLE_succ (X := alg)
    (fun m => ((step m).toHom : alg (m + 1) ⟶ alg m)) m
  refine Eq.trans ?_ (congrArg (· ≫ (stepFunctor alg step).map (homOfLE h).op) e)
  rw [← Functor.map_comp]
  rfl

/-- In each degree `n`, the comparison map `Cₘ₊₁ ⟶ Cₖ` of `stepFunctor` is the step
`Cₘ₊₁ ⟶ Cₘ` followed by the comparison map `Cₘ ⟶ Cₖ`. -/
lemma stepFunctor_map_app_succ (m k : ℕ) (h : k ≤ m) (n : ℤ) :
    ((stepFunctor alg step).map (homOfLE (h.trans (Nat.le_succ m))).op).app n =
      (step m).app n ≫ ((stepFunctor alg step).map (homOfLE h).op).app n := by
  rw [stepFunctor_map_succ]; rfl

/-- In every degree, the comparison map `Cₖ ⟶ Cₖ` of `stepFunctor` is the identity. -/
lemma stepFunctor_map_self (k : ℕ) (n : ℤ) :
    ((stepFunctor alg step).map (homOfLE (le_refl k)).op).app n = 𝟙 _ := by
  have e : (stepFunctor alg step).map (homOfLE (le_refl k)).op = 𝟙 _ := by
    rw [show (homOfLE (le_refl k)).op = 𝟙 (Opposite.op k) from rfl]
    exact (stepFunctor alg step).map_id _
  rw [e]; rfl

/-- **A tower from its single steps.** The comparison maps `Cₘ ⟶ Cₖ` are the composites of the
steps `Cₘ₊₁ ⟶ Cₘ`; it suffices that the steps be compatible with the structure maps out of `𝓟`
and invertible in degrees `n ≤ m`. -/
def ofSteps (φ : ∀ m, SheafOfModules.GradedAlgebra.UnitalHom P (alg m))
    (hφ : ∀ m, (φ (m + 1)).comp (step m) = φ m)
    (hiso : ∀ (m : ℕ) (n : ℤ), n ≤ (m : ℤ) → IsIso ((step m).app n))
    (hneg : ∀ (m : ℕ) (n : ℤ), n < 0 → IsZero ((alg m).piece n)) : Tower P where
  alg := alg
  φ := φ
  c m k h := (stepFunctor alg step).map (homOfLE h).op
  c_φ m k h n := by
    induction m, h using Nat.le_induction with
    | base => rw [stepFunctor_map_self]; exact Category.comp_id _
    | succ m hkm ih =>
      rw [stepFunctor_map_app_succ alg step m k hkm n]
      have h1 : (φ (m + 1)).app n ≫ (step m).app n = (φ m).app n :=
        congrArg (fun g => g.app n) (hφ m)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ih)
  c_comp l m k h₁ h₂ n :=
    (congrArg (fun g => SheafOfModules.GradedAlgebra.Hom.app g n)
      ((stepFunctor alg step).map_comp (homOfLE h₁).op (homOfLE h₂).op)).symm
  c_self k n := stepFunctor_map_self alg step k n
  isIso_c m k h n hn := by
    induction m, h using Nat.le_induction with
    | base => rw [stepFunctor_map_self]; exact IsIso.id _
    | succ m hkm ih =>
      rw [stepFunctor_map_app_succ alg step m k hkm n]
      exact @IsIso.comp_isIso _ _ _ _ _ ((step m).app n)
        (((stepFunctor alg step).map (homOfLE hkm).op).app n)
        (hiso m n (hn.trans (by exact_mod_cast hkm))) ih
  alg_neg := hneg

end OfSteps

variable (T : Tower P)

/-! ### Moving up the tower -/

/-- The inverse of the comparison `cₘₖ` in a degree `n ≤ k`. -/
def lift (m k : ℕ) (h : k ≤ m) (n : ℤ) (hn : n ≤ (k : ℤ)) : (T.alg k).piece n ⟶ (T.alg m).piece n :=
  haveI := T.isIso_c m k h n hn
  inv ((T.c m k h).app n)

/-- The comparison `cₘₖ` undoes `lift` on sections. -/
lemma c_lift_apply (m k : ℕ) (h : k ≤ m) (n : ℤ) (hn : n ≤ k) (U : X.Opensᵒᵖ)
    (x : ((T.alg k).piece n).val.obj U) :
    ((T.c m k h).app n).val.app U ((T.lift m k h n hn).val.app U x) = x := by
  have := T.isIso_c m k h n hn
  exact congrArg (fun f => f.val.app U x) (IsIso.inv_hom_id ((T.c m k h).app n))

/-- `lift` undoes the comparison `cₘₖ` on sections. -/
lemma lift_c_apply (m k : ℕ) (h : k ≤ m) (n : ℤ) (hn : n ≤ k) (U : X.Opensᵒᵖ)
    (x : ((T.alg m).piece n).val.obj U) :
    (T.lift m k h n hn).val.app U (((T.c m k h).app n).val.app U x) = x := by
  have := T.isIso_c m k h n hn
  exact congrArg (fun f => f.val.app U x) (IsIso.hom_inv_id ((T.c m k h).app n))

/-- In a degree `n ≤ k`, the comparison `cₘₖ` is injective on sections. -/
lemma c_injective (m k : ℕ) (h : k ≤ m) (n : ℤ) (hn : n ≤ k) (U : X.Opensᵒᵖ) :
    Function.Injective (((T.c m k h).app n).val.app U) := fun x y hxy => by
  rw [← T.lift_c_apply m k h n hn U x, hxy, T.lift_c_apply]

/-- Lifting from `Cₖ` to itself is the identity on sections. -/
lemma lift_self_apply (k : ℕ) (n : ℤ) (hn : n ≤ k) (U : X.Opensᵒᵖ)
    (x : ((T.alg k).piece n).val.obj U) : (T.lift k k le_rfl n hn).val.app U x = x := by
  have h := T.c_lift_apply k k le_rfl n hn U x
  rwa [T.c_self] at h

/-- Lifting from `Cₖ` to `Cₘ` and then to `Cₗ` is lifting from `Cₖ` to `Cₗ`. -/
lemma lift_lift_apply (l m k : ℕ) (h₁ : m ≤ l) (h₂ : k ≤ m) (n : ℤ) (hn : n ≤ k)
    (U : X.Opensᵒᵖ) (x : ((T.alg k).piece n).val.obj U) :
    (T.lift l m h₁ n (hn.trans (by exact_mod_cast h₂))).val.app U
        ((T.lift m k h₂ n hn).val.app U x) = (T.lift l k (h₂.trans h₁) n hn).val.app U x := by
  apply T.c_injective l k (h₂.trans h₁) n hn U
  rw [T.c_lift_apply, ← T.c_comp l m k h₁ h₂ n]
  show ((T.c m k h₂).app n).val.app U (((T.c l m h₁).app n).val.app U _) = _
  rw [T.c_lift_apply, T.c_lift_apply]

/-- Lifting the image of `y` under `φₖ` to `Cₘ` gives the image of `y` under `φₘ`. -/
lemma lift_φ_apply (m k : ℕ) (h : k ≤ m) (n : ℤ) (hn : n ≤ k) (U : X.Opensᵒᵖ)
    (y : (P.piece n).val.obj U) :
    (T.lift m k h n hn).val.app U (((T.φ k).app n).val.app U y) =
      ((T.φ m).app n).val.app U y := by
  apply T.c_injective m k h n hn U
  rw [T.c_lift_apply, ← T.c_φ m k h n]
  rfl

/-- `lift` is multiplicative: the lift of a product `x * y` of degree `i + j ≤ k` is the
product of the lifts. -/
lemma lift_mul_apply (m k : ℕ) (h : k ≤ m) (i j : ℤ) (hi : i ≤ k) (hj : j ≤ k)
    (hij : i + j ≤ k) (U : X.Opensᵒᵖ) (x : ((T.alg k).piece i).val.obj U)
    (y : ((T.alg k).piece j).val.obj U) :
    (T.lift m k h (i + j) hij).val.app U (((T.alg k).mul i j).app U x y) =
      ((T.alg m).mul i j).app U ((T.lift m k h i hi).val.app U x)
        ((T.lift m k h j hj).val.app U y) := by
  apply T.c_injective m k h (i + j) hij U
  rw [T.c_lift_apply, (T.c m k h).map_mul, T.c_lift_apply, T.c_lift_apply]

/-- `lift` sends the unit of `Cₖ` to the unit of `Cₘ`. -/
lemma lift_one_apply (m k : ℕ) (h : k ≤ m) (U : X.Opensᵒᵖ) :
    (T.lift m k h 0 (by exact_mod_cast Nat.zero_le k)).val.app U ((T.alg k).one.eval U) =
      (T.alg m).one.eval U := by
  rw [← (T.φ k).map_one U, T.lift_φ_apply, (T.φ m).map_one U]

/-! ### The diagonal module -/

/-- The degree-`n` piece `(Cₙ)ₙ` of the diagonal module. -/
abbrev piece (n : ℤ) : X.Modules := (T.alg n.toNat).piece n

/-- Every section of a piece of negative degree of the diagonal module is zero. -/
lemma piece_eq_zero (n : ℤ) (hn : n < 0) (U : X.Opensᵒᵖ) (x : (T.piece n).val.obj U) :
    x = 0 :=
  Stacks.Coherent.sections_eq_zero_of_isZero _ (T.alg_neg _ n hn) U x

/-- The zero sections of the pieces of equal degrees `a = b` are heterogeneously equal. -/
lemma piece_heq_zero {a b : ℤ} (h : a = b) (U : X.Opensᵒᵖ) :
    HEq (0 : (T.piece a).val.obj U) (0 : (T.piece b).val.obj U) := by
  subst h; rfl

/-- The action of a degree-`i` section of `𝓟` on a section of `Mₙ`, for `i ≥ 0`. -/
def smulFun (n i : ℤ) (hi : 0 ≤ i) (U : X.Opensᵒᵖ) (x : (T.piece n).val.obj U)
    (y : (P.piece i).val.obj U) : (T.piece (n + i)).val.obj U :=
  ((T.alg (n + i).toNat).mul n i).app U
    ((T.lift (n + i).toNat n.toNat (by omega) n (Int.self_le_toNat n)).val.app U x)
    (((T.φ (n + i).toNat).app i).val.app U y)

/-- The action, as a biadditive map. -/
def smulHom (n i : ℤ) (U : X.Opensᵒᵖ) :
    (T.piece n).val.obj U →+ (P.piece i).val.obj U →+ (T.piece (n + i)).val.obj U :=
  if hi : 0 ≤ i then
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (T.smulFun n i hi U x) fun y y' => by
        simp only [smulFun, map_add])
      fun x x' => by
        ext y
        simp only [smulFun, map_add, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
  else 0

/-- For `i ≥ 0`, `smulHom` is given by `smulFun`. -/
lemma smulHom_of_nonneg (n i : ℤ) (hi : 0 ≤ i) (U : X.Opensᵒᵖ) (x : (T.piece n).val.obj U)
    (y : (P.piece i).val.obj U) : T.smulHom n i U x y = T.smulFun n i hi U x y := by
  simp only [smulHom, dif_pos hi, AddMonoidHom.mk'_apply]

/-- For `i < 0`, `smulHom` is zero. -/
lemma smulHom_of_neg (n i : ℤ) (hi : ¬ 0 ≤ i) (U : X.Opensᵒᵖ) (x : (T.piece n).val.obj U)
    (y : (P.piece i).val.obj U) : T.smulHom n i U x y = 0 := by
  simp only [smulHom, dif_neg hi, AddMonoidHom.zero_apply]

/-- `smulFun` may be computed at any level `M` of the tower equal to `(n + i).toNat`. -/
lemma smulFun_eq (n i : ℤ) (hi : 0 ≤ i) (_hn : 0 ≤ n) (M : ℕ) (hM : (n + i).toNat = M)
    (U : X.Opensᵒᵖ) (x : (T.piece n).val.obj U) (y : (P.piece i).val.obj U) :
    HEq (T.smulFun n i hi U x y)
      (((T.alg M).mul n i).app U
        ((T.lift M n.toNat (by omega) n (Int.self_le_toNat n)).val.app U x)
        (((T.φ M).app i).val.app U y)) := by
  subst hM; rfl

/-- The action of any section of `𝓟` on the zero section is zero. -/
lemma smulHom_zero_left (n i : ℤ) (U : X.Opensᵒᵖ) (y : (P.piece i).val.obj U) :
    T.smulHom n i U 0 y = 0 := by
  rw [map_zero, AddMonoidHom.zero_apply]

/-- `lift` is linear over the structure sheaf. -/
lemma lift_smul_apply (m k : ℕ) (h : k ≤ m) (n : ℤ) (hn : n ≤ (k : ℤ)) (U : X.Opensᵒᵖ)
    (r : X.ringCatSheaf.obj.obj U) (x : ((T.alg k).piece n).val.obj U) :
    (T.lift m k h n hn).val.app U (r • x) = r • (T.lift m k h n hn).val.app U x :=
  ((T.lift m k h n hn).val.app U).hom.map_smul r x

/-- The structure map `φₘ` is linear over the structure sheaf. -/
lemma φ_smul_apply (m : ℕ) (n : ℤ) (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj U)
    (y : (P.piece n).val.obj U) :
    ((T.φ m).app n).val.app U (r • y) = r • ((T.φ m).app n).val.app U y :=
  (((T.φ m).app n).val.app U).hom.map_smul r y

/-- Lifting from `C_N` to `C_K` with `K = N` is heterogeneously the identity. -/
lemma lift_heq_self (K N : ℕ) (hKN : K = N) (n : ℤ) (hn : n ≤ (N : ℤ)) (U : X.Opensᵒᵖ)
    (x : ((T.alg N).piece n).val.obj U) :
    HEq ((T.lift K N hKN.ge n hn).val.app U x) x := by
  subst hKN
  rw [T.lift_self_apply]

/-- For `K = N`, the images of `y` under `φ_K` and `φ_N` are heterogeneously equal. -/
lemma φ_heq (K N : ℕ) (hKN : K = N) (n : ℤ) (U : X.Opensᵒᵖ) (y : (P.piece n).val.obj U) :
    HEq (((T.φ K).app n).val.app U y) (((T.φ N).app n).val.app U y) := by
  subst hKN; rfl

variable (hP : ∀ n : ℤ, n < 0 → ∀ (U : X.Opensᵒᵖ) (y : (P.piece n).val.obj U), y = 0)
include hP

/-- Under `hP`, every section of a piece of `𝓟` of negative degree is zero. -/
lemma P_eq_zero (n : ℤ) (hn : n < 0) (U : X.Opensᵒᵖ) (y : (P.piece n).val.obj U) : y = 0 :=
  hP n hn U y

omit hP in
/-- The main identity behind associativity, at a common level of the tower. -/
lemma assoc_at (n i j : ℤ) (M : ℕ) (hM : n.toNat ≤ M) (U : X.Opensᵒᵖ)
    (x : (T.piece n).val.obj U) (y : (P.piece i).val.obj U) (z : (P.piece j).val.obj U) :
    HEq (((T.alg M).mul (n + i) j).app U (((T.alg M).mul n i).app U
        ((T.lift M n.toNat hM n (Int.self_le_toNat n)).val.app U x)
        (((T.φ M).app i).val.app U y)) (((T.φ M).app j).val.app U z))
      (((T.alg M).mul n (i + j)).app U
        ((T.lift M n.toNat hM n (Int.self_le_toNat n)).val.app U x)
        (((T.φ M).app (i + j)).val.app U ((P.mul i j).app U y z))) := by
  rw [(T.φ M).map_mul]
  exact (T.alg M).mul_assoc n i j U _ _ _

omit hP in
/-- The right-hand side of `assoc_at` does not depend on the level `M` of the tower, up to
heterogeneous equality. -/
lemma assoc_at_congr (n i j : ℤ) (M M' : ℕ) (hMM : M = M') (hM : n.toNat ≤ M)
    (hM' : n.toNat ≤ M') (U : X.Opensᵒᵖ)
    (x : (T.piece n).val.obj U) (y : (P.piece i).val.obj U) (z : (P.piece j).val.obj U) :
    HEq (((T.alg M).mul n (i + j)).app U
        ((T.lift M n.toNat hM n (Int.self_le_toNat n)).val.app U x)
        (((T.φ M).app (i + j)).val.app U ((P.mul i j).app U y z)))
      (((T.alg M').mul n (i + j)).app U
        ((T.lift M' n.toNat hM' n (Int.self_le_toNat n)).val.app U x)
        (((T.φ M').app (i + j)).val.app U ((P.mul i j).app U y z))) := by
  subst hMM; rfl

/-- **The diagonal graded `𝓟`-module of the tower.** -/
def module : SheafOfModules.GradedModule P where
  piece := T.piece
  smul := T.smulHom
  smul_smul_left n i U r x y := by
    by_cases hi : 0 ≤ i
    · simp only [T.smulHom_of_nonneg n i hi, smulFun, T.lift_smul_apply]
      exact ((T.alg (n + i).toNat).mul n i).map_smul_left U r _ _
    · simp only [T.smulHom_of_neg n i hi, smul_zero]
  smul_smul_right n i U r x y := by
    by_cases hi : 0 ≤ i
    · simp only [T.smulHom_of_nonneg n i hi, smulFun, T.φ_smul_apply]
      exact ((T.alg (n + i).toNat).mul n i).map_smul_right U r _ _
    · simp only [T.smulHom_of_neg n i hi, smul_zero]
  smul_naturality n i U V f x y := by
    by_cases hi : 0 ≤ i
    · refine Eq.trans ?_ (T.smulHom_of_nonneg n i hi V _ _).symm
      rw [T.smulHom_of_nonneg n i hi U]
      simp only [smulFun]
      rw [((T.alg (n + i).toNat).mul n i).naturality f]
      exact congrArg₂ (fun a b => ((T.alg (n + i).toNat).mul n i).app V a b)
        (PresheafOfModules.naturality_apply _ f _).symm
        (PresheafOfModules.naturality_apply _ f _).symm
    · refine Eq.trans ?_ (T.smulHom_of_neg n i hi V _ _).symm
      rw [T.smulHom_of_neg n i hi U]
      exact map_zero _
  smul_mul n i j U x y z := by
    by_cases hn : 0 ≤ n
    swap
    · rw [T.piece_eq_zero n (not_le.mp hn) U x, T.smulHom_zero_left, T.smulHom_zero_left,
        T.smulHom_zero_left]
      exact T.piece_heq_zero (add_assoc n i j) U
    by_cases hi : 0 ≤ i
    swap
    · rw [P_eq_zero hP i (not_le.mp hi) U y, map_zero, T.smulHom_zero_left,
        (P.mul i j).app U |>.map_zero, AddMonoidHom.zero_apply,
        ]
      exact (T.piece_heq_zero (add_assoc n i j) U).trans (heq_of_eq (map_zero _).symm)
    by_cases hj : 0 ≤ j
    swap
    · rw [P_eq_zero hP j (not_le.mp hj) U z, map_zero, map_zero]
      exact (T.piece_heq_zero (add_assoc n i j) U).trans (heq_of_eq (map_zero _).symm)
    have hij : 0 ≤ i + j := add_nonneg hi hj
    rw [T.smulHom_of_nonneg _ _ hj, T.smulHom_of_nonneg _ _ hi, T.smulHom_of_nonneg _ _ hij]
    simp only [smulFun]
    rw [T.lift_mul_apply (n + i + j).toNat (n + i).toNat (by omega) n i (by omega) (by omega)
      (Int.self_le_toNat _), T.lift_lift_apply, T.lift_φ_apply]
    exact (T.assoc_at n i j (n + i + j).toNat (by omega) U x y z).trans
      (T.assoc_at_congr n i j _ _ (by rw [add_assoc]) _ _ U x y z)
  smul_one n U x := by
    rw [T.smulHom_of_nonneg n 0 le_rfl]
    simp only [smulFun]
    rw [(T.φ (n + 0).toNat).map_one U]
    exact ((T.alg (n + 0).toNat).mul_one n U _).trans
      (T.lift_heq_self _ _ (by rw [add_zero]) n _ U x)

omit hP in
/-- A section transported along `a = b` equals a section heterogeneously equal to it. -/
lemma heq_of_heq_eqRec {U : X.Opensᵒᵖ} {a b : ℤ} (h : a = b) (v : (T.piece a).val.obj U)
    (w : (T.piece b).val.obj U) (hv : HEq v w) : h ▸ v = w := by
  subst h; exact eq_of_heq hv

/-- **The diagonal module is of finite type, generated in degree zero by the unit**, as soon as
each structure map `φₙ` is surjective in degree `n` on the sections over affine opens. -/
theorem isFiniteTypeOnAffine_module
    (hsurj : ∀ (U : X.affineOpens) (n : ℤ), 0 ≤ n →
      Function.Surjective (((T.φ n.toNat).app n).val.app (op U.1))) :
    Stacks.Coherent.IsFiniteTypeOnAffine (T.module hP) := by
  classical
  intro U
  let one : (T.piece 0).val.obj (op U.1) := (T.alg (0 : ℤ).toNat).one.eval (op U.1)
  refine ⟨{⟨0, one⟩}, fun n => ?_⟩
  refine top_unique fun t _ => ?_
  by_cases hn : 0 ≤ n
  swap
  · rw [T.piece_eq_zero n (not_le.mp hn) _ t]
    exact AddSubgroup.zero_mem _
  obtain ⟨a, rfl⟩ := hsurj U n hn t
  refine AddSubgroup.subset_closure ⟨⟨0, one⟩, Finset.mem_singleton_self _, n, a,
    zero_add n, ?_⟩
  symm
  refine T.heq_of_heq_eqRec (zero_add n) _ _ ?_
  show HEq (T.smulHom 0 n (op U.1) one a) _
  rw [T.smulHom_of_nonneg 0 n hn]
  simp only [smulFun]
  rw [T.lift_one_apply]
  exact ((T.alg (0 + n).toNat).one_mul n _ _).trans
    (T.φ_heq _ _ (by rw [zero_add]) n _ a)

end Tower

end Stacks.GradedTower

end
