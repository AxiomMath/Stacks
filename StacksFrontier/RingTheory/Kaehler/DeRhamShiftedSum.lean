module

public import StacksFrontier.Algebra.Homology.FilteredTensorGradedQuasiIso
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexComparison
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import StacksFrontier.Homology.KFlat.Flat

/-!
# A finite sum of shifted de Rham complexes, filtered by the degree of the forms

Let `R ⟶ A` be a map of commutative rings and let `n : I → ℕ` be a family of degrees. This file
builds the complex `M = ⨁_i Ω^•_{A/R}[-n_i]` of `R`-modules (the differential of the `i`-th
summand is `(-1)^{n_i} d`), elementwise: in degree `p` it is the product over `i` of the forms of
degree `b` with `n_i + b = p`. It is filtered by the degree of the forms, `F^k M` consisting of
the forms of degree at least `k`, and the graded pieces are
`gr^k M ≅ Ω^k_{A/R} ⊗_A G` moved up by `k` degrees, where `G = ⨁_i A[-n_i]` has zero differential.

This is the complex `M` of the proof of [Stacks, Tag 0FUM].

## Main definitions

* `Stacks.KatzOda.ShiftedSum.complex`: the complex `⨁_i Ω^•_{A/R}[-n_i]`.
* `Stacks.KatzOda.ShiftedSum.filtration`: its filtration by the degree of the forms.
* `Stacks.KatzOda.ShiftedSum.unitComplex`: the complex `⨁_i A[-n_i]` with zero differential.
* `Stacks.KatzOda.ShiftedSum.gradedIso`: `gr^k M ≅ Ω^k_{A/R} ⊗_A G` moved up by `k` degrees.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.KatzOda.ShiftedSum

open Stacks.AlgebraicGeometry.AffineDifferentialsIso

variable {R A : CommRingCat.{u}} (gR : R ⟶ A) {I : Type u} (n : I → ℕ)

/-- The degree-`p` term of `⨁_i Ω^•_{A/R}[-n_i]`: the forms of degree `b` with `n_i + b = p`. -/
abbrev MX (p : ℤ) : Type u :=
  ∀ (i : I) (b : {b : ℕ // (n i : ℤ) + b = p}), (ringDeRhamComplex gR).X b.1

/-- The `(i, b)`-component of the differential of `⨁_i Ω^•_{A/R}[-n_i]`. -/
def dAt {p : ℤ} (x : MX gR n p) (i : I) :
    ∀ (b : ℕ), (n i : ℤ) + b = p + 1 → (ringDeRhamComplex gR).X b
  | 0, _ => 0
  | c + 1, h => ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom
      (x i ⟨c, by push_cast at h; omega⟩)

/-- The component of `dAt` at forms of degree `0` vanishes. -/
theorem dAt_zero {p : ℤ} (x : MX gR n p) (i : I) (h : (n i : ℤ) + (0 : ℕ) = p + 1) :
    dAt gR n x i 0 h = 0 :=
  rfl

/-- The component of `dAt` at forms of degree `c + 1` is `(-1)^{n_i} d` applied to the
`(i, c)`-component. -/
theorem dAt_succ {p : ℤ} (x : MX gR n p) (i : I) (c : ℕ) (h : (n i : ℤ) + (c + 1 : ℕ) = p + 1) :
    dAt gR n x i (c + 1) h = ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom
      (x i ⟨c, by push_cast at h; omega⟩) :=
  rfl

/-- The differential of `⨁_i Ω^•_{A/R}[-n_i]`, from degree `p` to degree `q = p + 1`. -/
def dTo (p q : ℤ) (h : p + 1 = q) : MX gR n p →ₗ[R] MX gR n q where
  toFun x i b := dAt gR n x i b.1 (b.2.trans h.symm)
  map_add' x y := by
    funext i ⟨b, hb⟩
    rcases b with _ | c
    · exact (add_zero 0).symm
    · change ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom
          (x i ⟨c, _⟩ + y i ⟨c, _⟩) =
        ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom (x i ⟨c, _⟩) +
          ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom (y i ⟨c, _⟩)
      rw [map_add, smul_add]
  map_smul' r x := by
    funext i ⟨b, hb⟩
    rcases b with _ | c
    · exact (smul_zero r).symm
    · change ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom (r • x i ⟨c, _⟩) =
        r • (((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom (x i ⟨c, _⟩))
      rw [map_smul, smul_comm]

/-- The `(i, b)`-component of `dTo` is `dAt` at `(i, b)`. -/
theorem dTo_apply (p q : ℤ) (h : p + 1 = q) (x : MX gR n p) (i : I)
    (b : {b : ℕ // (n i : ℤ) + b = q}) :
    dTo gR n p q h x i b = dAt gR n x i b.1 (b.2.trans h.symm) :=
  rfl

/-- Two consecutive differentials of `⨁_i Ω^•_{A/R}[-n_i]` compose to zero. -/
theorem dTo_dTo (p : ℤ) (x : MX gR n p) :
    dTo gR n (p + 1) (p + 1 + 1) rfl (dTo gR n p (p + 1) rfl x) = 0 := by
  funext i ⟨b, hb⟩
  rcases b with _ | _ | c
  · rfl
  · change ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d 0 1).hom
      (0 : (ringDeRhamComplex gR).X 0) = 0
    rw [map_zero, smul_zero]
  · change ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d (c + 1) (c + 1 + 1)).hom
      (((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom (x i ⟨c, _⟩)) = 0
    rw [map_zsmul, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      (ringDeRhamComplex gR).d_comp_d]
    simp

/-- The differentials of `⨁_i Ω^•_{A/R}[-n_i]`. -/
def diff (p q : ℤ) : ModuleCat.of R (MX gR n p) ⟶ ModuleCat.of R (MX gR n q) :=
  if h : p + 1 = q then ModuleCat.ofHom (dTo gR n p q h) else 0

/-- **The complex `⨁_i Ω^•_{A/R}[-n_i]`**, the differential of the `i`-th summand being
`(-1)^{n_i} d`. -/
abbrev complex : CochainComplex (ModuleCat.{u} R) ℤ where
  X p := ModuleCat.of R (MX gR n p)
  d := diff gR n
  shape p q h := dite_eq_right h
  d_comp_d' p q r hpq hqr := by
    subst hpq hqr
    rw [diff, diff, dite_eq_left rfl, dite_eq_left rfl]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => dTo_dTo gR n p x)

/-- The differential of `complex` from degree `p` to degree `p + 1` is `dTo`. -/
theorem complex_d_apply {p q : ℤ} (h : p + 1 = q) (x : MX gR n p) :
    ((complex gR n).d p q).hom x = dTo gR n p q h x := by
  change (diff gR n p q).hom x = _
  rw [diff, dite_eq_left h]
  rfl

/-! ### The filtration by the degree of the forms -/

/-- The `k`-th step of the filtration: the forms of degree at least `k`. -/
def step (k : ℕ) (p : ℤ) : Submodule R (MX gR n p) where
  carrier := {x | ∀ (i : I) (b : {b : ℕ // (n i : ℤ) + b = p}), b.1 < k → x i b = 0}
  add_mem' {x y} hx hy i b hb := by
    change x i b + y i b = 0
    rw [hx i b hb, hy i b hb, add_zero]
  zero_mem' _ _ _ := rfl
  smul_mem' r x hx i b hb := by
    change r • x i b = 0
    rw [hx i b hb, smul_zero]

/-- An element lies in `step k` if and only if its components of form degree below `k` vanish. -/
theorem mem_step {k : ℕ} {p : ℤ} {x : MX gR n p} :
    x ∈ step gR n k p ↔ ∀ (i : I) (b : {b : ℕ // (n i : ℤ) + b = p}), b.1 < k → x i b = 0 :=
  Iff.rfl

/-- The differential maps `step k` in degree `p` into `step (k + 1)` in degree `p + 1`. -/
theorem dTo_mem_step {k : ℕ} {p q : ℤ} (h : p + 1 = q) {x : MX gR n p} (hx : x ∈ step gR n k p) :
    dTo gR n p q h x ∈ step gR n (k + 1) q := by
  rintro i ⟨b, hb⟩ hbk
  rcases b with _ | c
  · rfl
  · have hc : (n i : ℤ) + c = p := by push_cast at hb; omega
    change ((-1 : ℤ) ^ n i) • ((ringDeRhamComplex gR).d c (c + 1)).hom (x i ⟨c, hc⟩) = 0
    rw [hx i ⟨c, hc⟩ (by change c + 1 < k + 1 at hbk; change c < k; omega), map_zero, smul_zero]

/-- The filtration is decreasing: `step (k + 1) ≤ step k`. -/
theorem step_succ_le {k : ℕ} {q : ℤ} : step gR n (k + 1) q ≤ step gR n k q :=
  fun _ hy i b hb => hy i b (by omega)

/-- **The filtration of `⨁_i Ω^•_{A/R}[-n_i]` by the degree of the forms.** -/
def filtration : CochainComplex.SubmoduleFiltration (complex gR n) where
  step := step gR n
  map_d_le k p q := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases h : p + 1 = q
    · rw [complex_d_apply gR n h]
      exact step_succ_le gR n (dTo_mem_step gR n h hx)
    · rw [(complex gR n).shape p q h]
      exact zero_mem _
  step_succ_le k p := step_succ_le gR n
  step_zero p := eq_top_iff.2 fun x _ i b hb => absurd hb (Nat.not_lt_zero _)
  step_eq_bot k p hp := eq_bot_iff.2 fun x hx => by
    refine (Submodule.mem_bot R).2 (funext fun i => funext fun b => hx i b ?_)
    have := b.2
    omega

/-! ### The graded pieces -/

/-- The forms of degree exactly `k` of an element of the `k`-th step. -/
def gradedProj (k : ℕ) (p : ℤ) :
    (filtration gR n).step k p →ₗ[R]
      ∀ (_ : {i : I // (n i : ℤ) + k = p}), (ringDeRhamComplex gR).X k where
  toFun x i := (x : MX gR n p) i.1 ⟨k, i.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `gradedProj` is surjective. -/
theorem gradedProj_surjective (k : ℕ) (p : ℤ) : Function.Surjective (gradedProj gR n k p) := by
  classical
  intro v
  refine ⟨⟨fun i b => if h : b.1 = k then h ▸ v ⟨i, h ▸ b.2⟩ else 0, fun i b hb => ?_⟩, ?_⟩
  · exact dite_eq_right (Nat.ne_of_lt hb)
  · funext i
    exact dite_eq_left rfl

/-- The kernel of `gradedProj` on the `k`-th step is the `(k + 1)`-st step. -/
theorem ker_gradedProj (k : ℕ) (p : ℤ) :
    LinearMap.ker (gradedProj gR n k p) =
      ((filtration gR n).step (k + 1) p).comap ((filtration gR n).step k p).subtype := by
  ext ⟨x, hx⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  refine ⟨fun h0 i b hb => ?_, fun h1 => funext fun i => h1 i.1 ⟨k, i.2⟩ (Nat.lt_succ_self k)⟩
  by_cases hbk : b.1 = k
  · obtain ⟨b, hb'⟩ := b
    change b = k at hbk
    subst hbk
    exact congrFun h0 ⟨i, hb'⟩
  · exact hx i b (by omega)

/-- **The graded pieces of `⨁_i Ω^•_{A/R}[-n_i]`, degreewise**: `gr^k M^p` is the product of the
`k`-forms over the `i` with `n_i + k = p`. -/
def gradedXEquiv (k : ℕ) (p : ℤ) :
    ((filtration gR n).graded k).X p ≃ₗ[R]
      ∀ (_ : {i : I // (n i : ℤ) + k = p}), (ringDeRhamComplex gR).X k :=
  (Submodule.quotEquivOfEq _ _ (ker_gradedProj gR n k p).symm).trans
    ((gradedProj gR n k p).quotKerEquivOfSurjective (gradedProj_surjective gR n k p))

/-- `gradedXEquiv` sends the class of `x` to its forms of degree exactly `k`. -/
theorem gradedXEquiv_mk (k : ℕ) (p : ℤ) (x : (filtration gR n).step k p) :
    gradedXEquiv gR n k p (Submodule.Quotient.mk x) = gradedProj gR n k p x :=
  rfl

/-- The graded pieces `gr^k M` have zero differential. -/
theorem graded_d_eq_zero (k : ℕ) (p q : ℤ) : ((filtration gR n).graded k).d p q = 0 := by
  by_cases h : p + 1 = q
  · refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (⟨((complex gR n).d p q).hom
      (Subtype.val (x : (filtration gR n).step k p)), _⟩ : (filtration gR n).step k q) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change ((complex gR n).d p q).hom (Subtype.val (x : (filtration gR n).step k p)) ∈
      step gR n (k + 1) q
    rw [complex_d_apply gR n h]
    exact dTo_mem_step gR n h x.2
  · exact ((filtration gR n).graded k).shape p q h

variable (A) in
/-- **The complex `⨁_i A[-n_i]`**, with zero differential. -/
abbrev unitComplex : CochainComplex (ModuleCat.{u} A) ℤ where
  X q := ModuleCat.of A (∀ (_ : {i : I // (n i : ℤ) = q}), A)
  d _ _ := 0

/-- The module `Ω^k_{A/R}`. -/
abbrev formsN (k : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR))

variable [Fintype I] [DecidableEq I]

/-- The `k`-forms of `Ω^•_{A/R}`, read as Kähler forms. -/
def castX (k : ℕ) (p : ℤ) :
    (∀ (_ : {i : I // (n i : ℤ) + k = p}), (ringDeRhamComplex gR).X k) ≃+
      ∀ (_ : {i : I // (n i : ℤ) + k = p}), ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The tensor product `Ω^k_{A/R} ⊗_A (⨁_i A[-n_i])^{p-k}`, as a product of copies of
`Ω^k_{A/R}`. -/
def tensorXEquiv (k : ℕ) (p : ℤ) :
    (formsN gR k) ⊗[A] (∀ (_ : {i : I // (n i : ℤ) = p - k}), A) ≃ₗ[A]
      ∀ (_ : {i : I // (n i : ℤ) + k = p}), ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR) :=
  (TensorProduct.piRight A A (formsN gR k) fun _ : {i : I // (n i : ℤ) = p - k} => A).trans
    ((LinearEquiv.piCongrRight fun _ => TensorProduct.rid A (formsN gR k)).trans
      (LinearEquiv.piCongrLeft' A (fun _ => formsN gR k)
        (Equiv.subtypeEquivRight fun i => by omega)))

/-- The tensor product `Ω^k_{A/R} ⊗_A (⨁_i A[-n_i])^{p-k}`, read as abelian group. -/
def tensorXAddEquiv (k : ℕ) (p : ℤ) :
    ((CochainComplex.SubmoduleFiltration.forgetAb A).obj (CochainComplex.reindex
      (((tensorLeft (formsN gR k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (unitComplex A n)) k)).X p ≃+
      ∀ (_ : {i : I // (n i : ℤ) + k = p}), ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR) where
  toFun x := tensorXEquiv gR n k p x
  invFun x := (tensorXEquiv gR n k p).symm x
  left_inv x := (tensorXEquiv gR n k p).symm_apply_apply x
  right_inv x := (tensorXEquiv gR n k p).apply_symm_apply x
  map_add' x y := map_add (tensorXEquiv gR n k p) x y

/-- `gr^k M^p`, read as abelian group, as a product of copies of `Ω^k_{A/R}`. -/
def gradedXAddEquiv (k : ℕ) (p : ℤ) :
    ((CochainComplex.SubmoduleFiltration.forgetAb R).obj ((filtration gR n).graded k)).X p ≃+
      ∀ (_ : {i : I // (n i : ℤ) + k = p}), ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR) where
  toFun x := castX gR n k p (gradedXEquiv gR n k p x)
  invFun x := (gradedXEquiv gR n k p).symm ((castX gR n k p).symm x)
  left_inv x := (gradedXEquiv gR n k p).symm_apply_apply x
  right_inv x := (gradedXEquiv gR n k p).apply_symm_apply x
  map_add' x y := map_add (gradedXEquiv gR n k p) x y

/-- `tensorXEquiv` sends `ν ⊗ e_i` to `ν` placed in the `i`-th factor. -/
theorem tensorXEquiv_tmul_single (k : ℕ) (p : ℤ) (ν : formsN gR k)
    (i : {i : I // (n i : ℤ) = p - k}) :
    tensorXEquiv gR n k p (ν ⊗ₜ Pi.single i 1) = Pi.single ⟨i.1, by have := i.2; omega⟩ ν := by
  funext i'
  simp only [tensorXEquiv, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply, LinearEquiv.piCongrLeft'_apply,
    TensorProduct.rid_tmul, Pi.single_apply]
  by_cases h : i'.1 = i.1
  · have h1 : (Equiv.subtypeEquivRight (fun j => by omega) : {i : I // (n i : ℤ) = p - k} ≃
        {i : I // (n i : ℤ) + k = p}).symm i' = i := Subtype.ext h
    have h2 : i' = ⟨i.1, by have := i.2; omega⟩ := Subtype.ext h
    rw [ite_eq_left h1, ite_eq_left h2, one_smul]
  · have h1 : (Equiv.subtypeEquivRight (fun j => by omega) : {i : I // (n i : ℤ) = p - k} ≃
        {i : I // (n i : ℤ) + k = p}).symm i' ≠ i := fun e => h (congrArg Subtype.val e)
    have h2 : i' ≠ ⟨i.1, by have := i.2; omega⟩ := fun e => h (congrArg Subtype.val e)
    rw [ite_eq_right h1, ite_eq_right h2, zero_smul]

/-- The inverse of `tensorXEquiv` sends `ν` placed in the `i`-th factor to `ν ⊗ e_i`. -/
theorem tensorXEquiv_symm_single (k : ℕ) (p : ℤ) (i : {i : I // (n i : ℤ) + k = p})
    (ν : ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR)) :
    (tensorXEquiv gR n k p).symm (Pi.single i ν) =
      (ν : formsN gR k) ⊗ₜ Pi.single (⟨i.1, by have := i.2; omega⟩ : {i : I // (n i : ℤ) = p - k})
        1 := by
  rw [LinearEquiv.symm_apply_eq, tensorXEquiv_tmul_single]

/-- **The graded pieces of `⨁_i Ω^•_{A/R}[-n_i]` as tensor products**:
`gr^k M ≅ Ω^k_{A/R} ⊗_A (⨁_i A[-n_i])` moved up by `k` degrees, as complexes of abelian groups
(both with zero differential). -/
def gradedIso (k : ℕ) :
    (CochainComplex.SubmoduleFiltration.forgetAb R).obj ((filtration gR n).graded k) ≅
      (CochainComplex.SubmoduleFiltration.forgetAb A).obj
        (CochainComplex.reindex
          (((tensorLeft (formsN gR k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (unitComplex A n)) k) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => ((gradedXAddEquiv gR n k p).trans (tensorXAddEquiv gR n k p).symm).toAddCommGrpIso)
    (by
      intro p q _
      have h1 : ((CochainComplex.SubmoduleFiltration.forgetAb R).obj
          ((filtration gR n).graded k)).d p q = 0 := by
        change (forget₂ (ModuleCat R) AddCommGrpCat).map (((filtration gR n).graded k).d p q) = 0
        rw [graded_d_eq_zero, Functor.map_zero]
      have h2 : ((CochainComplex.SubmoduleFiltration.forgetAb A).obj (CochainComplex.reindex
          (((tensorLeft (formsN gR k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (unitComplex A n)) k)).d p q = 0 := by
        change (forget₂ (ModuleCat A) AddCommGrpCat).map
          ((formsN gR k) ◁ (0 : (unitComplex A n).X (p - k) ⟶ _)) = 0
        rw [MonoidalPreadditive.whiskerLeft_zero, Functor.map_zero]
      rw [h1, h2, Limits.comp_zero, Limits.zero_comp])

omit [Fintype I] [DecidableEq I] in
/-- **The complex `⨁_i A[-n_i]` is K-flat**: it is bounded and its terms are free. -/
theorem kFlat_unitComplex [Finite I] : CochainComplex.KFlat.{u, u} (unitComplex A n) := by
  have := Fintype.ofFinite I
  have : (unitComplex A n).IsStrictlyLE ((Finset.univ.sup n : ℕ) : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    have : IsEmpty {i : I // (n i : ℤ) = q} := ⟨fun i => by
      have h1 : n i.1 ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i.1)
      have := i.2
      omega⟩
    exact ModuleCat.isZero_of_subsingleton _
  have : ∀ q : ℤ, Module.Flat A ((unitComplex A n).X q) := fun q => by
    change Module.Flat A (∀ (_ : {i : I // (n i : ℤ) = q}), A)
    infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat (unitComplex A n) ((Finset.univ.sup n : ℕ) : ℤ)

end Stacks.KatzOda.ShiftedSum

end
