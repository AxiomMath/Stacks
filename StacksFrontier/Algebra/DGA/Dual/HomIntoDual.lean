module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Topology.Instances.AddCircle.Defs
public import StacksFrontier.Algebra.DGA.Dual.Homotopy

/-!
# Homomorphisms into `A^vee[k]` and the dual complex

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and `M` a right
differential graded `A`-module. For every `k : ℤ` there are isomorphisms of abelian groups,
natural in `M`,
`Hom_{Mod_(A,d)}(M, A^vee[k]) ≅ Z^k(M^vee)` and `Hom_{K(Mod_(A,d))}(M, A^vee[k]) ≅ H^k(M^vee)`.

## Main results

* `DGAlgebra.statement_one`: `Hom_{Mod_(A,d)}(M, A^vee[k]) ≅ Z^k(M^vee)`, naturally in `M`.
* `DGAlgebra.statement_two`: `Hom_{K(Mod_(A,d))}(M, A^vee[k]) ≅ H^k(M^vee)`, naturally in `M`.

## References

* [Stacks Project, Tag 09K4](https://stacks.math.columbia.edu/tag/09K4)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Stacks.DifferentialGradedDual

universe u

variable (R : Type u) [CommRing R]

namespace DGAlgebra
variable {R}

variable {A : DGAlgebra R}

/-! ### Homomorphisms into `A^vee[k]` and cocycles of `M^vee`

By the tensor–Hom adjunction `Hom(M, A^vee) = Hom_Z(M ⊗_A A, Q/Z) = Hom_Z(M, Q/Z)`, a
homomorphism `f : M → A^vee[k]` corresponds to the cochain `x ↦ f(x)(1)` of `M^vee` of
degree `k`, and a cochain `g` corresponds to the homomorphism `x ↦ (a ↦ g(x·a))`. Under this
bijection, `f` commutes with the differentials exactly when `g` is a `k`-cocycle.

* `forwardDual`: `f ↦ (x ↦ f^{-k}(x)(1))`.
* `invHom`: `g ↦ (n ↦ x ↦ (a ↦ g(x·a)))`.
-/

/-- Evaluating a `degCastLin` transport of an element of `A^vee` at a point. -/
private theorem dualPiece_degCastLin_apply {a b : ℤ} (h : a = b) (g : DualPiece A a)
    (y : A.carrier (-b)) :
    (show A.carrier (-b) →+ QZ from degCastLin R (V := DualPiece A) h g) y
      = (show A.carrier (-a) →+ QZ from g)
          (degCast (V := fun n => A.carrier (-n)) (show b = a by rw [h]) y) := by
  subst h; rfl

namespace RightModule
variable (M : RightModule A)

/-- The cochain `x ↦ f^{-k}(x)(1)` in `(M^vee)^k` attached to a homomorphism
`f : M → A^vee[k]`. -/
noncomputable def forwardDual (k : ℤ) (f : RightModuleHom M ((dualModule A).shift k)) :
    M.dualSpace k :=
  { toFun := fun x =>
      (show A.carrier (-(-k + k)) →+ QZ from f.toFun (-k) x)
        (degCast (V := A.carrier) (show (0 : ℤ) = -(-k + k) by ring) A.one)
    map_zero' := by simp
    map_add' := by
      intro x y
      rw [map_add]
      rfl }

/-- `forwardDual k f` evaluated at `x` is `f(x)` evaluated at the unit `1` of `A`. -/
@[simp] theorem forwardDual_apply (k : ℤ) (f : RightModuleHom M ((dualModule A).shift k))
    (x : M.carrier (-k)) :
    (show M.carrier (-k) →+ QZ from M.forwardDual k f) x
      = (show A.carrier (-(-k + k)) →+ QZ from f.toFun (-k) x)
          (degCast (V := A.carrier) (show (0 : ℤ) = -(-k + k) by ring) A.one) := rfl

/-- `forwardDual` is additive in `f`. -/
theorem forwardDual_add (k : ℤ) (f g : RightModuleHom M ((dualModule A).shift k)) :
    M.forwardDual k (f + g) = M.forwardDual k f + M.forwardDual k g := by
  apply RDual.ext
  intro x
  simp only [forwardDual_apply, RightModuleHom.add_toFun, RDual.add_apply]
  rfl

/-- `forwardDual f` is a `k`-cocycle of `M^vee`: `d_{M^vee}(forwardDual f) = 0`. -/
theorem forwardDual_mem_cocyclesₛ (k : ℤ)
    (f : RightModuleHom M ((dualModule A).shift k)) :
    M.forwardDual k f ∈ M.cocyclesₛ k := by
  have hd1 : A.d 0 A.one = 0 := by
    have hleib := A.leibniz 0 0 A.one A.one
    have hc : (0 + 0) + 1 = (1 : ℤ) := by ring
    have hcast := congrArg (degCast (V := A.carrier) hc) hleib
    rw [degCast_add, degCast_smul] at hcast
    have eL : degCast (V := A.carrier) hc (A.d (0 + 0) (A.mul 0 0 A.one A.one))
        = A.d 0 A.one := by
      have hu1 := A.one_mul 0 A.one
      have h00 : (0 + 0 : ℤ) = 0 := by ring
      have harg : HEq (A.mul 0 0 A.one A.one) A.one :=
        (degCast_heq (V := A.carrier) (zero_add (0 : ℤ)) _).symm.trans (heq_of_eq hu1)
      apply eq_of_heq
      refine (degCast_heq (V := A.carrier) hc _).trans ?_
      refine HEq.trans ?_ (heq_of_eq (rfl : A.d 0 A.one = A.d 0 A.one))
      congr 1
    have eT1 : degCast (V := A.carrier) hc
        (degCast (V := A.carrier) (show (0 + 1) + 0 = (0 + 0) + 1 by ring)
          (A.mul (0 + 1) 0 (A.d 0 A.one) A.one)) = A.d 0 A.one := by
      have hu2 := A.mul_one (0 + 1) (A.d 0 A.one)
      apply eq_of_heq
      refine (degCast_heq (V := A.carrier) hc _).trans ?_
      refine (degCast_heq (V := A.carrier) _ _).trans ?_
      exact (degCast_heq (V := A.carrier) (add_zero (0 + 1)) _).symm.trans (heq_of_eq hu2)
    have eT2 : degCast (V := A.carrier) hc
        (degCast (V := A.carrier) (show 0 + (0 + 1) = (0 + 0) + 1 by ring)
          (A.mul 0 (0 + 1) A.one (A.d 0 A.one))) = A.d 0 A.one := by
      have hu3 := A.one_mul (0 + 1) (A.d 0 A.one)
      apply eq_of_heq
      refine (degCast_heq (V := A.carrier) hc _).trans ?_
      refine (degCast_heq (V := A.carrier) _ _).trans ?_
      exact (degCast_heq (V := A.carrier) (zero_add (0 + 1)) _).symm.trans (heq_of_eq hu3)
    rw [eL, eT1, Int.natAbs_zero, pow_zero, one_smul, eT2] at hcast
    have hz : A.d 0 A.one + 0 = A.d 0 A.one + A.d 0 A.one := by rw [add_zero]; exact hcast
    exact (add_left_cancel hz).symm
  rw [RightModule.cocyclesₛ, LinearMap.mem_ker]
  apply RDual.ext
  intro x
  rw [RightModule.dDual_apply]
  show _ = (show M.carrier (-(k + 1)) →+ QZ from (0 : M.dualSpace (k + 1))) x
  rw [RDual.zero_apply]
  rw [RightModule.dDownshift_apply]
  suffices hinner : (show M.carrier (-k) →+ QZ from M.forwardDual k f)
      (degCastLin R (show (-(k + 1)) + 1 = -k by ring) (M.d (-(k + 1)) x)) = 0 by
    rw [hinner, smul_zero]
  rw [forwardDual_apply]
  rw [family0_degCastLin R (fun n => f.toFun n)
        (show (-(k + 1)) + 1 = -k by ring) (M.d (-(k + 1)) x)]
  rw [f.map_d (-(k + 1)) x]
  simp only [RightModule.shift, dualModule, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe,
    ]
  have ev : ∀ {a b c : ℤ} (h : a = b) (g : DualPiece A (a + c)) (y : A.carrier (-(b + c))),
      (show A.carrier (-(b + c)) →+ QZ from
          degCastLin R (V := fun n => DualPiece A (n + c)) h g) y
        = (show A.carrier (-(a + c)) →+ QZ from g)
            (degCast (V := fun n => A.carrier (-n)) (show b + c = a + c by rw [h]) y) := by
    intro a b c h g y; subst h; rfl
  rw [ev, dualPiece_degCastLin_apply, AddMonoidHom.zsmul_apply, dualD_apply]
  rw [smul_smul]
  refine smul_eq_zero_of_right _ ?_
  rw [show (A.d (-(-(k + 1) + k + 1))
      (degCast (V := fun n => A.carrier (-n)) (show -(k + 1) + 1 + k = -(k + 1) + k + 1 by ring)
        (degCast (V := fun n => A.carrier (-n)) (show -k + k = -(k + 1) + 1 + k by ring)
          (degCast (V := A.carrier) (show (0 : ℤ) = -(-k + k) by ring) A.one)))) = 0 from ?_,
      degCastLin_zero, AddMonoidHom.map_zero]
  apply eq_of_heq
  refine HEq.trans (d_congr_heq A (show -(-(k + 1) + k + 1) = (0 : ℤ) by ring)
      (show HEq _ A.one from
        (degCast_heq _ _).trans ((degCast_heq _ _).trans (degCast_heq _ _)))) ?_
  rw [hd1]
  exact (degCast_heq (V := A.carrier) (show (0 : ℤ) + 1 = -(-(k + 1) + k + 1) + 1 by ring)
    (0 : A.carrier (0 + 1))).symm.trans (heq_of_eq (degCast_zero _))

/-- `forwardDual`, as an additive group hom `Hom(M, A^vee[k]) →+ Z^k(M^vee)`. -/
noncomputable def forwardDualHom (k : ℤ) :
    RightModuleHom M ((dualModule A).shift k) →+ M.cocycles k where
  toFun f := ⟨M.forwardDual k f, M.forwardDual_mem_cocyclesₛ k f⟩
  map_zero' := by
    apply Subtype.ext
    apply RDual.ext
    intro x
    simp only [forwardDual_apply, RightModuleHom.zero_toFun, RDual.zero_apply]
    rfl
  map_add' f g := Subtype.ext (M.forwardDual_add k f g)

/-- For a cochain `g : M^{-k} →+ Q/Z` and `x : M^n`, the element `a ↦ g(x·a)` of
`(A^vee[k])^n`. -/
noncomputable def invInner (k : ℤ) (g : M.dualSpace k) (n : ℤ) (x : M.carrier n) :
    DualPiece A (n + k) :=
  { toFun := fun a =>
      (show M.carrier (-k) →+ QZ from g)
        (degCastLin R (show n + -(n + k) = -k by ring) (M.smul n (-(n + k)) x a))
    map_zero' := by simp
    map_add' := by
      intro a b
      rw [map_add, map_add, map_add] }

/-- `invInner k g n x` evaluated at `a` is `g(x·a)`. -/
@[simp] theorem invInner_apply (k : ℤ) (g : M.dualSpace k) (n : ℤ) (x : M.carrier n)
    (a : A.carrier (-(n + k))) :
    (show A.carrier (-(n + k)) →+ QZ from M.invInner k g n x) a
      = (show M.carrier (-k) →+ QZ from g)
          (degCastLin R (show n + -(n + k) = -k by ring) (M.smul n (-(n + k)) x a)) := rfl

/-- For a cochain `g`, the `R`-linear map `M^n → (A^vee[k])^n`, `x ↦ (a ↦ g(x·a))`. -/
noncomputable def invToFun (k : ℤ) (g : M.dualSpace k) (n : ℤ) :
    M.carrier n →ₗ[R] DualPiece A (n + k) where
  toFun x := M.invInner k g n x
  map_add' x y := by
    apply DualPiece.ext'
    intro a
    rw [invInner_apply]
    show _ = (show A.carrier (-(n + k)) →+ QZ from M.invInner k g n x + M.invInner k g n y) a
    rw [AddMonoidHom.add_apply, invInner_apply, invInner_apply]
    rw [show M.smul n (-(n + k)) (x + y) a
          = M.smul n (-(n + k)) x a + M.smul n (-(n + k)) y a by rw [map_add]; rfl]
    rw [map_add, map_add]
  map_smul' r x := by
    apply DualPiece.ext'
    intro a
    rw [RingHom.id_apply]
    change (show A.carrier (-(n + k)) →+ QZ from M.invInner k g n (r • x)) a
        = (show A.carrier (-(n + k)) →+ QZ from r • M.invInner k g n x) a
    rw [invInner_apply, DualPiece.smul_apply, invInner_apply]
    congr 2
    rw [map_smul]
    change r • M.smul n (-(n + k)) x a = M.smul n (-(n + k)) x (r • a)
    rw [map_smul]

/-- `invToFun k g n x` evaluated at `a` is `g(x·a)`. -/
@[simp] theorem invToFun_apply (k : ℤ) (g : M.dualSpace k) (n : ℤ) (x : M.carrier n)
    (a : A.carrier (-(n + k))) :
    (show A.carrier (-(n + k)) →+ QZ from M.invToFun k g n x) a
      = (show M.carrier (-k) →+ QZ from g)
          (degCastLin R (show n + -(n + k) = -k by ring) (M.smul n (-(n + k)) x a)) := rfl

/-- Congruence of `M.smul` under `HEq` in both arguments. -/
theorem smul_congr_heq2 (M : RightModule A) {i i' p p' : ℤ} (hi : i = i') (hp : p = p')
    {x : M.carrier i} {x' : M.carrier i'} (hx : HEq x x')
    {a : A.carrier p} {a' : A.carrier p'} (ha : HEq a a') :
    HEq (M.smul i p x a) (M.smul i' p' x' a') := by
  subst hi; subst hp; cases hx; cases ha; rfl

/-- Reassociating `(x·a)·b` into `x·w`, where `w` is `HEq` to `a·b`, up to degree casts. -/
private theorem degCastLin_smul_smul_eq (M : RightModule A) {n m s t c : ℤ}
    (x : M.carrier n) (a : A.carrier m) (b : A.carrier s) {w : A.carrier t}
    (hw : HEq w (A.mul m s a b)) (ht : m + s = t) (e₁ : n + m + s = c) (e₂ : n + t = c) :
    degCastLin R (V := M.carrier) e₁ (M.smul (n + m) s (M.smul n m x a) b)
      = degCastLin R (V := M.carrier) e₂ (M.smul n t x w) := by
  apply eq_of_heq
  refine (degCastLin_heq R _ _).trans ?_
  refine HEq.trans ?_ (degCastLin_heq R _ _).symm
  refine (degCast_heq _ _).symm.trans ((heq_of_eq (M.smul_assoc n m s x a b)).trans ?_)
  exact smul_congr_heq2 M rfl ht HEq.rfl hw.symm

/-- If `g` is a `k`-cocycle of `M^vee`, then `invToFun k g` commutes with the differentials
of `M` and of `A^vee[k]`. -/
theorem invHom_map_d_aux (k : ℤ) (g : M.dualSpace k) (hg : g ∈ M.cocyclesₛ k)
    (n : ℤ) (x : M.carrier n) :
    M.invToFun k g (n + 1) (M.d n x)
      = ((dualModule A).shift k).d n (M.invToFun k g n x) := by
  apply DualPiece.ext'
  intro b
  rw [invToFun_apply]
  simp only [RightModule.shift, dualModule, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe,
    ]
  rw [dualPiece_degCastLin_apply]
  set b' : A.carrier (-((n + k) + 1)) :=
    degCast (V := fun j => A.carrier (-j)) (show (n + 1) + k = (n + k) + 1 by ring) b with hb'
  show (show M.carrier (-k) →+ QZ from g) ((degCastLin R (show (n + 1) + -(n + 1 + k) = -k by
      ring))
      (((M.smul (n + 1) (-(n + 1 + k))) ((M.d n) x)) b))
    = (show A.carrier (-((n + k) + 1)) →+ QZ from
        (-1 : ℤ) ^ k.natAbs • (A.dualD (n + k)) ((M.invToFun k g n) x)) b'
  rw [AddMonoidHom.zsmul_apply, dualD_apply, invToFun_apply]
  have hcoc : ∀ y : M.carrier (-(k + 1)),
      (show M.carrier (-k) →+ QZ from g)
        (degCastLin R (show (-(k + 1)) + 1 = -k by ring) (M.d (-(k + 1)) y)) = 0 := by
    intro y
    have hk : M.dDual k g = 0 := by
      rw [RightModule.cocyclesₛ, LinearMap.mem_ker] at hg; exact hg
    have happ := congrArg (fun (f : M.dualSpace (k + 1)) =>
      (show M.carrier (-(k + 1)) →+ QZ from f) y) hk
    simp only at happ
    rw [dDual_apply, dDownshift_apply, RDual.zero_apply] at happ
    have hu : ((-1 : ℤ) ^ (k + 1).natAbs) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      simp
    have := congrArg (fun z => ((-1 : ℤ) ^ (k + 1).natAbs) • z) happ
    simp only [smul_zero, smul_smul] at this
    rw [show ((-1 : ℤ) ^ (k + 1).natAbs) * ((-1 : ℤ) ^ (k + 1).natAbs)
          = ((-1 : ℤ) ^ (k + 1).natAbs) ^ 2 by ring, hu, one_smul] at this
    exact this
  set y : M.carrier (-(k + 1)) :=
    degCast (V := M.carrier) (show n + -(n + 1 + k) = -(k + 1) by ring)
      (M.smul n (-(n + 1 + k)) x b) with hy
  set Larg : M.carrier (-k) :=
    degCastLin R (show (n + 1) + -(n + 1 + k) = -k by ring)
      (M.smul (n + 1) (-(n + 1 + k)) (M.d n x) b) with hLarg
  set R2arg : M.carrier (-k) :=
    degCastLin R (show n + (-(n + 1 + k) + 1) = -k by ring)
      (M.smul n (-(n + 1 + k) + 1) x (A.d (-(n + 1 + k)) b)) with hR2arg
  have hkey : degCastLin R (show (-(k + 1)) + 1 = -k by ring) (M.d (-(k + 1)) y)
      = Larg + ((-1 : ℤ) ^ n.natAbs) • R2arg := by
    have hleib := M.leibniz n (-(n + 1 + k)) x b
    apply eq_of_heq
    refine HEq.trans (degCastLin_heq R _ _) ?_
    refine HEq.trans (d_congr_heq2 M (show -(k + 1) = n + -(n + 1 + k) by ring)
      (HEq.trans (heq_of_eq hy) (degCast_heq _ _))) ?_
    refine HEq.trans (heq_of_eq hleib) ?_
    refine add_congr_heq (a := (n + -(n + 1 + k)) + 1) (b := -k) (by ring) ?_ ?_
    · rw [hLarg]
      exact (degCast_heq _ _).trans (degCastLin_heq R _ _).symm
    · rw [hR2arg]
      refine zsmul_congr_heq (by ring) _ ?_
      exact (degCast_heq _ _).trans (degCastLin_heq R _ _).symm
  set RHSinner : M.carrier (-k) :=
    degCastLin R (show n + -(n + k) = -k by ring)
      (M.smul n (-(n + k)) x (degCastLin R (show (-(n + k + 1)) + 1 = -(n + k) by ring)
        (A.d (-(n + k + 1)) b'))) with hRHSinner
  have hRR : R2arg = RHSinner := by
    have ha : HEq (A.d (-(n + 1 + k)) b)
        (degCastLin R (show (-(n + k + 1)) + 1 = -(n + k) by ring) (A.d (-(n + k + 1)) b')) := by
      refine HEq.trans ?_ (degCastLin_heq R _ _).symm
      exact d_congr_heq A (show -(n + 1 + k) = -(n + k + 1) by ring)
        (HEq.trans (heq_of_eq hb') (degCast_heq _ _)).symm
    apply eq_of_heq
    rw [hR2arg, hRHSinner]
    refine HEq.trans (degCastLin_heq R _ _) ?_
    refine HEq.trans
      (smul_congr_heq2 M (i := n) (i' := n) (p := -(n + 1 + k) + 1) (p' := -(n + k))
        rfl (by ring) HEq.rfl ha) ?_
    exact (degCastLin_heq R _ _).symm
  have hzero := hcoc y
  rw [hkey, map_add, map_zsmul] at hzero
  have hLeq : (show M.carrier (-k) →+ QZ from g) Larg
      = -(((-1 : ℤ) ^ n.natAbs) • (show M.carrier (-k) →+ QZ from g) R2arg) := by
    rw [eq_neg_iff_add_eq_zero]; exact hzero
  rw [hLeq, hRR]
  rw [smul_smul]
  rw [show ((-1 : ℤ) ^ k.natAbs) * ((-1 : ℤ) ^ (n + k + 1).natAbs)
        = -((-1 : ℤ) ^ n.natAbs) by
    rw [show (n + k + 1 : ℤ) = (n + k) + 1 by ring, neg_one_pow_natAbs_succ,
      mul_neg, sign_recon]]
  rw [neg_smul]

/-- `invToFun k g` is right `A`-linear: `invToFun k g (x·a) = (invToFun k g x)·a`. -/
theorem invHom_map_smul_aux (k : ℤ) (g : M.dualSpace k) (n m : ℤ)
    (x : M.carrier n) (a : A.carrier m) :
    M.invToFun k g (n + m) (M.smul n m x a)
      = ((dualModule A).shift k).smul n m (M.invToFun k g n x) a := by
  apply DualPiece.ext'
  intro b
  rw [RightModule.invToFun_apply]
  simp only [RightModule.shift, LinearMap.comp_apply, LinearMap.llcomp_apply,
    LinearEquiv.coe_coe, dualModule]
  rw [dualPiece_degCastLin_apply]
  rw [dualSmul_apply]
  rw [RightModule.invToFun_apply, mulMap_apply]
  congr 1
  refine M.degCastLin_smul_smul_eq x a b ?_ ?_ _ _
  · exact (degCastLin_heq R _ _).trans
      (mul_arg_congr m a (by ring) (degCast_heq (V := fun j => A.carrier (-j)) _ b))
  all_goals ring

/-- The homomorphism `M → A^vee[k]`, `x ↦ (a ↦ g(x·a))`, attached to a `k`-cocycle `g` of
`M^vee`. -/
noncomputable def invHom (k : ℤ) (g : M.dualSpace k) (hg : g ∈ M.cocyclesₛ k) :
    RightModuleHom M ((dualModule A).shift k) where
  toFun n := M.invToFun k g n
  map_smul n m x a := M.invHom_map_smul_aux k g n m x a
  map_d n x := M.invHom_map_d_aux k g hg n x

/-- The components of `invHom k g hg` are `invToFun k g`. -/
@[simp] theorem invHom_toFun (k : ℤ) (g : M.dualSpace k) (hg : g ∈ M.cocyclesₛ k)
    (n : ℤ) (x : M.carrier n) :
    (M.invHom k g hg).toFun n x = M.invToFun k g n x := rfl

/-- For a `k`-cocycle `g` of `M^vee`, `forwardDual k (invHom k g hg) = g`. -/
theorem forwardDual_invHom (k : ℤ) (g : M.dualSpace k) (hg : g ∈ M.cocyclesₛ k) :
    M.forwardDual k (M.invHom k g hg) = g := by
  apply RDual.ext
  intro x
  simp only [forwardDual_apply, invHom_toFun, invToFun_apply]
  congr 1
  apply eq_of_heq
  refine HEq.trans (degCastLin_heq R _ _) ?_
  refine HEq.trans (smul_congr_heq2 M (by ring) (by ring) HEq.rfl
    (degCast_heq (V := A.carrier) _ A.one)) ?_
  refine HEq.trans (degCast_heq (add_zero (-k)) _).symm ?_
  exact heq_of_eq (M.smul_one (-k) x)

/-- For a homomorphism `f : M → A^vee[k]`, `invHom k (forwardDual k f) _ = f`. -/
theorem invHom_forwardDual (k : ℤ) (f : RightModuleHom M ((dualModule A).shift k)) :
    M.invHom k (M.forwardDual k f) (M.forwardDual_mem_cocyclesₛ k f) = f := by
  apply RightModuleHom.ext
  intro n x
  apply DualPiece.ext'
  intro a
  simp only [invHom_toFun, invToFun_apply, forwardDual_apply]
  rw [family0_degCastLin R (fun n => f.toFun n) (show n + -(n + k) = -k by ring)
    (M.smul n (-(n + k)) x a)]
  rw [f.map_smul n (-(n + k)) x a]
  have evS : ∀ {p q : ℤ} (h : p = q) (gg : ((dualModule A).shift k).carrier p)
      (y : A.carrier (-(q + k))),
      (show A.carrier (-(q + k)) →+ QZ from
          degCastLin R (V := ((dualModule A).shift k).carrier) h gg) y
        = (show A.carrier (-(p + k)) →+ QZ from gg)
            (degCast (V := fun j => A.carrier (-(j + k))) (show q = p by rw [h]) y) := by
    intro p q h gg y; subst h; rfl
  rw [evS]
  simp only [RightModule.shift, LinearMap.comp_apply, LinearMap.llcomp_apply,
    LinearEquiv.coe_coe, dualModule]
  rw [dualPiece_degCastLin_apply, dualSmul_apply, mulMap_apply]
  refine congrArg _ ?_
  apply eq_of_heq
  refine HEq.trans (degCastLin_heq R _ _) ?_
  refine HEq.trans (mul_arg_congr (-(n + k)) a (show -(n + k + -(n + k)) = 0 by ring)
    (HEq.trans (degCast_heq _ _) (HEq.trans (degCast_heq _ _) (degCast_heq _ _)))) ?_
  exact (degCast_heq _ _).symm.trans (heq_of_eq (A.mul_one (-(n + k)) a))

/-- The additive group isomorphism `Φ_M : Hom_{Mod_(A,d)}(M, A^vee[k]) ≃+ Z^k(M^vee)`, given by
`forwardDual` with inverse `invHom`. -/
noncomputable def Phi (k : ℤ) :
    RightModuleHom M ((dualModule A).shift k) ≃+ M.cocycles k where
  toFun := M.forwardDualHom k
  invFun c := M.invHom k (c : M.dualSpace k) c.2
  left_inv f := M.invHom_forwardDual k f
  right_inv c := Subtype.ext (M.forwardDual_invHom k (c : M.dualSpace k) c.2)
  map_add' f g := (M.forwardDualHom k).map_add f g

end RightModule

variable (A)

/-- Naturality of `Φ`: for `φ : M' → M` and `f : M → A^vee[k]`, precomposing `f` by `φ` and
then applying `Φ_{M'}` equals applying `Φ_M` and then the induced map `cocyclesMap φ` on
cocycles. -/
theorem Phi_naturality (k : ℤ) {M' M : RightModule A} (φ : RightModuleHom M' M)
    (f : RightModuleHom M ((dualModule A).shift k)) :
    M'.Phi k (precomp φ ((dualModule A).shift k) f)
      = cocyclesMap φ k (M.Phi k f) := by
  apply Subtype.ext
  apply RDual.ext
  intro x
  show (show M'.carrier (-k) →+ QZ from (M'.forwardDual k (precomp φ ((dualModule A).shift k)
      f))) x
      = (show M'.carrier (-k) →+ QZ from (dualMap φ k (M.forwardDual k f))) x
  rw [dualMap, RDual.precompₗ_apply, RightModule.forwardDual_apply, RightModule.forwardDual_apply]
  rfl

/-- There is an isomorphism of abelian groups
`Hom_{Mod_(A,d)}(M, A^vee[k]) ~= Z^k(M^vee)`, natural in `M`: it is compatible with
precomposition by an arbitrary morphism `phi : M' -> M` on the left and the induced
map `phi^vee` of dual complexes on the right. -/
@[stacks 09K4]
theorem statement_one (k : ℤ) :
    ∃ Φ : ∀ M : RightModule A,
        RightModuleHom M ((dualModule A).shift k) ≃+ M.cocycles k,
      ∀ {M' M : RightModule A} (φ : RightModuleHom M' M)
        (f : RightModuleHom M ((dualModule A).shift k)),
        Φ M' (precomp φ ((dualModule A).shift k) f)
          = cocyclesMap φ k (Φ M f) :=
  ⟨fun M => M.Phi k, fun φ f => Phi_naturality A k φ f⟩

/-! ### Homotopy classes of homomorphisms into `A^vee[k]` and cohomology of `M^vee`

The isomorphism `Φ_M : Hom(M, A^vee[k]) ≃+ Z^k(M^vee)` carries the subgroup of
nullhomotopic maps onto the subgroup of coboundaries, so it descends to an isomorphism
`Ψ_M : Hom_{K}(M, A^vee[k]) ≃+ H^k(M^vee)`.
-/

variable {A}

/-- If `f : M → A^vee[k]` is nullhomotopic, then `forwardDual f` is a coboundary of `M^vee`. -/
theorem forwardDual_mem_coboundariesₛ_of_nullhomotopic {M : RightModule A} (k : ℤ)
    {f : RightModuleHom M ((dualModule A).shift k)} (H : Homotopy f 0) :
    M.forwardDual k f ∈ M.coboundariesₛ k := by
  let idN : RightModuleHom ((dualModule A).shift k) ((dualModule A).shift k) :=
    { toFun := fun _ => LinearMap.id
      map_smul := by intro n m x a; rfl
      map_d := by intro n x; rfl }
  have heq : M.forwardDual k f = dualMap f k (((dualModule A).shift k).forwardDual k idN) :=
    RDual.ext fun _ => rfl
  rw [heq]
  exact dualMap_nullhomotopic_mem_coboundariesₛ H k
    (((dualModule A).shift k).forwardDual_mem_cocyclesₛ k idN)

/-- If a `k`-cocycle `g` of `M^vee` is a coboundary, then `invHom k g hg` is nullhomotopic. -/
theorem invHom_nullhomotopic_of_coboundary {M : RightModule A} (k : ℤ)
    (g : M.dualSpace k) (hg : g ∈ M.cocyclesₛ k) (hb : g ∈ M.coboundariesₛ k) :
    Homotopic (M.invHom k g hg) 0 := by
  rcases hb with ⟨z, ⟨g₀, hg0⟩, hz⟩
  set g₀' : M.dualSpace (k - 1) := ((-1 : ℤ) ^ k.natAbs) • g₀ with hg0'
  set H : ∀ n, M.carrier n →ₗ[R] ((dualModule A).shift k).carrier (n - 1) :=
    fun n => (degCastLin R (show n + (k - 1) = n - 1 + k by ring)
      (V := fun j => DualPiece A j)).toLinearMap.comp (M.invToFun (k - 1) g₀' n) with hH
  refine ⟨{ toFun := H, map_smul := ?_, homotopy := ?_ }⟩
  · intro n m x a
    apply DualPiece.ext'
    intro b
    have Hap : ∀ (j : ℤ) (y : M.carrier j),
        H j y = degCastLin R (show j + (k - 1) = j - 1 + k by ring)
          (V := fun i => DualPiece A i) (M.invToFun (k - 1) g₀' j y) := fun j y => rfl
    rw [Hap, dualPiece_degCastLin_apply, RightModule.invToFun_apply]
    have ev1 : ∀ {a b : ℤ} (h : a = b) (gg : DualPiece A (a + k)) (y : A.carrier (-(b + k))),
        (show A.carrier (-(b + k)) →+ QZ from
            degCast (V := fun j => DualPiece A (j + k)) h gg) y
          = (show A.carrier (-(a + k)) →+ QZ from gg)
              (degCast (V := fun j => A.carrier (-(j + k))) (show b = a by rw [h]) y) := by
      intro a b h gg y; subst h; rfl
    simp only [RightModule.shift, LinearMap.comp_apply, LinearMap.llcomp_apply,
      LinearEquiv.coe_coe]
    rw [ev1]
    simp only [dualModule]
    rw [dualPiece_degCastLin_apply, dualSmul_apply]
    simp only [hH, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [dualPiece_degCastLin_apply, RightModule.invToFun_apply, mulMap_apply]
    congr 1
    refine M.degCastLin_smul_smul_eq x a _ ?_ ?_ _ _
    · refine (degCast_heq _ _).trans
        ((degCastLin_heq R _ _).trans (mul_arg_congr m a (by ring) ?_))
      exact (degCast_heq (V := fun j => A.carrier (-j)) _ _).trans
        ((degCast_heq (V := fun j => A.carrier (-(j + k))) _ b).trans
          (degCast_heq (V := fun j => A.carrier (-j)) _ _).symm)
    all_goals ring
  · intro n x
    simp only [RightModule.invHom_toFun, RightModuleHom.zero_toFun, sub_zero]
    apply DualPiece.ext'
    intro b
    have hgdef : g = degCastLin R (show k - 1 + 1 = k by ring)
        (V := fun j => M.dualSpace j) (M.dDual (k - 1) g₀) := by rw [hg0]; exact hz.symm
    rw [RightModule.invToFun_apply, hgdef]
    rw [dualSpace_degCastLin_apply (N := M) (show k - 1 + 1 = k by ring)]
    rw [RightModule.dDual_apply, RightModule.dDownshift_apply]
    rw [show (show A.carrier (-(n + k)) →+ QZ from
          degCast (show (n - 1) + 1 = n by ring) (((A.dualModule.shift k).d (n - 1)) ((H n) x))
          + degCast (show (n + 1) - 1 = n by ring) ((H (n + 1)) ((M.d n) x))) b
        = (show A.carrier (-(n + k)) →+ QZ from
            degCast (show (n - 1) + 1 = n by ring) (((A.dualModule.shift k).d (n - 1)) ((H n) x))) b
          + (show A.carrier (-(n + k)) →+ QZ from
            degCast (show (n + 1) - 1 = n by ring) ((H (n + 1)) ((M.d n) x))) b from rfl]
    have evN : ∀ {a b : ℤ} (h : a = b) (gg : (A.dualModule.shift k).carrier a)
        (y : A.carrier (-(b + k))),
        (show A.carrier (-(b + k)) →+ QZ from
            degCast (V := fun j => (A.dualModule.shift k).carrier j) h gg) y
          = (show A.carrier (-(a + k)) →+ QZ from gg)
              (degCast (V := fun j => A.carrier (-(j + k))) (show b = a by rw [h]) y) := by
      intro a b h gg y; subst h; rfl
    have Hap : ∀ (j : ℤ) (y : M.carrier j),
        H j y = degCastLin R (show j + (k - 1) = j - 1 + k by ring)
          (V := fun i => DualPiece A i) (M.invToFun (k - 1) g₀' j y) := fun j y => rfl
    rw [evN (show (n + 1) - 1 = n by ring), Hap (n + 1) (M.d n x), dualPiece_degCastLin_apply,
      RightModule.invToFun_apply]
    rw [evN (show (n - 1) + 1 = n by ring)]
    simp only [RightModule.shift, LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe]
    simp only [dualModule]
    rw [dualPiece_degCastLin_apply, AddMonoidHom.zsmul_apply, dualD_apply]
    simp only [hH, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [dualPiece_degCastLin_apply, RightModule.invToFun_apply]
    rw [hg0']
    have hsmulg : ∀ (w : M.carrier (-(k - 1))),
        (show M.carrier (-(k - 1)) →+ QZ from ((-1 : ℤ) ^ k.natAbs) • g₀) w
          = ((-1 : ℤ) ^ k.natAbs) • (show M.carrier (-(k - 1)) →+ QZ from g₀) w := by
      intro w; rfl
    rw [hsmulg, hsmulg]
    rw [degCastLin_trans]
    have hkey : degCastLin R (show -(k - 1 + 1) + 1 = -(k - 1) by ring)
          (M.d (-(k - 1 + 1)) (degCastLin R (show n + -(n + k) = -(k - 1 + 1) by ring)
            (M.smul n (-(n + k)) x b)))
        = degCastLin R (show (n + 1) + -(n + 1 + (k - 1)) = -(k - 1) by ring)
            (M.smul (n + 1) (-(n + 1 + (k - 1))) (M.d n x)
              (degCast (V := fun j => A.carrier (-j)) (show n + k = n + 1 + (k - 1) by ring) b))
          + ((-1 : ℤ) ^ n.natAbs) • degCastLin R (show n + (-(n + k) + 1) = -(k - 1) by ring)
            (M.smul n (-(n + k) + 1) x (A.d (-(n + k)) b)) := by
      have hleib := M.leibniz n (-(n + k)) x b
      apply eq_of_heq
      refine HEq.trans (degCastLin_heq R _ _) ?_
      refine HEq.trans (d_congr_heq2 M (show -(k - 1 + 1) = n + -(n + k) by ring)
        (degCastLin_heq R _ _)) ?_
      refine HEq.trans (heq_of_eq hleib) ?_
      refine add_congr_heq (a := (n + -(n + k)) + 1) (b := -(k - 1)) (by ring) ?_ ?_
      · refine HEq.trans (degCast_heq _ _) ?_
        refine HEq.trans ?_ (degCastLin_heq R _ _).symm
        refine RightModule.smul_congr_heq2 M (i := n + 1) (i' := n + 1)
          (p := -(n + k)) (p' := -(n + 1 + (k - 1))) (by ring) (by ring) HEq.rfl ?_
        exact (degCast_heq (V := fun j => A.carrier (-j)) _ _).symm
      · refine zsmul_congr_heq (by ring) _ ?_
        refine HEq.trans (degCast_heq _ _) ?_
        exact (degCastLin_heq R _ _).symm
    rw [hkey]
    rw [map_add, map_zsmul, smul_add, smul_smul]
    rw [add_comm]
    congr 1
    · rw [show (k - 1 + 1).natAbs = k.natAbs by congr 1; ring]
      rw [show (n - 1 + k + 1).natAbs = (n + k).natAbs by congr 1; ring]
      rw [smul_smul, smul_smul]
      have hc : (-1 : ℤ) ^ k.natAbs * (-1) ^ n.natAbs
          = (-1) ^ k.natAbs * (-1) ^ (n + k).natAbs * (-1) ^ k.natAbs := by
        rw [_root_.mul_comm ((-1 : ℤ) ^ k.natAbs) ((-1 : ℤ) ^ (n + k).natAbs),
          _root_.mul_assoc, neg_one_pow_natAbs_add k k]
        have h2 : ((-1 : ℤ) ^ (k + k).natAbs) = 1 := by
          rw [show (k + k : ℤ) = 2 * k by ring, Int.natAbs_mul,
            show (2 : ℤ).natAbs = 2 from rfl, pow_mul]
          simp
        rw [h2, _root_.mul_one, _root_.mul_comm, neg_one_pow_natAbs_add]
      rw [hc]
      apply congrArg
      apply congrArg
      apply eq_of_heq
      refine HEq.trans (degCastLin_heq R _ _) ?_
      refine HEq.trans ?_ (degCastLin_heq R _ _).symm
      refine RightModule.smul_congr_heq2 M rfl (by ring) HEq.rfl ?_
      refine HEq.trans ?_ (degCast_heq (V := fun j => A.carrier (-j)) _ _).symm
      refine HEq.trans ?_ (degCastLin_heq R _ _).symm
      refine d_congr_heq A (show -(n + k) = -(n - 1 + k + 1) by ring) ?_
      apply HEq.symm
      apply HEq.trans (degCast_heq (V := fun j => A.carrier (-j)) _ _)
      apply degCast_heq
    · rw [show (k - 1 + 1).natAbs = k.natAbs by congr 1; ring]
      congr 2
      apply eq_of_heq
      refine HEq.trans (degCastLin_heq R _ _) ?_
      refine HEq.trans ?_ (degCastLin_heq R _ _).symm
      refine RightModule.smul_congr_heq2 M rfl (by ring) HEq.rfl ?_
      refine HEq.trans (degCast_heq (V := fun j => A.carrier (-j)) _ _) ?_
      apply HEq.symm
      apply HEq.trans (degCast_heq (V := fun j => A.carrier (-j)) _ _)
      apply degCast_heq

namespace RightModule
variable (M : RightModule A)

/-- The map `Hom_{K}(M, A^vee[k]) →+ H^k(M^vee)` induced by `forwardDualHom` on the
quotients. -/
noncomputable def PsiFwd (k : ℤ) :
    homotopyHom M ((dualModule A).shift k) →+ M.cohomology k :=
  QuotientAddGroup.map (nullhomotopic M ((dualModule A).shift k))
    ((M.coboundaries k).addSubgroupOf (M.cocycles k)) (M.forwardDualHom k)
    (by
      intro f hf
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      exact forwardDual_mem_coboundariesₛ_of_nullhomotopic k hf.some)

/-- `invHom`, as an additive group hom `Z^k(M^vee) →+ Hom(M, A^vee[k])`. -/
noncomputable def invCocycleHom (k : ℤ) :
    M.cocycles k →+ RightModuleHom M ((dualModule A).shift k) where
  toFun c := M.invHom k (c : M.dualSpace k) c.2
  map_zero' := by
    apply RightModuleHom.ext
    intro n x
    apply DualPiece.ext'
    intro a
    simp only [invHom_toFun, invToFun_apply, RightModuleHom.zero_toFun,
      ZeroMemClass.coe_zero, RDual.zero_apply]
  map_add' c d := by
    apply RightModuleHom.ext
    intro n x
    apply DualPiece.ext'
    intro a
    change (show A.carrier (-(n + k)) →+ QZ from
        (M.invHom k (↑(c + d)) (c + d).2).toFun n x) a
      = (show A.carrier (-(n + k)) →+ QZ from
          (M.invHom k (↑c) c.2).toFun n x + (M.invHom k (↑d) d.2).toFun n x) a
    rw [AddMonoidHom.add_apply]
    simp only [invHom_toFun, invToFun_apply, AddSubgroup.coe_add, RDual.add_apply]

/-- The map `H^k(M^vee) →+ Hom_{K}(M, A^vee[k])` induced by `invCocycleHom` on the
quotients. -/
noncomputable def PsiInv (k : ℤ) :
    M.cohomology k →+ homotopyHom M ((dualModule A).shift k) :=
  QuotientAddGroup.map ((M.coboundaries k).addSubgroupOf (M.cocycles k))
    (nullhomotopic M ((dualModule A).shift k)) (M.invCocycleHom k)
    (by
      intro c hc
      rw [AddSubgroup.mem_comap]
      rw [AddSubgroup.mem_addSubgroupOf] at hc
      exact invHom_nullhomotopic_of_coboundary k (c : M.dualSpace k) c.2 hc)

/-- The additive group isomorphism `Ψ_M : Hom_{K(Mod_(A,d))}(M, A^vee[k]) ≃+ H^k(M^vee)`
induced by `Φ_M` on the quotients. -/
noncomputable def Psi (k : ℤ) :
    homotopyHom M ((dualModule A).shift k) ≃+ M.cohomology k where
  toFun := M.PsiFwd k
  invFun := M.PsiInv k
  left_inv := by
    intro ξ
    induction ξ using QuotientAddGroup.induction_on with
    | _ f =>
      show M.PsiInv k (M.PsiFwd k (QuotientAddGroup.mk f)) = QuotientAddGroup.mk f
      simp only [PsiFwd, PsiInv]
      exact congrArg _ (M.invHom_forwardDual k f)
  right_inv := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | _ c₀ =>
      show M.PsiFwd k (M.PsiInv k (QuotientAddGroup.mk c₀)) = QuotientAddGroup.mk c₀
      simp only [PsiInv, PsiFwd]
      refine congrArg _ (Subtype.ext ?_)
      exact M.forwardDual_invHom k (c₀ : M.dualSpace k) c₀.2
  map_add' := (M.PsiFwd k).map_add

end RightModule

variable (A)

/-- Naturality of `Ψ`: for `φ : M' → M`, applying `Ψ_{M'}` after `homotopyPrecomp φ` equals
applying `cohomologyMap φ k` after `Ψ_M`. -/
theorem Psi_naturality (k : ℤ) {M' M : RightModule A} (φ : RightModuleHom M' M)
    (ξ : homotopyHom M ((dualModule A).shift k)) :
    M'.Psi k (homotopyPrecomp φ ((dualModule A).shift k) ξ)
      = cohomologyMap φ k (M.Psi k ξ) := by
  induction ξ using QuotientAddGroup.induction_on with
  | _ f =>
    show M'.PsiFwd k (homotopyPrecomp φ ((dualModule A).shift k) (QuotientAddGroup.mk f))
      = cohomologyMap φ k (M.PsiFwd k (QuotientAddGroup.mk f))
    simp only [homotopyPrecomp, RightModule.PsiFwd]
    exact congrArg _ (Phi_naturality A k φ f)

/-- There is an isomorphism of abelian groups `Hom_{K(Mod_(A,d))}(M, A^vee[k]) ~= H^k(M^vee)`,
natural in `M` over the homotopy category: there is a family of group isomorphisms `Ψ M` such
that, for every morphism `phi : M' -> M`, the precomposition map `homotopyPrecomp phi` on
homotopy-category Hom groups corresponds under `Ψ` to the map `cohomologyMap phi k` induced on
cohomology by the dual chain map `dualMap phi`; moreover `cohomologyMap phi k` depends only on
the homotopy class of `phi`. -/
@[stacks 09K4]
theorem statement_two (k : ℤ) :
    ∃ Ψ : ∀ M : RightModule A, homotopyHom M ((dualModule A).shift k) ≃+ M.cohomology k,
      (∀ {M' M : RightModule A} (φ : RightModuleHom M' M)
          (ξ : homotopyHom M ((dualModule A).shift k)),
          Ψ M' (homotopyPrecomp φ ((dualModule A).shift k) ξ)
            = cohomologyMap φ k (Ψ M ξ))
      ∧ (∀ {M' M : RightModule A} {φ ψ : RightModuleHom M' M},
          Homotopic φ ψ → cohomologyMap φ k = cohomologyMap ψ k) := by
  refine ⟨fun M => M.Psi k, ?_, ?_⟩
  · intro M' M φ ξ
    exact Psi_naturality A k φ ξ
  · intro M' M φ ψ h
    exact cohomologyMap_congr_of_homotopic h.some k

end DGAlgebra

end Stacks.DifferentialGradedDual
