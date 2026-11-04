module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Topology.Instances.AddCircle.Defs
public import StacksFrontier.Algebra.DGA.Dual.DualModule

/-!
# Homotopies and functoriality of the dual complex

Homotopies between homomorphisms of right differential graded modules, the homomorphism
groups of the homotopy category, and the maps `Z^k(M^vee) → Z^k((M')^vee)` and
`H^k(M^vee) → H^k((M')^vee)` induced by a homomorphism `M' → M`. The induced map on cohomology
depends only on the homotopy class of the homomorphism.

## Main definitions

* `DGAlgebra.Homotopy`, `DGAlgebra.homotopyHom`: homotopies between homomorphisms, and the
  homomorphism groups of the homotopy category.
* `DGAlgebra.cohomologyMap`: the map `H^k(M^vee) → H^k((M')^vee)` induced by a homomorphism
  `M' → M`.

## Main results

* `DGAlgebra.cohomologyMap_congr_of_homotopic`: homotopic homomorphisms induce the same map on
  the cohomology of the dual complexes.

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

/-! ### Homotopies and the homotopy category -/

/-- A homotopy from `f` to `g`: a degree-`-1`, `R`-linear, right `A`-linear family
`h : M^n -> N^{n-1}` with `f - g = d_N . h + h . d_M`. -/
structure Homotopy {M N : RightModule A} (f g : RightModuleHom M N) where
  /-- The component `h : M^n -> N^{n-1}` in degree `n`. -/
  toFun : ∀ n, M.carrier n →ₗ[R] N.carrier (n - 1)
  map_smul : ∀ (n m : ℤ) (x : M.carrier n) (a : A.carrier m),
    toFun (n + m) (M.smul n m x a) = degCast (by ring) (N.smul (n - 1) m (toFun n x) a)
  homotopy : ∀ (n : ℤ) (x : M.carrier n),
    f.toFun n x - g.toFun n x
      = degCast (show (n - 1) + 1 = n by ring) (N.d (n - 1) (toFun n x))
        + degCast (show (n + 1) - 1 = n by ring) (toFun (n + 1) (M.d n x))

/-- `f` and `g` are homotopic. -/
def Homotopic {M N : RightModule A} (f g : RightModuleHom M N) : Prop := Nonempty (Homotopy f g)

/-- The zero homotopy from `0` to `0`. -/
def Homotopy.zero {M N : RightModule A} : Homotopy (0 : RightModuleHom M N) 0 where
  toFun _ := 0
  map_smul := by
    intro n m x a
    simp only [LinearMap.zero_apply, map_zero, degCast_zero]
  homotopy := by
    intro n x
    simp only [RightModuleHom.zero_toFun, sub_zero, LinearMap.zero_apply, map_zero, degCast_zero,
      add_zero]

/-- Add two homotopies (to `0`). -/
def Homotopy.add {M N : RightModule A} {f g : RightModuleHom M N}
    (hf : Homotopy f 0) (hg : Homotopy g 0) : Homotopy (f + g) 0 where
  toFun n := hf.toFun n + hg.toFun n
  map_smul := by
    intro n m x a
    simp only [LinearMap.add_apply, hf.map_smul, hg.map_smul, map_add, ← degCast_add]
  homotopy := by
    intro n x
    have hf' := hf.homotopy n x
    have hg' := hg.homotopy n x
    simp only [RightModuleHom.add_toFun, RightModuleHom.zero_toFun, sub_zero] at hf' hg' ⊢
    simp only [LinearMap.add_apply, map_add, degCast_add]
    rw [hf', hg']; abel

/-- Negate a homotopy (to `0`). -/
def Homotopy.neg {M N : RightModule A} {f : RightModuleHom M N}
    (hf : Homotopy f 0) : Homotopy (-f) 0 where
  toFun n := -hf.toFun n
  map_smul := by
    intro n m x a
    simp only [LinearMap.neg_apply, hf.map_smul, map_neg, ← degCast_neg]
  homotopy := by
    intro n x
    have hf' := hf.homotopy n x
    simp only [RightModuleHom.neg_toFun, RightModuleHom.zero_toFun, sub_zero] at hf' ⊢
    simp only [LinearMap.neg_apply, map_neg, degCast_neg]
    rw [hf']; abel

/-- The subgroup of nullhomotopic maps `M -> N` (those homotopic to `0`). -/
def nullhomotopic (M N : RightModule A) : AddSubgroup (RightModuleHom M N) where
  carrier := {f | Homotopic f 0}
  zero_mem' := ⟨Homotopy.zero⟩
  add_mem' := fun {_ _} hf hg => ⟨Homotopy.add hf.some hg.some⟩
  neg_mem' := fun {_} hf => ⟨Homotopy.neg hf.some⟩

/-- The homomorphism group of the homotopy category,
`Hom_{K(Mod_(A,d))}(M, N) = Hom_{Mod_(A,d)}(M, N) / (nullhomotopic maps)`. -/
def homotopyHom (M N : RightModule A) : Type u :=
  (RightModuleHom M N) ⧸ (nullhomotopic M N)

/-- The quotient group structure on `Hom_{K(Mod_(A,d))}(M, N)`. -/
instance (M N : RightModule A) : AddCommGroup (homotopyHom M N) := by
  unfold homotopyHom; infer_instance

/-! ### Functoriality -/

/-- Precomposition `f |-> f . phi` on the contravariant Hom-functor `Hom(-, N)`. -/
def precomp {M' M : RightModule A} (φ : RightModuleHom M' M) (N : RightModule A) :
    RightModuleHom M N →+ RightModuleHom M' N where
  toFun f := f.comp φ
  map_zero' := by ext n x; simp [RightModuleHom.comp]
  map_add' f g := by ext n x; simp [RightModuleHom.comp]

/-- A homotopy from `f` to `0` induces a homotopy from `f.comp phi` to `0`. -/
def homotopyPrecompAux {M' M : RightModule A} (φ : RightModuleHom M' M) (N : RightModule A)
    {f : RightModuleHom M N} (hf : Homotopy f 0) : Homotopy (f.comp φ) 0 where
  toFun n := (hf.toFun n).comp (φ.toFun n)
  map_smul := by
    intro n m x a
    simp only [LinearMap.comp_apply]
    rw [φ.map_smul, hf.map_smul]
  homotopy := by
    intro n x
    simp only [RightModuleHom.comp_toFun, RightModuleHom.zero_toFun, sub_zero, LinearMap.comp_apply]
    have hh := hf.homotopy n (φ.toFun n x)
    simp only [RightModuleHom.zero_toFun, sub_zero] at hh
    rw [hh]
    congr 2
    rw [φ.map_d]

/-- Precomposition with `phi` on the homotopy category, as an additive group hom
`Hom_{K}(M, N) -> Hom_{K}(M', N)`. -/
noncomputable def homotopyPrecomp {M' M : RightModule A} (φ : RightModuleHom M' M)
    (N : RightModule A) : homotopyHom M N →+ homotopyHom M' N :=
  QuotientAddGroup.map (nullhomotopic M N) (nullhomotopic M' N) (precomp φ N)
    (by
      intro f hf
      exact ⟨homotopyPrecompAux φ N hf.some⟩)

/-- The induced map of dual complexes `phi^vee : M^vee -> (M')^vee` in degree `k`
(precomposition with `phi` on the underlying complexes), as an `R`-linear map. -/
noncomputable def dualMap {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ) :
    M.dualSpace k →ₗ[R] M'.dualSpace k :=
  RDual.precompₗ (φ.toFun (-k))

/-- `phi^vee` commutes with the dual differentials. -/
theorem dualMap_comm_dDual {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ)
    (f : M.dualSpace k) :
    M'.dDual k (dualMap φ k f) = dualMap φ (k + 1) (M.dDual k f) := by
  apply RDual.ext
  intro x
  rw [RightModule.dDual_apply]
  show _ = (show M'.carrier (-(k + 1)) →+ QZ from
      RDual.precompₗ (φ.toFun (-(k + 1))) (M.dDual k f)) x
  rw [RDual.precompₗ_apply, RightModule.dDual_apply]
  show ((-1 : ℤ) ^ (k + 1).natAbs) • (RDual.toFun (dualMap φ k f)) (M'.dDownshift k x)
      = ((-1 : ℤ) ^ (k + 1).natAbs) • (RDual.toFun f) (M.dDownshift k (φ.toFun (-(k + 1)) x))
  congr 1
  show (RDual.toFun f) (φ.toFun (-k) (M'.dDownshift k x))
      = (RDual.toFun f) (M.dDownshift k (φ.toFun (-(k + 1)) x))
  congr 1
  rw [RightModule.dDownshift_apply, RightModule.dDownshift_apply]
  rw [family0_degCastLin R φ.toFun, φ.map_d]

/-- `phi^vee` carries cocycles to cocycles: if `f` is a `k`-cocycle of `M^vee` then
`dualMap phi k f` is a `k`-cocycle of `(M')^vee`. -/
theorem dualMap_mem_cocyclesₛ {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ)
    {f : M.dualSpace k} (hf : f ∈ M.cocyclesₛ k) : dualMap φ k f ∈ M'.cocyclesₛ k := by
  rw [RightModule.cocyclesₛ, LinearMap.mem_ker] at hf ⊢
  rw [dualMap_comm_dDual, hf, map_zero]

/-- `phi^vee` carries coboundaries to coboundaries. -/
theorem dualMap_mem_coboundariesₛ {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ)
    {f : M.dualSpace k} (hf : f ∈ M.coboundariesₛ k) : dualMap φ k f ∈ M'.coboundariesₛ k := by
  rcases hf with ⟨z, ⟨w, hw⟩, hz⟩
  subst hz
  subst hw
  refine ⟨M'.dDual (k - 1) (dualMap φ (k - 1) w), ⟨dualMap φ (k - 1) w, rfl⟩, ?_⟩
  show (degCastLin R (show k - 1 + 1 = k by ring) (V := fun n => M'.dualSpace n))
        (M'.dDual (k - 1) (dualMap φ (k - 1) w))
      = dualMap φ k ((degCastLin R (show k - 1 + 1 = k by ring) (V := fun n => M.dualSpace n))
          (M.dDual (k - 1) w))
  rw [family0_degCastLin R (fun n => dualMap φ n) (show k - 1 + 1 = k by ring)]
  rw [dualMap_comm_dDual]

/-- `phi^vee` restricted to cocycles, as an additive group hom
`Z^k(M^vee) -> Z^k((M')^vee)`. -/
noncomputable def cocyclesMap {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ) :
    M.cocycles k →+ M'.cocycles k where
  toFun := fun f => ⟨dualMap φ k (f : M.dualSpace k), dualMap_mem_cocyclesₛ φ k f.2⟩
  map_zero' := by ext; simp [RightModule.cocycles]
  map_add' f g := by ext; simp [RightModule.cocycles]

/-- The underlying cochain of `cocyclesMap phi k f` is `dualMap phi k f`. -/
@[simp] theorem cocyclesMap_coe {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ)
    (f : M.cocycles k) : ((cocyclesMap φ k f : M'.cocycles k) : M'.dualSpace k)
      = dualMap φ k (f : M.dualSpace k) := rfl

/-- `cocyclesMap phi k` sends coboundaries to coboundaries, both viewed inside the cocycle
subgroups. -/
theorem cocyclesMap_coboundaries {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ)
    {f : M.cocycles k} (hf : f ∈ (M.coboundaries k).addSubgroupOf (M.cocycles k)) :
    cocyclesMap φ k f ∈ (M'.coboundaries k).addSubgroupOf (M'.cocycles k) := by
  rw [AddSubgroup.mem_addSubgroupOf] at hf ⊢
  exact dualMap_mem_coboundariesₛ φ k hf

/-- The map `H^k(phi^vee) : H^k(M^vee) -> H^k((M')^vee)` induced on cohomology by the dual
chain map `dualMap phi`. -/
noncomputable def cohomologyMap {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ) :
    M.cohomology k →+ M'.cohomology k :=
  QuotientAddGroup.map ((M.coboundaries k).addSubgroupOf (M.cocycles k))
    ((M'.coboundaries k).addSubgroupOf (M'.cocycles k)) (cocyclesMap φ k)
    (fun _ hf => cocyclesMap_coboundaries φ k hf)

/-- `cohomologyMap phi k` sends the class of a cocycle `f` to the class of
`cocyclesMap phi k f`. -/
@[simp] theorem cohomologyMap_mk {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ)
    (f : M.cocycles k) :
    cohomologyMap φ k (QuotientAddGroup.mk f) = QuotientAddGroup.mk (cocyclesMap φ k f) := rfl

/-! ### Homotopy invariance of the induced map on cohomology

If `phi : M' -> M` is null-homotopic, then the induced chain map `phi^vee` on dual
complexes is null-homotopic, hence `cohomologyMap phi k = 0`. Consequently
`cohomologyMap` depends only on the homotopy class of `phi`. -/

/-- The dual of a degree-`-1` homotopy `h : M' -> M`, as the degree-`-1` family on dual
complexes `M^vee -> (M')^vee` obtained by precomposition with `h`. -/
noncomputable def homotopyDualMap {M' M : RightModule A}
    (h : ∀ n, M'.carrier n →ₗ[R] M.carrier (n - 1)) (k : ℤ) :
    M.dualSpace k →ₗ[R] M'.dualSpace (k - 1) :=
  RDual.precompₗ ((degCastLin R (show (-(k - 1)) - 1 = -k by ring)).toLinearMap.comp (h (-(k - 1))))

/-- `homotopyDualMap h k f` evaluated at `z` is `f (h z)`, with `h z` transported into
degree `-k`. -/
@[simp] theorem homotopyDualMap_apply {M' M : RightModule A}
    (h : ∀ n, M'.carrier n →ₗ[R] M.carrier (n - 1)) (k : ℤ) (f : M.dualSpace k)
    (z : M'.carrier (-(k - 1))) :
    (show M'.carrier (-(k - 1)) →+ QZ from homotopyDualMap h k f) z
      = (RDual.toFun f) (degCastLin R (show (-(k - 1)) - 1 = -k by ring) (h (-(k - 1)) z)) := rfl

/-- Congruence of a module differential `M.d` under `HEq`. -/
theorem d_congr_heq2 (M : RightModule A) {i j : ℤ} (hij : i = j) {x : M.carrier i}
    {y : M.carrier j} (hxy : HEq x y) : HEq (M.d i x) (M.d j y) := by
  subst hij; cases hxy; rfl

/-- Congruence of a homotopy family `H.toFun` under `HEq`. -/
theorem h_congr_heq2 {M' M : RightModule A} {φ : RightModuleHom M' M}
    (H : Homotopy φ (0 : RightModuleHom M' M)) {i j : ℤ} (hij : i = j) {x : M'.carrier i}
    {y : M'.carrier j} (hxy : HEq x y) : HEq (H.toFun i x) (H.toFun j y) := by
  subst hij; cases hxy; rfl

/-- Evaluating a `degCastLin` transport of a dual-complex element: the degree cast on
`(M^vee)` becomes the opposite cast on the underlying point. -/
theorem dualSpace_degCastLin_apply (N : RightModule A) {a b : ℤ} (h : a = b)
    (g : N.dualSpace a) (y : N.carrier (-b)) :
    (show N.carrier (-b) →+ QZ from
        (degCastLin R h (V := fun n => N.dualSpace n)) g) y
      = (show N.carrier (-a) →+ QZ from g)
          (degCastLin R (show -b = -a by rw [h]) (V := fun n => N.carrier n) y) := by
  subst h; rfl

/-- Transporting `x` along `degCast` equals transporting `y` along `degCastLin` when
`x` and `y` are heterogeneously equal. -/
private theorem degCast_eq_degCastLin_of_heq {V : ℤ → Type u} [∀ n, AddCommGroup (V n)]
    [∀ n, Module R (V n)] {a c b : ℤ} (h : a = b) (h' : c = b) {x : V a} {y : V c}
    (hxy : HEq x y) : degCast h x = degCastLin R h' y :=
  eq_of_heq ((degCast_heq h x).trans (hxy.trans (degCastLin_heq R h' y).symm))

/-- If `H` is a homotopy from `phi` to `0`, then for every `k`-cocycle `f` of `M^vee`,
`phi^vee(f) = (-1)^k d_{(M')^vee}(homotopyDualMap H.toFun k f)`. -/
theorem dualMap_nullhomotopic_on_cocycles {M' M : RightModule A} {φ : RightModuleHom M' M}
    (H : Homotopy φ (0 : RightModuleHom M' M)) (k : ℤ)
    {f : M.dualSpace k} (hf : f ∈ M.cocyclesₛ k) :
    dualMap φ k f
      = ((-1 : ℤ) ^ k.natAbs) • (degCastLin R (show k - 1 + 1 = k by ring)
          (V := fun n => M'.dualSpace n)) (M'.dDual (k - 1) (homotopyDualMap H.toFun k f)) := by
  apply RDual.ext
  intro y
  show (RDual.toFun f) (φ.toFun (-k) y) = _
  rw [AddMonoidHom.zsmul_apply]
  rw [show (show M'.carrier (-k) →+ QZ from
        (degCastLin R (show k - 1 + 1 = k by ring) (V := fun n => M'.dualSpace n))
          (M'.dDual (k - 1) (homotopyDualMap H.toFun k f))) y
      = (show M'.carrier (-(k - 1 + 1)) →+ QZ from
          M'.dDual (k - 1) (homotopyDualMap H.toFun k f))
          (degCastLin R (show -k = -(k - 1 + 1) by ring) y) from ?_]
  · rw [RightModule.dDual_apply]
    rw [homotopyDualMap_apply]
    have hH := H.homotopy (-k) y
    simp only [RightModuleHom.zero_toFun, sub_zero] at hH
    rw [hH, map_add]
    rw [RightModule.cocyclesₛ, LinearMap.mem_ker] at hf
    have hterm1 : (RDual.toFun f) (degCast (show (-k - 1) + 1 = -k by ring)
        (M.d (-k - 1) (H.toFun (-k) y))) = 0 := by
      set z : M.carrier (-(k + 1)) :=
        degCast (V := M.carrier) (show (-k - 1) = -(k + 1) by ring) (H.toFun (-k) y) with hz
      have hev := congrArg (fun (g : M.dualSpace (k + 1)) =>
          (show M.carrier (-(k + 1)) →+ QZ from g) z) hf
      simp only at hev
      rw [RightModule.dDual_apply, RDual.zero_apply, RightModule.dDownshift_apply] at hev
      have hpow : ((-1 : ℤ) ^ (k + 1).natAbs) = 1 ∨ ((-1 : ℤ) ^ (k + 1).natAbs) = -1 :=
        neg_one_pow_eq_or ℤ _
      have hcancel : (RDual.toFun f) (degCastLin R (show (-(k + 1)) + 1 = -k by ring)
          (M.d (-(k + 1)) z)) = 0 := by
        rcases hpow with h1 | h1
        · rw [h1, one_smul] at hev; exact hev
        · rw [h1, neg_one_smul, neg_eq_zero] at hev; exact hev
      rw [show degCast (show (-k - 1) + 1 = -k by ring) (M.d (-k - 1) (H.toFun (-k) y))
            = degCastLin R (show (-(k + 1)) + 1 = -k by ring) (M.d (-(k + 1)) z) from ?_]
      · exact hcancel
      · refine degCast_eq_degCastLin_of_heq _ _ (d_congr_heq2 M (by ring) ?_)
        exact (degCast_heq (V := M.carrier) _ _).symm
    rw [hterm1, zero_add]
    rw [smul_smul, neg_one_pow_natAbs_add k (k - 1 + 1), show k + (k - 1 + 1) = 2 * k by ring,
      show (2 * k).natAbs = 2 * k.natAbs by rw [Int.natAbs_mul]; rfl, pow_mul]
    simp only [neg_one_sq, one_pow, one_smul]
    congr 1
    refine degCast_eq_degCastLin_of_heq _ _ ?_
    rw [RightModule.dDownshift_apply]
    refine h_congr_heq2 H (by ring) ?_
    refine HEq.trans ?_ (degCastLin_heq R _ _).symm
    exact d_congr_heq2 M' (by ring) (degCastLin_heq R _ _).symm
  · rw [dualSpace_degCastLin_apply (N := M') (show k - 1 + 1 = k by ring)]

/-- If `phi` is null-homotopic, then `phi^vee` sends every cocycle to a coboundary. -/
theorem dualMap_nullhomotopic_mem_coboundariesₛ {M' M : RightModule A}
    {φ : RightModuleHom M' M} (H : Homotopy φ (0 : RightModuleHom M' M)) (k : ℤ)
    {f : M.dualSpace k} (hf : f ∈ M.cocyclesₛ k) : dualMap φ k f ∈ M'.coboundariesₛ k := by
  rw [dualMap_nullhomotopic_on_cocycles H k hf]
  have hb : (degCastLin R (show k - 1 + 1 = k by ring) (V := fun n => M'.dualSpace n))
      (M'.dDual (k - 1) (homotopyDualMap H.toFun k f)) ∈ M'.coboundariesₛ k :=
    ⟨M'.dDual (k - 1) (homotopyDualMap H.toFun k f), ⟨homotopyDualMap H.toFun k f, rfl⟩, rfl⟩
  rcases neg_one_pow_eq_or ℤ k.natAbs with h1 | h1
  · rwa [h1, one_smul]
  · rw [h1, neg_one_smul]
    exact (M'.coboundariesₛ k).neg_mem hb

/-- If `phi` is homotopic to `0`, the induced map on cohomology vanishes. -/
theorem cohomologyMap_eq_zero_of_homotopy {M' M : RightModule A}
    {φ : RightModuleHom M' M} (H : Homotopy φ (0 : RightModuleHom M' M)) (k : ℤ) :
    cohomologyMap φ k = 0 := by
  ext c
  induction c using QuotientAddGroup.induction_on with
  | _ f =>
    rw [cohomologyMap_mk, AddMonoidHom.zero_apply, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf]
    exact dualMap_nullhomotopic_mem_coboundariesₛ H k f.2

/-- `cocyclesMap` is additive in the morphism `phi`. -/
theorem cocyclesMap_add {M' M : RightModule A} (φ χ : RightModuleHom M' M) (k : ℤ)
    (f : M.cocycles k) :
    cocyclesMap (φ + χ) k f = cocyclesMap φ k f + cocyclesMap χ k f := by
  apply Subtype.ext
  show dualMap (φ + χ) k (f : M.dualSpace k)
      = dualMap φ k (f : M.dualSpace k) + dualMap χ k (f : M.dualSpace k)
  apply RDual.ext
  intro x
  simp only [dualMap, RDual.precompₗ_apply, RightModuleHom.add_toFun, RDual.add_apply, map_add]

/-- `cocyclesMap` is compatible with negation in the morphism `phi`. -/
theorem cocyclesMap_neg {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ)
    (f : M.cocycles k) : cocyclesMap (-φ) k f = - cocyclesMap φ k f := by
  apply Subtype.ext
  show dualMap (-φ) k (f : M.dualSpace k) = - dualMap φ k (f : M.dualSpace k)
  apply RDual.ext
  intro x
  simp only [dualMap, RDual.precompₗ_apply, RightModuleHom.neg_toFun, RDual.neg_apply, map_neg]

/-- `cohomologyMap` is additive in the morphism `phi`. -/
theorem cohomologyMap_add {M' M : RightModule A} (φ χ : RightModuleHom M' M) (k : ℤ) :
    cohomologyMap (φ + χ) k = cohomologyMap φ k + cohomologyMap χ k := by
  ext c
  induction c using QuotientAddGroup.induction_on with
  | _ f =>
    simp only [AddMonoidHom.add_apply, cohomologyMap_mk]
    rw [cocyclesMap_add, QuotientAddGroup.mk_add]

/-- `cohomologyMap` is compatible with negation in the morphism `phi`. -/
theorem cohomologyMap_neg {M' M : RightModule A} (φ : RightModuleHom M' M) (k : ℤ) :
    cohomologyMap (-φ) k = - cohomologyMap φ k := by
  ext c
  induction c using QuotientAddGroup.induction_on with
  | _ f =>
    simp only [AddMonoidHom.neg_apply, cohomologyMap_mk]
    rw [cocyclesMap_neg, QuotientAddGroup.mk_neg]

/-- Homotopic homomorphisms `phi` and `psi` induce the same map on cohomology. -/
theorem cohomologyMap_congr_of_homotopic {M' M : RightModule A}
    {φ ψ : RightModuleHom M' M} (H : Homotopy φ ψ) (k : ℤ) :
    cohomologyMap φ k = cohomologyMap ψ k := by
  have hsub : cohomologyMap (φ + (-ψ)) k = 0 := by
    refine cohomologyMap_eq_zero_of_homotopy (φ := φ + (-ψ)) ?_ k
    refine { toFun := H.toFun, map_smul := H.map_smul, homotopy := ?_ }
    intro n x
    have := H.homotopy n x
    simp only [RightModuleHom.add_toFun, RightModuleHom.neg_toFun, RightModuleHom.zero_toFun,
      sub_zero]
    rw [show φ.toFun n x + -ψ.toFun n x = φ.toFun n x - ψ.toFun n x from (sub_eq_add_neg _ _).symm]
    exact this
  rw [cohomologyMap_add, cohomologyMap_neg, add_neg_eq_zero] at hsub
  exact hsub

end DGAlgebra

end Stacks.DifferentialGradedDual
