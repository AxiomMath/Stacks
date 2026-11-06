module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompletedGroupAlgebra
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Discrete modules over a profinite group as modules over its completed group algebra

Let `R` be a ring, not necessarily commutative, and `Q` a compact topological group. A continuous
discrete `R`-`Q`-module `N` is a module over the completed group algebra
`R[[Q]] = lim_U R[Q/U]` (`Stacks.GroupHomology.CompletedGroupAlgebra`): an element `v` of `N` is
fixed by some open normal subgroup `U` of `Q`, and `x ∈ R[[Q]]` acts on `v` through its image in
`R[Q/U]`, which acts on the `U`-invariants of `N`. The result does not depend on `U`.

This is the functor along which the derived categories of discrete modules of [Stacks, Section
03VI] embed into the derived category `D(R[[Q]])` of [Stacks, Tag 03VM]: for `Q` the Galois group
`Gal(k̄/k) ≅ Ẑ` of a finite field it is the passage from discrete `Gal(k̄/k)`-modules to
`R[[Ẑ]]`-modules.

## Main definitions

* `Stacks.ContinuousCohomology.fixedSubmodule`: the `U`-invariants of `N`, with the residual
  action of `Q` for `U` normal.
* `Stacks.ContinuousCohomology.discreteCompletedGroupAlgebraModule`: the `R[[Q]]`-module
  structure on `N`.
* `Stacks.ContinuousCohomology.discreteToCompletedGroupAlgebra`: the functor
  `Mod_{R,Q} ⥤ ModuleCat R[[Q]]`.

## Main results

* `Stacks.ContinuousCohomology.discreteSMul_eq`: `x • v` is computed by `R[Q/U]` for **any** open
  normal `U` fixing `v`.
* `Stacks.ContinuousCohomology.discreteSMul_of` and
  `Stacks.ContinuousCohomology.discreteSMul_const`: group elements act through the representation,
  constants through the `R`-module structure.
* `Stacks.ContinuousCohomology.preservesHomology_discreteToCompletedGroupAlgebra`: the functor is
  exact (it does not change underlying abelian groups).

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupHomology MonoidAlgebra

universe u u' v w w₂

namespace Stacks.GroupHomology.CompletedGroupAlgebra

variable {Λ : Type u} [Ring Λ] {Λ' : Type u'} [Ring Λ'] {G : Type v} [Group G]
  [TopologicalSpace G]

/-- **Change of coefficients** `Λ[[G]] → Λ'[[G]]` along a ring homomorphism `f : Λ → Λ'`,
componentwise on the group algebras `Λ[G/U]`. -/
def mapCoeff (f : Λ →+* Λ') : CompletedGroupAlgebra Λ G →+* CompletedGroupAlgebra Λ' G where
  toFun x := mk (fun U ↦ MonoidAlgebra.mapRingHom _ f (eval U x)) fun U V h ↦ by
    rw [← quotientAlgebraMap_eval h x]
    exact (DFunLike.congr_fun (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom f
      (QuotientGroup.map _ _ (MonoidHom.id G) fun _ hx ↦ h hx)) (eval U x)).symm
  map_one' := ext fun U ↦ by simp
  map_mul' x y := ext fun U ↦ by simp
  map_zero' := ext fun U ↦ by simp
  map_add' x y := ext fun U ↦ by simp

/-- The `U`-component of `mapCoeff f x` is the image of the `U`-component of `x` under `f`. -/
@[simp]
theorem eval_mapCoeff (f : Λ →+* Λ') (U : OpenNormalSubgroup G) (x : CompletedGroupAlgebra Λ G) :
    eval U (mapCoeff f x) = MonoidAlgebra.mapRingHom _ f (eval U x) :=
  rfl

/-- Change of coefficients along the identity is the identity. -/
@[simp]
theorem mapCoeff_id (x : CompletedGroupAlgebra Λ G) : mapCoeff (RingHom.id Λ) x = x :=
  ext fun U ↦ by simp [MonoidAlgebra.mapRingHom_id]

end Stacks.GroupHomology.CompletedGroupAlgebra


namespace Stacks.ContinuousCohomology

/-! ### Equivariant maps commute with the action of `R[G/U]` -/

section QuotientAlgebraAction

variable {R : Type u} [Ring R] {G : Type v} [Group G] [TopologicalSpace G]
  {M M' : Type*} [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction G M'] [SMulCommClass G R M']

/-- **A `φ`-semilinear `G`-equivariant map intertwines the actions of `R[G/U]` and `R'[G/U]`**,
`R[G/U] → R'[G/U]` being induced by `φ`. -/
theorem map_quotientAlgebraAction_semilinear {R' : Type u'} [Ring R'] {M' : Type*} [AddCommGroup M']
    [Module R' M'] [DistribMulAction G M'] [SMulCommClass G R' M'] (φ : R →+* R')
    (f : M →ₛₗ[φ] M') (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (U : OpenNormalSubgroup G) (hU : ∀ g ∈ U, ∀ m : M, g • m = m)
    (hU' : ∀ g ∈ U, ∀ m : M', g • m = m) (y : MonoidAlgebra R (G ⧸ (U : Subgroup G))) (m : M) :
    f (quotientAlgebraAction M U hU y m) =
      quotientAlgebraAction M' U hU' (MonoidAlgebra.mapRingHom _ φ y) (f m) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, map_add, map_add]
    show f ((quotientAlgebraAction M U hU) y₁ m + (quotientAlgebraAction M U hU) y₂ m) =
      (quotientAlgebraAction M' U hU') (MonoidAlgebra.mapRingHom _ φ y₁) (f m) +
        (quotientAlgebraAction M' U hU') (MonoidAlgebra.mapRingHom _ φ y₂) (f m)
    rw [map_add, h₁, h₂]
  | single q a =>
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [MonoidAlgebra.mapRingHom_single, quotientAlgebraAction_single,
        quotientAlgebraAction_single, map_smulₛₗ, hf]

/-- An `R`-linear `G`-equivariant map commutes with the action of `R[G/U]`. -/
theorem map_quotientAlgebraAction (f : M →ₗ[R] M') (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (U : OpenNormalSubgroup G) (hU : ∀ g ∈ U, ∀ m : M, g • m = m)
    (hU' : ∀ g ∈ U, ∀ m : M', g • m = m) (y : MonoidAlgebra R (G ⧸ (U : Subgroup G))) (m : M) :
    f (quotientAlgebraAction M U hU y m) = quotientAlgebraAction M' U hU' y (f m) := by
  have h := map_quotientAlgebraAction_semilinear (RingHom.id R) f hf U hU hU' y m
  rwa [MonoidAlgebra.mapRingHom_id, RingHom.id_apply] at h

end QuotientAlgebraAction

section Fixed

variable (R : Type u) [Ring R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  (N : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)

/-- The action of `g * h` on `x` is the action of `g` on the action of `h` on `x`. -/
lemma continuousModuleRho_mul_apply (g h : Q) (x : N.obj.obj.V) :
    (N.obj.obj.ρ (g * h)).asHom.hom x =
      (N.obj.obj.ρ g).asHom.hom ((N.obj.obj.ρ h).asHom.hom x) := by
  rw [map_mul]
  rfl

/-- The identity element of `Q` acts trivially. -/
lemma continuousModuleRho_one_apply (x : N.obj.obj.V) : (N.obj.obj.ρ 1).asHom.hom x = x := by
  rw [map_one]
  rfl

/-- **The `U`-invariants of a discrete `R`-`Q`-module.** -/
def fixedSubmodule (U : Subgroup Q) : Submodule R N.obj.obj.V where
  carrier := {x | ∀ g ∈ U, (N.obj.obj.ρ g).asHom.hom x = x}
  zero_mem' := fun _ _ ↦ map_zero _
  add_mem' := fun ha hb g hg ↦ by rw [map_add, ha g hg, hb g hg]
  smul_mem' := fun a _ hx g hg ↦ by rw [map_smul, hx g hg]

variable {R N} in
/-- An element lies in `fixedSubmodule R N U` if and only if every `g ∈ U` fixes it. -/
lemma mem_fixedSubmodule {U : Subgroup Q} {x : N.obj.obj.V} :
    x ∈ fixedSubmodule R N U ↔ ∀ g ∈ U, (N.obj.obj.ρ g).asHom.hom x = x :=
  Iff.rfl

/-- The invariants under a normal subgroup are stable under `Q`. -/
lemma rho_mem_fixedSubmodule (U : Subgroup Q) [U.Normal] (q : Q) {x : N.obj.obj.V}
    (hx : x ∈ fixedSubmodule R N U) : (N.obj.obj.ρ q).asHom.hom x ∈ fixedSubmodule R N U := by
  intro g hg
  have hconj : q⁻¹ * g * q ∈ U := by simpa using ‹U.Normal›.conj_mem g hg q⁻¹
  have hsplit : g * q = q * (q⁻¹ * g * q) := by group
  rw [← continuousModuleRho_mul_apply, hsplit, continuousModuleRho_mul_apply, hx _ hconj]

/-- The residual action of `Q` on the invariants under a normal subgroup. -/
instance fixedSubmodule.distribMulAction (U : Subgroup Q) [U.Normal] :
    DistribMulAction Q (fixedSubmodule R N U) where
  smul q x := ⟨(N.obj.obj.ρ q).asHom.hom x, rho_mem_fixedSubmodule R N U q x.2⟩
  one_smul x := Subtype.ext (continuousModuleRho_one_apply R N x.1)
  mul_smul g h x := Subtype.ext (continuousModuleRho_mul_apply R N g h x.1)
  smul_zero _q := Subtype.ext (map_zero _)
  smul_add _q _x _y := Subtype.ext (map_add _ _ _)

/-- The residual action of `q` on an invariant element is the action of `q` on `N`. -/
lemma fixedSubmodule.coe_smul (U : Subgroup Q) [U.Normal] (q : Q) (x : fixedSubmodule R N U) :
    ((q • x : fixedSubmodule R N U) : N.obj.obj.V) = (N.obj.obj.ρ q).asHom.hom x :=
  rfl

/-- The residual action of `Q` on the invariants commutes with the action of `R`. -/
instance fixedSubmodule.smulCommClass (U : Subgroup Q) [U.Normal] :
    SMulCommClass Q R (fixedSubmodule R N U) where
  smul_comm q a x := Subtype.ext (map_smul (N.obj.obj.ρ q).asHom.hom a x.1)

/-- The subgroup `U` acts trivially on the `U`-invariants. -/
lemma fixedSubmodule.smul_eq_self (U : Subgroup Q) [U.Normal] :
    ∀ g ∈ U, ∀ m : fixedSubmodule R N U, g • m = m :=
  fun g hg m ↦ Subtype.ext (m.2 g hg)

/-- The inclusion of the invariants under a smaller normal subgroup. -/
lemma fixedSubmodule_mono {U U' : Subgroup Q} (h : U' ≤ U) :
    fixedSubmodule R N U ≤ fixedSubmodule R N U' :=
  fun _ hx g hg ↦ hx g (h hg)

/-- Every element is fixed by some open normal subgroup, `Q` being compact. -/
lemma exists_mem_fixedSubmodule [IsTopologicalGroup Q] [CompactSpace Q] (x : N.obj.obj.V) :
    ∃ U : OpenNormalSubgroup Q, x ∈ fixedSubmodule R N (U : Subgroup Q) := by
  let S : Subgroup Q :=
    { carrier := {g | (N.obj.obj.ρ g).asHom.hom x = x}
      mul_mem' := fun {a b} ha hb ↦ by
        show (N.obj.obj.ρ (a * b)).asHom.hom x = x
        rw [continuousModuleRho_mul_apply, show (N.obj.obj.ρ b).asHom.hom x = x from hb, ha]
      one_mem' := continuousModuleRho_one_apply R N x
      inv_mem' := fun {a} ha ↦ by
        show (N.obj.obj.ρ a⁻¹).asHom.hom x = x
        conv_lhs => rw [← (show (N.obj.obj.ρ a).asHom.hom x = x from ha)]
        rw [← continuousModuleRho_mul_apply, inv_mul_cancel, continuousModuleRho_one_apply] }
  have hS : IsOpen (S : Set Q) := Stacks.GroupCohomology.isOpen_stabilizer R Q N x
  obtain ⟨U, hU⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    (⟨S, hS⟩ : OpenSubgroup Q).isClopen S.one_mem
  exact ⟨U, fun g hg ↦ hU hg⟩

end Fixed

/-! ### The action of `R[[Q]]` -/

section Action

variable (R : Type u) [Ring R] {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (N : Stacks.Injectives.ContinuousModule.{u, v, w} R Q)

/-- The action of `x ∈ R[[Q]]` on the `U`-invariants, through `R[Q/U]`. -/
def smulAt (U : OpenNormalSubgroup Q) (x : CompletedGroupAlgebra R Q)
    (m : fixedSubmodule R N (U : Subgroup Q)) : fixedSubmodule R N (U : Subgroup Q) :=
  quotientAlgebraAction (fixedSubmodule R N (U : Subgroup Q)) U
    (fixedSubmodule.smul_eq_self R N (U : Subgroup Q)) (CompletedGroupAlgebra.eval U x) m

omit [IsTopologicalGroup Q] in
/-- `smulAt` does not depend on the open normal subgroup. -/
lemma smulAt_of_le {U U' : OpenNormalSubgroup Q} (h : U' ≤ U) (x : CompletedGroupAlgebra R Q)
    (m : fixedSubmodule R N (U : Subgroup Q)) :
    (smulAt R N U' x ⟨m.1, fixedSubmodule_mono R N h m.2⟩ : N.obj.obj.V) = smulAt R N U x m := by
  let ι : fixedSubmodule R N (U : Subgroup Q) →ₗ[R] fixedSubmodule R N (U' : Subgroup Q) :=
    Submodule.inclusion (fixedSubmodule_mono R N h)
  have hU'm : ∀ g ∈ U', ∀ m : fixedSubmodule R N (U : Subgroup Q), g • m = m :=
    fun g hg m ↦ fixedSubmodule.smul_eq_self R N (U : Subgroup Q) g (h hg) m
  have key := map_quotientAlgebraAction ι (fun _ _ ↦ rfl) U' hU'm
    (fixedSubmodule.smul_eq_self R N (U' : Subgroup Q)) (CompletedGroupAlgebra.eval U' x) m
  have hcomp := DFunLike.congr_fun (DFunLike.congr_fun
    (quotientAlgebraAction_comp (fixedSubmodule R N (U : Subgroup Q)) h hU'm
      (fixedSubmodule.smul_eq_self R N (U : Subgroup Q))) (CompletedGroupAlgebra.eval U' x)) m
  rw [RingHom.comp_apply, CompletedGroupAlgebra.quotientAlgebraMap_eval] at hcomp
  show ((quotientAlgebraAction (fixedSubmodule R N (U' : Subgroup Q)) U'
      (fixedSubmodule.smul_eq_self R N (U' : Subgroup Q)) (CompletedGroupAlgebra.eval U' x)
      (ι m)) : N.obj.obj.V) = _
  rw [← key, ← hcomp]
  rfl

variable [CompactSpace Q]

/-- A chosen open normal subgroup fixing `v`. -/
def fixingSubgroup (v : N.obj.obj.V) : OpenNormalSubgroup Q :=
  (exists_mem_fixedSubmodule R N v).choose

/-- The element `v` is fixed by `fixingSubgroup R N v`. -/
lemma mem_fixedSubmodule_fixingSubgroup (v : N.obj.obj.V) :
    v ∈ fixedSubmodule R N (fixingSubgroup R N v : Subgroup Q) :=
  (exists_mem_fixedSubmodule R N v).choose_spec

/-- The action of `x ∈ R[[Q]]` on an element `v`. -/
def discreteSMul (x : CompletedGroupAlgebra R Q) (v : N.obj.obj.V) : N.obj.obj.V :=
  smulAt R N (fixingSubgroup R N v) x ⟨v, mem_fixedSubmodule_fixingSubgroup R N v⟩

/-- **`x • v` is computed by `R[Q/U]` for any open normal `U` fixing `v`.** -/
theorem discreteSMul_eq (U : OpenNormalSubgroup Q) (x : CompletedGroupAlgebra R Q)
    (v : N.obj.obj.V) (hv : v ∈ fixedSubmodule R N (U : Subgroup Q)) :
    discreteSMul R N x v = smulAt R N U x ⟨v, hv⟩ := by
  have h₁ : U ⊓ fixingSubgroup R N v ≤ U := inf_le_left
  have h₂ : U ⊓ fixingSubgroup R N v ≤ fixingSubgroup R N v := inf_le_right
  rw [discreteSMul, ← smulAt_of_le R N h₂, ← smulAt_of_le R N h₁]

/-- **The `R[[Q]]`-module structure of a discrete `R`-`Q`-module.** -/
@[instance_reducible]
def discreteCompletedGroupAlgebraModule :
    Module (CompletedGroupAlgebra R Q) N.obj.obj.V where
  smul := discreteSMul R N
  one_smul v := by
    change discreteSMul R N 1 v = v
    rw [discreteSMul, smulAt, map_one, map_one]
    rfl
  mul_smul x y v := by
    change discreteSMul R N (x * y) v = discreteSMul R N x (discreteSMul R N y v)
    let U := fixingSubgroup R N v
    have hv := mem_fixedSubmodule_fixingSubgroup R N v
    have hyv : discreteSMul R N y v ∈ fixedSubmodule R N (U : Subgroup Q) :=
      (smulAt R N U y ⟨v, hv⟩).2
    rw [discreteSMul_eq R N U x _ hyv]
    change (smulAt R N U (x * y) ⟨v, hv⟩ : N.obj.obj.V) = _
    rw [smulAt, map_mul, map_mul]
    rfl
  smul_zero x := by
    change discreteSMul R N x 0 = 0
    let U : OpenNormalSubgroup Q := fixingSubgroup R N 0
    rw [discreteSMul_eq R N U x 0 (Submodule.zero_mem _)]
    exact congrArg Subtype.val (map_zero (quotientAlgebraAction (fixedSubmodule R N
      (U : Subgroup Q)) U (fixedSubmodule.smul_eq_self R N (U : Subgroup Q))
      (CompletedGroupAlgebra.eval U x)))
  smul_add x v w := by
    change discreteSMul R N x (v + w) = discreteSMul R N x v + discreteSMul R N x w
    let U : OpenNormalSubgroup Q := fixingSubgroup R N v ⊓ fixingSubgroup R N w
    have hv : v ∈ fixedSubmodule R N (U : Subgroup Q) :=
      fixedSubmodule_mono R N inf_le_left (mem_fixedSubmodule_fixingSubgroup R N v)
    have hw : w ∈ fixedSubmodule R N (U : Subgroup Q) :=
      fixedSubmodule_mono R N inf_le_right (mem_fixedSubmodule_fixingSubgroup R N w)
    rw [discreteSMul_eq R N U x _ (Submodule.add_mem _ hv hw), discreteSMul_eq R N U x _ hv,
      discreteSMul_eq R N U x _ hw]
    exact congrArg Subtype.val (map_add (quotientAlgebraAction (fixedSubmodule R N
      (U : Subgroup Q)) U (fixedSubmodule.smul_eq_self R N (U : Subgroup Q))
      (CompletedGroupAlgebra.eval U x)) ⟨v, hv⟩ ⟨w, hw⟩)
  add_smul x y v := by
    change discreteSMul R N (x + y) v = discreteSMul R N x v + discreteSMul R N y v
    rw [discreteSMul, discreteSMul, discreteSMul, smulAt, smulAt, smulAt, map_add, map_add]
    rfl
  zero_smul v := by
    change discreteSMul R N 0 v = 0
    rw [discreteSMul, smulAt, map_zero, map_zero]
    rfl

/-! The module axioms for `discreteSMul`, stated without the instance. -/

/-- The unit of `R[[Q]]` acts as the identity. -/
theorem discreteSMul_one (v : N.obj.obj.V) : discreteSMul R N 1 v = v :=
  let := discreteCompletedGroupAlgebraModule R N
  one_smul (CompletedGroupAlgebra R Q) v

/-- The action of `x * y` is the action of `x` after that of `y`. -/
theorem discreteSMul_mul (x y : CompletedGroupAlgebra R Q) (v : N.obj.obj.V) :
    discreteSMul R N (x * y) v = discreteSMul R N x (discreteSMul R N y v) :=
  let := discreteCompletedGroupAlgebraModule R N
  mul_smul x y v

/-- The action is additive in the element of `R[[Q]]`. -/
theorem discreteSMul_add_left (x y : CompletedGroupAlgebra R Q) (v : N.obj.obj.V) :
    discreteSMul R N (x + y) v = discreteSMul R N x v + discreteSMul R N y v :=
  let := discreteCompletedGroupAlgebraModule R N
  add_smul x y v

/-- The zero of `R[[Q]]` acts as zero. -/
theorem discreteSMul_zero_left (v : N.obj.obj.V) : discreteSMul R N 0 v = 0 :=
  let := discreteCompletedGroupAlgebraModule R N
  zero_smul (CompletedGroupAlgebra R Q) v

/-- Each element of `R[[Q]]` acts additively. -/
theorem discreteSMul_add_right (x : CompletedGroupAlgebra R Q) (v w : N.obj.obj.V) :
    discreteSMul R N x (v + w) = discreteSMul R N x v + discreteSMul R N x w :=
  let := discreteCompletedGroupAlgebraModule R N
  smul_add x v w

/-- Each element of `R[[Q]]` sends zero to zero. -/
theorem discreteSMul_zero_right (x : CompletedGroupAlgebra R Q) : discreteSMul R N x 0 = 0 :=
  let := discreteCompletedGroupAlgebraModule R N
  smul_zero (A := N.obj.obj.V) x

/-- If every component of `x` is `a δ_q`, then `x` acts as `a` times the action of `q`. -/
private theorem discreteSMul_eq_smul_rho_of_eval_eq_single (x : CompletedGroupAlgebra R Q) (q : Q)
    (a : R) (hx : ∀ U : OpenNormalSubgroup Q,
      CompletedGroupAlgebra.eval U x = single (q : Q ⧸ (U : Subgroup Q)) a) (v : N.obj.obj.V) :
    discreteSMul R N x v = a • (N.obj.obj.ρ q).asHom.hom v := by
  rw [discreteSMul, smulAt, hx]
  show ((quotientAlgebraAction _ _ _ (single (q : Q ⧸ _) a)
    ⟨v, mem_fixedSubmodule_fixingSubgroup R N v⟩ : fixedSubmodule R N _) : N.obj.obj.V) = _
  rw [quotientAlgebraAction_single]
  rfl

/-- A group element acts through the representation. -/
theorem discreteSMul_of (q : Q) (v : N.obj.obj.V) :
    discreteSMul R N (CompletedGroupAlgebra.of q) v = (N.obj.obj.ρ q).asHom.hom v := by
  rw [discreteSMul_eq_smul_rho_of_eval_eq_single R N _ q 1 (fun U ↦ rfl), one_smul]

/-- A constant acts through the `R`-module structure. -/
theorem discreteSMul_const (a : R) (v : N.obj.obj.V) :
    discreteSMul R N (CompletedGroupAlgebra.const a) v = a • v := by
  rw [discreteSMul_eq_smul_rho_of_eval_eq_single R N _ 1 a (fun U ↦ rfl),
    continuousModuleRho_one_apply]

end Action

/-! ### The functor -/

section Functor

variable (R : Type u) [Ring R] (Q : Type v) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q]

/-- **A `φ`-semilinear `Q`-equivariant map of discrete modules intertwines the actions of
`R[[Q]]` and `R'[[Q]]`**, through `CompletedGroupAlgebra.mapCoeff φ`, for modules in any two
universes. -/
theorem discreteSMul_map_semilinear {R' : Type u'} [Ring R'] (φ : R →+* R')
    {N : Stacks.Injectives.ContinuousModule.{u, v, w} R Q}
    {N' : Stacks.Injectives.ContinuousModule.{u', v, w₂} R' Q}
    (f : N.obj.obj.V →ₛₗ[φ] N'.obj.obj.V)
    (hf : ∀ (q : Q) (v : N.obj.obj.V), f ((N.obj.obj.ρ q).asHom.hom v) =
      (N'.obj.obj.ρ q).asHom.hom (f v))
    (x : CompletedGroupAlgebra R Q) (v : N.obj.obj.V) :
    f (discreteSMul R N x v) = discreteSMul R' N' (CompletedGroupAlgebra.mapCoeff φ x) (f v) := by
  let U := fixingSubgroup R N v
  have hv := mem_fixedSubmodule_fixingSubgroup R N v
  have hfv : f v ∈ fixedSubmodule R' N' (U : Subgroup Q) := fun g hg ↦ by
    rw [← hf g v, hv g hg]
  rw [discreteSMul_eq R' N' U _ _ hfv]
  let fU : fixedSubmodule R N (U : Subgroup Q) →ₛₗ[φ] fixedSubmodule R' N' (U : Subgroup Q) :=
    { toFun m := ⟨f m.1, fun g hg ↦ by rw [← hf g m.1, m.2 g hg]⟩
      map_add' _ _ := Subtype.ext (map_add f _ _)
      map_smul' _ _ := Subtype.ext (map_smulₛₗ f _ _) }
  exact congrArg Subtype.val (map_quotientAlgebraAction_semilinear φ fU
    (fun g m ↦ Subtype.ext (hf g m.1)) U (fixedSubmodule.smul_eq_self R N (U : Subgroup Q))
    (fixedSubmodule.smul_eq_self R' N' (U : Subgroup Q)) (CompletedGroupAlgebra.eval U x) ⟨v, hv⟩)

/-- **An `R`-linear `Q`-equivariant map of discrete modules is `R[[Q]]`-linear**, for modules in
any two universes. -/
theorem discreteSMul_map_linear {N : Stacks.Injectives.ContinuousModule.{u, v, w} R Q}
    {N' : Stacks.Injectives.ContinuousModule.{u, v, w₂} R Q} (f : N.obj.obj.V →ₗ[R] N'.obj.obj.V)
    (hf : ∀ (q : Q) (v : N.obj.obj.V), f ((N.obj.obj.ρ q).asHom.hom v) =
      (N'.obj.obj.ρ q).asHom.hom (f v))
    (x : CompletedGroupAlgebra R Q) (v : N.obj.obj.V) :
    f (discreteSMul R N x v) = discreteSMul R N' x (f v) := by
  have h := discreteSMul_map_semilinear R Q (RingHom.id R) f hf x v
  rwa [CompletedGroupAlgebra.mapCoeff_id] at h

/-- A morphism of discrete `R`-`Q`-modules is `R[[Q]]`-linear. -/
theorem discreteSMul_map {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R Q} (f : N ⟶ N')
    (x : CompletedGroupAlgebra R Q) (v : N.obj.obj.V) :
    f.hom.hom.hom.hom (discreteSMul R N x v) = discreteSMul R N' x (f.hom.hom.hom.hom v) :=
  discreteSMul_map_linear R Q f.hom.hom.hom.hom
    (fun q v ↦ ConcreteCategory.congr_hom (f.hom.hom.comm q) v) x v

/-- **Discrete `R`-`Q`-modules as `R[[Q]]`-modules**: the same abelian group, with
`Stacks.ContinuousCohomology.discreteCompletedGroupAlgebraModule`. -/
def discreteToCompletedGroupAlgebra :
    Stacks.Injectives.ContinuousModule.{u, v, w} R Q ⥤
      ModuleCat.{w} (CompletedGroupAlgebra R Q) where
  obj N :=
    letI := discreteCompletedGroupAlgebraModule R N
    ModuleCat.of (CompletedGroupAlgebra R Q) N.obj.obj.V
  map {N N'} f :=
    letI := discreteCompletedGroupAlgebraModule R N
    letI := discreteCompletedGroupAlgebraModule R N'
    ModuleCat.ofHom
      { toFun := f.hom.hom.hom.hom
        map_add' := map_add _
        map_smul' := discreteSMul_map R Q f }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying function of the image of a morphism. -/
@[simp] lemma discreteToCompletedGroupAlgebra_map_apply
    {N N' : Stacks.Injectives.ContinuousModule.{u, v, w} R Q} (f : N ⟶ N') (v : N.obj.obj.V) :
    ((discreteToCompletedGroupAlgebra R Q).map f).hom v = f.hom.hom.hom.hom v :=
  rfl

/-- The action on the image of `N` is `discreteSMul`. -/
lemma discreteToCompletedGroupAlgebra_smul
    (N : Stacks.Injectives.ContinuousModule.{u, v, w} R Q) (x : CompletedGroupAlgebra R Q)
    (v : (discreteToCompletedGroupAlgebra R Q).obj N) :
    x • v = discreteSMul R N x v :=
  rfl

/-- The functor `discreteToCompletedGroupAlgebra R Q` is additive. -/
instance discreteToCompletedGroupAlgebra_additive :
    (discreteToCompletedGroupAlgebra R Q).Additive where
  map_add := rfl

/-- **The functor is exact**: a short complex of discrete modules is exact exactly when the
underlying complex of `R`-modules is, and the functor does not change the underlying maps. -/
theorem preservesHomology_discreteToCompletedGroupAlgebra :
    (discreteToCompletedGroupAlgebra.{u, v, w} R Q).PreservesHomology := by
  refine ((Functor.exact_tfae (discreteToCompletedGroupAlgebra.{u, v, w} R Q)).out 2 3).mp
    fun S hS ↦ ?_
  have := Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{u, v, w} R Q
  have := Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{u, v, w} R Q
  have : (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R Q).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hU : (S.map (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R Q)).Exact :=
    hS.map _
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hU ⊢
  exact hU

/-- The functor `discreteToCompletedGroupAlgebra R Q` preserves finite limits. -/
instance preservesFiniteLimits_discreteToCompletedGroupAlgebra :
    PreservesFiniteLimits (discreteToCompletedGroupAlgebra.{u, v, w} R Q) :=
  have := preservesHomology_discreteToCompletedGroupAlgebra.{u, v, w} R Q
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- The functor `discreteToCompletedGroupAlgebra R Q` preserves finite colimits. -/
instance preservesFiniteColimits_discreteToCompletedGroupAlgebra :
    PreservesFiniteColimits (discreteToCompletedGroupAlgebra.{u, v, w} R Q) :=
  have := preservesHomology_discreteToCompletedGroupAlgebra.{u, v, w} R Q
  Functor.preservesFiniteColimits_of_preservesHomology _

end Functor

end Stacks.ContinuousCohomology

end
