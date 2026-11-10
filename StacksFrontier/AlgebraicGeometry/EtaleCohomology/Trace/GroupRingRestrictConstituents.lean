module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LatticeReductionConstituents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CliffordRestrictionFactor
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Order.Atoms.Finite

/-!
# Constituents of restrictions of group-ring modules

For a group homomorphism `φ : G' → G` and a `ℤ[G]`-module `M`, write
`Stacks.EtaleCohomology.GroupRingRestrict φ M` for `M` viewed as a `ℤ[G']`-module along `φ`.

## Main definitions

* `Stacks.EtaleCohomology.GroupRingRestrict`: a `ℤ[G]`-module viewed as a `ℤ[G']`-module along
  `φ : G' → G`.
* `Stacks.EtaleCohomology.SimpleSubquotientIndex`: the simple subquotients `W / W'` of `M`, with
  `W'` a coatom of the submodules of `W`.

## Main results

* `Stacks.EtaleCohomology.isSemisimpleModule_of_forall_exists_isCompl_zmod`: a `ℤ[G]`-module
  killed by `n` is semisimple as soon as every `G`-stable `ℤ/n`-subspace has a `G`-stable
  complement.
* `Stacks.EtaleCohomology.hasConstituentsIn_simpleSubquotient`: the simple subquotients of `M` are
  its constituents.
* `Stacks.EtaleCohomology.HasConstituentsIn.groupRingRestrict`: if each simple subquotient of a
  finite `M` stays semisimple along `φ`, the restriction of `M` along `φ` has its constituents in
  the restrictions of the simple subquotients.
* `Stacks.EtaleCohomology.isSemisimpleModule_groupRingRestrict_of_isSimpleModule`: the restriction
  of a simple module killed by a prime `ℓ` is semisimple, in the group-ring form of
  `Stacks.EtaleCohomology.exists_isCompl_comp_of_normal_factor`.
* `Stacks.EtaleCohomology.HasConstituentsIn.of_isogeny` (Brauer–Nesbitt): if `ι : L₂ → L₁` and
  `κ : L₁ → L₂` compose to `ℓⁿ` both ways and `L₂` has no `ℓ`-torsion, then every `L₂ / ℓᵏ L₂`
  has the constituents of `L₁ / ℓ L₁`.
-/

@[expose] public noncomputable section

universe v

namespace Stacks.EtaleCohomology

open MonoidAlgebra

section GroupRing

variable {G : Type*} [Group G]

/-- **An additive map commuting with `G` is `ℤ[G]`-linear.** -/
def groupRingLinearMap {M N : Type*} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    [AddCommGroup N] [Module (MonoidAlgebra ℤ G) N] (f : M →+ N)
    (hf : ∀ g x, f (of ℤ G g • x) = of ℤ G g • f x) : M →ₗ[MonoidAlgebra ℤ G] N where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by
    rw [RingHom.id_apply]
    induction a using MonoidAlgebra.induction_on with
    | of g => exact hf g x
    | add a b ha hb => rw [add_smul, map_add, ha, hb, add_smul]
    | smul r a ha => rw [smul_assoc, map_zsmul, ha, smul_assoc]

/-- `groupRingLinearMap f hf` agrees with `f`. -/
@[simp]
theorem groupRingLinearMap_apply {M N : Type*} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    [AddCommGroup N] [Module (MonoidAlgebra ℤ G) N] (f : M →+ N)
    (hf : ∀ g x, f (of ℤ G g • x) = of ℤ G g • f x) (x : M) :
    groupRingLinearMap f hf x = f x :=
  rfl

variable {G' : Type*} [Group G'] (φ : G' →* G)

/-- **`M` as a `ℤ[G']`-module along `φ : G' → G`.** -/
def GroupRingRestrict (_φ : G' →* G) (M : Type*) : Type _ := M

variable (M : Type*) [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]

/-- The restriction of `M` along `φ` has the additive group structure of `M`. -/
instance instAddCommGroupGroupRingRestrict : AddCommGroup (GroupRingRestrict φ M) :=
  inferInstanceAs (AddCommGroup M)

/-- The `ℤ[G']`-module structure on `M` obtained by pulling back the `ℤ[G]`-action along the ring
homomorphism `ℤ[G'] → ℤ[G]` induced by `φ`. -/
instance instModuleGroupRingRestrict : Module (MonoidAlgebra ℤ G') (GroupRingRestrict φ M) :=
  (Module.compHom M (mapDomainRingHom ℤ φ) : Module (MonoidAlgebra ℤ G') M)

/-- The restriction of a finite module along `φ` is finite. -/
instance instFiniteGroupRingRestrict [Finite M] : Finite (GroupRingRestrict φ M) :=
  inferInstanceAs (Finite M)

/-- The restriction of `M` along `φ` has the `ℤ/n`-module structure of `M`. -/
instance instZModModuleGroupRingRestrict (n : ℕ) [Module (ZMod n) M] :
    Module (ZMod n) (GroupRingRestrict φ M) :=
  inferInstanceAs (Module (ZMod n) M)

variable {M}

/-- The identity of `M`, into its restriction along `φ`. -/
def toGroupRingRestrict : M ≃+ GroupRingRestrict φ M := AddEquiv.refl M

/-- An element `a` of `ℤ[G']` acts on the restriction of `M` along `φ` as its image in `ℤ[G]`
acts on `M`. -/
theorem groupRingRestrict_smul (a : MonoidAlgebra ℤ G') (x : GroupRingRestrict φ M) :
    a • x = toGroupRingRestrict φ (mapDomainRingHom ℤ φ a • (toGroupRingRestrict φ).symm x) :=
  rfl

/-- An element `g` of `G'` acts on the restriction of `M` along `φ` as `φ g` acts on `M`. -/
theorem groupRingRestrict_of_smul (g : G') (x : GroupRingRestrict φ M) :
    of ℤ G' g • x = toGroupRingRestrict φ (of ℤ G (φ g) • (toGroupRingRestrict φ).symm x) := by
  rw [groupRingRestrict_smul]
  congr 2
  simp [MonoidAlgebra.of_apply, mapDomain_single]

variable {N : Type*} [AddCommGroup N] [Module (MonoidAlgebra ℤ G) N]

/-- A `ℤ[G]`-linear map, along `φ`. -/
def groupRingRestrictMap (f : M →ₗ[MonoidAlgebra ℤ G] N) :
    GroupRingRestrict φ M →ₗ[MonoidAlgebra ℤ G'] GroupRingRestrict φ N where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := f.map_smul (mapDomainRingHom ℤ φ a) x

/-- A `ℤ[G]`-linear equivalence, along `φ`. -/
def groupRingRestrictEquiv (e : M ≃ₗ[MonoidAlgebra ℤ G] N) :
    GroupRingRestrict φ M ≃ₗ[MonoidAlgebra ℤ G'] GroupRingRestrict φ N where
  __ := groupRingRestrictMap φ e.toLinearMap
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- A `ℤ[G]`-submodule, as a `ℤ[G']`-submodule of the restriction. -/
def groupRingRestrictSubmodule (U : Submodule (MonoidAlgebra ℤ G) M) :
    Submodule (MonoidAlgebra ℤ G') (GroupRingRestrict φ M) where
  carrier := {x | (toGroupRingRestrict φ).symm x ∈ U}
  add_mem' hx hy := U.add_mem hx hy
  zero_mem' := U.zero_mem
  smul_mem' a _ hx := U.smul_mem (mapDomainRingHom ℤ φ a) hx

/-- An element lies in the restricted submodule exactly when it lies in `U`. -/
theorem mem_groupRingRestrictSubmodule (U : Submodule (MonoidAlgebra ℤ G) M)
    (x : GroupRingRestrict φ M) :
    x ∈ groupRingRestrictSubmodule φ U ↔ (toGroupRingRestrict φ).symm x ∈ U :=
  Iff.rfl

/-- The restricted submodule is the restriction of the submodule. -/
def groupRingRestrictSubmoduleEquiv (U : Submodule (MonoidAlgebra ℤ G) M) :
    groupRingRestrictSubmodule φ U ≃ₗ[MonoidAlgebra ℤ G'] GroupRingRestrict φ U where
  toFun x := toGroupRingRestrict φ ⟨(toGroupRingRestrict φ).symm x.1, x.2⟩
  invFun x := ⟨toGroupRingRestrict φ ((toGroupRingRestrict φ).symm x).1,
    ((toGroupRingRestrict φ).symm x).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The quotient by the restricted submodule is the restriction of the quotient. -/
def groupRingRestrictQuotientEquiv (U : Submodule (MonoidAlgebra ℤ G) M) :
    (GroupRingRestrict φ M ⧸ groupRingRestrictSubmodule φ U) ≃ₗ[MonoidAlgebra ℤ G']
      GroupRingRestrict φ (M ⧸ U) := by
  refine LinearEquiv.ofBijective ((groupRingRestrictSubmodule φ U).liftQ
    (groupRingRestrictMap φ U.mkQ) fun x hx ↦ (Submodule.Quotient.mk_eq_zero U).2 hx) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero U).1 hx
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H y => exact ⟨Submodule.Quotient.mk (toGroupRingRestrict φ y), rfl⟩

end GroupRing

/-! ### Semisimplicity over `ℤ[G]` from complements over `ℤ/n` -/

section ZMod

variable {H : Type*} [Group H] (n : ℕ) {M : Type*} [AddCommGroup M]
  [Module (MonoidAlgebra ℤ H) M] [Module (ZMod n) M]

/-- **The action of `H` on `M`, by `ℤ/n`-linear maps.** -/
def groupRingZModAction : H →* Module.End (ZMod n) M where
  toFun h := (DistribSMul.toAddMonoidHom M (of ℤ H h)).toZModLinearMap n
  map_one' := by
    refine LinearMap.ext fun x ↦ ?_
    change of ℤ H 1 • x = x
    rw [map_one, one_smul]
  map_mul' a b := by
    refine LinearMap.ext fun x ↦ ?_
    change of ℤ H (a * b) • x = of ℤ H a • of ℤ H b • x
    rw [map_mul, mul_smul]

/-- `groupRingZModAction n h` acts on `M` as `h` does. -/
theorem groupRingZModAction_apply (h : H) (x : M) :
    groupRingZModAction n h x = of ℤ H h • x :=
  rfl

variable [NeZero n]

/-- A `ℤ[H]`-submodule, as a `ℤ/n`-subspace. -/
def zmodSubmoduleOfGroupRing (U : Submodule (MonoidAlgebra ℤ H) M) : Submodule (ZMod n) M where
  carrier := U
  add_mem' hx hy := U.add_mem hx hy
  zero_mem' := U.zero_mem
  smul_mem' c x hx := by
    change c • x ∈ U
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact U.toAddSubmonoid.nsmul_mem hx _

/-- A `H`-stable `ℤ/n`-subspace, as a `ℤ[H]`-submodule. -/
def groupRingSubmoduleOfZMod (W : Submodule (ZMod n) M)
    (hW : ∀ h : H, W ≤ W.comap (groupRingZModAction n h)) :
    Submodule (MonoidAlgebra ℤ H) M where
  carrier := W
  add_mem' hx hy := W.add_mem hx hy
  zero_mem' := W.zero_mem
  smul_mem' a x hx := by
    change a • x ∈ W
    induction a using MonoidAlgebra.induction_on with
    | of h => exact hW h hx
    | add a b ha hb =>
      rw [add_smul]
      exact W.add_mem ha hb
    | smul r a ha =>
      rw [smul_assoc]
      exact W.toAddSubgroup.zsmul_mem ha r

omit [NeZero n] in
/-- The `ℤ[H]`-submodule of an `H`-stable `ℤ/n`-subspace `W` has the elements of `W`. -/
theorem mem_groupRingSubmoduleOfZMod (W : Submodule (ZMod n) M)
    (hW : ∀ h : H, W ≤ W.comap (groupRingZModAction n h)) (x : M) :
    x ∈ groupRingSubmoduleOfZMod n W hW ↔ x ∈ W :=
  Iff.rfl

/-- **Semisimplicity over `ℤ[H]` from `H`-stable complements over `ℤ/n`.** -/
theorem isSemisimpleModule_of_forall_exists_isCompl_zmod
    (h : ∀ W : Submodule (ZMod n) M, (∀ g : H, W ≤ W.comap (groupRingZModAction n g)) →
      ∃ W', IsCompl W W' ∧ ∀ g : H, W' ≤ W'.comap (groupRingZModAction n g)) :
    IsSemisimpleModule (MonoidAlgebra ℤ H) M := by
  refine (isSemisimpleModule_iff _ _).2 ⟨fun U ↦ ?_⟩
  obtain ⟨W', hc, hW'⟩ := h (zmodSubmoduleOfGroupRing n U)
    (fun g x hx ↦ U.smul_mem (of ℤ H g) hx)
  refine ⟨groupRingSubmoduleOfZMod n W' hW', ?_, ?_⟩
  · exact Submodule.disjoint_def.2 fun x hx hx' ↦ Submodule.disjoint_def.1 hc.disjoint x hx hx'
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1
      (codisjoint_iff.1 hc.codisjoint ▸ Submodule.mem_top : x ∈ zmodSubmoduleOfGroupRing n U ⊔ W')
    exact Submodule.add_mem_sup hy hz

omit [NeZero n] in
/-- **A simple `ℤ[H]`-module has no `H`-stable `ℤ/n`-subspaces but `0` and itself.** -/
theorem eq_bot_or_eq_top_of_isSimpleModule_zmod [IsSimpleModule (MonoidAlgebra ℤ H) M]
    (W : Submodule (ZMod n) M) (hW : ∀ h : H, W ≤ W.comap (groupRingZModAction n h)) :
    W = ⊥ ∨ W = ⊤ := by
  refine (IsSimpleOrder.eq_bot_or_eq_top (groupRingSubmoduleOfZMod n W hW)).imp
    (fun h ↦ ?_) fun h ↦ ?_ <;> ext x <;> simp [← mem_groupRingSubmoduleOfZMod n W hW x, h]

end ZMod

/-! ### Simple subquotients and restriction -/

section Subquotients

variable (A : Type*) [Ring A] (M : Type v) [AddCommGroup M] [Module A M]

/-- **The simple subquotients `W / W'` of `M`**, `W'` a coatom of the submodules of `W`. -/
def SimpleSubquotientIndex : Type v := Σ W : Submodule A M, {W' : Submodule A W // IsCoatom W'}

/-- The simple subquotient `W / W'` indexed by `j`. -/
abbrev simpleSubquotient (j : SimpleSubquotientIndex A M) : Type v := j.1 ⧸ j.2.1

/-- Each simple subquotient is a simple module. -/
instance instIsSimpleModuleSimpleSubquotient (j : SimpleSubquotientIndex A M) :
    IsSimpleModule A (simpleSubquotient A M j) :=
  isSimpleModule_iff_isCoatom.2 j.2.2

/-- A finite module has finitely many submodules. -/
theorem finite_submodule_of_finite [Finite M] : Finite (Submodule A M) :=
  Finite.of_injective (fun U : Submodule A M ↦ (U : Set M)) SetLike.coe_injective

/-- A finite module has finitely many simple subquotients `W / W'`. -/
instance instFiniteSimpleSubquotientIndex [Finite M] : Finite (SimpleSubquotientIndex A M) := by
  have := finite_submodule_of_finite A M
  have : ∀ W : Submodule A M, Finite (Submodule A W) := fun W => finite_submodule_of_finite A W
  unfold SimpleSubquotientIndex
  infer_instance

/-- **The simple subquotients are the constituents.** -/
theorem hasConstituentsIn_simpleSubquotient :
    HasConstituentsIn A (simpleSubquotient A M) M := by
  intro W S _ _ q hq hS
  let e := q.quotKerEquivOfSurjective hq
  have : IsSimpleModule A (W ⧸ LinearMap.ker q) := IsSimpleModule.congr e
  exact ⟨⟨W, LinearMap.ker q, isSimpleModule_iff_isCoatom.1 inferInstance⟩,
    e.symm.toLinearMap, e.toLinearMap, by ext; simp⟩

variable {G G' : Type*} [Group G] [Group G'] (φ : G' →* G) {M}
  [Module (MonoidAlgebra ℤ G) M]

/-- **Constituents of a restriction**: if every simple subquotient of the finite `ℤ[G]`-module
`M` stays semisimple along `φ`, the restriction of `M` along `φ` has its constituents in the
restrictions of the simple subquotients of `M`. -/
theorem HasConstituentsIn.groupRingRestrict [Finite M]
    (hss : ∀ j : SimpleSubquotientIndex (MonoidAlgebra ℤ G) M,
      IsSemisimpleModule (MonoidAlgebra ℤ G')
        (GroupRingRestrict φ (simpleSubquotient (MonoidAlgebra ℤ G) M j))) :
    HasConstituentsIn (MonoidAlgebra ℤ G')
      (fun j => GroupRingRestrict φ (simpleSubquotient (MonoidAlgebra ℤ G) M j))
      (GroupRingRestrict φ M) := by
  refine (hasConstituentsIn_simpleSubquotient (MonoidAlgebra ℤ G) M).prop
    (fun X _ _ ↦ HasConstituentsIn (MonoidAlgebra ℤ G')
      (fun j ↦ GroupRingRestrict φ (simpleSubquotient (MonoidAlgebra ℤ G) M j))
      (GroupRingRestrict φ X)) ?_ ?_ ?_ ?_ M
  · intro X Y _ _ _ _ e h
    exact h.of_linearEquiv (groupRingRestrictEquiv φ e)
  · intro X _ _ hX
    have : Subsingleton (GroupRingRestrict φ X) := hX
    exact hasConstituentsIn_of_subsingleton
  · intro X _ _ _ i f g hgf
    have := hss i
    refine (hasConstituentsIn_self_of_isSemisimpleModule
      (𝓜 := fun j ↦ GroupRingRestrict φ (simpleSubquotient (MonoidAlgebra ℤ G) M j))
      i).of_injective (groupRingRestrictMap φ f) fun a b hab ↦ ?_
    exact (LinearMap.congr_fun hgf a).symm.trans
      ((congrArg g hab).trans (LinearMap.congr_fun hgf b))
  · intro X _ _ _ U hU hQ
    exact HasConstituentsIn.of_extension (groupRingRestrictSubmodule φ U)
      (hU.of_linearEquiv (groupRingRestrictSubmoduleEquiv φ U).symm)
      (hQ.of_linearEquiv (groupRingRestrictQuotientEquiv φ U).symm)

end Subquotients

/-! ### Semisimplicity of the restriction of a simple module killed by `ℓ` -/

section Restriction

variable {Γ G' P P' : Type*} [Group Γ] [Group G'] [Group P] [Group P'] (ℓ : ℕ)
  {T : Type*} [AddCommGroup T] [Module (MonoidAlgebra ℤ Γ) T] [Finite T]

/-- **The restriction of a simple module killed by `ℓ` through a normal subgroup on which the
action factors is semisimple**: the group-ring form of
`Stacks.EtaleCohomology.exists_isCompl_comp_of_normal_factor`. -/
theorem isSemisimpleModule_groupRingRestrict_of_isSimpleModule [Fact ℓ.Prime]
    [IsSimpleModule (MonoidAlgebra ℤ Γ) T] [Module (ZMod ℓ) T] (φ : G' →* Γ)
    (π : Γ →* P) (π' : G' →* P') (hπ' : Function.Surjective π') (ι : P' →* P) [ι.range.Normal]
    (hcomm : ∀ g, π (φ g) = ι (π' g)) (N : Subgroup Γ) [N.Normal]
    (hfac : ∀ n₁ ∈ N, ∀ n₂ ∈ N, π n₁ = π n₂ → ∀ x : T, of ℤ Γ n₁ • x = of ℤ Γ n₂ • x)
    [(N.comap φ).FiniteIndex] (hidx : ((N.comap φ).index : ZMod ℓ) ≠ 0) :
    IsSemisimpleModule (MonoidAlgebra ℤ G') (GroupRingRestrict φ T) := by
  have : FiniteDimensional (ZMod ℓ) T := Module.Finite.of_finite
  refine isSemisimpleModule_of_forall_exists_isCompl_zmod ℓ fun W hW ↦ ?_
  let W₁ : Submodule (ZMod ℓ) T := W
  have hW₁ : ∀ g : G', W₁ ≤ W₁.comap (groupRingZModAction (H := Γ) ℓ (M := T) (φ g)) := by
    intro g x hx
    have h1 : of ℤ G' g • (toGroupRingRestrict φ x) ∈ W := hW g hx
    rwa [groupRingRestrict_of_smul] at h1
  obtain ⟨W', hc, hW''⟩ := exists_isCompl_comp_of_normal_factor
    (groupRingZModAction (H := Γ) ℓ (M := T)) φ π π' hπ' ι hcomm N
    (fun n₁ h₁ n₂ h₂ he ↦ LinearMap.ext fun x ↦ hfac n₁ h₁ n₂ h₂ he x) hidx
    (fun W₀ hW₀ ↦ by
      rcases eq_bot_or_eq_top_of_isSimpleModule_zmod ℓ W₀ hW₀ with rfl | rfl
      · exact ⟨⊤, isCompl_bot_top, fun _ ↦ le_top⟩
      · exact ⟨⊥, isCompl_top_bot, fun _ ↦ bot_le⟩) W₁ hW₁
  refine ⟨W', hc, fun g x hx ↦ ?_⟩
  change of ℤ G' g • x ∈ W'
  rw [groupRingRestrict_of_smul]
  exact hW'' g hx

end Restriction

/-! ### Isogenous lattices -/

section Isogeny

variable {A : Type*} [Ring A] {ι : Type*} {𝓜 : ι → Type v} [∀ i, AddCommGroup (𝓜 i)]
  [∀ i, Module A (𝓜 i)] {ℓ : ℕ}

/-- A linear equivalence `e : L ≃ L'` maps `ℓᵏ L` onto `ℓᵏ L'`. -/
theorem powSMulRange_map_linearEquiv {L L' : Type v} [AddCommGroup L] [Module A L]
    [AddCommGroup L'] [Module A L'] (e : L ≃ₗ[A] L') (k : ℕ) :
    (powSMulRange A ℓ L k).map (e : L →ₗ[A] L') = powSMulRange A ℓ L' k := by
  ext x
  rw [Submodule.mem_map, mem_powSMulRange]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_powSMulRange.1 hy
    exact ⟨e z, by rw [LinearEquiv.coe_coe, map_nsmul]⟩
  · rintro ⟨z, rfl⟩
    exact ⟨ℓ ^ k • e.symm z, mem_powSMulRange.2 ⟨_, rfl⟩, by
      rw [LinearEquiv.coe_coe, map_nsmul, LinearEquiv.apply_symm_apply]⟩

/-- **Isogenous lattices have the same constituents modulo `ℓ`** (Brauer–Nesbitt): if
`ι : L₂ → L₁`, `κ : L₁ → L₂` compose to `ℓⁿ` both ways, `L₂` has no `ℓ`-torsion and `L₁ / ℓ L₁`
has its constituents in `𝓜`, then so has every `L₂ / ℓᵏ L₂`. -/
theorem HasConstituentsIn.of_isogeny {L₁ L₂ : Type v} [AddCommGroup L₁] [Module A L₁]
    [AddCommGroup L₂] [Module A L₂] (ι' : L₂ →ₗ[A] L₁) (κ : L₁ →ₗ[A] L₂) (n : ℕ)
    (hικ : ∀ x, ι' (κ x) = ℓ ^ n • x) (hκι : ∀ y, κ (ι' y) = ℓ ^ n • y)
    (htf : ∀ y : L₂, ℓ ^ n • y = 0 → y = 0)
    (h : HasConstituentsIn A 𝓜 (L₁ ⧸ powSMulRange A ℓ L₁ 1)) (k : ℕ) :
    HasConstituentsIn A 𝓜 (L₂ ⧸ powSMulRange A ℓ L₂ k) := by
  have hinj : Function.Injective ι' :=
    (injective_iff_map_eq_zero ι').2 fun y hy ↦ htf y (by rw [← hκι, hy, map_zero])
  have hn : powSMulRange A ℓ L₁ n ≤ LinearMap.range ι' := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_powSMulRange.1 hx
    exact ⟨κ y, hικ y⟩
  let e : L₂ ≃ₗ[A] LinearMap.range ι' := LinearEquiv.ofInjective ι' hinj
  exact ((h.quotient_lattice (LinearMap.range ι') n hn).of_linearEquiv
    (Submodule.Quotient.equiv _ _ e.symm
      (powSMulRange_map_linearEquiv e.symm 1))).quotient_powSMulRange k

end Isogeny

end Stacks.EtaleCohomology

end
