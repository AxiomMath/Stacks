module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksCore.Tactic.StacksAttribute

/-!
# Nonvanishing sections of an invertible sheaf of modules

Let `(X, O_X)` be a ringed space all of whose stalks `O_{X,x}` are local rings, and let `L` be an
invertible sheaf of `O_X`-modules. For a global section `s ∈ Γ(X, L)` the *nonvanishing locus*
is
`X_s = {x ∈ X | s_x ∉ 𝔪_x L_x}`,
and this file proves that `X_s` is open. This is the first assertion of
[Stacks, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY).

Openness is reduced to a pointwise criterion that is manifestly local: `x ∈ X_s` if and only if
`s` pairs to the unit section on some open neighbourhood of `x`
(`Stacks.SheafOfModules.mem_nonvanishingLocus_iff`). The pairing in question comes from a
trivialization `ψ : L ⊗_{O_X} N ≅ O_X` of `L`, which exists by Tag 0B8K
(`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`); the criterion does not depend
on the choice of `N` or `ψ`, since both sides of the equivalence are statements about `X_s`.

The "only if" direction is where the mathematical content sits, and it is isolated as a statement
about modules over a local ring: if `Θ : M ⊗_R P ≃ R` with `R` local and `s ∈ M` does not lie in
`𝔪 M`, then `Θ (s ⊗ n) = 1` for some `n ∈ P`
(`Stacks.SheafOfModules.exists_tmul_eq_one`). Transporting that statement to the stalks at `x`
uses the canonical isomorphism `(L ⊗_{O_X} N)_x ≅ L_x ⊗_{O_{X,x}} N_x` of Tag 01CB
(`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`).

## Main definitions

* `Stacks.SheafOfModules.nonvanishingLocus`: the set `X_s` above.
* `Stacks.SheafOfModules.nonvanishingOpen`: the same set, packaged as an element of `Opens X`.
* `Stacks.SheafOfModules.tensorContract` and `Stacks.SheafOfModules.pairingAut`: for a pairing
  `Θ : M ⊗_R P ≃ R`, the contraction `a ⊗ (b ⊗ c) ↦ Θ (a ⊗ c) • b` and the resulting
  automorphism `m ↦ ∑ Θ (m ⊗ cᵢ) • bᵢ` of `M`, where `∑ bᵢ ⊗ cᵢ = Θ⁻¹ 1`.
* `Stacks.SheafOfModules.stalkLinearEquiv`: the stalk at `x` of an isomorphism of sheaves of
  modules, as an `O_{X,x}`-linear equivalence.
* `Stacks.SheafOfModules.unitSection`, `Stacks.SheafOfModules.unitGerm` and
  `Stacks.SheafOfModules.unitStalkLinearEquiv`: the unit section `1 ∈ O_X(W)` read as a section
  of the structure sheaf viewed as a module over itself, its germ, and the resulting
  identification of `(O_X)_x` with the stalk of that module.
* `Stacks.SheafOfModules.tensorPairing` and `Stacks.SheafOfModules.stalkPairing`: the pairings
  `L(W) × N(W) → O_X(W)` and `L_x ⊗_{O_{X,x}} N_x ≃ O_{X,x}` determined by a trivialization of
  `L ⊗_{O_X} N`.

## Main results

* `Stacks.SheafOfModules.isOpen_nonvanishingLocus` is **Tag 01CY**, openness clause.
* `Stacks.SheafOfModules.exists_tmul_eq_one` and
  `Stacks.SheafOfModules.notMem_smul_of_tmul_eq_one`: the two directions of the local-algebra
  core. The first is the Nakayama-type step of the Stacks proof; the second is the elementary
  observation that a section pairing to a unit cannot be in `𝔪 M`.
* `Stacks.SheafOfModules.mem_nonvanishingLocus_iff`: the local criterion for membership in `X_s`.
* `Stacks.SheafOfModules.stalkPairing_germ`: the stalk pairing computes the section pairing on
  germs. This is the single compatibility that links the sheaf-theoretic and algebraic halves.
* `Stacks.SheafOfModules.stalkModule_eq`: the Tag 01CB module structure on a stalk coincides with
  Mathlib's; `Stacks.SheafOfModules.mem_smul_top_congr` transports membership in `𝔪 • ⊤` across
  that equality.

## Implementation notes

The Stacks proof argues that `s_x` is a *basis* of `L_x` by Nakayama's lemma, which presupposes
that `L_x` is a finitely generated `O_{X,x}`-module — a fact that Tag 0B8K supplies through its
"locally a direct summand of a finite free module" clause, which is not available here (see the
implementation notes of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne.lean`).
`exists_tmul_eq_one` avoids any finiteness hypothesis: `Θ (s ⊗ P)` is an ideal of `R`, and if it
were contained in `𝔪` then the automorphism `pairingAut Θ` of `M` would carry `s` into `𝔪 M`,
hence `s ∈ 𝔪 M` because an automorphism preserves `𝔪 M`. That `pairingAut Θ` is an automorphism
is the same braiding-and-associator computation that the Stacks proof of Tag 0B8K performs on
sheaves, here done once over a ring; it is the only place the symmetry of the tensor product is
used.

Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`, matching the Tag 01CB
development: the site `Opens X` forces the carrier, ring and module
universes to agree, and no statement is specialized further.

The `O_{X,x}`-module structure on the stalk of a sheaf of modules is the one used for Stacks Tag
01CB, `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, whose characterizing property is
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul`. It is, by definition,
Mathlib's instance from `Mathlib/Algebra/Category/ModuleCat/Stalk.lean`;
`Stacks.SheafOfModules.stalkModule_eq` records that `rfl`, so either name may be used in the
statement.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

section LocalAlgebra

variable {R : Type u} [CommRing R] {M P : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

/-- The contraction `a ⊗ (b ⊗ c) ↦ Θ (a ⊗ c) • b`.

Named `tensorContract` rather than `contract` because
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSummand` declares a `contract` in
this same namespace, and two declarations of one name made the two modules impossible to
co-import. They are genuinely different notions, not a duplication: that one contracts a
*sheaf*-level pairing against a global section, this one is plain commutative algebra on
modules. -/
noncomputable def tensorContract (Θ : M ⊗[R] P ≃ₗ[R] R) : M ⊗[R] (M ⊗[R] P) ≃ₗ[R] M :=
  (TensorProduct.assoc R M M P).symm.trans <|
    (TensorProduct.congr (TensorProduct.comm R M M) (LinearEquiv.refl R P)).trans <|
      (TensorProduct.assoc R M M P).trans <|
        (TensorProduct.congr (LinearEquiv.refl R M) Θ).trans (TensorProduct.rid R M)

lemma tensorContract_apply (Θ : M ⊗[R] P ≃ₗ[R] R) (a b : M) (c : P) :
    tensorContract Θ (a ⊗ₜ (b ⊗ₜ c)) = Θ (a ⊗ₜ c) • b := by
  simp [tensorContract]

/-- The automorphism `m ↦ ∑ Θ (m ⊗ cᵢ) • bᵢ` of `M`, where `∑ bᵢ ⊗ cᵢ = Θ⁻¹ 1`. -/
noncomputable def pairingAut (Θ : M ⊗[R] P ≃ₗ[R] R) : M ≃ₗ[R] M :=
  (TensorProduct.rid R M).symm.trans <|
    (TensorProduct.congr (LinearEquiv.refl R M) Θ.symm).trans (tensorContract Θ)

lemma pairingAut_apply (Θ : M ⊗[R] P ≃ₗ[R] R) (m : M) :
    pairingAut Θ m = tensorContract Θ (m ⊗ₜ Θ.symm 1) := by
  simp [pairingAut]

lemma contract_mem_smul (Θ : M ⊗[R] P ≃ₗ[R] R) (I : Ideal R) (s : M)
    (hs : ∀ n : P, Θ (s ⊗ₜ n) ∈ I) (ξ : M ⊗[R] P) :
    tensorContract Θ (s ⊗ₜ ξ) ∈ I • (⊤ : Submodule R M) := by
  induction ξ with
  | tmul b c => rw [tensorContract_apply]; exact Submodule.smul_mem_smul (hs c) Submodule.mem_top
  | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hy hz

/-- Equal module structures give the same submodule `I • ⊤`, hence the same membership. This is
what makes two spellings of a nonvanishing locus that differ only in the chosen stalk module
instance interchangeable: the naive rewrite is blocked because the type `Submodule R M` itself
depends on the instance. -/
lemma mem_smul_top_congr {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    {inst₁ inst₂ : Module S Q} (h : inst₁ = inst₂) (I : Ideal S) (m : Q) :
    (m ∈ letI := inst₁; I • (⊤ : Submodule S Q)) ↔
      (m ∈ letI := inst₂; I • (⊤ : Submodule S Q)) := by
  subst h
  exact Iff.rfl

variable [IsLocalRing R]

/-- If `M ⊗ P ≃ R` over a local ring `R` and `s : M` does not lie in `𝔪 M`, then `s` pairs
to `1` with some element of `P`. -/
theorem exists_tmul_eq_one (Θ : M ⊗[R] P ≃ₗ[R] R) (s : M)
    (hs : s ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :
    ∃ n : P, Θ (s ⊗ₜ n) = 1 := by
  set J : Ideal R := Submodule.map (Θ.toLinearMap ∘ₗ TensorProduct.mk R M P s)
    (⊤ : Submodule R P) with hJ
  by_cases hJtop : J = ⊤
  · have h : (1 : R) ∈ J := hJtop ▸ Submodule.mem_top
    obtain ⟨n, -, hn⟩ := h
    exact ⟨n, hn⟩
  · exfalso
    have hJm : ∀ n : P, Θ (s ⊗ₜ n) ∈ IsLocalRing.maximalIdeal R := fun n =>
      IsLocalRing.le_maximalIdeal hJtop ⟨n, Submodule.mem_top, rfl⟩
    have h1 : pairingAut Θ s ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
      rw [pairingAut_apply]
      exact contract_mem_smul Θ _ s hJm _
    refine hs ?_
    have h2 : Submodule.map (pairingAut Θ : M →ₗ[R] M)
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
        = IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
      rw [Submodule.map_smul'']
      congr 1
      exact Submodule.eq_top_iff'.2 fun y =>
        ⟨(pairingAut Θ).symm y, Submodule.mem_top, by simp⟩
    rw [← h2] at h1
    obtain ⟨y, hy, hy2⟩ := h1
    rwa [← (pairingAut Θ).injective hy2]

/-- Conversely, a section pairing to `1` cannot lie in `𝔪 M`. -/
theorem notMem_smul_of_tmul_eq_one (Θ : M ⊗[R] P ≃ₗ[R] R) (s : M) (n : P)
    (h : Θ (s ⊗ₜ n) = 1) :
    s ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  intro hs
  have h1 : s ⊗ₜ[R] n ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (M ⊗[R] P)) := by
    refine Submodule.smul_induction_on hs ?_ ?_
    · intro a ha y _
      rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · intro y z hy hz
      rw [TensorProduct.add_tmul]
      exact Submodule.add_mem _ hy hz
  have h2 : Θ (s ⊗ₜ[R] n) ∈ IsLocalRing.maximalIdeal R := by
    refine Submodule.smul_induction_on h1 ?_ ?_
    · intro a ha y _
      rw [map_smul]
      exact Ideal.mul_mem_right _ _ ha
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  rw [h] at h2
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2

end LocalAlgebra

section Stalks

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : RingedSpace.{u, u})

/-- Germ formula for the canonical `O_{X,x}`-linear stalk map of a morphism of presheaves of
modules. -/
lemma stalkMapL_germ {F F' : PresheafOfModules.{u} (O X)} (φ : F ⟶ F') (x : X.carrier)
    (U : Opens X.carrier) (hxU : x ∈ U) (t : F.obj (op U)) :
    stalkMapL X F F' φ x (grpGerm X F x U hxU t)
      = grpGerm X F' x U hxU ((φ.app (op U)).hom t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hxU
    ((PresheafOfModules.toPresheaf (O X)).map φ) t

/-- Every element of a stalk is a germ. -/
lemma exists_grpGerm_eq (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    (m : grpStalk X F x) :
    ∃ (U : Opens X.carrier) (hxU : x ∈ U) (t : F.obj (op U)), grpGerm X F x U hxU t = m := by
  obtain ⟨U, hxU, t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) F.presheaf m
  exact ⟨U, hxU, t, ht⟩

/-- The germ at `x ∈ W` of the restriction of a section over `⊤` is the germ of that section. -/
private lemma grpGerm_map_top (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    (W : Opens X.carrier) (hxW : x ∈ W) (t : F.obj (op ⊤)) :
    grpGerm X F x W hxW (F.map (homOfLE (le_top (a := W))).op t)
      = grpGerm X F x ⊤ trivial t :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) F.presheaf
    (homOfLE (le_top (a := W))) x hxW t

lemma stalkMapL_hom_inv {F G : SheafOfModules.{u} (structureSheafRing X)} (e : F ≅ G)
    (x : X.carrier) (m : grpStalk X F.val x) :
    stalkMapL X G.val F.val e.inv.val x (stalkMapL X F.val G.val e.hom.val x m) = m := by
  obtain ⟨U, hxU, t, rfl⟩ := exists_grpGerm_eq X F.val x m
  rw [stalkMapL_germ, stalkMapL_germ]
  congr 1
  have h : ((e.hom ≫ e.inv).val.app (op U)).hom t = t := by rw [e.hom_inv_id]; rfl
  exact h

/-- The stalk at `x` of an isomorphism of sheaves of `O_X`-modules, as an `O_{X,x}`-linear
equivalence of stalks. -/
noncomputable def stalkLinearEquiv {F G : SheafOfModules.{u} (structureSheafRing X)}
    (e : F ≅ G) (x : X.carrier) :
    grpStalk X F.val x ≃ₗ[ringStalk X x] grpStalk X G.val x :=
  LinearEquiv.ofLinearMap (stalkMapL X F.val G.val e.hom.val x)
    (stalkMapL X G.val F.val e.inv.val x)
    (LinearMap.ext fun m => stalkMapL_hom_inv X e.symm x m)
    (LinearMap.ext fun m => stalkMapL_hom_inv X e x m)

lemma stalkLinearEquiv_germ {F G : SheafOfModules.{u} (structureSheafRing X)}
    (e : F ≅ G) (x : X.carrier) (U : Opens X.carrier) (hxU : x ∈ U) (t : F.val.obj (op U)) :
    stalkLinearEquiv X e x (grpGerm X F.val x U hxU t)
      = grpGerm X G.val x U hxU ((e.hom.val.app (op U)).hom t) :=
  stalkMapL_germ X e.hom.val x U hxU t

/-- The `O_{X,x}`-module structure on the stalk of a sheaf of modules used in Tag 01CB is
Mathlib's, by definition. -/
lemma stalkModule_eq (F : PresheafOfModules.{u} (O X)) (x : X.carrier) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X F x
      = PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F x :=
  rfl

/-! ### The stalk of the structure sheaf as a module over itself -/

/-- The unit section `1 ∈ O_X(W)`, read as a section of the structure sheaf viewed as a module
over itself. -/
noncomputable def unitSection (W : Opens X.carrier) :
    (SheafOfModules.unit (structureSheafRing X)).val.obj (op W) :=
  (1 : ToType ((structureSheafRing X).obj.obj (op W)))

/-- The germ at `x` of the unit section. -/
noncomputable def unitGerm (x : X.carrier) :
    grpStalk X (SheafOfModules.unit (structureSheafRing X)).val x :=
  grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x ⊤ trivial (unitSection X ⊤)

lemma grpGerm_unitSection (x : X.carrier) (W : Opens X.carrier) (hxW : x ∈ W) :
    grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x W hxW (unitSection X W)
      = unitGerm X x := by
  have h : ((SheafOfModules.unit (structureSheafRing X)).val.map
      (homOfLE (le_top (a := W))).op).hom (unitSection X ⊤) = unitSection X W :=
    map_one ((structureSheafRing X).obj.map (homOfLE (le_top (a := W))).op).hom
  rw [unitGerm, ← h]
  exact grpGerm_map_top X _ x W hxW _

lemma ringGerm_smul_unitGerm (x : X.carrier) (W : Opens X.carrier) (hxW : x ∈ W)
    (α : (SheafOfModules.unit (structureSheafRing X)).val.obj (op W)) :
    ringGerm X x W hxW α • unitGerm X x
      = grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x W hxW α := by
  rw [← grpGerm_unitSection X x W hxW,
    ← stalkModule_germ_smul X (SheafOfModules.unit (structureSheafRing X)).val x W hxW α
      (unitSection X W)]
  congr 1
  exact mul_one (show X.presheaf.obj (op W) from α)

/-- The stalk of the structure sheaf, regarded as a module over itself, is free of rank one on
the germ of the unit section. -/
noncomputable def unitStalkLinearEquiv (x : X.carrier) :
    ringStalk X x ≃ₗ[ringStalk X x]
      grpStalk X (SheafOfModules.unit (structureSheafRing X)).val x :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringStalk X x) _ (unitGerm X x)) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr ?_, ?_⟩
    · intro a ha
      obtain ⟨W, hxW, α, rfl⟩ := X.presheaf.exists_germ_eq a
      have h0 : grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x W hxW α = 0 := by
        rw [← ringGerm_smul_unitGerm X x W hxW α]
        exact ha
      have hz : grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x W hxW α
          = grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x W hxW 0 := by
        rw [h0, map_zero]
      obtain ⟨V, hxV, iV, jV, hV⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
        (SheafOfModules.unit (structureSheafRing X)).val.presheaf x hxW hxW α 0 hz
      have hres : (X.presheaf.map iV.op).hom α = 0 := by
        refine hV.trans ?_
        exact map_zero ((SheafOfModules.unit (structureSheafRing X)).val.presheaf.map jV.op).hom
      have hg := TopCat.Presheaf.germ_res_apply X.presheaf iV x hxV α
      rw [hres, map_zero] at hg
      exact hg.symm
    · intro q
      obtain ⟨W, hxW, α, rfl⟩ :=
        exists_grpGerm_eq X (SheafOfModules.unit (structureSheafRing X)).val x q
      exact ⟨ringGerm X x W hxW α, ringGerm_smul_unitGerm X x W hxW α⟩

lemma unitStalkLinearEquiv_symm_grpGerm (x : X.carrier) (W : Opens X.carrier) (hxW : x ∈ W)
    (α : (SheafOfModules.unit (structureSheafRing X)).val.obj (op W)) :
    (unitStalkLinearEquiv X x).symm
        (grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x W hxW α)
      = ringGerm X x W hxW α := by
  rw [LinearEquiv.symm_apply_eq]
  exact (ringGerm_smul_unitGerm X x W hxW α).symm

end Stalks

section Nonvanishing

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : RingedSpace.{u, u}}

/-- The *nonvanishing locus* `X_s` of a global section `s` of a sheaf of `O_X`-modules `L`:
the set of points at which the germ of `s` does not lie in `𝔪_x L_x`. -/
def nonvanishingLocus [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    (L : SheafOfModules.{u} (structureSheafRing X)) (s : L.sections) : Set X.carrier :=
  {x | grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) ∉
    IsLocalRing.maximalIdeal (ringStalk X x) •
      (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x))}

variable {L N : SheafOfModules.{u} (structureSheafRing X)}
  (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf,
      (X).IsSheaf⟩).obj L).obj N ≅
    SheafOfModules.unit (structureSheafRing X))

/-- The pairing `L(W) × N(W) → O_X(W)` obtained from a trivialization `ψ : L ⊗ N ≅ O_X`. -/
noncomputable def tensorPairing (W : Opens X.carrier)
    (a : L.val.obj (op W)) (b : N.val.obj (op W)) :
    (SheafOfModules.unit (structureSheafRing X)).val.obj (op W) :=
  ψ.hom.val.app (op W) (toTensorSheafSection X L N (op W) (a ⊗ₜ[X.presheaf.obj (op W)] b))

lemma tensorPairing_res {V W : Opens X.carrier} (i : V ⟶ W)
    (a : L.val.obj (op W)) (b : N.val.obj (op W)) :
    (SheafOfModules.unit (structureSheafRing X)).val.map i.op (tensorPairing ψ W a b)
      = tensorPairing ψ V (L.val.map i.op a) (N.val.map i.op b) := by
  have h1 : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf,
      (X).IsSheaf⟩).obj L).obj N).val.map
      i.op
        (toTensorSheafSection X L N (op W) (a ⊗ₜ[X.presheaf.obj (op W)] b))
      = toTensorSheafSection X L N (op V)
        (L.val.map i.op a ⊗ₜ[X.presheaf.obj (op V)] N.val.map i.op b) :=
    (PresheafOfModules.naturality_apply
      (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) L.val N.val)) i.op
      (a ⊗ₜ[X.presheaf.obj (op W)] b)).symm
  have h2 := PresheafOfModules.naturality_apply ψ.hom.val i.op
    (toTensorSheafSection X L N (op W) (a ⊗ₜ[X.presheaf.obj (op W)] b))
  exact h2.symm.trans (congrArg (fun z => ψ.hom.val.app (op V) z) h1)

/-- The pairing of the stalks induced by a trivialization of `L ⊗ N`. -/
noncomputable def stalkPairing (x : X.carrier) :
    (grpStalk X L.val x) ⊗[ringStalk X x] (grpStalk X N.val x) ≃ₗ[ringStalk X x]
      ringStalk X x :=
  (tensorStalkIso X x L N).symm.trans
    ((stalkLinearEquiv X ψ x).trans (unitStalkLinearEquiv X x).symm)

lemma stalkPairing_germ (x : X.carrier) (W : Opens X.carrier) (hxW : x ∈ W)
    (a : L.val.obj (op W)) (b : N.val.obj (op W)) :
    stalkPairing ψ x
        (grpGerm X L.val x W hxW a ⊗ₜ[ringStalk X x] grpGerm X N.val x W hxW b)
      = ringGerm X x W hxW (tensorPairing ψ W a b) := by
  have h : (tensorStalkIso X x L N).symm
      (grpGerm X L.val x W hxW a ⊗ₜ[ringStalk X x] grpGerm X N.val x W hxW b)
      = grpGerm X
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf,
            (X).IsSheaf⟩).obj L).obj N).val
        x W hxW
        (toTensorSheafSection X L N (op W) (a ⊗ₜ[X.presheaf.obj (op W)] b)) := by
    rw [LinearEquiv.symm_apply_eq]
    exact (tensorStalkIso_germ X x L N W hxW a b).symm
  rw [stalkPairing, LinearEquiv.trans_apply, h, LinearEquiv.trans_apply]
  exact (congrArg (unitStalkLinearEquiv X x).symm (stalkLinearEquiv_germ X ψ x W hxW _)).trans
    (unitStalkLinearEquiv_symm_grpGerm X x W hxW (tensorPairing ψ W a b))

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- The nonvanishing locus is exactly the set of points having a neighbourhood on which the
section pairs to the unit section. -/
theorem mem_nonvanishingLocus_iff (s : L.sections) (x : X.carrier) :
    x ∈ nonvanishingLocus L s ↔
      ∃ (W : Opens X.carrier) (_ : x ∈ W) (b : N.val.obj (op W)),
        tensorPairing ψ W (s.eval (op W)) b = unitSection X W := by
  have hgerm : ∀ (W : Opens X.carrier) (hxW : x ∈ W),
      grpGerm X L.val x W hxW (s.eval (op W))
        = grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) := by
    intro W hxW
    have hres : L.val.map (homOfLE (le_top (a := W))).op (s.eval (op ⊤)) = s.eval (op W) :=
      PresheafOfModules.sections_property s (homOfLE (le_top (a := W))).op
    rw [← hres]
    exact grpGerm_map_top X L.val x W hxW _
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := exists_tmul_eq_one (stalkPairing ψ x)
      (grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))) hx
    obtain ⟨V, hxV, b, rfl⟩ := exists_grpGerm_eq X N.val x n
    rw [← hgerm V hxV, stalkPairing_germ] at hn
    have hu : grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x V hxV
        (tensorPairing ψ V (s.eval (op V)) b)
        = grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x ⊤ (Opens.mem_top x)
          (unitSection X ⊤) := by
      rw [← ringGerm_smul_unitGerm X x V hxV (tensorPairing ψ V (s.eval (op V)) b), hn,
        one_smul, unitGerm]
    obtain ⟨W, hxW, iW, jW, hW⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
      (SheafOfModules.unit (structureSheafRing X)).val.presheaf x hxV (Opens.mem_top x)
      (tensorPairing ψ V (s.eval (op V)) b) (unitSection X ⊤) hu
    refine ⟨W, hxW, N.val.map iW.op b, ?_⟩
    have hs : L.val.map iW.op (s.eval (op V)) = s.eval (op W) :=
      PresheafOfModules.sections_property s iW.op
    rw [← hs, ← tensorPairing_res]
    refine hW.trans ?_
    exact map_one ((structureSheafRing X).obj.map jW.op).hom
  · rintro ⟨W, hxW, b, hb⟩
    have hne := notMem_smul_of_tmul_eq_one (stalkPairing ψ x)
      (grpGerm X L.val x W hxW (s.eval (op W))) (grpGerm X N.val x W hxW b) (by
        rw [stalkPairing_germ, hb]
        exact map_one (ringGerm X x W hxW))
    rw [hgerm W hxW] at hne
    exact hne

/-- **Stacks Project, Tag 01CY** (openness). For an invertible sheaf of modules on a ringed
space all of whose stalks are local rings, the nonvanishing locus of a global section is
open. -/
@[stacks 01CY "openness", ega "0 5.5.2"]
theorem isOpen_nonvanishingLocus
    (L : SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections) :
    IsOpen (nonvanishingLocus L s) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hxW, b, hb⟩ := (mem_nonvanishingLocus_iff ψ s x).mp hx
  exact ⟨W, fun y hy => (mem_nonvanishingLocus_iff ψ s y).mpr ⟨W, hy, b, hb⟩, W.isOpen, hxW⟩

/-- The open subset on which a global section of an invertible module is nonvanishing. -/
noncomputable def nonvanishingOpen (L : SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections) :
    Opens X.carrier :=
  ⟨nonvanishingLocus L s, isOpen_nonvanishingLocus L s⟩

end Nonvanishing

end Stacks.SheafOfModules

end
