module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.FreeProduct.Basic

/-!
# Warfield's characterization of summands of sums of cyclic modules

Let `R` be a commutative ring and `P` an `R`-module. Then `P` is a direct summand of a direct sum
of modules of the form `R / f R` if and only if, for every short exact sequence
`0 → A → B → C → 0` of `R`-modules with `f A = A ∩ f B` for all `f ∈ R`, the induced map
`Hom_R(P, B) → Hom_R(P, C)` is surjective.

## Main definitions

* `IsSummandOfSumCyclic`: `P` is a direct summand of `⨁_{i ∈ I} R / f_i R` for some family
  `f : I → R`.
* `LiftingProperty`: every `R`-linear map from `P` lifts along every surjection of a short exact
  sequence satisfying the purity condition `f A = A ∩ f B`.
* `cyclicLift`: the linear map `R / f R → P` sending `1` to an element `p` with `f • p = 0`.

## Main results

* `summand_sum_cyclic_iff_lifting`: `IsSummandOfSumCyclic R P ↔ LiftingProperty R P`.

## References

* [Stacks, Tag 0ASM](https://stacks.math.columbia.edu/tag/0ASM)
-/

@[expose] public section

universe u v w x y

/-- `P` is a direct summand of a direct sum `⨁_{i ∈ I} R / f_i R`: there are linear maps
`ι : P → ⨁_i R / f_i R` and `π : ⨁_i R / f_i R → P` with `π ∘ ι = id`. -/
def IsSummandOfSumCyclic (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P] :
    Prop :=
  ∃ (I : Type (max u v)) (f : I → R)
    (ι : P →ₗ[R] (DirectSum I (fun i => R ⧸ Ideal.span {f i})))
    (π : (DirectSum I (fun i => R ⧸ Ideal.span {f i})) →ₗ[R] P),
    π ∘ₗ ι = LinearMap.id

open Pointwise in
/-- For every short exact sequence `0 → A → B → C → 0` (`α` injective, `β` surjective,
`range α = ker β`) satisfying `f • range α = range α ⊓ f • ⊤` for all `f ∈ R`, the induced map
`Hom_R(P, B) → Hom_R(P, C)`, `φ ↦ β ∘ φ`, is surjective. -/
def LiftingProperty (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P]
    [Module R P] : Prop :=
  ∀ (A B C : Type (max u v)) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (α : A →ₗ[R] B) (β : B →ₗ[R] C),
    Function.Injective α → Function.Surjective β →
    LinearMap.range α = LinearMap.ker β →
    (∀ f : R, f • (LinearMap.range α) = (LinearMap.range α) ⊓ f • (⊤ : Submodule R B)) →
    ∀ ψ : P →ₗ[R] C, ∃ φ : P →ₗ[R] B, β ∘ₗ φ = ψ

section Helpers

variable {R : Type u} [CommRing R]

/-- The linear map `R ⧸ Ideal.span {f} → P` sending `1` to `p`, where `f • p = 0`. -/
noncomputable def cyclicLift {P : Type v} [AddCommGroup P] [Module R P]
    (f : R) (p : P) (hp : f • p = 0) : (R ⧸ Ideal.span {f}) →ₗ[R] P :=
  Submodule.liftQSpanSingleton f (LinearMap.toSpanSingleton R P p) (by simpa using hp)

/-- `cyclicLift f p hp` sends the class of `r` to `r • p`. -/
@[simp] lemma cyclicLift_mk {P : Type v} [AddCommGroup P] [Module R P]
    (f : R) (p : P) (hp : f • p = 0) (r : R) :
    cyclicLift f p hp (Submodule.Quotient.mk r) = r • p :=
  rfl

open Pointwise in
/-- Given a short exact sequence `0 → A → B → C → 0` with `f A = A ∩ f B` for all `f ∈ R`, every
`c : C` with `f • c = 0` has a preimage `b : B` with `f • b = 0`. -/
lemma pure_lift_elem {A : Type v} {B : Type w} {C : Type x} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (α : A →ₗ[R] B) (β : B →ₗ[R] C) (hβ : Function.Surjective β)
    (hrk : LinearMap.range α = LinearMap.ker β)
    (hpure : ∀ f : R,
      f • (LinearMap.range α) = (LinearMap.range α) ⊓ f • (⊤ : Submodule R B))
    (f : R) (c : C) (hc : f • c = 0) :
    ∃ b : B, β b = c ∧ f • b = 0 := by
  obtain ⟨b₀, hb₀⟩ := hβ c
  have hmem : f • b₀ ∈ LinearMap.range α ⊓ f • (⊤ : Submodule R B) :=
    ⟨by rw [hrk, SetLike.mem_coe, LinearMap.mem_ker, map_smul, hb₀, hc],
      Submodule.smul_mem_pointwise_smul b₀ f ⊤ Submodule.mem_top⟩
  rw [← hpure f] at hmem
  obtain ⟨a, ha, hfa⟩ := hmem
  simp only [DistribSMul.toLinearMap_apply] at hfa
  have hβa : β a = 0 := by rwa [← LinearMap.mem_ker, ← hrk]
  exact ⟨b₀ - a, by rw [map_sub, hb₀, hβa, sub_zero], by rw [smul_sub, hfa, sub_self]⟩

/-- For a family `q : J → R`, the generator `lof j (mk 1)` of `⨁_k R / q_k R` is annihilated
by `q j`. -/
lemma lof_smul_self_eq_zero {J : Type v} [DecidableEq J] (q : J → R) (j : J) :
    q j • (DirectSum.lof R J (fun k => R ⧸ Ideal.span {q k}) j
        (Submodule.Quotient.mk 1)) = 0 := by
  rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
    (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton_self _), map_zero]

/-- Every `p : P` with `g • p = 0` is the image of an element `e` with `g • e = 0` under the
canonical map `⨁_{(g, φ)} R / g R → P` indexed by all maps `φ : R / g R → P`. -/
lemma exists_toModule_sigmaCyclic_eq {P : Type v} [AddCommGroup P] [Module R P]
    [DecidableEq (Σ g : R, (R ⧸ Ideal.span {g} →ₗ[R] P))] (g : R) (p : P) (hp : g • p = 0) :
    ∃ e : DirectSum (Σ g : R, (R ⧸ Ideal.span {g} →ₗ[R] P)) (fun i => R ⧸ Ideal.span {i.1}),
      DirectSum.toModule R _ P (fun i => i.2) e = p ∧ g • e = 0 := by
  refine ⟨DirectSum.lof R (Σ g : R, (R ⧸ Ideal.span {g} →ₗ[R] P))
    (fun i => R ⧸ Ideal.span {i.1}) ⟨g, cyclicLift g p hp⟩ (Submodule.Quotient.mk 1), ?_, ?_⟩
  · rw [DirectSum.toModule_lof, cyclicLift_mk, one_smul]
  · exact lof_smul_self_eq_zero (fun i : Σ g : R, (R ⧸ Ideal.span {g} →ₗ[R] P) => i.1)
      ⟨g, cyclicLift g p hp⟩

open Pointwise in
/-- If every `g`-torsion element of `P` lifts along `β` to a `g`-torsion element, then
`g • ker β = ker β ⊓ g • M`. -/
lemma ker_smul_eq_inf_of_torsion_lift {M : Type v} {P : Type w} [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module R P] (β : M →ₗ[R] P)
    (h : ∀ (g : R) (p : P), g • p = 0 → ∃ e, β e = p ∧ g • e = 0) (g : R) :
    g • LinearMap.ker β = LinearMap.ker β ⊓ g • (⊤ : Submodule R M) := by
  apply le_antisymm
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨(LinearMap.ker β).smul_mem g ha,
      Submodule.smul_mem_pointwise_smul a g ⊤ Submodule.mem_top⟩
  · rintro x ⟨hxk, y, -, rfl⟩
    obtain ⟨e, hβe, hge⟩ := h g (β y) (by rwa [← map_smul])
    refine ⟨y - e, by simp [hβe], ?_⟩
    simp [smul_sub, hge]

end Helpers

open Pointwise in
/-- Given a short exact sequence `0 → A → B → C → 0` with `f A = A ∩ f B` for all `f ∈ R`, every
linear map `⨁_i R / f_i R → C` lifts to a linear map `⨁_i R / f_i R → B`. -/
lemma directSum_cyclic_lifts {R : Type u} [CommRing R] {I : Type v} (f : I → R)
    {A : Type w} {B : Type x} {C : Type y} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (α : A →ₗ[R] B) (β : B →ₗ[R] C) (hβ : Function.Surjective β)
    (hrk : LinearMap.range α = LinearMap.ker β)
    (hpure : ∀ f : R,
      f • (LinearMap.range α) = (LinearMap.range α) ⊓ f • (⊤ : Submodule R B))
    (Ψ : (DirectSum I (fun i => R ⧸ Ideal.span {f i})) →ₗ[R] C) :
    ∃ Φ : (DirectSum I (fun i => R ⧸ Ideal.span {f i})) →ₗ[R] B, β ∘ₗ Φ = Ψ := by
  classical
  have hlift : ∀ i, ∃ b : B,
      β b = Ψ (DirectSum.lof R I _ i (Submodule.Quotient.mk 1)) ∧ f i • b = 0 := fun i =>
    pure_lift_elem α β hβ hrk hpure (f i) _
      (by rw [← map_smul, lof_smul_self_eq_zero f i, map_zero])
  choose b hb hfb using hlift
  refine ⟨DirectSum.toModule R I B fun i => cyclicLift (f i) (b i) (hfb i),
    DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | _ r =>
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof, cyclicLift_mk]
    rw [map_smul, hb i, ← map_smul, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      mul_one]

open Pointwise in
/-- For a commutative ring `R` and an `R`-module `P`, `P` is a direct summand of a direct sum of
modules `R / f R` if and only if every linear map from `P` lifts along every short exact sequence
`0 → A → B → C → 0` satisfying `f A = A ∩ f B` for all `f ∈ R`. -/
@[stacks 0ASM]
theorem summand_sum_cyclic_iff_lifting
    (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P] :
    IsSummandOfSumCyclic R P ↔ LiftingProperty R P := by
  constructor
  · rintro ⟨I, f, ι, π, hπι⟩
    intro A B C _ _ _ _ _ _ α β hα hβ hrk hpure ψ
    obtain ⟨Φ, hΦ⟩ := directSum_cyclic_lifts f α β hβ hrk hpure (ψ ∘ₗ π)
    refine ⟨Φ ∘ₗ ι, ?_⟩
    rw [← LinearMap.comp_assoc, hΦ, LinearMap.comp_assoc, hπι, LinearMap.comp_id]
  · intro hlift
    classical
    let Q := ULift.{u} P
    let ε : Q ≃ₗ[R] P := ULift.moduleEquiv
    let I := Σ g : R, (R ⧸ Ideal.span {g} →ₗ[R] Q)
    let β : DirectSum I (fun i => R ⧸ Ideal.span {i.1}) →ₗ[R] Q :=
      DirectSum.toModule R I Q fun i => i.2
    have ht : ∀ (g : R) (q : Q), g • q = 0 → ∃ e, β e = q ∧ g • e = 0 :=
      exists_toModule_sigmaCyclic_eq
    have hβ : Function.Surjective β := fun q => (ht 0 q (zero_smul _ _)).imp fun _ h => h.1
    have hrk := Submodule.range_subtype (LinearMap.ker β)
    obtain ⟨φ, hφ⟩ := hlift (LinearMap.ker β) _ Q (LinearMap.ker β).subtype β
      Subtype.coe_injective hβ hrk
      (by rw [hrk]; exact ker_smul_eq_inf_of_torsion_lift β ht) ε.symm.toLinearMap
    refine ⟨I, fun i => i.1, φ, ε.toLinearMap ∘ₗ β, LinearMap.ext fun p => ?_⟩
    have h := LinearMap.congr_fun hφ p
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe] at h ⊢
    rw [h, ε.apply_symm_apply]
