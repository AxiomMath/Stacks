module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.FreeProduct.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Lemma 19.2.7 (Tag 05NW) of the Stacks Project, part of Baer's argument that
every `R`-module embeds in an injective module.  Throughout, `R` is a fixed commutative
ring and all modules are `R`-modules.  An *ideal* of `R` is an `R`-submodule
`a ⊆ R` (i.e. `Ideal R`), and `Hom_R(-,-)` denotes `R`-module homomorphisms.

## Main Definitions

* `I(M) = { (a, φ) : a an ideal of R, φ ∈ Hom_R(a, M) }`  — the index set.
* `S(M) = ⨁_{(a,φ) ∈ I(M)} a`  and  `T(M) = ⨁_{(a,φ) ∈ I(M)} R`  — the two source modules.
* `e_M : S(M) → M` and `d_M : S(M) → T(M)` — the two structure maps, determined on the
  summand indexed by `(a, φ)` by `e_M (ι a) = φ a` and `d_M (ι a) = a` (the same element,
  viewed in the corresponding `R`-summand of `T(M)`).  In particular `d_M` is injective.
* `𝐌(M) = (M ⊕ T(M)) / U_M`, the pushout of `M ← S(M) → T(M)`, where
  `U_M = { (e_M s, -d_M s) : s ∈ S(M) }`.  We write `u_M : M → 𝐌(M)` and
  `v_M : T(M) → 𝐌(M)` for the two canonical maps into the pushout.

## Main Statements

1. (Functoriality) `M ↦ (u_M : M → 𝐌(M))` is functorial: there is an assignment on
   morphisms preserving identities and composition, and the maps `u_M` form a natural
   transformation from the identity functor to `𝐌`.
2. (Injectivity) `u_M : M → 𝐌(M)` is injective for every `M`.
3. (Extension property) For every ideal `a` and `φ : a → M`, there is `φ' : R → 𝐌(M)`
   with `φ' |_a = u_M ∘ φ`.
-/

universe u

-- (Classical opened locally where needed)

variable (R : Type u) [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]

-- Main Definition(s)

/-- Definition 1: the index set `I(M)`, consisting of pairs `(a, φ)` of an ideal `a` of
`R` together with an `R`-module map `φ : a → M`. -/
abbrev BaerIndex : Type u := Σ a : Ideal R, a →ₗ[R] M

/-- Definition 2: `S(M) = ⨁_{(a,φ) ∈ I(M)} a`, the summand indexed by `(a, φ)` being the
ideal `a` viewed as an `R`-module. -/
abbrev BaerS : Type u := DirectSum (BaerIndex R M) (fun i => i.1)

/-- Definition 2: `T(M) = ⨁_{(a,φ) ∈ I(M)} R`, each summand a copy of `R`. -/
abbrev BaerT : Type u := DirectSum (BaerIndex R M) (fun _ => R)

open Classical in
/-- Definition 3: `e_M : S(M) → M`, determined on the summand indexed by `(a, φ)` by
`e_M (ι a) = φ a`. -/
noncomputable def baerE : BaerS R M →ₗ[R] M :=
  DirectSum.toModule R _ M (fun i => i.2)

open Classical in
/-- Definition 3: `d_M : S(M) → T(M)`, sending `a` in the summand indexed by `(a, φ)` to
the same element `a`, viewed in the `R`-summand of `T(M)` indexed by the same `(a, φ)`.
On each summand it is the inclusion `a ↪ R`, so `d_M` is injective. -/
noncomputable def baerD : BaerS R M →ₗ[R] BaerT R M :=
  DirectSum.toModule R _ _
    (fun i => (DirectSum.lof R (BaerIndex R M) (fun _ => R) i).comp i.1.subtype)

/-- The combined map `S(M) → M ⊕ T(M)`, `s ↦ (e_M s, -d_M s)`. -/
noncomputable def baerRel : BaerS R M →ₗ[R] (M × BaerT R M) :=
  (baerE R M).prod (-(baerD R M))

/-- Definition 4: the submodule `U_M = { (e_M s, -d_M s) : s ∈ S(M) }` of `M ⊕ T(M)`. -/
noncomputable def baerU : Submodule R (M × BaerT R M) := LinearMap.range (baerRel R M)

/-- Definition 4: `𝐌(M) = (M ⊕ T(M)) / U_M`, the pushout of `M ← S(M) → T(M)`. -/
abbrev BaerM : Type u := (M × BaerT R M) ⧸ baerU R M

/-- Definition 4: the canonical map `u_M : M → 𝐌(M)`, `m ↦ (m, 0) + U_M`. -/
noncomputable def baerUMap : M →ₗ[R] BaerM R M :=
  (baerU R M).mkQ.comp (LinearMap.inl R M (BaerT R M))

/-- Definition 4: the canonical map `v_M : T(M) → 𝐌(M)`, `t ↦ (0, t) + U_M`. -/
noncomputable def baerV : BaerT R M →ₗ[R] BaerM R M :=
  (baerU R M).mkQ.comp (LinearMap.inr R M (BaerT R M))

/-- `e_M` sends the element `x` of the summand indexed by `(a, φ)` to `φ x`. -/
private theorem baerE_lof_aux [DecidableEq (BaerIndex R M)] (a : Ideal R) (φ : a →ₗ[R] M)
    (x : a) :
    baerE R M (DirectSum.lof R (BaerIndex R M) (fun i => (i.1 : Type u)) ⟨a, φ⟩ x) = φ x := by
  rw [baerE]
  convert DirectSum.toModule_lof (ι := BaerIndex R M) (M := fun i => i.1) R ⟨a, φ⟩ x

/-- `d_M` sends the element `x` of the summand indexed by `(a, φ)` to `x` in the matching copy
of `R`. -/
private theorem baerD_lof_aux [DecidableEq (BaerIndex R M)] (a : Ideal R) (φ : a →ₗ[R] M)
    (x : a) :
    baerD R M (DirectSum.lof R (BaerIndex R M) (fun i => (i.1 : Type u)) ⟨a, φ⟩ x)
      = DirectSum.lof R (BaerIndex R M) (fun _ => R) ⟨a, φ⟩ (x : R) := by
  rw [baerD]
  convert DirectSum.toModule_lof (ι := BaerIndex R M) (M := fun i => i.1) R ⟨a, φ⟩ x
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  congr!

/- ARGUMENT (proved): For `s ∈ S(M)`, `u_M (e_M s) - v_M (d_M s)` is the class of
`(e_M s, 0) - (0, d_M s) = (e_M s, -d_M s) = baerRel s ∈ U_M = range baerRel`, hence `0` in
the quotient. Formally: `LinearMap.ext`, then reduce to `mkQ (e_M s, -d_M s) = 0` via
`Submodule.Quotient.mk_eq_zero`, with witness `s`. -/
/-- The pushout square commutes: `u_M ∘ e_M = v_M ∘ d_M` as maps `S(M) → 𝐌(M)`. -/
theorem baer_pushout_square :
    (baerUMap R M).comp (baerE R M) = (baerV R M).comp (baerD R M) := by
  apply LinearMap.ext
  intro s
  simp only [LinearMap.comp_apply, baerUMap, baerV,
    LinearMap.inl_apply, LinearMap.inr_apply]
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨s, ?_⟩
  rw [baerRel]
  ext <;> simp [LinearMap.prod_apply]

-- Main Statement(s)

section Functorial

/-- Reindexing of the index set `I(M) → I(N)` induced by `χ : M → N`, sending `(a, φ)` to
`(a, χ ∘ φ)`. The ideal component is unchanged. -/
def baerIdx {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (χ : M →ₗ[R] N) : BaerIndex R M → BaerIndex R N := fun i => ⟨i.1, χ.comp i.2⟩

open Classical in
/-- `S(χ) : S(M) → S(N)`, the identity on each ideal summand `a`, reindexed by `baerIdx`. -/
noncomputable def baerSMap {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R
    N]
    (χ : M →ₗ[R] N) : BaerS R M →ₗ[R] BaerS R N :=
  DirectSum.toModule R _ _ (fun i =>
    (DirectSum.lof R (BaerIndex R N) (fun j => (j.1 : Type u)) (baerIdx R χ i)).comp
      (LinearMap.id : (i.1 : Type u) →ₗ[R] (i.1 : Type u)))

open Classical in
/-- `T(χ) : T(M) → T(N)`, the identity on each `R`-summand, reindexed by `baerIdx`. -/
noncomputable def baerTMap {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R
    N]
    (χ : M →ₗ[R] N) : BaerT R M →ₗ[R] BaerT R N :=
  DirectSum.toModule R _ _ (fun i => DirectSum.lof R (BaerIndex R N) (fun _ => R) (baerIdx R χ i))

/-- Compatibility square 1: `χ ∘ e_M = e_N ∘ S(χ)`.  (Proved.) -/
theorem baerE_natural {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (χ : M →ₗ[R] N) : χ.comp (baerE R M) = (baerE R N).comp (baerSMap R χ) := by
  classical
  apply DirectSum.linearMap_ext; intro i; apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply]
  rw [baerE, DirectSum.toModule_lof, baerSMap, DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply]
  rw [baerE, DirectSum.toModule_lof]; rfl

/-- Compatibility square 2: `T(χ) ∘ d_M = d_N ∘ S(χ)`.  (Proved.) -/
theorem baerD_natural {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (χ : M →ₗ[R] N) : (baerTMap R χ).comp (baerD R M) = (baerD R N).comp (baerSMap R χ) := by
  classical
  apply DirectSum.linearMap_ext; intro i; apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply]
  rw [baerD, DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [baerTMap, DirectSum.toModule_lof, baerSMap, DirectSum.toModule_lof]
  simp only [LinearMap.comp_apply]
  rw [baerD, DirectSum.toModule_lof]; rfl

/-- The induced map `M ⊕ T(M) → N ⊕ T(N)`, `(m, t) ↦ (χ m, T(χ) t)`. -/
noncomputable def baerPair {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R
    N]
    (χ : M →ₗ[R] N) : (M × BaerT R M) →ₗ[R] (N × BaerT R N) := χ.prodMap (baerTMap R χ)

/-- `baerPair χ ∘ baerRel M = baerRel N ∘ S(χ)`: the relation submodule transports.  (Proved
from the two naturality squares.) -/
theorem baerPair_baerRel {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (χ : M →ₗ[R] N) (s : BaerS R M) :
    baerPair R χ (baerRel R M s) = baerRel R N (baerSMap R χ s) := by
  have he := baerE_natural R χ; rw [LinearMap.ext_iff] at he
  have hd := baerD_natural R χ; rw [LinearMap.ext_iff] at hd
  rw [baerPair, baerRel, baerRel]
  apply Prod.ext
  · simp only [LinearMap.prodMap_apply, LinearMap.prod_apply, Function.prod]
    simpa using he s
  · simp only [LinearMap.prodMap_apply, LinearMap.prod_apply, Function.prod, LinearMap.neg_apply,
      map_neg]
    have := hd s; simp only [LinearMap.comp_apply] at this; rw [this]

/-- `baerPair χ` maps `U_M` into `U_N`, allowing descent to the quotient.  (Proved.) -/
theorem baerU_le {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (χ : M →ₗ[R] N) : baerU R M ≤ Submodule.comap (baerPair R χ) (baerU R N) := by
  rw [baerU, LinearMap.range_le_iff_comap, eq_top_iff]
  intro s _
  simp only [Submodule.mem_comap]
  rw [baerPair_baerRel, baerU]
  exact ⟨baerSMap R χ s, rfl⟩

/-- `𝐌(χ) : 𝐌(M) → 𝐌(N)`, the descent of `baerPair χ` to the pushout quotients. -/
noncomputable def baerMMap {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R
    N]
    (χ : M →ₗ[R] N) : BaerM R M →ₗ[R] BaerM R N :=
  Submodule.mapQ (baerU R M) (baerU R N) (baerPair R χ) (baerU_le R χ)

/-- `baerIdx id = id`. -/
theorem baerIdx_id {M : Type u} [AddCommGroup M] [Module R M] :
    baerIdx R (LinearMap.id : M →ₗ[R] M) = id := by funext i; simp [baerIdx]

/-- `baerIdx (χ' ∘ χ) = baerIdx χ' ∘ baerIdx χ`. -/
theorem baerIdx_comp {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (χ : M →ₗ[R] N) (χ' : N →ₗ[R] P) :
    baerIdx R (χ'.comp χ) = (baerIdx R χ') ∘ (baerIdx R χ) := by
  funext i; simp [baerIdx, LinearMap.comp_assoc]

/-- `T(id) = id`. -/
theorem baerTMap_id {M : Type u} [AddCommGroup M] [Module R M] :
    baerTMap R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext; intro i; apply LinearMap.ext; intro x
  simp only [baerTMap, LinearMap.comp_apply, DirectSum.toModule_lof, LinearMap.id_comp]
  rw [show baerIdx R (LinearMap.id : M →ₗ[R] M) i = i from by rw [baerIdx_id]; rfl]

/-- `T(χ' ∘ χ) = T(χ') ∘ T(χ)`. -/
theorem baerTMap_comp {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (χ : M →ₗ[R] N) (χ' : N →ₗ[R] P) :
    baerTMap R (χ'.comp χ) = (baerTMap R χ').comp (baerTMap R χ) := by
  classical
  apply DirectSum.linearMap_ext; intro i; apply LinearMap.ext; intro x
  simp only [baerTMap, LinearMap.comp_apply, DirectSum.toModule_lof]
  rw [show baerIdx R (χ'.comp χ) i = baerIdx R χ' (baerIdx R χ i) from by rw [baerIdx_comp]; rfl]

/-- `baerPair id = id`. -/
theorem baerPair_id {M : Type u} [AddCommGroup M] [Module R M] :
    baerPair R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  rw [baerPair, baerTMap_id]; ext x <;> simp

/-- `baerPair (χ' ∘ χ) = baerPair χ' ∘ baerPair χ`. -/
theorem baerPair_comp {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (χ : M →ₗ[R] N) (χ' : N →ₗ[R] P) :
    baerPair R (χ'.comp χ) = (baerPair R χ').comp (baerPair R χ) := by
  rw [baerPair, baerPair, baerPair, baerTMap_comp]; ext x <;> simp

/-- Functor law 1: `𝐌(id) = id`. -/
theorem baerMMap_id {M : Type u} [AddCommGroup M] [Module R M] :
    baerMMap R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  simp only [baerMMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
    baerPair_id, LinearMap.id_coe, id_eq, LinearMap.id_comp]

/-- Functor law 2: `𝐌(χ' ∘ χ) = 𝐌(χ') ∘ 𝐌(χ)`. -/
theorem baerMMap_comp {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (χ : M →ₗ[R] N) (χ' : N →ₗ[R] P) :
    baerMMap R (χ'.comp χ) = (baerMMap R χ').comp (baerMMap R χ) := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  simp only [baerMMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
    baerPair_comp]

/-- Naturality: `𝐌(χ) ∘ u_M = u_N ∘ χ`. -/
theorem baerMMap_natural {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (χ : M →ₗ[R] N) : (baerMMap R χ).comp (baerUMap R M) = (baerUMap R N).comp χ := by
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, baerUMap, baerMMap]
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  simp [baerPair, LinearMap.prodMap_apply, map_zero]

end Functorial

/-- Statement 1 (Functoriality).  The construction `M ↦ (u_M : M → 𝐌(M))` is functorial:
there is an assignment `MMap` on `R`-module morphisms `χ : M → N`, giving a map
`MMap χ : 𝐌(M) → 𝐌(N)`, such that

1. `MMap id = id` (identities are preserved);
2. `MMap (χ' ∘ χ) = MMap χ' ∘ MMap χ` (composition is preserved);
3. the maps `u_M` are a natural transformation `𝟭 ⟹ 𝐌`, i.e.
   `MMap χ ∘ u_M = u_N ∘ χ` for every `χ : M → N`.

Here the morphism action `MMap` is quantified existentially, modelling "there is a
functor `𝐌` with `u` a natural transformation from the identity to `𝐌`". -/
@[stacks 05NW "(1)"]
theorem baer_functorial :
    ∃ MMap : ∀ {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
        (M →ₗ[R] N) → (BaerM R M →ₗ[R] BaerM R N),
      (∀ (M : Type u) [AddCommGroup M] [Module R M],
          MMap (LinearMap.id : M →ₗ[R] M) = LinearMap.id) ∧
      (∀ {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
          [AddCommGroup P] [Module R P] (χ : M →ₗ[R] N) (χ' : N →ₗ[R] P),
          MMap (χ'.comp χ) = (MMap χ').comp (MMap χ)) ∧
      (∀ {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
          (χ : M →ₗ[R] N),
          (MMap χ).comp (baerUMap R M) = (baerUMap R N).comp χ) := by
  refine ⟨fun {M N} _ _ _ _ χ => baerMMap R χ, ?_, ?_, ?_⟩
  · intro M _ _; exact baerMMap_id R
  · intro M N P _ _ _ _ _ _ χ χ'; exact baerMMap_comp R χ χ'
  · intro M N _ _ _ _ χ; exact baerMMap_natural R χ

/-- Helper: the component of `d_M s` at index `i` is the inclusion `a ↪ R` applied to the
`i`-component of `s`.  (Proved by `DirectSum` induction.) -/
theorem baerD_component (s : BaerS R M) (i : BaerIndex R M) :
    DirectSum.component R (BaerIndex R M) (fun _ => R) i (baerD R M s)
      = (DirectSum.component R (BaerIndex R M) (fun j => (j.1 : Type u)) i s : R) := by
  classical
  rw [baerD]
  induction s using DirectSum.induction_on with
  | zero => simp
  | of j x =>
      rw [← DirectSum.lof_eq_of R, DirectSum.toModule_lof]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      by_cases h : i = j
      · subst h
        rw [DirectSum.component.lof_self, DirectSum.component.lof_self]
      · rw [DirectSum.component.of, DirectSum.component.of, dite_eq_right (Ne.symm h),
            dite_eq_right (Ne.symm
          h)]
        rfl
  | add x y hx hy => simp [hx, hy]

/-- `d_M` is injective: on each summand it is the inclusion `a ↪ R`, and the inclusions land
in distinct summands.  (Proved via `baerD_component`.) -/
theorem baerD_injective : Function.Injective (baerD R M) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  ext i
  have hcomp := baerD_component R M s i
  rw [hs] at hcomp
  simp only [map_zero] at hcomp
  have h0 : (DirectSum.component R (BaerIndex R M) (fun j => (j.1 : Type u)) i s
      : (i.1 : Type u)) = 0 := by
    apply Subtype.ext
    simpa using hcomp.symm
  exact congrArg _ h0

/-- Statement 2 (Injectivity).  The canonical map `u_M : M → 𝐌(M)` is injective. -/
/- ARGUMENT (proved): `u_M m = 0` means `(m, 0) ∈ U_M = range baerRel`, i.e. there is
`s ∈ S(M)` with `e_M s = m` and `-d_M s = 0`. Then `d_M s = 0`, so `s = 0` by injectivity
of `d_M` (`baerD_injective`), whence `m = e_M 0 = 0`. -/
@[stacks 05NW "(2)"]
theorem baer_uMap_injective : Function.Injective (baerUMap R M) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  rw [baerUMap, LinearMap.comp_apply, LinearMap.inl_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, baerU, LinearMap.mem_range] at hm
  obtain ⟨s, hs⟩ := hm
  have h1 : baerE R M s = m := congrArg Prod.fst hs
  have h2 : (-(baerD R M)) s = 0 := congrArg Prod.snd hs
  have hd : baerD R M s = 0 := by
    have := h2; rw [LinearMap.neg_apply, neg_eq_zero] at this; exact this
  have hs0 : s = 0 := baerD_injective R M (by rw [hd, map_zero])
  rw [hs0, map_zero] at h1
  exact h1.symm

/-- Statement 3 (Extension property).  For every ideal `a` and `R`-module map
`φ : a → M`, there is an `R`-module map `φ' : R → 𝐌(M)` with `φ' |_a = u_M ∘ φ`, i.e.
`φ' (a) = u_M (φ a)` for all `a ∈ a`. -/
/- ARGUMENT (proved): The pair `(a, φ)` is one of the indices. Take
`φ' = v_M ∘ ⱼ_(a,φ)`, the canonical inclusion of the `(a,φ)` `R`-summand of `T(M)` followed
by `v_M`. For `x ∈ a`, `d_M (ι x) = ⱼ x` and `e_M (ι x) = φ x`, so by the pushout square
`φ'(x) = v_M (ⱼ x) = v_M (d_M (ι x)) = u_M (e_M (ι x)) = u_M (φ x)`. -/
@[stacks 05NW "(3)"]
theorem baer_extension (a : Ideal R) (φ : a →ₗ[R] M) :
    ∃ φ' : R →ₗ[R] BaerM R M,
      φ'.comp a.subtype = (baerUMap R M).comp φ := by
  classical
  refine ⟨(baerV R M).comp (DirectSum.lof R (BaerIndex R M) (fun _ => R) ⟨a, φ⟩), ?_⟩
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [← baerE_lof_aux R M a φ x, ← baerD_lof_aux R M a φ x]
  exact LinearMap.congr_fun (baer_pushout_square R M).symm _

section Pushout

variable {N : Type u} [AddCommGroup N] [Module R N]

open Classical in
/-- The top horizontal arrow `⨁_{(a, φ)} a → M` of the defining square of `𝐌(M)`, read on
the summands: the element `x` of the ideal `a`, placed in the summand indexed by the pair
`(a, φ)`, is sent to `φ x ∈ M`.  The direct sum over the sigma type `I(M) = Σ a, Hom(a, M)`
realizes the iterated coproduct `⨁_a ⨁_{φ ∈ Hom(a, M)}`. -/
@[stacks 05NV "the top horizontal arrow"]
theorem baerE_lof (a : Ideal R) (φ : a →ₗ[R] M) (x : a) :
    baerE R M (DirectSum.lof R (BaerIndex R M) (fun i => (i.1 : Type u)) ⟨a, φ⟩ x) = φ x := by
  exact baerE_lof_aux R M a φ x

open Classical in
/-- The left vertical arrow `⨁_{(a, φ)} a → ⨁_{(a, φ)} R` of the defining square of `𝐌(M)`,
read on the summands: the element `x` of the ideal `a`, placed in the summand indexed by the
pair `(a, φ)`, is sent to the same element `x`, now viewed in the copy of `R` indexed by that
same pair `(a, φ)`. -/
@[stacks 05NV "the left vertical arrow"]
theorem baerD_lof (a : Ideal R) (φ : a →ₗ[R] M) (x : a) :
    baerD R M (DirectSum.lof R (BaerIndex R M) (fun i => (i.1 : Type u)) ⟨a, φ⟩ x)
      = DirectSum.lof R (BaerIndex R M) (fun _ => R) ⟨a, φ⟩ (x : R) := by
  exact baerD_lof_aux R M a φ x

/-- The map out of `𝐌(M)` determined by a commutative square on the two canonical maps:
given `f : M → N` and `g : T(M) → N` with `f ∘ e_M = g ∘ d_M`, the assignment
`(m, t) ↦ f m + g t` kills the relation submodule `U_M` and therefore descends to
`𝐌(M) = (M ⊕ T(M)) / U_M`. -/
noncomputable def baerDesc (f : M →ₗ[R] N) (g : BaerT R M →ₗ[R] N)
    (h : f.comp (baerE R M) = g.comp (baerD R M)) : BaerM R M →ₗ[R] N :=
  (baerU R M).liftQ (f.coprod g) <| by
    rw [baerU, LinearMap.range_le_ker_iff]
    rw [LinearMap.ext_iff] at h
    apply LinearMap.ext
    intro s
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, baerRel, LinearMap.prod_apply,
      Function.prod, LinearMap.coprod_apply, LinearMap.neg_apply, map_neg]
    rw [← sub_eq_add_neg, sub_eq_zero]
    exact h s

/-- `baerDesc` restricted along `u_M : M → 𝐌(M)` recovers the map `f` it was built from. -/
theorem baerDesc_comp_uMap (f : M →ₗ[R] N) (g : BaerT R M →ₗ[R] N)
    (h : f.comp (baerE R M) = g.comp (baerD R M)) :
    (baerDesc R M f g h).comp (baerUMap R M) = f := by
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, baerUMap, baerDesc, LinearMap.inl_apply, Submodule.mkQ_apply,
    Submodule.liftQ_apply, LinearMap.coprod_apply, map_zero, add_zero]

/-- `baerDesc` restricted along `v_M : T(M) → 𝐌(M)` recovers the map `g` it was built from. -/
theorem baerDesc_comp_v (f : M →ₗ[R] N) (g : BaerT R M →ₗ[R] N)
    (h : f.comp (baerE R M) = g.comp (baerD R M)) :
    (baerDesc R M f g h).comp (baerV R M) = g := by
  apply LinearMap.ext
  intro t
  simp only [LinearMap.comp_apply, baerV, baerDesc, LinearMap.inr_apply, Submodule.mkQ_apply,
    Submodule.liftQ_apply, LinearMap.coprod_apply, map_zero, zero_add]

/-- Two maps out of `𝐌(M)` that agree after restriction along both canonical maps `u_M` and
`v_M` are equal: the quotient `𝐌(M)` is generated by the images of `M` and of `T(M)`. -/
theorem baerM_hom_ext {k₁ k₂ : BaerM R M →ₗ[R] N}
    (hu : k₁.comp (baerUMap R M) = k₂.comp (baerUMap R M))
    (hv : k₁.comp (baerV R M) = k₂.comp (baerV R M)) : k₁ = k₂ := by
  apply Submodule.linearMap_qext
  refine LinearMap.prod_ext ?_ ?_
  · rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
    exact hu
  · rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
    exact hv

/-- The module `𝐌(M)`, together with the canonical maps `u_M : M → 𝐌(M)` and
`v_M : T(M) → 𝐌(M)`, is the pushout of `M ← S(M) → T(M)`: for every `R`-module `N` and every
pair of maps `f : M → N`, `g : T(M) → N` making the outer square commute, there is a unique
`k : 𝐌(M) → N` with `k ∘ u_M = f` and `k ∘ v_M = g`.  Together with `baer_pushout_square`,
`baerE_lof` and `baerD_lof` this says that the square

    ⨁_{(a, φ)} a  --e_M-->  M
         |                   |
        d_M                 u_M
         v                   v
    ⨁_{(a, φ)} R  --v_M-->  𝐌(M)

is the pushout square defining `𝐌(M)`. -/
@[stacks 05NV "the pushout defining 𝐌(M)"]
theorem baer_pushout_universal (f : M →ₗ[R] N) (g : BaerT R M →ₗ[R] N)
    (h : f.comp (baerE R M) = g.comp (baerD R M)) :
    ∃! k : BaerM R M →ₗ[R] N, k.comp (baerUMap R M) = f ∧ k.comp (baerV R M) = g := by
  refine ⟨baerDesc R M f g h, ⟨baerDesc_comp_uMap R M f g h, baerDesc_comp_v R M f g h⟩, ?_⟩
  intro k hk
  refine baerM_hom_ext R M ?_ ?_
  · rw [hk.1, baerDesc_comp_uMap]
  · rw [hk.2, baerDesc_comp_v]

end Pushout
