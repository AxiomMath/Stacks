module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module

/-!
# Constituents of the reductions of lattices (Brauer–Nesbitt, set-theoretic form)

Let `A` be a ring (for us the group ring of a fundamental group with coefficients in `ℤ_ℓ`) and
`𝓜` a family of `A`-modules. Say that an `A`-module `M` has its constituents in `𝓜`
(`Stacks.EtaleCohomology.HasConstituentsIn`) if every simple subquotient of `M` is a retract of
some `𝓜 i`. This class is closed under submodules, quotients and extensions
(`Stacks.EtaleCohomology.HasConstituentsIn.of_injective`, `.of_surjective`, `.of_extension`), and
contains every semisimple member of the family
(`Stacks.EtaleCohomology.hasConstituentsIn_self_of_isSemisimpleModule`).

The set-theoretic Brauer–Nesbitt lemma
(`Stacks.EtaleCohomology.HasConstituentsIn.quotient_lattice`): if `L/ℓL` has its constituents in
`𝓜` and `M₂` is a submodule of `L` containing `ℓⁿL`, then so does `M₂/ℓM₂`. Indeed `L/ℓⁿ⁺¹L` is an
iterated extension of quotients of `L/ℓL` (multiplication by `ℓᵏ`), and `M₂/ℓM₂` is a quotient of
`M₂/(M₂ ∩ ℓⁿ⁺¹L)`, a submodule of `L/ℓⁿ⁺¹L`. Applied to two stable lattices of the same rational
representation (after scaling one into the other) this says that every constituent of the
reduction of one lattice is a constituent of the reduction of the other.

Finally a finite module with its constituents in `𝓜` has every property which is closed under
isomorphisms and extensions and holds for the zero module and the retracts of the `𝓜 i`
(`Stacks.EtaleCohomology.HasConstituentsIn.prop`): this is how the reduction modulo `ℓ` of a
lattice lands in the closure under extensions and summands used for the generic lisse locus of
Laumon's Fourier family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.HasConstituentsIn`.

## Main results

* `Stacks.EtaleCohomology.HasConstituentsIn.of_extension`.
* `Stacks.EtaleCohomology.hasConstituentsIn_self_of_isSemisimpleModule`.
* `Stacks.EtaleCohomology.HasConstituentsIn.quotient_lattice`.
* `Stacks.EtaleCohomology.HasConstituentsIn.prop`.
-/

@[expose] public noncomputable section

universe v

namespace Stacks.EtaleCohomology

variable {A : Type*} [Ring A] {ι : Type*} (𝓜 : ι → Type v) [∀ i, AddCommGroup (𝓜 i)]
  [∀ i, Module A (𝓜 i)]

variable (A) in
/-- **`M` has its constituents in `𝓜`**: every simple subquotient `S` of `M` (a simple module
with a surjection from a submodule of `M`) is a retract of some `𝓜 i`. -/
def HasConstituentsIn (M : Type v) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (W : Submodule A M) (S : Type v) [AddCommGroup S] [Module A S] (q : W →ₗ[A] S),
    Function.Surjective q → IsSimpleModule A S →
      ∃ i, ∃ (f : S →ₗ[A] 𝓜 i) (g : 𝓜 i →ₗ[A] S), g ∘ₗ f = LinearMap.id

variable {𝓜}
variable {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- **Submodules**: constituents pass along an injection. -/
theorem HasConstituentsIn.of_injective (f : N →ₗ[A] M) (hf : Function.Injective f)
    (h : HasConstituentsIn A 𝓜 M) : HasConstituentsIn A 𝓜 N := by
  intro W S _ _ q hq hS
  let e := Submodule.equivMapOfInjective f hf W
  exact h (W.map f) S (q ∘ₗ e.symm.toLinearMap) (hq.comp e.symm.surjective) hS

/-- **Quotients**: constituents pass along a surjection. -/
theorem HasConstituentsIn.of_surjective (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (h : HasConstituentsIn A 𝓜 M) : HasConstituentsIn A 𝓜 N := by
  intro W S _ _ q hq hS
  let f' : W.comap f →ₗ[A] W := f.restrict (fun x hx => hx)
  refine h (W.comap f) S (q ∘ₗ f') (hq.comp ?_) hS
  rintro ⟨w, hw⟩
  obtain ⟨m, rfl⟩ := hf w
  exact ⟨⟨m, hw⟩, rfl⟩

/-- **A module without nonzero elements has its constituents anywhere.** -/
theorem hasConstituentsIn_of_subsingleton [Subsingleton M] : HasConstituentsIn A 𝓜 M := by
  intro W S _ _ q hq hS
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  obtain ⟨w, rfl⟩ := hq s
  exact absurd (by rw [Subsingleton.elim w 0, map_zero]) hs

/-- **Extensions**: if `U ⊆ M` and `M / U` have their constituents in `𝓜`, so does `M`. A simple
subquotient `q : W ↠ S` of `M` either is already a quotient of `W ∩ U`, or kills `W ∩ U` and is a
quotient of the image of `W` in `M / U`. -/
theorem HasConstituentsIn.of_extension (U : Submodule A M) (hU : HasConstituentsIn A 𝓜 U)
    (hQ : HasConstituentsIn A 𝓜 (M ⧸ U)) : HasConstituentsIn A 𝓜 M := by
  intro W S _ _ q hq hS
  let WU : Submodule A W := U.comap W.subtype
  rcases IsSimpleOrder.eq_bot_or_eq_top (WU.map q) with h0 | h1
  · let φ : W →ₗ[A] M ⧸ U := U.mkQ ∘ₗ W.subtype
    have hle : LinearMap.ker φ ≤ LinearMap.ker q := by
      intro x hx
      have hxU : (x : M) ∈ U := by
        simpa [φ, Submodule.Quotient.mk_eq_zero] using hx
      have hx' : q x ∈ WU.map q := ⟨x, hxU, rfl⟩
      rw [h0] at hx'
      simpa using hx'
    let q' : LinearMap.range φ →ₗ[A] S :=
      (LinearMap.ker φ).liftQ q hle ∘ₗ φ.quotKerEquivRange.symm.toLinearMap
    refine hQ (LinearMap.range φ) S q' ?_ hS
    intro s
    obtain ⟨w, rfl⟩ := hq s
    refine ⟨φ.quotKerEquivRange (Submodule.Quotient.mk w), ?_⟩
    simp [q']
  · let g : W.comap U.subtype →ₗ[A] W := U.subtype.restrict (fun x hx => hx)
    refine hU (W.comap U.subtype) S (q ∘ₗ g) ?_ hS
    intro s
    have hs : s ∈ WU.map q := by simp [h1]
    obtain ⟨x, hxU, rfl⟩ := hs
    exact ⟨⟨⟨(x : M), hxU⟩, x.2⟩, rfl⟩

/-- **Isomorphisms**: constituents pass along a linear equivalence. -/
theorem HasConstituentsIn.of_linearEquiv (e : M ≃ₗ[A] N) (h : HasConstituentsIn A 𝓜 M) :
    HasConstituentsIn A 𝓜 N :=
  h.of_surjective e.toLinearMap e.surjective

/-- **A semisimple member of the family has its constituents in the family**: a simple
subquotient `q : W ↠ S` of a semisimple module `M` is a direct summand of `M`, through a
complement of `ker q` in `W` and a complement of `W` in `M`. -/
theorem hasConstituentsIn_self_of_isSemisimpleModule (i : ι) [IsSemisimpleModule A (𝓜 i)] :
    HasConstituentsIn A 𝓜 (𝓜 i) := by
  intro W S _ _ q hq hS
  refine ⟨i, ?_⟩
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker q)
  obtain ⟨D, hD⟩ := exists_isCompl W
  let e : C ≃ₗ[A] S := ((LinearMap.ker q).quotientEquivOfIsCompl C hC).symm.trans
    (q.quotKerEquivOfSurjective hq)
  have he : ∀ c : C, q c = e c := by
    intro c
    simp [e, LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨W.subtype ∘ₗ C.subtype ∘ₗ e.symm.toLinearMap,
    q ∘ₗ W.projectionOnto D hD, ?_⟩
  ext s
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe,
    id_eq]
  rw [show W.projectionOnto D hD (W.subtype (C.subtype (e.symm s))) = C.subtype (e.symm s) from
    Submodule.projectionOnto_apply_left _ _, Submodule.subtype_apply, he, e.apply_symm_apply]

/-- Constituents pass from `M ⧸ p` to the target of a surjection `M → N` killing `p`. -/
private theorem HasConstituentsIn.of_surjective_of_le_ker (p : Submodule A M) (f : M →ₗ[A] N)
    (hp : p ≤ LinearMap.ker f) (hf : Function.Surjective f) (h : HasConstituentsIn A 𝓜 (M ⧸ p)) :
    HasConstituentsIn A 𝓜 N := by
  refine h.of_surjective (p.liftQ f hp) fun n => ?_
  obtain ⟨m, rfl⟩ := hf n
  exact ⟨Submodule.Quotient.mk m, rfl⟩

section Lattice

variable (ℓ : ℕ) (L : Type v) [AddCommGroup L] [Module A L]

variable (A) in
/-- `ℓᵏ L`, the image of multiplication by `ℓᵏ`. -/
abbrev powSMulRange (k : ℕ) : Submodule A L :=
  LinearMap.range ((ℓ ^ k) • (LinearMap.id : L →ₗ[A] L))

variable {ℓ L}

/-- An element lies in `ℓᵏ L` if and only if it is `ℓᵏ` times an element of `L`. -/
theorem mem_powSMulRange {k : ℕ} {x : L} : x ∈ powSMulRange A ℓ L k ↔ ∃ y : L, ℓ ^ k • y = x :=
  LinearMap.mem_range.trans (by simp only [LinearMap.smul_apply, LinearMap.id_apply])

/-- **`L / ℓᵏ L` has the constituents of `L / ℓ L`**: it is an iterated extension of quotients of
`L / ℓ L`, through `0 → ℓᵏ L / ℓᵏ⁺¹ L → L / ℓᵏ⁺¹ L → L / ℓᵏ L → 0` and the surjection
`L / ℓ L → ℓᵏ L / ℓᵏ⁺¹ L` given by multiplication by `ℓᵏ`. -/
theorem HasConstituentsIn.quotient_powSMulRange
    (h : HasConstituentsIn A 𝓜 (L ⧸ powSMulRange A ℓ L 1)) (k : ℕ) :
    HasConstituentsIn A 𝓜 (L ⧸ powSMulRange A ℓ L k) := by
  induction k with
  | zero =>
    have : Subsingleton (L ⧸ powSMulRange A ℓ L 0) := by
      refine Submodule.Quotient.subsingleton_iff.2 ?_
      rw [eq_top_iff]
      intro x _
      exact mem_powSMulRange.2 ⟨x, by simp⟩
    exact hasConstituentsIn_of_subsingleton
  | succ k ih =>
    let R := powSMulRange A ℓ L (k + 1)
    let U : Submodule A (L ⧸ R) := (powSMulRange A ℓ L k).map R.mkQ
    refine HasConstituentsIn.of_extension U ?_ ?_
    · -- `L / ℓ L ↠ ℓᵏ L / ℓᵏ⁺¹ L`
      let b : L →ₗ[A] U := (R.mkQ ∘ₗ ((ℓ ^ k) • LinearMap.id)).codRestrict U
        (fun x => ⟨ℓ ^ k • x, mem_powSMulRange.2 ⟨x, rfl⟩, rfl⟩)
      have hb : powSMulRange A ℓ L 1 ≤ LinearMap.ker b := by
        intro y hy
        obtain ⟨x, rfl⟩ := mem_powSMulRange.1 hy
        rw [LinearMap.mem_ker]
        refine Subtype.ext ?_
        show R.mkQ ((ℓ ^ k) • (ℓ ^ 1 • x)) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        refine (mem_powSMulRange (A := A) (ℓ := ℓ) (k := k + 1)).2 ⟨x, ?_⟩
        rw [smul_smul, ← pow_add]
      refine h.of_surjective_of_le_ker _ b hb ?_
      rintro ⟨u, y, hy, rfl⟩
      obtain ⟨x, rfl⟩ := mem_powSMulRange.1 hy
      exact ⟨x, rfl⟩
    · -- `L / ℓᵏ L ↠ (L / ℓᵏ⁺¹ L) / (ℓᵏ L / ℓᵏ⁺¹ L)`
      have hc : powSMulRange A ℓ L k ≤ LinearMap.ker (U.mkQ ∘ₗ R.mkQ) := by
        intro y hy
        rw [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨y, hy, rfl⟩
      exact ih.of_surjective_of_le_ker _ _ hc (U.mkQ_surjective.comp R.mkQ_surjective)

/-- **Brauer–Nesbitt, set-theoretic form**: if `L / ℓ L` has its constituents in `𝓜` and `M₂` is a
submodule of `L` containing `ℓⁿ L`, then `M₂ / ℓ M₂` has its constituents in `𝓜`. -/
theorem HasConstituentsIn.quotient_lattice (h : HasConstituentsIn A 𝓜 (L ⧸ powSMulRange A ℓ L 1))
    (M₂ : Submodule A L) (n : ℕ) (hn : powSMulRange A ℓ L n ≤ M₂) :
    HasConstituentsIn A 𝓜 (M₂ ⧸ powSMulRange A ℓ M₂ 1) := by
  let R := powSMulRange A ℓ L (n + 1)
  let R₂ : Submodule A M₂ := R.comap M₂.subtype
  -- `M₂ / (M₂ ∩ ℓⁿ⁺¹ L) ⊆ L / ℓⁿ⁺¹ L`
  have h₁ : HasConstituentsIn A 𝓜 (M₂ ⧸ R₂) := by
    refine (h.quotient_powSMulRange (n + 1)).of_injective (R₂.mapQ R M₂.subtype le_rfl) ?_
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    exact Submodule.mkQ_map_self _
  -- `M₂ ∩ ℓⁿ⁺¹ L ⊆ ℓ M₂`
  have hle : R₂ ≤ powSMulRange A ℓ M₂ 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_powSMulRange.1 hx
    refine mem_powSMulRange.2 ⟨⟨ℓ ^ n • y, hn (mem_powSMulRange.2 ⟨y, rfl⟩)⟩, ?_⟩
    rw [Submodule.subtype_apply] at hy
    ext
    show ℓ ^ 1 • (ℓ ^ n • y) = (x : L)
    rw [← hy, smul_smul, ← pow_add, add_comm]
  exact h₁.of_surjective_of_le_ker _ (powSMulRange A ℓ M₂ 1).mkQ
    (by rwa [Submodule.ker_mkQ]) (Submodule.mkQ_surjective _)

end Lattice

/-- **A finite module with its constituents in `𝓜` has every property closed under
isomorphisms and extensions, true for the zero module and for the retracts of the `𝓜 i`**: by
induction on the cardinality, splitting off a simple submodule. -/
theorem HasConstituentsIn.prop (P : ∀ (X : Type v) [AddCommGroup X] [Module A X], Prop)
    (_hiso : ∀ (X Y : Type v) [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y],
      (X ≃ₗ[A] Y) → P X → P Y)
    (hzero : ∀ (X : Type v) [AddCommGroup X] [Module A X], Subsingleton X → P X)
    (hret : ∀ (X : Type v) [AddCommGroup X] [Module A X] [Finite X] (i : ι) (f : X →ₗ[A] 𝓜 i)
      (g : 𝓜 i →ₗ[A] X), g ∘ₗ f = LinearMap.id → P X)
    (hext : ∀ (X : Type v) [AddCommGroup X] [Module A X] [Finite X] (U : Submodule A X),
      P U → P (X ⧸ U) → P X)
    (M : Type v) [AddCommGroup M] [Module A M] [Finite M] (hM : HasConstituentsIn A 𝓜 M) :
    P M := by
  suffices H : ∀ (d : ℕ) (X : Type v) [AddCommGroup X] [Module A X] [Finite X],
      Nat.card X = d → HasConstituentsIn A 𝓜 X → P X from H _ M rfl hM
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro X _ _ _ hd hX
  rcases subsingleton_or_nontrivial X with hs | hnt
  · exact hzero X hs
  have : IsArtinian A X := isArtinian_of_finite
  have : IsStronglyAtomic (Submodule A X) := instIsStronglyAtomicOfWellFoundedLT
  obtain ⟨S, hS⟩ := IsAtomic.eq_bot_or_exists_atom_le (⊤ : Submodule A X) |>.resolve_left
    (by simp) |>.imp fun _ h => h.1
  have : IsSimpleModule A S := (isSimpleModule_iff_isAtom).2 hS
  obtain ⟨i, f, g, hfg⟩ := hX S S LinearMap.id Function.surjective_id inferInstance
  have : Finite (X ⧸ S) := Finite.of_surjective _ (Submodule.mkQ_surjective S)
  refine hext X S (hret S i f g hfg) ?_
  have hcard : Nat.card (X ⧸ S) < d := by
    rw [← hd, Submodule.card_eq_card_quotient_mul_card S]
    have h1 : 1 < Nat.card S := by
      have : Nontrivial S := IsSimpleModule.nontrivial A S
      exact Finite.one_lt_card
    have h2 : 0 < Nat.card (X ⧸ S) := Nat.card_pos
    nlinarith
  exact ih _ hcard (X ⧸ S) rfl (hX.of_surjective S.mkQ S.mkQ_surjective)

end Stacks.EtaleCohomology

end
