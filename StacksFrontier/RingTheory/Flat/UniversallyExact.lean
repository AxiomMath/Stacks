module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Examples of universally exact sequences

Fix a commutative ring `R`. All modules are `R`-modules and all maps are
`R`-module homomorphisms. The tensor product `⊗` is taken over `R`.

This formalizes Example 10.82.2 of the Stacks project (tag 058J), in the section
on universally injective module maps.

## Definitions

* **Universally injective map.** Imported from `StacksFrontier.RingTheory.Flat.UniversallyInjective`:
  a map `f : M → N` is *universally injective* if for every `R`-module `Q` the
  induced map `f ⊗ id_Q : M ⊗ Q → N ⊗ Q` is injective.  In Lean `f ⊗ id_Q` is
  `LinearMap.rTensor Q f`.

* **Short exact sequence.** `0 → M₁ → M₂ → M₃ → 0` with `f₁` injective, `f₂`
  surjective and `range f₁ = ker f₂`.

* **Universally exact sequence.** A short exact sequence whose first map `f₁` is
  universally injective.  (As noted in the source, since `- ⊗ Q` is right exact,
  this single extra condition is equivalent to exactness of the tensored sequence.)

* **Split short exact sequence.** A short exact sequence whose surjection `f₂`
  admits an `R`-linear section `s : M₃ → M₂` with `f₂ ∘ s = id`.

* **Directed system of short exact sequences.** Indexed by a directed set `(I, ≤)`,
  a family of short exact sequences with transition maps that commute with the
  `f₁, f₂` and form directed systems.  Its colimit is the sequence of (filtered)
  colimits, with the induced maps; the colimits are `Module.DirectLimit` and the
  induced maps are `Module.DirectLimit.map`.

## Main results

1. A split short exact sequence is universally exact (equivalently, its `f₁` is
   universally injective).
2. The colimit of a directed system of universally exact sequences is universally
   exact.
3. (Corollary) The colimit of a directed system of split exact sequences is
   universally exact.

## Notes

* The forward reference of Example 058J ("conversely, any universally exact
  sequence arises in this way", Theorem 058K) is not part of the content here and
  is not formalized.
* "Directed" and "filtered" colimits agree in this `Ab`-enriched / abelian setting.
-/

@[expose] public section
universe u v

variable {R : Type u} [CommRing R]

/-- A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of `R`-modules:
`f₁` is injective, `f₂` is surjective, and `range f₁ = ker f₂`. -/
@[sga "3 XV 2.10"]
structure ShortExact (M₁ M₂ M₃ : Type v) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] where
  /-- The first map `M₁ → M₂`. -/
  f₁ : M₁ →ₗ[R] M₂
  /-- The second map `M₂ → M₃`. -/
  f₂ : M₂ →ₗ[R] M₃
  /-- `f₁` is injective. -/
  inj : Function.Injective f₁
  /-- `f₂` is surjective. -/
  surj : Function.Surjective f₂
  /-- Exactness in the middle: `im f₁ = ker f₂`. -/
  exact : LinearMap.range f₁ = LinearMap.ker f₂

/--
A short exact sequence is *universally exact* when its first map `f₁` is
universally injective. -/
abbrev ShortExact.UniversallyExact {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (S : ShortExact (R := R) M₁ M₂ M₃) : Prop :=
  UniversallyInjective S.f₁

/--
A short exact sequence is *split* when its surjection `f₂` admits an `R`-linear
section `s : M₃ → M₂` with `f₂ ∘ s = id`. -/
abbrev ShortExact.IsSplit {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (S : ShortExact (R := R) M₁ M₂ M₃) : Prop :=
  ∃ s : M₃ →ₗ[R] M₂, S.f₂ ∘ₗ s = LinearMap.id

/--
Indexed by a directed set `(ι, ≤)`: for each index `i` a short exact sequence
`0 → M₁ i → M₂ i → M₃ i → 0`, together with transition maps `t₁, t₂, t₃` forming
directed systems and commuting with the `f₁, f₂`.

The fields `tr₁` and `tr₂` record commutativity of the transition maps with the
`f₁` and `f₂`. The colimit sequence is obtained by applying `Module.DirectLimit`
and `Module.DirectLimit.map`; see the statements below. -/
structure DirectedSES (ι : Type v) [Preorder ι]
    (M₁ M₂ M₃ : ι → Type v)
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)] where
  /-- Transition maps for the family `M₁`. -/
  t₁ : (i j : ι) → i ≤ j → M₁ i →ₗ[R] M₁ j
  /-- Transition maps for the family `M₂`. -/
  t₂ : (i j : ι) → i ≤ j → M₂ i →ₗ[R] M₂ j
  /-- Transition maps for the family `M₃`. -/
  t₃ : (i j : ι) → i ≤ j → M₃ i →ₗ[R] M₃ j
  /-- `(M₁, t₁)` is a directed system. -/
  ds₁ : DirectedSystem M₁ (fun i j h => t₁ i j h)
  /-- `(M₂, t₂)` is a directed system. -/
  ds₂ : DirectedSystem M₂ (fun i j h => t₂ i j h)
  /-- `(M₃, t₃)` is a directed system. -/
  ds₃ : DirectedSystem M₃ (fun i j h => t₃ i j h)
  /-- The short exact sequence at each index. -/
  seq : (i : ι) → ShortExact (R := R) (M₁ i) (M₂ i) (M₃ i)
  /-- Transition maps commute with the first maps. -/
  tr₁ : ∀ i j (h : i ≤ j), (seq j).f₁ ∘ₗ t₁ i j h = t₂ i j h ∘ₗ (seq i).f₁
  /-- Transition maps commute with the second maps. -/
  tr₂ : ∀ i j (h : i ≤ j), (seq j).f₂ ∘ₗ t₂ i j h = t₃ i j h ∘ₗ (seq i).f₂

namespace DirectedSES

variable {ι : Type v} [Preorder ι]
    {M₁ M₂ M₃ : ι → Type v}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)]
    [DecidableEq ι]
    (D : DirectedSES (R := R) ι M₁ M₂ M₃)

/-- The colimit (direct limit) of the first family of modules. -/
abbrev colim₁ : Type v := Module.DirectLimit M₁ D.t₁

/-- The colimit (direct limit) of the second family of modules. -/
abbrev colim₂ : Type v := Module.DirectLimit M₂ D.t₂

/-- The colimit (direct limit) of the third family of modules. -/
abbrev colim₃ : Type v := Module.DirectLimit M₃ D.t₃

/-- The induced map `colim f₁ : colim₁ → colim₂` on colimits. -/
noncomputable def colimF₁ : D.colim₁ →ₗ[R] D.colim₂ :=
  Module.DirectLimit.map (fun i => (D.seq i).f₁) D.tr₁

/-- The induced map `colim f₂ : colim₂ → colim₃` on colimits. -/
noncomputable def colimF₂ : D.colim₂ →ₗ[R] D.colim₃ :=
  Module.DirectLimit.map (fun i => (D.seq i).f₂) D.tr₂

end DirectedSES

/-- If `of (g i x) = 0` in the colimit, then `g j (f i j x) = 0` for some `j ≥ i`. -/
private theorem exists_map_eq_zero {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [DecidableEq ι] {G G' : ι → Type v} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j) (f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G' j)
    [DirectedSystem G' fun i j h => f' i j h] (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (i : ι) (x : G i) (hz : Module.DirectLimit.of R ι G' f' i (g i x) = 0) :
    ∃ j, ∃ hij : i ≤ j, g j (f i j hij x) = 0 := by
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz
  exact ⟨j, hij, by simpa [← hj] using LinearMap.congr_fun (hg i j hij) x⟩

namespace ColimHelper

open Module

variable {ι : Type v} [Preorder ι]
    {G G' : ι → Type v}
    [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
    [DecidableEq ι]

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]

/-- Naturality of `TensorProduct.directLimitLeft`: tensoring a colimit map equals the colimit
of the tensored maps, conjugated by `(directLimitLeft _ Q).symm`. -/
theorem rTensor_map_eq (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    (f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G' j)
    (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (Q : Type v) [AddCommGroup Q] [Module R Q]
    (hgQ : ∀ (i j : ι) (h : i ≤ j),
      (g j).rTensor Q ∘ₗ (f i j h).rTensor Q = (f' i j h).rTensor Q ∘ₗ (g i).rTensor Q)
    (z : Module.DirectLimit (fun i => TensorProduct R (G i) Q)
      (fun i j h => (f i j h).rTensor Q)) :
    (Module.DirectLimit.map g hg).rTensor Q ((TensorProduct.directLimitLeft f Q).symm z)
      = (TensorProduct.directLimitLeft f' Q).symm
          (Module.DirectLimit.map (fun i => (g i).rTensor Q) hgQ z) := by
  obtain ⟨i, w, rfl⟩ := DirectLimit.exists_of z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x q => simp [DirectLimit.map_apply_of]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- A directed limit of injective maps is injective. -/
theorem map_injective (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    (f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G' j)
    [DirectedSystem G' fun i j h => f' i j h]
    (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (hgi : ∀ i, Function.Injective (g i)) :
    Function.Injective (Module.DirectLimit.map g hg) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_of z
  rw [DirectLimit.map_apply_of] at hz
  obtain ⟨j, hij, hj⟩ := exists_map_eq_zero f f' g hg i x hz
  have hx0 : f i j hij x = 0 := hgi j (by simpa using hj)
  have : DirectLimit.of R ι G f i x = DirectLimit.of R ι G f j (f i j hij x) :=
    (DirectLimit.of_f).symm
  rw [this, hx0, map_zero]

/- Let `y : colim G'`. By `DirectLimit.exists_of` there is an index `i` and `y₀ : G' i` with
`y = of_{G'} i y₀`. Since `g i : G i → G' i` is surjective, pick `x : G i` with `g i x = y₀`.
Then `DirectLimit.map g hg (of_G i x) = of_{G'} i (g i x) = of_{G'} i y₀ = y`. -/
/-- A directed limit of surjective maps is surjective. -/
theorem map_surjective (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    (f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G' j)
    (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (hgs : ∀ i, Function.Surjective (g i)) :
    Function.Surjective (Module.DirectLimit.map g hg) := by
  intro y
  obtain ⟨i, y₀, rfl⟩ := DirectLimit.exists_of y
  obtain ⟨x, hx⟩ := hgs i y₀
  refine ⟨DirectLimit.of R ι G f i x, ?_⟩
  rw [DirectLimit.map_apply_of, hx]

/- We show `range (map g₁) = ker (map g₂)` where `g₁ i = (seq i).f₁`,
`g₂ i = (seq i).f₂` and each row is exact (`range (g₁ i) = ker (g₂ i)`).

(⊆) `map g₂ ∘ map g₁ = map (g₂ ∘ g₁)` and each `g₂ i ∘ g₁ i = 0` (from
`range (g₁ i) = ker (g₂ i)`), so the composite colimit map is `0`; hence
`range (map g₁) ≤ ker (map g₂)`.

(⊇) Let `z ∈ ker (map g₂)`. Write `z = of_G₂ i x` (`exists_of`). Then
`map g₂ z = of_{G₃} i (g₂ i x) = 0`, so by `DirectLimit.of.zero_exact` there is `j ≥ i`
with `t₃ i j (g₂ i x) = 0`, i.e. (by `tr₂` commutativity) `g₂ j (t₂ i j x) = 0`. Thus
`t₂ i j x ∈ ker (g₂ j) = range (g₁ j)`, so `t₂ i j x = g₁ j w` for some `w : G₁ j`. Then
`z = of_G₂ i x = of_G₂ j (t₂ i j x) = of_G₂ j (g₁ j w) = map g₁ (of_G₁ j w)`, exhibiting
`z ∈ range (map g₁)`. -/
/-- Middle exactness is preserved by directed colimits. -/
theorem map_exact
    {G'' : ι → Type v} [∀ i, AddCommGroup (G'' i)] [∀ i, Module R (G'' i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    (f' : (i j : ι) → i ≤ j → G' i →ₗ[R] G' j)
    (f'' : (i j : ι) → i ≤ j → G'' i →ₗ[R] G'' j)
    [DirectedSystem G'' fun i j h => f'' i j h]
    (g₁ : (i : ι) → G i →ₗ[R] G' i)
    (g₂ : (i : ι) → G' i →ₗ[R] G'' i)
    (hg₁ : ∀ (i j : ι) (h : i ≤ j), g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i)
    (hg₂ : ∀ (i j : ι) (h : i ≤ j), g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i)
    (hrow : ∀ i, LinearMap.range (g₁ i) = LinearMap.ker (g₂ i)) :
    LinearMap.range (Module.DirectLimit.map g₁ hg₁)
      = LinearMap.ker (Module.DirectLimit.map g₂ hg₂) := by
  apply le_antisymm
  · -- range (map g₁) ≤ ker (map g₂)
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_of z
    rw [DirectLimit.map_apply_of, DirectLimit.map_apply_of]
    have hmem : g₁ i x ∈ LinearMap.ker (g₂ i) := by
      rw [← hrow i]
      exact LinearMap.mem_range_self _ x
    rw [LinearMap.mem_ker] at hmem
    rw [hmem, map_zero]
  · -- ker (map g₂) ≤ range (map g₁)
    intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_of z
    rw [DirectLimit.map_apply_of] at hz
    obtain ⟨j, hij, hj⟩ := exists_map_eq_zero f' f'' g₂ hg₂ i x hz
    obtain ⟨w, hw⟩ : f' i j hij x ∈ LinearMap.range (g₁ j) := by
      rw [hrow j, LinearMap.mem_ker]
      exact hj
    rw [LinearMap.mem_range]
    refine ⟨DirectLimit.of R ι G f j w, ?_⟩
    rw [DirectLimit.map_apply_of, hw]
    exact DirectLimit.of_f

end ColimHelper

/--
A split short exact sequence is universally exact; equivalently its first map `f₁`
is universally injective. -/
@[stacks 058J "(1)"]
theorem split_universallyExact
    {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (S : ShortExact (R := R) M₁ M₂ M₃) (hS : S.IsSplit) :
    S.UniversallyExact := by
  obtain ⟨s, hs⟩ := hS
  have hf₂ : ∀ x, S.f₂ (S.f₁ x) = 0 := fun x =>
    LinearMap.mem_ker.mp (S.exact ▸ LinearMap.mem_range_self S.f₁ x)
  have hmem : ∀ m, (LinearMap.id - s ∘ₗ S.f₂ : M₂ →ₗ[R] M₂) m ∈ LinearMap.range S.f₁ :=
    fun m => by
      rw [S.exact, LinearMap.mem_ker]
      simpa using congr(S.f₂ m - $(LinearMap.congr_fun hs (S.f₂ m)))
  let e := LinearEquiv.ofInjective S.f₁ S.inj
  let r := e.symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hmem
  have hr : Function.LeftInverse r S.f₁ := fun x =>
    e.symm_apply_eq.mpr (Subtype.ext (by simp [e, hf₂]))
  intro Q _ _
  have hcomp : r.rTensor Q ∘ₗ S.f₁.rTensor Q = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, show r ∘ₗ S.f₁ = LinearMap.id from LinearMap.ext hr,
      LinearMap.rTensor_id]
  exact Function.LeftInverse.injective (g := r.rTensor Q) fun x => congr($hcomp x)

/-- Injectivity of the first map of the colimit sequence. -/
theorem colim_colimF₁_injective
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    {M₁ M₂ M₃ : ι → Type v}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)]
    (D : DirectedSES (R := R) ι M₁ M₂ M₃) :
    Function.Injective D.colimF₁ := by
  unfold DirectedSES.colimF₁
  have := D.ds₂
  exact ColimHelper.map_injective D.t₁ D.t₂ (fun i => (D.seq i).f₁) D.tr₁
    (fun i => (D.seq i).inj)

/-- Surjectivity of the second map of the colimit sequence. -/
theorem colim_colimF₂_surjective
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    {M₁ M₂ M₃ : ι → Type v}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)]
    (D : DirectedSES (R := R) ι M₁ M₂ M₃) :
    Function.Surjective D.colimF₂ := by
  unfold DirectedSES.colimF₂
  exact ColimHelper.map_surjective D.t₂ D.t₃ (fun i => (D.seq i).f₂) D.tr₂
    (fun i => (D.seq i).surj)

/-- Exactness in the middle of the colimit sequence. -/
theorem colim_middle_exact
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    {M₁ M₂ M₃ : ι → Type v}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)]
    (D : DirectedSES (R := R) ι M₁ M₂ M₃) :
    LinearMap.range D.colimF₁ = LinearMap.ker D.colimF₂ := by
  unfold DirectedSES.colimF₁ DirectedSES.colimF₂
  have := D.ds₃
  exact ColimHelper.map_exact D.t₁ D.t₂ D.t₃
    (fun i => (D.seq i).f₁) (fun i => (D.seq i).f₂) D.tr₁ D.tr₂ (fun i => (D.seq i).exact)

/-- Universal injectivity of the first map of the colimit sequence. -/
theorem colim_colimF₁_universallyInjective
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    {M₁ M₂ M₃ : ι → Type v}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)]
    (D : DirectedSES (R := R) ι M₁ M₂ M₃)
    (hD : ∀ i, (D.seq i).UniversallyExact) :
    UniversallyInjective D.colimF₁ := by
  intro Q _ _
  have hgQ : ∀ (i j : ι) (h : i ≤ j),
      ((D.seq j).f₁).rTensor Q ∘ₗ (D.t₁ i j h).rTensor Q
        = (D.t₂ i j h).rTensor Q ∘ₗ ((D.seq i).f₁).rTensor Q := by
    intro i j h
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, D.tr₁ i j h]
  set mtens := Module.DirectLimit.map (fun i => ((D.seq i).f₁).rTensor Q) hgQ
  have := D.ds₂
  have hmtens_inj : Function.Injective mtens :=
    ColimHelper.map_injective (R := R)
      (fun i j h => (D.t₁ i j h).rTensor Q) (fun i j h => (D.t₂ i j h).rTensor Q)
      (fun i => ((D.seq i).f₁).rTensor Q) hgQ (fun i => hD i Q)
  have hconj : ∀ z, D.colimF₁.rTensor Q ((TensorProduct.directLimitLeft D.t₁ Q).symm z)
      = (TensorProduct.directLimitLeft D.t₂ Q).symm (mtens z) :=
    ColimHelper.rTensor_map_eq D.t₁ D.t₂ (fun i => (D.seq i).f₁) D.tr₁ Q hgQ
  intro a b hab
  obtain ⟨a, rfl⟩ := (TensorProduct.directLimitLeft D.t₁ Q).symm.surjective a
  obtain ⟨b, rfl⟩ := (TensorProduct.directLimitLeft D.t₁ Q).symm.surjective b
  rw [hconj, hconj] at hab
  rw [hmtens_inj ((TensorProduct.directLimitLeft D.t₂ Q).symm.injective hab)]

/-- Filtered colimits preserve universally exact short exact sequences. -/
@[stacks 058J "(2)"]
theorem colim_universallyExact
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    {M₁ M₂ M₃ : ι → Type v}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)]
    (D : DirectedSES (R := R) ι M₁ M₂ M₃)
    (hD : ∀ i, (D.seq i).UniversallyExact) :
    Function.Injective D.colimF₁ ∧
      Function.Surjective D.colimF₂ ∧
      LinearMap.range D.colimF₁ = LinearMap.ker D.colimF₂ ∧
      UniversallyInjective D.colimF₁ :=
  ⟨colim_colimF₁_injective D, colim_colimF₂_surjective D,
    colim_middle_exact D, colim_colimF₁_universallyInjective D hD⟩

/-- Filtered colimits of split short exact sequences are universally exact. -/
theorem colim_universallyExact_of_isSplit
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DecidableEq ι]
    {M₁ M₂ M₃ : ι → Type v}
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)]
    [∀ i, AddCommGroup (M₃ i)] [∀ i, Module R (M₃ i)]
    (D : DirectedSES (R := R) ι M₁ M₂ M₃)
    (hD : ∀ i, (D.seq i).IsSplit) :
    Function.Injective D.colimF₁ ∧
      Function.Surjective D.colimF₂ ∧
      LinearMap.range D.colimF₁ = LinearMap.ker D.colimF₂ ∧
      UniversallyInjective D.colimF₁ :=
  colim_universallyExact D (fun i => split_universallyExact (D.seq i) (hD i))

-- ===== merged from StacksDraft.Ch10.Sec82.Tag058P =====

/-!
# Flatness in a universally exact sequence

Throughout, `R` is a commutative ring (with unit), and all modules are `R`-modules.
Tensor products are taken over `R`.

## Definitions

* Definition 1 (Flat module): An `R`-module `M` is flat if `- otimes_R M` is exact;
  equivalently, for every injective `R`-module homomorphism `g : N -> N'`, the induced
  map `id_M otimes g : M otimes_R N -> M otimes_R N'` is injective. We use Mathlib's
  `Module.Flat`.

* Definition 2 (Universally injective map): A homomorphism `f : M -> N` is universally
  injective if for every `R`-module `Q`, the map `f otimes id_Q : M otimes_R Q ->
  N otimes_R Q` is injective.

* Definition 3 (Universally exact sequence): A short exact sequence
  `0 -> M_1 ->[u] M_2 ->[v] M_3 -> 0` is universally exact if it is exact and the map
  `u : M_1 -> M_2` is universally injective. Equivalently, for every `Q` the tensored
  sequence `0 -> M_1 otimes Q -> M_2 otimes Q -> M_3 otimes Q -> 0` is short exact.

## Main results
Theorem (Stacks Tag 058P, Lemma 10.82.7): Let `R` be a commutative ring and let
`0 -> M_1 ->[u] M_2 ->[v] M_3 -> 0` be a universally exact sequence of `R`-modules.
Suppose that `M_2` is flat. Then `M_1` and `M_3` are flat.
-/

@[expose] public section
-- We work in a fixed universe `u`, over a fixed commutative ring `R : Type u`, with all
-- modules and the test module `Q` living in `Type u`. Flatness and universal injectivity
-- are robust under change of universe, so this is faithful to the (universe-agnostic)
-- mathematical statement.

variable {R : Type u} [CommRing R]

/--
The short exact sequence `0 -> M_1 ->[u] M_2 ->[v] M_3 -> 0` is *universally exact* if it
is a short exact sequence (`u` injective, `v` surjective, exact at `M_2`) and the map `u`
is universally injective. -/
structure UniversallyExact
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (u : M₁ →ₗ[R] M₂) (v : M₂ →ₗ[R] M₃) : Prop where
  /-- The map `u` is injective. -/
  injective_u : Function.Injective u
  /-- The map `v` is surjective. -/
  surjective_v : Function.Surjective v
  /-- The sequence is exact at `M_2`: `range u = ker v`. -/
  exact : Function.Exact u v
  /-- The map `u` is universally injective (Definition 2). -/
  universally_injective_u : UniversallyInjective u

/-- `rTensor` and `lTensor` commute (naturality of the tensor product in both variables). -/
private theorem rTensor_comp_lTensor_comm {M M' N N' : Type u} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [AddCommGroup N'] [Module R M] [Module R M'] [Module R N] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    f.rTensor N' ∘ₗ g.lTensor M = g.lTensor M' ∘ₗ f.rTensor N := by
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- **Theorem (Stacks Tag 058P, Lemma 10.82.7).**
Let `0 -> M_1 ->[u] M_2 ->[v] M_3 -> 0` be a universally exact sequence of `R`-modules
with `M_2` flat. Then `M_1` is flat and `M_3` is flat. -/
@[stacks 058P, ega "0 6.7.4" "partial"]
theorem UniversallyExact.flat_of_middle_flat
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (u : M₁ →ₗ[R] M₂) (v : M₂ →ₗ[R] M₃)
    (hue : UniversallyExact u v) (hM₂ : Module.Flat R M₂) :
    Module.Flat R M₁ ∧ Module.Flat R M₃ := by
  have hM₁ : Module.Flat R M₁ := by
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ g hg
    refine Function.Injective.of_comp (f := LinearMap.rTensor N' u) ?_
    rw [← LinearMap.coe_comp, rTensor_comp_lTensor_comm u g, LinearMap.coe_comp]
    exact (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp
      (hue.universally_injective_u N)
  refine ⟨hM₁, ?_⟩
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ g hg
  set Qm : Submodule R N' := LinearMap.range g
  set π : N' →ₗ[R] (N' ⧸ Qm) := Qm.mkQ
  have hgπ : Function.Exact g π := LinearMap.exact_map_mkQ_range g
  have hπg : π ∘ₗ g = 0 := by
    ext x
    simpa using (hgπ.apply_apply_eq_zero x)
  have hrowN' : Function.Exact (LinearMap.rTensor N' u) (LinearMap.rTensor N' v) :=
    rTensor_exact N' hue.exact hue.surjective_v
  have hcolM₁ : Function.Exact (LinearMap.lTensor M₁ g) (LinearMap.lTensor M₁ π) :=
    lTensor_exact M₁ hgπ Qm.mkQ_surjective
  rw [injective_iff_map_eq_zero (LinearMap.lTensor M₃ g)]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective N hue.surjective_v x
  have h1 : (LinearMap.rTensor N' v) ((LinearMap.lTensor M₂ g) y) = 0 :=
    (LinearMap.congr_fun (rTensor_comp_lTensor_comm v g) y).trans hx
  rw [hrowN'] at h1
  obtain ⟨z, hz⟩ := h1
  have h2 : (LinearMap.rTensor (N' ⧸ Qm) u) ((LinearMap.lTensor M₁ π) z) = 0 := by
    have e := LinearMap.congr_fun (rTensor_comp_lTensor_comm u π) z
    simp only [LinearMap.comp_apply] at e
    rw [e, hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπg]
    simp
  have h3 : (LinearMap.lTensor M₁ π) z = 0 := hue.universally_injective_u (N' ⧸ Qm) h2
  rw [hcolM₁] at h3
  obtain ⟨w, hw⟩ := h3
  have h4 : (LinearMap.lTensor M₂ g) y = (LinearMap.lTensor M₂ g) ((LinearMap.rTensor N u) w) := by
    rw [← hz, ← hw]
    exact LinearMap.congr_fun (rTensor_comp_lTensor_comm u g) w
  rw [Module.Flat.lTensor_preserves_injective_linearMap g hg h4]
  exact (rTensor_exact N hue.exact hue.surjective_v).apply_apply_eq_zero w
