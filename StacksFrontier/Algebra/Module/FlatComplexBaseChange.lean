module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.IsBaseChange
public import Mathlib.Algebra.FiveLemma

/-!
# Exact bounded complexes of flat modules are universally exact

Let `R` be a commutative ring and let `M⁰ → M¹ → M² → ⋯` be a complex of flat `R`-modules which
vanishes in large degrees. If the complex is exact in all degrees `≥ n + 1`, then it stays exact
in those degrees after tensoring with an arbitrary `R`-module `P`, the kernel `Zⁿ` of the
differential out of `Mⁿ` is flat, and its formation commutes with `P ⊗_R -`.

## Main definitions

* `StacksDraft.FlatComplex.UniversallyExactFrom`: the complex is universally exact from degree
  `n`.

## Main results

* `StacksDraft.FlatComplex.flat_of_exact`: in a short exact sequence `0 → K → M → Q → 0` with `M`
  and `Q` flat, `K` is flat.
* `StacksDraft.FlatComplex.universallyExact`: the statement above.
* `StacksDraft.FlatComplex.lTensor_injective_and_exact_of_range_eq_ker`: its degree-zero case,
  for any injective map onto the kernel of `d 0`.
* `StacksDraft.FlatComplex.isBaseChange_of_left_exact_of_baseChange`: kernels commute with a base
  change which keeps the source row left exact.

## Implementation notes

The complex is a family `M : ℕ → Type v` with differentials `d n : M n →ₗ[R] M (n + 1)`;
exactness at `m + 1` is `Function.Exact (d m) (d (m + 1))`. Tensoring is `LinearMap.lTensor`, so
the statement covers base change along any ring map `R → B`, a `B`-module being an `R`-module.
-/

@[expose] public section

open TensorProduct LinearMap

universe u v w

namespace StacksDraft.FlatComplex

variable {R : Type u} [CommRing R]

/-- **Two out of three for flatness.** In a short exact sequence `0 → K → M → Q → 0` with `M` and
`Q` flat, the kernel `K` is flat. -/
theorem flat_of_exact {K M Q : Type v} [AddCommGroup K] [AddCommGroup M] [AddCommGroup Q]
    [Module R K] [Module R M] [Module R Q] [Module.Flat R M] [Module.Flat R Q]
    (i : K →ₗ[R] M) (q : M →ₗ[R] Q) (hi : Function.Injective i) (hq : Function.Surjective q)
    (h : Function.Exact i q) : Module.Flat R K := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have hcomm : (i.lTensor N') ∘ₗ (f.rTensor K) = (f.rTensor M) ∘ₗ (i.lTensor N) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have : Function.Injective ((i.lTensor N') ∘ₗ (f.rTensor K)) := by
    rw [hcomm]
    exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
      (LinearMap.lTensor_injective_of_exact_of_flat q hq i hi h N)
  exact Function.Injective.of_comp this

/-- A tensor product with a subsingleton module is a subsingleton. -/
theorem subsingleton_tensor {P M : Type*} [AddCommGroup P] [AddCommGroup M] [Module R P]
    [Module R M] [Subsingleton M] : Subsingleton (P ⊗[R] M) :=
  inferInstance

/-- Tensoring a factorization `f = j ∘ e` through a surjection `e` preserves the range of `j`. -/
private theorem range_lTensor_eq_of_comp_surjective {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (P : Type*)
    [AddCommGroup P] [Module R P] {j : B →ₗ[R] C} {e : A →ₗ[R] B} {f : A →ₗ[R] C}
    (hf : j ∘ₗ e = f) (he : Function.Surjective e) :
    range (f.lTensor P) = range (j.lTensor P) := by
  subst hf
  rw [LinearMap.lTensor_comp, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective P he))]

variable {M : ℕ → Type v} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (d : ∀ n, M n →ₗ[R] M (n + 1))

/-- The complex `M` is universally exact from degree `n`: the kernel `Zⁿ` of `d n` is flat and,
for every `R`-module `P`, the complex `P ⊗ M` is exact in every degree `≥ n + 1`, the map
`P ⊗ Zⁿ → P ⊗ Mⁿ` is injective and its image is the kernel of `P ⊗ d n`. -/
def UniversallyExactFrom (n : ℕ) : Prop :=
  Module.Flat R (ker (d n)) ∧ ∀ (P : Type w) [AddCommGroup P] [Module R P],
    (∀ m, n ≤ m → Function.Exact ((d m).lTensor P) ((d (m + 1)).lTensor P)) ∧
      Function.Injective ((ker (d n)).subtype.lTensor P) ∧
      range ((ker (d n)).subtype.lTensor P) = ker ((d n).lTensor P)

/-- A complex whose terms in all degrees `≥ n` are subsingletons is universally exact from
degree `n`. -/
theorem universallyExactFrom_of_subsingleton (n : ℕ) (hM : ∀ m, n ≤ m → Subsingleton (M m)) :
    UniversallyExactFrom.{u, v, w} d n := by
  have hn := hM n le_rfl
  have : Subsingleton (ker (d n)) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  refine ⟨inferInstance, fun P _ _ =>
    ⟨fun m hm => ?_, Function.injective_of_subsingleton _, Subsingleton.elim _ _⟩⟩
  have := hM (m + 1) (by omega)
  intro y
  rw [Subsingleton.elim y 0]
  exact ⟨fun _ => ⟨0, map_zero _⟩, fun _ => map_zero _⟩

/-- If the complex is exact at `n + 1` and universally exact from degree `n + 1`, it is
universally exact from degree `n`. -/
theorem universallyExactFrom_step [∀ n, Module.Flat R (M n)] (n : ℕ)
    (hex : Function.Exact (d n) (d (n + 1))) (ih : UniversallyExactFrom.{u, v, w} d (n + 1)) :
    UniversallyExactFrom.{u, v, w} d n := by
  obtain ⟨hflat, ih⟩ := ih
  let Z := ker (d (n + 1))
  let dn : M n →ₗ[R] Z := (d n).codRestrict Z fun x => (hex (d n x)).2 ⟨x, rfl⟩
  have hdn : Z.subtype ∘ₗ dn = d n := LinearMap.subtype_comp_codRestrict _ _ _
  have hsurj : Function.Surjective dn := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := (hex z).1 hz
    exact ⟨x, Subtype.ext hx⟩
  have hexact : Function.Exact (ker (d n)).subtype dn := by
    intro y
    constructor
    · intro h
      exact ⟨⟨y, LinearMap.mem_ker.2 (congrArg Subtype.val h)⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Subtype.ext (LinearMap.mem_ker.1 z.2)
  refine ⟨flat_of_exact (ker (d n)).subtype dn (ker (d n)).injective_subtype hsurj hexact,
    fun P _ _ => ?_⟩
  obtain ⟨hP, hinj, hrange⟩ := ih P
  have hcomp : (d n).lTensor P = (Z.subtype.lTensor P) ∘ₗ (dn.lTensor P) := by
    rw [← LinearMap.lTensor_comp, hdn]
  refine ⟨fun m hm => ?_, LinearMap.lTensor_injective_of_exact_of_flat dn hsurj _
    (ker (d n)).injective_subtype hexact P, ?_⟩
  · rcases Nat.eq_or_lt_of_le hm with rfl | hm
    · rw [LinearMap.exact_iff, ← hrange, range_lTensor_eq_of_comp_surjective P hdn hsurj]
    · exact hP m hm
  · rw [hcomp, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 hinj),
      ← LinearMap.exact_iff.1 (_root_.lTensor_exact P hexact hsurj)]

/-- **Exact bounded complexes of flat modules are universally exact.** Let `M⁰ → M¹ → ⋯` be a
complex of flat `R`-modules vanishing above degree `N`, exact in every degree `≥ n + 1`. Then the
kernel `Zⁿ` of `d n` is flat, and for every `R`-module `P` the complex `P ⊗ M` is exact in every
degree `≥ n + 1`, the map `P ⊗ Zⁿ → P ⊗ Mⁿ` is injective and its image is the kernel of
`P ⊗ d n`. -/
theorem universallyExact [∀ n, Module.Flat R (M n)] (N : ℕ)
    (hN : ∀ m, N < m → Subsingleton (M m)) (n : ℕ)
    (hex : ∀ m, n ≤ m → Function.Exact (d m) (d (m + 1))) :
    UniversallyExactFrom.{u, v, w} d n := by
  suffices h : ∀ k n, N < n + k → (∀ m, n ≤ m → Function.Exact (d m) (d (m + 1))) →
      UniversallyExactFrom.{u, v, w} d n by
    exact h (N + 1) n (by omega) hex
  intro k
  induction k with
  | zero =>
    intro n hn _
    exact universallyExactFrom_of_subsingleton d n fun m hm => hN m (by omega)
  | succ k ih =>
    intro n hn hex
    by_cases h : N < n
    · exact universallyExactFrom_of_subsingleton d n fun m hm => hN m (by omega)
    · exact universallyExactFrom_step d n (hex n le_rfl)
        (ih (n + 1) (by omega) fun m hm => hex m (by omega))

/-- **Degree zero of `universallyExact`, for any presentation of the kernel.** If the complex is
exact in every positive degree and `ι : T → M⁰` is injective with image the kernel of `d 0`, then
for every `R`-module `P` the map `P ⊗ ι` is injective with image the kernel of `P ⊗ d 0`. -/
theorem lTensor_injective_and_exact_of_range_eq_ker [∀ n, Module.Flat R (M n)] (N : ℕ)
    (hN : ∀ m, N < m → Subsingleton (M m)) (hex : ∀ m, Function.Exact (d m) (d (m + 1)))
    {T : Type*} [AddCommGroup T] [Module R T] (ι : T →ₗ[R] M 0) (hι : Function.Injective ι)
    (hrange : range ι = ker (d 0)) (P : Type w) [AddCommGroup P] [Module R P] :
    Function.Injective (ι.lTensor P) ∧ Function.Exact (ι.lTensor P) ((d 0).lTensor P) := by
  obtain ⟨-, H⟩ := universallyExact.{u, v, w} d N hN 0 fun m _ => hex m
  obtain ⟨-, hinj, hrng⟩ := H P
  let e : T ≃ₗ[R] ker (d 0) :=
    (LinearEquiv.ofInjective ι hι).trans (LinearEquiv.ofEq _ _ hrange)
  have hιe : (ker (d 0)).subtype ∘ₗ e.toLinearMap = ι := LinearMap.ext fun _ => rfl
  refine ⟨?_, ?_⟩
  · rw [← hιe, LinearMap.lTensor_comp]
    exact hinj.comp (e.lTensor P).injective
  · rw [LinearMap.exact_iff, range_lTensor_eq_of_comp_surjective P hιe e.surjective, hrng]

section IsBaseChange

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module S N₁] [Module S N₂] [Module S N₃]
  [IsScalarTower R S N₁] [IsScalarTower R S N₂] [IsScalarTower R S N₃]
  (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃)
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[S] N₂} {g' : N₂ →ₗ[S] N₃}

/-- **Kernels commute with a base change which keeps the source row left exact.** Given a
commutative diagram from the row `M₁ → M₂ → M₃` of `R`-modules to the exact row `N₁ → N₂ → N₃` of
`S`-modules with injective first map, in which `h₂` and `h₃` are base changes, if the base change
of `M₁ → M₂ → M₃` along `R → S` is exact with injective first map, then `h₁` is a base change. -/
theorem isBaseChange_of_left_exact_of_baseChange
    (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂)
    (isb₂ : IsBaseChange S h₂) (isb₃ : IsBaseChange S h₃)
    (exact₁ : Function.Exact (f.baseChange S) (g.baseChange S))
    (inj₁ : Function.Injective (f.baseChange S))
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange S h₁ := by
  simp only [IsBaseChange, IsTensorProduct] at isb₂ isb₃ ⊢
  refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ exact₁ exact₂ isb₂ isb₃.1 inj₁ inj₂
  · ext s m
    simpa using congr(s • ($comm₁ m)).symm
  · ext s m
    simpa using congr(s • ($comm₂ m)).symm

end IsBaseChange

end StacksDraft.FlatComplex
