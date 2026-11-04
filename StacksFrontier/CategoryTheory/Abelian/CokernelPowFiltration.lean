module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.LinearAlgebra.NilpotentSingleBlock
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ConnectingSurjective
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# The cokernels of the powers of an endomorphism, checked on jointly faithful exact fibres

Let `C` be an abelian category with a family of exact functors `Φ_i : C ⥤ ModuleCat K` which is
jointly faithful — for instance the fibre functors at a conservative family of points of a site.
Let `s : M ⟶ M` be an endomorphism such that on every fibre `ker (Φ_i s)^j ⊆ im (Φ_i s)`. Then the
cokernels `Q_m = coker sᵐ` fit into short exact sequences

`0 → coker s --s^j--> coker s^{j+1} → coker s^j → 0`.

When `Φ_i s` is nilpotent of order `n = dim Φ_i M` with one-dimensional kernel, the fibre condition
holds for every `j < n` (`Module.End.range_pow_eq_ker_pow_of_finrank_ker_eq_one`); this is the
filtration of the free module on a torsor under `ℤ/ℓ` by the powers of `τ - 1`.

## Main results

* `Stacks.Abelian.isZero_of_isZero_obj`, `Stacks.Abelian.exact_of_exact_map`,
  `Stacks.Abelian.mono_of_injective_map`: a jointly faithful family of exact functors to modules
  reflects zero objects, exactness and monomorphisms.
* `Stacks.Abelian.cokernelPowShortComplex_shortExact`: the short exact sequence above.
* `Stacks.Abelian.exists_map_eq_of_finrank`: the fibre condition from the dimensions of the
  fibres and of the kernels of `s` on them.
* `Stacks.Abelian.natCard_ext_two_cokernel_pow_le`: along that tower, `Ext²(O, coker sʲ)` is a
  quotient of `Ext²(O, M)` as soon as `Ext³(O, coker s) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace Stacks.Abelian

section Defs

variable {C : Type*} [Category C] [Abelian C] {M : C} (s : End M)

/-- The map `coker s → coker s^{j+1}` induced by `s^j`. -/
def cokernelPowι (j : ℕ) : cokernel s ⟶ cokernel (s ^ (j + 1)) :=
  cokernel.desc s ((s ^ j) ≫ cokernel.π (s ^ (j + 1))) (by
    rw [← Category.assoc, ← End.mul_def, ← pow_succ, cokernel.condition])

/-- The projection `coker s^{j+1} → coker s^j`. -/
def cokernelPowq (j : ℕ) :
    cokernel (s ^ (j + 1)) ⟶ cokernel (s ^ j) :=
  cokernel.desc _ (cokernel.π (s ^ j)) (by
    rw [pow_succ, End.mul_def, Category.assoc, cokernel.condition, comp_zero])

/-- The composite `M → coker s → coker s^{j+1}` of the projection with `cokernelPowι s j` is `s^j`
followed by the projection onto `coker s^{j+1}`. -/
@[reassoc (attr := simp)]
theorem π_cokernelPowι (j : ℕ) :
    cokernel.π s ≫ cokernelPowι s j = (s ^ j) ≫ cokernel.π (s ^ (j + 1)) :=
  cokernel.π_desc _ _ _

/-- The composite `M → coker s^{j+1} → coker s^j` is the projection onto `coker s^j`. -/
@[reassoc (attr := simp)]
theorem π_cokernelPowq (j : ℕ) :
    cokernel.π (s ^ (j + 1)) ≫ cokernelPowq s j = cokernel.π (s ^ j) :=
  cokernel.π_desc _ _ _

/-- The composite `coker s → coker s^{j+1} → coker s^j` is zero. -/
theorem cokernelPowι_comp_cokernelPowq (j : ℕ) :
    cokernelPowι s j ≫ cokernelPowq s j = 0 := by
  rw [← cancel_epi (cokernel.π s), π_cokernelPowι_assoc, π_cokernelPowq, comp_zero,
    cokernel.condition]

/-- The short complex `coker s → coker s^{j+1} → coker s^j`. -/
def cokernelPowShortComplex (j : ℕ) : ShortComplex C :=
  ShortComplex.mk (cokernelPowι s j) (cokernelPowq s j) (cokernelPowι_comp_cokernelPowq s j)

end Defs

/-- A functor to modules carries `s ^ j` to the `j`-th power of the linear map of `s`. -/
private theorem hom_map_pow {C : Type*} [Category C] {K : Type*} [Ring K]
    (F : C ⥤ ModuleCat.{w} K) {M : C} (s : End M) (j : ℕ) :
    (F.map (s ^ j)).hom = (F.map s).hom ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, End.one_def, F.map_id]; rfl
  | succ j ih =>
    rw [pow_succ, End.mul_def, F.map_comp, ModuleCat.hom_comp, ih, pow_succ]
    rfl

/-- If `s ^ n = 0` and the fibre has dimension `n`, the linear map of `s` on it is nilpotent of
order its dimension. -/
private theorem hom_map_pow_finrank_eq_zero {C : Type*} [Category C] [Preadditive C]
    {K : Type*} [Ring K] (F : C ⥤ ModuleCat.{w} K) [F.Additive] {M : C} (s : End M) {n : ℕ}
    (hdim : Module.finrank K (F.obj M) = n) (hs : s ^ n = 0) :
    (F.map s).hom ^ Module.finrank K (F.obj M) = 0 := by
  rw [hdim, ← hom_map_pow, hs, Functor.map_zero]
  rfl

variable {C : Type*} [Category C] [Abelian C] {K : Type*} [Ring K] {ι : Type*}
  (Φ : ι → C ⥤ ModuleCat.{w} K) [∀ i, (Φ i).Additive]
  [∀ i, PreservesFiniteLimits (Φ i)] [∀ i, PreservesFiniteColimits (Φ i)]
  (hΦ : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i, (Φ i).map f = (Φ i).map g) → f = g)

include hΦ

omit [∀ i, (Φ i).Additive] [∀ i, PreservesFiniteLimits (Φ i)]
  [∀ i, PreservesFiniteColimits (Φ i)] in
/-- A jointly faithful family of additive functors reflects zero objects. -/
theorem isZero_of_isZero_obj {X : C} (h : ∀ i, IsZero ((Φ i).obj X)) : IsZero X :=
  (IsZero.iff_id_eq_zero X).2 (hΦ _ _ fun i => (h i).eq_of_src _ _)

/-- A jointly faithful family of exact functors reflects exactness of short complexes. -/
theorem exact_of_exact_map {S : ShortComplex C} (h : ∀ i, (S.map (Φ i)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  refine isZero_of_isZero_obj Φ hΦ fun i => ?_
  exact ((S.map (Φ i)).exact_iff_isZero_homology.1 (h i)).of_iso (S.mapHomologyIso (Φ i)).symm

omit [∀ i, PreservesFiniteLimits (Φ i)] [∀ i, PreservesFiniteColimits (Φ i)] in
/-- A jointly faithful family of additive functors to modules reflects monomorphisms. -/
theorem mono_of_injective_map {X Y : C} (f : X ⟶ Y)
    (h : ∀ i, Function.Injective ((Φ i).map f)) : Mono f := by
  refine Preadditive.mono_of_cancel_zero f fun {P} g hg => hΦ _ _ fun i => ?_
  rw [Functor.map_zero]
  ext x
  apply h i
  have := congrArg (fun φ => (Φ i).map φ) hg
  simp only [Functor.map_comp, Functor.map_zero] at this
  simpa using ConcreteCategory.congr_hom this x

omit hΦ [∀ i, (Φ i).Additive] [∀ i, PreservesFiniteLimits (Φ i)] in
/-- An exact functor to modules carries a cokernel map to a surjection. -/
theorem surjective_map_cokernel_π (i : ι) {X Y : C} (f : X ⟶ Y) :
    Function.Surjective ((Φ i).map (cokernel.π f)) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

omit hΦ in
/-- An exact functor to modules carries `X --f--> Y → coker f` to an exact sequence. -/
theorem exists_eq_of_map_cokernel_π_eq_zero (i : ι) {X Y : C} (f : X ⟶ Y)
    (y : (Φ i).obj Y) (hy : (Φ i).map (cokernel.π f) y = 0) : ∃ x, (Φ i).map f x = y :=
  (ShortComplex.moduleCat_exact_iff _).1 ((ShortComplex.exact_cokernel f).map (Φ i)) y hy

variable {M : C} (s : End M)

omit hΦ [Abelian C] [∀ i, (Φ i).Additive] [∀ i, PreservesFiniteLimits (Φ i)]
  [∀ i, PreservesFiniteColimits (Φ i)] in
/-- On the fibre `Φ_i M`, the map induced by `s^j` is the `j`-th iterate of the map induced by
`s`. -/
theorem map_pow_apply (i : ι) (j : ℕ) (x : (Φ i).obj M) :
    (Φ i).map (s ^ j) x = ((Φ i).map s).hom^[j] x := by
  rw [← Module.End.pow_apply, ← hom_map_pow]

/-- **The cokernels of the powers of `s` form a filtration with steps `coker s`**: if on every
fibre the kernel of the `j`-th power of `s` lies in the image of `s`, then
`0 → coker s --s^j--> coker s^{j+1} → coker s^j → 0` is short exact. -/
theorem cokernelPowShortComplex_shortExact (j : ℕ)
    (hker : ∀ i (x : (Φ i).obj M), ((Φ i).map s).hom^[j] x = 0 → ∃ y, (Φ i).map s y = x) :
    (cokernelPowShortComplex s j).ShortExact where
  exact := by
    refine exact_of_exact_map Φ hΦ fun i => (ShortComplex.moduleCat_exact_iff _).2 ?_
    intro y hy
    obtain ⟨x, rfl⟩ := surjective_map_cokernel_π Φ i _ y
    have hx : (Φ i).map (cokernel.π (s ^ j)) x = 0 := by
      change ((Φ i).map (cokernel.π (s ^ (j + 1))) ≫ (Φ i).map (cokernelPowq s j)) x = 0 at hy
      rwa [← Functor.map_comp, π_cokernelPowq] at hy
    obtain ⟨z, rfl⟩ := exists_eq_of_map_cokernel_π_eq_zero Φ i _ x hx
    refine ⟨(Φ i).map (cokernel.π s) z, ?_⟩
    show ((Φ i).map (cokernel.π s) ≫ (Φ i).map (cokernelPowι s j)) z = _
    rw [← Functor.map_comp, π_cokernelPowι, Functor.map_comp]
    rfl
  mono_f := by
    refine mono_of_injective_map Φ hΦ _ fun i => ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨x, rfl⟩ := surjective_map_cokernel_π Φ i _ y
    have h1 : (Φ i).map (cokernel.π (s ^ (j + 1))) ((Φ i).map (s ^ j) x) = 0 := by
      change ((Φ i).map (cokernel.π s) ≫ (Φ i).map (cokernelPowι s j)) x = 0 at hy
      rwa [← Functor.map_comp, π_cokernelPowι, Functor.map_comp] at hy
    obtain ⟨z, hz⟩ := exists_eq_of_map_cokernel_π_eq_zero Φ i _ _ h1
    have h2 : ((Φ i).map s).hom^[j] (x - (Φ i).map s z) = 0 := by
      have e1 := map_pow_apply Φ s i j x
      have e2 := map_pow_apply Φ s i (j + 1) z
      rw [Function.iterate_succ_apply] at e2
      rw [← map_pow_apply Φ s i j, map_sub, map_pow_apply Φ s i j, map_pow_apply Φ s i j,
        ← e1, ← hz, e2, sub_self]
    obtain ⟨w, hw⟩ := hker i _ h2
    have hx : x = (Φ i).map s (w + z) := by
      rw [map_add, hw, sub_add_cancel]
    rw [hx]
    show ((Φ i).map s ≫ (Φ i).map (cokernel.π s)) (w + z) = 0
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
    rfl
  epi_g := by
    have : Epi (cokernel.π (s ^ (j + 1)) ≫ cokernelPowq s j) := by
      rw [π_cokernelPowq]
      infer_instance
    exact epi_of_epi (cokernel.π _) (cokernelPowq s j)

omit hΦ in
/-- **The fibre condition from dimensions**: if on every fibre `Φ_i s` is nilpotent of order
`n = dim Φ_i M` with one-dimensional kernel, then for `j < n` the kernel of `(Φ_i s)^j` lies in the
image of `Φ_i s`. -/
theorem exists_map_eq_of_finrank {K : Type*} [Field K] {ι : Type*} {C : Type*} [Category C]
    [Abelian C] (Φ : ι → C ⥤ ModuleCat.{w} K) [∀ i, (Φ i).Additive]
    [∀ i, PreservesFiniteLimits (Φ i)] [∀ i, PreservesFiniteColimits (Φ i)] {M : C} (s : End M)
    {n : ℕ} [∀ i, FiniteDimensional K ((Φ i).obj M)]
    (hdim : ∀ i, Module.finrank K ((Φ i).obj M) = n) (hs : s ^ n = 0)
    (hker : ∀ i, Module.finrank K (LinearMap.ker ((Φ i).map s).hom) = 1) {j : ℕ} (hj : j < n)
    (i : ι) (x : (Φ i).obj M) (hx : ((Φ i).map s).hom^[j] x = 0) :
    ∃ y, (Φ i).map s y = x := by
  exact Module.End.exists_apply_eq_of_pow_apply_eq_zero_of_finrank_ker_eq_one
    (hom_map_pow_finrank_eq_zero (Φ i) s (hdim i) hs) (hker i)
    (by rwa [hdim i]) (by rwa [Module.End.pow_apply])

section Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {M : C} (s : End M)

omit hΦ in
/-- **`H²` along the tower of cokernels of the powers of `s`**: if the sequences
`0 → coker s → coker s^{j+1} → coker s^j → 0` are short exact for `1 ≤ j < n`, `sⁿ = 0` and
`Ext³(O, coker s) = 0`, then `Ext²(O, coker s^j)` is a quotient of `Ext²(O, M)` for every
`1 ≤ j ≤ n`. -/
theorem natCard_ext_two_cokernel_pow_le (O : C) {n : ℕ} (hs : s ^ n = 0)
    (hSES : ∀ j, 1 ≤ j → j < n → (cokernelPowShortComplex s j).ShortExact)
    (h3 : Subsingleton (CategoryTheory.Abelian.Ext O (cokernel s) 3))
    [Finite (CategoryTheory.Abelian.Ext O M 2)] :
    ∀ j, 1 ≤ j → j ≤ n → Finite (CategoryTheory.Abelian.Ext O (cokernel (s ^ j)) 2) ∧
      Nat.card (CategoryTheory.Abelian.Ext O (cokernel (s ^ j)) 2) ≤
        Nat.card (CategoryTheory.Abelian.Ext O M 2) := by
  have hn : ∀ m, m ≤ n - 1 →
      Finite (CategoryTheory.Abelian.Ext O (cokernel (s ^ (n - m))) 2) ∧
      Nat.card (CategoryTheory.Abelian.Ext O (cokernel (s ^ (n - m))) 2) ≤
        Nat.card (CategoryTheory.Abelian.Ext O M 2) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, hs]
      let e : CategoryTheory.Abelian.Ext O M 2 ≃
          CategoryTheory.Abelian.Ext O (cokernel (0 : M ⟶ M)) 2 :=
        Equiv.ofBijective _ (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
          (cokernel.π (0 : M ⟶ M)) (X := O) 2)
      exact ⟨Finite.of_equiv _ e, (Nat.card_congr e).symm.le⟩
    | succ m ih =>
      intro hm
      obtain ⟨hfin, hle⟩ := ih (by omega)
      have hj : n - (m + 1) + 1 = n - m := by omega
      have hS := hSES (n - (m + 1)) (by omega) (by omega)
      rw [cokernelPowShortComplex] at hS
      have hsurj := CategoryTheory.Abelian.Ext.surjective_comp_mk₀_g_of_subsingleton hS O 2 h3
      rw [← hj] at hfin hle
      exact ⟨Finite.of_surjective _ hsurj, (Nat.card_le_card_of_surjective _ hsurj).trans hle⟩
  intro j hj1 hjn
  have := hn (n - j) (by omega)
  rwa [Nat.sub_sub_self hjn] at this

end Ext

end Stacks.Abelian

namespace Stacks.Abelian

section Lift

variable {C : Type*} [Category C] [Abelian C] {M : C} (s : End M)

/-- For `j ≤ n` and `sⁿ = 0`, the map `coker s^j → M` induced by `s^{n-j}`. -/
def cokernelPowLift {n : ℕ} (hs : s ^ n = 0) {j : ℕ} (hj : j ≤ n) : cokernel (s ^ j) ⟶ M :=
  cokernel.desc _ (s ^ (n - j)) (by rw [← End.mul_def, ← pow_add, Nat.sub_add_cancel hj, hs])

/-- The composite `M → coker s^j → M` of the projection with `cokernelPowLift s hs hj` is
`s^{n-j}`. -/
@[reassoc (attr := simp)]
theorem π_cokernelPowLift {n : ℕ} (hs : s ^ n = 0) {j : ℕ} (hj : j ≤ n) :
    cokernel.π (s ^ j) ≫ cokernelPowLift s hs hj = s ^ (n - j) :=
  cokernel.π_desc _ _ _

/-- The composite `coker s^j → M → M` of `cokernelPowLift s hs hj` with `s^j` is zero. -/
theorem cokernelPowLift_comp_pow {n : ℕ} (hs : s ^ n = 0) {j : ℕ} (hj : j ≤ n) :
    cokernelPowLift s hs hj ≫ s ^ j = 0 := by
  rw [← cancel_epi (cokernel.π (s ^ j)), π_cokernelPowLift_assoc, ← End.mul_def, ← pow_add,
    Nat.add_sub_cancel' hj, hs, comp_zero]

/-- The short complex `coker s^j --s^{n-j}--> M --s^j--> M`. -/
def cokernelPowLiftShortComplex {n : ℕ} (hs : s ^ n = 0) {j : ℕ} (hj : j ≤ n) : ShortComplex C :=
  ShortComplex.mk (cokernelPowLift s hs hj) (s ^ j) (cokernelPowLift_comp_pow s hs hj)

end Lift

/-- `(Φ s^j)` is the `j`-th power of `Φ s` as a linear map. -/
theorem map_pow_hom {C : Type*} [Category C] [Preadditive C] {K : Type*} [Ring K]
    (F : C ⥤ ModuleCat.{w} K) {M : C} (s : End M) (j : ℕ) :
    (F.map (s ^ j)).hom = (F.map s).hom ^ j := by
  exact hom_map_pow F s j

/-- **`s^{n-j}` identifies `coker s^j` with the kernel of `s^j`**: if on every fibre `Φ_i s` is
nilpotent of order `n = dim Φ_i M` with one-dimensional kernel, then for `j ≤ n` the sequence
`0 → coker s^j --s^{n-j}--> M --s^j--> M` is exact. -/
theorem cokernelPowLiftShortComplex_exact_and_mono {K : Type*} [Field K] {ι : Type*} {C : Type*}
    [Category C] [Abelian C] (Φ : ι → C ⥤ ModuleCat.{w} K) [∀ i, (Φ i).Additive]
    [∀ i, PreservesFiniteLimits (Φ i)] [∀ i, PreservesFiniteColimits (Φ i)]
    (hΦ : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i, (Φ i).map f = (Φ i).map g) → f = g)
    {M : C} (s : End M) {n : ℕ} [∀ i, FiniteDimensional K ((Φ i).obj M)]
    (hdim : ∀ i, Module.finrank K ((Φ i).obj M) = n) (hs : s ^ n = 0)
    (hker : ∀ i, Module.finrank K (LinearMap.ker ((Φ i).map s).hom) = 1) {j : ℕ} (hj : j ≤ n) :
    (cokernelPowLiftShortComplex s hs hj).Exact ∧ Mono (cokernelPowLift s hs hj) := by
  have hpow := fun i => hom_map_pow_finrank_eq_zero (Φ i) s (hdim i) hs
  have hrange : ∀ i m, m ≤ n → LinearMap.range (((Φ i).map s).hom ^ (n - m)) =
      LinearMap.ker (((Φ i).map s).hom ^ m) := fun i m hm => by
    have := Module.End.range_pow_eq_ker_pow_of_finrank_ker_eq_one (hpow i) (hker i)
      (m := m) (by rwa [hdim i])
    rwa [hdim i] at this
  have hfac : ∀ i (x : (Φ i).obj M), (Φ i).map (cokernelPowLift s hs hj)
      ((Φ i).map (cokernel.π (s ^ j)) x) = (((Φ i).map s).hom ^ (n - j)) x := fun i x => by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, π_cokernelPowLift, ← map_pow_hom]
  refine ⟨exact_of_exact_map Φ hΦ fun i => (ShortComplex.moduleCat_exact_iff _).2 ?_,
    mono_of_injective_map Φ hΦ _ fun i => ?_⟩
  · intro (x : (Φ i).obj M) hx
    have hx' : x ∈ LinearMap.ker (((Φ i).map s).hom ^ j) := by
      rwa [LinearMap.mem_ker, ← map_pow_hom]
    rw [← hrange i j hj] at hx'
    obtain ⟨z, rfl⟩ := hx'
    exact ⟨(Φ i).map (cokernel.π (s ^ j)) z, hfac i z⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := surjective_map_cokernel_π Φ i _ y
    rw [hfac] at hy
    have hx : x ∈ LinearMap.ker (((Φ i).map s).hom ^ (n - j)) := hy
    rw [← hrange i (n - j) (Nat.sub_le n j), Nat.sub_sub_self hj] at hx
    obtain ⟨z, rfl⟩ := hx
    rw [← map_pow_hom, ← ModuleCat.comp_apply, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero]
    rfl

/-- `cokernelPowLiftShortComplex_exact_and_mono` read as a universal property: a map killed by
`s^j` factors uniquely through `coker s^j --s^{n-j}--> M`. -/
theorem exists_comp_cokernelPowLift_and_cancel {C : Type*} [Category C] [Abelian C] {M : C}
    (s : End M) {n : ℕ} (hs : s ^ n = 0) {j : ℕ} (hj : j ≤ n)
    (h : (cokernelPowLiftShortComplex s hs hj).Exact ∧ Mono (cokernelPowLift s hs hj)) :
    (∀ {A : C} (k : A ⟶ M), k ≫ s ^ j = 0 → ∃ k', k' ≫ cokernelPowLift s hs hj = k) ∧
      ∀ {A : C} (a b : A ⟶ cokernel (s ^ j)),
        a ≫ cokernelPowLift s hs hj = b ≫ cokernelPowLift s hs hj → a = b := by
  obtain ⟨hex, hmono⟩ := h
  have : Mono (cokernelPowLiftShortComplex s hs hj).f := hmono
  exact ⟨fun k hk => ⟨hex.lift k hk, hex.lift_f k hk⟩, fun a b hab => (cancel_mono _).1 hab⟩

end Stacks.Abelian

end
