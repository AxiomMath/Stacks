module

public import StacksFrontier.Algebra.Module.Injective.ZModPrimePower
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Algebra.Homology.PseudoCoherentNoetherianModels
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Tensor

/-!
# Perfectness over `ℤ/pᵐℤ` from the reduction modulo `p`

Let `p` be a prime and `R = ℤ/pᵐℤ`.  Let `J` be a bounded below complex of flat `R`-modules
(for instance the global sections of an injective resolution of a flat sheaf).  If the complex
`J[p]` of `p`-torsion, that is the complex `Hom_R(ℤ/pℤ, J)` of `ℤ/pℤ`-modules, has finite
cohomology vanishing in large degrees, then `J` is a perfect object of `D(R)`.

The hypothesis is on the complex `J[p]` itself, not on the derived reduction of `J`: a bounded
below complex of flat modules need not be K-flat, and `J = (R --p--> R --p--> ⋯)` over `ℤ/p²ℤ`
is acyclic while `J[p]` is not.  For a flat `R`-module `M` the multiplication by `p^(m-1)`
identifies `M / pM` with `M[p]`, so `J[p] ≅ J / pJ`; this is the form in which the cohomology of
the reduction `F ⊗ ℤ/ℓ` of a flat sheaf of `ℤ/ℓᵐℤ`-modules enters the proof of [Tag 03V2].

The argument: the short exact sequences `0 → J[p^c] → J[p^{c+1}] --p^c--> J[p] → 0` of complexes
give, by induction on `c`, finiteness and vanishing in degrees `> b` of the cohomology of every
`J[p^c]`, and `J[p^m] = J`.  The cycles `Z^b(J)` are then flat, so `J` is quasi-isomorphic to
its canonical truncation `τ_{≤ b} J`, a bounded complex of flat modules; it has finite
cohomology over the Noetherian ring `R`, hence is perfect by [Tag 066E] and [Tag 0658].

## Main results

* `Stacks.ZModPrimePower.flat_of_isPowExact`: a `ℤ/pᵐℤ`-module on which `p^(m - a)` and `p^a`
  form exact sequences is flat.
* `Stacks.ZModPrimePower.torsionComplex`: the complex `J[p^c]` of `p^c`-torsion elements.
* `Stacks.ZModPrimePower.isPerfect_of_bounded_reduction`: the perfectness criterion.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Stacks.ZModPrimePower

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-! ### Flatness -/

/-- **A `ℤ/pᵐℤ`-module with the exactness property is flat.**  Every ideal is `(g)` with
`g = p^a u`, and every element of `(g) ⊗ M` is `g ⊗ x`; it maps to `g x`, and `g x = 0` gives
`x = p^(m - a) y`, so `g ⊗ x = p^(m - a) g ⊗ y = 0`. -/
theorem flat_of_isPowExact {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ m)) M]
    (hM : IsPowExact p m M) : Module.Flat (ZMod (p ^ m)) M := by
  have : IsPrincipalIdealRing (ZMod (p ^ m)) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod (p ^ m))) ZMod.intCast_surjective
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  obtain ⟨g, rfl⟩ : ∃ g, I = Ideal.span {g} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  obtain ⟨a, ha, u, hgu⟩ := exists_eq_pow_mul_unit g
  have hg : g ∈ Ideal.span {g} := Ideal.subset_span rfl
  have hgen : ∀ t : TensorProduct (ZMod (p ^ m)) (Ideal.span {g}) M,
      ∃ x : M, t = (⟨g, hg⟩ : Ideal.span {g}) ⊗ₜ x := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul i x =>
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 i.2
      refine ⟨r • x, ?_⟩
      have : i = r • (⟨g, hg⟩ : Ideal.span {g}) := Subtype.ext (by simp [← hr])
      rw [this, TensorProduct.smul_tmul]
    | add s t hs ht =>
      obtain ⟨x, rfl⟩ := hs
      obtain ⟨y, rfl⟩ := ht
      exact ⟨x + y, by rw [TensorProduct.tmul_add]⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨x, rfl⟩ := hgen t
  rw [LinearMap.rTensor_tmul, Submodule.subtype_apply] at ht
  have hgx : g • x = 0 := by
    simpa using congrArg (TensorProduct.lid (ZMod (p ^ m)) M) ht
  have hux : p ^ a • ((u : ZMod (p ^ m)) • x) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ m)), smul_smul, Nat.cast_pow, ← hgu, hgx]
  obtain ⟨y, hy⟩ := hM a ha _ hux
  have hx : x = (p ^ (m - a) : ZMod (p ^ m)) •
      (((u⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) • y) := by
    calc x = ((u⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) • ((u : ZMod (p ^ m)) • x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = ((u⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) • (p ^ (m - a) • y) := by rw [hy]
      _ = _ := by rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ m)), smul_comm, Nat.cast_pow]
  have hzero : (p ^ (m - a) : ZMod (p ^ m)) • (⟨g, hg⟩ : Ideal.span {g}) = 0 := by
    ext
    change (p : ZMod (p ^ m)) ^ (m - a) * g = 0
    rw [hgu, ← mul_assoc, ← pow_add, Nat.sub_add_cancel ha]
    have : ((p : ZMod (p ^ m)) ^ m) = 0 := by exact_mod_cast ZMod.natCast_self (p ^ m)
    rw [this, zero_mul]
  rw [hx, ← TensorProduct.smul_tmul, hzero, TensorProduct.zero_tmul]

end Stacks.ZModPrimePower

/-! ### The torsion subcomplexes -/

namespace Stacks.ZModPrimePower

section Torsion

variable (p : ℕ) {R : Type*} [Ring R] (J : CochainComplex (ModuleCat.{v} R) ℤ)

/-- The `p^c`-torsion submodule of a term of a complex. -/
abbrev torsionSubmodule (c : ℕ) (i : ℤ) : Submodule R (J.X i) :=
  LinearMap.ker ((p ^ c) • LinearMap.id : J.X i →ₗ[R] J.X i)

variable {p J} in
/-- An element lies in the `p^c`-torsion submodule if and only if `p^c • x = 0`. -/
lemma mem_torsionSubmodule {c : ℕ} {i : ℤ} (x : J.X i) :
    x ∈ torsionSubmodule p J c i ↔ p ^ c • x = 0 := Iff.rfl

variable {p J} in
/-- The differential of `J` maps `p^c`-torsion elements to `p^c`-torsion elements. -/
lemma d_mem_torsionSubmodule {c : ℕ} {i : ℤ} (j : ℤ) {x : J.X i}
    (hx : x ∈ torsionSubmodule p J c i) :
    J.d i j x ∈ torsionSubmodule p J c j := by
  rw [mem_torsionSubmodule] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

/-- **The complex `J[p^c]`** of `p^c`-torsion elements of `J`. -/
def torsionComplex (c : ℕ) : CochainComplex (ModuleCat.{v} R) ℤ where
  X i := ModuleCat.of R (torsionSubmodule p J c i)
  d i j := ModuleCat.ofHom ((J.d i j).hom.restrict (fun _ hx => d_mem_torsionSubmodule j hx))
  shape i j h := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    change J.d i j x.1 = 0
    rw [J.shape i j h]
    rfl))
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    change J.d j k (J.d i j x.1) = 0
    rw [← ModuleCat.comp_apply, J.d_comp_d]
    rfl))

/-- The differential of `torsionComplex p J c` is the restriction of the differential of `J`. -/
lemma torsionComplex_d_apply (c : ℕ) (i j : ℤ) (x : torsionSubmodule p J c i) :
    (((torsionComplex p J c).d i j).hom x).1 = J.d i j x.1 := rfl

variable {p J} in
/-- The `p^c`-torsion submodule is contained in the `p^{c+1}`-torsion submodule. -/
lemma torsionSubmodule_le_succ (c : ℕ) (i : ℤ) :
    torsionSubmodule p J c i ≤ torsionSubmodule p J (c + 1) i := fun x hx => by
  rw [mem_torsionSubmodule] at hx ⊢
  rw [pow_succ, mul_nsmul, hx, nsmul_zero]

variable {p J} in
/-- Multiplication by `p^c` maps `p^{c+1}`-torsion elements to `p`-torsion elements. -/
lemma pow_smul_mem_torsionSubmodule_one (c : ℕ) {i : ℤ} {x : J.X i}
    (hx : x ∈ torsionSubmodule p J (c + 1) i) : p ^ c • x ∈ torsionSubmodule p J 1 i := by
  rw [mem_torsionSubmodule] at hx ⊢
  rw [smul_smul, ← pow_add, add_comm]
  exact hx

/-- The inclusion `J[p^c] ⟶ J[p^{c+1}]`. -/
def torsionComplexInclusion (c : ℕ) :
    torsionComplex p J c ⟶ torsionComplex p J (c + 1) where
  f i := ModuleCat.ofHom (Submodule.inclusion (torsionSubmodule_le_succ c i))
  comm' _i _j _ := ModuleCat.hom_ext (LinearMap.ext fun _x => Subtype.ext rfl)

/-- Multiplication by `p^c`, `J[p^{c+1}] ⟶ J[p]`. -/
def torsionComplexPow (c : ℕ) :
    torsionComplex p J (c + 1) ⟶ torsionComplex p J 1 where
  f i := ModuleCat.ofHom (((p ^ c) • LinearMap.id : J.X i →ₗ[R] J.X i).restrict
    (fun _ hx => pow_smul_mem_torsionSubmodule_one c hx))
  comm' i j _ := ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
    change J.d i j (p ^ c • x.1) = p ^ c • J.d i j x.1
    exact map_nsmul (J.d i j).hom (p ^ c) x.1))

/-- The components of `torsionComplexPow p J c` are multiplication by `p^c`. -/
lemma torsionComplexPow_f_apply (c : ℕ) (i : ℤ) (x : torsionSubmodule p J (c + 1) i) :
    (((torsionComplexPow p J c).f i).hom x).1 = p ^ c • x.1 := rfl

/-- The components of `torsionComplexInclusion p J c` are the submodule inclusions. -/
lemma torsionComplexInclusion_f_apply (c : ℕ) (i : ℤ) (x : torsionSubmodule p J c i) :
    (((torsionComplexInclusion p J c).f i).hom x).1 = x.1 := rfl

/-- The short complex `0 → J[p^c] → J[p^{c+1}] --p^c--> J[p] → 0`. -/
def torsionShortComplex (c : ℕ) : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) :=
  ShortComplex.mk (torsionComplexInclusion p J c) (torsionComplexPow p J c) (by
    ext i x
    exact Subtype.ext x.2)

/-- **A complex mapping injectively onto the `p^c`-torsion of `J` is `J[p^c]`.** -/
noncomputable def torsionComplexIsoOfRange {c : ℕ} {A : CochainComplex (ModuleCat.{v} R) ℤ}
    (e : A ⟶ J) (he : ∀ n, Function.Injective (e.f n).hom)
    (hr : ∀ n, LinearMap.range (e.f n).hom = torsionSubmodule p J c n) :
    A ≅ torsionComplex p J c :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((LinearEquiv.ofInjective (e.f n).hom (he n)).trans
      (LinearEquiv.ofEq _ _ (hr n))).toModuleIso)
    (fun i j _ => ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (by
      change J.d i j (e.f i x) = e.f j (A.d i j x)
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e.comm])))

end Torsion

/-! ### Exactness of the torsion sequences -/

section Exactness

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
  (J : CochainComplex (ModuleCat.{v} (ZMod (p ^ m))) ℤ)

omit hp in
/-- Every element of a `ℤ/pᵐℤ`-module is killed by `p^m`. -/
lemma pow_nsmul_eq_zero {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ m)) M] (x : M) :
    p ^ m • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ m)), ZMod.natCast_self, zero_smul]

omit hp in
/-- **`0 → J[p^c] → J[p^{c+1}] --p^c--> J[p] → 0` is exact** when the terms of `J` are flat
and `c < m`. -/
theorem torsionShortComplex_shortExact (hJ : ∀ i, IsPowExact p m (J.X i)) {c : ℕ}
    (hc : c + 1 ≤ m) : (torsionShortComplex p J c).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun i => ?_)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨⟨x.1, ?_⟩, rfl⟩
    have := congrArg Subtype.val hx
    exact this
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext this
  · rw [ModuleCat.epi_iff_surjective]
    intro x
    obtain ⟨y, hy⟩ := hJ i 1 (by omega) x.1 x.2
    refine ⟨⟨p ^ (m - 1 - c) • y, ?_⟩, Subtype.ext ?_⟩
    · change p ^ (c + 1) • p ^ (m - 1 - c) • y = 0
      rw [smul_smul, ← pow_add, show c + 1 + (m - 1 - c) = m by omega, pow_nsmul_eq_zero]
    · change p ^ c • p ^ (m - 1 - c) • y = x.1
      rw [smul_smul, ← pow_add, show c + (m - 1 - c) = m - 1 by omega, hy]

/-- `J[p^m] = J`. -/
def torsionComplexTopIso : torsionComplex p J m ≅ J :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (LinearEquiv.ofTop _ (by
      ext x
      simp only [Submodule.mem_top, iff_true]
      exact pow_nsmul_eq_zero x)).toModuleIso) (fun i j _ => rfl)

/-- Exactness of a complex of modules in degree `j`, elementwise. -/
lemma exactAt_iff_mem' {R : Type*} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    K.ExactAt j ↔ ∀ x : K.X j, K.d j k x = 0 → ∃ y : K.X i, K.d i j y = x := by
  rw [HomologicalComplex.exactAt_iff' K i j k (by simp; omega) (by simp; omega),
    ShortComplex.moduleCat_exact_iff]
  rfl

/-- Exactness of a complex of modules in degree `i`, elementwise. -/
lemma exactAt_iff_mem {R : Type*} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    K.ExactAt i ↔ ∀ x : K.X i, K.d i (i + 1) x = 0 → ∃ y : K.X (i - 1), K.d (i - 1) i y = x :=
  exactAt_iff_mem' K (i - 1) i (i + 1) (by omega) rfl

end Exactness

/-! ### Cohomology of the torsion complexes -/

section Cohomology

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
  (J : CochainComplex (ModuleCat.{v} (ZMod (p ^ m))) ℤ)

omit hp in
/-- `J[p^0]` is the zero complex. -/
lemma exactAt_torsionComplex_zero (i : ℤ) : (torsionComplex p J 0).ExactAt i := by
  rw [exactAt_iff_mem]
  intro x _
  refine ⟨0, Subtype.ext ?_⟩
  have hx : x.1 = 0 := by simpa using x.2
  rw [map_zero, hx]
  rfl

omit hp in
/-- **Vanishing propagates from `J[p]` to every `J[p^c]`.** -/
theorem exactAt_torsionComplex (hJ : ∀ i, IsPowExact p m (J.X i)) (i : ℤ)
    (h₁ : (torsionComplex p J 1).ExactAt i) {c : ℕ} (hc : c ≤ m) :
    (torsionComplex p J c).ExactAt i := by
  induction c with
  | zero => exact exactAt_torsionComplex_zero J i
  | succ c ih =>
    have hS := torsionShortComplex_shortExact J hJ hc
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hS.homology_exact₂ i).isZero_X₂ ((ih (by omega)).isZero_homology.eq_of_src _ _)
      (h₁.isZero_homology.eq_of_tgt _ _)

/-- In an exact sequence `A → B → C` of modules over a Noetherian ring, `B` is finite if `A`
and `C` are. -/
lemma finite_X₂_of_exact {R : Type*} [CommRing R] [IsNoetherianRing R]
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.Exact) (h₁ : Module.Finite R S.X₁)
    (h₃ : Module.Finite R S.X₃) : Module.Finite R S.X₂ := by
  have hex : Function.Exact S.f.hom S.g.hom.rangeRestrict := by
    intro y
    have h := hS.moduleCat_range_eq_ker
    change S.g.hom.rangeRestrict y = 0 ↔ y ∈ Set.range S.f.hom
    rw [← LinearMap.coe_range, h]
    exact ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩
  have := h₁
  have := h₃
  exact Module.Finite.of_exact hex (LinearMap.surjective_rangeRestrict _)

/-- **Finiteness propagates from `J[p]` to every `J[p^c]`.** -/
theorem finite_homology_torsionComplex (hJ : ∀ i, IsPowExact p m (J.X i)) (i : ℤ)
    (h₁ : Module.Finite (ZMod (p ^ m)) ((torsionComplex p J 1).homology i)) {c : ℕ}
    (hc : c ≤ m) : Module.Finite (ZMod (p ^ m)) ((torsionComplex p J c).homology i) := by
  induction c with
  | zero =>
    have : Subsingleton ((torsionComplex p J 0).homology i) :=
      ModuleCat.subsingleton_of_isZero (exactAt_torsionComplex_zero J i).isZero_homology
    infer_instance
  | succ c ih =>
    exact finite_X₂_of_exact ((torsionShortComplex_shortExact J hJ hc).homology_exact₂ i)
      (ih (by omega)) h₁

end Cohomology

/-! ### The perfectness criterion -/

section Perfect

attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
  (J : CochainComplex (ModuleCat.{v} (ZMod (p ^ m))) ℤ)

omit hp in
/-- A subsingleton is pow-exact. -/
lemma isPowExact_of_subsingleton {M : Type*} [AddCommGroup M] [Subsingleton M] :
    IsPowExact p m M := fun _ _ _x _ => ⟨0, Subsingleton.elim _ _⟩

omit hp in
/-- **The cycles are flat** in a degree `b` above which every `J[p^c]` is exact. -/
theorem isPowExact_ker_d (hJ : ∀ i, IsPowExact p m (J.X i)) (b k : ℤ) (hk : b + 1 = k)
    (hb : ∀ c ≤ m, (torsionComplex p J c).ExactAt k) :
    IsPowExact p m (LinearMap.ker (J.d b k).hom) := by
  intro a ha x hx
  have hx' : p ^ a • x.1 = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := hJ b a ha x.1 hx'
  have hdy : J.d b k y ∈ torsionSubmodule p J (m - a) k := by
    rw [mem_torsionSubmodule, ← map_nsmul, hy]
    exact x.2
  obtain ⟨z, hz⟩ := (exactAt_iff_mem' _ b k (k + 1) hk rfl).1 (hb (m - a) (Nat.sub_le m a))
    ⟨_, hdy⟩ (Subtype.ext (by
      change J.d k (k + 1) (J.d b k y) = 0
      rw [← ModuleCat.comp_apply, J.d_comp_d]
      rfl))
  have hz' : J.d b k z.1 = J.d b k y := congrArg Subtype.val hz
  refine ⟨⟨y - z.1, ?_⟩, Subtype.ext ?_⟩
  · change J.d b k (y - z.1) = 0
    rw [map_sub, hz', sub_self]
  · change p ^ (m - a) • (y - z.1) = x.1
    have hz0 : p ^ (m - a) • z.1 = 0 := z.2
    rw [smul_sub, hz0, sub_zero, hy]

/-- **Perfectness from the reduction modulo `p`.**  Let `J` be a bounded below complex of flat
`ℤ/pᵐℤ`-modules whose `p`-torsion complex `J[p] ≅ J / pJ` has finite cohomology, vanishing in
degrees above `b`.  Then `J` is a perfect object of `D(ℤ/pᵐℤ)`. -/
theorem isPerfect_of_bounded_reduction (hJ : ∀ i, IsPowExact p m (J.X i)) (a b : ℤ)
    [J.IsStrictlyGE a] (hb : ∀ i, b < i → (torsionComplex p J 1).ExactAt i)
    (hf : ∀ i, Module.Finite (ZMod (p ^ m)) ((torsionComplex p J 1).homology i)) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj J) := by
  have hc : ∀ i, b < i → ∀ c ≤ m, (torsionComplex p J c).ExactAt i :=
    fun i hi c hc => exactAt_torsionComplex J hJ i (hb i hi) hc
  have hJb : ∀ i, b < i → J.ExactAt i := fun i hi =>
    (hc i hi m le_rfl).of_iso (torsionComplexTopIso J)
  have hJf : ∀ i, Module.Finite (ZMod (p ^ m)) (J.homology i) := fun i => by
    have := finite_homology_torsionComplex J hJ i (hf i) (le_refl m)
    exact Module.Finite.equiv
      (HomologicalComplex.homologyMapIso (torsionComplexTopIso J) i).toLinearEquiv
  have : J.IsLE b := (CochainComplex.isLE_iff J b).2 hJb
  let eH : ∀ i, (DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj J) ≅
      J.homology i := fun i => (DerivedCategory.homologyFunctorFactors _ i).app J
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj J) :=
    StacksDraft.PseudoCoherence.isPseudoCoherentIn_of_boundedAbove_finite_homology _
      ⟨b, fun i hi => (hJb i hi).isZero_homology.of_iso (eH i)⟩
      (fun i => Module.Finite.equiv (eH i).toLinearEquiv.symm)
  have hflat : ∀ i, Module.Flat (ZMod (p ^ m)) ((J.truncLE b).X i) := fun i => by
    rcases lt_trichotomy i b with hi | rfl | hi
    · have := flat_of_isPowExact (hJ i)
      exact Module.Flat.of_linearEquiv (J.truncLEXIso b i hi).toLinearEquiv
    · have hn : (ComplexShape.up ℤ).next i = i + 1 := CochainComplex.next ℤ i
      have hK : Module.Flat (ZMod (p ^ m)) (J.sc i).moduleCatLeftHomologyData.K :=
        flat_of_isPowExact (isPowExact_ker_d J hJ i ((ComplexShape.up ℤ).next i)
          hn.symm (hc _ (by omega)))
      exact Module.Flat.of_linearEquiv ((J.truncLEXIsoCycles i) ≪≫
        (J.sc i).moduleCatCyclesIso).toLinearEquiv
    · have : Subsingleton ((J.truncLE b).X i) :=
        ModuleCat.subsingleton_of_isZero ((J.truncLE b).isZero_of_isStrictlyLE b i hi)
      exact flat_of_isPowExact (p := p) isPowExact_of_subsingleton
  have : (J.truncLE b).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rcases lt_trichotomy i b with hib | rfl | hib
    · exact (J.isZero_of_isStrictlyGE a i hi).of_iso (J.truncLEXIso b i hib)
    · refine IsZero.of_iso ?_ (J.truncLEXIsoCycles i)
      exact IsZero.of_mono (J.iCycles i) (J.isZero_of_isStrictlyGE a i hi)
    · exact (J.truncLE b).isZero_of_isStrictlyLE b i hib
  have hfr : StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj J) a b :=
    ⟨J.truncLE b, hflat, inferInstance, inferInstance,
      ⟨(asIso (DerivedCategory.Q.map (J.ιTruncLE b))).symm⟩⟩
  exact (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension _).1.2
    ⟨hpc, a, b, hfr⟩

end Perfect



end Stacks.ZModPrimePower
