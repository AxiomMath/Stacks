module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R]

/-- Gluing data for modules over a ring `R` along elements `f : ι → R`:
for each `i`, a module `M i` that is also an `R_{f i}`-module compatibly,
together with `R`-linear isomorphisms
`ψ i j : (M i)_{f j} ≃ₗ (M j)_{f i}`
satisfying the cocycle condition on triple localizations.

The modules `M i` live in a universe independent of the one of `R`, so that gluing data can be
formed out of modules that are not of the ring's own size. -/
structure ModuleGluingData (ι : Type v) (f : ι → R) where
  /-- The module over `R_{f i}` attached to the index `i`. -/
  M : ι → Type w
  [addCommGroup : ∀ i, AddCommGroup (M i)]
  [moduleR : ∀ i, Module R (M i)]
  [moduleAway : ∀ i, Module (Localization.Away (f i)) (M i)]
  [scalarTower : ∀ i, IsScalarTower R (Localization.Away (f i)) (M i)]
  /-- The transition isomorphisms `(M i)_{f j} ≃ (M j)_{f i}`. -/
  ψ : ∀ i j, LocalizedModule (Submonoid.powers (f j)) (M i) ≃ₗ[R]
              LocalizedModule (Submonoid.powers (f i)) (M j)
  cocycle :
    ∀ i j k : ι,
      ((LocalizedModule.map (Submonoid.powers (f i))
              (LocalizedModule.mkLinearMap (Submonoid.powers (f j))
                (M k))).restrictScalars R).comp
          ((ψ i k).toLinearMap.comp
            (LocalizedModule.mkLinearMap (Submonoid.powers (f k)) (M i)))
        =
      ((LocalizedModule.map (Submonoid.powers (f i))
              (ψ j k).toLinearMap).restrictScalars R).comp
        (((LocalizedModule.map (Submonoid.powers (f i))
                (LocalizedModule.mkLinearMap (Submonoid.powers (f k))
                  (M j))).restrictScalars R).comp
          ((ψ i j).toLinearMap.comp
            (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (M i))))

attribute [instance] ModuleGluingData.addCommGroup ModuleGluingData.moduleR
  ModuleGluingData.moduleAway ModuleGluingData.scalarTower

variable {ι : Type v} [Fintype ι] [DecidableEq ι] {f : ι → R}

namespace ModuleGluingData

/-- The direct sum of the modules `M i`. -/
abbrev DirectSumM (D : ModuleGluingData ι f) :=
  DirectSum ι D.M

/-- The direct sum, over pairs `(i, j)`, of the localizations `(M i)_{f j}`. -/
abbrev DirectSumLoc (D : ModuleGluingData ι f) :=
  DirectSum (ι × ι) (fun p : ι × ι =>
    LocalizedModule (Submonoid.powers (f p.snd)) (D.M p.fst))

/-- The component of `glueMap` from `M k`: sends `m ↦ Σ_j (k,j)-component (m/1)
- Σ_i (i,k)-component (ψ k i (m/1))`. -/
noncomputable def gluingComponent
    (D : ModuleGluingData ι f) (k : ι) :
    D.M k →ₗ[R] D.DirectSumLoc :=
  (∑ j : ι, (DirectSum.lof R (ι × ι)
      (fun p : ι × ι => LocalizedModule (Submonoid.powers (f p.snd)) (D.M p.fst))
      (k, j)).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (D.M k))) -
  (∑ i : ι, (DirectSum.lof R (ι × ι)
      (fun p : ι × ι => LocalizedModule (Submonoid.powers (f p.snd)) (D.M p.fst))
      (i, k)).comp
        ((D.ψ k i).toLinearMap.comp
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M k))))

/-- The `R`-linear map `⨁ M i → ⨁_{i,j} (M i)_{f j}` whose kernel is the glued
module. On the `k`-th summand it equals `gluingComponent D k`. -/
noncomputable def glueMap
    (D : ModuleGluingData ι f) :
    D.DirectSumM →ₗ[R] D.DirectSumLoc :=
  DirectSum.toModule R ι _ D.gluingComponent

/-- The glued module `M = Ker(⨁ M i → ⨁_{i,j} (M i)_{f j})`. -/
noncomputable def gluedModule
    (D : ModuleGluingData ι f) :
    Submodule R D.DirectSumM :=
  LinearMap.ker D.glueMap

/-- Membership in the glued module is the vanishing of the gluing-defect map. -/
@[simp]
lemma mem_gluedModule (D : ModuleGluingData ι f) {m : D.DirectSumM} :
    m ∈ D.gluedModule ↔ D.glueMap m = 0 := by
  rw [gluedModule, LinearMap.mem_ker]

/-- Projection of an element of the glued module to its `i`-th component in `M i`. -/
noncomputable def proj
    (D : ModuleGluingData ι f) (i : ι) :
    D.gluedModule →ₗ[R] D.M i :=
  (DirectSum.component R ι _ i).comp D.gluedModule.subtype

/-- Projection of a glued element evaluates its underlying direct sum. -/
@[simp]
lemma proj_apply (D : ModuleGluingData ι f) (i : ι) (m : D.gluedModule) :
    D.proj i m = (m : D.DirectSumM) i :=
  rfl

/-- General lemma: if `M` is an `R`-module via a scalar tower from a
semiring `S`, and `algebraMap R S s` is a unit in `S`, then the corresponding
endomorphism of `M` (given by `R`-action `m ↦ s • m`) is a unit in
`Module.End R M`. -/
lemma isUnit_algebraMap_end_of_isUnit_algebraMap {R : Type*} [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M]
    (S : Type*) [Semiring S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (s : R) (hs : IsUnit (algebraMap R S s)) :
    IsUnit (algebraMap R (Module.End R M) s) := by
  rw [← (Algebra.lsmul R (A := S) R M).commutes]
  exact hs.map _

omit [Fintype ι] [DecidableEq ι] in
/-- Every `s ∈ Submonoid.powers (f i)` acts as a unit on `M i` via the
`R`-action induced by the scalar tower `R → R_{f i} → M i`. -/
lemma isUnit_algebraMap_end
    (D : ModuleGluingData ι f) (i : ι) (s : Submonoid.powers (f i)) :
    IsUnit (algebraMap R (Module.End R (D.M i)) s) :=
  isUnit_algebraMap_end_of_isUnit_algebraMap (D.M i) (Localization.Away (f i)) _
    (IsLocalization.map_units (Localization.Away (f i)) s)

/-- If `LocalizedModule.mkLinearMap (Submonoid.powers r) M x = 0`, then there
exists `n : ℕ` with `r^n • x = 0`. -/
lemma exists_pow_smul_eq_zero_of_mk_eq_zero
    {M : Type w} [AddCommGroup M] [Module R M]
    (r : R) (x : M)
    (h : LocalizedModule.mkLinearMap (Submonoid.powers r) M x = 0) :
    ∃ n : ℕ, r^n • x = 0 := by
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers r) _).mp h
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
  exact ⟨n, hsx⟩

/-- If `r ^ n • x = 0`, then `r ^ N • x = 0` for every `N ≥ n`. -/
private lemma pow_smul_eq_zero_of_le {R M : Type*} [Monoid R] [AddMonoid M]
    [DistribMulAction R M] {r : R} {x : M} {n N : ℕ} (hn : r ^ n • x = 0) (h : n ≤ N) :
    r ^ N • x = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hn, smul_zero]

/-- Given a finite type `ι`, an element `r : R`, and elements `m i : M i` each
annihilated by some power of `r`, there is a uniform exponent `N` with
`r^N • m i = 0` for every `i`. -/
lemma exists_uniform_pow_annihilator
    {ι R : Type*} {M : ι → Type*} [Finite ι] [Monoid R]
    [∀ i, AddMonoid (M i)] [∀ i, DistribMulAction R (M i)]
    (r : R) (m : ∀ i, M i) (h : ∀ i, ∃ n : ℕ, r ^ n • m i = 0) :
    ∃ N : ℕ, ∀ i, r ^ N • m i = 0 := by
  have H : ∀ i, ∀ᶠ N in Filter.atTop, r ^ N • m i = 0 := fun i => by
    obtain ⟨n, hn⟩ := h i
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    exact pow_smul_eq_zero_of_le hn hN
  exact (Filter.eventually_all.2 H).exists

/-- The component formula for `gluingComponent` evaluated at a single summand.
At position `(a,b)` the only nonzero contributions are from the diagonal
`(k,k)` summand giving `m_k/1` in `(M_a)_{f_b}` (if `k=a`, `j=b`) and
`ψ_{k a}(m_k/1)` in `(M_a)_{f_b}` (if `k=b`, `i=a`). -/
private lemma component_gluingComponent
    (D : ModuleGluingData ι f) (k : ι) (mk : D.M k) (a b : ι) :
    DirectSum.component R (ι × ι)
        (fun p : ι × ι => LocalizedModule (Submonoid.powers (f p.2)) (D.M p.1))
        (a, b) (D.gluingComponent k mk) =
      (if hka : k = a then
        LocalizedModule.mkLinearMap (Submonoid.powers (f b)) (D.M a) (hka ▸ mk)
       else 0) -
      (if hkb : k = b then
        (D.ψ b a) (LocalizedModule.mkLinearMap (Submonoid.powers (f a)) (D.M b) (hkb ▸ mk))
       else 0) := by
  classical
  simp only [gluingComponent, LinearMap.sub_apply, map_sub, map_sum,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply]
  congr 1
  · -- First sum: Σ_j component (a,b) (lof (k,j) (m_k/1)) = component for j=b, k=a only
    rw [Finset.sum_eq_single b]
    · -- j = b case
      by_cases hka : k = a
      · subst hka
        simp [DirectSum.component.lof_self]
      · simp only [hka, dite_false]
        rw [DirectSum.component.of]
        simp [hka, Prod.mk.injEq]
    · intro j _ hjb
      rw [DirectSum.component.of, dite_eq_right]
      exact fun h => hjb ((Prod.mk.injEq _ _ _ _).mp h).right
    · exact fun h => absurd (Finset.mem_univ b) h
  · -- Second sum: Σ_i component (a,b) (lof (i,k) (ψ_{k i}(m_k/1))) = component for i=a, k=b only
    rw [Finset.sum_eq_single a]
    · -- i = a case
      by_cases hkb : k = b
      · subst hkb
        simp [DirectSum.component.lof_self]
      · simp only [hkb, dite_false]
        rw [DirectSum.component.of, dite_eq_right]
        exact fun h => hkb ((Prod.mk.injEq _ _ _ _).mp h).right
    · intro i _ hia
      rw [DirectSum.component.of, dite_eq_right]
      exact fun h => hia ((Prod.mk.injEq _ _ _ _).mp h).left
    · exact fun h => absurd (Finset.mem_univ a) h

/-- Componentwise formula for `glueMap`: the `(a, b)` component of
`glueMap m` equals `(m_a)/1 - ψ_{b a}(m_b/1)` in `(M_a)_{f_b}`. -/
lemma component_glueMap
    (D : ModuleGluingData ι f) (m : D.DirectSumM) (a b : ι) :
    DirectSum.component R (ι × ι)
        (fun p : ι × ι => LocalizedModule (Submonoid.powers (f p.2)) (D.M p.1))
        (a, b) (D.glueMap m) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f b)) (D.M a) (m a) -
        (D.ψ b a) (LocalizedModule.mkLinearMap (Submonoid.powers (f a)) (D.M b) (m b)) := by
  classical
  induction m using DirectSum.induction_on with
  | zero => simp [glueMap]
  | of k mk =>
      rw [← DirectSum.lof_eq_of R, glueMap, DirectSum.toModule_lof,
        D.component_gluingComponent k mk a b]
      -- Reduce ((lof k mk) a) and ((lof k mk) b) using `component.of`.
      have ha : (DirectSum.lof R ι D.M k mk) a =
          if h : k = a then h ▸ mk else 0 := by
        rw [DirectSum.apply_eq_component R, DirectSum.component.of]
      have hb : (DirectSum.lof R ι D.M k mk) b =
          if h : k = b then h ▸ mk else 0 := by
        rw [DirectSum.apply_eq_component R, DirectSum.component.of]
      rw [ha, hb]
      split_ifs with hka hkb hkb
      · subst hka hkb
        rfl
      · subst hka; simp
      · subst hkb; simp
      · simp
  | add x y hx hy =>
      simp only [map_add, DirectSum.add_apply, hx, hy]
      abel

/-- For `m ∈ gluedModule`, the gluing relation holds: `ψ i j (m_i/1) = m_j/1`. -/
@[stacks 00EQ "moreover clause: `ψ i j (m/1) = m/1` for `m` in the glued module"]
lemma psi_apply_of_mem_gluedModule
    (D : ModuleGluingData ι f) (m : D.gluedModule) (i j : ι) :
    D.ψ i j (LocalizedModule.mkLinearMap (Submonoid.powers (f j))
              (D.M i) ((m : D.DirectSumM) i)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M j) ((m : D.DirectSumM) j) := by
  have hcomp := D.component_glueMap (m : D.DirectSumM) j i
  rw [D.mem_gluedModule.mp m.property, map_zero] at hcomp
  -- hcomp : 0 = mkLinearMap (m j) - ψ i j (mkLinearMap (m i))
  -- So ψ i j (mkLinearMap (m i)) = mkLinearMap (m j)
  exact (sub_eq_zero.mp hcomp.symm).symm

/-- **Injectivity up to torsion** for `proj i`: if `m ∈ gluedModule` has
`(m : ⨁ M k) i = 0`, then some power of `f i` annihilates `m`. -/
lemma exists_smul_eq_zero_of_proj_eq_zero
    (D : ModuleGluingData ι f) (i : ι) (m : D.gluedModule)
    (hm : D.proj i m = 0) :
    ∃ (s : Submonoid.powers (f i)), (s : R) • m = 0 := by
  -- From `m ∈ gluedModule` we get `ψ i j (m_i / 1) = m_j / 1`, hence `m_j / 1 = 0`.
  have hi_zero : (m : D.DirectSumM) i = 0 := by
    rwa [proj_apply] at hm
  have hzero : ∀ j, LocalizedModule.mkLinearMap (Submonoid.powers (f i))
      (D.M j) ((m : D.DirectSumM) j) = 0 := by
    intro j
    have hpsi := D.psi_apply_of_mem_gluedModule m i j
    rw [hi_zero, map_zero, map_zero] at hpsi
    exact hpsi.symm
  -- Each component is killed by some power of f i; choose a uniform exponent.
  obtain ⟨N, hN⟩ := exists_uniform_pow_annihilator (f i) _ fun j =>
    exists_pow_smul_eq_zero_of_mk_eq_zero (f i) _ (hzero j)
  refine ⟨⟨(f i) ^ N, pow_mem (Submonoid.mem_powers _) N⟩, ?_⟩
  -- (f i)^N • m = 0 in gluedModule iff (f i)^N • (m : DirectSumM) = 0
  ext k
  rw [Submodule.coe_smul, Submodule.coe_zero, DirectSum.smul_apply, DirectSum.zero_apply]
  exact hN k

/-- Localizing a linear map commutes with the canonical map `x ↦ x/1`. -/
private lemma map_mkLinearMap_apply {S : Submonoid R} {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (h : M →ₗ[R] N) (x : M) :
    ((LocalizedModule.map S h).restrictScalars R) (LocalizedModule.mkLinearMap S M x) =
      LocalizedModule.mkLinearMap S N (h x) := by
  simpa only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply] using
    LocalizedModule.map_mk S h x (1 : S)

omit [Fintype ι] [DecidableEq ι] in
/-- Every element of `(M j)_{f i}` of the form `f_i^{-n} • ψ_{ij}(y/1)` is represented by an
honest element of `M j`: there are `n` and `x : M j` with `f_i^n • ψ_{ij}(y/1) = x/1`. -/
private lemma exists_pow_representation (D : ModuleGluingData ι f) (i j : ι)
    (y : D.M i) :
    ∃ (n : ℕ) (x : D.M j),
      (f i) ^ n • D.ψ i j
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (D.M i) y) =
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M j) x := by
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers (f i))
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M j))
    (D.ψ i j (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (D.M i) y))
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.property
  exact ⟨n, x, by simpa [Submonoid.smul_def, hn] using hs⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The cocycle condition, read in `((M a)_{f b})_{f i}`: the candidate components
`x a`, `x b` built from `y : M i` satisfy the gluing relation after localizing at `f i`. -/
private lemma localized_gluing_relation (D : ModuleGluingData ι f) (i a b : ι)
    (y : D.M i) (N : ℕ) (x : ∀ j, D.M j)
    (hx : ∀ j,
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M j) (x j) =
        (f i) ^ N • D.ψ i j
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (D.M i) y)) :
    LocalizedModule.mkLinearMap (Submonoid.powers (f i))
        (LocalizedModule (Submonoid.powers (f b)) (D.M a))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f b)) (D.M a) (x a)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i))
        (LocalizedModule (Submonoid.powers (f b)) (D.M a))
        (D.ψ b a (LocalizedModule.mkLinearMap (Submonoid.powers (f a)) (D.M b) (x b))) := by
  have hc := LinearMap.congr_fun (D.cocycle i b a) y
  simp only [LinearMap.comp_apply] at hc
  have hcN := congrArg (fun z => (f i) ^ N • z) hc
  conv at hcN => lhs; rw [← map_smul]
  conv at hcN => rhs; rw [← map_smul, ← map_smul]
  have hxa : (f i) ^ N • ((D.ψ i a).toLinearMap
      (LocalizedModule.mkLinearMap (Submonoid.powers (f a)) (D.M i) y)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M a) (x a) := (hx a).symm
  have hxb : (f i) ^ N • ((D.ψ i b).toLinearMap
      (LocalizedModule.mkLinearMap (Submonoid.powers (f b)) (D.M i) y)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M b) (x b) := (hx b).symm
  rw [hxa, hxb] at hcN
  simpa only [map_mkLinearMap_apply, LinearEquiv.coe_coe] using hcN

omit [Fintype ι] [DecidableEq ι] in
/-- The diagonal transition map `ψ_{ii}` is the identity on elements of the form `y/1`. -/
private lemma self_transition (D : ModuleGluingData ι f) (i : ι) (y : D.M i) :
    D.ψ i i (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M i) y) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M i) y := by
  let g := LocalizedModule.mkLinearMap (Submonoid.powers (f i))
    (LocalizedModule (Submonoid.powers (f i)) (D.M i))
  have hg : Function.Injective g := by
    rw [IsLocalizedModule.injective_iff_isRegular (S := Submonoid.powers (f i))]
    intro s x x' h
    exact IsLocalizedModule.smul_injective
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M i)) s h
  let z := LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M i) y
  let w := D.ψ i i z
  have hc := LinearMap.congr_fun (D.cocycle i i i) y
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hc
  have hmapMk (t : LocalizedModule (Submonoid.powers (f i)) (D.M i)) :
      ((LocalizedModule.map (Submonoid.powers (f i)))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M i))) t = g t := by
    induction t with
    | _ m s =>
      simp only [g, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, LocalizedModule.smul'_mk]
      exact (LocalizedModule.mk_cancel s m).symm
  have hmapPsi (t : LocalizedModule (Submonoid.powers (f i)) (D.M i)) :
      ((LocalizedModule.map (Submonoid.powers (f i))) (D.ψ i i).toLinearMap) (g t) =
        g (D.ψ i i t) := by
    induction t with
    | _ m s => simp [g, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]
  have hc' : g w = g (D.ψ i i w) := by
    rw [hmapMk, hmapPsi] at hc
    simpa [w, z] using hc
  exact (D.ψ i i).injective (hg hc').symm

/-- **Surjectivity up to torsion** for `proj i`: every `y : M i` is hit by an element of the
glued module after multiplying by a power of `f i`. -/
private lemma exists_glued_preimage (D : ModuleGluingData ι f) (i : ι) (y : D.M i) :
    ∃ (m : D.gluedModule) (n : ℕ), (f i) ^ n • y = D.proj i m := by
  choose n x hx using fun j => exists_pow_representation D i j y
  let N := Finset.univ.sup n
  let x' : ∀ j, D.M j := fun j => (f i) ^ (N - n j) • x j
  have hx' : ∀ j,
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M j) (x' j) =
        (f i) ^ N • D.ψ i j
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (D.M i) y) := by
    intro j
    have hj : n j ≤ N := Finset.le_sup (f := n) (Finset.mem_univ j)
    rw [show N = (N - n j) + n j by omega, pow_add, mul_smul, map_smul, hx j]
  let e := fun p : ι × ι =>
    LocalizedModule (Submonoid.powers (f p.2)) (D.M p.1)
  let d : ∀ p : ι × ι, e p := fun p =>
    LocalizedModule.mkLinearMap (Submonoid.powers (f p.2)) (D.M p.1) (x' p.1) -
      D.ψ p.2 p.1
        (LocalizedModule.mkLinearMap (Submonoid.powers (f p.1)) (D.M p.2) (x' p.2))
  have hdloc : ∀ p, LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (e p) (d p) = 0 := by
    rintro ⟨a, b⟩
    rw [map_sub, sub_eq_zero]
    exact localized_gluing_relation D i a b y N x' hx'
  choose q hq using fun p => exists_pow_smul_eq_zero_of_mk_eq_zero (f i) _ (hdloc p)
  have hselfloc : LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (D.M i)
      ((f i) ^ N • y - x' i) = 0 := by
    rw [map_sub, map_smul, hx' i, sub_eq_zero, self_transition D i y]
  obtain ⟨q0, hq0⟩ := exists_pow_smul_eq_zero_of_mk_eq_zero
    (f i) ((f i) ^ N • y - x' i) hselfloc
  let Q := max (Finset.univ.sup q) q0
  let m0 : D.DirectSumM := DirectSum.mk D.M Finset.univ
    (fun j : (↑(Finset.univ : Finset ι) : Set ι) => (f i) ^ Q • x' j.1)
  have hm0 : D.glueMap m0 = 0 := by
    ext p
    obtain ⟨a, b⟩ := p
    rw [DirectSum.apply_eq_component R, DirectSum.zero_apply, D.component_glueMap]
    dsimp [m0]
    rw [DirectSum.mk_apply_of_mem (Finset.mem_univ a),
      DirectSum.mk_apply_of_mem (Finset.mem_univ b)]
    simp only [map_smul]
    rw [← smul_sub]
    dsimp only [d] at hq
    exact pow_smul_eq_zero_of_le (hq (a, b))
      ((Finset.le_sup (f := q) (Finset.mem_univ (a, b))).trans (Nat.le_max_left _ _))
  let m : D.gluedModule := ⟨m0, D.mem_gluedModule.mpr hm0⟩
  refine ⟨m, Q + N, ?_⟩
  rw [proj_apply, pow_add, mul_smul]
  simp only [m, m0, DirectSum.mk_apply_of_mem (Finset.mem_univ i)]
  rw [← sub_eq_zero, ← smul_sub]
  exact pow_smul_eq_zero_of_le hq0 (Nat.le_max_right _ _)

/-- **Stacks 00EQ (localization comparison).** For finite module gluing data, projection to the
`i`-th component is the localization map at the powers of `f i`. Thus the induced canonical map
from the localization of the glued module to `D.M i` is an isomorphism. -/
@[stacks 00EQ "localization comparison"]
theorem proj_isLocalizedModule (D : ModuleGluingData ι f) (i : ι) :
    IsLocalizedModule (Submonoid.powers (f i)) (D.proj i) where
  map_units := D.isUnit_algebraMap_end i
  surj y := by
    obtain ⟨m, n, hm⟩ := exists_glued_preimage D i y
    exact ⟨⟨m, ⟨(f i) ^ n, pow_mem (Submonoid.mem_powers _) n⟩⟩,
      by simpa [Submonoid.smul_def] using hm⟩
  exists_of_eq := by
    intro x₁ x₂ h
    obtain ⟨s, hs⟩ := D.exists_smul_eq_zero_of_proj_eq_zero i (x₁ - x₂) (by
      rw [map_sub, h, sub_self])
    exact ⟨s, sub_eq_zero.mp (by simpa [Submonoid.smul_def, smul_sub] using hs)⟩

end ModuleGluingData
