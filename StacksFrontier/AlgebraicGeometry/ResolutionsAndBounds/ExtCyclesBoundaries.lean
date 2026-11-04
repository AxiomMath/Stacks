module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Cycles, boundaries and `Ext` out of a fixed object

Let `𝒜` be an abelian category, `P` an object of `𝒜` and `K` a cochain complex in `𝒜` indexed
by `ℕ` whose terms satisfy `Ext^k(P, K^q) = 0` for `k ≥ 1`. Write `Hom(P, K^•)` for the complex
of morphisms out of `P`. This file records two dimension-shifting statements about the
cohomology of `Hom(P, K^•)`.

* If `K` is a resolution of an object `G` (that is, `G ⟶ K^0 ⟶ K^1` is left exact and `K` is
  exact in positive degrees), then `Ext^n(P, G)` vanishes for an `n ≥ 1` exactly when every
  `n`-cycle `P ⟶ K^n` of `Hom(P, K^•)` is a boundary. This is the computation of `Ext` by an
  acyclic resolution, in the form of a vanishing criterion.
* If the cohomology objects of `K` satisfy `Ext^k(P, H^q(K)) = 0` whenever `k + q > d`, then
  every `n`-cycle of `Hom(P, K^•)` is a boundary for every `n > d`. This is the vanishing
  statement of the hypercohomology spectral sequence `Ext^k(P, H^q(K)) ⇒ H^{k+q}(Hom(P, K^•))`,
  proved here directly by descending through the cycles of `K`.

## Main results

* `Stacks.ExtCycles.subsingleton_ext_iff_forall_cycle_boundary`: the first statement.
* `Stacks.ExtCycles.exists_comp_d_eq_of_subsingleton_ext_homology`: the second statement.

## Implementation notes

Vanishing of an `Ext` group is expressed by `Subsingleton`. A cycle of `Hom(P, K^•)` in degree
`n + 1` is a morphism `φ : P ⟶ K^{n+1}` with `φ ≫ d = 0`, and it is a boundary when
`φ = ψ ≫ d` for some `ψ : P ⟶ K^n`. The two statements are proved through the short exact
sequences `0 ⟶ Z^q ⟶ K^q ⟶ B^{q+1} ⟶ 0` and `0 ⟶ B^q ⟶ Z^q ⟶ H^q ⟶ 0`, where `Z^q` is the
object of cycles and `B^q` the kernel of `Z^q ⟶ H^q`, and the long exact sequence of
`Ext(P, -)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.ExtCycles

open Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (P : C)

/-! ### Two-out-of-three for the vanishing of `Ext` along a short exact sequence -/

section ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact)
include hS

/-- In the long exact sequence of `Ext(P, -)` the middle term vanishes when its neighbours
do. -/
theorem subsingleton_ext_X₂ {k : ℕ} (h₁ : Subsingleton (Ext.{w} P S.X₁ k))
    (h₃ : Subsingleton (Ext.{w} P S.X₃ k)) : Subsingleton (Ext.{w} P S.X₂ k) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨z₁, hz₁⟩ := Ext.covariant_sequence_exact₂ P hS z (h₃.elim _ _)
  rw [← hz₁, h₁.elim z₁ 0, Ext.zero_comp]

/-- In the long exact sequence of `Ext(P, -)`, `Ext^k(P, X₃)` vanishes when `Ext^k(P, X₂)` and
`Ext^{k+1}(P, X₁)` do. -/
theorem subsingleton_ext_X₃ {k : ℕ} (h₂ : Subsingleton (Ext.{w} P S.X₂ k))
    (h₁ : Subsingleton (Ext.{w} P S.X₁ (k + 1))) : Subsingleton (Ext.{w} P S.X₃ k) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨z₂, hz₂⟩ := Ext.covariant_sequence_exact₃ P hS z rfl (h₁.elim _ _)
  rw [← hz₂, h₂.elim z₂ 0, Ext.zero_comp]

/-- In the long exact sequence of `Ext(P, -)`, `Ext^{k+1}(P, X₁)` vanishes when `Ext^k(P, X₃)`
and `Ext^{k+1}(P, X₂)` do. -/
theorem subsingleton_ext_X₁ {k : ℕ} (h₃ : Subsingleton (Ext.{w} P S.X₃ k))
    (h₂ : Subsingleton (Ext.{w} P S.X₂ (k + 1))) : Subsingleton (Ext.{w} P S.X₁ (k + 1)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨z₃, hz₃⟩ := Ext.covariant_sequence_exact₁ P hS z (h₂.elim _ _) rfl
  rw [← hz₃, h₃.elim z₃ 0, Ext.zero_comp]

/-- In the long exact sequence of `Ext(P, -)`, a morphism `P ⟶ X₃` lifts to `X₂` when
`Ext^1(P, X₁)` vanishes. -/
private theorem exists_comp_g_eq_of_subsingleton_ext_one (h : Subsingleton (Ext.{w} P S.X₁ 1))
    (z : P ⟶ S.X₃) : ∃ ψ : P ⟶ S.X₂, ψ ≫ S.g = z := by
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ z) (zero_add 1) (h.elim _ _)
  obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective P S.X₂).2 x₂
  exact ⟨ψ, (Ext.mk₀_bijective _ _).1 (by rwa [Ext.mk₀_comp_mk₀] at hx₂)⟩

end ShortExact

/-- `Ext` out of `P` vanishes into a zero object. -/
theorem subsingleton_ext_of_isZero {Y : C} (hY : IsZero Y) (k : ℕ) :
    Subsingleton (Ext.{w} P Y k) :=
  subsingleton_of_forall_eq 0 fun z => by
    rw [← Ext.comp_mk₀_id z, show 𝟙 Y = 0 from hY.eq_of_src _ _, Ext.mk₀_zero, Ext.comp_zero]

/-- `Ext` out of `P` into isomorphic objects vanishes simultaneously. -/
theorem subsingleton_ext_of_iso {Y Y' : C} (e : Y ≅ Y') {k : ℕ}
    (h : Subsingleton (Ext.{w} P Y k)) : Subsingleton (Ext.{w} P Y' k) :=
  subsingleton_of_forall_eq 0 fun z => by
    have : z = (z.comp (Ext.mk₀ e.inv) (add_zero k)).comp (Ext.mk₀ e.hom) (add_zero k) := by
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.comp_mk₀_id]
    rw [this, h.elim (z.comp (Ext.mk₀ e.inv) (add_zero k)) 0, Ext.zero_comp]

/-! ### The two short exact sequences attached to a cochain complex -/

variable (K : CochainComplex C ℕ)

/-- The object `B^q` of a cochain complex: the kernel of `Z^q ⟶ H^q`. -/
noncomputable abbrev boundaries (q : ℕ) : C := kernel (K.homologyπ q)

/-- The short complex `B^q ⟶ Z^q ⟶ H^q`. -/
noncomputable abbrev boundariesSc (q : ℕ) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (K.homologyπ q)) (K.homologyπ q) (kernel.condition _)

omit [HasExt C] in
/-- The short complex `0 ⟶ B^q ⟶ Z^q ⟶ H^q ⟶ 0` is short exact. -/
theorem boundariesSc_shortExact (q : ℕ) : (boundariesSc K q).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance inferInstance

/-- The map `K^q ⟶ B^{q+1}` induced by the differential. -/
noncomputable abbrev toBoundaries (q : ℕ) : K.X q ⟶ boundaries K (q + 1) :=
  kernel.lift _ (K.toCycles q (q + 1)) (K.toCycles_comp_homologyπ q (q + 1))

/-- The short complex `Z^q ⟶ K^q ⟶ B^{q+1}`. -/
noncomputable abbrev cyclesSc (q : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles q) (toBoundaries K q) (by
    rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, zero_comp,
      ← cancel_mono (K.iCycles (q + 1)), Category.assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

omit [HasExt C] in
/-- The sequence `K^q ⟶ Z^{q+1} ⟶ H^{q+1}` is exact. -/
theorem toCycles_exact (q : ℕ) :
    (ShortComplex.mk (K.toCycles q (q + 1)) (K.homologyπ (q + 1))
      (K.toCycles_comp_homologyπ q (q + 1))).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel q (q + 1) (by simp))

/-- A map `g` out of `K^q` which becomes the differential after a monomorphism has kernel
`Z^q`. -/
private theorem exact_iCycles_of_comp_mono {D : Type*} [Category D] [Abelian D]
    (K : CochainComplex D ℕ) (q : ℕ) {Y : D} (g : K.X q ⟶ Y) (m : Y ⟶ K.X (q + 1)) [Mono m]
    (hgm : g ≫ m = K.d q (q + 1)) (hg : K.iCycles q ≫ g = 0) :
    (ShortComplex.mk (K.iCycles q) g hg).Exact := by
  let S' := ShortComplex.mk (K.iCycles q) (K.d q (q + 1)) (K.iCycles_d q (q + 1))
  have hS' : S'.Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel q (q + 1) (by simp))
  let φ : ShortComplex.mk (K.iCycles q) g hg ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := m
      comm₁₂ := by simp [S']
      comm₂₃ := by simp [S', hgm] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS'

omit [HasExt C] in
/-- The short complex `0 ⟶ Z^q ⟶ K^q ⟶ B^{q+1} ⟶ 0` is short exact. -/
theorem cyclesSc_shortExact (q : ℕ) : (cyclesSc K q).ShortExact :=
  ShortComplex.ShortExact.mk'
    (exact_iCycles_of_comp_mono K q (toBoundaries K q) (kernel.ι _ ≫ K.iCycles (q + 1))
      (by simp) _)
    inferInstance (toCycles_exact K q).epi_kernelLift

omit [HasExt C] in
/-- The object `B^0` of a cochain complex indexed by `ℕ` is zero. -/
theorem isZero_boundaries_zero : IsZero (boundaries K 0) :=
  isZero_kernel_of_mono _

/-- A lift `ψ` of a cycle `φ'` through `K^n ⟶ Z^{n+1}` is a primitive of the cycle. -/
private theorem comp_d_eq_of_comp_toCycles_eq {D : Type*} [Category D] [Abelian D]
    (K : CochainComplex D ℕ) {X : D} {n : ℕ} (ψ : X ⟶ K.X n) (φ : X ⟶ K.X (n + 1))
    (hφ : φ ≫ K.d (n + 1) (n + 2) = 0)
    (h : ψ ≫ K.toCycles n (n + 1) = K.liftCycles φ (n + 2) (by simp) hφ) :
    ψ ≫ K.d n (n + 1) = φ := by
  rw [← K.toCycles_i n (n + 1), ← Category.assoc, h]
  exact K.liftCycles_i φ (n + 2) (by simp) hφ

/-! ### Cycles are boundaries above the cohomological bound -/

/-- **Cycles are boundaries above the bound.** Let `K` be a cochain complex with
`Ext^k(P, K^q) = 0` for `k ≥ 1`, and suppose that `Ext^k(P, H^q(K)) = 0` whenever `k + q > d`.
Then every cycle `P ⟶ K^{m+1}` of `Hom(P, K^•)` in a degree `m + 1 > d` is a boundary. -/
theorem exists_comp_d_eq_of_subsingleton_ext_homology (d : ℕ)
    (hK : ∀ q k : ℕ, Subsingleton (Ext.{w} P (K.X q) (k + 1)))
    (hH : ∀ q k : ℕ, d < k + q → Subsingleton (Ext.{w} P (K.homology q) k))
    (m : ℕ) (hm : d < m + 1) (φ : P ⟶ K.X (m + 1)) (hφ : φ ≫ K.d (m + 1) (m + 2) = 0) :
    ∃ ψ : P ⟶ K.X m, ψ ≫ K.d m (m + 1) = φ := by
  have hZ : ∀ j : ℕ, j ≤ m → Subsingleton (Ext.{w} P (K.cycles j) (m + 1 - j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact subsingleton_ext_X₂ P (boundariesSc_shortExact K 0)
        (subsingleton_ext_of_isZero P (isZero_boundaries_zero K) _)
        (hH 0 _ (by omega))
    | succ j ih =>
      intro hj
      have h1 : Subsingleton (Ext.{w} P (boundaries K (j + 1)) (m - j)) := by
        have hk : m - j = (m - j - 1) + 1 := by omega
        have h₁ : Subsingleton (Ext.{w} P (K.cycles j) (m - j + 1)) := by
          have := ih (by omega)
          rwa [show m + 1 - j = m - j + 1 by omega] at this
        rw [hk] at h₁ ⊢
        exact subsingleton_ext_X₃ P (cyclesSc_shortExact K j) (hK j _) h₁
      have h2 := subsingleton_ext_X₂ P (boundariesSc_shortExact K (j + 1)) h1
        (hH (j + 1) (m - j) (by omega))
      rwa [show m + 1 - (j + 1) = m - j by omega]
  have hZm : Subsingleton (Ext.{w} P (K.cycles m) 1) := by simpa using hZ m le_rfl
  let φ' : P ⟶ K.cycles (m + 1) := K.liftCycles φ (m + 2) (by simp) hφ
  have hπ : φ' ≫ K.homologyπ (m + 1) = 0 :=
    (Ext.mk₀_bijective _ _).1 ((hH (m + 1) 0 (by omega)).elim (Ext.mk₀ _) (Ext.mk₀ 0))
  let φ'' : P ⟶ boundaries K (m + 1) := kernel.lift _ φ' hπ
  obtain ⟨ψ, hψ⟩ : ∃ ψ : P ⟶ K.X m, ψ ≫ toBoundaries K m = φ'' :=
    exists_comp_g_eq_of_subsingleton_ext_one P (cyclesSc_shortExact K m) hZm φ''
  refine ⟨ψ, comp_d_eq_of_comp_toCycles_eq K ψ φ hφ ?_⟩
  rw [← kernel.lift_ι (K.homologyπ (m + 1)) (K.toCycles m (m + 1))
    (K.toCycles_comp_homologyπ m (m + 1)), ← Category.assoc, hψ, kernel.lift_ι]

/-! ### Computing `Ext` by an acyclic resolution -/

/-- The short complex `Z^q ⟶ K^q ⟶ Z^{q+1}` of a complex that is exact in degree `q + 1`. -/
noncomputable abbrev cyclesSc' (q : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles q) (K.toCycles q (q + 1)) (by
    rw [← cancel_mono (K.iCycles (q + 1)), Category.assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

omit [HasExt C] in
/-- If `K` is exact in degree `q + 1`, then the short complex `0 ⟶ Z^q ⟶ K^q ⟶ Z^{q+1} ⟶ 0` is
short exact. -/
theorem cyclesSc'_shortExact (q : ℕ) (hq : K.ExactAt (q + 1)) : (cyclesSc' K q).ShortExact := by
  have hH : IsZero (K.homology (q + 1)) := (K.exactAt_iff_isZero_homology _).1 hq
  exact ShortComplex.ShortExact.mk'
    (exact_iCycles_of_comp_mono K q (K.toCycles q (q + 1)) (K.iCycles (q + 1)) (by simp) _)
    inferInstance ((toCycles_exact K q).epi_f (hH.eq_of_tgt _ _))

/-- **`Ext` computed by an acyclic resolution.** Let `K` be a cochain complex which is exact in
every positive degree and satisfies `Ext^k(P, K^q) = 0` for `k ≥ 1`, and let `G ≅ Z^0(K)`. Then
`Ext^{n+1}(P, G)` vanishes exactly when every cycle `P ⟶ K^{n+1}` of `Hom(P, K^•)` is a
boundary. -/
theorem subsingleton_ext_iff_forall_cycle_boundary {G : C} (e : G ≅ K.cycles 0)
    (hexact : ∀ q : ℕ, K.ExactAt (q + 1))
    (hK : ∀ q k : ℕ, Subsingleton (Ext.{w} P (K.X q) (k + 1))) (n : ℕ) :
    Subsingleton (Ext.{w} P G (n + 1)) ↔
      ∀ φ : P ⟶ K.X (n + 1), φ ≫ K.d (n + 1) (n + 2) = 0 →
        ∃ ψ : P ⟶ K.X n, ψ ≫ K.d n (n + 1) = φ := by
  constructor
  · intro hG φ hφ
    -- `Ext^{n+1-j}(P, Z^j) = 0` for `j ≤ n`.
    have hZ : ∀ j : ℕ, j ≤ n → Subsingleton (Ext.{w} P (K.cycles j) (n + 1 - j)) := by
      intro j
      induction j with
      | zero => intro _; simpa using subsingleton_ext_of_iso P e hG
      | succ j ih =>
        intro hj
        have h := subsingleton_ext_X₃ P (cyclesSc'_shortExact K j (hexact j))
          (k := n - j) (by rw [show n - j = (n - j - 1) + 1 by omega]; exact hK j _)
          (by have := ih (by omega); rwa [show n + 1 - j = n - j + 1 by omega] at this)
        rwa [show n + 1 - (j + 1) = n - j by omega]
    have hZn : Subsingleton (Ext.{w} P (K.cycles n) 1) := by simpa using hZ n le_rfl
    let φ' : P ⟶ K.cycles (n + 1) := K.liftCycles φ (n + 2) (by simp) hφ
    obtain ⟨ψ, hψ⟩ : ∃ ψ : P ⟶ K.X n, ψ ≫ K.toCycles n (n + 1) = φ' :=
      exists_comp_g_eq_of_subsingleton_ext_one P (cyclesSc'_shortExact K n (hexact n)) hZn φ'
    exact ⟨ψ, comp_d_eq_of_comp_toCycles_eq K ψ φ hφ hψ⟩
  · intro hcyc
    have hZn : Subsingleton (Ext.{w} P (K.cycles n) 1) := by
      refine subsingleton_of_forall_eq 0 fun z => ?_
      obtain ⟨z₃, hz₃⟩ := Ext.covariant_sequence_exact₁ P (cyclesSc'_shortExact K n (hexact n))
        z ((hK n 0).elim _ _) (zero_add 1)
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective P (K.cycles (n + 1))).2 z₃
      obtain ⟨ψ, hψ⟩ := hcyc (g ≫ K.iCycles (n + 1)) (by simp)
      have hg : g = ψ ≫ K.toCycles n (n + 1) := by
        rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, HomologicalComplex.toCycles_i,
          hψ]
      rw [← hz₃, hg, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
        (cyclesSc'_shortExact K n (hexact n)).comp_extClass, Ext.comp_zero]
    have hZ : ∀ j : ℕ, j ≤ n → Subsingleton (Ext.{w} P (K.cycles (n - j)) (j + 1)) := by
      intro j
      induction j with
      | zero => intro _; simpa using hZn
      | succ j ih =>
        intro hj
        exact subsingleton_ext_X₁ P (cyclesSc'_shortExact K (n - (j + 1)) (hexact _))
          (k := j + 1)
          (by
            have := ih (by omega)
            rwa [show n - j = n - (j + 1) + 1 by omega] at this) (hK _ _)
    exact subsingleton_ext_of_iso P e.symm (by simpa using hZ n le_rfl)

/-- **`Ext` computed by an acyclic resolution**, for a resolution presented by a kernel fork:
`G ⟶ K^0` is a kernel of `K^0 ⟶ K^1`. -/
theorem subsingleton_ext_iff_forall_cycle_boundary_of_isLimit {G : C} {f : G ⟶ K.X 0}
    {hw : f ≫ K.d 0 1 = 0} (hf : IsLimit (KernelFork.ofι f hw))
    (hexact : ∀ q : ℕ, K.ExactAt (q + 1))
    (hK : ∀ q k : ℕ, Subsingleton (Ext.{w} P (K.X q) (k + 1))) (n : ℕ) :
    Subsingleton (Ext.{w} P G (n + 1)) ↔
      ∀ φ : P ⟶ K.X (n + 1), φ ≫ K.d (n + 1) (n + 2) = 0 →
        ∃ ψ : P ⟶ K.X n, ψ ≫ K.d n (n + 1) = φ :=
  subsingleton_ext_iff_forall_cycle_boundary P K
    (IsLimit.conePointUniqueUpToIso hf (K.cyclesIsKernel 0 1 (by simp))) hexact hK n

end Stacks.ExtCycles

end
