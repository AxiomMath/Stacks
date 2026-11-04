module

public import StacksFrontier.RingTheory.HilbertFunction.AdmissibleModule
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Data.Rat.Star
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.AffineMonoid.UniqueSums

/-!
# The degree bound for the Hilbert function of `k[X_1, …, X_d]/I`

Admissibility of the cokernel of multiplication by the last variable, the Hilbert–Serre
induction for admissible graded modules, and the main result `hilbertFunction_degree_lt`
(Stacks Lemma 10.58.10, Tag 00K3).
-/

@[expose] public section
-- needed file-wide: `FinModule.cls_eq_of_linearEquiv`, `FinModule.cls_add_of_ses`,
-- `KPrime0.hom_ext`, `xpow_four_term_class` and `hilbertFun_xpow_step_identity` all rewrite
-- through the `FinModule`/`KPrime0` quotient wrappers and the graded-piece subgroup coercions,
-- which only unfold with defeq transparency relaxed.  See also the note before
-- `section MainPieces`, which depends on this option holding for the whole file.
set_option backward.isDefEq.respectTransparency false
universe u

namespace Stacks.HilbertFunction.PolynomialQuotient

variable {k : Type*} [Field k] {d : ℕ}

/-- **Homogeneity of the image of a degree-shifting linear map.** For an independent
spanning grading `p` and a degree-raising map `T`, the degree-`(m+1)` piece of the range
of `T` is exactly the image of the degree-`m` piece. -/
theorem image_homogeneous {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : ℕ → Submodule R M) (T : M →ₗ[R] M) (hindep : iSupIndep p) (htop : iSup p = ⊤)
    (hshift : ∀ (n : ℕ) (x : M), x ∈ p n → T x ∈ p (n + 1)) (m : ℕ) :
    LinearMap.range T ⊓ p (m + 1) = Submodule.map T (p m) := by
  classical
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hzr, hzp⟩ := hz
    rw [LinearMap.mem_range] at hzr
    obtain ⟨y, rfl⟩ := hzr
    have hymem : y ∈ ⨆ n, p n := htop ▸ Submodule.mem_top
    rw [Submodule.mem_iSup_iff_exists_dfinsupp] at hymem
    obtain ⟨f, hf⟩ := hymem
    set L := DFinsupp.lsum ℕ (fun n => (p n).subtype) with hL
    have hLeq : ∀ (φ : Π₀ n, p n), L φ = φ.sum (fun n b => (b : M)) := by
      intro φ
      simp only [hL, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]; rfl
    set g : Π₀ n, p n :=
      f.sum
        (fun i fi =>
          DFinsupp.single (i + 1) (⟨T (fi : M), hshift i fi fi.property⟩ : p (i + 1))) with
      hg
    have hLg : L g = T y := by
      rw [hg, map_dfinsuppSum]
      rw [← hf, hLeq, map_dfinsuppSum]
      have hfun :
        (fun a (b : p a) =>
            L (DFinsupp.single (a + 1) (⟨T (b : M), hshift a b b.property⟩ : p (a + 1)))) =
          (fun a (b : p a) => T (b : M)) := by
        funext a b
        rw [hL, DFinsupp.lsum_single]
        rfl
      rw [hfun]
    -- the single concentrated at m+1
    set s : Π₀ n, p n := DFinsupp.single (m + 1) (⟨T y, hzp⟩ : p (m + 1)) with hs
    have hLs : L s = T y := by
      rw [hs, hL, DFinsupp.lsum_single]; rfl
    have hgs : g = s := by
      apply hindep.dfinsupp_lsum_injective
      rw [← hL, hLg, hLs]
    -- read off component m+1
    have hgm : ((g (m + 1) : p (m + 1)) : M) = T y := by
      rw [hgs, hs, DFinsupp.single_apply, dite_eq_left rfl]
    -- also g (m+1) = T (f m)
    have hcomp : ((g (m + 1) : p (m + 1)) : M) = T (f m : M) := by
      rw [hg, DFinsupp.sum_apply]
      let h₀ : (j : ℕ) → p j → p (m + 1) := fun j fj =>
        (DFinsupp.single (j + 1) (⟨T (fj : M), hshift j fj fj.property⟩ : p (j + 1)) :
            Π₀ n, ↥(p n))
          (m + 1)
      have hpush := map_dfinsuppSum (AddSubmonoidClass.subtype (p (m + 1))) f h₀
      show (AddSubmonoidClass.subtype (p (m + 1))) (f.sum h₀) = T (f m : M)
      rw [hpush]
      rw [show
          (f.sum fun j (fj : p j) => (AddSubmonoidClass.subtype (p (m + 1))) (h₀ j fj)) =
            ∑ j ∈ f.support, (AddSubmonoidClass.subtype (p (m + 1))) (h₀ j (f j))
          from rfl]
      rw [Finset.sum_eq_single m]
      · show ((h₀ m (f m) : p (m + 1)) : M) = T (f m : M)
        simp only [h₀]
        rw [DFinsupp.single_apply, dite_eq_left rfl]
      · intro j _ hjm
        show ((h₀ j (f j) : p (m + 1)) : M) = 0
        simp only [h₀]
        rw [DFinsupp.single_apply, dite_eq_right (by omega)]
        simp
      · intro hni
        rw [DFinsupp.mem_support_toFun] at hni
        have hfm0 : f m = 0 := by simpa using hni
        show ((h₀ m (f m) : p (m + 1)) : M) = 0
        simp only [h₀]
        rw [DFinsupp.single_apply, dite_eq_left rfl]
        rw [hfm0]
        simp
    -- conclude
    have : T y = T (f m : M) := by rw [← hgm, hcomp]
    rw [this]
    exact Submodule.mem_map_of_mem (f m).property
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact ⟨LinearMap.mem_range.mpr ⟨x, rfl⟩, hshift m x hx⟩

/-- Component extraction: if `a` is homogeneous of degree `i`, `b` lives in the other
degrees, and `a - b` lies in `⨆ n, Q n` with `Q n ≤ p n` for an independent grading `p`,
then `a ∈ Q i`. -/
theorem homog_component_mem {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ι → Submodule R M) (Q : ι → Submodule R M) (hQ : ∀ n, Q n ≤ p n) (hindep : iSupIndep p)
    (i : ι) (a b : M) (ha : a ∈ p i) (hb : b ∈ ⨆ (j : ι) (_ : j ≠ i), p j)
    (hab : a - b ∈ ⨆ n, Q n) : a ∈ Q i := by
  classical
  rw [Submodule.mem_iSup_iff_exists_dfinsupp] at hab
  obtain ⟨q, hq⟩ := hab
  -- q i ∈ Q i
  -- a - q i  ∈ p i ⊓ (⨆ j≠i p j) = ⊥
  set L := DFinsupp.lsum ℕ (fun n => (Q n).subtype) with hL
  -- decompose: a - b = ∑ q n
  -- so a - (q i) = b + ∑_{n≠i} q n  ∈ ⨆ j≠i p j
  have hdisj : Disjoint (p i) (⨆ (j : ι) (_ : j ≠ i), p j) := (iSupIndep_def.mp hindep) i
  -- show a - (q i : M) ∈ p i
  have h1 : (a - (q i : M)) ∈ p i := Submodule.sub_mem _ ha (hQ i (q i).property)
  -- show a - (q i : M) ∈ ⨆ j≠i p j
  have h2 : (a - (q i : M)) ∈ ⨆ (j : ι) (_ : j ≠ i), p j := by
    -- a - q i = b + (∑ q n - q i) = b + ∑_{n≠i} q n
    have hsum : (a - b) = L q := hq.symm
    -- a - q i = b + ((a-b) - q i) ... actually a - q i = (a - b) + b - q i
    have hrw : a - (q i : M) = b + ((L q) - (q i : M)) := by
      rw [← hsum]; abel
    rw [hrw]
    apply Submodule.add_mem
    · exact hb
    · -- (∑ q n) - q i = ∑_{n≠i} q n ∈ ⨆ j≠i p j
      have hLsum : L q = ∑ n ∈ q.support, ((q n : M)) := by
        rw [hL, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum]
        rfl
      rw [hLsum]
      have hmem_erase : (∑ n ∈ q.support.erase i, ((q n : M))) ∈ ⨆ (j : ι) (_ : j ≠ i), p j := by
        apply Submodule.sum_mem
        intro n hn
        have hni : n ≠ i := Finset.ne_of_mem_erase hn
        exact Submodule.mem_iSup_of_mem n (Submodule.mem_iSup_of_mem hni (hQ n (q n).property))
      by_cases hi : i ∈ q.support
      · rwa [Finset.sum_erase_eq_sub hi] at hmem_erase
      · have hqi0 : (q i : M) = 0 := by
          have h0 := DFinsupp.notMem_support_iff.mp hi
          rw [h0]; rfl
        rw [hqi0, sub_zero, ← Finset.erase_eq_of_notMem hi]
        exact hmem_erase
  have : (a - (q i : M)) = 0 := (Submodule.disjoint_def.mp hdisj) _ h1 h2
  have : a = (q i : M) := by
    rw [sub_eq_zero] at this; exact this
  rw [this]; exact (q i).property

/-- Images of an independent grading under a linear map are independent, provided the
kernel of the map is homogeneous. -/
theorem iSupIndep_map_of_ker_le {ι R M C : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup C] [Module R C] (φ : M →ₗ[R] C) (p : ι → Submodule R M) (hindep : iSupIndep p)
    (hker : LinearMap.ker φ ≤ ⨆ n, (LinearMap.ker φ ⊓ p n)) :
    iSupIndep (fun n => Submodule.map φ (p n)) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro c hci hcrest
  -- c ∈ map φ (p i)
  rw [Submodule.mem_map] at hci
  obtain ⟨a, ha, hac⟩ := hci
  -- c ∈ ⨆ j≠i, map φ (p j) = map φ (⨆ j≠i p j)
  have hsupeq :
    (⨆ (j : ι) (_ : j ≠ i), Submodule.map φ (p j)) =
      Submodule.map φ (⨆ (j : ι) (_ : j ≠ i), p j) := by
    rw [Submodule.map_iSup]
    apply iSup_congr; intro j; rw [Submodule.map_iSup]
  rw [hsupeq, Submodule.mem_map] at hcrest
  obtain ⟨b, hb, hbc⟩ := hcrest
  -- φ (a - b) = 0
  have hab0 : φ (a - b) = 0 := by rw [map_sub, hac, hbc, sub_self]
  have habker : a - b ∈ LinearMap.ker φ := LinearMap.mem_ker.mpr hab0
  -- apply homog_component_mem with Q n = ker φ ⊓ p n
  have hain : a ∈ LinearMap.ker φ ⊓ p i :=
    homog_component_mem p (fun n => LinearMap.ker φ ⊓ p n) (fun n => inf_le_right) hindep i a b ha
      hb (hker habker)
  have : φ a = 0 := LinearMap.mem_ker.mp hain.left
  rw [← hac, this]

/-- The range of a degree-raising map is homogeneous: contained in the sup of its graded
intersections. -/
theorem range_homogeneous {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : ℕ → Submodule R M) (T : M →ₗ[R] M) (hindep : iSupIndep p) (htop : iSup p = ⊤)
    (hshift : ∀ (n : ℕ) (x : M), x ∈ p n → T x ∈ p (n + 1)) :
    LinearMap.range T ≤ ⨆ n, (LinearMap.range T ⊓ p n) := by
  intro z hz
  have hzr : z ∈ Submodule.map T (⨆ n, p n) := by
    rw [htop]
    rw [LinearMap.mem_range] at hz
    obtain ⟨y, rfl⟩ := hz
    exact Submodule.mem_map_of_mem Submodule.mem_top
  rw [Submodule.map_iSup] at hzr
  -- z ∈ ⨆ n, map T (p n)
  have hle : ∀ n, Submodule.map T (p n) ≤ ⨆ m, (LinearMap.range T ⊓ p m) := by
    intro n
    rw [image_homogeneous p T hindep htop hshift n |>.symm]
    exact le_iSup (fun m => LinearMap.range T ⊓ p m) (n + 1)
  exact iSup_le hle hzr

/-- Rank–nullity for the restriction of a linear map to a finite-dimensional submodule `P`:
`dim π(P) + dim (P ∩ ker π) = dim P`. -/
private theorem finrank_map_add_finrank_comap_ker {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (π : M →ₗ[k] N) (P : Submodule k M) [Module.Finite k P] :
    Module.finrank k (P.map π) + Module.finrank k ((LinearMap.ker π).comap P.subtype) =
      Module.finrank k P := by
  have := LinearMap.finrank_range_add_finrank_ker (π.submoduleMap P)
  rwa [LinearMap.range_eq_top.mpr (π.submoduleMap_surjective P), finrank_top,
    LinearMap.ker_submoduleMap] at this

/-- For an admissible graded `S^{(d+1)}`-module `A`, the cokernel `C = M/(X_last·M)` is an
admissible graded `S^{(d)}`-module whose degree-`n` Hilbert value (for `n ≥ 1`) equals
`dim_k (A.Mgr n) - dim_k (range (mulXLastDeg A (n-1)))`, i.e. the dimension of the
cokernel of the degreewise map `mulXLastDeg A (n-1) : A.Mgr (n-1) → A.Mgr n`. In degree
`0` (where there is no incoming map) `C_0 = A.Mgr 0`.

Construction: dual to the kernel — `C = A.M / (X_last · A.M)` is a graded quotient with
`C_n = A.Mgr n / range(mulXLastDeg A (n-1))`; `X_last` annihilates `C`, descend the action
to `S^{(d)}`; quotient of f.g. is f.g.; finite-dim degreewise. -/
theorem exists_cokernel_admissible {d : ℕ} (A : AdmissibleGradedModule k (d + 1)) :
    ∃ Cmod : AdmissibleGradedModule k d,
      ∀ n : ℕ,
        1 ≤ n →
          Cmod.hilb n =
            (Module.finrank k (A.Mgr n) : ℤ) -
              (Module.finrank k (LinearMap.range (mulXLastDeg A (n - 1))) : ℤ) := by
  classical
  set ren : MvPolynomial (Fin d) k →ₐ[k] MvPolynomial (Fin (d + 1)) k :=
    MvPolynomial.rename Fin.castSucc with hren
  set lXS : A.M →ₗ[MvPolynomial (Fin (d + 1)) k] A.M :=
    LinearMap.lsmul (MvPolynomial (Fin (d + 1)) k) A.M (MvPolynomial.X (Fin.last d)) with hlXS
  set lX : A.M →ₗ[k] A.M := lXS.restrictScalars k with hlX
  set XM : Submodule (MvPolynomial (Fin (d + 1)) k) A.M := LinearMap.range lXS with hXM
  -- C = A.M / XM
  -- S^(d)-module structure on the quotient via ren
  let moduleS₀ : Module (MvPolynomial (Fin d) k) (A.M ⧸ XM) :=
    Module.compHom (M := A.M ⧸ XM) ren.toRingHom
  have tower₀ : IsScalarTower k (MvPolynomial (Fin d) k) (A.M ⧸ XM) := by
    refine ⟨fun c r x => ?_⟩
    show (ren (c • r)) • x = c • ((ren r) • x)
    rw [map_smul, smul_assoc]
  -- the k-linear quotient map
  set π : A.M →ₗ[k] (A.M ⧸ XM) := (XM.mkQ).restrictScalars k with hπ
  -- grading
  set Cgr : ℕ → Submodule k (A.M ⧸ XM) := fun n => Submodule.map π (A.Mgr n) with hCgr
  -- lX raises degree
  have hshiftlX : ∀ (n : ℕ) (x : A.M), x ∈ A.Mgr n → lX x ∈ A.Mgr (n + 1) :=
    fun n x hx => A.smul_mem (Fin.last d) n x hx
  -- ker π = XM.restrictScalars k = range lX
  have hkerπ : LinearMap.ker π = LinearMap.range lX := by
    rw [hπ, LinearMap.ker_restrictScalars, Submodule.ker_mkQ, hXM, hlX,
      LinearMap.range_restrictScalars]
  refine
    ⟨{  M := A.M ⧸ XM
        Mgr := Cgr
        iSupIndep := ?_
        iSup_eq := ?_
        finite := ?_
        smul_mem := ?_
        fg := ?_ }, ?_⟩
  · -- iSupIndep
    apply iSupIndep_map_of_ker_le π A.Mgr A.iSupIndep
    rw [hkerπ]
    exact range_homogeneous A.Mgr lX A.iSupIndep A.iSup_eq hshiftlX
  · -- iSup_eq
    rw [hCgr, ← Submodule.map_iSup, A.iSup_eq, Submodule.map_top, hπ,
      LinearMap.range_restrictScalars, Submodule.range_mkQ, Submodule.restrictScalars_top]
  · -- finite
    intro n
    have : Module.Finite k (A.Mgr n) := A.finite n
    exact Module.Finite.map (A.Mgr n) π
  · -- smul_mem
    intro i n x hx
    rw [hCgr] at hx ⊢
    rw [Submodule.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [Submodule.mem_map]
    refine
      ⟨(MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (d + 1)) k) • a,
        A.smul_mem (Fin.castSucc i) n a ha, ?_⟩
    -- π (X(castSucc i) • a) = X i • π a
    have hsm :
      (MvPolynomial.X i : MvPolynomial (Fin d) k) • (π a) =
        (ren (MvPolynomial.X i : MvPolynomial (Fin d) k)) • (π a) :=
      rfl
    rw [hsm, hren, MvPolynomial.rename_X]
    change
      π ((MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (d + 1)) k) • a) =
        (MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (d + 1)) k) • (π a)
    rw [hπ]
    exact (XM.mkQ.map_smul _ _).symm ▸ rfl
  · -- fg
    -- C is f.g. over S₁ = S^(d+1) (quotient of f.g.)
    have hR1fin : Module.Finite (MvPolynomial (Fin (d + 1)) k) A.M := A.fg
    have hCfin1 : Module.Finite (MvPolynomial (Fin (d + 1)) k) (A.M ⧸ XM) :=
      Module.Finite.of_surjective XM.mkQ (Submodule.mkQ_surjective XM)
    -- X_last annihilates C
    have hXlast0 :
      ∀ c : (A.M ⧸ XM), (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • c = 0 := by
      intro c
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective XM c
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hXM]
      exact ⟨a, rfl⟩
    -- key semilinearity: qmap(s) • c = s • c
    have hsurj : RingHomSurjective (qmap k d).toRingHom := ⟨qmap_surjective k d⟩
    have hkey :
      ∀ (s : MvPolynomial (Fin (d + 1)) k) (c : (A.M ⧸ XM)),
        ((qmap k d s) • c : (A.M ⧸ XM)) = s • c := by
      intro s c
      show (ren (qmap k d s)) • c = s • c
      have hmem := sub_rename_qmap_mem_span_X_last k d s
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨h, hh⟩ := hmem
      have hz : (s - ren (qmap k d s)) • c = 0 := by
        rw [hren] at *
        rw [hh, mul_comm, mul_smul, hXlast0, smul_zero]
      rw [sub_smul, sub_eq_zero] at hz
      exact hz.symm
    -- qmap-semilinear identity map C → C
    let f : (A.M ⧸ XM) →ₛₗ[(qmap k d).toRingHom] (A.M ⧸ XM) :=
      { toFun := id
        map_add' := fun a b => rfl
        map_smul' := fun s x => (hkey s x).symm }
    exact Module.Finite.of_surjective f (fun x => ⟨x, rfl⟩)
  · -- hilb
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    change
      (Module.finrank k ((A.Mgr (m + 1)).map π) : ℤ) =
        (Module.finrank k (A.Mgr (m + 1)) : ℤ) -
          (Module.finrank k (LinearMap.range (mulXLastDeg A m)) : ℤ)
    have : Module.Finite k (A.Mgr (m + 1)) := A.finite (m + 1)
    -- the kernel of `π` on `A.Mgr (m+1)` is the range of `mulXLastDeg A m`
    have hkereq : (LinearMap.ker π).comap (A.Mgr (m + 1)).subtype =
        LinearMap.range (mulXLastDeg A m) := by
      apply le_antisymm
      · rintro ⟨x, hx⟩ hxk
        have hxrange : x ∈ LinearMap.range lX := by
          rw [← hkerπ]; exact hxk
        -- x ∈ range lX ⊓ A.Mgr (m+1) = map lX (A.Mgr m)
        have hxinf : x ∈ LinearMap.range lX ⊓ A.Mgr (m + 1) := ⟨hxrange, hx⟩
        rw [image_homogeneous A.Mgr lX A.iSupIndep A.iSup_eq hshiftlX m] at hxinf
        obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hxinf
        exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
      · rintro _ ⟨⟨y, hy⟩, rfl⟩
        have hmem :
          (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • y ∈ LinearMap.range lX :=
          ⟨y, rfl⟩
        rw [← hkerπ] at hmem
        exact hmem
    have hrn := finrank_map_add_finrank_comap_ker π (A.Mgr (m + 1))
    rw [hkereq] at hrn
    omega

/-- Rank–nullity for multiplication by the last variable: the kernel and cokernel are
admissible graded modules over `d` variables whose Hilbert functions compute the first
difference of the Hilbert function of `A`. -/
theorem exists_kernel_cokernel_firstDifference {d : ℕ} (A : AdmissibleGradedModule k (d + 1)) :
    ∃ (Kmod Cmod : AdmissibleGradedModule k d),
      ∀ n : ℕ, 1 ≤ n → A.hilb n - A.hilb (n - 1) = Cmod.hilb n - Kmod.hilb (n - 1) := by
  -- Obtain the kernel and cokernel admissible modules with their dimension formulas.
  obtain ⟨Kmod, hK⟩ := exists_kernel_admissible A
  obtain ⟨Cmod, hC⟩ := exists_cokernel_admissible A
  refine ⟨Kmod, Cmod, fun n hn => ?_⟩
  -- Let `m := n - 1`, so `n = m + 1`. The degreewise map is `μ := mulXLastDeg A m`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- Rewrite the kernel/cokernel Hilbert values via `hK`, `hC`.
  rw [hK m, hC (m + 1) (by omega)]
  -- Now the goal is, with `μ := mulXLastDeg A m : A.Mgr m → A.Mgr (m+1)`:
  --   A.hilb (m+1) - A.hilb m
  --     = (finrank (A.Mgr (m+1)) - finrank (range μ)) - finrank (ker μ).
  -- Unfold `A.hilb` and apply rank–nullity `finrank (range μ) + finrank (ker μ) =
  --   finrank (A.Mgr m)` (`LinearMap.finrank_range_add_finrank_ker`, valid since the
  --   pieces are finite-dim over the field k by `A.finite`).
  change
    (Module.finrank k (A.Mgr (m + 1)) : ℤ) - (Module.finrank k (A.Mgr m) : ℤ) =
      ((Module.finrank k (A.Mgr (m + 1)) : ℤ) -
          (Module.finrank k (LinearMap.range (mulXLastDeg A m)) : ℤ)) -
        (Module.finrank k (LinearMap.ker (mulXLastDeg A m)) : ℤ)
  -- The arithmetic reduces to: finrank (A.Mgr m) = finrank (range μ) + finrank (ker μ).
  have hrn :
    Module.finrank k (LinearMap.range (mulXLastDeg A m)) +
        Module.finrank k (LinearMap.ker (mulXLastDeg A m)) =
      Module.finrank k (A.Mgr m) := by
    have := A.finite m
    have := A.finite (m + 1)
    exact LinearMap.finrank_range_add_finrank_ker (mulXLastDeg A m)
  have :
    (Module.finrank k (A.Mgr m) : ℤ) =
      (Module.finrank k (LinearMap.range (mulXLastDeg A m)) : ℤ) +
        (Module.finrank k (LinearMap.ker (mulXLastDeg A m)) : ℤ) := by
    rw [← hrn]; push_cast; ring
  rw [this]; ring

/-- **Hilbert–Serre for admissible graded modules.** The Hilbert function of any
admissible graded `S^{(d)}`-module is a `ℕ`-indexed numerical polynomial. -/
theorem isNumericalPolynomialByNaturalArgs_hilb :
    ∀ (d : ℕ) (A : AdmissibleGradedModule k d), IsNumericalPolynomialByNaturalArgs A.hilb := by
  intro d
  induction d with
  | zero =>
    intro A
    exact
      IsNumericalPolynomialByNaturalArgs.congr (AdmissibleGradedModule.hilb_eventually_eq_zero A)
        (by simpa using (isNumericalPolynomialByNaturalArgs_binomial_sum 0 (fun _ => 0)))
  | succ d ih =>
    intro A
    obtain ⟨Kmod, Cmod, hid⟩ := exists_kernel_cokernel_firstDifference A
    have hK : IsNumericalPolynomialByNaturalArgs Kmod.hilb := ih Kmod
    have hC : IsNumericalPolynomialByNaturalArgs Cmod.hilb := ih Cmod
    have hdiff : IsNumericalPolynomialByNaturalArgs (fun n => Cmod.hilb n - Kmod.hilb (n - 1)) :=
      IsNumericalPolynomialByNaturalArgs.sub hC (IsNumericalPolynomialByNaturalArgs.comp_sub_one hK)
    have hAdiff : IsNumericalPolynomialByNaturalArgs (fun n => A.hilb n - A.hilb (n - 1)) := by
      refine IsNumericalPolynomialByNaturalArgs.congr ?_ hdiff
      rw [Filter.eventually_atTop]
      exact ⟨1, fun n hn => hid n hn⟩
    exact numerical_polynomial_of_difference A.hilb hAdiff

/-- **Specialization to `M = S/I`.** For a homogeneous ideal `I ⊆ S = k[X_1..X_d]`,
the quotient `S/I` with its quotient grading is an admissible graded `S`-module whose
generalized Hilbert function agrees with `hilbertFunction I`. -/
theorem exists_admissible_of_ideal (I : Ideal (MvPolynomial (Fin d) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) k) I) :
    ∃ A : AdmissibleGradedModule k d, ∀ n : ℕ, A.hilb n = (hilbertFunction I n : ℤ) := by
  classical
  -- the k-linear quotient map S → S/I
  set π : MvPolynomial (Fin d) k →ₗ[k] (MvPolynomial (Fin d) k ⧸ I) :=
    (Ideal.Quotient.mkₐ k I).toLinearMap with hπ
  -- kernel of π = I.restrictScalars k
  have hkerπ : LinearMap.ker π = I.restrictScalars k := by
    ext x
    simp only [hπ, LinearMap.mem_ker, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Submodule.restrictScalars_mem, Ideal.Quotient.eq_zero_iff_mem]
  -- grading on S/I
  set Mgr : ℕ → Submodule k (MvPolynomial (Fin d) k ⧸ I) := fun n =>
    Submodule.map π (gradedPieceS k d n) with hMgr
  -- homogeneity of the grading of S
  have hSint : DirectSum.IsInternal (MvPolynomial.homogeneousSubmodule (Fin d) k) :=
    DirectSum.Decomposition.isInternal _
  have hindepS : iSupIndep (fun n => gradedPieceS k d n) := hSint.submodule_iSupIndep
  have htopS : iSup (fun n => gradedPieceS k d n) = ⊤ := hSint.submodule_iSup_eq_top
  -- homogeneity of the kernel
  have hkerhom : LinearMap.ker π ≤ ⨆ n, (LinearMap.ker π ⊓ gradedPieceS k d n) := by
    rw [hkerπ]
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    have hdecomp := DirectSum.sum_support_decompose (MvPolynomial.homogeneousSubmodule (Fin d) k) x
    rw [← hdecomp]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.mem_iSup_of_mem i
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Submodule.restrictScalars_mem]
      exact hI_hom i hx
    · exact (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin d) k) x i).property
  -- semilinearity: π (s • a) = s • π a
  have hsmul : ∀ (s a : MvPolynomial (Fin d) k), π (s • a) = s • (π a) := by
    intro s a
    simp only [hπ, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul]
    rw [map_mul]; rfl
  -- finiteness of each graded piece S_n
  have hSnfin : ∀ n, Module.Finite k (gradedPieceS k d n) := by
    intro n
    rw [gradedPieceS]
    have hle :
      MvPolynomial.homogeneousSubmodule (Fin d) k n ≤
        MvPolynomial.restrictTotalDegree (Fin d) k n := by
      intro p hp
      rw [MvPolynomial.mem_homogeneousSubmodule] at hp
      rw [MvPolynomial.mem_restrictTotalDegree]
      exact hp.totalDegree_le
    have : Module.Finite k (MvPolynomial.restrictTotalDegree (Fin d) k n) := inferInstance
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  refine
    ⟨{  M := MvPolynomial (Fin d) k ⧸ I
        Mgr := Mgr
        iSupIndep := ?_
        iSup_eq := ?_
        finite := ?_
        smul_mem := ?_
        fg := ?_ }, ?_⟩
  · -- iSupIndep
    exact iSupIndep_map_of_ker_le π (gradedPieceS k d) hindepS hkerhom
  · -- iSup_eq
    rw [hMgr, ← Submodule.map_iSup, htopS, Submodule.map_top]
    rw [hπ]
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨a, rfl⟩
  · -- finite
    intro n
    have : Module.Finite k (gradedPieceS k d n) := hSnfin n
    exact Module.Finite.map (gradedPieceS k d n) π
  · -- smul_mem
    intro i n x hx
    rw [hMgr] at hx ⊢
    rw [Submodule.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [Submodule.mem_map]
    refine ⟨(MvPolynomial.X i : MvPolynomial (Fin d) k) • a, ?_, ?_⟩
    · -- X i • a ∈ S_{n+1}
      rw [gradedPieceS, MvPolynomial.mem_homogeneousSubmodule] at ha ⊢
      rw [smul_eq_mul]
      have hXi : (MvPolynomial.X i : MvPolynomial (Fin d) k).IsHomogeneous 1 :=
        MvPolynomial.isHomogeneous_X k i
      have := hXi.mul ha
      rwa [add_comm 1 n] at this
    · exact (hsmul (MvPolynomial.X i) a).symm
  · -- fg
    exact Module.Finite.of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
  · -- hilb identity
    intro n
    show (Module.finrank k ((gradedPieceS k d n).map π) : ℤ) = (hilbertFunction I n : ℤ)
    have : Module.Finite k (gradedPieceS k d n) := hSnfin n
    have hkereq : (LinearMap.ker π).comap (gradedPieceS k d n).subtype =
        (gradedPieceI I n).comap (gradedPieceS k d n).subtype := by
      ext y
      rw [hkerπ, gradedPieceI, Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_inf]
      exact ⟨fun h => ⟨h, y.property⟩, fun h => h.1⟩
    have hcomap_rank :
      Module.finrank k ((gradedPieceI I n).comap (gradedPieceS k d n).subtype) =
        Module.finrank k (gradedPieceI I n) :=
      LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_right)
    have hrn := finrank_map_add_finrank_comap_ker π (gradedPieceS k d n)
    rw [hkereq, hcomap_rank] at hrn
    -- hilbertFunction I n = finrank S_n - finrank I_n
    rw [hilbertFunction]
    omega

/-- The first difference of the Hilbert function of `S/I` is a `ℕ`-indexed
numerical polynomial. -/
theorem isNumericalPolynomialByNaturalArgs_hilbertFunction_sub
    (I : Ideal (MvPolynomial (Fin d) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) k) I) :
    IsNumericalPolynomialByNaturalArgs
      (fun n : ℕ => (hilbertFunction I n : ℤ) - (hilbertFunction I (n - 1) : ℤ)) := by
  -- Realize `hilbertFunction I` as the Hilbert function of an admissible graded module.
  obtain ⟨A, hA⟩ := exists_admissible_of_ideal I hI_hom
  -- `hilbertFunction I` is a numerical polynomial by the generalized induction.
  have hHil : IsNumericalPolynomialByNaturalArgs (fun n : ℕ => (hilbertFunction I n : ℤ)) :=
    (isNumericalPolynomialByNaturalArgs_hilb d A).congr
      (Filter.Eventually.of_forall fun n => (hA n).symm)
  simpa using hHil.sub hHil.comp_sub_one

/-- The Hilbert function of `S ⧸ I` for a homogeneous ideal `I`, as a function of a natural
number argument, is a numerical polynomial. -/
theorem isNumericalPolynomialByNaturalArgs_hilbertFunction (I : Ideal (MvPolynomial (Fin d) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) k) I) :
    IsNumericalPolynomialByNaturalArgs (fun n : ℕ => (hilbertFunction I n : ℤ)) := by
  -- Reduce to the first-difference fact via the antidifference closure
  -- `numerical_polynomial_of_difference` (Stacks Tag 00JZ).
  exact
    numerical_polynomial_of_difference (fun n : ℕ => (hilbertFunction I n : ℤ))
      (isNumericalPolynomialByNaturalArgs_hilbertFunction_sub I hI_hom)

/-- The Hilbert function of `S ⧸ I`, extended by `0` to negative degrees, is a numerical
polynomial in the sense of tag 00JX. -/
theorem isNumericalPolynomial_hilbertFunction (I : Ideal (MvPolynomial (Fin d) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) k) I) :
    IsNumericalPolynomial
      (fun n : ℤ => (if 0 ≤ n then (hilbertFunction I n.toNat : ℤ) else 0)) :=
  (isNumericalPolynomialByNaturalArgs_hilbertFunction I hI_hom).isNumericalPolynomial_extend

/-! ## Main results

(Stacks Lemma 10.58.10, Tag 00K3.) -/

/-- **Main Theorem (Stacks Lemma 10.58.10, Tag 00K3).**
Let `k` be a field, `d ≥ 1`, and `S = k[X_1, …, X_d]` with the standard grading.
Let `I ⊆ S` be a *nonzero* graded ideal and set `M = S / I`. Then the Hilbert
function `H_M(n) = dim_k(M_n)` is, for large `n`, given by a rational polynomial
`P` whose degree is strictly less than `d - 1`.

Concretely: there exist `P ∈ ℚ[T]` with `deg P < d - 1` and an integer `N` such
that `dim_k(M_n) = P(n)` for all `n ≥ N`. The degree bound `deg P < d - 1` is
expressed using `Polynomial.degree : ℚ[X] → WithBot ℕ`, which sends the zero
polynomial to `⊥`; thus `deg P < d - 1` automatically allows `P = 0` (the case
`-∞ < d - 1`), and when `d = 1` it forces `P = 0`. -/
@[stacks 00K3]
theorem hilbertFunction_degree_lt (hd : 1 ≤ d) (I : Ideal (MvPolynomial (Fin d) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin d) k) I)
    (hI_ne : I ≠ ⊥) :
    ∃ (P : Polynomial ℚ) (N : ℕ),
      P.degree < ((d - 1 : ℕ) : WithBot ℕ) ∧
        ∀ n : ℕ, N ≤ n → (hilbertFunction I n : ℚ) = P.eval (n : ℚ) := by
  -- PROOF SKETCH (assembles the decomposition lemmas above). Let
  --   f : ℤ → ℤ := fun n => if 0 ≤ n then (hilbertFunction I n.toNat : ℤ) else 0
  -- the extended Hilbert function.
  classical
  set f : ℤ → ℤ := fun n => if 0 ≤ n then (hilbertFunction I n.toNat : ℤ) else 0 with hf_def
  -- (1) `f` is a numerical polynomial — the background fact (Tags 00K1/00K2).
  have hf_num : IsNumericalPolynomial f := isNumericalPolynomial_hilbertFunction I hI_hom
  -- (2) `f` is eventually nonnegative (it is a cast of a ℕ-valued function for n ≥ 0).
  have hf_nonneg : ∀ᶠ n : ℤ in Filter.atTop, 0 ≤ f n := by
    -- For `n ≥ 0`, `f n = (hilbertFunction I n.toNat : ℤ) ≥ 0`.
    rw [Filter.eventually_atTop]
    refine ⟨0, fun n hn => ?_⟩
    simp only [hf_def]
    rw [ite_eq_left hn]
    exact Int.natCast_nonneg _
  -- (3) Upper bound by the binomial difference. From `hilbertFunction_le_choose_diff`
  --     get `e` and the bound `H_M(n) ≤ (n+d-1).choose n - (n-e+d-1).choose (n-e)`.
  obtain ⟨e, he_bound⟩ := hilbertFunction_le_choose_diff I hI_hom hI_ne
  -- (4) The binomial difference is (eventually) a polynomial `Q` of degree `< d-1`
  --     (valid for any `e ≥ 0`; for `e = 0` it is the zero polynomial).
  obtain ⟨Q, hQ_deg, hQ_eval⟩ := exists_polynomial_choose_diff (d := d) e hd
  -- Relate the `choose n` / `choose (d-1)` forms: for `n ≥ e`, `d ≥ 1`,
  --   `(n+d-1).choose n = (n+d-1).choose (d-1)` and likewise for `n-e`, so the
  -- ℕ bound from (3) matches `Q.eval n` in ℚ.
  have hle : ∀ᶠ n : ℤ in Filter.atTop, (f n : ℚ) ≤ Q.eval (n : ℚ) := by
    -- For large `n ≥ e`: `f n = (hilbertFunction I n.toNat : ℤ)`, cast to ℚ;
    -- chain `he_bound`, the `choose`-form identity, and `hQ_eval`. Truncated ℕ
    -- subtraction `≤` the ℚ subtraction since the subtrahend `(n-e+d-1).choose(d-1)`
    -- is `≤` the minuend `(n+d-1).choose(d-1)` for `n ≥ e`.
    rw [Filter.eventually_atTop]
    refine ⟨(e : ℤ), fun n hn => ?_⟩
    have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg e) hn
    -- set m := n.toNat
    set m : ℕ := n.toNat with hm
    have hmn : (m : ℤ) = n := Int.toNat_of_nonneg hn0
    have hem : e ≤ m := by
      have : (e : ℤ) ≤ (m : ℤ) := by
        rw [hmn]; exact hn
      exact_mod_cast this
    -- f n = (hilbertFunction I m : ℤ)
    have hfn : f n = (hilbertFunction I m : ℤ) := by
      simp only [hf_def]; rw [ite_eq_left hn0]
    rw [hfn]
    -- rewrite (n : ℚ) = (m : ℚ)
    have hnq : (n : ℚ) = (m : ℚ) := by
      rw [← hmn]; push_cast; ring
    rw [hnq, ← hQ_eval m hem]
    -- Now goal: ((hilbertFunction I m : ℤ) : ℚ) ≤ ((m+d-1).choose (d-1):ℚ) - ((m-e+d-1).choose
    -- (d-1):ℚ)
    push_cast
    -- choose-form identities
    have hsub1 : (m + d - 1) - m = d - 1 := by omega
    have hc1 : (m + d - 1).choose m = (m + d - 1).choose (d - 1) := by
      rw [← hsub1, Nat.choose_symm (by omega)]
    have hsub2 : (m - e + d - 1) - (m - e) = d - 1 := by omega
    have hc2 : (m - e + d - 1).choose (m - e) = (m - e + d - 1).choose (d - 1) := by
      rw [← hsub2, Nat.choose_symm (by omega)] -- monotonicity: subtrahend ≤ minuend
    have hmono : (m - e + d - 1).choose (d - 1) ≤ (m + d - 1).choose (d - 1) :=
      Nat.choose_le_choose (d - 1) (by omega)
    have hbound := he_bound m hem
    rw [hc1, hc2] at hbound
    -- cast the ℕ bound to ℚ
    have :
      (hilbertFunction I m : ℚ) ≤
        ((m + d - 1).choose (d - 1) : ℚ) - ((m - e + d - 1).choose (d - 1) : ℚ) := by
      have h2 :
        ((((m + d - 1).choose (d - 1)) - ((m - e + d - 1).choose (d - 1)) : ℕ) : ℚ) =
          ((m + d - 1).choose (d - 1) : ℚ) - ((m - e + d - 1).choose (d - 1) : ℚ) := by
        rw [Nat.cast_sub hmono]
      rw [← h2]
      exact_mod_cast hbound
    convert this using 2
  -- (5) Conclude via the degree-comparison lemma: a nonnegative numerical polynomial
  --     bounded above by a degree-`<d-1` polynomial is itself degree `< d-1`.
  obtain ⟨P, N, hP_deg, hP_eval⟩ :=
    isNumericalPolynomial_degree_lt_of_le (d := d) f hf_num hf_nonneg Q hQ_deg hle
  -- Transport `hP_eval` (about `f`) back to `hilbertFunction I n` for `n ≥ N`,
  -- using `f n = (hilbertFunction I n.toNat)` and `(↑n).toNat = n` for `n : ℕ`.
  refine ⟨P, N, hP_deg, fun n hn => ?_⟩
  have := hP_eval n hn
  -- `f (n:ℤ) = (hilbertFunction I n : ℤ)` since `(0:ℤ) ≤ n` and `(↑n).toNat = n`.
  simpa [hf_def, Int.toNat_natCast] using this


/-- **Main Theorem, special case `d = 1`.**
When `d = 1`, the Hilbert function of `S / I` for a nonzero graded ideal `I`
vanishes for all sufficiently large `n`. This is the special case `d = 1` of the
degree bound `deg P < d - 1 = 0`, where `deg P < 0` forces `P = 0`. -/
theorem hilbertFunction_eventually_zero_of_dim_one (I : Ideal (MvPolynomial (Fin 1) k))
    (hI_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 1) k) I)
    (hI_ne : I ≠ ⊥) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → hilbertFunction I n = 0 := by
  -- PROOF SKETCH. Apply the main theorem with `d = 1`: get `P : ℚ[X]` and `N` with
  -- `P.degree < ((1 - 1 : ℕ) : WithBot ℕ) = (0 : WithBot ℕ)` and
  -- `(hilbertFunction I n : ℚ) = P.eval n` for `n ≥ N`. `degree P < 0` (in
  -- `WithBot ℕ`, `(0 : WithBot ℕ)` is `↑(0:ℕ)`) forces `P = 0`
  -- (`Polynomial.degree_lt_zero_iff`-style: only `⊥ < 0`, and `degree = ⊥ ↔ P = 0`
  -- via `Polynomial.degree_eq_bot`). Hence `(hilbertFunction I n : ℚ) = 0` for
  -- `n ≥ N`, and since `hilbertFunction I n : ℕ`, the cast being `0` gives
  -- `hilbertFunction I n = 0` (`Nat.cast_eq_zero`).
  obtain ⟨P, N, hP_deg, hP_eval⟩ :=
    hilbertFunction_degree_lt (k := k) (d := 1) le_rfl I hI_hom hI_ne
  refine ⟨N, fun n hn => ?_⟩
  have hP0 : P = 0 := by
    -- `((1 - 1 : ℕ) : WithBot ℕ) = (0 : WithBot ℕ)`; `P.degree < 0` ⟹ `P.degree = ⊥`
    -- ⟹ `P = 0`.
    have hlt : P.degree < (0 : WithBot ℕ) := by simpa using hP_deg
    exact Polynomial.degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hlt)
  exact_mod_cast (by rw [hP_eval n hn, hP0, Polynomial.eval_zero] : (hilbertFunction I n : ℚ) = 0)

end Stacks.HilbertFunction.PolynomialQuotient
