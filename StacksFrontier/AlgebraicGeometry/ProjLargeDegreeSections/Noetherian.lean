module

public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.SaturationBound
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegreeSections.SectionFractions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison `M_n ⟶ Γ(Proj 𝒮, M(n)~)` for a finite graded module

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring whose degree-zero part is Noetherian and which is
generated over it by finitely many elements `f 0, …, f (r-1)` of `𝒮 1`, let `M = ⨁_{n ∈ ℤ} 𝒨 n`
be a finite graded `S`-module and `X = Proj 𝒮`. The canonical maps

`𝒨 n ⟶ Γ(X, M(n)~)`

of Equation 01MR are isomorphisms for all sufficiently large `n`.

## Main definitions

* `tailAnnihilator`: the submodule of elements annihilated by `f i` for every `i ≥ k`.

## Main results

* `exists_forall_injective_degreeNToGlobalSections`: the comparison is injective in all large
  degrees.
* `exists_forall_surjective_of_tailAnnihilated`: in all large degrees, every section of `M(n)~`
  annihilated by `f i` for every `i ≥ k` comes from a homogeneous element of degree `n`.
* `exists_bijective_degreeNToGlobalSections_of_finite`: the comparison is bijective in all large
  degrees.

## References

* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent degreeNToGlobalSections homogeneousScalarGlobalSections
    degreeNToGlobalSections_homogeneousScalar)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegreeSections

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- The submodule of elements annihilated by `fam i` for every index `i` at or above `k`. -/
@[ega "0 16.2.3.1" "more general"]
def tailAnnihilator {r : ℕ} (fam : Fin r → S) (k : ℕ) : Submodule S M where
  carrier := {m : M | ∀ i : Fin r, k ≤ (i : ℕ) → fam i • m = 0}
  add_mem' {x y} hx hy i hi := by
    change fam i • (x + y) = 0
    rw [smul_add, hx i hi, hy i hi, add_zero]
  zero_mem' i _ := smul_zero _
  smul_mem' c x hx i hi := by
    change fam i • (c • x) = 0
    rw [smul_comm, hx i hi, smul_zero]

/-- Membership in `tailAnnihilator` is annihilation by the tail of the family. -/
theorem mem_tailAnnihilator {r : ℕ} {fam : Fin r → S} {k : ℕ} {m : M} :
    m ∈ tailAnnihilator (M := M) fam k ↔ ∀ i : Fin r, k ≤ (i : ℕ) → fam i • m = 0 := Iff.rfl

/-- Transport a homogeneous element along an equality of degrees. -/
def ofDegreeEqMem {p q : ℤ} (h : p = q) (m : 𝒨 p) : 𝒨 q :=
  ⟨(m : M), by subst h; exact m.2⟩

omit [AddCommGroup M] [AddSubgroupClass τ M] [Decomposition 𝒨] in
/-- Transport along an equality of degrees does not change the underlying element. -/
theorem coe_ofDegreeEqMem {p q : ℤ} (h : p = q) (m : 𝒨 p) :
    (ofDegreeEqMem 𝒨 h m : M) = (m : M) := rfl

omit [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- The tail annihilator is a graded submodule. -/
theorem isHomogeneousSubmodule_tailAnnihilator {r : ℕ} (fam : Fin r → S)
    (hfam : ∀ i, fam i ∈ 𝒮 1) (k : ℕ) :
    IsHomogeneousSubmodule 𝒨 (tailAnnihilator (M := M) fam k) := by
  intro x hx d i hi
  have h := coe_decompose_smul_add_of_left_mem 𝒮 𝒨 (hfam i) x d
  rw [hx i hi] at h
  change fam i • (decompose 𝒨 x d : M) = 0
  rw [← h, decompose_zero]
  rfl

/-- The comparison `𝒨 n ⟶ Γ(Proj 𝒮, M(n)~)` is injective in all large degrees. -/
theorem exists_forall_injective_degreeNToGlobalSections [IsNoetherianRing S] [Module.Finite S M]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    {r : ℕ} (fam : Fin r → S) (hfam : ∀ i, fam i ∈ 𝒮 1)
    (hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → Function.Injective (degreeNToGlobalSections 𝒮 𝒨 n) := by
  have hbot : IsHomogeneousSubmodule 𝒨 (⊥ : Submodule S M) := by
    intro x hx d
    rw [(Submodule.mem_bot S).mp hx, decompose_zero]
    exact (Submodule.mem_bot S).mpr rfl
  obtain ⟨d₀, hd₀⟩ := exists_forall_mem_of_forall_pow_smul_mem 𝒮 𝒨 hgen fam hspan hbot
  refine ⟨d₀, fun n hn => ?_⟩
  rw [injective_iff_map_eq_zero]
  intro m hm
  refine Subtype.ext ?_
  rw [ZeroMemClass.coe_zero]
  refine (Submodule.mem_bot S).mp (hd₀ n hn (m : M) m.2 fun i => ?_)
  have h := coe_frac_degreeNToGlobalSections 𝒮 𝒨 (hfam i) n m
  rw [hm, coe_fracDeg_zero] at h
  obtain ⟨k, hk⟩ := (mk_eq_zero_iff_exists_pow_smul (f := fam i) (m : M) _).mp h.symm
  exact ⟨k, by rw [hk]; exact Submodule.zero_mem _⟩

/-- A section of `M(n)~` annihilated by `fam i` for every `i ≥ k` comes from a homogeneous element
of degree `n`, once `n` is large. -/
theorem exists_forall_surjective_of_tailAnnihilated [IsNoetherianRing S] [Module.Finite S M]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    {r : ℕ} (fam : Fin r → S) (hfam : ∀ i, fam i ∈ 𝒮 1)
    (hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal) (k : ℕ) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ s : shiftedSectionsComponent 𝒮 𝒨 n,
      (∀ i : Fin r, k ≤ (i : ℕ) →
        homogeneousScalarGlobalSections 𝒮 𝒨 1 n ⟨fam i, hfam i⟩ s = 0) →
      ∃ m : 𝒨 n, s = degreeNToGlobalSections 𝒮 𝒨 n m := by
  induction k with
  | zero =>
      refine ⟨0, fun n _ s hs => ⟨0, ?_⟩⟩
      rw [map_zero]
      exact eq_zero_of_forall_coe_frac_eq_zero 𝒮 𝒨 fam hfam hspan n s fun i =>
        coe_frac_eq_zero_of_smul_self_eq_zero 𝒮 𝒨 (hfam i) n s (hs i (Nat.zero_le _))
  | succ k ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      by_cases hk : k < r
      swap
      · refine ⟨n₁, fun n hn s hs => hn₁ n hn s fun i hi => ?_⟩
        have := i.2
        omega
      set g := fam ⟨k, hk⟩ with hgdef
      have hg : g ∈ 𝒮 1 := hfam ⟨k, hk⟩
      have powSMul_mem : ∀ (l b : ℕ) (n : ℤ) {w : M}, w ∈ 𝒨 ((b : ℤ) + n) →
          (powDegOne 𝒮 hg l : S) • w ∈ 𝒨 ((b : ℤ) + ((l : ℤ) + n)) := by
        intro l b n w hw
        have h := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) (powDegOne 𝒮 hg l).2 hw
        have hd : l +ᵥ ((b : ℤ) + n) = (b : ℤ) + ((l : ℤ) + n) := by
          change (l : ℤ) + ((b : ℤ) + n) = (b : ℤ) + ((l : ℤ) + n)
          ring
        rwa [hd] at h
      have hP : IsHomogeneousSubmodule 𝒨 (tailAnnihilator (M := M) fam (k + 1)) :=
        isHomogeneousSubmodule_tailAnnihilator 𝒮 𝒨 fam hfam (k + 1)
      have hN : IsHomogeneousSubmodule 𝒨
          ((tailAnnihilator (M := M) fam (k + 1)).map (LinearMap.lsmul S M g)) :=
        isHomogeneousSubmodule_map_lsmul 𝒮 𝒨 hg hP
      obtain ⟨d₂, hd₂⟩ := exists_forall_mem_of_forall_pow_smul_mem 𝒮 𝒨 hgen fam hspan hN
      have onestep : ∀ n' : ℤ, max n₁ d₂ ≤ n' → ∀ u : shiftedSectionsComponent 𝒮 𝒨 n',
          (∀ i : Fin r, k + 1 ≤ (i : ℕ) →
            homogeneousScalarGlobalSections 𝒮 𝒨 1 n' ⟨fam i, hfam i⟩ u = 0) →
          ∀ q : 𝒨 (((1 : ℕ) : ℤ) + n'),
            homogeneousScalarGlobalSections 𝒮 𝒨 1 n' ⟨g, hg⟩ u =
              degreeNToGlobalSections 𝒮 𝒨 (((1 : ℕ) : ℤ) + n') q →
          ∃ m : 𝒨 n', u = degreeNToGlobalSections 𝒮 𝒨 n' m := by
        intro n' hn' u hu q hq
        have hqN : ∀ i : Fin r, ∃ c : ℕ, fam i ^ c • (q : M) ∈
            (tailAnnihilator (M := M) fam (k + 1)).map (LinearMap.lsmul S M g) := by
          intro i
          obtain ⟨a, p, hp, hpP, hfr⟩ := exists_mk_coe_frac_smul_eq_zero 𝒮 𝒨 (hfam i) n' u
            (fun j : {j : Fin r // k + 1 ≤ (j : ℕ)} => fam j.1)
            (fun j => hfam j.1) (fun j => hu j.1 j.2)
          have hpmem : p ∈ tailAnnihilator (M := M) fam (k + 1) := fun j hj => hpP ⟨j, hj⟩
          have h1 := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n' 1 ⟨g, hg⟩ u hp hfr
          rw [hq, coe_frac_degreeNToGlobalSections] at h1
          obtain ⟨c, hc⟩ := (LocalizedModule.mk_eq).mp h1
          obtain ⟨e, he⟩ := c.2
          refine ⟨e + a, ⟨fam i ^ e • p, Submodule.smul_mem _ _ hpmem, ?_⟩⟩
          change g • (fam i ^ e • p) = fam i ^ (e + a) • (q : M)
          simp only [Submonoid.smul_def, pow_zero, one_smul] at hc
          rw [← he] at hc
          have hce : fam i ^ e • (fam i ^ a • (q : M)) = fam i ^ e • (g • p) := hc
          rw [pow_add, mul_smul, hce]
          exact (smul_comm (fam i ^ e) g p).symm
        have hqmem : (q : M) ∈
            (tailAnnihilator (M := M) fam (k + 1)).map (LinearMap.lsmul S M g) := by
          refine hd₂ (((1 : ℕ) : ℤ) + n') ?_ (q : M) q.2 hqN
          have := le_max_right n₁ d₂
          omega
        obtain ⟨p, hpP, hpq⟩ := hqmem
        have hp'P : (decompose 𝒨 p n' : M) ∈ tailAnnihilator (M := M) fam (k + 1) :=
          hP p hpP n'
        have hgp' : g • (decompose 𝒨 p n' : M) = (q : M) := by
          have h := coe_decompose_smul_add_of_left_mem 𝒮 𝒨 hg p n'
          change g • (decompose 𝒨 p n' : M) = (q : M)
          rw [← h]
          change (decompose 𝒨 ((LinearMap.lsmul S M g) p) (((1 : ℕ) : ℤ) + n') : M) = (q : M)
          rw [hpq, decompose_of_mem_same 𝒨 q.2]
        have hv : homogeneousScalarGlobalSections 𝒮 𝒨 1 n' ⟨g, hg⟩
            (u - degreeNToGlobalSections 𝒮 𝒨 n' ⟨(decompose 𝒨 p n' : M), (decompose 𝒨 p n').2⟩)
              = 0 := by
          rw [homogeneousScalarGlobalSections_sub, hq, degreeNToGlobalSections_homogeneousScalar,
            sub_eq_zero]
          exact congrArg _ (Subtype.ext hgp'.symm)
        have hvtail : ∀ i : Fin r, k ≤ (i : ℕ) →
            homogeneousScalarGlobalSections 𝒮 𝒨 1 n' ⟨fam i, hfam i⟩
              (u - degreeNToGlobalSections 𝒮 𝒨 n'
                ⟨(decompose 𝒨 p n' : M), (decompose 𝒨 p n').2⟩) = 0 := by
          intro i hi
          rcases Nat.lt_or_ge (i : ℕ) (k + 1) with hik | hik
          · have hieq : i = ⟨k, hk⟩ := Fin.ext (show (i : ℕ) = k by omega)
            subst hieq
            exact hv
          · rw [homogeneousScalarGlobalSections_sub, hu i hik,
              degreeNToGlobalSections_homogeneousScalar, zero_sub, neg_eq_zero]
            exact Eq.trans (congrArg (degreeNToGlobalSections 𝒮 𝒨 (((1 : ℕ) : ℤ) + n'))
              (Subtype.ext (hp'P i hik))) (map_zero _)
        obtain ⟨m, hm⟩ := hn₁ n' (le_trans (le_max_left n₁ d₂) hn') _ hvtail
        refine ⟨m + ⟨(decompose 𝒨 p n' : M), (decompose 𝒨 p n').2⟩, ?_⟩
        rw [map_add, ← hm]
        abel
      have descent : ∀ j : ℕ, ∀ n' : ℤ, max n₁ d₂ ≤ n' →
          ∀ u : shiftedSectionsComponent 𝒮 𝒨 n',
          (∀ i : Fin r, k + 1 ≤ (i : ℕ) →
            homogeneousScalarGlobalSections 𝒮 𝒨 1 n' ⟨fam i, hfam i⟩ u = 0) →
          ∀ q : 𝒨 ((j : ℤ) + n'),
            homogeneousScalarGlobalSections 𝒮 𝒨 j n' (powDegOne 𝒮 hg j) u =
              degreeNToGlobalSections 𝒮 𝒨 ((j : ℤ) + n') q →
          ∃ m : 𝒨 n', u = degreeNToGlobalSections 𝒮 𝒨 n' m := by
        intro j
        induction j with
        | zero =>
            intro n' _ u _ q hq
            have hdeg : ((0 : ℕ) : ℤ) + n' = n' := by push_cast; ring
            refine ⟨ofDegreeEqMem 𝒨 hdeg q, ?_⟩
            refine eq_of_forall_coe_frac_eq 𝒮 𝒨 fam hfam hspan n' u _ fun i => ?_
            obtain ⟨a, w, hw, hfr⟩ := exists_mk_coe_frac 𝒮 𝒨 (hfam i) n' u
            have h1 := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n' 0
              (powDegOne 𝒮 hg 0) u hw hfr
            rw [hq, coe_frac_degreeNToGlobalSections] at h1
            rw [show (powDegOne 𝒮 hg 0 : S) • w = w by simp [powDegOne]] at h1
            rw [hfr, coe_frac_degreeNToGlobalSections]
            exact h1.symm
        | succ j ihj =>
            intro n' hn' u hu q hq
            have hjn : max n₁ d₂ ≤ (j : ℤ) + n' := by
              have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
              omega
            have hu' : ∀ i : Fin r, k + 1 ≤ (i : ℕ) →
                homogeneousScalarGlobalSections 𝒮 𝒨 1 ((j : ℤ) + n') ⟨fam i, hfam i⟩
                  (homogeneousScalarGlobalSections 𝒮 𝒨 j n' (powDegOne 𝒮 hg j) u) = 0 :=
              fun i hi => homogeneousScalarGlobalSections_smul_eq_zero 𝒮 𝒨 fam hfam hspan n' u
                (hfam i) (hu i hi) j (powDegOne 𝒮 hg j)
            have hdeg : ((j + 1 : ℕ) : ℤ) + n' = ((1 : ℕ) : ℤ) + ((j : ℤ) + n') := by
              push_cast; ring
            have hq' : homogeneousScalarGlobalSections 𝒮 𝒨 1 ((j : ℤ) + n') ⟨g, hg⟩
                (homogeneousScalarGlobalSections 𝒮 𝒨 j n' (powDegOne 𝒮 hg j) u) =
                degreeNToGlobalSections 𝒮 𝒨 (((1 : ℕ) : ℤ) + ((j : ℤ) + n'))
                  (ofDegreeEqMem 𝒨 hdeg q) := by
              refine eq_of_forall_coe_frac_eq 𝒮 𝒨 fam hfam hspan _ _ _ fun i => ?_
              obtain ⟨a, w, hw, hfr⟩ := exists_mk_coe_frac 𝒮 𝒨 (hfam i) n' u
              have hu'frac := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n' j
                (powDegOne 𝒮 hg j) u hw hfr
              have hwj := powSMul_mem j a n' hw
              have h1 := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) ((j : ℤ) + n') 1
                ⟨g, hg⟩ _ hwj hu'frac
              have h2 := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n' (j + 1)
                (powDegOne 𝒮 hg (j + 1)) u hw hfr
              rw [hq, coe_frac_degreeNToGlobalSections] at h2
              rw [h1, coe_frac_degreeNToGlobalSections]
              change LocalizedModule.mk (g • (g ^ j • w)) _ = _
              rw [← mul_smul, ← pow_succ']
              exact h2.symm
            obtain ⟨m', hm'⟩ := onestep ((j : ℤ) + n') hjn _ hu' _ hq'
            exact ihj n' hn' u hu m' hm'
      refine ⟨max n₁ d₂, fun n hn s hs => ?_⟩
      obtain ⟨a, p, hp, hpP, hfr⟩ := exists_mk_coe_frac_smul_eq_zero 𝒮 𝒨 hg n s
        (fun j : {j : Fin r // k + 1 ≤ (j : ℕ)} => fam j.1)
        (fun j => hfam j.1) (fun j => hs j.1 (by have := j.2; omega))
      have hfracgt : (frac 𝒮 𝒨 hg ((a : ℤ) + n)
          (homogeneousScalarGlobalSections 𝒮 𝒨 a n (powDegOne 𝒮 hg a) s -
            degreeNToGlobalSections 𝒮 𝒨 ((a : ℤ) + n) ⟨p, hp⟩) :
            LocalizedModule.Away g M) = 0 := by
        rw [coe_fracDeg_sub,
          coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 hg n a (powDegOne 𝒮 hg a) s hp hfr,
          coe_frac_degreeNToGlobalSections, sub_eq_zero]
        refine (LocalizedModule.mk_eq).mpr ⟨1, ?_⟩
        simp only [Submonoid.smul_def, one_smul, pow_zero]
        change (powDegOne 𝒮 hg a : S) • p = g ^ a • p
        rfl
      obtain ⟨l, hl⟩ := exists_pow_smul_eq_zero_of_coe_frac_eq_zero 𝒮 𝒨 fam hfam hspan hg
        ((a : ℤ) + n) _ hfracgt
      rw [homogeneousScalarGlobalSections_sub, degreeNToGlobalSections_homogeneousScalar,
        sub_eq_zero] at hl
      have hdeg2 : ((l + a : ℕ) : ℤ) + n = (l : ℤ) + ((a : ℤ) + n) := by push_cast; ring
      have hqfin : homogeneousScalarGlobalSections 𝒮 𝒨 (l + a) n (powDegOne 𝒮 hg (l + a)) s =
          degreeNToGlobalSections 𝒮 𝒨 (((l + a : ℕ) : ℤ) + n)
            (ofDegreeEqMem 𝒨 hdeg2.symm
              ⟨(powDegOne 𝒮 hg l : S) • p, SetLike.GradedSMul.smul_mem
                (A := 𝒮) (B := 𝒨) (powDegOne 𝒮 hg l).2 hp⟩) := by
        refine eq_of_forall_coe_frac_eq 𝒮 𝒨 fam hfam hspan _ _ _ fun i => ?_
        obtain ⟨b, w, hw, hfrw⟩ := exists_mk_coe_frac 𝒮 𝒨 (hfam i) n s
        have hA := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n (l + a)
          (powDegOne 𝒮 hg (l + a)) s hw hfrw
        have hB := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) n a
          (powDegOne 𝒮 hg a) s hw hfrw
        have hwa := powSMul_mem a b n hw
        have hC := coe_frac_homogeneousScalarGlobalSections 𝒮 𝒨 (hfam i) ((a : ℤ) + n) l
          (powDegOne 𝒮 hg l) _ hwa hB
        rw [hl, coe_frac_degreeNToGlobalSections] at hC
        rw [hA, coe_frac_degreeNToGlobalSections]
        change LocalizedModule.mk (g ^ (l + a) • w) _ = _
        rw [pow_add, mul_smul]
        exact hC.symm
      exact descent (l + a) n hn s hs _ hqfin

/-- Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring whose degree-zero part is Noetherian and which is
generated over that part by finitely many elements `fam 0, …` of `𝒮 1`, let `M = ⨁_{n ∈ ℤ} 𝒨 n`
be a finite graded `S`-module and `X = Proj 𝒮`. The canonical maps

`𝒨 n ⟶ Γ(X, M(n)~)`

of Equation 01MR are isomorphisms for all sufficiently large `n`. -/
@[stacks 0AG7 "the maps M_n to Gamma(Proj A, M(n)~) of Equation 01MR are isomorphisms in all \
sufficiently large degrees, for A_0 Noetherian, A generated over A_0 by finitely many elements \
of A_1, and M a finite graded A-module"]
theorem exists_bijective_degreeNToGlobalSections_of_finite [IsNoetherianRing ↥(𝒮 0)]
    [Module.Finite S M] {r : ℕ} (fam : Fin r → S) (hfam : ∀ i, fam i ∈ 𝒮 1)
    (hgen : Algebra.adjoin ↥(𝒮 0) (Set.range fam) = ⊤) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → Function.Bijective (degreeNToGlobalSections 𝒮 𝒨 n) := by
  classical
  have hft : Algebra.FiniteType ↥(𝒮 0) S := ⟨⟨Finset.image fam Finset.univ, by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hgen⟩⟩
  have hnoeth : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ↥(𝒮 0) S
  have hsub : Set.range fam ⊆ (𝒮 1 : Set S) := by
    rintro x ⟨i, rfl⟩
    exact hfam i
  have hgen1 : Algebra.adjoin ↥(𝒮 0) ((𝒮 1 : Set S)) = ⊤ :=
    le_antisymm le_top (by rw [← hgen]; exact Algebra.adjoin_mono hsub)
  have hspan : Ideal.span (Set.range fam) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal :=
    (generates_algebra_iff_generates_irrelevant 𝒮 fam (fun _ => 1)
      (fun _ => Nat.one_pos) hfam).mp hgen
  obtain ⟨n₂, hn₂⟩ :=
    exists_forall_injective_degreeNToGlobalSections 𝒮 𝒨 hgen1 fam hfam hspan
  obtain ⟨n₃, hn₃⟩ :=
    exists_forall_surjective_of_tailAnnihilated 𝒮 𝒨 hgen1 fam hfam hspan r
  refine ⟨max n₂ n₃, fun n hn => ⟨hn₂ n (le_trans (le_max_left n₂ n₃) hn), fun s => ?_⟩⟩
  obtain ⟨m, hm⟩ := hn₃ n (le_trans (le_max_right n₂ n₃) hn) s fun i hi => by
    have := i.2
    omega
  exact ⟨m, hm.symm⟩

end Stacks.AlgebraicGeometry.ProjLargeDegreeSections

end
