module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Homology of the complex of ideal-power multiples (tag 0G3K)

For a complex `K → L → M` of finite modules over a Noetherian ring, the homology of the complex
of multiples `I ^ n K → I ^ n L → I ^ n M` is pro-isomorphic to the system `I ^ n H` with a
uniform shift: `Stacks.AdicSystem.Homology.homologyIdealPowers_proIsomorphic`.
-/

/-! ## Tag 0G3K -/

section

namespace Stacks.AdicSystem.Homology

universe u v w x

private abbrev cycles {A : Type u} [CommRing A]
    {L : Type w} {M : Type x} [AddCommGroup L] [AddCommGroup M]
    [Module A L] [Module A M] (I : Ideal A) (β : L →ₗ[A] M) (n : ℕ) :
    Submodule A L := LinearMap.ker β ⊓ (I ^ n • (⊤ : Submodule A L))

private abbrev boundaries {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) :
    Submodule A (cycles I β n) :=
  Submodule.comap (cycles I β n).subtype
    (Submodule.map α (I ^ n • (⊤ : Submodule A K)))

private abbrev homology {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) : Type _ :=
  (cycles I β n) ⧸ boundaries I α β n

private lemma cycles_mono {A : Type u} [CommRing A]
    {L : Type w} {M : Type x} [AddCommGroup L] [AddCommGroup M]
    [Module A L] [Module A M] (I : Ideal A) (β : L →ₗ[A] M)
    {m n : ℕ} (h : n ≤ m) : cycles I β m ≤ cycles I β n :=
  inf_le_inf le_rfl (Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl)

private def transition {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (m n : ℕ) (h : n ≤ m) : homology I α β m →ₗ[A] homology I α β n :=
  (boundaries I α β m).mapQ (boundaries I α β n)
    (Submodule.inclusion (cycles_mono I β h)) (by
      rintro y hy
      change (y : L) ∈ Submodule.map α (I ^ m • (⊤ : Submodule A K)) at hy
      change (y : L) ∈ Submodule.map α (I ^ n • (⊤ : Submodule A K))
      exact (Submodule.map_mono (Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl)) hy)

private lemma transition_mk {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (m n : ℕ) (h : n ≤ m) (y : cycles I β m) :
    transition I α β m n h (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨y, cycles_mono I β h y.2⟩ : cycles I β n) := by
  apply Submodule.mapQ_apply

private lemma transition_id {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) :
    transition I α β n n (le_refl n) = LinearMap.id := by
  apply Submodule.linearMap_qext
  ext y
  simp [transition_mk]

private lemma transition_comp {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m) :
    (transition I α β m n hmn).comp (transition I α β k m hkm) =
      transition I α β k n (hmn.trans hkm) := by
  apply Submodule.linearMap_qext
  ext y
  simp [transition_mk]

private lemma transition_transition {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m) (z : homology I α β k) :
    transition I α β m n hmn (transition I α β k m hkm z) =
      transition I α β k n (hmn.trans hkm) z := by
  rw [← LinearMap.comp_apply, transition_comp]

private lemma transition_mk_restrict {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (k m n : ℕ) (hmk : m ≤ k) (hnm : n ≤ m) (y : cycles I β k) :
    transition I α β m n hnm
        (Submodule.Quotient.mk (⟨y, cycles_mono I β hmk y.2⟩ : cycles I β m)) =
      transition I α β k n (hnm.trans hmk) (Submodule.Quotient.mk y) := by
  rw [← transition_mk I α β k m hmk y, transition_transition]

private lemma artinRees_le {A : Type u} [CommRing A] [IsNoetherianRing A]
    {L : Type w} [AddCommGroup L] [Module A L] [Module.Finite A L]
    (I : Ideal A) (N : Submodule A L) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ n →
      N ⊓ (I ^ n • (⊤ : Submodule A L)) ≤ I ^ (n - c) • N := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  refine ⟨k + 1, by omega, fun n hn => ?_⟩
  rw [inf_comm, hk n (by omega)]
  exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) inf_le_right

/-- Pushing `I ^ n • ⊤` in the cycles through the inclusion gives `I ^ n • ker β`. -/
private lemma map_subtype_cycles_smul_top {A : Type u} [CommRing A]
    {L : Type w} {M : Type x} [AddCommGroup L] [AddCommGroup M]
    [Module A L] [Module A M] (I : Ideal A) (β : L →ₗ[A] M) (n : ℕ) :
    Submodule.map (cycles I β 0).subtype (I ^ n • (⊤ : Submodule A (cycles I β 0))) =
      I ^ n • LinearMap.ker β := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  simp [cycles]

/-- An element of `I ^ n • ⊤` in the zero-th cycles lies in `I ^ n • ker β`. -/
private lemma coe_mem_smul_ker {A : Type u} [CommRing A]
    {L : Type w} {M : Type x} [AddCommGroup L] [AddCommGroup M]
    [Module A L] [Module A M] (I : Ideal A) (β : L →ₗ[A] M) (n : ℕ)
    {s : cycles I β 0} (hs : s ∈ I ^ n • (⊤ : Submodule A (cycles I β 0))) :
    (s : L) ∈ I ^ n • LinearMap.ker β :=
  (map_subtype_cycles_smul_top I β n).le (Submodule.mem_map_of_mem hs)

private lemma cycle0_mem_power {A : Type u} [CommRing A]
    {L : Type w} {M : Type x} [AddCommGroup L] [AddCommGroup M]
    [Module A L] [Module A M] (I : Ideal A) (β : L →ₗ[A] M)
    (n : ℕ) (y : L) (hyker : y ∈ LinearMap.ker β)
    (hy : y ∈ I ^ n • LinearMap.ker β) :
    (⟨y, hyker, by simp⟩ : cycles I β 0) ∈
      I ^ n • (⊤ : Submodule A (cycles I β 0)) := by
  obtain ⟨z, hz, hzy⟩ := (map_subtype_cycles_smul_top I β n).ge hy
  rwa [show (⟨y, hyker, by simp⟩ : cycles I β 0) = z from Subtype.ext hzy.symm]

/-- Passing to the quotient maps `I ^ n • ⊤` in the zero-th cycles into `I ^ n • ⊤`
in the zero-th homology. -/
private lemma mkQ_mem_smul_top {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) {x : cycles I β 0}
    (hx : x ∈ I ^ n • (⊤ : Submodule A (cycles I β 0))) :
    (boundaries I α β 0).mkQ x ∈ I ^ n • (⊤ : Submodule A (homology I α β 0)) := by
  rw [← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
    LinearMap.range_eq_map, ← Submodule.map_smul'']
  exact ⟨x, hx, rfl⟩

private def toPower {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (c n : ℕ) (_hn : c ≤ n)
    (hc : cycles I β n ≤ I ^ (n - c) • LinearMap.ker β) :
    homology I α β n →ₗ[A]
      ↥(I ^ (n - c) • (⊤ : Submodule A (homology I α β 0))) :=
  LinearMap.codRestrict _ (transition I α β n 0 (Nat.zero_le n)) (fun z => by
    induction z using Submodule.Quotient.induction_on with
    | _ y =>
      rw [transition_mk]
      exact mkQ_mem_smul_top I α β _ (cycle0_mem_power I β _ y.1 y.2.1 (hc y.2)))

private abbrev powerSource {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (_α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) :=
  I ^ n • (⊤ : Submodule A (cycles I β 0))

private def sourceToPower {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) :
    powerSource I α β n →ₗ[A]
      ↥(I ^ n • (⊤ : Submodule A (homology I α β 0))) :=
  LinearMap.codRestrict _ ((boundaries I α β 0).mkQ.domRestrict _)
    (fun z => mkQ_mem_smul_top I α β n z.2)

private lemma sourceToPower_surjective {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) :
    Function.Surjective (sourceToPower I α β n) := by
  intro z
  have hz := z.2
  have hmap : Submodule.map (boundaries I α β 0).mkQ
      (I ^ n • (⊤ : Submodule A (cycles I β 0))) =
      I ^ n • (⊤ : Submodule A (homology I α β 0)) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)]
  have hz' : z.1 ∈ Submodule.map (boundaries I α β 0).mkQ
      (I ^ n • (⊤ : Submodule A (cycles I β 0))) := by
    simpa only [hmap] using hz
  rcases hz' with ⟨y, hy, hyz⟩
  exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

private def sourceToLevelInclusion {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (c n : ℕ) :
    powerSource I α β n →ₗ[A] cycles I β (n - c) :=
  { toFun := fun z => ⟨z.1.1, z.1.2.1,
      Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.sub_le n c)) le_top
        (coe_mem_smul_ker I β n z.2)⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun (r : A) (z : powerSource I α β n) => by
      apply Subtype.ext
      simp only [Submodule.coe_smul, RingHom.id_apply] }

private def sourceToLevel {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (c n : ℕ) :
    powerSource I α β n →ₗ[A] homology I α β (n - c) :=
  (boundaries I α β (n - c)).mkQ.comp (sourceToLevelInclusion I α β c n)

private lemma source_kernel_le {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (c n : ℕ)
    (hb : LinearMap.range α ⊓ (I ^ n • (⊤ : Submodule A L)) ≤
      I ^ (n - c) • LinearMap.range α) :
    LinearMap.ker (sourceToPower I α β n) ≤
      LinearMap.ker (sourceToLevel I α β c n) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  have hzD0 : (z.1.1 : L) ∈ LinearMap.range α := by
    have := congrArg Subtype.val hz
    change (boundaries I α β 0).mkQ z.1 = 0 at this
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at this
    change (z.1.1 : L) ∈ Submodule.map α (I ^ 0 • (⊤ : Submodule A K)) at this
    simpa using this
  have hzAR := hb ⟨hzD0,
    Submodule.smul_mono le_rfl le_top (coe_mem_smul_ker I β n z.2)⟩
  rw [← Submodule.map_top,
    ← Submodule.map_smul'' (I ^ (n - c)) (⊤ : Submodule A K) α] at hzAR
  change (boundaries I α β (n - c)).mkQ (sourceToLevelInclusion I α β c n z) = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact hzAR

private noncomputable def fromPower {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (c n : ℕ) (_hn : c ≤ n)
    (hb : LinearMap.range α ⊓ (I ^ n • (⊤ : Submodule A L)) ≤
      I ^ (n - c) • LinearMap.range α) :
    ↥(I ^ n • (⊤ : Submodule A (homology I α β 0))) →ₗ[A]
      homology I α β (n - c) :=
  ((LinearMap.ker (sourceToPower I α β n)).liftQ (sourceToLevel I α β c n)
      (source_kernel_le I α β c n hb)).comp
    (LinearMap.quotKerEquivOfSurjective (sourceToPower I α β n)
      (sourceToPower_surjective I α β n)).symm.toLinearMap

private lemma quotientFactor_apply {A : Type u} [CommRing A]
    {S Q T : Type*} [AddCommGroup S] [AddCommGroup Q] [AddCommGroup T]
    [Module A S] [Module A Q] [Module A T]
    (f : S →ₗ[A] Q) (hf : Function.Surjective f) (g : S →ₗ[A] T)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) (s : S) :
    ((LinearMap.ker f).liftQ g hker).comp
        (LinearMap.quotKerEquivOfSurjective f hf).symm.toLinearMap (f s) = g s := by
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

private lemma fromPower_apply_of_source {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (c n : ℕ) (hn : c ≤ n)
    (hb : LinearMap.range α ⊓ (I ^ n • (⊤ : Submodule A L)) ≤
      I ^ (n - c) • LinearMap.range α)
    (s : powerSource I α β n) :
    fromPower I α β c n hn hb (sourceToPower I α β n s) = sourceToLevel I α β c n s :=
  quotientFactor_apply (sourceToPower I α β n) (sourceToPower_surjective I α β n)
    (sourceToLevel I α β c n) (source_kernel_le I α β c n hb) s

private lemma fromPower_apply_of_cycle {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (c n : ℕ)
    (hn : c ≤ n)
    (hb : LinearMap.range α ⊓ (I ^ n • (⊤ : Submodule A L)) ≤
      I ^ (n - c) • LinearMap.range α)
    (z : ↥(I ^ n • (⊤ : Submodule A (homology I α β 0))))
    (y : cycles I β n) (hy : y.1 ∈ I ^ n • LinearMap.ker β)
    (hzy : (z : homology I α β 0) =
      transition I α β n 0 (Nat.zero_le n) (Submodule.Quotient.mk y)) :
    fromPower I α β c n hn hb z =
      transition I α β n (n - c) (Nat.sub_le n c) (Submodule.Quotient.mk y) := by
  let y0 : cycles I β 0 := ⟨y.1, y.2.1, by simp⟩
  let s : powerSource I α β n :=
    ⟨y0, cycle0_mem_power I β n y.1 y.2.1 hy⟩
  have hs : z = sourceToPower I α β n s := by
    apply Subtype.ext
    change z.1 = (boundaries I α β 0).mkQ y0
    rw [hzy, transition_mk]
    rfl
  subst z
  have h := fromPower_apply_of_source I α β c n hn hb s
  change fromPower I α β c n hn hb (sourceToPower I α β n s) = _ at h
  rw [h, transition_mk]
  rfl

private def sourceToCycle {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ) :
    powerSource I α β n →ₗ[A] cycles I β n := by
  simpa only [Nat.sub_zero] using sourceToLevelInclusion I α β 0 n

private lemma exists_cycle_of_mem_smul {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M) (n : ℕ)
    (z : ↥(I ^ n • (⊤ : Submodule A (homology I α β 0)))) :
    ∃ y : cycles I β n, y.1 ∈ I ^ n • LinearMap.ker β ∧
      (z : homology I α β 0) =
        transition I α β n 0 (Nat.zero_le n) (Submodule.Quotient.mk y) := by
  obtain ⟨s, rfl⟩ := sourceToPower_surjective I α β n z
  refine ⟨sourceToCycle I α β n s, coe_mem_smul_ker I β n s.2, ?_⟩
  rw [transition_mk]
  rfl

private lemma eqRec_linearMap_submodule_coe
    {R : Type u} [CommRing R] {S : Type v} {T : Type w}
    [AddCommGroup S] [AddCommGroup T] [Module R S] [Module R T]
    (P : ℕ → Submodule R T) {a b : ℕ} (h : a = b)
    (f : S →ₗ[R] ↥(P a)) (s : S) :
    (((Eq.ndrec (motive := fun k : ℕ => S →ₗ[R] ↥(P k)) f h) s :
        ↥(P b)) : T) = (f s : T) := by
  cases h
  rfl

private lemma eqRec_linearMap_submodule_apply
    {R : Type u} [CommRing R] {S : Type v} {T : Type w}
    [AddCommGroup S] [AddCommGroup T] [Module R S] [Module R T]
    (P : ℕ → Submodule R T) {a b : ℕ} (h : a = b)
    (f : S →ₗ[R] ↥(P a)) (s : S) :
    (Eq.ndrec (motive := fun k : ℕ => S →ₗ[R] ↥(P k)) f h) s =
      Eq.ndrec (motive := fun k : ℕ => ↥(P k)) (f s) h := by
  cases h
  rfl

private lemma eqRec_homology_linearMap_apply {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    {S : Type*} [AddCommGroup S] [Module A S]
    {a b : ℕ} (h : a = b) (f : S →ₗ[A] homology I α β a) (s : S) :
    (Eq.ndrec (motive := fun k : ℕ => S →ₗ[A] homology I α β k) f h) s =
      Eq.ndrec (motive := fun k : ℕ => homology I α β k) (f s) h := by
  cases h
  rfl

private lemma transition_eqRec {A : Type u} [CommRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (a b a' b' : ℕ) (ha : a = a') (hb : b = b')
    (hba : b ≤ a) (hba' : b' ≤ a') (z : homology I α β a) :
    Eq.ndrec (motive := fun k : ℕ => homology I α β k)
      (transition I α β a b hba z) hb =
    transition I α β a' b' hba'
      (Eq.ndrec (motive := fun k : ℕ => homology I α β k) z ha) := by
  subst a'
  subst b'
  rfl

set_option maxHeartbeats 1000000 in
-- Elaborating the quotient comparison and all pro-system identities needs a larger budget.
/-- **Stacks 0G3K.** The homology of the complex of ideal powers is canonically
pro-isomorphic to the ideal powers of the homology. -/
@[stacks 0G3K]
public theorem homologyIdealPowers_proIsomorphic
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup M]
    [Module A K] [Module A L] [Module A M]
    [Module.Finite A K] [Module.Finite A L] [Module.Finite A M]
    (I : Ideal A) (α : K →ₗ[A] L) (β : L →ₗ[A] M)
    (_hβα : β.comp α = 0) :
    let P : ℕ → Submodule A L := fun n =>
      LinearMap.ker β ⊓ (I ^ n • (⊤ : Submodule A L))
    let D : (n : ℕ) → Submodule A (P n) := fun n =>
      Submodule.comap (P n).subtype
        (Submodule.map α (I ^ n • (⊤ : Submodule A K)))
    let H : ℕ → Type _ := fun n => (P n) ⧸ D n
    let Q : ℕ → Type _ := fun n =>
      ↥(I ^ n • (⊤ : Submodule A (H 0)))
    ∃ (τ : ∀ (m n : ℕ), n ≤ m → H m →ₗ[A] H n),
      (∀ n, τ n n (le_refl n) = LinearMap.id) ∧
      (∀ (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m),
        (τ m n hmn).comp (τ k m hkm) = τ k n (hmn.trans hkm)) ∧
      (∀ (m n : ℕ) (hmn : n ≤ m) (y : P m),
        ∃ z : P n, z.1 = y.1 ∧
          τ m n hmn (Submodule.Quotient.mk y : H m) =
            (Submodule.Quotient.mk z : H n)) ∧
      ∃ c : ℕ, 0 < c ∧
        ∃ (ρ : ∀ (n : ℕ), c ≤ n → H n →ₗ[A]
              ↥(I ^ (n - c) • (⊤ : Submodule A (H 0))))
          (ψ : ∀ (n : ℕ), c ≤ n →
              ↥(I ^ n • (⊤ : Submodule A (H 0))) →ₗ[A] H (n - c)),
          (∀ (n : ℕ) (hn : c ≤ n) (z : H n),
            ((ρ n hn z : ↥(I ^ (n - c) • (⊤ : Submodule A (H 0)))) : H 0) =
              τ n 0 (Nat.zero_le n) z) ∧
          (∀ (n : ℕ) (hn : c ≤ n)
            (z : ↥(I ^ n • (⊤ : Submodule A (H 0)))) (y : P n),
            y.1 ∈ I ^ n • LinearMap.ker β →
            (z : H 0) = τ n 0 (Nat.zero_le n) (Submodule.Quotient.mk y : H n) →
            ψ n hn z = τ n (n - c) (Nat.sub_le n c)
              (Submodule.Quotient.mk y : H n)) ∧
          (∀ (m n : ℕ) (hmn : n ≤ m) (hm : c ≤ m) (hn : c ≤ n)
            (z : ↥(I ^ m • (⊤ : Submodule A (H 0))))
            (z' : ↥(I ^ n • (⊤ : Submodule A (H 0)))),
            (z' : H 0) = z →
            τ (m - c) (n - c) (Nat.sub_le_sub_right hmn c) (ψ m hm z) =
              ψ n hn z') ∧
          (∀ (n : ℕ) (hn : 2 * c ≤ n)
            (z : ↥(I ^ n • (⊤ : Submodule A (H 0)))),
            (((ρ (n - c) (by omega) (ψ n (by omega) z) :
                ↥(I ^ ((n - c) - c) • (⊤ : Submodule A (H 0)))) : H 0) = z.1)) ∧
          (∀ (n : ℕ) (hn : 2 * c ≤ n) (z : H n),
            ψ (n - c) (by omega) (ρ n (by omega) z) =
              τ n ((n - c) - c) (by omega) z) ∧
          -- The standard explicit witness that the two inverse systems are
          -- isomorphic as pro-objects, using the cofinal shift `n ↦ n + c`.
          ∃ (forward : ∀ m : ℕ, H (m + c) →ₗ[A] Q m)
              (backward : ∀ m : ℕ, Q (m + c) →ₗ[A] H m),
            (∀ (m m' : ℕ) (h : m ≤ m') (z : H (m' + c)),
              ((forward m (τ (m' + c) (m + c) (by omega) z) : Q m) : H 0) =
                (forward m' z : H 0)) ∧
            (∀ (m m' : ℕ) (h : m ≤ m') (z : Q (m' + c)) (z' : Q (m + c)),
              (z' : H 0) = z →
                backward m z' = τ m' m h (backward m' z)) ∧
            (∀ (m : ℕ) (z : H ((m + c) + c)),
              backward m (forward (m + c) z) =
                τ ((m + c) + c) m (by omega) z) ∧
            (∀ (m : ℕ) (z : Q ((m + c) + c)),
              ((forward m (backward (m + c) z) : Q m) : H 0) = z) := by
  classical
  dsimp only
  refine ⟨fun m n h => transition I α β m n h, ?_, ?_, ?_, ?_⟩
  · intro n
    exact transition_id I α β n
  · intro k m n hkm hmn
    exact transition_comp I α β k m n hkm hmn
  · intro m n hmn y
    exact ⟨⟨y.1, cycles_mono I β hmn y.2⟩, rfl,
      transition_mk I α β m n hmn y⟩
  · obtain ⟨c₁, hc₁, h₁⟩ := artinRees_le I (LinearMap.range α)
    obtain ⟨c₂, hc₂, h₂⟩ := artinRees_le I (LinearMap.ker β)
    let c := c₁ + c₂
    have hc : 0 < c := by dsimp [c]; omega
    have hb (n : ℕ) (hn : c ≤ n) :
        LinearMap.range α ⊓ (I ^ n • (⊤ : Submodule A L)) ≤
          I ^ (n - c) • LinearMap.range α :=
      (h₁ n (by dsimp [c] at hn; omega)).trans
        (Submodule.smul_mono (Ideal.pow_le_pow_right (by dsimp [c]; omega)) le_rfl)
    have hk (n : ℕ) (hn : c ≤ n) :
        cycles I β n ≤ I ^ (n - c) • LinearMap.ker β :=
      (h₂ n (by dsimp [c] at hn; omega)).trans
        (Submodule.smul_mono (Ideal.pow_le_pow_right (by dsimp [c]; omega)) le_rfl)
    have ψ_nat : ∀ (m n : ℕ) (hmn : n ≤ m) (hm : c ≤ m) (hn : c ≤ n)
        (z : ↥(I ^ m • (⊤ : Submodule A (homology I α β 0))))
        (z' : ↥(I ^ n • (⊤ : Submodule A (homology I α β 0)))),
        (z' : homology I α β 0) = z →
        transition I α β (m - c) (n - c) (Nat.sub_le_sub_right hmn c)
          (fromPower I α β c m hm (hb m hm) z) =
          fromPower I α β c n hn (hb n hn) z' := by
      intro m n hmn hm hn z z' hzz'
      obtain ⟨y, hy, hzm⟩ := exists_cycle_of_mem_smul I α β m z
      let yn : cycles I β n := ⟨y.1, cycles_mono I β hmn y.2⟩
      have hyn : yn.1 ∈ I ^ n • LinearMap.ker β :=
        (Submodule.smul_mono (Ideal.pow_le_pow_right hmn) le_rfl) hy
      have hzn : (z' : homology I α β 0) =
          transition I α β n 0 (Nat.zero_le n) (Submodule.Quotient.mk yn) := by
        rw [hzz', hzm]
        exact (transition_mk_restrict I α β m n 0 hmn _ y).symm
      have hψm := fromPower_apply_of_cycle I α β c m hm (hb m hm) z y hy hzm
      have hψn := fromPower_apply_of_cycle I α β c n hn (hb n hn) z' yn hyn hzn
      change transition I α β (m - c) (n - c) (Nat.sub_le_sub_right hmn c)
          (fromPower I α β c m hm (hb m hm) z) =
        fromPower I α β c n hn (hb n hn) z'
      rw [hψm, hψn]
      exact (transition_transition ..).trans (transition_mk_restrict I α β m n _ hmn _ y).symm
    have rho_psi : ∀ (n : ℕ) (hn : 2 * c ≤ n)
        (z : ↥(I ^ n • (⊤ : Submodule A (homology I α β 0)))),
        (((toPower I α β c (n - c) (by omega) (hk (n - c) (by omega))
          (fromPower I α β c n (by omega) (hb n (by omega)) z) :
            ↥(I ^ ((n - c) - c) •
              (⊤ : Submodule A (homology I α β 0)))) :
                homology I α β 0) = z.1) := by
      intro n hn z
      have hn₁ : c ≤ n := by omega
      have hn₂ : c ≤ n - c := by omega
      obtain ⟨y, hy, hz⟩ := exists_cycle_of_mem_smul I α β n z
      have hψ := fromPower_apply_of_cycle I α β c n hn₁ (hb n hn₁) z y hy hz
      change transition I α β (n - c) 0 (Nat.zero_le (n - c))
          (fromPower I α β c n hn₁ (hb n hn₁) z) = z.1
      rw [hψ, transition_transition]
      exact hz.symm
    have psi_rho : ∀ (n : ℕ) (hn : 2 * c ≤ n)
        (z : homology I α β n),
        fromPower I α β c (n - c) (by omega) (hb (n - c) (by omega))
          (toPower I α β c n (by omega) (hk n (by omega)) z) =
          transition I α β n ((n - c) - c) (by omega) z := by
      intro n hn z
      have hn₁ : c ≤ n := by omega
      have hn₂ : c ≤ n - c := by omega
      induction z using Submodule.Quotient.induction_on with
      | _ y =>
        let y' : cycles I β (n - c) :=
          ⟨y.1, cycles_mono I β (Nat.sub_le n c) y.2⟩
        have hy' : y'.1 ∈ I ^ (n - c) • LinearMap.ker β :=
          hk n hn₁ y.2
        have hzy : ((toPower I α β c n hn₁ (hk n hn₁)
            (Submodule.Quotient.mk y) :
              ↥(I ^ (n - c) • (⊤ : Submodule A (homology I α β 0)))) :
                homology I α β 0) =
            transition I α β (n - c) 0 (Nat.zero_le (n - c))
              (Submodule.Quotient.mk y') := by
          exact (transition_mk_restrict I α β n (n - c) 0 (Nat.sub_le n c) _ y).symm
        have hψ := fromPower_apply_of_cycle I α β c (n - c) hn₂
          (hb (n - c) hn₂) (toPower I α β c n hn₁ (hk n hn₁)
            (Submodule.Quotient.mk y)) y' hy' hzy
        change fromPower I α β c (n - c) hn₂ (hb (n - c) hn₂)
            (toPower I α β c n hn₁ (hk n hn₁) (Submodule.Quotient.mk y)) =
          transition I α β n ((n - c) - c) (by omega)
            (Submodule.Quotient.mk y)
        rw [hψ]
        exact transition_mk_restrict I α β n (n - c) _ (Nat.sub_le n c) _ y
    let forward (m : ℕ) : homology I α β (m + c) →ₗ[A]
        ↥(I ^ m • (⊤ : Submodule A (homology I α β 0))) := by
      have hmc : m + c - c = m := by omega
      let f := toPower I α β c (m + c) (by omega) (hk (m + c) (by omega))
      exact Eq.ndrec (motive := fun k : ℕ =>
        homology I α β (m + c) →ₗ[A]
          ↥(I ^ k • (⊤ : Submodule A (homology I α β 0)))) f hmc
    let backward (m : ℕ) :
        ↥(I ^ (m + c) • (⊤ : Submodule A (homology I α β 0))) →ₗ[A]
          homology I α β m := by
      have hmc : m + c - c = m := by omega
      let f := fromPower I α β c (m + c) (by omega) (hb (m + c) (by omega))
      exact Eq.ndrec (motive := fun k : ℕ =>
        ↥(I ^ (m + c) • (⊤ : Submodule A (homology I α β 0))) →ₗ[A]
          homology I α β k) f hmc
    have forward_coe (m : ℕ) (z : homology I α β (m + c)) :
        ((forward m z : ↥(I ^ m • (⊤ : Submodule A (homology I α β 0)))) :
          homology I α β 0) =
        transition I α β (m + c) 0 (Nat.zero_le (m + c)) z := by
      have h := eqRec_linearMap_submodule_coe
        (P := fun k => I ^ k • (⊤ : Submodule A (homology I α β 0)))
        (Nat.add_sub_cancel_right m c)
        (toPower I α β c (m + c) (by omega) (hk (m + c) (by omega))) z
      exact h.trans rfl
    have forward_apply (m : ℕ) (z : homology I α β (m + c)) :
        forward m z =
          Eq.ndrec (motive := fun k : ℕ =>
            ↥(I ^ k • (⊤ : Submodule A (homology I α β 0))))
              (toPower I α β c (m + c) (by omega) (hk (m + c) (by omega)) z)
              (Nat.add_sub_cancel_right m c) :=
      eqRec_linearMap_submodule_apply
        (P := fun k => I ^ k • (⊤ : Submodule A (homology I α β 0)))
        (Nat.add_sub_cancel_right m c)
        (toPower I α β c (m + c) (by omega) (hk (m + c) (by omega))) z
    have backward_apply (m : ℕ)
        (z : ↥(I ^ (m + c) • (⊤ : Submodule A (homology I α β 0)))) :
        backward m z =
          Eq.ndrec (motive := fun k : ℕ => homology I α β k)
            (fromPower I α β c (m + c) (by omega) (hb (m + c) (by omega)) z)
            (Nat.add_sub_cancel_right m c) :=
      eqRec_homology_linearMap_apply I α β
        (Nat.add_sub_cancel_right m c)
        (fromPower I α β c (m + c) (by omega) (hb (m + c) (by omega))) z
    refine ⟨c, hc, fun n hn => toPower I α β c n hn (hk n hn),
      fun n hn => fromPower I α β c n hn (hb n hn), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn z
      rfl
    · intro n hn z y hy hzy
      exact fromPower_apply_of_cycle I α β c n hn (hb n hn) z y hy hzy
    · exact ψ_nat
    · exact rho_psi
    · exact psi_rho
    · exact forward
    · refine ⟨backward, ?_, ?_, ?_, ?_⟩
      · intro m m' h z
        rw [forward_coe, forward_coe, transition_transition]
      · intro m m' h z z' hzz'
        have hnat := ψ_nat (m' + c) (m + c) (by omega) (by omega) (by omega)
          z z' hzz'
        rw [backward_apply, backward_apply]
        have hcast := congrArg
          (fun t : homology I α β (m + c - c) =>
            Eq.ndrec (motive := fun k : ℕ => homology I α β k) t
              (Nat.add_sub_cancel_right m c)) hnat.symm
        exact hcast.trans (transition_eqRec I α β
          (m' + c - c) (m + c - c) m' m
          (Nat.add_sub_cancel_right m' c) (Nat.add_sub_cancel_right m c)
          (by omega) h
          (fromPower I α β c (m' + c) (by omega) (hb (m' + c) (by omega)) z))
      · intro m z
        induction z using Submodule.Quotient.induction_on with
        | _ y =>
          let y' : cycles I β (m + c) :=
            ⟨y.1, cycles_mono I β (by omega : m + c ≤ (m + c) + c) y.2⟩
          have hy' : y'.1 ∈ I ^ (m + c) • LinearMap.ker β := by
            have hy := hk ((m + c) + c) (by omega) y.2
            simpa only [Nat.add_sub_cancel_right] using hy
          have hz :
              ((forward (m + c) (Submodule.Quotient.mk y) :
                ↥(I ^ (m + c) • (⊤ : Submodule A (homology I α β 0)))) :
                  homology I α β 0) =
              transition I α β (m + c) 0 (Nat.zero_le (m + c))
                (Submodule.Quotient.mk y') := by
            rw [forward_coe]
            exact (transition_mk_restrict I α β _ (m + c) 0 (by omega) _ y).symm
          have hψ := fromPower_apply_of_cycle I α β c (m + c) (by omega)
            (hb (m + c) (by omega))
            (forward (m + c) (Submodule.Quotient.mk y)) y' hy' hz
          rw [backward_apply]
          have hcast := congrArg
            (fun t : homology I α β (m + c - c) =>
              Eq.ndrec (motive := fun k : ℕ => homology I α β k) t
                (Nat.add_sub_cancel_right m c)) hψ
          apply hcast.trans
          calc
            Eq.ndrec (motive := fun k : ℕ => homology I α β k)
                (transition I α β (m + c) (m + c - c) (Nat.sub_le _ _)
                  (Submodule.Quotient.mk y'))
                (Nat.add_sub_cancel_right m c) =
              Eq.ndrec (motive := fun k : ℕ => homology I α β k)
                (transition I α β ((m + c) + c) (m + c - c) (by omega)
                  (Submodule.Quotient.mk y))
                (Nat.add_sub_cancel_right m c) := by
                  congr 1
            _ = transition I α β ((m + c) + c) m (by omega)
                  (Submodule.Quotient.mk y) :=
                    transition_eqRec I α β
                      ((m + c) + c) (m + c - c) ((m + c) + c) m
                      rfl (Nat.add_sub_cancel_right m c) (by omega) (by omega)
                      (Submodule.Quotient.mk y)
      · intro m z
        rw [forward_coe, backward_apply]
        have htrans := transition_eqRec I α β
          ((m + c) + c - c) 0 (m + c) 0
          (Nat.add_sub_cancel_right (m + c) c) rfl
          (Nat.zero_le _) (Nat.zero_le _)
          (fromPower I α β c ((m + c) + c) (by omega)
            (hb ((m + c) + c) (by omega)) z)
        exact htrans.symm.trans (rho_psi ((m + c) + c) (by omega) z)

end Stacks.AdicSystem.Homology

end

end
