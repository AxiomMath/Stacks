module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.FormallySmooth.Regularity
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.MvPowerSeries.HomExt
public import StacksFrontier.RingTheory.Regular.RegularRingHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transfer of adic formal smoothness between complete local algebras

Let `Λ` be a ring. This file collects elementary permanence properties of
`RingHom.FormallySmoothNAdic` (formal smoothness for an adic topology, Tag 07EE) and uses them to
compare the formal smoothness over `Λ` of two Noetherian complete local `Λ`-algebras linked by a
formally smooth local homomorphism, as in the proof of Tag 0DZS.

## Main results

* `RingHom.FormallySmoothNAdic.comp`: adic formal smoothness is stable under composition.
* `RingHom.FormallySmoothNAdic.of_retract`: it passes to a retract.
* `RingHom.formallySmoothNAdic_C_mvPowerSeries`: `A → A[[t₁, …, t_r]]` is formally smooth.
* `RingHom.formallySmoothNAdic_algebraMap_mvPowerSeries_iff`: `Λ → A` is formally smooth if and
  only if `Λ → A[[t₁, …, t_r]]` is.
* `RingHom.formallySmoothNAdic_algebraMap_iff_of_isLocalization`: localizing the source.
* `RingHom.formallySmoothNAdic_algebraMap_adicCompletion_iff`: completing the target.
* `RingHom.formallySmoothNAdic_algebraMap_adicCompletion_maximalIdeal_iff`: completing a
  Noetherian local target at its maximal ideal.
* `RingHom.formallySmoothNAdic_iff_of_comp_algebraMap_adicCompletion`: completing the source.
* `RingHom.formallySmoothNAdic_algebraMap_iff_of_formallySmoothNAdic`: if `A → A'` is a formally
  smooth local homomorphism of Noetherian complete local `Λ`-algebras, then `Λ → A` is formally
  smooth if and only if `Λ → A'` is.

## References

* [Stacks Project, Tag 07EE](https://stacks.math.columbia.edu/tag/07EE)
* [Stacks Project, Tag 07PM](https://stacks.math.columbia.edu/tag/07PM)
* [Stacks Project, Tag 07NT](https://stacks.math.columbia.edu/tag/07NT)
* [Stacks Project, Tag 0DZS](https://stacks.math.columbia.edu/tag/0DZS)
-/

@[expose] public section

universe u

open IsLocalRing

namespace RingHom

/-- If `n.map ψ ≤ m` and `χ` kills `m ^ k`, then `χ ∘ ψ` kills `n ^ k`. -/
private theorem pow_le_ker_comp_of_map_le {S T X : Type u} [CommRing S] [CommRing T]
    [CommRing X] {ψ : S →+* T} {n : Ideal S} {m : Ideal T} (hnm : n.map ψ ≤ m)
    {χ : T →+* X} {k : ℕ} (hk : m ^ k ≤ RingHom.ker χ) : n ^ k ≤ RingHom.ker (χ.comp ψ) := by
  intro x hx
  rw [RingHom.mem_ker, RingHom.comp_apply]
  apply hk
  have hx' : ψ x ∈ (n ^ k).map ψ := Ideal.mem_map_of_mem ψ hx
  rw [Ideal.map_pow] at hx'
  exact Ideal.pow_right_mono hnm k hx'

/-- If `J ^ 2 = 0` and `g` kills `K ^ k` modulo `J`, then `g` kills `K ^ (2 * k)`. -/
private theorem pow_two_mul_le_ker {X C : Type u} [CommRing X] [CommRing C] {J : Ideal C}
    (hJ : J ^ 2 = ⊥) (g : X →+* C) {K : Ideal X} {k : ℕ}
    (h : K ^ k ≤ RingHom.ker ((Ideal.Quotient.mk J).comp g)) :
    K ^ (2 * k) ≤ RingHom.ker g := by
  have h' : (K ^ k).map g ≤ J :=
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
      Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.mp (h hx))
  intro x hx
  have hx2 : g x ∈ J ^ 2 := by
    apply Ideal.pow_right_mono h' 2
    rw [← Ideal.map_pow, ← pow_mul, mul_comm]
    exact Ideal.mem_map_of_mem _ hx
  rwa [hJ, Ideal.mem_bot] at hx2

/-- A ring map `g : B → C` killing `I ^ k` extends to the `I`-adic completion of `B`, by a map
killing `(I B^∧) ^ k`. -/
private theorem exists_adicCompletion_lift {B C : Type u} [CommRing B] [CommRing C] (I : Ideal B)
    {k : ℕ} (g : B →+* C) (hg : I ^ k ≤ RingHom.ker g) :
    ∃ gh : AdicCompletion I B →+* C, gh.comp (algebraMap B (AdicCompletion I B)) = g ∧
      (I.map (algebraMap B (AdicCompletion I B))) ^ k ≤ RingHom.ker gh := by
  let gh : AdicCompletion I B →+* C :=
    (Ideal.Quotient.lift (I ^ k) g hg).comp (AdicCompletion.evalₐ I k).toRingHom
  have hgh : gh.comp (algebraMap B (AdicCompletion I B)) = g := by
    ext b
    simp [gh, AdicCompletion.algebraMap_apply]
    rfl
  refine ⟨gh, hgh, ?_⟩
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hgh]
  exact hg hb

namespace FormallySmoothNAdic

/-- Adic formal smoothness is stable under composition: if `φ : R → S` is formally smooth for the
`n`-adic topology, `ψ : S → T` is formally smooth for the `m`-adic topology and `ψ(n) ⊆ m`, then
`ψ ∘ φ` is formally smooth for the `m`-adic topology. -/
theorem comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {φ : R →+* S} {ψ : S →+* T} {n : Ideal S} {m : Ideal T}
    (hφ : FormallySmoothNAdic.{u} φ n) (hψ : FormallySmoothNAdic.{u} ψ m)
    (hnm : n.map ψ ≤ m) : FormallySmoothNAdic.{u} (ψ.comp φ) m := by
  intro C _ J hJ f χ hcomm ⟨k, hk, hker⟩
  obtain ⟨g, hgπ, hgφ⟩ := hφ C J hJ f (χ.comp ψ)
    (by rw [RingHom.comp_assoc]; exact hcomm) ⟨k, hk, pow_le_ker_comp_of_map_le hnm hker⟩
  obtain ⟨h, hhπ, hhψ⟩ := hψ C J hJ g χ hgπ.symm ⟨k, hk, hker⟩
  exact ⟨h, hhπ, by rw [← RingHom.comp_assoc, hhψ, hgφ]⟩

/-- Adic formal smoothness passes to a retract: if `ρ ∘ ι = id`, `ρ(m) ⊆ n` and `ι ∘ φ` is
formally smooth for the `m`-adic topology, then `φ` is formally smooth for the `n`-adic
topology. -/
theorem of_retract {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {φ : R →+* S} {ι : S →+* T} {ρ : T →+* S} (hρι : ρ.comp ι = RingHom.id S)
    {n : Ideal S} {m : Ideal T} (hmn : m.map ρ ≤ n)
    (h : FormallySmoothNAdic.{u} (ι.comp φ) m) : FormallySmoothNAdic.{u} φ n := by
  intro C _ J hJ f χ hcomm ⟨k, hk, hker⟩
  have hcomm' : (χ.comp ρ).comp (ι.comp φ) = (Ideal.Quotient.mk J).comp f := by
    rw [← hcomm]
    ext x
    have hx := RingHom.congr_fun hρι (φ x)
    simp only [RingHom.comp_apply, RingHom.id_apply] at hx ⊢
    rw [hx]
  obtain ⟨g, hgπ, hgφ⟩ :=
    h C J hJ f (χ.comp ρ) hcomm' ⟨k, hk, pow_le_ker_comp_of_map_le hmn hker⟩
  refine ⟨g.comp ι, ?_, ?_⟩
  · rw [← RingHom.comp_assoc, hgπ, RingHom.comp_assoc, hρι, RingHom.comp_id]
  · rwa [RingHom.comp_assoc]

end FormallySmoothNAdic

/-! ### Power series -/

/-- The inclusion `A → A[[t₁, …, t_r]]` is formally smooth for the `M`-adic topology for every
ideal `M` containing the variables. -/
@[ega "IV 17.5.3" "Implication d'') ⇒ d')"]
theorem formallySmoothNAdic_C_mvPowerSeries {A : Type u} [CommRing A] (r : ℕ)
    (M : Ideal (MvPowerSeries (Fin r) A)) (hX : ∀ i, MvPowerSeries.X i ∈ M) :
    FormallySmoothNAdic.{u} (MvPowerSeries.C : A →+* MvPowerSeries (Fin r) A) M := by
  intro C _ J hJ f ψ hcomm ⟨k, hk, hker⟩
  choose c hc using fun i : Fin r => Ideal.Quotient.mk_surjective (ψ (MvPowerSeries.X i))
  have hnil : ∀ i, IsNilpotent (c i) := by
    intro i
    have hcJ : c i ^ k ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, hc i, ← map_pow]
      exact hker (Ideal.pow_mem_pow (hX i) k)
    refine ⟨k * 2, ?_⟩
    have h2 := Ideal.pow_mem_pow hcJ 2
    rwa [hJ, Ideal.mem_bot, ← pow_mul] at h2
  let : UniformSpace A := ⊥
  let : UniformSpace C := ⊥
  have hfc : Continuous f := continuous_of_discreteTopology
  have he : MvPowerSeries.HasEval c :=
    ⟨fun i => (hnil i).isTopologicallyNilpotent, by simp⟩
  let F : MvPowerSeries (Fin r) A →+* C := MvPowerSeries.eval₂Hom hfc he
  have hFC : ∀ a, F (MvPowerSeries.C a) = f a := fun a => by
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
  have hFX : ∀ i, F (MvPowerSeries.X i) = c i := fun i => by
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
  have : IsHausdorff (M.map ψ) (C ⧸ J) := by
    refine ⟨fun x hx => ?_⟩
    have h1 : x ∈ (M.map ψ) ^ k := by
      simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hx k
    rw [← Ideal.map_pow] at h1
    exact (Ideal.mem_bot).mp
      (Ideal.map_le_iff_le_comap.mpr (hker.trans (RingHom.ker_eq_comap_bot ψ).le) h1)
  refine ⟨F, ?_, RingHom.ext hFC⟩
  apply mvPowerSeries_hom_ext (M.map ψ) r
  · intro a
    rw [RingHom.comp_apply, hFC]
    exact (RingHom.congr_fun hcomm a).symm
  · intro i
    rw [RingHom.comp_apply, hFX, hc i]
  · intro i
    rw [RingHom.comp_apply, hFX, hc i]
    exact Ideal.mem_map_of_mem ψ (hX i)

/-- For a local ring `A`, `Λ → A` is formally smooth for the maximal-ideal-adic topology if and
only if `Λ → A[[t₁, …, t_r]]` is. -/
@[ega "0 19.3.4" "special case"]
theorem formallySmoothNAdic_algebraMap_mvPowerSeries_iff {Λ A : Type u} [CommRing Λ]
    [CommRing A] [Algebra Λ A] [IsLocalRing A] (r : ℕ) :
    FormallySmoothNAdic.{u} (algebraMap Λ A) (maximalIdeal A) ↔
      FormallySmoothNAdic.{u} (algebraMap Λ (MvPowerSeries (Fin r) A))
        (maximalIdeal (MvPowerSeries (Fin r) A)) := by
  have halg : algebraMap Λ (MvPowerSeries (Fin r) A) =
      (MvPowerSeries.C : A →+* MvPowerSeries (Fin r) A).comp (algebraMap Λ A) :=
    RingHom.ext fun a => MvPowerSeries.algebraMap_apply (σ := Fin r) (R := Λ) (A := A) (r := a)
  have hmax : ∀ x : MvPowerSeries (Fin r) A, x ∈ maximalIdeal (MvPowerSeries (Fin r) A) ↔
      MvPowerSeries.constantCoeff x ∈ maximalIdeal A := by
    intro x
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
  rw [halg]
  constructor
  · intro h
    refine h.comp (formallySmoothNAdic_C_mvPowerSeries r _ fun i => ?_) ?_
    · rw [hmax, MvPowerSeries.constantCoeff_X]
      exact zero_mem _
    · refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      rwa [Ideal.mem_comap, hmax, MvPowerSeries.constantCoeff_C]
  · intro h
    refine FormallySmoothNAdic.of_retract
      (ρ := (MvPowerSeries.constantCoeff : MvPowerSeries (Fin r) A →+* A)) ?_ ?_ h
    · ext a
      simp
    · exact Ideal.map_le_iff_le_comap.2 fun x hx => (hmax x).mp hx

/-! ### Localization of the source -/

/-- Let `R'` be a localization of `R` and `A` an `R'`-algebra. Then `R → A` is formally smooth for
the `n`-adic topology if and only if `R' → A` is. -/
theorem formallySmoothNAdic_algebraMap_iff_of_isLocalization {R R' A : Type u} [CommRing R]
    [CommRing R'] [CommRing A] [Algebra R R'] [Algebra R A] [Algebra R' A]
    [IsScalarTower R R' A] (M : Submonoid R) [IsLocalization M R'] (n : Ideal A) :
    FormallySmoothNAdic.{u} (algebraMap R A) n ↔ FormallySmoothNAdic.{u} (algebraMap R' A) n := by
  have htower : (algebraMap R' A).comp (algebraMap R R') = algebraMap R A :=
    (IsScalarTower.algebraMap_eq R R' A).symm
  constructor
  · intro h C _ J hJ f ψ hcomm hk
    obtain ⟨g, hgπ, hg⟩ := h C J hJ (f.comp (algebraMap R R')) ψ
      (by rw [← htower, ← RingHom.comp_assoc, hcomm, RingHom.comp_assoc]) hk
    refine ⟨g, hgπ, IsLocalization.ringHom_ext M ?_⟩
    rw [RingHom.comp_assoc, htower, hg]
  · intro h C _ J hJ f ψ hcomm hk
    have hunits : ∀ s : M, IsUnit (f s) := by
      intro s
      have hu : IsUnit (ψ (algebraMap R A s)) := by
        rw [← htower, RingHom.comp_apply]
        exact ((IsLocalization.map_units R' s).map (algebraMap R' A)).map ψ
      have hv : ψ (algebraMap R A s) = Ideal.Quotient.mk J (f s) := RingHom.congr_fun hcomm s
      rw [hv] at hu
      exact (IsNilpotent.isUnit_quotient_mk_iff (I := J) ⟨2, hJ⟩).mp hu
    let f' : R' →+* C := IsLocalization.lift (M := M) (S := R') hunits
    have hf' : f'.comp (algebraMap R R') = f := IsLocalization.lift_comp hunits
    obtain ⟨g, hgπ, hg⟩ := h C J hJ f' ψ (IsLocalization.ringHom_ext M (by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, htower, hf', hcomm])) hk
    exact ⟨g, hgπ, by rw [← htower, ← RingHom.comp_assoc, hg, hf']⟩

/-! ### Completion of the target and of the source -/

/-- For a finitely generated ideal `I` of a `Λ`-algebra `B`, the map `Λ → B` is formally smooth
for the `I`-adic topology if and only if `Λ → B^∧` is formally smooth for the `IB^∧`-adic
topology, where `B^∧` is the `I`-adic completion of `B`. -/
theorem formallySmoothNAdic_algebraMap_adicCompletion_iff {Λ B : Type u} [CommRing Λ]
    [CommRing B] [Algebra Λ B] (I : Ideal B) (hI : I.FG) :
    FormallySmoothNAdic.{u} (algebraMap Λ B) I ↔
      FormallySmoothNAdic.{u} (algebraMap Λ (AdicCompletion I B))
        (I.map (algebraMap B (AdicCompletion I B))) := by
  set ι := algebraMap B (AdicCompletion I B) with hι
  have htower : ι.comp (algebraMap Λ B) = algebraMap Λ (AdicCompletion I B) :=
    (IsScalarTower.algebraMap_eq Λ B (AdicCompletion I B)).symm
  constructor
  · intro h C _ J hJ f ψ hcomm ⟨k, hk, hker⟩
    have hkerB : I ^ k ≤ RingHom.ker (ψ.comp ι) := pow_le_ker_comp_of_map_le le_rfl hker
    obtain ⟨g, hgπ, hg⟩ := h C J hJ f (ψ.comp ι)
      (by rw [RingHom.comp_assoc, htower]; exact hcomm) ⟨k, hk, hkerB⟩
    have hgker : I ^ (2 * k) ≤ RingHom.ker g := pow_two_mul_le_ker hJ g (by rwa [hgπ])
    obtain ⟨gh, hghι, hghker⟩ := exists_adicCompletion_lift I g hgker
    refine ⟨gh, ?_, ?_⟩
    · apply adicCompletion_ringHom_ext_of_pow_le_ker I hI
        ((Ideal.Quotient.mk J).comp gh) ψ (2 * k) k
      · intro x hx
        rw [RingHom.mem_ker, RingHom.comp_apply, hghker hx, map_zero]
      · exact hker
      · ext b
        rw [RingHom.comp_apply, RingHom.comp_apply, ← hι, ← RingHom.comp_apply gh, hghι,
          ← RingHom.comp_apply, hgπ, RingHom.comp_apply]
    · rw [← htower, ← RingHom.comp_assoc, hghι, hg]
  · intro h C _ J hJ f ψ hcomm ⟨k, hk, hker⟩
    obtain ⟨ψh, hψh, hψhker⟩ := exists_adicCompletion_lift I ψ hker
    obtain ⟨g, hgπ, hg⟩ := h C J hJ f ψh
      (by rw [← htower, ← RingHom.comp_assoc, hψh, hcomm]) ⟨k, hk, hψhker⟩
    exact ⟨g.comp ι, by rw [← RingHom.comp_assoc, hgπ, hψh],
      by rw [RingHom.comp_assoc, htower, hg]⟩

/-- For a Noetherian local `Λ`-algebra `B`, the map `Λ → B` is formally smooth for the
maximal-ideal-adic topology if and only if `Λ → B^∧` is, where `B^∧` is the completion of `B`. -/
theorem formallySmoothNAdic_algebraMap_adicCompletion_maximalIdeal_iff {Λ B : Type u}
    [CommRing Λ] [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra Λ B] :
    FormallySmoothNAdic.{u} (algebraMap Λ B) (maximalIdeal B) ↔
      FormallySmoothNAdic.{u} (algebraMap Λ (AdicCompletion (maximalIdeal B) B))
        (maximalIdeal (AdicCompletion (maximalIdeal B) B)) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact formallySmoothNAdic_algebraMap_adicCompletion_iff _
    (maximalIdeal B).fg_of_isNoetherianRing

/-- Let `I` be a finitely generated ideal of `O`, let `φ : O → A` carry `I` into an ideal `n`
of `A`, and let `φ^∧ : O^∧ → A` extend `φ` to the `I`-adic completion. Then `φ` is formally
smooth for the `n`-adic topology if and only if `φ^∧` is. -/
theorem formallySmoothNAdic_iff_of_comp_algebraMap_adicCompletion {O A : Type u} [CommRing O]
    [CommRing A] (I : Ideal O) (hI : I.FG) (n : Ideal A) (φ : O →+* A)
    (φh : AdicCompletion I O →+* A) (hφh : φh.comp (algebraMap O (AdicCompletion I O)) = φ)
    (hIn : I.map φ ≤ n) :
    FormallySmoothNAdic.{u} φ n ↔ FormallySmoothNAdic.{u} φh n := by
  set ι := algebraMap O (AdicCompletion I O) with hι
  have hmap : (I.map ι).map φh ≤ n := by
    rwa [Ideal.map_map, hφh]
  constructor
  · intro h C _ J hJ f ψ hcomm ⟨k, hk, hker⟩
    obtain ⟨g, hgπ, hg⟩ := h C J hJ (f.comp ι) ψ
      (by rw [← hφh, ← RingHom.comp_assoc, hcomm, RingHom.comp_assoc]) ⟨k, hk, hker⟩
    refine ⟨g, hgπ, ?_⟩
    have hfker : (I.map ι) ^ (2 * k) ≤ RingHom.ker f :=
      pow_two_mul_le_ker hJ f (by rw [← hcomm]; exact pow_le_ker_comp_of_map_le hmap hker)
    have hgker : n ^ (2 * k) ≤ RingHom.ker g := pow_two_mul_le_ker hJ g (by rwa [hgπ])
    apply adicCompletion_ringHom_ext_of_pow_le_ker I hI (g.comp φh) f (2 * k) (2 * k)
    · exact pow_le_ker_comp_of_map_le hmap hgker
    · exact hfker
    · rw [RingHom.comp_assoc, ← hι, hφh, hg]
  · intro h C _ J hJ f ψ hcomm ⟨k, hk, hker⟩
    have hfker : I ^ (2 * k) ≤ RingHom.ker f :=
      pow_two_mul_le_ker hJ f (by rw [← hcomm]; exact pow_le_ker_comp_of_map_le hIn hker)
    obtain ⟨fh, hfh, hfhker⟩ := exists_adicCompletion_lift I f hfker
    have hcomm' : ψ.comp φh = (Ideal.Quotient.mk J).comp fh := by
      apply adicCompletion_ringHom_ext_of_pow_le_ker I hI _ _ k (2 * k)
      · exact pow_le_ker_comp_of_map_le hmap hker
      · intro x hx
        rw [RingHom.mem_ker, RingHom.comp_apply, hfhker hx, map_zero]
      · rw [RingHom.comp_assoc, RingHom.comp_assoc, ← hι, hφh, hfh, hcomm]
    obtain ⟨g, hgπ, hg⟩ := h C J hJ fh ψ hcomm' ⟨k, hk, hker⟩
    exact ⟨g, hgπ, by rw [← hφh, ← RingHom.comp_assoc, hg, hfh]⟩

/-! ### Transfer along a formally smooth local homomorphism -/

/-- Let `f : A → A'` be a local homomorphism of Noetherian complete local `Λ`-algebras, with `Λ`
Noetherian, which is formally smooth for the `m_{A'}`-adic topology. Then `Λ → A` is formally
smooth for the `m_A`-adic topology if and only if `Λ → A'` is formally smooth for the
`m_{A'}`-adic topology. -/
theorem formallySmoothNAdic_algebraMap_iff_of_formallySmoothNAdic {Λ A A' : Type u}
    [CommRing Λ] [IsNoetherianRing Λ]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    [Algebra Λ A]
    [CommRing A'] [IsLocalRing A'] [IsNoetherianRing A'] [IsAdicComplete (maximalIdeal A') A']
    [Algebra Λ A']
    (f : A →ₐ[Λ] A') [IsLocalHom f.toRingHom]
    (hf : FormallySmoothNAdic.{u} f.toRingHom (maximalIdeal A')) :
    FormallySmoothNAdic.{u} (algebraMap Λ A) (maximalIdeal A) ↔
      FormallySmoothNAdic.{u} (algebraMap Λ A') (maximalIdeal A') := by
  have hfΛ : f.toRingHom.comp (algebraMap Λ A) = algebraMap Λ A' :=
    RingHom.ext fun a => f.commutes a
  constructor
  · intro h
    rw [← hfΛ]
    exact h.comp hf (map_maximalIdeal_le f.toRingHom)
  intro hA'
  let p : Ideal Λ := (maximalIdeal A).comap (algebraMap Λ A)
  let O := Localization.AtPrime p
  have : IsNoetherianRing O := IsLocalization.isNoetherianRing p.primeCompl O inferInstance
  have hunits : ∀ s : p.primeCompl, IsUnit (algebraMap Λ A s) := fun s => of_not_not s.2
  let φO : O →+* A := IsLocalization.lift (M := p.primeCompl) (S := O) hunits
  have hφO : φO.comp (algebraMap Λ O) = algebraMap Λ A := IsLocalization.lift_comp hunits
  let : Algebra O A := φO.toAlgebra
  have : IsScalarTower Λ O A :=
    IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hφO a).symm
  let : Algebra O A' := (f.toRingHom.comp φO).toAlgebra
  have : IsScalarTower Λ O A' := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap Λ A' a = f.toRingHom (φO (algebraMap Λ O a))
    rw [← RingHom.comp_apply φO, hφO, ← RingHom.comp_apply, hfΛ]
  have hOm : (maximalIdeal O).map φO ≤ maximalIdeal A := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hφO]
    exact Ideal.map_comap_le
  let Oh := AdicCompletion (maximalIdeal O) O
  let φh : Oh →+* A :=
    ((AdicCompletion.ofAlgEquiv (maximalIdeal A)).symm :
      AdicCompletion (maximalIdeal A) A →+* A).comp
        (adicCompletionMap φO (maximalIdeal O) (maximalIdeal A) hOm)
  have hφh : φh.comp (algebraMap O Oh) = φO := by
    ext a
    simp only [φh, RingHom.comp_apply]
    exact (AdicCompletion.ofAlgEquiv (maximalIdeal A)).symm.commutes (φO a)
  have hφhm : (maximalIdeal Oh).map φh ≤ maximalIdeal A := by
    rwa [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hφh]
  have : IsLocalHom φh := ((IsLocalRing.local_hom_TFAE φh).out 3 1).mp hφhm
  have hOm' : (maximalIdeal O).map (f.toRingHom.comp φO) ≤ maximalIdeal A' := by
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hOm).trans (map_maximalIdeal_le f.toRingHom)
  have hcomp' : (f.toRingHom.comp φh).comp (algebraMap O Oh) = f.toRingHom.comp φO := by
    rw [RingHom.comp_assoc, hφh]
  have hO' : FormallySmoothNAdic.{u} (f.toRingHom.comp φO) (maximalIdeal A') :=
    (formallySmoothNAdic_algebraMap_iff_of_isLocalization (R' := O) (A := A') p.primeCompl
      (maximalIdeal A')).mp hA'
  have hOh' : FormallySmoothNAdic.{u} (f.toRingHom.comp φh) (maximalIdeal A') :=
    (formallySmoothNAdic_iff_of_comp_algebraMap_adicCompletion (maximalIdeal O)
      (maximalIdeal O).fg_of_isNoetherianRing (maximalIdeal A') _ _ hcomp' hOm').mp hO'
  have hregOh' : IsRegularRingHom (f.toRingHom.comp φh) :=
    ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
      (f.toRingHom.comp φh)).out 4 1).mp hOh'
  have hregf : IsRegularRingHom f.toRingHom :=
    ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
      f.toRingHom).out 4 1).mp hf
  have hflat : f.toRingHom.Flat := hregf.1
  have hff : f.toRingHom.FaithfullyFlat := by
    let : Algebra A A' := f.toRingHom.toAlgebra
    have : Module.Flat A A' := hflat
    have : IsLocalHom (algebraMap A A') := ‹IsLocalHom f.toRingHom›
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hsurj := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff).2
  have hregOh : IsRegularRingHom φh :=
    isRegularRingHom_of_comp_of_flat_of_surjectiveOnSpec φh f.toRingHom hregOh' hflat hsurj
  have hOh : FormallySmoothNAdic.{u} φh (maximalIdeal A) :=
    ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
      φh).out 1 4).mp hregOh
  have hO : FormallySmoothNAdic.{u} φO (maximalIdeal A) :=
    (formallySmoothNAdic_iff_of_comp_algebraMap_adicCompletion (maximalIdeal O)
      (maximalIdeal O).fg_of_isNoetherianRing (maximalIdeal A) _ _ hφh hOm).mpr hOh
  exact (formallySmoothNAdic_algebraMap_iff_of_isLocalization (R' := O) (A := A) p.primeCompl
    (maximalIdeal A)).mpr hO

end RingHom

end
