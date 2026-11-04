module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Smooth.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FormallySmooth.Topological

/-!
# Adic formal smoothness from the special fibre

For a local homomorphism `A → B` of Noetherian local rings, flatness together with adic formal
smoothness of the special fibre `k → k ⊗[A] B` (where `k` is the residue field of `A`) implies
that `A → B` itself is formally smooth for the `𝔪_B`-adic topology.

This is the implication (2) ⟹ (3) of Stacks Tag 07NQ. The reverse implication and the
equivalence with geometric regularity of the special fibre are not proved here; they need the
comparison of adic and topological formal smoothness for a *non-discrete* source, which is a
separate chain of tags. The implication proved here is self-contained, and it is the one that
supplies the substantive direction of Tag 09E7 for extensions of discrete valuation rings.

## Main results

* `RingHom.FormallySmoothNAdic.of_flat_of_specialFibre`: (2) ⟹ (3) of Tag 07NQ.
* `RingHom.FormallySmoothNAdic.of_algEquiv`: transport along an isomorphism of the target.
* `RingHom.formallySmoothNAdic_bot_iff`: for the zero ideal, adic formal smoothness is
  `Algebra.FormallySmooth`.

## Implementation notes

The proof is the usual two-step dévissage. `liftOfAnnihilated` solves a lifting problem whose
square-zero ideal is annihilated by `𝔪_A`, by descending it along a fibre product and using
Artin–Rees plus flatness to separate the kernel from the auxiliary ideal; the general case is
reduced to it by induction on the power of `𝔪_A` annihilating the ideal.

`formallySmoothNAdic_bot_iff` is stated at the test universe `max u v` because that is the
universe `Algebra.FormallySmooth.iff_comp_surjective` quantifies over: for `R : Type u` and
`S : Type v` the two notions agree exactly there.

## References

* [The Stacks Project, Tag 07NQ](https://stacks.math.columbia.edu/tag/07NQ)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

namespace RingHom

universe u v w

/-! ### Transport and the degenerate ideal -/

/-- For a surjection `f` of local rings, `𝔪ⁿ` is killed by `g` iff its preimage is killed by
`g ∘ f`. -/
private theorem maximalIdeal_pow_le_ker_comp_iff {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (hf : Function.Surjective f)
    (g : S →+* T) (n : ℕ) :
    maximalIdeal S ^ n ≤ RingHom.ker g ↔ maximalIdeal R ^ n ≤ RingHom.ker (g.comp f) := by
  rw [← map_maximalIdeal_of_surjective f hf, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  rfl

/-- Adic formal smoothness of a structure map transports along an isomorphism of the target. -/
theorem FormallySmoothNAdic.of_algEquiv.{t, uK, uC, uD}
    {K : Type uK} {C : Type uC} {D : Type uD} [CommRing K] [CommRing C] [CommRing D]
    [Algebra K C] [Algebra K D] [IsLocalRing C] [IsLocalRing D] (e : C ≃ₐ[K] D)
    (h : FormallySmoothNAdic.{t, uK, uC} (algebraMap K C) (maximalIdeal C)) :
    FormallySmoothNAdic.{t, uK, uD} (algebraMap K D) (maximalIdeal D) := by
  intro E _ J hJ a ψ hcomm hk
  have hcomm' : (ψ.comp e.toRingHom).comp (algebraMap K C) = (Ideal.Quotient.mk J).comp a := by
    ext r
    simpa using DFunLike.congr_fun hcomm r
  obtain ⟨n, hn, hk⟩ := hk
  obtain ⟨d, hd, hda⟩ := h E J hJ a (ψ.comp e.toRingHom) hcomm'
    ⟨n, hn, (maximalIdeal_pow_le_ker_comp_iff e.toRingHom e.surjective ψ n).mp hk⟩
  refine ⟨d.comp e.symm.toRingHom, ?_, ?_⟩
  · ext x
    simpa using DFunLike.congr_fun hd (e.symm x)
  · ext r
    simpa using DFunLike.congr_fun hda r

/-- For the zero ideal, formal smoothness for the adic topology is exactly
`Algebra.FormallySmooth`: the side condition "`ψ` kills a power of the ideal" is vacuous, so
the lifting property is the usual one against square-zero extensions. -/
theorem formallySmoothNAdic_bot_iff {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] :
    FormallySmoothNAdic.{max u v, u, v} (algebraMap R S) ⊥ ↔ Algebra.FormallySmooth R S := by
  constructor
  · intro h
    refine Algebra.FormallySmooth.iff_comp_surjective.mpr ?_
    intro T _ _ I hI ψ
    obtain ⟨g, hgmk, hgalg⟩ := h T I hI (algebraMap R T) ψ.toRingHom
      (by ext r; simp) ⟨1, le_rfl, by simp⟩
    refine ⟨{ g with commutes' := fun r => DFunLike.congr_fun hgalg r },
      AlgHom.ext fun x => ?_⟩
    exact DFunLike.congr_fun hgmk x
  · intro h T _ J hJ a ψ hcomm _
    let _ : Algebra R T := a.toAlgebra
    have hmk : algebraMap R (T ⧸ J) = (Ideal.Quotient.mk J).comp a := rfl
    let ψ' : S →ₐ[R] T ⧸ J :=
      { ψ with commutes' := fun r => by rw [hmk]; exact DFunLike.congr_fun hcomm r }
    obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R S J hJ ψ'
    exact ⟨g.toRingHom, by ext x; exact DFunLike.congr_fun hg x, by ext r; exact g.commutes r⟩

/-! ### The dévissage -/

/-- Two elements of a square-zero ideal multiply to zero. -/
private theorem mul_eq_zero_of_sq_eq_bot {R : Type*} [CommRing R] {L : Ideal R} (hL : L ^ 2 = ⊥)
    {x y : R} (hx : x ∈ L) (hy : y ∈ L) : x * y = 0 :=
  (Submodule.eq_bot_iff _).mp hL _ (pow_two L ▸ Ideal.mul_mem_mul hx hy)

/-- If the kernel of a surjection `π : E → B` meets an ideal `M` of `E` trivially, then a ring
map `B → E ⧸ M` compatible with `π` modulo `ker π` lifts to a section of `π`. -/
public theorem section_of_disjoint {E B : Type*} [CommRing E] [CommRing B]
    (π : E →+* B) (hπ : Function.Surjective π) (M : Ideal E)
    (hdisj : RingHom.ker π ⊓ M = ⊥) (σ : B →+* E ⧸ M)
    (hσ : ∀ e : E, Ideal.Quotient.mk ((RingHom.ker π).map (Ideal.Quotient.mk M)) (σ (π e)) =
      Ideal.Quotient.mk ((RingHom.ker π).map (Ideal.Quotient.mk M)) (Ideal.Quotient.mk M e)) :
    ∃ s : B →+* E, (∀ b, π (s b) = b) ∧ (∀ b, Ideal.Quotient.mk M (s b) = σ b) := by
  set q := Ideal.Quotient.mk M
  set L := (RingHom.ker π).map q
  let F : Subring ((E ⧸ M) × B) :=
    RingHom.eqLocus ((Ideal.Quotient.mk L).comp (RingHom.fst _ _))
      (((Ideal.Quotient.mk L).comp σ).comp (RingHom.snd _ _))
  let Φ : E →+* F := RingHom.codRestrict (q.prod π) F (fun e => (hσ e).symm)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro e he
    have h1 : q e = 0 := congrArg (fun x : F => x.1.1) he
    have h2 : π e = 0 := congrArg (fun x : F => x.1.2) he
    exact (Submodule.eq_bot_iff _).mp hdisj e ⟨h2, Ideal.Quotient.eq_zero_iff_mem.mp h1⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨⟨x, b⟩, hxb⟩
    obtain ⟨e₀, rfl⟩ := hπ b
    have hx : Ideal.Quotient.mk L x = Ideal.Quotient.mk L (q e₀) := by
      rw [← hσ e₀]; exact hxb
    rw [Ideal.Quotient.eq] at hx
    obtain ⟨l, hl, hlx⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hx
    refine ⟨e₀ + l, Subtype.ext ?_⟩
    show (q (e₀ + l), π (e₀ + l)) = (x, π e₀)
    rw [map_add, map_add, hlx, RingHom.mem_ker.mp hl]
    simp
  let e := RingEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let τ : B →+* F := RingHom.codRestrict (σ.prod (RingHom.id B)) F (fun _ => rfl)
  refine ⟨e.symm.toRingHom.comp τ, fun b => ?_, fun b => ?_⟩
  · exact congrArg (fun x : F => x.1.2) (e.apply_symm_apply (τ b))
  · exact congrArg (fun x : F => x.1.1) (e.apply_symm_apply (τ b))

/-- Solve a lifting problem whose square-zero ideal `L` is annihilated by the extended ideal
`I·E`, granted the lifting property `H` for test rings on which `I` acts as zero.

The lift is produced on the fibre product `D = E ×_{E ⧸ L} S`. Artin–Rees for `n` and `I·S`,
together with flatness of `S` over `R`, makes the kernel of `D → S` meet the auxiliary ideal
`I·D + (ker(D → E) ∩ n^j·D)` trivially, so `H` applied over `D ⧸ M` descends to a section. -/
private theorem liftOfAnnihilated.{u', v', w'}
    {R : Type w'} {S : Type v'} {E : Type (max u' v')}
    [CommRing R] [CommRing S] [CommRing E] [IsNoetherianRing S]
    [Algebra R S] [Module.Flat R S]
    (I : Ideal R) (n : Ideal S)
    (H : ∀ (T : Type (max u' v')) [CommRing T] (K : Ideal T), K ^ 2 = ⊥ →
      ∀ (α : R →+* T), I ≤ RingHom.ker α → ∀ (β : S →+* T ⧸ K),
        β.comp (algebraMap R S) = (Ideal.Quotient.mk K).comp α →
        (∃ j : ℕ, 1 ≤ j ∧ n ^ j ≤ RingHom.ker β) →
        ∃ γ : S →+* T, (Ideal.Quotient.mk K).comp γ = β ∧ γ.comp (algebraMap R S) = α)
    (L : Ideal E) (hL : L ^ 2 = ⊥) (a : R →+* E) (haL : I.map a * L = ⊥)
    (φ : S →+* E ⧸ L) (hcomm : φ.comp (algebraMap R S) = (Ideal.Quotient.mk L).comp a)
    (m : ℕ) (hm : 1 ≤ m) (hφ : n ^ m ≤ RingHom.ker φ) :
    ∃ g : S →+* E, (Ideal.Quotient.mk L).comp g = φ ∧ g.comp (algebraMap R S) = a := by
  classical
  let D : Subring (E × S) :=
    RingHom.eqLocus ((Ideal.Quotient.mk L).comp (RingHom.fst E S)) (φ.comp (RingHom.snd E S))
  have memD : ∀ x : E × S, x ∈ D ↔ Ideal.Quotient.mk L x.1 = φ x.2 := fun _ => Iff.rfl
  let π : D →+* S := (RingHom.snd E S).comp D.subtype
  let π₁ : D →+* E := (RingHom.fst E S).comp D.subtype
  let ρ : R →+* D := RingHom.codRestrict (a.prod (algebraMap R S)) D
    (fun r => (DFunLike.congr_fun hcomm r).symm)
  have hπρ : π.comp ρ = algebraMap R S := rfl
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (φ s)
    exact ⟨⟨(e, s), he⟩, rfl⟩
  have hzeroD : ∀ t : S, t ∈ n ^ m → (((0 : E), t) ∈ D) := by
    intro t ht
    rw [memD, map_zero]
    exact (RingHom.mem_ker.mp (hφ ht)).symm
  have hkerL : ∀ x : D, x ∈ RingHom.ker π → x.1.1 ∈ L := by
    intro x hx
    have h2 : x.1.2 = 0 := hx
    have hmem := (memD x.1).mp x.2
    rw [h2, map_zero] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem
  have hflatD : RingHom.ker π ⊓ I.map ρ = ⊥ := by
    let _ : Algebra R D := ρ.toAlgebra
    let πₗ : D →ₗ[R] S :=
      { toFun := π
        map_add' := π.map_add
        map_smul' := fun r x => by
          show π (r • x) = r • π x
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          rfl }
    have key := LinearMap.ker_inf_smul_top_eq_smul_of_flat I πₗ hπ
    have hzero : I • LinearMap.ker πₗ = ⊥ := by
      rw [eq_bot_iff]
      apply Submodule.smul_le.mpr
      intro i hi x hx
      have hx1 : x.1.1 ∈ L := hkerL x hx
      have hx2 : x.1.2 = 0 := hx
      show ρ i * x ∈ (⊥ : Submodule R D)
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply Prod.ext
      · show a i * x.1.1 = 0
        exact (Submodule.eq_bot_iff _).mp haL _ (Ideal.mul_mem_mul (Ideal.mem_map_of_mem a hi) hx1)
      · show algebraMap R S i * x.1.2 = 0
        rw [hx2, mul_zero]
    rw [hzero, Ideal.smul_top_eq_map] at key
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ LinearMap.ker πₗ ⊓ (I.map (algebraMap R D)).restrictScalars R := ⟨hx.1, hx.2⟩
    rw [key] at hx'
    exact hx'
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul n (I.map (algebraMap R S) : Submodule S S)
  set j := m + c with hj
  have hAR : n ^ j ⊓ I.map (algebraMap R S) ≤ n ^ m * I.map (algebraMap R S) := by
    have h := hc j (by omega)
    have hjc : j - c = m := by omega
    rw [hjc] at h
    intro x hx
    have hx' : x ∈ n ^ j • (⊤ : Submodule S S) ⊓
        (I.map (algebraMap R S) : Submodule S S) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hx
    rw [h] at hx'
    exact Submodule.smul_mono le_rfl inf_le_right hx'
  have hgen : n ^ m * I.map (algebraMap R S) ≤ (I.map ρ ⊓ RingHom.ker π₁).map π := by
    rw [Ideal.mul_le]
    intro t ht w hw
    have hw' : w ∈ (I.map ρ).map π := by rwa [Ideal.map_map, hπρ]
    obtain ⟨y₀, hy₀, rfl⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hw'
    let t' : D := ⟨(0, t), hzeroD t ht⟩
    have hmul : π (t' * y₀) = t * π y₀ := by rw [map_mul]; rfl
    rw [← hmul]
    refine Ideal.mem_map_of_mem π ⟨Ideal.mul_mem_left _ _ hy₀, ?_⟩
    show (0 : E) * y₀.1.1 = 0
    rw [zero_mul]
  let N : Ideal D := RingHom.ker π₁ ⊓ (n ^ j).comap π
  let M : Ideal D := I.map ρ ⊔ N
  have hdisj : RingHom.ker π ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxM⟩
    obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.mp hxM
    have hπy : π y ∈ n ^ j ⊓ I.map (algebraMap R S) := by
      constructor
      · have h0 : π y + π u = 0 := by rw [← map_add]; exact hx
        rw [eq_neg_of_add_eq_zero_left h0]
        exact neg_mem hu.2
      · have hmem := Ideal.mem_map_of_mem π hy
        rwa [Ideal.map_map, hπρ] at hmem
    obtain ⟨y', ⟨hy'I, hy'1⟩, hy'π⟩ :=
      (Ideal.mem_map_iff_of_surjective π hπ).mp (hgen (hAR hπy))
    have hyy' : y = y' := by
      exact sub_eq_zero.mp <| (Submodule.eq_bot_iff _).mp hflatD _
        ⟨by change π (y - y') = 0; rw [map_sub, hy'π, sub_self], sub_mem hy hy'I⟩
    subst hyy'
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply Prod.ext
    · show y.1.1 + u.1.1 = 0
      rw [show y.1.1 = 0 from hy'1, show u.1.1 = 0 from hu.1, add_zero]
    · exact hx
  let K : Ideal (D ⧸ M) := (RingHom.ker π).map (Ideal.Quotient.mk M)
  have hK : K ^ 2 = ⊥ := by
    have hker : RingHom.ker π ^ 2 = ⊥ := by
      rw [eq_bot_iff, pow_two, Ideal.mul_le]
      intro x hx y hy
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply Prod.ext
      · show x.1.1 * y.1.1 = 0
        exact mul_eq_zero_of_sq_eq_bot hL (hkerL x hx) (hkerL y hy)
      · show x.1.2 * y.1.2 = 0
        rw [show x.1.2 = 0 from hx, zero_mul]
    show ((RingHom.ker π).map (Ideal.Quotient.mk M)) ^ 2 = ⊥
    rw [← Ideal.map_pow, hker, Ideal.map_bot]
  let α : R →+* D ⧸ M := (Ideal.Quotient.mk M).comp ρ
  have hαI : I ≤ RingHom.ker α := by
    intro i hi
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem ρ hi))
  let β : S →+* (D ⧸ M) ⧸ K := π.liftOfSurjective hπ
    ⟨(Ideal.Quotient.mk K).comp (Ideal.Quotient.mk M), fun x hx => by
      rw [RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)⟩
  have hβ : ∀ x : D, β (π x) = Ideal.Quotient.mk K (Ideal.Quotient.mk M x) := fun x =>
    RingHom.liftOfSurjective_comp_apply π hπ _ x
  have hβf : β.comp (algebraMap R S) = (Ideal.Quotient.mk K).comp α := by
    ext r
    exact hβ (ρ r)
  have hβn : n ^ j ≤ RingHom.ker β := by
    intro t ht
    have htm : t ∈ n ^ m := Ideal.pow_le_pow_right (by omega) ht
    let t' : D := ⟨(0, t), hzeroD t htm⟩
    have ht'M : t' ∈ M := Ideal.mem_sup_right ⟨rfl, ht⟩
    rw [RingHom.mem_ker]
    show β (π t') = 0
    rw [hβ, Ideal.Quotient.eq_zero_iff_mem.mpr ht'M, map_zero]
  obtain ⟨γ, hγK, hγf⟩ := H (D ⧸ M) K hK α hαI β hβf ⟨j, by omega, hβn⟩
  obtain ⟨s, hsπ, hsM⟩ := section_of_disjoint π hπ M hdisj γ (fun e => by
    rw [← hβ e, ← hγK]; rfl)
  have hsf : ∀ r, s (algebraMap R S r) = ρ r := by
    intro r
    have hmem : s (algebraMap R S r) - ρ r ∈ RingHom.ker π ⊓ M := by
      constructor
      · show π (s (algebraMap R S r) - ρ r) = 0
        rw [map_sub, hsπ]
        exact sub_self _
      · apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, hsM, ← RingHom.comp_apply γ (algebraMap R S), hγf]
        exact sub_self _
    exact sub_eq_zero.mp ((Submodule.eq_bot_iff _).mp hdisj _ hmem)
  refine ⟨π₁.comp s, ?_, ?_⟩
  · ext t
    show Ideal.Quotient.mk L (s t).1.1 = φ t
    rw [(memD (s t).1).mp (s t).2]
    exact congrArg φ (hsπ t)
  · ext r
    show (s (algebraMap R S r)).1.1 = a r
    rw [hsf r]
    rfl

/-- A lifting problem for `f : A → B` whose test map kills `𝔪_A` factors through the special
fibre `k ⊗[A] B`, so adic formal smoothness of the special fibre solves it. -/
private theorem liftThroughSpecialFibre.{u', v'}
    {A : Type u'} {B : Type v'}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hbar : FormallySmoothNAdic.{max u' v'}
      (algebraMap (ResidueField A) (ResidueField A ⊗[A] B))
      (maximalIdeal (ResidueField A ⊗[A] B)))
    (T : Type (max u' v')) [CommRing T] (K : Ideal T) (hK : K ^ 2 = ⊥)
    (α : A →+* T) (hα : maximalIdeal A ≤ RingHom.ker α) (β : B →+* T ⧸ K)
    (hβf : β.comp (algebraMap A B) = (Ideal.Quotient.mk K).comp α)
    (hβn : ∃ j : ℕ, 1 ≤ j ∧ maximalIdeal B ^ j ≤ RingHom.ker β) :
    ∃ γ : B →+* T, (Ideal.Quotient.mk K).comp γ = β ∧ γ.comp (algebraMap A B) = α := by
  let k := ResidueField A
  let Bbar := k ⊗[A] B
  let incl : B →+* Bbar := Algebra.TensorProduct.includeRight.toRingHom
  have hincl : Function.Surjective incl :=
    TensorProduct.mk_surjective A B k residue_surjective
  have hker : RingHom.ker incl ≤ RingHom.ker β := by
    intro b hb
    have hb' : b ∈ (maximalIdeal A).map (algebraMap A B) := by
      let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)
      have h0 : e (Ideal.Quotient.mk _ b) = 0 := by
        rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
        exact hb
      exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h0)
    have hle : (maximalIdeal A).map (algebraMap A B) ≤ RingHom.ker β := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      show β (algebraMap A B x) = 0
      rw [← RingHom.comp_apply, hβf, RingHom.comp_apply, RingHom.mem_ker.mp (hα hx), map_zero]
    exact hle hb'
  let βbar : Bbar →+* T ⧸ K := incl.liftOfSurjective hincl ⟨β, hker⟩
  have hβbar : ∀ b, βbar (incl b) = β b := fun b =>
    RingHom.liftOfSurjective_comp_apply incl hincl ⟨β, hker⟩ b
  let αbar : k →+* T := Ideal.Quotient.lift (maximalIdeal A) α hα
  have halg : ∀ x : A, algebraMap k Bbar (residue A x) = incl (algebraMap A B x) := by
    intro x
    show (residue A x) ⊗ₜ[A] (1 : B) = (1 : k) ⊗ₜ[A] (algebraMap A B x)
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  have hcomm : βbar.comp (algebraMap k Bbar) = (Ideal.Quotient.mk K).comp αbar := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    show βbar (algebraMap k Bbar (residue A x)) = Ideal.Quotient.mk K (α x)
    rw [halg, hβbar, ← RingHom.comp_apply, hβf, RingHom.comp_apply]
  obtain ⟨j, hj, hjle⟩ := hβn
  have hpow : maximalIdeal Bbar ^ j ≤ RingHom.ker βbar := by
    rw [maximalIdeal_pow_le_ker_comp_iff incl hincl, show βbar.comp incl = β from RingHom.ext hβbar]
    exact hjle
  obtain ⟨γbar, hγK, hγk⟩ := hbar T K hK αbar βbar hcomm ⟨j, hj, hpow⟩
  refine ⟨γbar.comp incl, ?_, ?_⟩
  · ext b
    show Ideal.Quotient.mk K (γbar (incl b)) = β b
    rw [← hβbar, ← hγK]
    rfl
  · ext x
    show γbar (incl (algebraMap A B x)) = α x
    rw [← halg, ← RingHom.comp_apply γbar, hγk]
    rfl

/-- **Stacks 07NQ, (2) ⟹ (3).** A flat local homomorphism of Noetherian local rings whose
special fibre is adically formally smooth over the residue field of the source is itself formally
smooth for the maximal-ideal-adic topology. -/
@[stacks 07NQ "(2) ⟹ (3)", ega "0 19.0.2" "I, one direction", ega "0 19.7.1" "b) ⇒ a)", sga
  "1 III 1.7" "if direction", sga "1 III 1.7" "if direction"]
theorem FormallySmoothNAdic.of_flat_of_specialFibre
    (A : Type u) (B : Type v)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hbar : FormallySmoothNAdic.{max u v}
      (algebraMap (ResidueField A) (ResidueField A ⊗[A] B))
      (maximalIdeal (ResidueField A ⊗[A] B))) :
    FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B) := by
  let I := maximalIdeal A
  let n := maximalIdeal B
  have H : ∀ (T : Type (max u v)) [CommRing T] (K : Ideal T), K ^ 2 = ⊥ →
      ∀ (α : A →+* T), I ≤ RingHom.ker α → ∀ (β : B →+* T ⧸ K),
        β.comp (algebraMap A B) = (Ideal.Quotient.mk K).comp α →
        (∃ j : ℕ, 1 ≤ j ∧ n ^ j ≤ RingHom.ker β) →
        ∃ γ : B →+* T, (Ideal.Quotient.mk K).comp γ = β ∧
          γ.comp (algebraMap A B) = α :=
    fun T _ K hK α hα β hβf hβn => liftThroughSpecialFibre hbar T K hK α hα β hβf hβn
  -- Induct on the power of `𝔪_A` annihilating the square-zero ideal.
  have step : ∀ t : ℕ, ∀ (E : Type (max u v)) [CommRing E] (L : Ideal E), L ^ 2 = ⊥ →
      ∀ (a : A →+* E) (φ : B →+* E ⧸ L),
        φ.comp (algebraMap A B) = (Ideal.Quotient.mk L).comp a →
        (∃ m : ℕ, 1 ≤ m ∧ n ^ m ≤ RingHom.ker φ) → (I.map a) ^ (t + 1) * L = ⊥ →
        ∃ g : B →+* E, (Ideal.Quotient.mk L).comp g = φ ∧
          g.comp (algebraMap A B) = a := by
    intro t
    induction t with
    | zero =>
      intro E _ L hL a φ hcomm ⟨m, hm, hφ⟩ hann
      rw [zero_add, pow_one] at hann
      exact liftOfAnnihilated.{u} I n H L hL a hann φ hcomm m hm hφ
    | succ t ih =>
      intro E _ L hL a φ hcomm ⟨m, hm, hφ⟩ hann
      let L' : Ideal E := (I.map a) ^ (t + 1) * L
      have hL'L : L' ≤ L := Ideal.mul_le_right
      have hL'2 : L' ^ 2 = ⊥ := eq_bot_iff.mpr (hL ▸ Ideal.pow_right_mono hL'L 2)
      have hIL' : I.map a * L' = ⊥ := by
        rw [← hann, ← mul_assoc, ← pow_succ']
      let L₁ : Ideal (E ⧸ L') := L.map (Ideal.Quotient.mk L')
      let eq := DoubleQuot.quotQuotEquivQuotOfLE hL'L
      have heq : ∀ x : E, eq (Ideal.Quotient.mk L₁ (Ideal.Quotient.mk L' x)) =
          Ideal.Quotient.mk L x := fun x => DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x hL'L
      let a' : A →+* E ⧸ L' := (Ideal.Quotient.mk L').comp a
      let φ' : B →+* (E ⧸ L') ⧸ L₁ := eq.symm.toRingHom.comp φ
      have hL₁ : L₁ ^ 2 = ⊥ := by
        show (L.map (Ideal.Quotient.mk L')) ^ 2 = ⊥
        rw [← Ideal.map_pow, hL, Ideal.map_bot]
      have hcomm' : φ'.comp (algebraMap A B) = (Ideal.Quotient.mk L₁).comp a' := by
        ext r
        show eq.symm (φ (algebraMap A B r)) =
          Ideal.Quotient.mk L₁ (Ideal.Quotient.mk L' (a r))
        rw [eq.symm_apply_eq, heq, ← RingHom.comp_apply, hcomm, RingHom.comp_apply]
      have hφ' : n ^ m ≤ RingHom.ker φ' := by
        intro x hx
        show eq.symm (φ x) = 0
        rw [RingHom.mem_ker.mp (hφ hx), map_zero]
      have hann' : (I.map a') ^ (t + 1) * L₁ = ⊥ := by
        show (I.map ((Ideal.Quotient.mk L').comp a)) ^ (t + 1) *
          L.map (Ideal.Quotient.mk L') = ⊥
        rw [← Ideal.map_map, ← Ideal.map_pow, ← Ideal.map_mul]
        exact Ideal.map_quotient_self L'
      obtain ⟨g', hg'K, hg'f⟩ := ih (E ⧸ L') L₁ hL₁ a' φ' hcomm' ⟨m, hm, hφ'⟩ hann'
      have hg'n : n ^ (m + m) ≤ RingHom.ker g' := by
        have h1 : n ^ m ≤ L₁.comap g' := by
          intro x hx
          rw [Ideal.mem_comap]
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          show ((Ideal.Quotient.mk L₁).comp g') x = 0
          rw [hg'K]
          exact hφ' hx
        rw [pow_add, Ideal.mul_le]
        intro x hx y hy
        rw [RingHom.mem_ker, map_mul]
        exact mul_eq_zero_of_sq_eq_bot hL₁ (h1 hx) (h1 hy)
      obtain ⟨g, hgK, hgf⟩ := liftOfAnnihilated.{u} I n H L' hL'2 a hIL' g' hg'f
        (m + m) (by omega) hg'n
      refine ⟨g, ?_, hgf⟩
      ext x
      show Ideal.Quotient.mk L (g x) = φ x
      rw [← heq, ← RingHom.comp_apply (Ideal.Quotient.mk L'), hgK]
      show eq ((Ideal.Quotient.mk L₁).comp g' x) = φ x
      rw [hg'K]
      exact eq.apply_symm_apply (φ x)
  intro E _ J hJ a ψ hcomm ⟨m, hm, hk⟩
  have hIm : (I ^ m).map a ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    show ((Ideal.Quotient.mk J).comp a) x = 0
    rw [← hcomm]
    apply hk
    have hpow : (I ^ m).map (algebraMap A B) ≤ n ^ m := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (map_maximalIdeal_le (algebraMap A B)) m
    exact hpow (Ideal.mem_map_of_mem (algebraMap A B) hx)
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  apply step t E J hJ a ψ hcomm ⟨t + 1, hm, hk⟩
  rw [Ideal.map_pow] at hIm
  rw [eq_bot_iff, ← hJ, pow_two]
  exact Ideal.mul_mono_left hIm

end RingHom
