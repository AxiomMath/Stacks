module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus

/-!
# Flat models of finite type over `ℤ`

Maps out of finitely presented algebras and modules into a directed colimit factor through a stage
(the elementwise form of Stacks 00QO and 05LI); in the directed system of finite type models of
Stacks 00R1 the module becomes flat over the base at some stage; and parts (1) and (2) of
Stacks 02JO.

## Main results

* `AlgHom.exists_comp_eq_of_finitePresentation`, `LinearMap.exists_comp_eq_of_finitePresentation`
* `Algebra.FiniteTypeSystem.exists_flat_stage`
* `Module.Flat.exists_finiteType_model`: Stacks 02JO (1).
* `Module.Flat.exists_finitePresentation_model_of_directed`: Stacks 02JO (2).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- A finite family in a directed preorder has a common upper bound above any given index. -/
private theorem exists_ge_forall_le {ι α : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (t : Finset α) (k : α → ι) (i₀ : ι) : ∃ j, i₀ ≤ j ∧ ∀ a ∈ t, k a ≤ j := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨j, hj⟩ := (insert i₀ (t.image k)).exists_le
  exact ⟨j, hj _ (Finset.mem_insert_self _ _),
    fun a ha => hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha))⟩

/-- **Maps out of a finitely presented algebra factor through a stage of a directed colimit.**
Let `R` be the directed colimit of `A`-algebras `G i` (every element of `R` comes from a stage, and
an element of a stage dying in `R` dies at a later stage). Then every `A`-algebra map `C → R` with
`C` of finite presentation over `A` factors through some `G i`. This is the elementwise form of
Stacks 00QO. -/
theorem AlgHom.exists_comp_eq_of_finitePresentation {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.FinitePresentation A C] {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] {G : ι → Type*} [∀ i, CommRing (G i)] [∀ i, Algebra A (G i)]
    (f : ∀ i j, i ≤ j → G i →ₐ[A] G j) [DirectedSystem G fun i j h => f i j h]
    {R : Type*} [CommRing R] [Algebra A R] (g : ∀ i, G i →ₐ[A] R)
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x) (hs : ∀ r, ∃ i x, g i x = r)
    (hz : ∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) (w : C →ₐ[A] R) :
    ∃ i, ∃ ψ : C →ₐ[A] G i, (g i).comp ψ = w := by
  classical
  obtain ⟨n, π, hπ, E, hE⟩ := Algebra.FinitePresentation.out (R := A) (A := C)
  choose k z hz' using fun m : Fin n => hs (w (π (MvPolynomial.X m)))
  obtain ⟨i₀, -, hk'⟩ := exists_ge_forall_le Finset.univ k (Classical.arbitrary _)
  have hk (m : Fin n) : k m ≤ i₀ := hk' m (Finset.mem_univ m)
  let φ (j : ι) (h : i₀ ≤ j) : MvPolynomial (Fin n) A →ₐ[A] G j :=
    MvPolynomial.aeval fun m => f i₀ j h (f (k m) i₀ (hk m) (z m))
  have hφ (j : ι) (h : i₀ ≤ j) : (g j).comp (φ j h) = w.comp π := by
    refine MvPolynomial.algHom_ext fun m => ?_
    simp [φ, hg, hz']
  have hφf {j l : ι} (h : i₀ ≤ j) (h' : j ≤ l) :
      (f j l h').comp (φ j h) = φ l (h.trans h') := by
    refine MvPolynomial.algHom_ext fun m => ?_
    simp [φ, DirectedSystem.map_map' (fun i j h => f i j h)]
  have hE0 (e : MvPolynomial (Fin n) A) (he : e ∈ E) :
      ∃ j, ∃ h : i₀ ≤ j, φ j h e = 0 := by
    have hπe : π e = 0 := by
      have he' : e ∈ RingHom.ker π.toRingHom := hE ▸ Ideal.subset_span he
      simpa using RingHom.mem_ker.mp he'
    obtain ⟨j, h, hj⟩ := hz i₀ (φ i₀ le_rfl e) (by
      rw [← AlgHom.comp_apply, hφ, AlgHom.comp_apply, hπe, map_zero])
    exact ⟨j, h, by rw [← hφf le_rfl h, AlgHom.comp_apply, hj]⟩
  choose! l hl hl' using hE0
  obtain ⟨j, hi₀j, hlj⟩ := exists_ge_forall_le E l i₀
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker (φ j hi₀j).toRingHom := by
    rw [← hE, Ideal.span_le]
    intro e he
    rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ← hφf (hl e he) (hlj e he), AlgHom.comp_apply, hl' e he, map_zero]
  refine ⟨j, AlgHom.liftOfSurjective π hπ (φ j hi₀j) hker, ?_⟩
  refine AlgHom.ext fun c => ?_
  obtain ⟨p, rfl⟩ := hπ c
  rw [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply, ← AlgHom.comp_apply, hφ,
    AlgHom.comp_apply]

/-- **Maps out of a finitely presented module factor through a stage of a directed colimit.**
Let `Y` be the directed colimit of `K`-modules `Q j`. Then every `K`-linear map `P → Y` with `P`
finitely presented factors through some `Q j`. -/
theorem LinearMap.exists_comp_eq_of_finitePresentation {K P : Type*} [CommRing K]
    [AddCommGroup P] [Module K P] [Module.FinitePresentation K P] {J : Type*} [Preorder J]
    [Nonempty J] [IsDirected J (· ≤ ·)] {Q : J → Type*} [∀ j, AddCommGroup (Q j)]
    [∀ j, Module K (Q j)] (q : ∀ j k, j ≤ k → Q j →ₗ[K] Q k)
    [DirectedSystem Q fun j k h => q j k h] {Y : Type*} [AddCommGroup Y] [Module K Y]
    (ν : ∀ j, Q j →ₗ[K] Y) (hν : ∀ j k (h : j ≤ k) x, ν k (q j k h x) = ν j x)
    (hs : ∀ y, ∃ j x, ν j x = y) (hz : ∀ j x, ν j x = 0 → ∃ k, ∃ h : j ≤ k, q j k h x = 0)
    (w : P →ₗ[K] Y) : ∃ j, ∃ ψ : P →ₗ[K] Q j, ν j ∘ₗ ψ = w := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' K P
  obtain ⟨E, hE⟩ := Module.FinitePresentation.fg_ker π hπ
  choose k z hz' using fun m : Fin n => hs (w (π (Pi.single m 1)))
  obtain ⟨i₀, -, hk'⟩ := exists_ge_forall_le Finset.univ k (Classical.arbitrary _)
  have hk (m : Fin n) : k m ≤ i₀ := hk' m (Finset.mem_univ m)
  let φ (j : J) (h : i₀ ≤ j) : (Fin n → K) →ₗ[K] Q j :=
    Fintype.linearCombination K fun m => q i₀ j h (q (k m) i₀ (hk m) (z m))
  have hφ (j : J) (h : i₀ ≤ j) : ν j ∘ₗ φ j h = w ∘ₗ π := by
    refine LinearMap.pi_ext' fun m => LinearMap.ext_ring ?_
    simp [φ, Fintype.linearCombination_apply, Pi.single_apply, hν, hz']
  have hφq {j l : J} (h : i₀ ≤ j) (h' : j ≤ l) : q j l h' ∘ₗ φ j h = φ l (h.trans h') := by
    refine LinearMap.pi_ext' fun m => LinearMap.ext_ring ?_
    simp [φ, Fintype.linearCombination_apply, Pi.single_apply,
      DirectedSystem.map_map' (fun i j h => q i j h)]
  have hE0 (e : Fin n → K) (he : e ∈ E) : ∃ j, ∃ h : i₀ ≤ j, φ j h e = 0 := by
    have hπe : π e = 0 := LinearMap.mem_ker.mp (hE ▸ Submodule.subset_span he)
    obtain ⟨j, h, hj⟩ := hz i₀ (φ i₀ le_rfl e) (by
      rw [← LinearMap.comp_apply, hφ, LinearMap.comp_apply, hπe, map_zero])
    exact ⟨j, h, by rw [← hφq le_rfl h, LinearMap.comp_apply, hj]⟩
  choose! l hl hl' using hE0
  obtain ⟨j, hi₀j, hlj⟩ := exists_ge_forall_le E l i₀
  have hker : LinearMap.ker π ≤ LinearMap.ker (φ j hi₀j) := by
    rw [← hE, Submodule.span_le]
    intro e he
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hφq (hl e he) (hlj e he), LinearMap.comp_apply,
      hl' e he, map_zero]
  refine ⟨j, (LinearMap.ker π).liftQ (φ j hi₀j) hker ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, LinearMap.ext fun p => ?_⟩
  obtain ⟨x, rfl⟩ := hπ p
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply, ← LinearMap.comp_apply,
    hφ, LinearMap.comp_apply]

namespace Algebra.FiniteTypeSystem

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Ideal

variable {R : Type u} [CommRing R] (R₀ : Subring R) (S₀ : Type u) [CommRing S₀] [Algebra R₀ S₀]
  {S : Type u} [CommRing S] [Algebra R S] [Algebra S₀ S] [IsScalarTower R₀ S₀ S]
  [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀] [Algebra.IsPushout R₀ R S₀ S]

/-- An ideal of `S_λ` which generates the unit ideal of `S` already generates the unit ideal of
some `S_μ`, `μ ≥ λ`. -/
theorem exists_map_ringMap_eq_top {i : Index R₀} (I : Ideal (Ring R₀ S₀ i))
    (hI : I.map (algebraMap (Ring R₀ S₀ i) S) = ⊤) :
    ∃ (j : Index R₀) (h : i ≤ j), I.map (ringMap R₀ S₀ h).toRingHom = ⊤ := by
  classical
  have : IsNoetherianRing (Base R₀ i) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsNoetherianRing (Ring R₀ S₀ i) := Algebra.FiniteType.isNoetherianRing (Base R₀ i) _
  obtain ⟨s, rfl⟩ := (IsNoetherian.noetherian I : I.FG)
  rw [Ideal.map_span, Set.image_eq_range] at hI
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hI ▸ Submodule.mem_top (x := 1))
  choose k d hd using fun x : s => (ring_colimit R₀ S₀ (S := S)).1 (c x)
  obtain ⟨j, hij, hkj⟩ := exists_ge_forall_le Finset.univ k i
  have hkj' (x : s) : k x ≤ j := hkj x (Finset.mem_univ x)
  let z : Ring R₀ S₀ j := ∑ x : s, ringMap R₀ S₀ (hkj' x) (d x) * ringMap R₀ S₀ hij x
  have hz : ringToRing R₀ S₀ (S := S) j z = ringToRing R₀ S₀ (S := S) j 1 := by
    simp only [z, map_sum, map_mul, ring_cocone, map_one, hd]
    exact hc
  obtain ⟨l, hjl, hl⟩ := (ring_colimit R₀ S₀ (S := S)).2 j z 1 hz
  refine ⟨l, hij.trans hjl, (Ideal.eq_top_iff_one _).mpr ?_⟩
  rw [map_one] at hl
  rw [← hl]
  simp only [z, map_sum, map_mul]
  refine Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_
  rw [DirectedSystem.map_map' (fun _ _ h => ringMap R₀ S₀ h)]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span x.2)

end Ideal

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (R₀ : Subring R) (S₀ P : Type u) [CommRing S₀] [Algebra R₀ S₀] [Algebra S₀ S]
  [IsScalarTower R₀ S₀ S] [AddCommGroup P] [Module S₀ P] [Module.Finite S₀ P]
  [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀] [Algebra.IsPushout R₀ R S₀ S]

/-- The flat locus of `S_λ ⊗_{S₀} P` over `R_λ`: the primes `p` of `S_λ` at which
`(S_λ)_p ⊗_{S₀} P` is flat over `R_λ`. -/
def flatLocus (i : Index R₀) : Set (PrimeSpectrum (Ring R₀ S₀ i)) :=
  {p | Module.Flat (Base R₀ i) (Localization.AtPrime p.asIdeal ⊗[S₀] P)}

omit [Algebra.FiniteType ℤ R₀] in
/-- The flat locus is open, by 00RC over the Noetherian ring `R_λ`. -/
theorem isOpen_flatLocus (i : Index R₀) :
    IsOpen (flatLocus R₀ S₀ P i) := by
  have : IsNoetherianRing (Base R₀ i) := Algebra.FiniteType.isNoetherianRing ℤ _
  have e : flatLocus R₀ S₀ P i = {p | Module.Flat (Base R₀ i)
      (LocalizedModule.AtPrime p.asIdeal (Ring R₀ S₀ i ⊗[S₀] P))} :=
    Set.ext fun p => (Module.flat_localizedModule_atPrime_iff_of_isBaseChange
      (TensorProduct.mk S₀ (Ring R₀ S₀ i) P 1) (TensorProduct.isBaseChange S₀ P _) p.asIdeal).symm
  rw [e]
  exact Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing

omit [Module.Finite S₀ P] [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀] in
/-- The flat loci increase along the system. -/
theorem mem_flatLocus_of_le {i j : Index R₀} (h : i ≤ j) (p : PrimeSpectrum (Ring R₀ S₀ j))
    (hp : PrimeSpectrum.comap (ringMap R₀ S₀ h).toRingHom p ∈ flatLocus R₀ S₀ P i) :
    p ∈ flatLocus R₀ S₀ P j :=
  flat_localized_of_le R₀ S₀ P h p.asIdeal hp

omit [Module.Finite S₀ P] [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀]
  [Algebra.IsPushout R₀ R S₀ S] in
/-- The primes of the stages under a prime of `S` are compatible with the transition maps. -/
theorem comap_ringMap_comap {i j : Index R₀} (h : i ≤ j) (q : PrimeSpectrum S) :
    PrimeSpectrum.comap (ringMap R₀ S₀ h).toRingHom
      (PrimeSpectrum.comap (algebraMap (Ring R₀ S₀ j) S) q) =
      PrimeSpectrum.comap (algebraMap (Ring R₀ S₀ i) S) q := by
  rw [← PrimeSpectrum.comap_comp_apply]
  exact congrArg (PrimeSpectrum.comap · q) (RingHom.ext fun x => ring_cocone R₀ S₀ h x)

/-- **The flat stage.** If `S_q ⊗_{S₀} P` is flat over `R` for every prime `q` of `S`, then
`S_λ ⊗_{S₀} P` is flat over `R_λ` for some `λ`. -/
theorem exists_flat_stage
    (hflat : ∀ q : PrimeSpectrum S, Module.Flat R (Localization.AtPrime q.asIdeal ⊗[S₀] P)) :
    ∃ i, Module.Flat (Base R₀ i) (Ring R₀ S₀ i ⊗[S₀] P) := by
  let V : Index R₀ → Set (PrimeSpectrum S) := fun i =>
    PrimeSpectrum.comap (algebraMap (Ring R₀ S₀ i) S) ⁻¹' flatLocus R₀ S₀ P i
  have hmono : Monotone V := fun i j h q hq =>
    mem_flatLocus_of_le R₀ S₀ P h _ (by rwa [comap_ringMap_comap])
  obtain ⟨i₀, hi₀⟩ := isCompact_univ.elim_directed_cover V
    (fun i => (isOpen_flatLocus R₀ S₀ P i).preimage (PrimeSpectrum.continuous_comap _))
    (fun q _ => Set.mem_iUnion.mpr (exists_flat_localized_stage R₀ S₀ P q.asIdeal (hflat q)))
    hmono.directed_le
  let I := PrimeSpectrum.vanishingIdeal (flatLocus R₀ S₀ P i₀)ᶜ
  have hZ : PrimeSpectrum.zeroLocus I = (flatLocus R₀ S₀ P i₀)ᶜ := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      (isOpen_flatLocus R₀ S₀ P i₀).isClosed_compl.closure_eq]
  have hI : I.map (algebraMap (Ring R₀ S₀ i₀) S) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hq : PrimeSpectrum.comap (algebraMap (Ring R₀ S₀ i₀) S) ⟨m, hm.isPrime⟩ ∈
        PrimeSpectrum.zeroLocus I := Ideal.map_le_iff_le_comap.mp hle
    rw [hZ] at hq
    exact hq (hi₀ (Set.mem_univ _))
  obtain ⟨j, hij, hj⟩ := exists_map_ringMap_eq_top R₀ S₀ I hI
  refine ⟨j, Module.flat_of_isLocalized_maximal (Ring R₀ S₀ j) _
    (fun p _ => LocalizedModule.AtPrime p (Ring R₀ S₀ j ⊗[S₀] P))
    (fun p _ => LocalizedModule.mkLinearMap p.primeCompl _) fun p hp => ?_⟩
  have hmem : (⟨p, hp.isPrime⟩ : PrimeSpectrum (Ring R₀ S₀ j)) ∈ flatLocus R₀ S₀ P j := by
    refine mem_flatLocus_of_le R₀ S₀ P hij _ (by_contra fun hZp => ?_)
    rw [← Set.mem_compl_iff, ← hZ] at hZp
    have : I.map (ringMap R₀ S₀ hij).toRingHom ≤ p := Ideal.map_le_iff_le_comap.mpr hZp
    exact hp.ne_top (top_le_iff.mp (hj ▸ this))
  exact (Module.flat_localizedModule_atPrime_iff_of_isBaseChange
    (TensorProduct.mk S₀ (Ring R₀ S₀ j) P 1) (TensorProduct.isBaseChange S₀ P _) p).mpr hmem

end Algebra.FiniteTypeSystem

open Algebra.FiniteTypeSystem in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 02JO (1).** Let `R → S` be of finite presentation and let `M` be a finitely
presented `S`-module which is flat over `R`. Then there are a ring `R₀` of finite type over `ℤ`,
an `R₀`-algebra `S₀` of finite type and a finite `S₀`-module `M₀` flat over `R₀`, together with
ring maps `R₀ → R`, `S₀ → S` and an `S₀`-linear map `M₀ → M`, such that `S = R ⊗_{R₀} S₀` and
`M = S ⊗_{S₀} M₀`. -/
@[stacks 02JO "(1)"]
theorem Module.Flat.exists_finiteType_model {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (M : Type w) [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M] [Module.Flat R M] :
    ∃ (R₀ S₀ M₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
      (_ : Algebra R₀ R) (_ : Algebra S₀ S) (_ : Algebra R₀ S) (_ : IsScalarTower R₀ R S)
      (_ : IsScalarTower R₀ S₀ S) (_ : AddCommGroup M₀) (_ : Module S₀ M₀) (_ : Module R₀ M₀)
      (_ : IsScalarTower R₀ S₀ M₀) (_ : Module S₀ M) (_ : IsScalarTower S₀ S M)
      (f : M₀ →ₗ[S₀] M),
      Algebra.FiniteType ℤ R₀ ∧ Algebra.FiniteType R₀ S₀ ∧ Module.Finite S₀ M₀ ∧
        Module.Flat R₀ M₀ ∧ Algebra.IsPushout R₀ R S₀ S ∧ IsBaseChange S f := by
  obtain ⟨R₀, S₀, P, _, _, _, _, _, _, _, _, f, _, _, _, _, hf⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := R) (S := S) M
  obtain ⟨i, hi⟩ := exists_flat_stage R₀ S₀ P fun q =>
    have := Module.Flat.of_isLocalizedModule_of_tower (R := R) q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
    (Module.flat_localizedModule_atPrime_iff_of_isBaseChange f hf q.asIdeal).mp this
  let T := Ring R₀ S₀ i
  let : Module T M := Module.compHom M (algebraMap T S)
  have : IsScalarTower T S M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S₀ T M := .to₁₂₄ S₀ T S M
  let hP := TensorProduct.isBaseChange S₀ P T
  refine ⟨Base R₀ i, T, T ⊗[S₀] P, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hP.lift f, inferInstance,
    inferInstance, inferInstance, hi, ringToRing_isPushout R₀ S₀ i, hP.of_comp ?_⟩
  rwa [IsBaseChange.lift_comp]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 02JO (2).** Let `R → S` be of finite presentation and let `M` be a finitely
presented `S`-module which is flat over `R`. If `R = colim_λ R_λ` is a directed colimit, then
there are `λ`, an `R_λ`-algebra `S_λ` of finite presentation and a finitely presented
`S_λ`-module `M_λ` which is flat over `R_λ`, with an algebra map `S_λ → S` and an `S_λ`-linear
map `M_λ → M` exhibiting `S = R ⊗_{R_λ} S_λ` and `M = S ⊗_{S_λ} M_λ`. -/
@[stacks 02JO "(2)", ega "IV 1.8.4.2"]
theorem Module.Flat.exists_finitePresentation_model_of_directed {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (M : Type w) [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M]
    [Module.Flat R M] {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {A : ι → Type v} [∀ i, CommRing (A i)] (a : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A fun i j h => a i j h] (ρ : ∀ i, A i →+* R)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x) (hs : ∀ r, ∃ i x, ρ i x = r)
    (hz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0) :
    ∃ i, letI := (ρ i).toAlgebra
      ∃ (T P : Type (max u v)) (_ : CommRing T) (_ : Algebra (A i) T) (_ : Algebra T S)
        (_ : Algebra (A i) S) (_ : IsScalarTower (A i) R S) (_ : IsScalarTower (A i) T S)
        (_ : AddCommGroup P) (_ : Module T P) (_ : Module (A i) P) (_ : IsScalarTower (A i) T P)
        (_ : Module T M) (_ : IsScalarTower T S M) (f : P →ₗ[T] M),
        Algebra.FinitePresentation (A i) T ∧ Module.FinitePresentation T P ∧
          Module.Flat (A i) P ∧ Algebra.IsPushout (A i) R T S ∧ IsBaseChange S f := by
  obtain ⟨R₀, S₀, M₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, f, _, _, _, _, _, hf⟩ :=
    Module.Flat.exists_finiteType_model (R := R) (S := S) M
  have := (Algebra.FinitePresentation.of_finiteType (R := ℤ) (A := R₀)).mp inferInstance
  have : DirectedSystem A fun i j h => (a i j h).toIntAlgHom := by
    simp only [RingHom.toIntAlgHom_coe]
    infer_instance
  obtain ⟨i, ψ, hψ⟩ := AlgHom.exists_comp_eq_of_finitePresentation
    (fun i j h => (a i j h).toIntAlgHom) (fun i => (ρ i).toIntAlgHom) hρ hs hz
    (algebraMap R₀ R).toIntAlgHom
  refine ⟨i, ?_⟩
  let : Algebra (A i) R := (ρ i).toAlgebra
  let : Algebra R₀ (A i) := ψ.toRingHom.toAlgebra
  have : IsScalarTower R₀ (A i) R :=
    .of_algebraMap_eq fun x => (DFunLike.congr_fun hψ x).symm
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  have := (Algebra.FinitePresentation.of_finiteType (R := R₀) (A := S₀)).mp inferInstance
  have := Module.finitePresentation_of_finite S₀ M₀
  let T := A i ⊗[R₀] S₀
  let : Algebra T S := (Algebra.TensorProduct.productMap
    ((IsScalarTower.toAlgHom R₀ R S).comp (IsScalarTower.toAlgHom R₀ (A i) R))
    (IsScalarTower.toAlgHom R₀ S₀ S)).toRingHom.toAlgebra
  let : Algebra (A i) S := ((algebraMap R S).comp (algebraMap (A i) R)).toAlgebra
  have : IsScalarTower (A i) R S := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A i) T S := .of_algebraMap_eq fun x => by
    simp [T, RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower S₀ T S := .of_algebraMap_eq fun x => by
    simp [T, RingHom.algebraMap_toAlgebra]
  have : IsScalarTower R₀ T S := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R₀ S₀ T x, ← IsScalarTower.algebraMap_apply S₀ T S,
      ← IsScalarTower.algebraMap_apply R₀ S₀ S]
  let : Module T M := Module.compHom M (algebraMap T S)
  have : IsScalarTower T S M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S₀ T M := .to₁₂₄ S₀ T S M
  let hM := TensorProduct.isBaseChange S₀ M₀ T
  refine ⟨T, T ⊗[S₀] M₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hM.lift f, inferInstance, inferInstance, ?_,
    (Algebra.IsPushout.comp_iff R₀ (A i) S₀ T).mp inferInstance, hM.of_comp ?_⟩
  · exact Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange R₀ (A i) S₀ T M₀)
  · rwa [IsBaseChange.lift_comp]
