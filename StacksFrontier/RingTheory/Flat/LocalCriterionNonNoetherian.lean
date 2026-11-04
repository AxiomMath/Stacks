module

public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.SpreadingOut.ModuleMapSystem
public import StacksFrontier.RingTheory.SpreadingOut.ResidueFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injectivity modulo the maximal ideal, without a Noetherian hypothesis

Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation
over `R`, let `𝔪` be the maximal ideal of `R` and let `u : M → N` be a map of `S`-modules with
`M`, `N` of finite presentation over `S` and `N` flat over `R`. If `ū : M/𝔪M → N/𝔪N` is injective,
then `u` is injective and `N/u(M)` is flat over `R`.

## Main results

* `Module.Flat.injective_of_injective_mapQ_maximalIdeal`: if `ū` is injective, then `u` is
  injective.
* `Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal`: if `ū` is
  injective, then `u` is injective and `N/u(M)` is flat over `R`.

## Implementation notes

The fibre `M/𝔪M` is the quotient `M ⧸ 𝔪 • (⊤ : Submodule R M)`, and `ū` is the map
`Submodule.mapQ` of `u.restrictScalars R` between two such quotients, which sends the class of `x`
to the class of `u x`. The cokernel `N/u(M)` is `N ⧸ LinearMap.range u`.

## References

* [Stacks Project, Tag 046Y](https://stacks.math.columbia.edu/tag/046Y)
-/

@[expose] public section


universe u u₁ u₂ u₃ u₄
open CategoryTheory Limits IsLocalRing

namespace Module.Flat

/-- `Module.Flat.injective_of_injective_mapQ_maximalIdeal` when `R`, `S`, `M` and `N` lie in one
universe. -/
private theorem injective_aux {R S M N : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.FinitePresentation S M] [Module.FinitePresentation S N]
    [Module.Flat R N] (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R M))
          (maximalIdeal R • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (u.restrictScalars R)))) :
    Function.Injective u := by
  obtain
    ⟨Λ, instP, instNe, instDir, A, B, φ, MF, NF, instM, instN, hsmulM, hsmulN, ρ, σ, μ, ν, hρ, hσ,
      hμ, hν, us, hcomm, hμsemi, hνsemi, hAloc, hBloc, hφloc, hρloc, hσloc, hAess, hφess, hMfin,
      hNfin, hcart, hMbc, hNbc, husmul, huscolim⟩ :=
    RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module_map hS u
  let _ : Preorder Λ := instP
  let _ : Nonempty Λ := instNe
  let _ : IsDirected Λ (· ≤ ·) := instDir
  refine SpreadingOut.injective_of_forall_exists_ge_injective u hμ hν us huscolim fun i => ?_
  obtain ⟨j, hij, hflatj⟩ :=
    Module.Flat.exists_ge_flat_of_isColimit (R := R) (S := S) (M := N) instN hsmulN hρ hσ hν hcomm
      hνsemi hAloc hBloc hφloc
      (fun {a b} h => CategoryTheory.isLocalHom_map_of_isLocalHom_app ρ hρloc h) hAess hφess hNfin
      hcart hNbc i
  refine ⟨j, hij, ?_⟩
  have hAj := hAloc j
  have hBj := hBloc j
  let algAB : Algebra ↑(A.obj j) ↑(B.obj j) := (φ.app j).hom.toAlgebra
  have hlocAB : IsLocalHom (algebraMap ↑(A.obj j) ↑(B.obj j)) := hφloc j
  have hAess' : Algebra.EssFiniteType ℤ ↑(A.obj j) := hAess j
  have hφess' : Algebra.EssFiniteType ↑(A.obj j) ↑(B.obj j) := hφess j
  have hAnoeth : IsNoetherianRing ↑(A.obj j) := Algebra.EssFiniteType.isNoetherianRing ℤ ↑(A.obj j)
  have hBnoeth : IsNoetherianRing ↑(B.obj j) :=
    Algebra.EssFiniteType.isNoetherianRing ↑(A.obj j) ↑(B.obj j)
  let modBM := instM j
  let modBN := instN j
  let modAM : Module ↑(A.obj j) ↑(MF.obj j) := Module.compHom _ (φ.app j).hom
  let modAN : Module ↑(A.obj j) ↑(NF.obj j) := Module.compHom _ (φ.app j).hom
  have towM : IsScalarTower ↑(A.obj j) ↑(B.obj j) ↑(MF.obj j) := .of_algebraMap_smul fun _ _ => rfl
  have towN : IsScalarTower ↑(A.obj j) ↑(B.obj j) ↑(NF.obj j) := .of_algebraMap_smul fun _ _ => rfl
  have hMfinj : Module.Finite ↑(B.obj j) ↑(MF.obj j) := hMfin j
  have hflatj' : Module.Flat ↑(A.obj j) ↑(NF.obj j) := hflatj
  let uj : ↑(MF.obj j) →ₗ[↑(A.obj j)] ↑(NF.obj j) :=
    { toFun := fun m => us.app j m
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a m => husmul j ((φ.app j) a) m }
  have hmj : (maximalIdeal R).comap (ρ.app j).hom = maximalIdeal ↑(A.obj j) := by
    have := hρloc j
    have hRj : IsLocalRing ↑(((Functor.const Λ).obj (CommRingCat.of R)).obj j) :=
      inferInstanceAs (IsLocalRing R)
    exact SpreadingOut.comap_maximalIdeal_of_isLocalHom (ρ.app j).hom
  have hujbar :
    Function.Injective
      (Submodule.mapQ (maximalIdeal ↑(A.obj j) • (⊤ : Submodule ↑(A.obj j) ↑(MF.obj j)))
        (maximalIdeal ↑(A.obj j) • (⊤ : Submodule ↑(A.obj j) ↑(NF.obj j))) uj
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal ↑(A.obj j)) uj)) := by
    refine (Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff _).2 fun m hm => ?_
    rw [Submodule.mem_comap] at hm
    rw [← hmj, ← mem_map_smul_top_iff (S := ↑(B.obj j))] at hm
    have h1 :
      (ν.app j (uj m) : N) ∈ ((maximalIdeal R).map (algebraMap R S)) • (⊤ : Submodule S N) :=
      Stacks.SpreadingOut.QuotientSystem.subN_le_comap_leg φ ρ σ ν (maximalIdeal R) instN hcomm
        hνsemi j hm
    obtain ⟨y, hy⟩ : ∃ y : M, (μ.app j m : M) = y := ⟨_, rfl⟩
    have hcc : u y = (ν.app j (us.app j m) : N) := hy ▸ huscolim j m
    have h2 : u y ∈ maximalIdeal R • (⊤ : Submodule R N) := by
      rwa [← mem_map_smul_top_iff (S := S), hcc]
    have h3 : y ∈ maximalIdeal R • (⊤ : Submodule R M) :=
      (Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff _).1 hu (Submodule.mem_comap.2 h2)
    have h4 : y ∈ ((maximalIdeal R).map (algebraMap R S)) • (⊤ : Submodule S M) :=
      (mem_map_smul_top_iff (S := S) (maximalIdeal R) y).2 h3
    have h5 :=
      SpreadingOut.mem_smul_top_of_leg_mem_smul_top φ ρ σ μ instM hsmulM hcomm hμsemi hρ hσ hμ
        hAloc hBloc hφloc hρloc hσloc hcart hMbc j m (by rwa [hy])
    rw [hmj] at h5
    exact (mem_map_smul_top_iff (S := ↑(B.obj j)) (maximalIdeal ↑(A.obj j)) m).1 h5
  exact
    (injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
        (R := ↑(A.obj j)) (S := ↑(B.obj j)) (N := ↑(MF.obj j)) (M := ↑(NF.obj j)) uj hujbar).1

/-- Membership in `I' M'` transports to membership in `I M` along an isomorphism of the datum,
where `I'` is the inverse image of `I`. -/
private lemma mem_smul_top_of_ringEquiv {R M R' M' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [CommRing R'] [AddCommGroup M'] [Module R' M'] (eR : R' ≃+* R) (eM : M' ≃+ M)
    (hcompat : ∀ (a : R') (m : M'), eM (a • m) = eR a • eM m) (I : Ideal R) {m : M'}
    (hm : m ∈ (I.comap (eR : R' →+* R)) • (⊤ : Submodule R' M')) :
    eM m ∈ I • (⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha z _
    rw [hcompat]
    exact Submodule.smul_mem_smul (Ideal.mem_comap.mp ha) Submodule.mem_top
  · intro p q hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq

/-- The two-sided form of `Module.Flat.mem_smul_top_of_ringEquiv`. -/
private lemma mem_smul_top_ringEquiv_iff {R M R' M' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [CommRing R'] [AddCommGroup M'] [Module R' M'] (eR : R' ≃+* R) (eM : M' ≃+ M)
    (hcompat : ∀ (a : R') (m : M'), eM (a • m) = eR a • eM m) (I : Ideal R) (m : M') :
    m ∈ (I.comap (eR : R' →+* R)) • (⊤ : Submodule R' M') ↔ eM m ∈ I • (⊤ : Submodule R M) := by
  refine ⟨mem_smul_top_of_ringEquiv eR eM hcompat I, fun hm => ?_⟩
  have hcompat' : ∀ (a : R) (z : M), eM.symm (a • z) = eR.symm a • eM.symm z := fun a z =>
    eM.injective (by rw [eM.apply_symm_apply, hcompat, eR.apply_symm_apply, eM.apply_symm_apply])
  have hI : (I.comap (eR : R' →+* R)).comap (eR.symm : R →+* R') = I := by
    ext z
    simp only [Ideal.mem_comap]
    rw [show (eR : R' →+* R) ((eR.symm : R →+* R') z) = z from eR.apply_symm_apply z]
  have h2 :=
    mem_smul_top_of_ringEquiv eR.symm eM.symm hcompat' (I.comap (eR : R' →+* R)) (m := eM m)
  rw [hI, eM.symm_apply_apply] at h2
  exact h2 hm

/-- The maximal ideal of a local ring pulls back to the maximal ideal along a ring isomorphism. -/
private lemma comap_maximalIdeal_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    [IsLocalRing R] [IsLocalRing R'] (e : R' ≃+* R) :
    (maximalIdeal R).comap (e : R' →+* R) = maximalIdeal R' := by
  have : IsLocalHom (e : R' →+* R) :=
    ⟨fun a ha => by
      have h : IsUnit ((e.symm : R →+* R') ((e : R' →+* R) a)) := ha.map (e.symm : R →+* R')
      rwa [show (e.symm : R →+* R') ((e : R' →+* R) a) = a from e.symm_apply_apply a] at h⟩
  exact SpreadingOut.comap_maximalIdeal_of_isLocalHom (e : R' →+* R)

/-- Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation
over `R`, let `𝔪` be the maximal ideal of `R`, and let `u : M → N` be a map of `S`-modules with
`M`, `N` of finite presentation over `S` and `N` flat over `R`. If the induced map
`ū : M/𝔪M → N/𝔪N` is injective, then `u` is injective. -/
public theorem injective_of_injective_mapQ_maximalIdeal {R : Type u₁} {S : Type u₂} {M : Type u₃}
    {N : Type u₄} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R M))
          (maximalIdeal R • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (u.restrictScalars R)))) :
    Function.Injective u := by
  let eR : ULift.{max u₂ u₃ u₄} R ≃+* R := ULift.ringEquiv
  let eS : ULift.{max u₁ u₃ u₄} S ≃+* S := ULift.ringEquiv
  let eM : ULift.{max u₁ u₂ u₄} M ≃ₗ[S] M := ULift.moduleEquiv
  let eN : ULift.{max u₁ u₂ u₃} N ≃ₗ[S] N := ULift.moduleEquiv
  let algR'S' : Algebra (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₃ u₄} S) :=
    ULift.algebra' R (ULift.{max u₁ u₃ u₄} S)
  let algS'S : Algebra (ULift.{max u₁ u₃ u₄} S) S := ULift.algebra' S S
  let algR'R : Algebra (ULift.{max u₂ u₃ u₄} R) R := ULift.algebra' R R
  have hlocR' : IsLocalRing (ULift.{max u₂ u₃ u₄} R) := eR.symm.isLocalRing
  have hlocS' : IsLocalRing (ULift.{max u₁ u₃ u₄} S) := eS.symm.isLocalRing
  have hlochom : IsLocalHom (algebraMap (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₃ u₄} S)) := by
    refine ⟨fun a ha => ?_⟩
    have h0 :
      (eS : ULift.{max u₁ u₃ u₄} S →+* S)
          (algebraMap (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₃ u₄} S) a) =
        algebraMap R S a.down :=
      rfl
    have h1 : IsUnit (algebraMap R S a.down) := h0 ▸ ha.map (eS : ULift.{max u₁ u₃ u₄} S →+* S)
    have h2 : IsUnit a.down := IsLocalHom.map_nonunit (f := algebraMap R S) a.down h1
    have h3 : (eR.symm : R →+* ULift.{max u₂ u₃ u₄} R) a.down = a := rfl
    exact h3 ▸ h2.map (eR.symm : R →+* ULift.{max u₂ u₃ u₄} R)
  have htowM :
    IsScalarTower (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₃ u₄} S) (ULift.{max u₁ u₂ u₄} M) :=
    ⟨fun a b c => by ext; exact smul_assoc a.down b.down c.down⟩
  have htowN :
    IsScalarTower (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₃ u₄} S) (ULift.{max u₁ u₂ u₃} N) :=
    ⟨fun a b c => by ext; exact smul_assoc a.down b.down c.down⟩
  have htowSM : IsScalarTower (ULift.{max u₁ u₃ u₄} S) S (ULift.{max u₁ u₂ u₄} M) :=
    ⟨fun a b c => by ext; exact mul_smul a.down b c.down⟩
  have htowSN : IsScalarTower (ULift.{max u₁ u₃ u₄} S) S (ULift.{max u₁ u₂ u₃} N) :=
    ⟨fun a b c => by ext; exact mul_smul a.down b c.down⟩
  have htowRN : IsScalarTower (ULift.{max u₂ u₃ u₄} R) R (ULift.{max u₁ u₂ u₃} N) :=
    ⟨fun a b c => by ext; exact mul_smul a.down b c.down⟩
  have hfpS'S : Module.FinitePresentation (ULift.{max u₁ u₃ u₄} S) S :=
    Module.FinitePresentation.of_equiv
      ({ eS with map_smul' := fun _ _ => rfl } :
        ULift.{max u₁ u₃ u₄} S ≃ₗ[ULift.{max u₁ u₃ u₄} S] S)
  have hfpSM' : Module.FinitePresentation S (ULift.{max u₁ u₂ u₄} M) :=
    Module.FinitePresentation.of_equiv (ULift.moduleEquiv (R := S)).symm
  have hfpSN' : Module.FinitePresentation S (ULift.{max u₁ u₂ u₃} N) :=
    Module.FinitePresentation.of_equiv (ULift.moduleEquiv (R := S)).symm
  have hfpM' : Module.FinitePresentation (ULift.{max u₁ u₃ u₄} S) (ULift.{max u₁ u₂ u₄} M) :=
    Module.FinitePresentation.trans (ULift.{max u₁ u₃ u₄} S) (ULift.{max u₁ u₂ u₄} M) S
  have hfpN' : Module.FinitePresentation (ULift.{max u₁ u₃ u₄} S) (ULift.{max u₁ u₂ u₃} N) :=
    Module.FinitePresentation.trans (ULift.{max u₁ u₃ u₄} S) (ULift.{max u₁ u₂ u₃} N) S
  have hflatR'R : Module.Flat (ULift.{max u₂ u₃ u₄} R) R :=
    Module.Flat.of_linearEquiv
      ({ eR.symm with map_smul' := fun _ _ => rfl } :
        R ≃ₗ[ULift.{max u₂ u₃ u₄} R] ULift.{max u₂ u₃ u₄} R)
  have hflatN' : Module.Flat (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₂ u₃} N) :=
    Module.Flat.trans (ULift.{max u₂ u₃ u₄} R) R (ULift.{max u₁ u₂ u₃} N)
  have hS' :
    (algebraMap (ULift.{max u₂ u₃ u₄} R)
        (ULift.{max u₁ u₃ u₄} S)).EssentiallyOfFinitePresentation :=
    RingHom.EssentiallyOfFinitePresentation.ulift hS
  let u' : ULift.{max u₁ u₂ u₄} M →ₗ[ULift.{max u₁ u₃ u₄} S] ULift.{max u₁ u₂ u₃} N :=
    { toFun := fun m => ULift.up (u m.down)
      map_add' := fun a b => by
        ext; exact map_add u a.down b.down
      map_smul' := fun a b => by
        ext; exact map_smul u a.down b.down }
  have hu' :
    Function.Injective
      (Submodule.mapQ
        (maximalIdeal (ULift.{max u₂ u₃ u₄} R) •
          (⊤ : Submodule (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₂ u₄} M)))
        (maximalIdeal (ULift.{max u₂ u₃ u₄} R) •
          (⊤ : Submodule (ULift.{max u₂ u₃ u₄} R) (ULift.{max u₁ u₂ u₃} N)))
        (u'.restrictScalars (ULift.{max u₂ u₃ u₄} R))
        (Submodule.smul_top_le_comap_smul_top _ _)) := by
    refine (Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff _).2 fun m hm => ?_
    rw [Submodule.mem_comap] at hm
    rw [← comap_maximalIdeal_ringEquiv eR] at hm ⊢
    have h1 : (u m.down : N) ∈ maximalIdeal R • (⊤ : Submodule R N) :=
      mem_smul_top_of_ringEquiv eR eN.toAddEquiv (fun _ _ => rfl) (maximalIdeal R) hm
    have h2 : (m.down : M) ∈ maximalIdeal R • (⊤ : Submodule R M) :=
      (Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff _).1 hu (Submodule.mem_comap.2 h1)
    exact (mem_smul_top_ringEquiv_iff eR eM.toAddEquiv (fun _ _ => rfl) (maximalIdeal R) m).2 h2
  intro a b hab
  exact congrArg ULift.down
    (injective_aux hS' u' hu' (congrArg ULift.up hab : u' (ULift.up a) = u' (ULift.up b)))

end Module.Flat

open IsLocalRing in
/-- Let `R → S` be a local homomorphism of local rings with `S` essentially of finite presentation
over `R`, let `𝔪` be the maximal ideal of `R`, and let `u : M → N` be a map of `S`-modules with
`M`, `N` of finite presentation over `S` and `N` flat over `R`. If the induced map
`ū : M/𝔪M → N/𝔪N` is injective, then `u` is injective and `N/u(M)` is flat over `R`.

Here `M/𝔪M` is `M ⧸ 𝔪 • ⊤` and `ū` is the canonical `Submodule.mapQ`, which sends the class of `x`
to the class of `u x`. -/
@[stacks 046Y "`M/𝔪M` is `M ⧸ 𝔪 • (⊤ : Submodule R M)` and `ū` the canonical `Submodule.mapQ` of
`u`. Hypothesis (1) is `RingHom.EssentiallyOfFinitePresentation` (Definition 00QM (2)), Mathlib
having no such predicate. The cokernel `N/u(M)` is `N ⧸ LinearMap.range u`, and the two
conclusions are conjoined; see the module docstring.", sga "1 IV 5.7" "(ii) ⟹ (i)"]
public theorem Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal
    {R S M N : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (u : M →ₗ[S] N)
    (hu :
      Function.Injective
        (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R M))
          (maximalIdeal R • (⊤ : Submodule R N)) (u.restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) (u.restrictScalars R)))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) :=
  ⟨Module.Flat.injective_of_injective_mapQ_maximalIdeal hS u hu,
    Module.Flat.flat_quotient_range_of_injective_mapQ_maximalIdeal hS u hu⟩
