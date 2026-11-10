module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus
import StacksFrontier.RingTheory.Etale.Lifting
import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftEquiv

/-!
# Lifting an algebraization across a square-zero thickening

Let `R → R₀` be a surjection of Noetherian rings with square-zero kernel `N`, let
`I = (f₁, …, f_k) ⊆ R`, let `S` be a finite type `R₀`-algebra, étale over `Spec R₀ ∖ V(I R₀)`, and
let `H` be an `I`-adically complete Noetherian `R`-algebra, flat over `R` after inverting each
`fᵢ`, with `H ⧸ N H ≅ S^∧`. This file constructs a finite type `R`-algebra `T`, étale over
`Spec R ∖ V(I)`, lifting `S` across `R → R₀` and with `I`-adic completion `H`.

## Main results

* `Rig.exists_squareZeroLift`: a finite type `R`-algebra `T`, étale over `Spec R ∖ V(I)`, with a
  surjection `T → S` of kernel `N T` and with `I`-adic completion `H`.
-/

@[expose] public section

namespace Rig

universe u

/-- Let `R → R₀` be a surjection of Noetherian rings with square-zero kernel `N`, let
`I = (f₁, …, f_k) ⊆ R`, and let `S` be a finite type `R₀`-algebra which is étale over
`Spec R₀ ∖ V(I R₀)`.  Let `H` be a Noetherian `I`-adically complete `R`-algebra whose
localizations `H_{fᵢ}` are flat over `R`, together with an `R`-algebra isomorphism
`e : H ⧸ N H ≅ S^∧`.  Then there is a finite type `R`-algebra `T`, étale over `Spec R ∖ V(I)`,
with a surjection `p : T → S` of kernel `N T` and a map `φ : T → H` compatible with `e`, which
identifies the `I`-adic completion of `T` with `H`. -/
public theorem exists_squareZeroLift
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {R₀ : Type u} [CommRing R₀] [Algebra R R₀]
    (hsurj : Function.Surjective (algebraMap R R₀))
    (hsq : RingHom.ker (algebraMap R R₀) ^ 2 = ⊥)
    {k : ℕ} (f : Fin k → R)
    (S : Type u) [CommRing S] [Algebra R₀ S] [Algebra R S] [IsScalarTower R R₀ S]
    [Algebra.FiniteType R₀ S]
    (hS : IsEtaleOutside ((Ideal.span (Set.range f)).map (algebraMap R R₀)) S)
    (H : Type u) [CommRing H] [Algebra R H] [IsNoetherianRing H]
    (hH : IsAdicComplete ((Ideal.span (Set.range f)).map (algebraMap R H)) H)
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (e : (H ⧸ (RingHom.ker (algebraMap R R₀)).map (algebraMap R H)) ≃ₐ[R]
      AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R S)) S) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Algebra.FiniteType R T ∧ IsEtaleOutside (Ideal.span (Set.range f)) T ∧
      ∃ (p : T →ₐ[R] S) (φ : T →ₐ[R] H),
        Function.Surjective p ∧
        RingHom.ker p.toRingHom = (RingHom.ker (algebraMap R R₀)).map (algebraMap R T) ∧
        (∀ x : T, e (Ideal.Quotient.mk _ (φ x)) =
          algebraMap S (AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R S)) S)
            (p x)) ∧
        ∃ E : AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R T)) T ≃ₐ[R] H,
          ∀ x : T, E (algebraMap T _ x) = φ x := by
  classical
  have hN : ∀ (A : Type u) [CommRing A] [Algebra R₀ A] [Algebra R A] [IsScalarTower R R₀ A],
      (RingHom.ker (algebraMap R R₀)).map (algebraMap R A) = ⊥ := fun A _ _ _ _ ↦ by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R R₀ A, (RingHom.mem_ker).mp hx,
      map_zero]
  have hNS := hN S
  have : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ _ hsurj
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R₀ S
  have : Algebra.FiniteType R R₀ :=
    Algebra.FiniteType.of_surjective (Algebra.ofId R R₀) hsurj
  have : Algebra.FiniteType R S := Algebra.FiniteType.trans (S := R₀) inferInstance inferInstance
  have : Algebra.FinitePresentation R₀ S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have := hH
  have hEt : ∀ s : Finset (Fin k), s.Nonempty →
      Algebra.Etale R₀ (SquareZeroLift.Sl f S s) := by
    intro s hs
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
    intro p hp
    apply hS
    simp only [Set.mem_preimage, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
      SetLike.coe_subset_coe]
    intro hle
    obtain ⟨i, hi⟩ := hs
    have hfi : algebraMap R S (f i) ∉ p.asIdeal := by
      intro hmem
      apply hp
      change algebraMap R S (∏ j ∈ s, f j) ∈ p.asIdeal
      rw [← Finset.mul_prod_erase s f hi, map_mul]
      exact Ideal.mul_mem_right _ _ hmem
    apply hfi
    have : algebraMap R R₀ (f i) ∈ (Ideal.span (Set.range f)).map (algebraMap R R₀) :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    have h2 := hle this
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h2
    rwa [IsScalarTower.algebraMap_apply R R₀ S]
  have hex : ∀ s : Finset (Fin k), s.Nonempty →
      ∃ L : SquareZeroLift.NilLift R (RingHom.ker (algebraMap R R₀)) (SquareZeroLift.Sl f S s),
        Algebra.Etale R L.carrier := by
    intro s hs
    have := hEt s hs
    obtain ⟨C, _, _, hC, ψ, hψ, hker⟩ :=
      etale_lift_along_surjection R R₀ (SquareZeroLift.Sl f S s) hsurj
    exact ⟨⟨C, ψ, hψ, hker⟩, hC⟩
  let triv : ∀ s : Finset (Fin k),
      SquareZeroLift.NilLift R (RingHom.ker (algebraMap R R₀)) (SquareZeroLift.Sl f S s) :=
    fun s ↦ ⟨SquareZeroLift.Sl f S s, AlgHom.id R _, Function.surjective_id, by
      rw [hN, (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id]⟩
  let L : ∀ s : Finset (Fin k),
      SquareZeroLift.NilLift R (RingHom.ker (algebraMap R R₀)) (SquareZeroLift.Sl f S s) :=
    fun s ↦ if hs : s.Nonempty then (hex s hs).choose else triv s
  have hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier := by
    intro s hs
    have key : ∀ X Y : SquareZeroLift.NilLift R (RingHom.ker (algebraMap R R₀))
        (SquareZeroLift.Sl f S s), X = Y → Algebra.Etale R X.carrier →
          Algebra.Etale R Y.carrier := by
      rintro X _ rfl h
      exact h
    exact key _ (L s) (dite_eq_left hs).symm (hex s hs).choose_spec
  have : Algebra.FiniteType R
      (SquareZeroLift.TT (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL) :=
    SquareZeroLift.finiteType_glued (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL hNS hflat
  have : IsNoetherianRing (SquareZeroLift.TT (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL) :=
    Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨E, hE⟩ := SquareZeroLift.exists_algEquiv_adicCompletion_of_bijective
    (Ideal.span (Set.range f)) (SquareZeroLift.prH (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL)
    (fun n h ↦ SquareZeroLift.exists_sub_prH_mem (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL
      hflat n h)
    (fun n t ht ↦ SquareZeroLift.mem_map_of_prH_mem (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL
      hNS hflat n t ht)
  exact ⟨SquareZeroLift.TT (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL, inferInstance,
    inferInstance, inferInstance,
    SquareZeroLift.isEtaleOutside_glued (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL hflat,
    SquareZeroLift.prS (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL,
    SquareZeroLift.prH (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL,
    SquareZeroLift.prS_surjective (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL hflat,
    SquareZeroLift.ker_prS (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL hNS hflat,
    SquareZeroLift.compat (RingHom.ker (algebraMap R R₀)) hsq f S H e L hL, E, hE⟩

end Rig

end
