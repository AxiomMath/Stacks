module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatumComplete
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftEquiv

/-!
# Lifting an algebraization across a square-zero thickening, from a glueing datum

Let `R → R₀` be a surjection of Noetherian rings with square-zero kernel `N`, let
`I = (f₁, …, f_k) ⊆ R`, let `S` be a finite type `R₀`-algebra, and let `H` be an `I`-adically
complete Noetherian `R`-algebra, flat over `R` after inverting each `fᵢ`, with
`H ⧸ N H ≅ S^∧`. Given a glueing datum `D` (`Rig.SquareZeroLift.GlueDatum`): lifts `V_s` of the
localizations `S[1/r_s]`, flat over `R`, with compatible transition maps and maps to the `H_s`,
this file constructs a finite type `R`-algebra `T` lifting `S` across `R → R₀`, with `I`-adic
completion `H`, and with `T[1/fᵢ] = V_{i}` for every `i`.

The ring `T` is `Rig.SquareZeroLift.GlueDatum.glued`. For lifts étale over `R` the transition
maps and the maps to the `H_s` are unique (`Rig.SquareZeroLift.etaleDatum`), and this is the
square-zero lifting step `Rig.exists_squareZeroLift` of Stacks 0AKA.

## Main results

* `Rig.SquareZeroLift.GlueDatum.exists_lift`: the square-zero lifting step for a glueing datum.
-/

@[expose] public section

namespace Rig.SquareZeroLift.GlueDatum

open FormalGlueing

universe u

/-- **The square-zero lifting step for a glueing datum.** Let `R → R₀` be a surjection of
Noetherian rings with square-zero kernel `N`, let `I = (f₁, …, f_k) ⊆ R`, let `S` be a finite type
`R₀`-algebra, and let `H` be a Noetherian `I`-adically complete `R`-algebra whose localizations
`H_{fᵢ}` are flat over `R`, with an `R`-algebra isomorphism `e : H ⧸ N H ≅ S^∧`. A glueing datum
`D` for these data gives a finite type `R`-algebra `T` with a surjection `p : T → S` of kernel
`N T` and a map `φ : T → H` compatible with `e`, which identifies the `I`-adic completion of `T`
with `H`; moreover, for every `i`, the lift `V_{i}` of `D` is the localization `T[1/fᵢ]`, by a map
compatible with `p` and `φ`. -/
theorem exists_lift
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {R₀ : Type u} [CommRing R₀] [Algebra R R₀]
    (hsurj : Function.Surjective (algebraMap R R₀))
    (hsq : RingHom.ker (algebraMap R R₀) ^ 2 = ⊥)
    {k : ℕ} {f : Fin k → R}
    {S : Type u} [CommRing S] [Algebra R₀ S] [Algebra R S] [IsScalarTower R R₀ S]
    [Algebra.FiniteType R₀ S]
    {H : Type u} [CommRing H] [Algebra R H] [IsNoetherianRing H]
    (hH : IsAdicComplete ((Ideal.span (Set.range f)).map (algebraMap R H)) H)
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    {e : (H ⧸ (RingHom.ker (algebraMap R R₀)).map (algebraMap R H)) ≃ₐ[R]
      AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R S)) S}
    (D : GlueDatum (RingHom.ker (algebraMap R R₀)) f S H e) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Algebra.FiniteType R T ∧
      ∃ (p : T →ₐ[R] S) (φ : T →ₐ[R] H),
        Function.Surjective p ∧
        RingHom.ker p.toRingHom = (RingHom.ker (algebraMap R R₀)).map (algebraMap R T) ∧
        (∀ x : T, e (Ideal.Quotient.mk _ (φ x)) =
          algebraMap S (AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R S)) S)
            (p x)) ∧
        (∃ E : AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R T)) T ≃ₐ[R] H,
          ∀ x : T, E (algebraMap T _ x) = φ x) ∧
        ∀ i : Fin k, ∃ (_ : Algebra T (D.L {i}).carrier),
          IsScalarTower R T (D.L {i}).carrier ∧
          IsLocalization.Away (algebraMap R T (f i)) (D.L {i}).carrier ∧
          (∀ x : T, (D.L {i}).ψ (algebraMap T _ x) = algebraMap S (Sl f S {i}) (p x)) ∧
          ∀ x : T, D.rho {i} (Finset.singleton_nonempty i) (algebraMap T _ x) =
            algebraMap H (Hl f H {i}) (φ x) := by
  classical
  have hNS : (RingHom.ker (algebraMap R R₀)).map (algebraMap R S) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R R₀ S, (RingHom.mem_ker).mp hx,
      map_zero]
  have : IsNoetherianRing R₀ := isNoetherianRing_of_surjective R R₀ _ hsurj
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R₀ S
  have : Algebra.FiniteType R R₀ :=
    Algebra.FiniteType.of_surjective (Algebra.ofId R R₀) hsurj
  have : Algebra.FiniteType R S := Algebra.FiniteType.trans (S := R₀) inferInstance inferInstance
  have := hH
  have : Algebra.FiniteType R D.TT := D.finiteType_glued hsq hNS hflat
  have : IsNoetherianRing D.TT := Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨E, hE⟩ := exists_algEquiv_adicCompletion_of_bijective (Ideal.span (Set.range f)) D.prH
    (fun n h ↦ D.exists_sub_prH_mem hsq hflat n h)
    (fun n t ht ↦ D.mem_map_of_prH_mem hsq hNS hflat n t ht)
  refine ⟨D.TT, inferInstance, inferInstance, inferInstance, D.prS, D.prH,
    D.prS_surjective hsq hflat, D.ker_prS hsq hNS hflat, D.compat, ⟨E, hE⟩, fun i ↦ ?_⟩
  let : Algebra D.TT (D.L {i}).carrier := (D.prV (singletonIndex i)).toRingHom.toAlgebra
  refine ⟨‹_›, IsScalarTower.of_algebraMap_eq fun r ↦
      ((D.prV (singletonIndex i)).commutes r).symm, D.isLocalization_prV hsq hflat i,
    D.psi_prV (singletonIndex i), D.rho_prV (singletonIndex i)⟩

end Rig.SquareZeroLift.GlueDatum

end
