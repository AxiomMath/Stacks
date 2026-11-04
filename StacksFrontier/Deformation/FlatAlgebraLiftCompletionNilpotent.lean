module

public import StacksFrontier.Deformation.FlatAlgebraLiftCompletionRelative
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationNilpotent
public import StacksFrontier.Deformation.FlatAlgebraLiftLocalizationNilpotent
import all StacksFrontier.Deformation.FlatAlgebraLiftCompletion

/-!
# Stacks 0DZ3 at a nilpotent kernel

Let `A' → A` be a surjection of Noetherian rings with nilpotent kernel `I`, let `B` be a finite
type flat `A`-algebra and let `𝔟 ⊆ B` be an ideal such that `Spec(B) → Spec(A)` is syntomic on
the complement of `V(𝔟)`. Stacks 0DZ3 says that `B` has a flat lift to `A'` if and only if the
`𝔟`-adic completion `B^∧` does.

The forward implication is
`Deformation.hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_of_isNoetherianRing`: the
completion of a flat lift is a flat lift of the completion. For the converse the published proof
rests on Stacks 0DZ2, which is false at a nilpotent kernel
(`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift`); this file
gives a proof that avoids it, along the lines of the proofs of Stacks 0DZ7 and 0DZB in
`StacksFrontier.Deformation.FlatAlgebraLiftLocalizationNilpotent` and
`StacksFrontier.Deformation.FlatAlgebraLiftHenselizationNilpotent`. Present `B` as `P'/𝔧` with
`P' = A'[x_1, …, x_n]`, let `𝔭' ⊆ P'` be the preimage of `𝔟` and `Q'` the `𝔭'`-adic completion
of `P'`.

* `Q' ⊗_{P'} B` is the `𝔟`-adic completion of `B` (`B` is a finite `P'`-module and `P'` is
  Noetherian), so `Q' → B^∧` is onto with kernel `𝔧Q'`. A flat lift `C'` of `B^∧` is complete
  along the preimage of `𝔟B^∧` (Stacks 0DYC), so the presentation lifts to `Q' → C'`, which is
  onto by Nakayama: `C' = Q'/𝔍` with `𝔍 + IQ' = 𝔧Q'`
  (`Deformation.exists_flat_quotient_adicCompletion`). Generators of `𝔍` lifting generators of
  `𝔧`, with lifts of the syzygies, then satisfy the relations exactly.
* `P'/𝔭'^N = Q'/𝔭'^N Q'` for every `N`, so this exact solution over `Q'` is approximated to any
  order along `𝔭'` by a solution over `P'` modulo `I`.
* Above `D(𝔭')` the algebra is syntomic, so the obstruction to improving a solution by one power
  of `I` is `𝔭'`-power torsion (`Deformation.obstructionTorsion_of_syntomic`, Stacks 07M8 at every
  level); Artin–Rees turns a good enough approximation into an exact solution over `P'`, which is
  a flat lift of `B` (the local criterion of flatness, Stacks 051C).

What the proof uses of Stacks 0DZ2 is therefore not the lemma itself but its square-zero
mechanism, run once per power of `I` on relation solutions; the local liftability that 0DZ2
assumes only at the bottom level is available at every level here because the local pieces are
syntomic.

## Main results

* `Deformation.mem_pow_of_algebraMap_mem_map_adicCompletion`: `P'/𝔭^N → (P')^∧/𝔭^N(P')^∧` is
  injective.
* `Deformation.exists_flat_quotient_adicCompletion`: a flat lift of `B^∧` is a flat quotient of
  the completed presentation.
* `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_obstructionTorsion`:
  the converse of Stacks 0DZ3, from the torsion of the obstruction.
* `Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_adicCompletion`: **Stacks 0DZ3**.

## References

* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
* [Stacks Project, Tag 0DYC](https://stacks.math.columbia.edu/tag/0DYC)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

open RelationLift

/-! ### The reduction of an adic completion modulo a power of the ideal -/

section Approx

/-- **`P'/𝔭^N → (P')^∧/𝔭^N(P')^∧` is injective.** For a Noetherian ring `P'`, an element of
`P'` whose image in the `𝔭`-adic completion lies in `𝔭^N (P')^∧` lies in `𝔭^N`. -/
theorem mem_pow_of_algebraMap_mem_map_adicCompletion {P' : Type u} [CommRing P']
    [IsNoetherianRing P'] (𝔭 : Ideal P') (N : ℕ) {x : P'}
    (hx : algebraMap P' (AdicCompletion 𝔭 P') x ∈
      (𝔭 ^ N).map (algebraMap P' (AdicCompletion 𝔭 P'))) :
    x ∈ 𝔭 ^ N := by
  have hfg : 𝔭.FG := IsNoetherian.noetherian 𝔭
  have h1 : algebraMap P' (AdicCompletion 𝔭 P') x ∈
      𝔭 ^ N • (⊤ : Submodule P' (AdicCompletion 𝔭 P')) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact hx
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker] at h1
  change AdicCompletion.eval 𝔭 P' N (AdicCompletion.of 𝔭 P' x) = 0 at h1
  rw [AdicCompletion.eval_of, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Ideal.smul_eq_mul, Ideal.mul_top] at h1
  exact h1

end Approx

/-! ### A flat lift of the completion is a quotient of the completed presentation -/

section Completion

/-- **A flat lift of `B^∧` is a flat quotient of `Q'`.** Let `π : P' → B` be a surjection of
`A'`-algebras with `P'` Noetherian and formally smooth, `𝔭' = π⁻¹(𝔟)` and `Q'` the `𝔭'`-adic
completion of `P'`. A flat lift of the `𝔟`-adic completion of `B` to `A'` is `Q' ⧸ 𝔍` for an
ideal `𝔍` with `𝔍 + IQ' = (ker π) Q'`. -/
theorem exists_flat_quotient_adicCompletion
    (A' A B P' : Type u) [CommRing A'] [CommRing A] [CommRing B] [CommRing P']
    [IsNoetherianRing A'] [IsNoetherianRing P']
    [Algebra A' A] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra A' P']
    [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (π : P' →ₐ[A'] B) (hπ : Function.Surjective π) (b : Ideal B)
    (hlift : HasFlatAlgebraLift A' A (AdicCompletion b B)) :
    ∃ 𝔍 : Ideal (AdicCompletion (b.comap π.toRingHom) P'),
      Module.Flat A' (AdicCompletion (b.comap π.toRingHom) P' ⧸ 𝔍) ∧
      𝔍 ⊔ (RingHom.ker (algebraMap A' A)).map
          (algebraMap A' (AdicCompletion (b.comap π.toRingHom) P')) =
        (RingHom.ker π).map (algebraMap P' (AdicCompletion (b.comap π.toRingHom) P')) := by
  classical
  set I := RingHom.ker (algebraMap A' A) with hI
  set 𝔭 := b.comap π.toRingHom with h𝔭
  set 𝔧 := RingHom.ker π with h𝔧
  let : Algebra P' B := π.toRingHom.toAlgebra
  have : IsScalarTower A' P' B := IsScalarTower.of_algebraMap_eq fun a => (π.commutes a).symm
  have : Module.Finite P' B := Module.Finite.of_surjective (Algebra.linearMap P' B) hπ
  have : IsNoetherianRing B := isNoetherianRing_of_surjective P' B π.toRingHom hπ
  have : IsScalarTower A' P' (AdicCompletion 𝔭 P') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hb : 𝔭.map (algebraMap P' B) = b := Ideal.map_comap_of_surjective π.toRingHom hπ b
  rw [← hb] at hlift
  set c₀ : Ideal B := 𝔭.map (algebraMap P' B) with hc₀
  -- the completion of `B` is Noetherian and complete along the extension of `c₀`
  have hc₀fg : c₀.FG := IsNoetherian.noetherian c₀
  have hc₀quot : IsNoetherianRing (B ⧸ c₀) :=
    isNoetherianRing_of_surjective B (B ⧸ c₀) (Ideal.Quotient.mk c₀) Ideal.Quotient.mk_surjective
  have hCnoeth : IsNoetherianRing (AdicCompletion c₀ B) :=
    (completion_noetherian B c₀ hc₀quot hc₀fg).1
  have hCcomplete : IsAdicComplete (c₀.map (algebraMap B (AdicCompletion c₀ B)))
      (AdicCompletion c₀ B) := (completion_noetherian B c₀ hc₀quot hc₀fg).2
  -- the map `Q' → B^∧`, as `Q' → Q' ⧸ 𝔧Q' ≅ Q' ⊗_{P'} B ≅ B^∧`
  let eB : (P' ⧸ RingHom.ker (Algebra.ofId P' B)) ≃ₐ[P'] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P' B) hπ
  have h𝔧' : RingHom.ker (Algebra.ofId P' B) = 𝔧 := rfl
  let E : ((AdicCompletion 𝔭 P') ⧸ (RingHom.ker (Algebra.ofId P' B)).map
      (algebraMap P' (AdicCompletion 𝔭 P'))) ≃ₐ[AdicCompletion 𝔭 P']
      (AdicCompletion 𝔭 P') ⊗[P'] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (AdicCompletion 𝔭 P')
      (RingHom.ker (Algebra.ofId P' B))).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl eB)
  have hE : ∀ q : AdicCompletion 𝔭 P', E (Ideal.Quotient.mk _ q) = q ⊗ₜ[P'] (1 : B) := by
    intro q
    simp only [E, AlgEquiv.trans_apply, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom,
      AlgEquiv.coe_refl, id_eq, map_one]
  let Φ := ofTensorProductAlgEquiv 𝔭 B
  let gh : AdicCompletion 𝔭 P' →+* AdicCompletion c₀ B :=
    Φ.toRingEquiv.toRingHom.comp (E.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk _))
  have hgh : ∀ q, gh q = Φ (q ⊗ₜ[P'] (1 : B)) := fun q => by
    change Φ (E (Ideal.Quotient.mk _ q)) = _
    rw [hE]
  have hghP : ∀ x : P', gh (algebraMap P' (AdicCompletion 𝔭 P') x) =
      algebraMap P' (AdicCompletion c₀ B) x := fun x => by
    rw [hgh, ← Φ.commutes x]
    rfl
  have hghsurj : Function.Surjective gh :=
    Φ.surjective.comp (E.surjective.comp Ideal.Quotient.mk_surjective)
  have hkergh : ∀ x, gh x = 0 ↔ x ∈ 𝔧.map (algebraMap P' (AdicCompletion 𝔭 P')) := by
    intro x
    change Φ (E (Ideal.Quotient.mk _ x)) = 0 ↔ _
    rw [map_eq_zero_iff _ Φ.injective, map_eq_zero_iff _ E.injective,
      Ideal.Quotient.eq_zero_iff_mem, h𝔧']
  -- algebra structures on the completion of `B`
  let : Algebra (AdicCompletion 𝔭 P') (AdicCompletion c₀ B) := gh.toAlgebra
  have : IsScalarTower A' (AdicCompletion 𝔭 P') (AdicCompletion c₀ B) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap A' (AdicCompletion c₀ B) a =
        gh (algebraMap P' (AdicCompletion 𝔭 P') (algebraMap A' P' a))
      rw [hghP, ← IsScalarTower.algebraMap_apply A' P' (AdicCompletion c₀ B)]
  have hJc : ∀ g ∈ 𝔭, algebraMap P' (AdicCompletion c₀ B) g ∈
      c₀.map (algebraMap B (AdicCompletion c₀ B)) := fun g hg => by
    rw [IsScalarTower.algebraMap_apply P' B (AdicCompletion c₀ B)]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg)
  obtain ⟨C', _, _, hflatC', ⟨eC⟩⟩ := hlift
  -- the lift `ψ : Q' → C'`, by Stacks 0DYC
  obtain ⟨ψ, hψ⟩ := exists_algHom_adicCompletion_of_algebraLift A' A P' (AdicCompletion c₀ B) C'
    hsurjA hnilA 𝔭 _ hCcomplete hJc hghP eC
  set ρ : C' →ₐ[A'] AdicCompletion c₀ B := (eC.restrictScalars A').toAlgHom.comp
    Algebra.TensorProduct.includeRight with hρdef
  have hρψ : ∀ x, ρ (ψ x) = gh x := fun x => hψ x
  have hρker : RingHom.ker ρ = I.map (algebraMap A' C') :=
    ker_comp_includeRight (AdicCompletion c₀ B) C' hsurjA (eC.restrictScalars A')
  -- `ψ` is onto, by Nakayama
  have hψsurj : Function.Surjective ψ := by
    have htop : LinearMap.range ψ.toLinearMap ⊔ I • (⊤ : Submodule A' C') = ⊤ := by
      refine eq_top_iff.mpr fun y _ => ?_
      obtain ⟨x, hx⟩ := hghsurj (ρ y)
      have hmem : y - ψ x ∈ I.map (algebraMap A' C') := by
        rw [← hρker, RingHom.mem_ker, map_sub, hρψ, hx, sub_self]
      have : y = ψ x + (y - ψ x) := by ring
      rw [this]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right ?_)
      rw [Ideal.smul_top_eq_map]; exact hmem
    have := Submodule.eq_top_of_sup_ideal_smul_top_eq_top hnilA htop
    intro y
    have hy : y ∈ LinearMap.range ψ.toLinearMap := this ▸ Submodule.mem_top
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, hx⟩
  have hmap : I.map (algebraMap A' C') =
      (I.map (algebraMap A' (AdicCompletion 𝔭 P'))).map ψ.toRingHom := by
    rw [Ideal.map_map, show ψ.toRingHom.comp (algebraMap A' (AdicCompletion 𝔭 P')) =
      algebraMap A' C' from RingHom.ext fun a => ψ.commutes a]
  refine ⟨RingHom.ker ψ, ?_, ?_⟩
  · exact Module.Flat.of_linearEquiv
      (Ideal.quotientKerAlgEquivOfSurjective (f := ψ) hψsurj).toLinearEquiv
  · apply le_antisymm
    · refine sup_le (fun x hx => (hkergh x).mp ?_) (fun x hx => (hkergh x).mp ?_)
      · rw [← hρψ, show ψ x = 0 from hx, map_zero]
      · rw [← hρψ]
        have : ψ x ∈ I.map (algebraMap A' C') := by
          rw [hmap]; exact Ideal.mem_map_of_mem ψ.toRingHom hx
        rw [← hρker] at this
        exact this
    · intro x hx
      have hψx : ψ x ∈ I.map (algebraMap A' C') := by
        rw [← hρker, RingHom.mem_ker, hρψ]; exact (hkergh x).mpr hx
      rw [hmap] at hψx
      obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective ψ.toRingHom hψsurj).mp hψx
      have : x = (x - y) + y := by ring
      rw [this]
      refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right hy)
      rw [RingHom.mem_ker, map_sub]
      change ψ x - ψ y = 0
      rw [show ψ y = ψ x from hxy, sub_self]

end Completion

/-! ### The converse of Stacks 0DZ3, from the torsion of the obstruction -/

section Converse

/-- **The converse of Stacks 0DZ3, from the torsion of the obstruction.** Let `π : P' → B` be a
surjection of `A'`-algebras with `P'` Noetherian, flat and formally smooth over `A'`, let `B` be
flat over `A` and `𝔭' = π⁻¹(𝔟)`. Assume that for generators `fh` of `ker π` and syzygy
generators `rh` of `fh` modulo `IP'` the obstruction to improving a solution is `𝔭'`-power
torsion. Then a flat lift of the `𝔟`-adic completion of `B` to `A'` gives a flat lift of `B`. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_obstructionTorsion
    (A' A B P' : Type u) [CommRing A'] [CommRing A] [CommRing B] [CommRing P']
    [IsNoetherianRing A']
    [Algebra A' A] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra A' P']
    [Algebra.FormallySmooth A' P'] [IsNoetherianRing P'] [Module.Flat A' P'] [Module.Flat A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (π : P' →ₐ[A'] B) (hπ : Function.Surjective π) (b : Ideal B)
    (hT : ∀ (m s : ℕ) (fh : Fin m → P') (rh : Fin s → Fin m → P'),
      Ideal.span (Set.range fh) = RingHom.ker π →
      SyzygyGenerators ((RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) fh rh →
      (∀ j, ∑ i, rh j i * fh i ∈ (RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) →
      ∀ k, 1 ≤ k → ObstructionTorsion ((RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
        (b.comap π.toRingHom) fh rh k)
    (hlift : HasFlatAlgebraLift A' A (AdicCompletion b B)) :
    HasFlatAlgebraLift A' A B := by
  classical
  set I := RingHom.ker (algebraMap A' A) with hI
  set 𝔭 := b.comap π.toRingHom with h𝔭
  set 𝔧 := RingHom.ker π with h𝔧
  have : IsScalarTower A' P' (AdicCompletion 𝔭 P') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hI𝔧 : I.map (algebraMap A' P') ≤ 𝔧 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, h𝔧, RingHom.mem_ker, π.commutes, IsScalarTower.algebraMap_apply A' A B,
      show algebraMap A' A a = 0 from ha, map_zero]
  obtain ⟨n₀, hn₀⟩ := hnilA
  have hn : I ^ (max n₀ 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (le_max_left _ _)).trans (le_of_eq hn₀))
  -- the flat quotient of `Q'`
  obtain ⟨𝔍, hflat𝔍, h𝔍⟩ := exists_flat_quotient_adicCompletion A' A B P' hsurjA ⟨n₀, hn₀⟩
    π hπ b hlift
  -- generators and syzygies
  obtain ⟨m, s, fh, rh, hfh, hsyz, hrh⟩ :=
    exists_generators_and_syzygyGenerators 𝔧 (I.map (algebraMap A' P'))
  have hIQ : I.map (algebraMap A' (AdicCompletion 𝔭 P')) =
      (I.map (algebraMap A' P')).map (algebraMap P' (AdicCompletion 𝔭 P')) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  -- an exact solution over `Q'`
  have hJ : 𝔍 ⊔ I.map (algebraMap A' (AdicCompletion 𝔭 P')) =
      Ideal.span (Set.range (fun i => algebraMap P' (AdicCompletion 𝔭 P') (fh i))) ⊔
        I.map (algebraMap A' (AdicCompletion 𝔭 P')) := by
    rw [h𝔍, show (fun i => algebraMap P' (AdicCompletion 𝔭 P') (fh i)) =
      algebraMap P' (AdicCompletion 𝔭 P') ∘ fh from rfl,
      Set.range_comp, ← Ideal.map_span, hfh, hIQ, sup_eq_left.mpr (Ideal.map_mono hI𝔧)]
  have := hflat𝔍
  obtain ⟨Ft, Gt, hFt, hGt, -, hrel⟩ := exists_relVec_eq_zero_of_flat_quotient I hn 𝔍
    (fun i => algebraMap P' (AdicCompletion 𝔭 P') (fh i))
    (fun j i => algebraMap P' (AdicCompletion 𝔭 P') (rh j i)) hJ
    (fun j => by
      rw [hIQ, map_mul_sum_helper]
      exact Ideal.mem_map_of_mem _ (hrh j))
  -- `P'/𝔭^N = Q'/𝔭^N Q'`
  have hfg : 𝔭.FG := IsNoetherian.noetherian 𝔭
  have happrox : ∀ (N : ℕ) (y : AdicCompletion 𝔭 P'), ∃ x : P',
      y - algebraMap P' (AdicCompletion 𝔭 P') x ∈
        (𝔭 ^ N).map (algebraMap P' (AdicCompletion 𝔭 P')) := fun N y =>
    AdicCompletion.exists_sub_mem_map_pow 𝔭 hfg N y
  have hcontr : ∀ (N : ℕ) (x : P'), algebraMap P' (AdicCompletion 𝔭 P') x ∈
      (𝔭 ^ N).map (algebraMap P' (AdicCompletion 𝔭 P')) → x ∈ 𝔭 ^ N := fun N _ hx =>
    mem_pow_of_algebraMap_mem_map_adicCompletion 𝔭 N hx
  -- the comparison
  obtain ⟨F, hF, hflatF⟩ := exists_flat_quotient_of_approx
    (algebraMap P' (AdicCompletion 𝔭 P')) 𝔭
    happrox hcontr I (le_max_right n₀ 1) hn fh rh hsyz hrh (hT m s fh rh hfh hsyz hrh) Ft Gt
    (fun i => by rw [← hIQ]; exact hFt i) (fun j i => by rw [← hIQ]; exact hGt j i) hrel
    (fun F hF => flat_reduction_of_sup_eq_ker hsurjA π hπ _ (span_sup_eq_of_sub_mem hF hfh hI𝔧))
  exact hasFlatAlgebraLift_of_flat_quotient hsurjA π hπ _ (span_sup_eq_of_sub_mem hF hfh hI𝔧)

end Converse

/-! ### Stacks 0DZ3 -/

section Tag

/-- **Torsion along an ideal passes to any ideal inside its radical.** If the obstruction is
`𝔭₀`-power torsion and `𝔭 ⊆ √𝔭₀`, it is `𝔭`-power torsion. -/
theorem ObstructionTorsion.of_le_radical {R : Type u} [CommRing R] {𝔦 𝔭 𝔭₀ : Ideal R}
    {m s : ℕ} {fh : Fin m → R} {rh : Fin s → Fin m → R} {k : ℕ} (h : 𝔭 ≤ 𝔭₀.radical)
    (hT : ObstructionTorsion 𝔦 𝔭₀ fh rh k) : ObstructionTorsion 𝔦 𝔭 fh rh k := by
  intro F G hsol g hg
  obtain ⟨n, hn⟩ := h hg
  obtain ⟨e, he⟩ := hT F G hsol (g ^ n) hn
  exact ⟨n * e, by rwa [pow_mul]⟩

/-- **Stacks 0DZ3.** Let `A' → A` be a surjective map of Noetherian rings with nilpotent kernel,
let `A → B` be a finite type flat ring map and let `𝔟 ⊆ B` be an ideal such that
`Spec(B) → Spec(A)` is syntomic on the complement of `V(𝔟)`. Then `B` has a flat lift to `A'` if
and only if the `𝔟`-adic completion `B^∧` has a flat lift to `A'`.

`Spec(B) → Spec(A)` is syntomic at the point `𝔮` exactly when `A → B_g` is syntomic for some
`g ∉ 𝔮` (Stacks 00SY, 01UE); that is how the hypothesis `hsyn` reads the source's condition at
every point `𝔮` of the complement of `V(𝔟)`. The proof does not go through Stacks 0DZ2 (which is
false at a nilpotent kernel); see the module documentation. -/
@[stacks 0DZ3 "`Spec(B) → Spec(A)` being syntomic on the complement of `V(𝔟)` is read pointwise \
and affinely: for every prime `𝔮` not containing `𝔟` there is `g ∉ 𝔮` with `A → B_g` syntomic, \
the characterization of Stacks 00SY and 01UE. `B^∧` is `AdicCompletion 𝔟 B`. The published proof \
rests on Stacks 0DZ2, which is false at a nilpotent kernel; the proof here approximates a flat \
lift over the completed presentation by relation solutions over the polynomial presentation and \
corrects them one power of the kernel at a time (Artin-Rees plus Stacks 07M8 at every level). \
See the module docstring."]
public theorem hasFlatAlgebraLift_iff_hasFlatAlgebraLift_adicCompletion
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ q : Ideal B, q.IsPrime → ¬ b ≤ q →
      ∃ g ∉ q, Algebra.Syntomic A (Localization.Away g)) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A (AdicCompletion b B) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  refine ⟨hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_of_isNoetherianRing A' A B
    hsurjA hnilA b, fun hlift => ?_⟩
  classical
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  -- the syntomic locus, as an ideal whose radical contains `𝔟`
  set b₀ : Ideal B := Ideal.span {g : B | Algebra.Syntomic A (Localization.Away g)} with hb₀
  have hsyn₀ : ∀ h ∈ b₀, Algebra.Syntomic A (Localization.Away h) := fun h hh =>
    syntomic_away_of_mem_span_syntomic hh
  have hbrad : b ≤ b₀.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun q ⟨hb₀q, hq⟩ => ?_
    by_contra hbq
    obtain ⟨g, hgq, hg⟩ := hsyn q hq hbq
    exact hgq (hb₀q (Ideal.subset_span hg))
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType A' A := Algebra.FiniteType.of_surjective (Algebra.ofId A' A) hsurjA
  have : Algebra.FiniteType A' B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A' B)
  have h𝔭 : b.comap π.toRingHom ≤ (b₀.comap π.toRingHom).radical := by
    rw [← Ideal.comap_radical]
    exact Ideal.comap_mono hbrad
  exact hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_obstructionTorsion A' A B
    (MvPolynomial (Fin n) A') hsurjA hnilA π hπ b
    (fun m s fh rh hfh hsyz _ k hk => ObstructionTorsion.of_le_radical h𝔭
      (obstructionTorsion_of_syntomic A' A B _ hsurjA hnilA π hπ b₀ hsyn₀ fh rh hfh hsyz hk))
    hlift

end Tag

end Deformation

end
