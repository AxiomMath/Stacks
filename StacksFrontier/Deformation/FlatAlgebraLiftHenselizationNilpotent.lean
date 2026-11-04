module

public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative
public import StacksFrontier.Deformation.FlatAlgebraLiftRelations
public import StacksFrontier.Deformation.FlatAlgebraLiftSyntomicTorsion
public import StacksFrontier.Deformation.FlatModuleLiftTransport
import all StacksFrontier.Deformation.FlatAlgebraLiftHenselization

/-!
# Stacks 0DZB at a nilpotent kernel

Let `A' → A` be a surjection of Noetherian rings with nilpotent kernel `I`, let `B` be a finite
type flat `A`-algebra and let `𝔟 ⊆ B` be an ideal such that `A → B_h` is syntomic for every
`h ∈ 𝔟`. Stacks 0DZB says that `B` has a flat lift to `A'` if and only if the henselization `Bʰ`
of the pair `(B, 𝔟)` does.

The forward implication is
`Deformation.hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective`. For the
converse the published proofs both rest on Stacks 0DZ2, which is false; this file gives a proof
that avoids it. Present `B` as `P'/𝔧` with `P' = A'[x_1, …, x_n]`, let `𝔭' ⊆ P'` be the preimage
of `𝔟` and `Q'` the henselization of `(P', 𝔭')`.

* A flat lift `C'` of `Bʰ` is a quotient `Q'/𝔍` of `Q'` (a lift of the presentation exists by
  formal smoothness and extends along `Q'` because `C'` is henselian, Stacks 0DYD; it is onto by
  Nakayama), with `𝔍 + IQ' = 𝔧Q'` (Stacks 0DYE). Generators of `𝔍` lifting generators `fh` of `𝔧`
  and lifts of the syzygies `rh` of `fh` modulo `I` then satisfy the relations *exactly*
  (`Deformation.RelationLift.exists_relVec_eq_zero_of_flat_quotient`).
* Since `P'/𝔭'^N = Q'/𝔭'^N Q'` for every `N` (Stacks 0AGU), this exact solution over `Q'` is
  approximated, to any order `N` along `𝔭'`, by a solution over `P'` modulo `I`
  (`Deformation.RelationLift.exists_isSolution_one_of_approx`).
* Above `D(𝔭')` the algebra is syntomic, so the obstruction to improving a solution by one power
  of `I` is `𝔭'`-power torsion; Artin–Rees then turns a good enough approximation into an exact
  solution over `P'` (`Deformation.RelationLift.exists_flat_quotient_of_approx`), and an exact
  solution is a flat lift of `B` (the local criterion of flatness, Stacks 051C).

## Main results

* `Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_henselization`: **Stacks 0DZB**, at the
  source's hypotheses, with no hypothesis standing for Stacks 0DZ2.
* `Deformation.hasFlatAlgebraLift_of_flat_quotient`: a flat quotient of `P'` reducing to `B`
  is a flat algebra lift of `B`.
* `Deformation.exists_flat_quotient_henselization`: a flat lift of `Bʰ` is a flat quotient of
  the henselized presentation `Q'`.
* `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_obstructionTorsion`:
  the converse of Stacks 0DZB, from the torsion of the obstruction, which
  `Deformation.obstructionTorsion_of_syntomic` supplies.

## Implementation notes

The henselization of `(B, 𝔟)` is described by the henselian-pair condition together with the
universal property, as in `StacksFrontier.Deformation.FlatAlgebraLiftHenselization`, whose
conditional `@[stacks 0DZB]` registration (on `h0DZ2`, a hypothesis that is refuted) this file
supersedes. The comparison ring `Q'` is the canonical `henselization P' 𝔭'`. Only `A'` needs to
be Noetherian for the proof; the source's Noetherian hypothesis on `A` is kept.

## References

* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
* [Stacks Project, Tag 0DYD](https://stacks.math.columbia.edu/tag/0DYD)
* [Stacks Project, Tag 0DYE](https://stacks.math.columbia.edu/tag/0DYE)
* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

open RelationLift

section Presentation

variable {A' A B P' : Type u} [CommRing A'] [CommRing A] [CommRing B] [CommRing P']
  [Algebra A' A] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra A' P']

/-- **A flat quotient of a presentation is a flat lift.** If `π : P' → B` is a surjection of
`A'`-algebras and `𝔞 ⊆ P'` is an ideal with `P' ⧸ 𝔞` flat over `A'` and `𝔞 + IP' = ker π`, where
`I = ker(A' → A)`, then `B` has a flat lift to `A'`. -/
theorem hasFlatAlgebraLift_of_flat_quotient (hsurjA : Function.Surjective (algebraMap A' A))
    (π : P' →ₐ[A'] B) (hπ : Function.Surjective π) (𝔞 : Ideal P')
    [Module.Flat A' (P' ⧸ 𝔞)]
    (h𝔞 : 𝔞 ⊔ (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') = RingHom.ker π) :
    HasFlatAlgebraLift A' A B := by
  set I := RingHom.ker (algebraMap A' A)
  have hle : 𝔞 ≤ RingHom.ker π := h𝔞 ▸ le_sup_left
  let πq : (P' ⧸ 𝔞) →ₐ[A'] B := Ideal.Quotient.liftₐ 𝔞 π fun x hx => hle hx
  let Φ : (A ⊗[A'] (P' ⧸ 𝔞)) →ₐ[A] B :=
    Algebra.TensorProduct.lift (Algebra.ofId A B) πq fun _ _ => Commute.all _ _
  have hΦ : ∀ y : P' ⧸ 𝔞, Φ (1 ⊗ₜ y) = πq y := fun y => by
    simp [Φ, Algebra.TensorProduct.lift_tmul]
  have hsurj : Function.Surjective Φ := by
    intro b
    obtain ⟨x, rfl⟩ := hπ b
    refine ⟨1 ⊗ₜ Ideal.Quotient.mk 𝔞 x, ?_⟩
    exact hΦ _
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := surjective_includeRight A' A (P' ⧸ 𝔞) hsurjA z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Φ (1 ⊗ₜ _) = 0 at hz
    rw [hΦ] at hz
    change π x = 0 at hz
    have hx : x ∈ 𝔞 ⊔ I.map (algebraMap A' P') := by rwa [h𝔞]
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have hker : Ideal.Quotient.mk 𝔞 (a + b) ∈ I.map (algebraMap A' (P' ⧸ 𝔞)) := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk 𝔞) hb
      rwa [Ideal.map_map] at this
    rwa [← ker_includeRight A' A (P' ⧸ 𝔞) hsurjA] at hker
  exact ⟨P' ⧸ 𝔞, inferInstance, inferInstance, inferInstance,
    ⟨AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩⟩

end Presentation

/-! ### A flat lift of the henselization is a quotient of the henselized presentation -/

section Henselian

/-- **A flat lift of `Bʰ` is a flat quotient of `Q'`.** Let `π : P' → B` be a surjection of
`A'`-algebras with `P'` formally smooth, `𝔭' = π⁻¹(𝔟)`, `(Q', 𝔭'Q')` the henselization of
`(P', 𝔭')` and `Bʰ` that of `(B, 𝔟)`. A flat lift of `Bʰ` to `A'` is `Q' ⧸ 𝔍` for an ideal `𝔍`
with `𝔍 + IQ' = (ker π) Q'`. -/
theorem exists_flat_quotient_henselization
    (A' A B P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing B] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra A' P']
    [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q'] [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (π : P' →ₐ[A'] B) (hπ : Function.Surjective π) (b : Ideal B)
    (hhensQ : HenselianPair Q' ((b.comap π.toRingHom).map (algebraMap P' Q')))
    (hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : P' →+* D, b.comap π.toRingHom ≤ K.comap f →
        ∃! g : Q' →+* D, g.comp (algebraMap P' Q') = f ∧
          (b.comap π.toRingHom).map (algebraMap P' Q') ≤ K.comap g)
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g)
    (hlift : HasFlatAlgebraLift A' A Bh) :
    ∃ 𝔍 : Ideal Q', Module.Flat A' (Q' ⧸ 𝔍) ∧
      𝔍 ⊔ (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') =
        (RingHom.ker π).map (algebraMap P' Q') := by
  classical
  set I := RingHom.ker (algebraMap A' A)
  set 𝔭 := b.comap π.toRingHom
  obtain ⟨C', _, _, hflatC', ⟨eC⟩⟩ := hlift
  -- the canonical map `Q' → Bʰ`
  let πh : P' →+* Bh := (algebraMap B Bh).comp π.toRingHom
  have hπh𝔭 : 𝔭 ≤ (b.map (algebraMap B Bh)).comap πh := fun x hx =>
    Ideal.mem_map_of_mem _ hx
  obtain ⟨gh, ⟨hgh1, hgh2⟩, -⟩ := hunivQ Bh inferInstance _ hhens πh hπh𝔭
  have hghP : ∀ x : P', gh (algebraMap P' Q' x) = algebraMap B Bh (π x) := RingHom.congr_fun hgh1
  -- algebra structures
  let : Algebra A' Bh := ((algebraMap A Bh).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A Bh := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Q' Bh := gh.toAlgebra
  let : Algebra P' Bh := πh.toAlgebra
  have : IsScalarTower P' Q' Bh := IsScalarTower.of_algebraMap_eq fun x => (hghP x).symm
  have : IsScalarTower A' P' Bh := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A Bh (algebraMap A' A a) = algebraMap B Bh (π (algebraMap A' P' a))
    rw [π.commutes, IsScalarTower.algebraMap_apply A' A B, ← IsScalarTower.algebraMap_apply A B Bh]
  -- the lift `ψ : Q' → C'`
  obtain ⟨ψ, hψ⟩ := exists_algHom_henselization_of_algebraLift A' A P' Q' Bh C' hsurjA hnilA 𝔭
    hunivQ (b.map (algebraMap B Bh)) hhens (fun g hg => Ideal.mem_map_of_mem _ hg) eC
  set ρ : C' →ₐ[A'] Bh := (eC.restrictScalars A').toAlgHom.comp
    Algebra.TensorProduct.includeRight
  have hρψ : ∀ x, ρ (ψ x) = gh x := fun x => hψ x
  have hρker : RingHom.ker ρ = I.map (algebraMap A' C') :=
    ker_comp_includeRight Bh C' hsurjA (eC.restrictScalars A')
  -- `gh` is onto, and its kernel is `(ker π) Q'` (Stacks 0DYE)
  let : Algebra P' B := π.toRingHom.toAlgebra
  have : IsScalarTower P' B Bh := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral P' B := Algebra.isIntegral_of_surjective hπ
  let ghₐ : Q' →ₐ[P'] Bh := { gh with commutes' := fun x => hghP x }
  have hzero : PrimeSpectrum.zeroLocus (b : Set B) =
      PrimeSpectrum.zeroLocus (𝔭.map (algebraMap P' B) : Set B) := by
    rw [show 𝔭.map (algebraMap P' B) = b from Ideal.map_comap_of_surjective _ hπ b]
  have hbij := henselization_tensorProduct_bijective_of_isIntegral P' Q' B Bh 𝔭 b
    (fun x hx => hx) hzero hhensQ hhens hunivQ huniv ghₐ hgh2
  set Φ := Algebra.TensorProduct.lift ghₐ (IsScalarTower.toAlgHom P' B Bh)
    (fun _ _ ↦ Commute.all _ _) with hΦ
  have hΦtmul : ∀ (q : Q') (y : B), Φ (q ⊗ₜ y) = gh q * algebraMap B Bh y := fun q y => by
    rw [hΦ, Algebra.TensorProduct.lift_tmul]
    rfl
  have hghsurj : Function.Surjective gh := by
    intro z
    obtain ⟨t, rfl⟩ := hbij.2 z
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul q y =>
        obtain ⟨p, rfl⟩ := hπ y
        refine ⟨q * algebraMap P' Q' p, ?_⟩
        rw [hΦtmul, map_mul, hghP]
    | add t t' ht ht' =>
        obtain ⟨x, hx⟩ := ht
        obtain ⟨x', hx'⟩ := ht'
        exact ⟨x + x', by rw [map_add, map_add, hx, hx']⟩
  set 𝔧 := RingHom.ker π
  have hkergh : RingHom.ker gh ≤ 𝔧.map (algebraMap P' Q') := by
    intro x hx
    let eB : (P' ⧸ RingHom.ker (Algebra.ofId P' B)) ≃ₐ[P'] B :=
      Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P' B) hπ
    have hle : RingHom.ker (Algebra.ofId P' B) ≤
        (𝔧.map (algebraMap P' Q')).comap (Algebra.ofId P' Q') := fun y hy =>
      Ideal.mem_map_of_mem _ hy
    let τB : B →ₐ[P'] Q' ⧸ 𝔧.map (algebraMap P' Q') :=
      (Ideal.quotientMapₐ _ (Algebra.ofId P' Q') hle).comp eB.symm.toAlgHom
    let τ := Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P' (𝔧.map (algebraMap P' Q'))) τB
      (fun _ _ ↦ Commute.all _ _)
    have h0 : x ⊗ₜ[P'] (1 : B) = 0 := hbij.1 (by rwa [map_zero, hΦtmul, map_one, mul_one])
    have h1 := congrArg τ h0
    rw [map_zero, Algebra.TensorProduct.lift_tmul, map_one, mul_one] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hkergh' : 𝔧.map (algebraMap P' Q') ≤ RingHom.ker gh := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hghP, show π x = 0 from hx, map_zero]
  -- `ψ` is onto, by Nakayama
  have hψsurj : Function.Surjective ψ := by
    have htop : LinearMap.range ψ.toLinearMap ⊔ I • (⊤ : Submodule A' C') = ⊤ := by
      refine eq_top_iff.mpr fun y _ => ?_
      obtain ⟨x, hx⟩ := hghsurj (ρ y)
      have hmem : y - ψ x ∈ I.map (algebraMap A' C') := by
        rw [← hρker, RingHom.mem_ker, map_sub, hρψ, hx, sub_self]
      rw [show y = ψ x + (y - ψ x) by ring]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right ?_)
      rwa [Ideal.smul_top_eq_map]
    intro y
    obtain ⟨x, hx⟩ : y ∈ LinearMap.range ψ.toLinearMap :=
      Submodule.eq_top_of_sup_ideal_smul_top_eq_top hnilA htop ▸ Submodule.mem_top
    exact ⟨x, hx⟩
  have hmap : I.map (algebraMap A' C') = (I.map (algebraMap A' Q')).map ψ.toRingHom := by
    rw [Ideal.map_map, show ψ.toRingHom.comp (algebraMap A' Q') = algebraMap A' C' from
      RingHom.ext fun a => ψ.commutes a]
  refine ⟨RingHom.ker ψ, ?_, ?_⟩
  · exact Module.Flat.of_linearEquiv
      (Ideal.quotientKerAlgEquivOfSurjective (f := ψ) hψsurj).toLinearEquiv
  · apply le_antisymm
    · refine sup_le (fun x hx => hkergh ?_) (fun x hx => hkergh ?_)
      · rw [RingHom.mem_ker, ← hρψ, show ψ x = 0 from hx, map_zero]
      · rw [RingHom.mem_ker, ← hρψ]
        have : ψ x ∈ I.map (algebraMap A' C') := hmap ▸ Ideal.mem_map_of_mem ψ.toRingHom hx
        rwa [← hρker] at this
    · intro x hx
      have hψx : ψ x ∈ I.map (algebraMap A' C') := by
        rw [← hρker, RingHom.mem_ker, hρψ]
        exact hkergh' hx
      rw [hmap] at hψx
      obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective ψ.toRingHom hψsurj).mp hψx
      rw [show x = (x - y) + y by ring]
      refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right hy)
      rw [RingHom.mem_ker, map_sub]
      change ψ x - ψ y = 0
      rw [show ψ y = ψ x from hxy, sub_self]

end Henselian

/-! ### The converse of Stacks 0DZB, from the torsion of the obstruction -/

section Converse

/-- `φ` of a sum of products. -/
theorem map_mul_sum_helper {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {m : ℕ}
    (a b : Fin m → R) :
    ∑ i, algebraMap R S (a i) * algebraMap R S (b i) = algebraMap R S (∑ i, a i * b i) := by
  simp [map_sum, map_mul]

/-- If `F ≡ fh` modulo `𝔦 ⊆ 𝔧` and `(fh) = 𝔧`, then `(F) + 𝔦 = 𝔧`. -/
theorem span_sup_eq_of_sub_mem {R : Type u} [CommRing R] {m : ℕ} {𝔦 𝔧 : Ideal R}
    {F fh : Fin m → R} (hF : ∀ i, F i - fh i ∈ 𝔦) (hfh : Ideal.span (Set.range fh) = 𝔧)
    (h𝔦 : 𝔦 ≤ 𝔧) : Ideal.span (Set.range F) ⊔ 𝔦 = 𝔧 := by
  apply le_antisymm
  · refine sup_le ?_ h𝔦
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [show F i = fh i + (F i - fh i) by ring]
    exact 𝔧.add_mem (hfh ▸ Ideal.subset_span ⟨i, rfl⟩) (h𝔦 (hF i))
  · rw [← hfh, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [show fh i = F i - (F i - fh i) by ring]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mem_sup_right (hF i))

/-- Generators of an ideal and of the syzygies of the generators modulo an ideal, over a
Noetherian ring. -/
theorem exists_generators_and_syzygyGenerators {R : Type u} [CommRing R] [IsNoetherianRing R]
    (𝔧 𝔦 : Ideal R) :
    ∃ (m s : ℕ) (fh : Fin m → R) (rh : Fin s → Fin m → R),
      Ideal.span (Set.range fh) = 𝔧 ∧ SyzygyGenerators 𝔦 fh rh ∧
        ∀ j, ∑ i, rh j i * fh i ∈ 𝔦 := by
  obtain ⟨m, fh, hfh⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian 𝔧)
  let Syz : Submodule R (Fin m → R) :=
    Submodule.comap (Fintype.linearCombination R fh : (Fin m → R) →ₗ[R] R) (𝔦 : Submodule R R)
  obtain ⟨s, rh, hrh⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian Syz)
  have hmem : ∀ c : Fin m → R, c ∈ Syz ↔ ∑ i, c i * fh i ∈ 𝔦 := fun c => by
    simp [Syz, Fintype.linearCombination_apply, smul_eq_mul]
  refine ⟨m, s, fh, rh, hfh, fun c hc => ?_, fun j => ?_⟩
  · have hc' : c ∈ Submodule.span R (Set.range rh) := by rw [hrh]; exact (hmem c).mpr hc
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hc'
    refine ⟨a, fun i => ?_⟩
    rw [← ha]
    simp [Finset.sum_apply, smul_eq_mul]
  · exact (hmem (rh j)).mp (hrh ▸ Submodule.subset_span ⟨j, rfl⟩)

/-- **The converse of Stacks 0DZB, from the torsion of the obstruction.** With `P'`, `π`, `𝔭'`,
`Q'` and `Bʰ` as in `exists_flat_quotient_henselization`, assume `P'` Noetherian and flat over
`A'`, `B` flat over `A`, and that for generators `fh` of `ker π` and syzygy generators `rh` of
`fh` modulo `IP'` the obstruction to improving a solution is `𝔭'`-power torsion. Then a flat lift
of `Bʰ` to `A'` gives a flat lift of `B`. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_obstructionTorsion
    (A' A B P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing B] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra A' P']
    [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q'] [Algebra.FormallySmooth A' P']
    [IsNoetherianRing P'] [Module.Flat A' P'] [Module.Flat A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (π : P' →ₐ[A'] B) (hπ : Function.Surjective π) (b : Ideal B)
    (hT : ∀ (m s : ℕ) (fh : Fin m → P') (rh : Fin s → Fin m → P'),
      Ideal.span (Set.range fh) = RingHom.ker π →
      SyzygyGenerators ((RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) fh rh →
      (∀ j, ∑ i, rh j i * fh i ∈ (RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) →
      ∀ k, 1 ≤ k → ObstructionTorsion ((RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
        (b.comap π.toRingHom) fh rh k)
    (hhensQ : HenselianPair Q' ((b.comap π.toRingHom).map (algebraMap P' Q')))
    (hunivQ : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : P' →+* D, b.comap π.toRingHom ≤ K.comap f →
        ∃! g : Q' →+* D, g.comp (algebraMap P' Q') = f ∧
          (b.comap π.toRingHom).map (algebraMap P' Q') ≤ K.comap g)
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g)
    (hlift : HasFlatAlgebraLift A' A Bh) :
    HasFlatAlgebraLift A' A B := by
  classical
  set I := RingHom.ker (algebraMap A' A)
  set 𝔭 := b.comap π.toRingHom
  set 𝔧 := RingHom.ker π with h𝔧
  have hI𝔧 : I.map (algebraMap A' P') ≤ 𝔧 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, h𝔧, RingHom.mem_ker, π.commutes, IsScalarTower.algebraMap_apply A' A B,
      show algebraMap A' A a = 0 from ha, map_zero]
  obtain ⟨n₀, hn₀⟩ := hnilA
  have hn : I ^ (max n₀ 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (le_max_left _ _)).trans (le_of_eq hn₀))
  -- the flat quotient of `Q'`
  obtain ⟨𝔍, _, h𝔍⟩ := exists_flat_quotient_henselization A' A B P' Q' hsurjA ⟨n₀, hn₀⟩
    π hπ b hhensQ hunivQ Bh hhens huniv hlift
  -- generators and syzygies
  obtain ⟨m, s, fh, rh, hfh, hsyz, hrh⟩ :=
    exists_generators_and_syzygyGenerators 𝔧 (I.map (algebraMap A' P'))
  have hIQ : I.map (algebraMap A' Q') = (I.map (algebraMap A' P')).map (algebraMap P' Q') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  -- an exact solution over `Q'`
  have hJ : 𝔍 ⊔ I.map (algebraMap A' Q') =
      Ideal.span (Set.range (fun i => algebraMap P' Q' (fh i))) ⊔ I.map (algebraMap A' Q') := by
    rw [h𝔍, show (fun i => algebraMap P' Q' (fh i)) = algebraMap P' Q' ∘ fh from rfl,
      Set.range_comp, ← Ideal.map_span, hfh, hIQ, sup_eq_left.mpr (Ideal.map_mono hI𝔧)]
  obtain ⟨Ft, Gt, hFt, hGt, -, hrel⟩ := exists_relVec_eq_zero_of_flat_quotient I hn 𝔍
    (fun i => algebraMap P' Q' (fh i)) (fun j i => algebraMap P' Q' (rh j i)) hJ
    (fun j => by
      rw [hIQ, map_mul_sum_helper]
      exact Ideal.mem_map_of_mem _ (hrh j))
  -- Stacks 0AGU: `P'/𝔭^N = Q'/𝔭^N Q'`
  obtain ⟨-, hbij⟩ := flat_henselization_and_bijective_quotientMap P' 𝔭 Q' hhensQ
    (fun D _ K hK f hf => hunivQ D inferInstance K hK f hf)
  have happrox : ∀ (N : ℕ) (y : Q'), ∃ x : P', y - algebraMap P' Q' x ∈
      (𝔭 ^ N).map (algebraMap P' Q') := fun N y =>
    exists_sub_mem_map_of_bijective_quotientMap (𝔭 ^ N) (hbij N) y
  have hcontr : ∀ (N : ℕ) (x : P'), algebraMap P' Q' x ∈ (𝔭 ^ N).map (algebraMap P' Q') →
      x ∈ 𝔭 ^ N := fun N x hx =>
    mem_of_algebraMap_mem_map_of_bijective_quotientMap (𝔭 ^ N) (hbij N) hx
  -- the comparison
  obtain ⟨F, hF, hflatF⟩ := exists_flat_quotient_of_approx (algebraMap P' Q') 𝔭 happrox hcontr I
    (le_max_right n₀ 1) hn fh rh hsyz hrh (hT m s fh rh hfh hsyz hrh) Ft Gt
    (fun i => by rw [← hIQ]; exact hFt i) (fun j i => by rw [← hIQ]; exact hGt j i) hrel
    (fun F hF => flat_reduction_of_sup_eq_ker hsurjA π hπ _ (span_sup_eq_of_sub_mem hF hfh hI𝔧))
  exact hasFlatAlgebraLift_of_flat_quotient hsurjA π hπ _ (span_sup_eq_of_sub_mem hF hfh hI𝔧)

end Converse

/-! ### Stacks 0DZB -/

section Tag

/-- **Stacks 0DZB.** Let `A' → A` be a surjective map of Noetherian rings with nilpotent kernel,
let `A → B` be a finite type flat ring map and let `𝔟 ⊆ B` be an ideal such that
`Spec(B) → Spec(A)` is syntomic on the complement of `V(𝔟)`, that is `A → B_h` is syntomic for
every `h ∈ 𝔟`. Let `(Bʰ, 𝔟ʰ)` be the henselization of the pair `(B, 𝔟)`. Then `B` has a flat lift
to `A'` if and only if `Bʰ` has a flat lift to `A'`.

The proof does not go through Stacks 0DZ2 (which is false); see the module documentation. -/
@[stacks 0DZB "The henselization of the pair `(B, 𝔟)` is described by the henselian-pair condition
`hhens` together with its universal property `huniv`, as in Stacks 0DZC, rather than by a chosen
model; the syntomic hypothesis is the affine reading: the complement of `V(𝔟)` is covered by the
`D(h)`, `h ∈ 𝔟`. Both published proofs rest on Stacks 0DZ2, which is false; the proof here
approximates a flat lift over the henselized presentation by solutions over the polynomial
presentation and corrects them one power of the kernel at a time (Artin-Rees plus Stacks 07M8 at
every level). See the module docstring."]
public theorem hasFlatAlgebraLift_iff_hasFlatAlgebraLift_henselization
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A Bh := by
  refine ⟨hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective A' A B hsurjA b Bh
    hhens huniv, fun hlift => ?_⟩
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType A' A := Algebra.FiniteType.of_surjective (Algebra.ofId A' A) hsurjA
  have : Algebra.FiniteType A' B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A' B)
  set P' := MvPolynomial (Fin n) A'
  set 𝔭 := b.comap π.toRingHom
  let Q' : Type u := (henselization P' 𝔭 : Type u)
  let : Algebra A' Q' := ((algebraMap P' Q').comp (algebraMap A' P')).toAlgebra
  have : IsScalarTower A' P' Q' := IsScalarTower.of_algebraMap_eq' rfl
  exact hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_obstructionTorsion A' A B P' Q'
    hsurjA hnilA π hπ b
    (fun m s fh rh hfh hsyz _ k hk =>
      obstructionTorsion_of_syntomic A' A B P' hsurjA hnilA π hπ b hsyn fh rh hfh hsyz hk)
    (henselianPair_henselization P' 𝔭) (henselization_universalProperty P' 𝔭) Bh hhens huniv hlift

end Tag

end Deformation

end
