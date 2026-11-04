module

public import StacksFrontier.Deformation.FlatAlgebraLift
public import StacksFrontier.Deformation.FlatModuleLift
public import StacksFrontier.Deformation.FlatModuleLiftTransport
public import StacksFrontier.Deformation.FlatAlgebraLiftRelations
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Algebra
import all StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections.SyntomicLift

/-!
# The obstruction to lifting a syntomic algebra is torsion

Let `A' → A` be a surjection with nilpotent kernel `I`, let `P'` be a formally smooth `A'`-algebra
of finite presentation, flat over `A'`, and let `π : P' → B` present an `A`-algebra `B` with
`A → B_h` syntomic for every `h` in an ideal `𝔟 ⊆ B`. For generators `fh` of `ker π` and syzygy
generators `rh` of `fh` modulo `IP'`, this file proves that the obstruction to improving a
`k`-solution `(F, G)` (in the sense of `Deformation.RelationLift`) by one power of `I` is
`π⁻¹(𝔟)`-power torsion, `Deformation.obstructionTorsion_of_syntomic`.

The argument is the one Stacks gives for the local liftability in 0DZ3, 0DZ7 and 0DZB, applied at
each level rather than once. Let `g ∈ π⁻¹(𝔟)`. Over `P'_g`, the solution presents a flat lift
`B_k` of the syntomic algebra `B_ḡ` to `A'/I^k` (local criterion of flatness), so `B_k` is
syntomic (its fibres are those of `B_ḡ`). By Stacks 07M8 it lifts to a syntomic, in particular
flat, `A'`-algebra; the presentation of `B_k` lifts to it by formal smoothness, and the kernel of
the lift is a flat lift of the ideal of `B_k`, which makes the relation vector solvable over
`P'_g` (`Deformation.RelationLift.relVec_mem_solvable_of_lift`). Clearing denominators gives a
power of `g`.

## Main results

* `Deformation.syntomic_of_flat_of_surjective`: a flat finitely presented lift of a syntomic
  algebra along a nilpotent thickening is syntomic.
* `Deformation.exists_flat_quotient_of_syntomic`: Stacks 07M8 for an embedded lift.
* `Deformation.obstructionTorsion_of_syntomic`: the torsion of the obstruction.

## References

* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

open RelationLift


/-- If `F ≡ fh` modulo `𝔦`, then `(F) + 𝔦 = (fh) + 𝔦`. -/
theorem span_sup_eq_of_sub_mem' {R : Type u} [CommRing R] {m : ℕ} {𝔦 : Ideal R}
    {F fh : Fin m → R} (hF : ∀ i, F i - fh i ∈ 𝔦) :
    Ideal.span (Set.range F) ⊔ 𝔦 = Ideal.span (Set.range fh) ⊔ 𝔦 := by
  apply le_antisymm <;> refine sup_le ?_ le_sup_right <;> rw [Ideal.span_le] <;>
    rintro _ ⟨i, rfl⟩
  · rw [show F i = fh i + (F i - fh i) by ring]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mem_sup_right (hF i))
  · rw [show fh i = F i - (F i - fh i) by ring]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      (Ideal.mem_sup_right (hF i))

section Reduction

variable {A' A B P' : Type u} [CommRing A'] [CommRing A] [CommRing B] [CommRing P']
  [Algebra A' A] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra A' P']

/-- **The reduction of a quotient lifting `B` is flat.** If `π : P' → B` is a surjection of
`A'`-algebras, `B` is flat over `A`, and `𝔞 + IP' = ker π`, then `(P' ⧸ 𝔞) ⧸ I(P' ⧸ 𝔞)` is flat
over `A' ⧸ I`. -/
theorem flat_reduction_of_sup_eq_ker (hsurjA : Function.Surjective (algebraMap A' A))
    [Module.Flat A B] (π : P' →ₐ[A'] B) (hπ : Function.Surjective π) (𝔞 : Ideal P')
    (h𝔞 : 𝔞 ⊔ (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') = RingHom.ker π) :
    Module.Flat (A' ⧸ RingHom.ker (algebraMap A' A))
      ((P' ⧸ 𝔞) ⧸ (RingHom.ker (algebraMap A' A) • (⊤ : Submodule A' (P' ⧸ 𝔞)))) := by
  set I := RingHom.ker (algebraMap A' A) with hI
  set N := I • (⊤ : Submodule A' (P' ⧸ 𝔞)) with hN
  have hle : 𝔞 ≤ RingHom.ker π := h𝔞 ▸ le_sup_left
  let πq : (P' ⧸ 𝔞) →ₐ[A'] B := Ideal.Quotient.liftₐ 𝔞 π fun x hx => hle hx
  have hNle : N ≤ LinearMap.ker πq.toLinearMap := by
    rw [hN, Submodule.smul_le]
    intro a ha y _
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_smul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A' A B, show algebraMap A' A a = 0 from ha, map_zero,
      zero_mul]
  let ψ : ((P' ⧸ 𝔞) ⧸ N) →ₗ[A'] B := N.liftQ πq.toLinearMap hNle
  have hψ : ∀ x, ψ (Submodule.Quotient.mk (Ideal.Quotient.mk 𝔞 x)) = π x := fun _ => rfl
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨_, hψ x⟩
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hψ] at hz
    have hx : x ∈ 𝔞 ⊔ I.map (algebraMap A' P') := by rw [h𝔞]; exact hz
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
    rw [Submodule.Quotient.mk_eq_zero, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    have hc' : c ∈ I • (⊤ : Submodule A' P') := by rw [Ideal.smul_top_eq_map]; exact hc
    refine Submodule.smul_induction_on hc' (fun r hr t _ => ?_) (fun x y hx hy => ?_)
    · change (Ideal.Quotient.mkₐ A' 𝔞) (r • t) ∈ N
      rw [map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]; exact Submodule.add_mem _ hx hy
  let e : ((P' ⧸ 𝔞) ⧸ N) ≃ₗ[A'] B := LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  let ε : A ≃+* A' ⧸ I := (RingHom.quotientKerEquivOfSurjective hsurjA).symm
  refine Deformation.flat_of_ringEquiv ε e.symm.toAddEquiv (fun r y => ?_) inferInstance
  obtain ⟨a, rfl⟩ := hsurjA r
  have hε : ε (algebraMap A' A a) = Ideal.Quotient.mk I a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [hε, LinearEquiv.coe_toAddEquiv, show algebraMap A' A a • y = a • y from
    (IsScalarTower.algebraMap_smul A a y)]
  exact e.symm.map_smul a y

end Reduction


/-- An element whose class modulo `J` lies in `𝔞 (R ⧸ J)` lies in `𝔞 + J`. -/
private theorem mem_sup_of_mk_mem_map {R : Type u} [CommRing R] {J 𝔞 : Ideal R} {y : R}
    (h : Ideal.Quotient.mk J y ∈ 𝔞.map (Ideal.Quotient.mk J)) : y ∈ 𝔞 ⊔ J := by
  obtain ⟨z, hz, hzy⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h
  have hd : y - z ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hzy, sub_self]
  rw [show y = z + (y - z) by ring]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hz) (Ideal.mem_sup_right hd)

/-- If `J ≤ 𝔟` and `(𝔞 + J) ∩ 𝔟 ⊆ 𝔟𝔞 + J`, then `𝔞 ∩ 𝔟 ⊆ 𝔟𝔞` holds modulo `J`. -/
private theorem map_mk_inf_le_mul_of_le {R : Type u} [CommRing R] {J 𝔞 𝔟 : Ideal R} (hJ : J ≤ 𝔟)
    (h : (𝔞 ⊔ J) ⊓ 𝔟 ≤ 𝔟 * 𝔞 ⊔ J) :
    𝔞.map (Ideal.Quotient.mk J) ⊓ 𝔟.map (Ideal.Quotient.mk J) ≤
      𝔟.map (Ideal.Quotient.mk J) * 𝔞.map (Ideal.Quotient.mk J) := by
  rintro x ⟨hx𝔞, hx𝔟⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (h ⟨mem_sup_of_mk_mem_map hx𝔞, sup_le le_rfl hJ (mem_sup_of_mk_mem_map hx𝔟)⟩)
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero, ← Ideal.map_mul]
  exact Ideal.mem_map_of_mem _ ha

/-- **A `k`-solution presents a flat lift to `Λ ⧸ 𝔫 ^ k`**, in the form
`(S ⧸ 𝔫^k S) ⧸ (F)`; see `Deformation.flat_quotient_of_isSolution`. -/
private theorem flat_quotient_map_of_isSolution {Λ A S B₀ : Type u} [CommRing Λ] [CommRing A]
    [CommRing S] [CommRing B₀] [Algebra Λ A] [Algebra Λ S] [Module.Flat Λ S] [Algebra A B₀]
    [Algebra Λ B₀] [IsScalarTower Λ A B₀] [Module.Flat A B₀]
    (hsurj : Function.Surjective (algebraMap Λ A)) {k : ℕ} (hk : 1 ≤ k) {m s : ℕ}
    {fh : Fin m → S} {rh : Fin s → Fin m → S}
    (hsyz : SyzygyGenerators ((RingHom.ker (algebraMap Λ A)).map (algebraMap Λ S)) fh rh)
    {F : Fin m → S} {G : Fin s → Fin m → S}
    (hsol : IsSolution ((RingHom.ker (algebraMap Λ A)).map (algebraMap Λ S)) fh rh k F G)
    (π : S →ₐ[Λ] B₀) (hπ : Function.Surjective π)
    (hker : Ideal.span (Set.range fh) ⊔ (RingHom.ker (algebraMap Λ A)).map (algebraMap Λ S) =
      RingHom.ker π) :
    Module.Flat (Λ ⧸ RingHom.ker (algebraMap Λ A) ^ k)
      ((S ⧸ (RingHom.ker (algebraMap Λ A) ^ k).map (algebraMap Λ S)) ⧸
        (Ideal.span (Set.range F)).map
          (Ideal.Quotient.mk ((RingHom.ker (algebraMap Λ A) ^ k).map (algebraMap Λ S)))) := by
  set 𝔫 := RingHom.ker (algebraMap Λ A) with h𝔫
  set 𝔦 := 𝔫.map (algebraMap Λ S) with h𝔦
  set Λk := Λ ⧸ 𝔫 ^ k
  set Sk := S ⧸ (𝔫 ^ k).map (algebraMap Λ S)
  have : Module.Flat Λk Sk := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (𝔫 ^ k)).toLinearEquiv
  have hpow : 𝔫 ^ k ≤ RingHom.ker (algebraMap Λ A) := Ideal.pow_le_self (by omega)
  let : Algebra Λk A := (Ideal.Quotient.lift (𝔫 ^ k) (algebraMap Λ A) hpow).toAlgebra
  have : IsScalarTower Λ Λk A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra Λk B₀ := ((algebraMap A B₀).comp (algebraMap Λk A)).toAlgebra
  have : IsScalarTower Λk A B₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Λ Λk B₀ := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap Λ B₀ a = algebraMap A B₀ (algebraMap Λ A a)
    rw [IsScalarTower.algebraMap_apply Λ A B₀]
  have hsurjk : Function.Surjective (algebraMap Λk A) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hkerk : RingHom.ker (algebraMap Λk A) = 𝔫.map (Ideal.Quotient.mk (𝔫 ^ k)) :=
    Ideal.ker_quotient_lift _ hpow
  have hπk : (𝔫 ^ k).map (algebraMap Λ S) ≤ RingHom.ker π := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
      IsScalarTower.algebraMap_apply Λ A B₀, show algebraMap Λ A a = 0 from hpow ha, map_zero]
  let πk : Sk →ₐ[Λk] B₀ :=
    { (Ideal.Quotient.lift _ π.toRingHom hπk) with
      commutes' := fun x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        change π (algebraMap Λ S a) = algebraMap A B₀ (algebraMap Λ A a)
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply Λ A B₀] }
  have hπksurj : Function.Surjective πk := Ideal.Quotient.lift_surjective_of_surjective _ _ hπ
  set 𝔞 : Ideal Sk := (Ideal.span (Set.range F)).map (Ideal.Quotient.mk _) with h𝔞
  have hmapk : (RingHom.ker (algebraMap Λk A)).map (algebraMap Λk Sk) =
      𝔦.map (Ideal.Quotient.mk ((𝔫 ^ k).map (algebraMap Λ S))) := by
    rw [hkerk, Ideal.map_map, h𝔦, Ideal.map_map]
    rfl
  have hF𝔦 : Ideal.span (Set.range F) ⊔ 𝔦 = RingHom.ker π :=
    (span_sup_eq_of_sub_mem' hsol.1).trans hker
  have hsup : 𝔞 ⊔ (RingHom.ker (algebraMap Λk A)).map (algebraMap Λk Sk) = RingHom.ker πk := by
    rw [hmapk, h𝔞, ← Ideal.map_sup, hF𝔦]
    exact (Ideal.ker_quotient_lift π.toRingHom hπk).symm
  have hrel : 𝔞 ⊓ (RingHom.ker (algebraMap Λk A)).map (algebraMap Λk Sk) ≤
      (RingHom.ker (algebraMap Λk A)).map (algebraMap Λk Sk) * 𝔞 := by
    rw [hmapk, h𝔞]
    refine map_mk_inf_le_mul_of_le (Ideal.map_mono (Ideal.pow_le_self (by omega))) ?_
    rw [Ideal.map_pow]
    exact span_sup_pow_inf_le_of_isSolution hsyz hk hsol
  exact RelationLift.flat_quotient_of_inf_le_mul _
    ⟨k, hk, by rw [hkerk, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]⟩ 𝔞
    (flat_reduction_of_sup_eq_ker hsurjk πk hπksurj 𝔞 hsup) hrel

/-- **A `k`-solution presents a flat lift to `Λ ⧸ 𝔫 ^ k`.** Let `Λ → A` be surjective with
kernel `𝔫`, `S` a flat `Λ`-algebra and `π : S → B₀` a surjection onto a flat `A`-algebra,
compatible with `Λ → A`, with `ker π = (fh) + 𝔫S`. If the `rh` generate the syzygies of `fh`
modulo `𝔫S` and `(F, G)` is a `k`-solution, `k ≥ 1`, then `S ⧸ ((F) + 𝔫^k S)` is flat over
`Λ ⧸ 𝔫 ^ k`. -/
theorem flat_quotient_of_isSolution {Λ A S B₀ : Type u} [CommRing Λ] [CommRing A] [CommRing S]
    [CommRing B₀] [Algebra Λ A] [Algebra Λ S] [Module.Flat Λ S] [Algebra A B₀] [Algebra Λ B₀]
    [IsScalarTower Λ A B₀] [Module.Flat A B₀]
    (hsurj : Function.Surjective (algebraMap Λ A)) {k : ℕ} (hk : 1 ≤ k) {m s : ℕ}
    {fh : Fin m → S} {rh : Fin s → Fin m → S}
    (hsyz : SyzygyGenerators ((RingHom.ker (algebraMap Λ A)).map (algebraMap Λ S)) fh rh)
    {F : Fin m → S} {G : Fin s → Fin m → S}
    (hsol : IsSolution ((RingHom.ker (algebraMap Λ A)).map (algebraMap Λ S)) fh rh k F G)
    (π : S →ₐ[Λ] B₀) (hπ : Function.Surjective π)
    (hker : Ideal.span (Set.range fh) ⊔ (RingHom.ker (algebraMap Λ A)).map (algebraMap Λ S) =
      RingHom.ker π) :
    letI : Algebra (Λ ⧸ RingHom.ker (algebraMap Λ A) ^ k)
        (S ⧸ (Ideal.span (Set.range F) ⊔ (RingHom.ker (algebraMap Λ A) ^ k).map
          (algebraMap Λ S))) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_sup_right)
    Module.Flat (Λ ⧸ RingHom.ker (algebraMap Λ A) ^ k)
      (S ⧸ (Ideal.span (Set.range F) ⊔ (RingHom.ker (algebraMap Λ A) ^ k).map
        (algebraMap Λ S))) := by
  set 𝔫 := RingHom.ker (algebraMap Λ A) with h𝔫
  set Λk := Λ ⧸ 𝔫 ^ k
  set Sk := S ⧸ (𝔫 ^ k).map (algebraMap Λ S)
  set 𝔞 : Ideal Sk := (Ideal.span (Set.range F)).map (Ideal.Quotient.mk _) with h𝔞
  have hflat : Module.Flat Λk (Sk ⧸ 𝔞) :=
    flat_quotient_map_of_isSolution hsurj hk hsyz hsol π hπ hker
  let : Algebra Λk (S ⧸ (Ideal.span (Set.range F) ⊔ (𝔫 ^ k).map (algebraMap Λ S))) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_sup_right)
  let e : (Sk ⧸ 𝔞) ≃+* (S ⧸ (Ideal.span (Set.range F) ⊔ (𝔫 ^ k).map (algebraMap Λ S))) :=
    (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq (sup_comm _ _))
  let eₗ : (Sk ⧸ 𝔞) ≃ₗ[Λk] (S ⧸ (Ideal.span (Set.range F) ⊔ (𝔫 ^ k).map (algebraMap Λ S))) :=
    { e with
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        exact (map_mul e _ _).trans rfl }
  exact Module.Flat.of_linearEquiv eₗ.symm

/-- A nilpotent ideal lies in every prime. -/
theorem le_of_isNilpotent_of_isPrime {R : Type u} [CommRing R] {𝔫 : Ideal R} (h𝔫 : IsNilpotent 𝔫)
    (p : Ideal R) [p.IsPrime] : 𝔫 ≤ p := by
  obtain ⟨n, hn⟩ := h𝔫
  intro x hx
  have h := Ideal.pow_mem_pow hx n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact ‹p.IsPrime›.mem_of_pow_mem n (h ▸ p.zero_mem)

/-- **A flat lift of a syntomic algebra along a nilpotent thickening is syntomic.** Let `Λ → A`
be surjective with nilpotent kernel `𝔫`, `B` a flat finitely presented `Λ`-algebra and
`β : B → B₀` a surjection onto a syntomic `A`-algebra, compatible with `Λ → A`, with kernel
`𝔫B`. Then `B` is syntomic over `Λ`. -/
theorem syntomic_of_flat_of_surjective {Λ A B B₀ : Type u} [CommRing Λ] [CommRing A] [CommRing B]
    [CommRing B₀] [Algebra Λ A] [Algebra Λ B] [Algebra A B₀] [Algebra Λ B₀] [IsScalarTower Λ A B₀]
    [Module.Flat Λ B] [Algebra.FinitePresentation Λ B] [Algebra.Syntomic A B₀]
    (hsurj : Function.Surjective (algebraMap Λ A))
    (hnil : IsNilpotent (RingHom.ker (algebraMap Λ A))) (β : B →ₐ[Λ] B₀)
    (hβ : Function.Surjective β)
    (hker : RingHom.ker β = (RingHom.ker (algebraMap Λ A)).map (algebraMap Λ B)) :
    Algebra.Syntomic Λ B := by
  set 𝔫 := RingHom.ker (algebraMap Λ A) with h𝔫
  let eA : (Λ ⧸ 𝔫) ≃+* A := RingHom.quotientKerEquivOfSurjective hsurj
  let : Algebra (Λ ⧸ 𝔫) A := eA.toRingHom.toAlgebra
  let : Algebra (Λ ⧸ 𝔫) B₀ := ((algebraMap A B₀).comp (algebraMap (Λ ⧸ 𝔫) A)).toAlgebra
  have : IsScalarTower (Λ ⧸ 𝔫) A B₀ := IsScalarTower.of_algebraMap_eq' rfl
  have hbij : Function.Bijective (algebraMap (Λ ⧸ 𝔫) A) := eA.bijective
  have : Algebra.Syntomic (Λ ⧸ 𝔫) B₀ := Stacks.Smoothing.syntomic_restrictScalars_of_bijective hbij
  let eB₀ : (B ⧸ 𝔫.map (algebraMap Λ B)) ≃+* B₀ :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hβ)
  have heB₀ : ∀ x : B, eB₀ (Ideal.Quotient.mk _ x) = β x := fun _ => rfl
  let eB : B₀ ≃ₐ[Λ ⧸ 𝔫] (B ⧸ 𝔫.map (algebraMap Λ B)) :=
    AlgEquiv.ofRingEquiv (f := eB₀.symm) (fun x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingEquiv.symm_apply_eq, Ideal.Quotient.algebraMap_quotient_map_quotient, heB₀,
        AlgHom.commutes]
      change algebraMap A B₀ (eA (Ideal.Quotient.mk 𝔫 a)) = _
      rw [IsScalarTower.algebraMap_apply Λ A B₀]
      rfl)
  have : Algebra.Syntomic (Λ ⧸ 𝔫) (B ⧸ 𝔫.map (algebraMap Λ B)) :=
    Stacks.SyntomicLocus.Algebra.Syntomic.of_algEquiv eB
  refine Stacks.Smoothing.syntomic_of_local_flat_and_completeIntersection fun q _ => ⟨?_, ?_⟩
  · exact Module.Flat.trans Λ B (Localization.AtPrime q)
  · exact Stacks.Smoothing.completeIntersection_fiber_of_syntomic_quotient 𝔫 q
      (le_of_isNilpotent_of_isPrime hnil _)

/-- **Stacks 07M8 for an embedded lift.** Let `S` be a formally smooth `A'`-algebra, `𝔪 ⊆ A'` a
nilpotent ideal and `γ : S → D` a surjection, compatible with `A' → A' ⧸ 𝔪`, onto a syntomic
`A' ⧸ 𝔪`-algebra. Then there is an ideal `Ĵ ⊆ S` with `S ⧸ Ĵ` flat over `A'` and
`Ĵ + 𝔪S = ker γ`. -/
theorem exists_flat_quotient_of_syntomic {A' S D : Type u} [CommRing A'] [CommRing S]
    [CommRing D] [Algebra A' S] [Algebra.FormallySmooth A' S] (𝔪 : Ideal A') (h𝔪 : IsNilpotent 𝔪)
    [Algebra (A' ⧸ 𝔪) D] [Algebra.Syntomic (A' ⧸ 𝔪) D] (γ : S →+* D)
    (hγ : Function.Surjective γ)
    (hγA : ∀ a : A', γ (algebraMap A' S a) = algebraMap (A' ⧸ 𝔪) D (Ideal.Quotient.mk 𝔪 a)) :
    ∃ Ĵ : Ideal S, Module.Flat A' (S ⧸ Ĵ) ∧ Ĵ ⊔ 𝔪.map (algebraMap A' S) = RingHom.ker γ := by
  obtain ⟨Ã, _, _, hÃsyn, e, he⟩ := Stacks.Smoothing.exists_syntomic_lift_of_surjective A'
    (A' ⧸ 𝔪) D Ideal.Quotient.mk_surjective inferInstance
  have := hÃsyn
  have h𝔪' : RingHom.ker (algebraMap A' (A' ⧸ 𝔪)) = 𝔪 := Ideal.mk_ker
  generalize hK : (RingHom.ker (algebraMap A' (A' ⧸ 𝔪))).map (algebraMap A' Ã) = K at e he
  rw [h𝔪'] at hK
  let τ : S →ₐ[A'] Ã ⧸ K :=
    { (e.toRingHom.comp γ) with
      commutes' := fun r => by
        change e (γ (algebraMap A' S r)) = _
        rw [hγA]
        exact he r }
  have hτ : ∀ x, τ x = e (γ x) := fun _ => rfl
  have hτsurj : Function.Surjective τ := fun y => by
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := hγ z
    exact ⟨x, rfl⟩
  let q : Ã →ₐ[A'] Ã ⧸ K := Ideal.Quotient.mkₐ A' K
  have hqsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hqker : RingHom.ker q = K := Ideal.Quotient.mkₐ_ker A' K
  have hqnil : IsNilpotent (RingHom.ker q) := by
    rw [hqker, ← hK]; exact isNilpotent_ideal_map h𝔪 _
  let ψ : S →ₐ[A'] Ã := Algebra.FormallySmooth.liftOfSurjective τ q hqsurj hqnil
  have hψ : ∀ x, q (ψ x) = τ x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply τ q hqsurj hqnil x
  have hKψ : K = (𝔪.map (algebraMap A' S)).map ψ.toRingHom := by
    rw [← hK, Ideal.map_map, show ψ.toRingHom.comp (algebraMap A' S) = algebraMap A' Ã from
      RingHom.ext fun a => ψ.commutes a]
  have hψsurj : Function.Surjective ψ := by
    have htop : LinearMap.range ψ.toLinearMap ⊔ 𝔪 • (⊤ : Submodule A' Ã) = ⊤ := by
      refine eq_top_iff.mpr fun y _ => ?_
      obtain ⟨x, hx⟩ := hτsurj (q y)
      have hmem : y - ψ x ∈ K := by
        rw [← hqker, RingHom.mem_ker, map_sub, hψ, hx, sub_self]
      rw [show y = ψ x + (y - ψ x) by ring]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right ?_)
      rw [Ideal.smul_top_eq_map, hK]; exact hmem
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_sup_ideal_smul_top_eq_top h𝔪 htop)
  refine ⟨RingHom.ker ψ, Module.Flat.of_linearEquiv
    (Ideal.quotientKerAlgEquivOfSurjective (f := ψ) hψsurj).toLinearEquiv, ?_⟩
  ext x
  have h1 : x ∈ RingHom.ker γ ↔ ψ x ∈ K := by
    rw [← hqker, RingHom.mem_ker, RingHom.mem_ker, hψ, hτ, map_eq_zero_iff _ e.injective]
  rw [h1, hKψ]
  change x ∈ _ ↔ x ∈ Ideal.comap ψ.toRingHom (Ideal.map ψ.toRingHom _)
  rw [Ideal.comap_map_of_surjective ψ.toRingHom hψsurj, sup_comm]
  rfl

/-! ### Localizing solutions -/

section Localize

variable {R S : Type u} [CommRing R] [CommRing S] {m s : ℕ}

/-- Solutions are transported along ring maps. -/
theorem isSolution_map (φ : R →+* S) {𝔦 : Ideal R} {fh : Fin m → R} {rh : Fin s → Fin m → R}
    {k : ℕ} {F : Fin m → R} {G : Fin s → Fin m → R} (h : IsSolution 𝔦 fh rh k F G) :
    IsSolution (𝔦.map φ) (fun i => φ (fh i)) (fun j i => φ (rh j i)) k (fun i => φ (F i))
      (fun j i => φ (G j i)) := by
  obtain ⟨hF, hG, hrel⟩ := h
  refine ⟨fun i => ?_, fun j i => ?_, fun j => ?_⟩
  · rw [← map_sub]; exact Ideal.mem_map_of_mem _ (hF i)
  · rw [← map_sub]; exact Ideal.mem_map_of_mem _ (hG j i)
  · rw [← Ideal.map_pow]
    simpa [map_sum, map_mul] using Ideal.mem_map_of_mem φ (hrel j)

variable [Algebra R S] (g : R) [IsLocalization.Away g S]

/-- Common exponent: a power of `g` making each member of a finite family land in an ideal. -/
theorem exists_pow_mul_mem_of_forall {n : ℕ} {𝔞 : Ideal R} {x : Fin n → R}
    (h : ∀ i, ∃ e : ℕ, g ^ e * x i ∈ 𝔞) : ∃ e : ℕ, ∀ i, g ^ e * x i ∈ 𝔞 := by
  choose e he using h
  refine ⟨∑ i, e i, fun i => ?_⟩
  have hle : e i ≤ ∑ i, e i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact 𝔞.mul_mem_left _ (he i)

/-- An element of `R` whose image in `R_g` lies in `𝔞 R_g` lies in `𝔞` after multiplying by a
power of `g`. -/
theorem exists_pow_mul_mem_of_algebraMap_mem {𝔞 : Ideal R} {x : R}
    (hx : algebraMap R S x ∈ 𝔞.map (algebraMap R S)) : ∃ e : ℕ, g ^ e * x ∈ 𝔞 := by
  obtain ⟨_, ⟨e, rfl⟩, he⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) S 𝔞 x).mp hx
  exact ⟨e, he⟩

/-- An element of `𝔞 R_g` is, after multiplying by a power of `g`, the image of an element of
`𝔞`. -/
theorem exists_pow_mul_eq_of_mem_map {𝔞 : Ideal R} {y : S} (hy : y ∈ 𝔞.map (algebraMap R S)) :
    ∃ (e : ℕ) (c : R), c ∈ 𝔞 ∧ algebraMap R S (g ^ e) * y = algebraMap R S c := by
  obtain ⟨⟨⟨c, hc⟩, ⟨_, e, rfl⟩⟩, h⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) S).mp hy
  exact ⟨e, c, hc, (mul_comm _ _).trans h⟩

include g in
/-- **Syzygy generators localize.** -/
theorem syzygyGenerators_localization {𝔦 : Ideal R} {fh : Fin m → R} {rh : Fin s → Fin m → R}
    (hsyz : SyzygyGenerators 𝔦 fh rh) :
    SyzygyGenerators (𝔦.map (algebraMap R S)) (fun i => algebraMap R S (fh i))
      (fun j i => algebraMap R S (rh j i)) := by
  intro c hc
  obtain ⟨⟨_, n, rfl⟩, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers g) c
  choose d hd using hb
  have hcd : ∀ i, algebraMap R S (g ^ n) * c i = algebraMap R S (d i) := fun i => by
    rw [hd i, Algebra.smul_def]
  have hsum : algebraMap R S (∑ i, d i * fh i) ∈ 𝔦.map (algebraMap R S) := by
    rw [map_sum]
    simp_rw [map_mul, ← hcd, mul_assoc, ← Finset.mul_sum]
    exact Ideal.mul_mem_left _ _ hc
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_algebraMap_mem (S := S) g hsum
  obtain ⟨a, ha⟩ := hsyz (fun i => g ^ e * d i) (by
    rw [Finset.mul_sum] at he; simpa [mul_assoc] using he)
  have hu : IsUnit (algebraMap R S (g ^ (e + n))) :=
    IsLocalization.map_units S (⟨g ^ (e + n), e + n, rfl⟩ : Submonoid.powers g)
  refine ⟨fun j => hu.unit⁻¹ * algebraMap R S (a j), fun i => ?_⟩
  have hci : c i = hu.unit⁻¹ * algebraMap R S (g ^ e * d i) := by
    rw [hu.unit.eq_inv_mul_iff_mul_eq, IsUnit.unit_spec, pow_add, map_mul, map_mul, ← hcd]
    ring
  have : c i - ∑ j, hu.unit⁻¹ * algebraMap R S (a j) * algebraMap R S (rh j i) =
      ↑hu.unit⁻¹ * algebraMap R S (g ^ e * d i - ∑ j, a j * rh j i) := by
    rw [hci, map_sub, map_sum, mul_sub, Finset.mul_sum]
    simp only [map_mul, mul_assoc]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))

/-- **Clearing denominators in `solvable`.** If the image of `x` in `R_g` is solvable, then so is
`g ^ e • x` for some `e`. -/
theorem exists_pow_smul_mem_solvable {𝔦 : Ideal R} {fh : Fin m → R} {rh : Fin s → Fin m → R}
    {k : ℕ} {x : Fin s → R}
    (hx : (fun j => algebraMap R S (x j)) ∈ solvable (𝔦.map (algebraMap R S))
      (fun i => algebraMap R S (fh i)) (fun j i => algebraMap R S (rh j i)) k) :
    ∃ e : ℕ, g ^ e • x ∈ solvable 𝔦 fh rh k := by
  set φ := algebraMap R S
  set W : Ideal R := 𝔦 ^ (k + 1) ⊔ 𝔦 ^ k * Ideal.span (Set.range fh) with hW
  obtain ⟨μ, hμ, hμx⟩ := hx
  have hWmap : (𝔦.map φ) ^ (k + 1) ⊔ (𝔦.map φ) ^ k * Ideal.span (Set.range (fun i => φ (fh i))) =
      W.map φ := by
    rw [hW, Ideal.map_sup, Ideal.map_mul, Ideal.map_span, ← Set.range_comp, Ideal.map_pow,
      Ideal.map_pow]
    rfl
  rw [← Ideal.map_pow] at hμ
  choose a c hc hac using fun i => exists_pow_mul_eq_of_mem_map (S := S) g (hμ i)
  let A := ∑ i, a i
  have hA : ∀ i, a i ≤ A := fun i =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let c' : Fin m → R := fun i => g ^ (A - a i) * c i
  have hc' : ∀ i, c' i ∈ 𝔦 ^ k := fun i => Ideal.mul_mem_left _ _ (hc i)
  have hc'μ : ∀ i, φ (c' i) = φ (g ^ A) * μ i := fun i => by
    change φ (g ^ (A - a i) * c i) = _
    rw [map_mul, ← hac i, ← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel (hA i)]
  have hy : ∀ j, ∃ f : ℕ, g ^ f * (g ^ A * x j + ∑ i, rh j i * c' i) ∈ W := by
    intro j
    refine exists_pow_mul_mem_of_algebraMap_mem (S := S) g ?_
    have : φ (g ^ A * x j + ∑ i, rh j i * c' i) =
        φ (g ^ A) * (φ (x j) + ∑ i, φ (rh j i) * μ i) := by
      rw [map_add, map_mul, map_sum, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hc'μ]; ring
    rw [this, ← hWmap]
    exact Ideal.mul_mem_left _ _ (hμx j)
  obtain ⟨f, hf⟩ := exists_pow_mul_mem_of_forall g (𝔞 := W) hy
  refine ⟨f + A, fun i => g ^ f * c' i, fun i => Ideal.mul_mem_left _ _ (hc' i), fun j => ?_⟩
  have : (g ^ (f + A) • x) j + ∑ i, rh j i * (g ^ f * c' i) =
      g ^ f * (g ^ A * x j + ∑ i, rh j i * c' i) := by
    simp only [Pi.smul_apply, smul_eq_mul, pow_add, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact hf j

end Localize

/-! ### The obstruction vanishes above the syntomic locus -/

section Vanishing

/-- **A `k`-solution above a syntomic algebra presents a syntomic lift.** Let `A' → A` be
surjective with kernel `I`, `L` a Noetherian, flat, finitely presented `A'`-algebra and
`β : L → B₀` a surjection onto a syntomic `A`-algebra with `ker β = (fh) + IL`. For a
`k`-solution `(F, G)`, `k ≥ 1`, `L ⧸ ((F) + I^k L)` is syntomic over `A' ⧸ I ^ k`. -/
private theorem syntomic_quotient_of_isSolution {A' A L B₀ : Type u} [CommRing A'] [CommRing A]
    [CommRing L] [CommRing B₀] [Algebra A' A] [Algebra A' L] [Algebra A B₀] [Algebra A' B₀]
    [IsScalarTower A' A B₀] [Module.Flat A' L] [Algebra.FinitePresentation A' L]
    [IsNoetherianRing L] [Algebra.Syntomic A B₀]
    (hsurjA : Function.Surjective (algebraMap A' A)) (β : L →ₐ[A'] B₀)
    (hβ : Function.Surjective β) {m s : ℕ} {fh : Fin m → L} {rh : Fin s → Fin m → L}
    (hsyz : SyzygyGenerators ((RingHom.ker (algebraMap A' A)).map (algebraMap A' L)) fh rh)
    (hker : Ideal.span (Set.range fh) ⊔ (RingHom.ker (algebraMap A' A)).map (algebraMap A' L) =
      RingHom.ker β) {k : ℕ} (hk : 1 ≤ k) {F : Fin m → L} {G : Fin s → Fin m → L}
    (hsol : IsSolution ((RingHom.ker (algebraMap A' A)).map (algebraMap A' L)) fh rh k F G) :
    letI : Algebra (A' ⧸ RingHom.ker (algebraMap A' A) ^ k)
        (L ⧸ (Ideal.span (Set.range F) ⊔ (RingHom.ker (algebraMap A' A) ^ k).map
          (algebraMap A' L))) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_sup_right)
    Algebra.Syntomic (A' ⧸ RingHom.ker (algebraMap A' A) ^ k)
      (L ⧸ (Ideal.span (Set.range F) ⊔ (RingHom.ker (algebraMap A' A) ^ k).map
        (algebraMap A' L))) := by
  set I := RingHom.ker (algebraMap A' A) with hI
  set 𝔟 : Ideal L := Ideal.span (Set.range F) ⊔ (I ^ k).map (algebraMap A' L) with h𝔟
  have hle𝔟 : I ^ k ≤ 𝔟.comap (algebraMap A' L) := Ideal.map_le_iff_le_comap.mp le_sup_right
  let : Algebra (A' ⧸ I ^ k) (L ⧸ 𝔟) := Ideal.Quotient.algebraQuotientOfLEComap hle𝔟
  have : IsScalarTower A' (A' ⧸ I ^ k) (L ⧸ 𝔟) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hflat : Module.Flat (A' ⧸ I ^ k) (L ⧸ 𝔟) :=
    flat_quotient_of_isSolution hsurjA hk hsyz hsol β hβ hker
  have hpow : I ^ k ≤ RingHom.ker (algebraMap A' A) := Ideal.pow_le_self (by omega)
  let : Algebra (A' ⧸ I ^ k) A := (Ideal.Quotient.lift (I ^ k) (algebraMap A' A) hpow).toAlgebra
  let : Algebra (A' ⧸ I ^ k) B₀ := ((algebraMap A B₀).comp (algebraMap (A' ⧸ I ^ k) A)).toAlgebra
  have : IsScalarTower (A' ⧸ I ^ k) A B₀ := IsScalarTower.of_algebraMap_eq' rfl
  have hsurjk : Function.Surjective (algebraMap (A' ⧸ I ^ k) A) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurjA
  have hkerk : RingHom.ker (algebraMap (A' ⧸ I ^ k) A) = I.map (Ideal.Quotient.mk (I ^ k)) :=
    Ideal.ker_quotient_lift _ hpow
  have hF𝔦 : Ideal.span (Set.range F) ⊔ I.map (algebraMap A' L) = RingHom.ker β :=
    (span_sup_eq_of_sub_mem' hsol.1).trans hker
  have h𝔟I : 𝔟 ≤ Ideal.span (Set.range F) ⊔ I.map (algebraMap A' L) :=
    sup_le_sup_left (Ideal.map_mono (Ideal.pow_le_self (by omega))) _
  let βk : (L ⧸ 𝔟) →ₐ[A' ⧸ I ^ k] B₀ :=
    { (Ideal.Quotient.lift 𝔟 β.toRingHom (h𝔟I.trans hF𝔦.le)) with
      commutes' := fun x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        change β (algebraMap A' L a) = algebraMap A B₀ (algebraMap A' A a)
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A' A B₀] }
  have hβksurj : Function.Surjective βk := Ideal.Quotient.lift_surjective_of_surjective _ _ hβ
  have hβkker : RingHom.ker βk =
      (RingHom.ker (algebraMap (A' ⧸ I ^ k) A)).map (algebraMap (A' ⧸ I ^ k) (L ⧸ 𝔟)) := by
    rw [hkerk, Ideal.map_map]
    refine (Ideal.ker_quotient_lift β.toRingHom _).trans ?_
    change _ = I.map ((Ideal.Quotient.mk 𝔟).comp (algebraMap A' L))
    rw [← Ideal.map_map, show RingHom.ker β.toRingHom = _ from hF𝔦.symm, Ideal.map_sup,
      Ideal.map_mk_eq_bot_of_le le_sup_left, bot_sup_eq]
  have : Algebra.FinitePresentation A' (L ⧸ 𝔟) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian 𝔟)
  have : Algebra.FinitePresentation (A' ⧸ I ^ k) (L ⧸ 𝔟) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A' (A' ⧸ I ^ k) (L ⧸ 𝔟)
  exact syntomic_of_flat_of_surjective hsurjk
    ⟨k, by rw [hkerk, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker]⟩ βk hβksurj hβkker

/-- **Above a syntomic algebra every solution can be improved.** Let `A' → A` be surjective with
nilpotent kernel `I`, `L` a Noetherian, flat, formally smooth, finitely presented `A'`-algebra and
`β : L → B₀` a surjection onto a syntomic `A`-algebra with `ker β = (fh) + IL`. Then the relation
vector of every `k`-solution, `k ≥ 1`, is solvable. -/
theorem relVec_mem_solvable_of_syntomic {A' A L B₀ : Type u} [CommRing A'] [CommRing A]
    [CommRing L] [CommRing B₀] [Algebra A' A] [Algebra A' L] [Algebra A B₀] [Algebra A' B₀]
    [IsScalarTower A' A B₀] [Module.Flat A' L] [Algebra.FinitePresentation A' L]
    [Algebra.FormallySmooth A' L] [IsNoetherianRing L] [Algebra.Syntomic A B₀]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A))) (β : L →ₐ[A'] B₀)
    (hβ : Function.Surjective β) {m s : ℕ} {fh : Fin m → L} {rh : Fin s → Fin m → L}
    (hsyz : SyzygyGenerators ((RingHom.ker (algebraMap A' A)).map (algebraMap A' L)) fh rh)
    (hker : Ideal.span (Set.range fh) ⊔ (RingHom.ker (algebraMap A' A)).map (algebraMap A' L) =
      RingHom.ker β) {k : ℕ} (hk : 1 ≤ k) {F : Fin m → L} {G : Fin s → Fin m → L}
    (hsol : IsSolution ((RingHom.ker (algebraMap A' A)).map (algebraMap A' L)) fh rh k F G) :
    relVec F G ∈ solvable ((RingHom.ker (algebraMap A' A)).map (algebraMap A' L)) fh rh k := by
  set I := RingHom.ker (algebraMap A' A) with hI
  set 𝔟 : Ideal L := Ideal.span (Set.range F) ⊔ (I ^ k).map (algebraMap A' L) with h𝔟
  have hle𝔟 : I ^ k ≤ 𝔟.comap (algebraMap A' L) := Ideal.map_le_iff_le_comap.mp le_sup_right
  let : Algebra (A' ⧸ I ^ k) (L ⧸ 𝔟) := Ideal.Quotient.algebraQuotientOfLEComap hle𝔟
  have : Algebra.Syntomic (A' ⧸ I ^ k) (L ⧸ 𝔟) :=
    syntomic_quotient_of_isSolution hsurjA β hβ hsyz hker hk hsol
  -- Stacks 07M8
  obtain ⟨Ĵ, hĴflat, hĴ⟩ := exists_flat_quotient_of_syntomic (S := L) (D := L ⧸ 𝔟) (I ^ k)
    (by
      obtain ⟨n, hn⟩ := hnilA
      exact ⟨n, by rw [← pow_mul, mul_comm, pow_mul, hn]; exact zero_pow (by omega)⟩)
    (Ideal.Quotient.mk 𝔟) Ideal.Quotient.mk_surjective (fun _ => rfl)
  rw [Ideal.mk_ker] at hĴ
  have := hĴflat
  refine relVec_mem_solvable_of_lift hk hsol Ĵ ?_ ?_
  · rw [← Ideal.map_pow, hĴ]
  · rw [← Ideal.map_pow]
    exact (inf_map_le_mul_of_flat_quotient Ĵ (I ^ k)).trans le_sup_left

end Vanishing


/-- **The obstruction is torsion above the syntomic locus.** Let `A' → A` be surjective with
nilpotent kernel `I`, `P'` a Noetherian, flat, formally smooth, finitely presented `A'`-algebra and
`π : P' → B` a surjection of `A'`-algebras with `A → B_h` syntomic for every `h ∈ 𝔟`. For
generators `fh` of `ker π` and syzygy generators `rh` of `fh` modulo `IP'`, the obstruction to
improving a `k`-solution, `k ≥ 1`, is `π⁻¹(𝔟)`-power torsion. -/
theorem obstructionTorsion_of_syntomic (A' A B P' : Type u) [CommRing A'] [CommRing A]
    [CommRing B] [CommRing P'] [Algebra A' A] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B]
    [Algebra A' P'] [Module.Flat A' P'] [Algebra.FinitePresentation A' P']
    [Algebra.FormallySmooth A' P'] [IsNoetherianRing P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A))) (π : P' →ₐ[A'] B)
    (hπ : Function.Surjective π) (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) {m s : ℕ} (fh : Fin m → P')
    (rh : Fin s → Fin m → P') (hfh : Ideal.span (Set.range fh) = RingHom.ker π)
    (hsyz : SyzygyGenerators ((RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) fh rh)
    {k : ℕ} (hk : 1 ≤ k) :
    ObstructionTorsion ((RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
      (b.comap π.toRingHom) fh rh k := by
  intro F G hsol g hg
  set I := RingHom.ker (algebraMap A' A) with hI
  let L := Localization.Away g
  let φ := algebraMap P' L
  have : Module.Flat A' L := Module.Flat.trans A' P' L
  have : Algebra.FinitePresentation P' L := IsLocalization.Away.finitePresentation g
  have : Algebra.FinitePresentation A' L := Algebra.FinitePresentation.trans A' P' L
  have : Algebra.FormallySmooth P' L :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
  have : Algebra.FormallySmooth A' L := Algebra.FormallySmooth.comp A' P' L
  have : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers g) L inferInstance
  set h := π g with hh
  have : Algebra.Syntomic A (Localization.Away h) := hsyn h hg
  let B₀ := Localization.Away h
  have : IsLocalization ((Submonoid.powers g).map π.toRingHom) B₀ := by
    rw [Submonoid.map_powers]; exact Localization.isLocalization
  let βr : L →+* B₀ := IsLocalization.map B₀ π.toRingHom (Submonoid.powers g).le_comap_map
  have hβr : ∀ x : P', βr (φ x) = algebraMap B B₀ (π x) := fun x => IsLocalization.map_eq _ _
  let β : L →ₐ[A'] B₀ :=
    { βr with
      commutes' := fun a => by
        change βr (φ (algebraMap A' P' a)) = _
        rw [hβr, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
  have hβ : Function.Surjective β := IsLocalization.map_surjective_of_surjective
    (M := Submonoid.powers g) (S := L) (Q := B₀) (g := π.toRingHom) hπ
  have hβker : RingHom.ker β = (RingHom.ker π).map φ :=
    IsLocalization.ker_map (M := Submonoid.powers g) (S := L) (Q := B₀) (g := π.toRingHom)
      (T := (Submonoid.powers g).map π.toRingHom) rfl
  have hIker : I.map (algebraMap A' P') ≤ RingHom.ker π := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, π.commutes, IsScalarTower.algebraMap_apply A' A B,
      show algebraMap A' A a = 0 from ha, map_zero]
  have hIL : I.map (algebraMap A' L) = (I.map (algebraMap A' P')).map φ := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hker : Ideal.span (Set.range (fun i => φ (fh i))) ⊔ I.map (algebraMap A' L) =
      RingHom.ker β := by
    have hspan : Ideal.span (Set.range (fun i => φ (fh i))) = (RingHom.ker π).map φ := by
      rw [← hfh, Ideal.map_span, ← Set.range_comp]; rfl
    rw [hβker, hIL, hspan]
    exact sup_eq_left.mpr (Ideal.map_mono hIker)
  have hsyzL := syzygyGenerators_localization (S := L) g hsyz
  rw [← hIL] at hsyzL
  have hsolL := isSolution_map φ hsol
  rw [← hIL] at hsolL
  have hmem := relVec_mem_solvable_of_syntomic hsurjA hnilA β hβ hsyzL hker hk hsolL
  rw [hIL] at hmem
  exact exists_pow_smul_mem_solvable (S := L) g (x := relVec F G) (by
    convert hmem using 1
    funext j
    simp [relVec, φ, map_sum, map_mul])

end Deformation

end
