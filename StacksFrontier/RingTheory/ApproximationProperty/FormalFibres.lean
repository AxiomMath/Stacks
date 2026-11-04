module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.ApproximationProperty.FiniteAlgebra
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.Henselian.IntegralDomain

/-!
# Formal fibres of a local ring with the approximation property

Let `(A, 𝔪)` be a Noetherian local ring with the approximation property. Rotthaus' theorem
(C. Rotthaus, *Rings with approximation property*) says that the formal fibres of `A` are
geometrically regular, that is, `A → Â` is a regular ring map, so that `A` is a G-ring. This file
reduces the theorem to its core case (Rotthaus, Remark 1.2 and §3.1):

  *for a Noetherian local domain `B` with the approximation property and a prime `P` of `B̂` with
  `P ∩ B = 0`, the local ring `B̂_P` is regular,*

which is recorded as the proposition `IsLocalRing.HasApproximationProperty.Core`.

The reduction runs as follows. The completion map `A → Â` is flat, and its fibre
`κ(p) ⊗[A] Â` over a prime `p` of `A` is Noetherian. By Stacks, Lemma 0381 geometric regularity
of the fibre is tested on finite purely inseparable extensions `K` of `κ(p)`, and
`K ⊗[κ(p)] (κ(p) ⊗[A] Â) = K ⊗[A] Â`. Multiplying a `κ(p)`-basis of `K` by a common element
`a ∉ p` makes it integral over `A`; the `A`-subalgebra `B ⊆ K` it generates is a domain, finite
over `A`, and `K` is the localization of `B` at the image of `A ∖ p`. As `A` is henselian, `B` is
local and `A → B` is a local homomorphism (Stacks, Lemma 092X), so `B` has the approximation
property and `B̂ = B ⊗[A] Â`. Hence `K ⊗[A] Â = K ⊗[B] B̂` is a localization of `B̂`, and its local
rings are the rings `B̂_P` for primes `P` of `B̂` meeting `B` only in `0`, which are regular by the
core statement. Finally `A` is a G-ring by the local criterion Stacks, Lemma 07PT.

## Main definitions

* `IsLocalRing.HasApproximationProperty.Core`: the core statement of Rotthaus' theorem.

## Main results

* `IsLocalRing.HasApproximationProperty.isRegularRingHom_adicCompletion_of_core`: given the core
  statement, the completion map of a Noetherian local ring with the approximation property is
  regular.
* `IsLocalRing.HasApproximationProperty.isGRing_of_core`: given the core statement, a Noetherian
  local ring with the approximation property is a G-ring.

## Implementation notes

The core statement quantifies over local domains in the universe `u` of `A`; the ring `B` built in
the reduction lives in that universe because it is a subring of the field `K`, which ranges over
`Type u` in the definition of geometric regularity.

## References

* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466]
* [Stacks Project, Tag 07BX](https://stacks.math.columbia.edu/tag/07BX)
* [Stacks Project, Tag 0381](https://stacks.math.columbia.edu/tag/0381)
* [Stacks Project, Tag 092X](https://stacks.math.columbia.edu/tag/092X)
* [Stacks Project, Tag 07PT](https://stacks.math.columbia.edu/tag/07PT)
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace IsLocalRing.HasApproximationProperty

/-- The core statement of Rotthaus' theorem in the universe `u`: for every Noetherian local
domain `B` with the approximation property and every prime `P` of the completion `B̂` which meets
`B` only in `0`, the local ring `B̂_P` is a regular local ring. -/
def Core : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B],
    HasApproximationProperty B →
      ∀ (P : Ideal (AdicCompletion (maximalIdeal B) B)) [P.IsPrime],
        P.comap (algebraMap B (AdicCompletion (maximalIdeal B) B)) = ⊥ →
          IsRegularLocalRing (Localization.AtPrime P)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- If the field `K` is a localization of a Noetherian local domain `B` with the approximation
property, then the core statement makes `K ⊗[B] B̂` a regular ring: it is a localization of `B̂`,
and its local rings are the local rings of `B̂` at primes meeting `B` only in `0`. -/
private theorem isRegularRing_tensorProduct_of_core (hcore : Core.{u}) (B : Type u)
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B]
    (hB : HasApproximationProperty B) (K : Type u) [Field K] [Algebra B K] (M : Submonoid B)
    [IsLocalization M K] (hinj : Function.Injective (algebraMap B K)) :
    IsRegularRing (K ⊗[B] AdicCompletion (maximalIdeal B) B) := by
  have : IsNoetherianRing (K ⊗[B] AdicCompletion (maximalIdeal B) B) :=
    IsLocalization.isNoetherianRing
      (Algebra.algebraMapSubmonoid (AdicCompletion (maximalIdeal B) B) M) _ inferInstance
  rw [isRegularRing_iff]
  intro Q _
  let P := Q.comap (algebraMap (AdicCompletion (maximalIdeal B) B)
    (K ⊗[B] AdicCompletion (maximalIdeal B) B))
  have : IsLocalization.AtPrime (Localization.AtPrime Q) P :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (AdicCompletion (maximalIdeal B) B) M)
      (T := Localization.AtPrime Q) Q
  -- `P` meets `B` only in `0`, since `B → K ⊗[B] B̂` factors through the field `K`
  have hP : P.comap (algebraMap B (AdicCompletion (maximalIdeal B) B)) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hK : Q.comap (algebraMap K (K ⊗[B] AdicCompletion (maximalIdeal B) B)) = ⊥ :=
      Ideal.eq_bot_of_prime _
    have hb' : algebraMap K (K ⊗[B] AdicCompletion (maximalIdeal B) B) (algebraMap B K b) ∈
        Q := by
      have : algebraMap (AdicCompletion (maximalIdeal B) B)
          (K ⊗[B] AdicCompletion (maximalIdeal B) B)
          (algebraMap B (AdicCompletion (maximalIdeal B) B) b) =
          algebraMap K (K ⊗[B] AdicCompletion (maximalIdeal B) B) (algebraMap B K b) := by
        simp [Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
          Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rw [← this]
      exact hb
    have : algebraMap B K b ∈ (⊥ : Ideal K) := hK ▸ hb'
    rw [Ideal.mem_bot] at this
    exact (Submodule.mem_bot B).mpr (hinj (this.trans (map_zero _).symm))
  have := hcore B hB P hP
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (Localization.AtPrime Q)).toRingEquiv

/-- The key step of the reduction: given the core statement, `K ⊗[A] Â` is a regular ring for
every finite field extension `K` of a residue field `κ(p)` of a Noetherian local ring `A` with
the approximation property. -/
private theorem isRegularRing_tensorProduct_adicCompletion {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : HasApproximationProperty A) (hcore : Core.{u})
    (p : Ideal A) [p.IsPrime] (K : Type u) [Field K] [Algebra p.ResidueField K]
    [Module.Finite p.ResidueField K] [Algebra A K] [IsScalarTower A p.ResidueField K] :
    IsRegularRing (K ⊗[A] AdicCompletion (maximalIdeal A) A) := by
  classical
  let : Algebra (A ⧸ p) K :=
    ((algebraMap p.ResidueField K).comp (algebraMap (A ⧸ p) p.ResidueField)).toAlgebra
  have : IsScalarTower (A ⧸ p) p.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  have hmk : ∀ c : A, algebraMap (A ⧸ p) K (Ideal.Quotient.mk p c) = algebraMap A K c := by
    intro c
    rw [IsScalarTower.algebraMap_apply (A ⧸ p) p.ResidueField K,
      IsScalarTower.algebraMap_apply A p.ResidueField K]
    rfl
  have : IsScalarTower A (A ⧸ p) K := IsScalarTower.of_algebraMap_eq fun c => (hmk c).symm
  -- a basis of `K` over `κ(p)`, made integral over `A` by a common multiplier `a ∉ p`
  let b := Module.finBasis p.ResidueField K
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples (A ⧸ p) p.ResidueField (L := K)
    (Finset.univ.image b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∉ p := fun h => hy0 (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  let g : Fin (Module.finrank p.ResidueField K) → K := fun i => algebraMap A K a * b i
  have hg : ∀ i, IsIntegral A (g i) := by
    intro i
    have := hy (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [Algebra.smul_def, hmk] at this
    exact isIntegral_trans _ this
  let B : Subalgebra A K := Algebra.adjoin A (Set.range g)
  have : Module.Finite A B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range g)
      (by rintro _ ⟨i, rfl⟩; exact hg i)
  -- `B` is a local domain, finite over `A`, with the approximation property
  have : HenselianLocalRing A := hA.henselianLocalRing
  obtain ⟨hBh, hBloc, -⟩ := RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain
    (algebraMap A B) (Algebra.IsIntegral.isIntegral (R := A) (A := B))
  have hBAP : HasApproximationProperty B := hA.of_finite
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_tensorProduct_of_isLocalRing A B
  -- `K` is the localization of `B` at the image of `A ∖ p`
  have hunit : ∀ c ∉ p, algebraMap A K c ≠ 0 := by
    intro c hc h
    rw [IsScalarTower.algebraMap_apply A p.ResidueField K, map_eq_zero_iff _
      (algebraMap p.ResidueField K).injective, Ideal.algebraMap_residueField_eq_zero] at h
    exact hc h
  let N : Submodule p.ResidueField K :=
    { carrier := {k | ∃ c ∉ p, algebraMap A K c * k ∈ B}
      add_mem' := by
        rintro k₁ k₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
        refine ⟨c₁ * c₂, p.primeCompl.mul_mem hc₁ hc₂, ?_⟩
        have : algebraMap A K (c₁ * c₂) * (k₁ + k₂) =
            algebraMap A K c₂ * (algebraMap A K c₁ * k₁) +
              algebraMap A K c₁ * (algebraMap A K c₂ * k₂) := by
          rw [map_mul]
          ring
        rw [this]
        exact B.add_mem (B.mul_mem (B.algebraMap_mem c₂) h₁) (B.mul_mem (B.algebraMap_mem c₁) h₂)
      zero_mem' := ⟨1, p.primeCompl.one_mem, by simp⟩
      smul_mem' := by
        rintro t k ⟨c, hc, h⟩
        obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A ⧸ p) t
        obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective u
        obtain ⟨β, rfl⟩ := Ideal.Quotient.mk_surjective v
        have hβ : β ∉ p := fun h => nonZeroDivisors.ne_zero hv
          (Ideal.Quotient.eq_zero_iff_mem.mpr h)
        refine ⟨β * c, p.primeCompl.mul_mem hβ hc, ?_⟩
        have : algebraMap A K (β * c) *
            ((algebraMap (A ⧸ p) p.ResidueField (Ideal.Quotient.mk p α) /
              algebraMap (A ⧸ p) p.ResidueField (Ideal.Quotient.mk p β)) • k) =
            algebraMap A K α * (algebraMap A K c * k) := by
          rw [Algebra.smul_def, map_div₀, map_mul]
          simp only [← IsScalarTower.algebraMap_apply, hmk]
          have hβK : algebraMap A K β ≠ 0 := hunit β hβ
          field_simp
        rw [this]
        exact B.mul_mem (B.algebraMap_mem α) h }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨a, ha, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) K := by
    rw [isLocalization_iff]
    refine ⟨?_, fun k => ?_, fun {x y} hxy => ⟨1, by rw [Subtype.val_injective hxy]⟩⟩
    · rintro ⟨_, c, hc, rfl⟩
      exact (hunit c hc).isUnit
    · have hk : k ∈ N := hN ▸ Submodule.mem_top
      obtain ⟨c, hc, h⟩ := hk
      exact ⟨⟨⟨_, h⟩, ⟨algebraMap A B c, c, hc, rfl⟩⟩, mul_comm _ _⟩
  -- conclusion: `K ⊗[A] Â ≅ K ⊗[B] (B ⊗[A] Â) ≅ K ⊗[B] B̂`, which is regular
  have := isRegularRing_tensorProduct_of_core hcore B hBAP K
    (Algebra.algebraMapSubmonoid B p.primeCompl) Subtype.val_injective
  let e₁ := Algebra.TensorProduct.cancelBaseChange A B K K (AdicCompletion (maximalIdeal A) A)
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[B] K) e
  exact IsRegularRing.of_ringEquiv (e₂.toRingEquiv.symm.trans e₁.toRingEquiv)

/-- **Reduction of Rotthaus' theorem to its core** (Rotthaus, Remark 1.2). Given the core
statement `Core`, the canonical map from a Noetherian local ring with the approximation property
to its completion is a regular ring map: it is flat, and its fibres are Noetherian and
geometrically regular. -/
theorem isRegularRingHom_adicCompletion_of_core {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : HasApproximationProperty A) (hcore : Core.{u}) :
    IsRegularRingHom (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, fun p _ => ?_⟩
  -- regularity after finite purely inseparable base change, which suffices by Lemma 0381
  have hreg : ∀ (K : Type u) [Field K] [Algebra p.ResidueField K]
      [Module.Finite p.ResidueField K] [IsPurelyInseparable p.ResidueField K],
      IsRegularRing (K ⊗[p.ResidueField] p.Fiber (AdicCompletion (maximalIdeal A) A)) := by
    intro K _ _ _ _
    let : Algebra A K :=
      ((algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)).toAlgebra
    have : IsScalarTower A p.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
    have := isRegularRing_tensorProduct_adicCompletion hA hcore p K
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.cancelBaseChange A p.ResidueField K K
      (AdicCompletion (maximalIdeal A) A)).symm.toRingEquiv
  have : Algebra.IsGeometricallyRegular p.ResidueField
      (p.Fiber (AdicCompletion (maximalIdeal A) A)) :=
    ⟨(Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
      _ _).mpr hreg⟩
  refine ⟨?_, this⟩
  -- the fibre is Noetherian: it is regular, being its own base change along `κ(p) → κ(p)`
  have : IsRegularRing (p.Fiber (AdicCompletion (maximalIdeal A) A)) :=
    IsRegularRing.of_ringEquiv
      (R := p.ResidueField ⊗[p.ResidueField] p.Fiber (AdicCompletion (maximalIdeal A) A))
      (Algebra.TensorProduct.lid p.ResidueField
        (p.Fiber (AdicCompletion (maximalIdeal A) A))).toRingEquiv
  infer_instance

/-- **Rotthaus' theorem, given its core.** Given the core statement `Core`, a Noetherian local
ring with the approximation property is a G-ring. By the local criterion (Stacks, Lemma 07PT) it
suffices that the completion map of the localization of `A` at its maximal ideal is regular; that
localization is isomorphic to `A`, so it has the approximation property. -/
theorem isGRing_of_core {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : HasApproximationProperty A) (hcore : Core.{u}) : IsGRing A := by
  rw [isGRing_iff_isRegularRingHom_adicCompletion_at_maximal]
  intro m _
  obtain rfl := IsLocalRing.eq_maximalIdeal ‹m.IsMaximal›
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl fun _ hx => not_not.mp hx
  exact isRegularRingHom_adicCompletion_of_core (hA.of_ringEquiv e.toRingEquiv) hcore

end IsLocalRing.HasApproximationProperty

end
