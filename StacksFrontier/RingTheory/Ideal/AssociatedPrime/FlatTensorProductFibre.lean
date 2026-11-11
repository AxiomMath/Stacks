module

public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatTensorProduct

@[expose] public section

/-!
# Associated primes of a flat tensor product on the fibre rings, in the sense of Tag 00LA

Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an `S`-module which is flat as
an `R`-module. Stacks Tag 05C2 states
`Ass_S(M ⊗_R N) ⊇ ⋃_{𝔭 ∈ Ass_R(M)} Ass_{S ⊗_R κ(𝔭)}(N ⊗_R κ(𝔭))`,
the spectra of the fibre rings being viewed inside `Spec(S)` (Remark 00E6), with equality when
`R` is Noetherian. Every `Ass` here is the one of Definition 00LA: a prime which *is* the
annihilator of an element (`IsAssociatedPrimeStacks`), over `R`, over `S` and over the fibre
rings alike. No Noetherian hypothesis is put on `S` or on the fibre rings.

The source proves this as a translation of Tag 0312, which describes the same set through the
modules `N / 𝔭N` over `S`, by Lemmas 05BY, 00HI and 05C1. Tag 0312 is
`associatedPrimes.tensorProduct_of_flat`, in the annihilator reading on the `S`-side. The
translation, for a prime `𝔭` of `R`, with `B = S ⊗_R κ(𝔭)` the fibre ring and
`F = B ⊗_S N` the fibre module, runs as follows.

* Every element of `R ∖ 𝔭` maps to a unit of `B`, and every element of `B` is a unit times an
  element of the image of `S` (`exists_isUnit_mul_eq_algebraMap_fibre`).
* `N / 𝔭N ≅ N ⊗_R R/𝔭` embeds `S`-linearly into `N ⊗_R κ(𝔭) ≅ F`, flatness of `N` keeping
  `R/𝔭 → κ(𝔭)` injective (`injective_quotToFibre`), and every element of `F` lands in the image
  after multiplication by an element of `R ∖ 𝔭` (`exists_smul_mem_range_quotToFibre`). Such an
  element acts on `F` through a unit of `B`, so it does not change annihilators: every element of
  `F` has the same annihilator in `S` as an element of `N / 𝔭N` (Lemma 05C1's
  `Ass_S(N/𝔭N) = Ass_S(N ⊗_R κ(𝔭))`, element by element).
* For `z ∈ F` the annihilator of `z` in `S` is the contraction of its annihilator in `B`
  (Lemma 05BY), and a `B`-ideal whose contraction to `S` is prime is prime, because every element
  of `B` is a unit times the image of an element of `S` (Lemma 05BZ (1)).

## Main results

* `assStacks_tensorProduct_of_flat_fiberRing`: Stacks Tag 05C2.

## References

* [StacksProject 05C2](https://stacks.math.columbia.edu/tag/05C2)

## Tags

associated prime, flat module, tensor product, fibre ring, residue field
-/

open TensorProduct

namespace Stacks.AssociatedPrimes.FibreRings

section Units

/-- A unit acts injectively: `u • w = 0` only for `w = 0`. -/
private theorem smul_eq_zero_iff_of_isUnit {B F : Type*} [Ring B] [AddCommGroup F] [Module B F]
    {u : B} (hu : IsUnit u) (w : F) : u • w = 0 ↔ w = 0 := by
  obtain ⟨v, rfl⟩ := hu
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  have h' := congrArg (fun y => (↑v⁻¹ : B) • y) h
  simpa [smul_smul] using h'

/-- An ideal of `B` whose contraction to `A` is prime is itself prime, provided every element of
`B` is a unit times the image of an element of `A`. -/
private theorem isPrime_of_isPrime_comap {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (h : ∀ b : B, ∃ u : B, IsUnit u ∧ ∃ s : A, u * b = algebraMap A B s) {Q : Ideal B}
    (hQ : (Q.comap (algebraMap A B)).IsPrime) : Q.IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun htop => hQ.ne_top (by rw [htop, Ideal.comap_top]), ?_⟩
  intro b₁ b₂ hb
  obtain ⟨u₁, hu₁, s₁, hs₁⟩ := h b₁
  obtain ⟨u₂, hu₂, s₂, hs₂⟩ := h b₂
  have hmem : s₁ * s₂ ∈ Q.comap (algebraMap A B) := by
    rw [Ideal.mem_comap, map_mul, ← hs₁, ← hs₂,
      show u₁ * b₁ * (u₂ * b₂) = (u₁ * u₂) * (b₁ * b₂) by ring]
    exact Q.mul_mem_left _ hb
  rcases hQ.mem_or_mem hmem with h₁ | h₂
  · left
    rw [Ideal.mem_comap, ← hs₁] at h₁
    exact (Ideal.unit_mul_mem_iff_mem Q hu₁).mp h₁
  · right
    rw [Ideal.mem_comap, ← hs₂] at h₂
    exact (Ideal.unit_mul_mem_iff_mem Q hu₂).mp h₂

/-- A linear isomorphism does not change the annihilator of an element. -/
private theorem colon_singleton_linearEquiv {A X Y : Type*} [CommRing A] [AddCommGroup X]
    [Module A X] [AddCommGroup Y] [Module A Y] (e : X ≃ₗ[A] Y) (w : X) :
    (⊥ : Submodule A Y).colon {e w} = (⊥ : Submodule A X).colon {w} := by
  ext s
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_smul,
    LinearEquiv.map_eq_zero_iff]

end Units

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

section FibreRing

/-- An element of `R ∖ 𝔭` becomes a unit in the fibre ring `S ⊗_R κ(𝔭)`. -/
private theorem isUnit_algebraMap_fibre (p : Ideal R) [p.IsPrime] {r : R} (hr : r ∉ p) :
    IsUnit (algebraMap R (S ⊗[R] p.ResidueField) r) := by
  have hu : IsUnit (algebraMap R p.ResidueField r) :=
    isUnit_iff_ne_zero.mpr (by simpa [Ideal.algebraMap_residueField_eq_zero] using hr)
  have e : algebraMap R (S ⊗[R] p.ResidueField) r =
      Algebra.TensorProduct.includeRight (algebraMap R p.ResidueField r) := by simp
  exact e ▸ hu.map _

/-- Every element of the fibre ring `S ⊗_R κ(𝔭)` is a unit times the image of an element of
`S`. -/
theorem exists_isUnit_mul_eq_algebraMap_fibre (p : Ideal R) [p.IsPrime]
    (b : S ⊗[R] p.ResidueField) :
    ∃ u : S ⊗[R] p.ResidueField, IsUnit u ∧ ∃ s : S,
      u * b = algebraMap S (S ⊗[R] p.ResidueField) s := by
  obtain ⟨r, hr, s, hs⟩ := Ideal.ResidueField.exists_smul_eq_tmul_one p b
  refine ⟨algebraMap R _ r, isUnit_algebraMap_fibre p hr, s, ?_⟩
  rw [← Algebra.smul_def, hs]
  simp

end FibreRing

variable {N : Type*} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

section FibreModule

variable (N) in
/-- The fibre module written as a base change, `(S ⊗_R κ(𝔭)) ⊗_S N`, is `N ⊗_R κ(𝔭)` as an
`S`-module. -/
noncomputable def fibreModuleEquiv (p : Ideal R) [p.IsPrime] :
    (S ⊗[R] p.ResidueField) ⊗[S] N ≃ₗ[S] N ⊗[R] p.ResidueField :=
  (TensorProduct.comm S (S ⊗[R] p.ResidueField) N).trans
    (AlgebraTensorModule.cancelBaseChange R S S N p.ResidueField)

variable (N) in
/-- The `S`-linear embedding `N ⊗_R R/𝔭 → (S ⊗_R κ(𝔭)) ⊗_S N`, `n ⊗ a ↦ 1 ⊗ (a • n)`: the base
change of `R/𝔭 → κ(𝔭)` along `N`, followed by the cancellation
`N ⊗_R κ(𝔭) ≅ (S ⊗_R κ(𝔭)) ⊗_S N`. -/
noncomputable def quotToFibre (p : Ideal R) [p.IsPrime] :
    N ⊗[R] (R ⧸ p) →ₗ[S] (S ⊗[R] p.ResidueField) ⊗[S] N :=
  (fibreModuleEquiv N p).symm.toLinearMap ∘ₗ
    AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N)
      (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap

/-- For `N` flat over `R`, the map `N ⊗_R R/𝔭 → (S ⊗_R κ(𝔭)) ⊗_S N` is injective: `R/𝔭 → κ(𝔭)`
is injective and tensoring with `N` keeps it so. -/
theorem injective_quotToFibre [Module.Flat R N] (p : Ideal R) [p.IsPrime] :
    Function.Injective (quotToFibre N (S := S) p) := fun _ _ h =>
  FlatBaseChange.injective_map_id (S := S)
    (f := (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap)
    (Ideal.injective_algebraMap_quotient_residueField p) ((fibreModuleEquiv N p).symm.injective h)

/-- Every element of `N ⊗_R κ(𝔭)` lies in the image of `N ⊗_R R/𝔭` after multiplication by an
element of `R ∖ 𝔭`. -/
private theorem exists_smul_mem_range_map (p : Ideal R) [p.IsPrime] (y : N ⊗[R] p.ResidueField) :
    ∃ r : R, r ∉ p ∧ ∃ x : N ⊗[R] (R ⧸ p), algebraMap R S r • y =
      AlgebraTensorModule.map (LinearMap.id : N →ₗ[S] N)
        (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField).toLinearMap x := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, fun h => (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.eq_top_iff_one _).mpr h), 0, by simp⟩
  | tmul n k =>
    obtain ⟨⟨a, d⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors (R ⧸ p)) k
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (d : R ⧸ p)
    have hrp : r ∉ p := by
      intro h
      apply nonZeroDivisors.ne_zero d.2
      rw [← hr]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
    refine ⟨r, hrp, n ⊗ₜ[R] a, ?_⟩
    have hrk : r • k = algebraMap (R ⧸ p) p.ResidueField a := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R (R ⧸ p) p.ResidueField,
        Ideal.Quotient.algebraMap_eq, hr, mul_comm]
      exact hk
    rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul, hrk,
      AlgebraTensorModule.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom']
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨r₁, hr₁, x₁, hx₁⟩ := h₁
    obtain ⟨r₂, hr₂, x₂, hx₂⟩ := h₂
    refine ⟨r₁ * r₂, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hr₁ hr₂,
      algebraMap R S r₂ • x₁ + algebraMap R S r₁ • x₂, ?_⟩
    rw [map_add, map_smul, map_smul, ← hx₁, ← hx₂, smul_add, map_mul, mul_smul, mul_smul,
      smul_comm (algebraMap R S r₁) (algebraMap R S r₂) y₁]

/-- Every element of the fibre module `(S ⊗_R κ(𝔭)) ⊗_S N` lies in the image of `N ⊗_R R/𝔭`
after multiplication by an element of `R ∖ 𝔭`. -/
theorem exists_smul_mem_range_quotToFibre (p : Ideal R) [p.IsPrime]
    (z : (S ⊗[R] p.ResidueField) ⊗[S] N) :
    ∃ r : R, r ∉ p ∧ ∃ x : N ⊗[R] (R ⧸ p), algebraMap R S r • z = quotToFibre N p x := by
  obtain ⟨r, hr, x, hx⟩ := exists_smul_mem_range_map (S := S) (N := N) p (fibreModuleEquiv N p z)
  refine ⟨r, hr, x, ?_⟩
  rw [quotToFibre, LinearMap.comp_apply, ← hx, LinearEquiv.coe_coe, map_smul,
    LinearEquiv.symm_apply_apply]

omit [Module R N] [IsScalarTower R S N] in
/-- Multiplication by an element of `R ∖ 𝔭` does not change the annihilator in `S` of an element
of the fibre module: it acts through a unit of the fibre ring. -/
private theorem colon_smul_algebraMap (p : Ideal R) [p.IsPrime] {r : R} (hr : r ∉ p)
    (z : (S ⊗[R] p.ResidueField) ⊗[S] N) :
    (⊥ : Submodule S ((S ⊗[R] p.ResidueField) ⊗[S] N)).colon {algebraMap R S r • z} =
      (⊥ : Submodule S ((S ⊗[R] p.ResidueField) ⊗[S] N)).colon {z} := by
  have hu : IsUnit (algebraMap S (S ⊗[R] p.ResidueField) (algebraMap R S r)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact isUnit_algebraMap_fibre p hr
  ext t
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  rw [smul_comm t (algebraMap R S r) z, ← algebraMap_smul (S ⊗[R] p.ResidueField)
    (algebraMap R S r) (t • z), smul_eq_zero_iff_of_isUnit hu]

/-- Every element of the fibre module `(S ⊗_R κ(𝔭)) ⊗_S N` has the same annihilator in `S` as some
element of `N / 𝔭N`. -/
theorem exists_quot_colon_eq [Module.Flat R N] (p : Ideal R) [p.IsPrime]
    (z : (S ⊗[R] p.ResidueField) ⊗[S] N) :
    ∃ w : N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)),
      (⊥ : Submodule S _).colon {w} =
        (⊥ : Submodule S ((S ⊗[R] p.ResidueField) ⊗[S] N)).colon {z} := by
  obtain ⟨r, hr, x, hx⟩ := exists_smul_mem_range_quotToFibre (N := N) p z
  set e := FlatBaseChange.quotSMulEquivTensorQuot (S := S) (N := N) p
  refine ⟨e.symm x, ?_⟩
  have h₁ := colon_singleton_linearEquiv e (e.symm x)
  have h₂ := FlatBaseChange.colon_singleton_apply (injective_quotToFibre (S := S) (N := N) p) x
  rw [← h₁, show e (e.symm x) = x from e.apply_symm_apply x, ← h₂, ← hx,
    colon_smul_algebraMap p hr]

omit [Module R N] [IsScalarTower R S N] in
/-- The annihilator in `S` of an element of the fibre module is the contraction of its
annihilator in the fibre ring (Lemma 05BY for restriction of scalars along
`S → S ⊗_R κ(𝔭)`). -/
theorem comap_colon_fibre (p : Ideal R) [p.IsPrime] (z : (S ⊗[R] p.ResidueField) ⊗[S] N) :
    ((⊥ : Submodule (S ⊗[R] p.ResidueField) ((S ⊗[R] p.ResidueField) ⊗[S] N)).colon {z}).comap
        (algebraMap S (S ⊗[R] p.ResidueField)) =
      (⊥ : Submodule S ((S ⊗[R] p.ResidueField) ⊗[S] N)).colon {z} := by
  ext s
  simp only [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot, algebraMap_smul]

end FibreModule

section Bridge

/-- A prime of the fibre ring `S ⊗_R κ(𝔭)` that is the annihilator of an element of the fibre
module contracts to a prime of `S` that is the annihilator of an element of `N / 𝔭N`. -/
theorem exists_quot_of_isAssociatedPrimeStacks_fibre [Module.Flat R N] (p : Ideal R) [p.IsPrime]
    {Q : Ideal (S ⊗[R] p.ResidueField)}
    (hQ : IsAssociatedPrimeStacks (S ⊗[R] p.ResidueField) ((S ⊗[R] p.ResidueField) ⊗[S] N) Q) :
    ∃ w : N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)),
      (⊥ : Submodule S _).colon {w} = Q.comap (algebraMap S (S ⊗[R] p.ResidueField)) := by
  obtain ⟨-, z, hz⟩ := hQ
  rw [Submodule.colon_span] at hz
  obtain ⟨w, hw⟩ := exists_quot_colon_eq p z
  exact ⟨w, by rw [hw, ← hz, comap_colon_fibre]⟩

/-- A prime of `S` that is the annihilator of an element of `N / 𝔭N` is the contraction of a
prime of the fibre ring `S ⊗_R κ(𝔭)` that is the annihilator of an element of the fibre
module. -/
theorem exists_isAssociatedPrimeStacks_fibre_of_quot [Module.Flat R N] (p : Ideal R) [p.IsPrime]
    {q : Ideal S} (hq : q.IsPrime)
    {w : N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))}
    (hw : (⊥ : Submodule S _).colon {w} = q) :
    ∃ Q : Ideal (S ⊗[R] p.ResidueField),
      IsAssociatedPrimeStacks (S ⊗[R] p.ResidueField) ((S ⊗[R] p.ResidueField) ⊗[S] N) Q ∧
        Q.comap (algebraMap S (S ⊗[R] p.ResidueField)) = q := by
  set z := quotToFibre N (S := S) p (FlatBaseChange.quotSMulEquivTensorQuot p w)
  have hz : (⊥ : Submodule S ((S ⊗[R] p.ResidueField) ⊗[S] N)).colon {z} = q := by
    rw [FlatBaseChange.colon_singleton_apply (injective_quotToFibre p)]
    exact (colon_singleton_linearEquiv
      (FlatBaseChange.quotSMulEquivTensorQuot (S := S) (N := N) p) w).trans hw
  have hcomap := (comap_colon_fibre p z).trans hz
  refine ⟨_, ⟨isPrime_of_isPrime_comap (exists_isUnit_mul_eq_algebraMap_fibre p)
    (hcomap ▸ hq), z, Submodule.colon_span⟩, hcomap⟩

end Bridge

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The inclusion of Tag 05C2, in the annihilator reading (Tag 00LA) on every side. -/
private theorem iUnion_fibre_subset [Module.Flat R N] :
    (⋃ p ∈ {p : PrimeSpectrum R | IsAssociatedPrimeStacks R M p.asIdeal},
        PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
          {Q | IsAssociatedPrimeStacks (S ⊗[R] p.asIdeal.ResidueField)
            ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N) Q.asIdeal}) ⊆
      {q : PrimeSpectrum S | IsAssociatedPrimeStacks S (N ⊗[R] M) q.asIdeal} := by
  intro q hq
  obtain ⟨p, ⟨hpp, m, hm⟩, hq⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨Q, hQ, rfl⟩ := hq
  rw [Submodule.colon_span] at hm
  obtain ⟨w, hw⟩ := exists_quot_of_isAssociatedPrimeStacks_fibre p.asIdeal hQ
  obtain ⟨hq', w', hw'⟩ := (associatedPrimes.tensorProduct_of_flat (R := R) (S := S) (M := M)
    (N := N)).1 (Set.mem_biUnion (x := p.asIdeal) ⟨hpp, m, hm⟩
      ⟨(PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) Q).isPrime, w, hw⟩)
  exact ⟨hq', w', by rw [Submodule.colon_span]; exact hw'⟩

end Stacks.AssociatedPrimes.FibreRings

open TensorProduct

/-- **Stacks Tag 05C2.** Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an
`S`-module which is flat as an `R`-module. Viewing `Spec(S ⊗_R κ(𝔭))` as a subset of `Spec(S)`
(Remark 00E6), we have
`Ass_S(N ⊗_R M) ⊇ ⋃_{𝔭 ∈ Ass_R(M)} Ass_{S ⊗_R κ(𝔭)}(N ⊗_R κ(𝔭))`,
and this inclusion is an equality if `R` is Noetherian. Every `Ass` is that of Definition 00LA,
`IsAssociatedPrimeStacks`: the primes that are the annihilator of an element, over `R`, over `S`
and over the fibre rings, with no Noetherian hypothesis on `S` or on the fibre rings.

The source writes `M ⊗_R N`; it is `N ⊗[R] M` here, the `S`-module structure being carried by the
left factor, and the two are the same `S`-module by `TensorProduct.comm`. The fibre module
`N ⊗_R κ(𝔭)` is spelled as the base change `(S ⊗[R] κ(𝔭)) ⊗[S] N`, which carries the action of
the fibre ring and is `S`-isomorphic to `N ⊗[R] κ(𝔭)` by
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. The inclusion
`Spec(S ⊗_R κ(𝔭)) ⊆ Spec(S)` is the image under `PrimeSpectrum.comap` of the canonical map
`S → S ⊗_R κ(𝔭)`. -/
@[stacks 05C2 "Every `Ass` is that of Definition 00LA (`IsAssociatedPrimeStacks`), over `R`, \
over `S` and over the fibre rings; the fibre module `N ⊗_R κ(𝔭)` is written \
`(S ⊗[R] κ(𝔭)) ⊗[S] N`."]
public theorem assStacks_tensorProduct_of_flat_fiberRing {R S M N : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] [Module.Flat R N] :
    (⋃ p ∈ {p : PrimeSpectrum R | IsAssociatedPrimeStacks R M p.asIdeal},
        PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
          {Q | IsAssociatedPrimeStacks (S ⊗[R] p.asIdeal.ResidueField)
            ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N) Q.asIdeal}) ⊆
      {q : PrimeSpectrum S | IsAssociatedPrimeStacks S (N ⊗[R] M) q.asIdeal} ∧
    (IsNoetherianRing R →
      {q : PrimeSpectrum S | IsAssociatedPrimeStacks S (N ⊗[R] M) q.asIdeal} =
        ⋃ p ∈ {p : PrimeSpectrum R | IsAssociatedPrimeStacks R M p.asIdeal},
          PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
            {Q | IsAssociatedPrimeStacks (S ⊗[R] p.asIdeal.ResidueField)
              ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N) Q.asIdeal}) := by
  refine ⟨Stacks.AssociatedPrimes.FibreRings.iUnion_fibre_subset, fun hR => ?_⟩
  have := hR
  refine Set.Subset.antisymm (fun q hq => ?_) Stacks.AssociatedPrimes.FibreRings.iUnion_fibre_subset
  obtain ⟨hqp, w, hw⟩ := hq
  rw [Submodule.colon_span] at hw
  have h0 : q.asIdeal ∈ {q : Ideal S | q.IsPrime ∧
      ∃ w : N ⊗[R] M, (⊥ : Submodule S (N ⊗[R] M)).colon {w} = q} := ⟨hqp, w, hw⟩
  rw [(associatedPrimes.tensorProduct_of_flat (R := R) (S := S) (M := M) (N := N)).2 hR] at h0
  have h := h0
  obtain ⟨p, hp, -, w', hw'⟩ := Set.mem_iUnion₂.mp h
  obtain ⟨hpp, m, hm⟩ := (isAssociatedPrime_iff (I := p) (M := M)).mp hp
  let P : PrimeSpectrum R := ⟨p, hpp⟩
  obtain ⟨Q, hQ, hQq⟩ :=
    Stacks.AssociatedPrimes.FibreRings.exists_isAssociatedPrimeStacks_fibre_of_quot
      (N := N) P.asIdeal q.isPrime hw'
  exact Set.mem_biUnion (x := P) ⟨hpp, m, by rw [Submodule.colon_span]; exact hm.symm⟩
    ⟨⟨Q, hQ.1⟩, hQ, PrimeSpectrum.ext hQq⟩
