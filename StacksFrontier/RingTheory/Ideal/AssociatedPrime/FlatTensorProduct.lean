module

public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.RelativeAssassin
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Associated primes of a flat tensor product, read on the fibre rings

Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an `S`-module which is flat as
an `R`-module. Stacks Tag 05C2 compares the primes of `S` associated to `N ⊗_R M` with the primes
associated to the fibre modules `N ⊗_R κ(𝔭)` over the fibre rings `S ⊗_R κ(𝔭)`, for `𝔭` running
through the associated primes of `M`, viewed inside `Spec(S)` through the canonical map
`Spec(S ⊗_R κ(𝔭)) → Spec(S)`.

Both halves are obtained from the comparison of the six candidate relative assassins
(`Module.relativeAssassin_comparison`, Tag 05GB), which identifies the fibre-ring description `A'`
with the description `A_fin` by the modules `N / 𝔭N` — unconditionally through `A`, and, for a
Noetherian `R`, all the way along to the description `B_fin` by the modules `N ⊗_R M'` for finite
`M'`.

For the inclusion this leaves a base change of an injection: a prime `𝔭` which is the annihilator
of an `m ∈ M` comes with an injection `R/𝔭 → M`, `r ↦ r • m`, and tensoring with the flat module
`N` keeps it injective, so `N / 𝔭N` is an `S`-submodule of `N ⊗_R M` and every prime of `S` which
is the radical of the annihilator of an element of `N / 𝔭N` is the radical of the annihilator of
an element of `N ⊗_R M`. A prime `𝔮` in the fibre over `𝔭` is automatic: the map `R → S ⊗_R κ(𝔭)`
factors through the field `κ(𝔭)`, whose only prime is `(0)`, and the kernel of `R → κ(𝔭)` is `𝔭`.

For the converse, over a Noetherian `R`, a witness `z ∈ N ⊗_R M` for `𝔮` already lies in
`N ⊗_R M₀` for a finitely generated submodule `M₀ ⊆ M`, with the same annihilator because
flatness makes `N ⊗_R M₀ → N ⊗_R M` injective; a finite module is a quotient of some `Rⁿ`, so
`M₀` may be replaced by an isomorphic module small enough to be a witness for `B_fin`, and
`B_fin = A'` gives `𝔮` in the fibre-ring description. That the contraction `𝔭 = R ∩ 𝔮` is
associated to `M` is the descent of associated primes along a flat base change: for `P` flat over
a Noetherian `R` and `M` finite, `Ass_R(P ⊗_R M) ⊆ Ass_R(M)`.

## Main results

* `Stacks.AssociatedPrimes.FibreRings.solution`: Stacks Tag 05C2.

## Implementation notes

`Ass_S` and `Ass_{S ⊗_R κ(𝔭)}` are Mathlib's `associatedPrimes`, the primes equal to the radical
of the annihilator of an element, as in Tag 05GB; the index set of the first assertion is the
source's `Ass_R(M)` of Tag 00LA, the primes that *are* such an annihilator, which is what supplies
the injection `R/𝔭 → M`. Over the Noetherian ring of the second assertion the two readings agree
(`isAssociatedPrime_iff_exists_injective_linearMap` produces the injection there, but only there:
it carries `IsNoetherianRing R`, so the first assertion builds its injection by hand from the
annihilator, in `exists_injective_of_colon_eq`), and the index set is spelled with
`associatedPrimes`.

The descent of associated primes along a flat base change,
`FlatBaseChange.associatedPrimes_tensorProduct_subset_of_flat`, is a statement about
`associatedPrimes` alone, with no reference to the ring map `R → S`; it and the reduction of
`N ⊗_R M` to finitely generated submodules `M₀ ⊆ M` (`FlatBaseChange.exists_fg_mem_range`) are
taken from Tag 0312, which proves both for want of a Mathlib name.

The `S`-linear maps `N ⊗_R M → N ⊗_R M'` induced by an `R`-linear `M → M'` are
`TensorProduct.AlgebraTensorModule.map LinearMap.id`, which agrees pointwise with
`LinearMap.lTensor N` (`FlatBaseChange.map_id_apply`); the flatness API is phrased for the latter
and the associated-primes API needs the former.

## References

* [StacksProject 05C2](https://stacks.math.columbia.edu/tag/05C2)
-/

open TensorProduct

namespace Stacks.AssociatedPrimes.FibreRings

universe u v w x

/-- Restriction of scalars along `R → S` contracts an associated prime of an `S`-module to an
associated prime of the same module over `R`. -/
@[ega "IV 3.1.10.1" "Contraction inclusion"]
private theorem comap_mem_associatedPrimes {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] {X : Type*} [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    {q : Ideal S} (hq : q ∈ associatedPrimes S X) :
    q.comap (algebraMap R S) ∈ associatedPrimes R X := by
  obtain ⟨hqp, z, hz⟩ := hq
  refine ⟨hqp.comap _, z, ?_⟩
  have hcolon : (⊥ : Submodule R X).colon {z}
      = ((⊥ : Submodule S X).colon {z}).comap (algebraMap R S) := by
    ext r
    simp [Ideal.mem_comap, Submodule.mem_colon_singleton, algebraMap_smul]
  rw [hcolon, ← Ideal.comap_radical, ← hz]

section ResidueField

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A prime of a ring receiving the residue field `κ(𝔭)` contracts to `𝔭` along
`R → κ(𝔭) → A`: it contracts to a prime of a field, hence to `(0)`, whose preimage in `R` is the
kernel `𝔭` of `R → κ(𝔭)`. -/
private theorem comap_comp_algebraMap_residueField (p : Ideal R) [p.IsPrime] {A : Type*}
    [CommRing A] (f : p.ResidueField →+* A) (Q : Ideal A) [Q.IsPrime] :
    Q.comap (f.comp (algebraMap R p.ResidueField)) = p := by
  rw [← Ideal.comap_comap, (Ideal.eq_bot_or_top _).resolve_right (Ideal.comap_isPrime f Q).ne_top,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

/-- A prime of the fibre ring `S ⊗_R κ(𝔭)` contracts to `𝔭` in `R`: the structure map
`R → S ⊗_R κ(𝔭)` is both `R → S → S ⊗_R κ(𝔭)` and `R → κ(𝔭) → S ⊗_R κ(𝔭)`. -/
public theorem comap_comap_algebraMap_fibre (p : Ideal R) [p.IsPrime]
    (Q : Ideal (S ⊗[R] p.ResidueField)) [Q.IsPrime] :
    (Q.comap (algebraMap S (S ⊗[R] p.ResidueField))).comap (algebraMap R S) = p := by
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
    ← (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := p.ResidueField)).comp_algebraMap]
  exact comap_comp_algebraMap_residueField p _ Q

end ResidueField

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x} [CommRing R] [CommRing S]
  [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
  [IsScalarTower R S N]

section BaseChange

/-- An associated prime of `N ⊗_R M` is already an associated prime of `N ⊗_R M₀` for some
finitely generated submodule `M₀ ⊆ M`, flatness of `N` keeping the annihilator of the witness. -/
private theorem exists_fg_mem_associatedPrimes [Module.Flat R N] {q : Ideal S}
    (hq : q ∈ associatedPrimes S (N ⊗[R] M)) :
    ∃ M₀ : Submodule R M, M₀.FG ∧ q ∈ associatedPrimes S (N ⊗[R] ↥M₀) := by
  obtain ⟨hqp, z, hz⟩ := hq
  obtain ⟨M₀, hM₀, w, hw⟩ := FlatBaseChange.exists_fg_mem_range (S := S) z
  refine ⟨M₀, hM₀, hqp, w, ?_⟩
  rw [hz, ← hw, FlatBaseChange.colon_singleton_apply
    (FlatBaseChange.injective_map_id (S := S) (Submodule.injective_subtype M₀)) w]

end BaseChange

/-- A finite module has a copy in `Type (max u v)`, so an associated prime of `N ⊗_R Y` for a
finite `R`-module `Y` in any universe is an associated prime of `N ⊗_R X` for a finite `X` in that
one: a finite module is a quotient of some `Rⁿ`. -/
private theorem exists_finite_mem_associatedPrimes {Y : Type*} [AddCommGroup Y] [Module R Y]
    [Module.Finite R Y] {q : Ideal S} (hq : q ∈ associatedPrimes S (N ⊗[R] Y)) :
    ∃ (X : Type (max u v)) (_ : AddCommGroup X) (_ : Module R X) (_ : Module.Finite R X),
      q ∈ associatedPrimes S (N ⊗[R] X) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R Y
  refine ⟨ULift.{v} ((Fin n → R) ⧸ LinearMap.ker f), inferInstance, inferInstance,
    Module.Finite.equiv
      (ULift.moduleEquiv.trans (LinearMap.quotKerEquivOfSurjective f hf)).symm, ?_⟩
  exact (LinearEquiv.isAssociatedPrime_iff (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl S N)
    (ULift.moduleEquiv.trans (LinearMap.quotKerEquivOfSurjective f hf)))).mpr hq

/-- `n ⊗ 1 = 0` in `N ⊗_R R/I` exactly when `n` lies in `IN`, which as an `S`-submodule of `N` is
`IS • N`. -/
private theorem tmul_one_eq_zero_iff (I : Ideal R) (n : N) :
    n ⊗ₜ[R] (1 : R ⧸ I) = 0 ↔ n ∈ I.map (algebraMap R S) • (⊤ : Submodule S N) := by
  rw [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top,
    ← Submodule.Quotient.mk_eq_zero, ← TensorProduct.tensorQuotEquivQuotSMul_symm_mk I n,
    map_eq_zero_iff _ (TensorProduct.tensorQuotEquivQuotSMul N I).symm.injective]

/-- The kernel of `N → N ⊗_R M`, `n ↦ n ⊗ φ 1`, for `φ : R ⧸ I → M` injective and `N` flat over
`R`, is `IN`: the map is `n ⊗ 1 ↦ n ⊗ φ 1` after `N ≅ N ⊗_R R/I`, and flatness makes that
injective. -/
private theorem ker_mk_flip [Module.Flat R N] (I : Ideal R) (φ : (R ⧸ I) →ₗ[R] M)
    (hφ : Function.Injective φ) :
    LinearMap.ker ((TensorProduct.AlgebraTensorModule.mk R S N M).flip (φ 1))
      = I.map (algebraMap R S) • (⊤ : Submodule S N) := by
  ext n
  have h : (TensorProduct.AlgebraTensorModule.mk R S N M).flip (φ 1) n
      = LinearMap.lTensor N φ (n ⊗ₜ[R] (1 : R ⧸ I)) := rfl
  rw [LinearMap.mem_ker, h,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap φ hφ),
    tmul_one_eq_zero_iff (S := S)]

/-- The map `X ⧸ p → Y` induced by `f : X → Y` is injective when `p` is exactly the kernel of
`f`. -/
private theorem injective_liftQ_of_ker_eq {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] {p : Submodule R X} {f : X →ₗ[R] Y}
    (hker : LinearMap.ker f = p) :
    Function.Injective (p.liftQ f hker.ge) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ hker.symm)

/-- Base change of an injection `R ⧸ I → M` along a flat `S`-module `N`: `N / IN` is an
`S`-submodule of `N ⊗_R M`, so every prime of `S` associated to `N / IN` is associated to
`N ⊗_R M`. -/
private theorem associatedPrimes_quot_subset [Module.Flat R N] (I : Ideal R)
    (φ : (R ⧸ I) →ₗ[R] M) (hφ : Function.Injective φ) :
    associatedPrimes S (N ⧸ (I.map (algebraMap R S) • (⊤ : Submodule S N))) ⊆
      associatedPrimes S (N ⊗[R] M) := by
  have hker := ker_mk_flip (S := S) (N := N) I φ hφ
  exact fun q hq => hq.map_of_injective
    ((I.map (algebraMap R S) • (⊤ : Submodule S N)).liftQ _ hker.ge)
    (injective_liftQ_of_ker_eq hker)

/-- A prime that *is* the annihilator of an `m ∈ M` (the reading of Tag 00LA) comes with an
injection `R ⧸ I → M`, namely `r ↦ r • m`. Unlike
`isAssociatedPrime_iff_exists_injective_linearMap` this needs no hypothesis on `R`. -/
private theorem exists_injective_of_colon_eq {I : Ideal R} {m : M}
    (hm : (⊥ : Submodule R M).colon {m} = I) :
    ∃ φ : (R ⧸ I) →ₗ[R] M, Function.Injective φ := by
  have hker : LinearMap.ker (LinearMap.toSpanSingleton R M m) = I := by
    rw [← hm]; ext r; simp [LinearMap.toSpanSingleton, Submodule.mem_colon_singleton]
  exact ⟨I.liftQ _ hker.ge,
    injective_liftQ_of_ker_eq hker⟩

/-- Tag 05GB (1) and (4): the fibre-ring description `A'` of the relative assassin agrees with the
description `A_fin` by the modules `N / 𝔭N`, for `N` flat over `R`. -/
private theorem fibreImage_eq_quot [Module.Flat R N] :
    {q : PrimeSpectrum S | ∃ Q : PrimeSpectrum
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
        Q.asIdeal ∈ associatedPrimes
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
          ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N) ∧
        PrimeSpectrum.comap (algebraMap S
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q}
      = {q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimes S
          (N ⧸ ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map (algebraMap R S) •
            (⊤ : Submodule S N)))} := by
  obtain ⟨e0, -, -, h4, -⟩ := Module.relativeAssassin_comparison R S N rfl rfl rfl rfl rfl rfl
  exact e0.symm.trans (h4 inferInstance).1

/-- Tag 05GB (5): over a Noetherian `R` and for `N` flat over `R`, the fibre-ring description `A'`
of the relative assassin agrees with the description `B_fin` by the modules `N ⊗_R M'` for finite
`M'`. -/
private theorem fibreImage_eq_tensorFinite [Module.Flat R N] (hR : IsNoetherianRing R) :
    {q : PrimeSpectrum S | ∃ Q : PrimeSpectrum
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
        Q.asIdeal ∈ associatedPrimes
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
          ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N) ∧
        PrimeSpectrum.comap (algebraMap S
          (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q}
      = {q : PrimeSpectrum S | ∃ (X : Type (max u v)) (_ : AddCommGroup X) (_ : Module R X)
          (_ : Module.Finite R X), q.asIdeal ∈ associatedPrimes S (N ⊗[R] X)} := by
  obtain ⟨-, -, -, -, h5⟩ := Module.relativeAssassin_comparison R S N rfl rfl rfl rfl rfl rfl
  obtain ⟨-, e1, e2, e3, -⟩ := h5 hR inferInstance
  exact e1.trans (e2.trans e3)

omit [Module R N] [IsScalarTower R S N] in
/-- A prime of `S` in the image of the fibre over `𝔭` is described by the fibre over its own
contraction: the two agree once the contraction has been computed. -/
private theorem mem_fibreImage {q : PrimeSpectrum S} (t : PrimeSpectrum R)
    (ht : PrimeSpectrum.comap (algebraMap R S) q = t)
    (Q : PrimeSpectrum (S ⊗[R] t.asIdeal.ResidueField))
    (hQ : Q.asIdeal ∈ associatedPrimes (S ⊗[R] t.asIdeal.ResidueField)
      ((S ⊗[R] t.asIdeal.ResidueField) ⊗[S] N))
    (hQq : PrimeSpectrum.comap (algebraMap S (S ⊗[R] t.asIdeal.ResidueField)) Q = q) :
    ∃ Q' : PrimeSpectrum
      (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
      Q'.asIdeal ∈ associatedPrimes
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
        ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N) ∧
      PrimeSpectrum.comap (algebraMap S
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q' = q := by
  subst ht
  exact ⟨Q, hQ, hQq⟩

/-- The image in `Spec(S)` of the primes associated to the fibre module at a prime `𝔭` which comes
with an injection `R/𝔭 → M` consists of primes associated to `N ⊗_R M`. -/
private theorem image_subset_of_injective [Module.Flat R N] (p : PrimeSpectrum R)
    (φ : (R ⧸ p.asIdeal) →ₗ[R] M) (hφ : Function.Injective φ) :
    PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
      {Q | Q.asIdeal ∈ associatedPrimes (S ⊗[R] p.asIdeal.ResidueField)
        ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N)} ⊆
      {q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)} := by
  rintro q ⟨Q, hQ, rfl⟩
  have hp : PrimeSpectrum.comap (algebraMap R S)
      (PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) Q) = p :=
    PrimeSpectrum.ext (comap_comap_algebraMap_fibre p.asIdeal Q.asIdeal)
  have h1 := (Set.ext_iff.mp (fibreImage_eq_quot (R := R) (S := S) (N := N))
    (PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) Q)).mp
      (mem_fibreImage p hp Q hQ rfl)
  rw [Set.mem_ofPred_eq, hp] at h1
  exact associatedPrimes_quot_subset p.asIdeal φ hφ h1

public theorem solution {R S M N : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] [Module.Flat R N] :
    (⋃ p ∈ {p : PrimeSpectrum R | ∃ m : M, (⊥ : Submodule R M).colon {m} = p.asIdeal},
        PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
          {Q | Q.asIdeal ∈ associatedPrimes (S ⊗[R] p.asIdeal.ResidueField)
            ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N)}) ⊆
      {q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)} ∧
    (IsNoetherianRing R →
      {q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)} =
        ⋃ p ∈ {p : PrimeSpectrum R | p.asIdeal ∈ associatedPrimes R M},
          PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
            {Q | Q.asIdeal ∈ associatedPrimes (S ⊗[R] p.asIdeal.ResidueField)
              ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N)}) := by
  refine ⟨Set.iUnion₂_subset fun p hp => ?_, fun hR => ?_⟩
  · obtain ⟨m, hm⟩ := hp
    obtain ⟨φ, hφ⟩ := exists_injective_of_colon_eq hm
    exact image_subset_of_injective p φ hφ
  · have := hR
    refine Set.Subset.antisymm (fun q hq => ?_) (Set.iUnion₂_subset fun p hp => ?_)
    · obtain ⟨M₀, hM₀, hq₀⟩ := exists_fg_mem_associatedPrimes (M := M) hq
      have : Module.Finite R ↥M₀ := Module.Finite.iff_fg.mpr hM₀
      obtain ⟨Q, hQ, hQq⟩ := (Set.ext_iff.mp (fibreImage_eq_tensorFinite hR) q).mpr
        (exists_finite_mem_associatedPrimes (S := S) (N := N) hq₀)
      have hcontr : (PrimeSpectrum.comap (algebraMap R S) q).asIdeal ∈
          associatedPrimes R (N ⊗[R] ↥M₀) := comap_mem_associatedPrimes hq₀
      exact Set.mem_biUnion
        (associatedPrimes.subset_of_injective (f := M₀.subtype) (Submodule.injective_subtype _)
          (FlatBaseChange.associatedPrimes_tensorProduct_subset_of_flat hcontr))
        ((Set.mem_image _ _ _).mpr ⟨Q, hQ, hQq⟩)
    · obtain ⟨-, φ, hφ⟩ :=
        (isAssociatedPrime_iff_exists_injective_linearMap p.asIdeal M).mp hp
      exact image_subset_of_injective p φ hφ

end Stacks.AssociatedPrimes.FibreRings

/-!
# Associated primes of a flat tensor product, described on the fibre rings

Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an `S`-module which is flat as
an `R`-module. For a prime `𝔭` of `R` the fibre ring `S ⊗_R κ(𝔭)` has spectrum the fibre of
`Spec(S) → Spec(R)` over `𝔭`, so `Spec(S ⊗_R κ(𝔭))` is a subset of `Spec(S)` (Tag 00E6), and the
fibre module `N ⊗_R κ(𝔭)` is a module over it. Every prime of `S` which, viewed in such a fibre,
is associated to the fibre module of an associated prime of `M` is associated to `N ⊗_R M`
over `S`:
`Ass_S(N ⊗_R M) ⊇ ⋃_{𝔭 ∈ Ass_R(M)} Ass_{S ⊗_R κ(𝔭)}(N ⊗_R κ(𝔭))`,
and the inclusion is an equality when `R` is Noetherian.

This is Tag 0312 with the modules `N / 𝔭N` over `S` replaced by the fibre modules `N ⊗_R κ(𝔭)`
over the fibre rings: the two indexings agree because `N ⊗_R κ(𝔭)` is a localization of
`N / 𝔭N` at which flatness makes every element of `R ∖ 𝔭` act injectively (Tags 05BY, 00HI
and 05C1).

## Main results

* `associatedPrimes.tensorProduct_of_flat_fiberRing`: the inclusion above, an equality when `R`
  is Noetherian.

## Implementation notes

The two readings of `Ass_R(M)` on the index side are distinguished, and this is forced. The source's
`Ass_R(M)` is Definition 00LA: the primes `𝔭` for which there is an `m ∈ M` with `Ann_R(m) = 𝔭`.
Mathlib's `associatedPrimes R M` is the weaker, radical-flavoured notion `𝔭 = √Ann_R(m)` (the field
`eq_radical_colon` of `Submodule.IsAssociatedPrime`), which the source reserves for §0546. The first
assertion carries no hypothesis on `R`, and there the distinction is not conservative: an index
prime only equal to the *radical* of an annihilator supplies no injection `R/𝔭 → M` to base change
along, and the inclusion is false — and its failure transfers to the fibre-ring form
because 05BY,
00HI and 05C1 turn `Ass_S(N / 𝔭N)` into the fibre-ring set by equalities. So the first conjunct is
indexed by the source's set, spelled `∃ m : M, (⊥ : Submodule R M).colon {m} = 𝔭` — Mathlib's own
phrasing of `Ann_R(m)`, as in `isAssociatedPrime_iff`. It is a subset of `associatedPrimes R M`, a
prime being its own radical, so the statement is the source's and not a weakening of it. The second
assertion carries `IsNoetherianRing R`, under which the two readings coincide
(`isAssociatedPrime_iff`, Tag 058A), so it is phrased with `associatedPrimes R M`, the notion
carrying the API.

`Ass_S` and `Ass_{S ⊗_R κ(𝔭)}` are Mathlib's `associatedPrimes` throughout. The source imposes no
Noetherian hypothesis on `S` or on the fibre rings, so no comparison is available there; the
radical reading makes the fibre sets larger and the target of the inclusion larger, and the
statement holds in it, which is also how the neighbouring Tags 0312, 05GB and 05GC read it.

The source writes the tensor product as `M ⊗_R N`; it is written `N ⊗[R] M` here, because the
`S`-module structure on a tensor product over `R` is carried by the left factor
(`TensorProduct.AlgebraTensorModule`, using `IsScalarTower R S N`). The two are the same
`S`-module by `TensorProduct.comm`. This is the choice made in Tag 0312
(`associatedPrimes.tensorProduct_of_flat`) and in Tag 05GB
(`Module.relativeAssassin_comparison`), so the three statements compare directly.

The fibre module is spelled as the base change `(S ⊗[R] κ(𝔭)) ⊗[S] N`, there being no
`Module (S ⊗[R] κ(𝔭)) (N ⊗[R] κ(𝔭))` instance in Mathlib. It is the same `S`-module as
`N ⊗[R] κ(𝔭)` by `TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N κ(𝔭)` (after
`TensorProduct.comm`), which is `S`-linear rather than fibre-ring-linear — there is no
fibre-ring-linear bridge to be had, the right-hand side carrying no fibre-ring action — and the
fibre-ring action on the left-hand side is the source's: `(s ⊗ lam) • ((s' ⊗ mu) ⊗ n)` matches
`(s ⊗ lam) • (n ⊗ mu) = s • n ⊗ lam * mu` under the cancellation. This is the spelling of the set
`A'` of Tag 05GB.

Remark 00E6, which views `Spec(S ⊗_R κ(𝔭))` inside `Spec(S)`, is spelled as the image under
`PrimeSpectrum.comap (algebraMap S (S ⊗[R] κ(𝔭)))`, the canonical map
`Spec(S ⊗_R κ(𝔭)) → Spec(S)`; again as for `A'` in Tag 05GB.

The union is indexed by `p : PrimeSpectrum R` rather than by an ideal: an associated prime is
prime, but it is `PrimeSpectrum` that carries that primality as an instance, which is what lets
`κ(𝔭)` be formed.

No finiteness hypothesis is imposed on `M`, and nothing is assumed of `S` beyond receiving the
ring map: the source's proof reduces the Noetherian half to a finite `M` by writing `M` as the
union of its finite submodules.

Faithfulness. (1) No hypothesis is dead: `Module.Flat R N` is the source's standing hypothesis
and is used by both halves — in the inclusion, to turn an injection `R/𝔭 → M` into an injection
`N/𝔭N → N ⊗_R M`, and in the equality, to make each element of `R ∖ 𝔭` act injectively on the
relevant subquotients of `N` — while `IsNoetherianRing R`, which the source imposes on its second
assertion alone, occurs in that conjunct alone. (2) The scalars and base are the source's: `Ass`
is taken over `S` for `N ⊗_R M`, over the fibre ring `S ⊗_R κ(𝔭)` for the fibre module, and over
`R` for the index set `Ass_R(M)`; the tensor products, the primes `𝔭` and their residue fields
are over `R`; `M` is an `R`-module, `N` is an `S`-module, and its `R`-module structure is the
restriction of scalars along `R → S` (`IsScalarTower R S N`); flatness is flatness over `R`.
(3) The canonical maps are pinned, not merely asserted to exist: the inclusion
`Spec(S ⊗_R κ(𝔭)) ⊆ Spec(S)` of Remark 00E6 is the image under
`PrimeSpectrum.comap (algebraMap S (S ⊗[R] κ(𝔭)))`, and the fibre ring and fibre module are the
base changes along `R → κ(𝔭)`, not abstract objects with those properties. (4) The instantiation
is not degenerate: for `R = k` a field, `S = k[x, y]/(xy)`, `N = S` and `M = k` the only prime of
`R` is `(0)`, with `κ((0)) = k` and fibre ring `S`, so both sides are
`Ass_S(S) = {(x), (y)}`, and `R` is Noetherian, so the equality is a statement about a nonempty
set; for `R = S = ℤ`, `N = ℤ` and `M = ℤ/2ℤ` both sides are `{(2)}`, the index prime `(2)` being
`Ann_ℤ(1)` on the nose, so the first conjunct is nonvacuous in its 00LA indexing too.

## References

* [StacksProject 05C2](https://stacks.math.columbia.edu/tag/05C2)

## Tags

associated prime, flat module, tensor product, fibre ring, residue field
-/

open TensorProduct

/-- **Stacks Tag 05C2.** Let `R → S` be a ring map, let `M` be an `R`-module and let `N` be an
`S`-module which is flat as an `R`-module. Viewing `Spec(S ⊗_R κ(𝔭))` as a subset of `Spec(S)`
(Tag 00E6), we have
`Ass_S(N ⊗_R M) ⊇ ⋃_{𝔭 ∈ Ass_R(M)} Ass_{S ⊗_R κ(𝔭)}(N ⊗_R κ(𝔭))`,
and this inclusion is an equality if `R` is Noetherian. Here `Ass_R(M)` is the source's set of
associated primes of Tag 00LA, the primes that *are* the annihilator of an element of `M`; over a
Noetherian ring it agrees with Mathlib's `associatedPrimes`, which is how the second assertion
spells it. -/
@[stacks 05C2, ega "IV 3.3.1" "affine case", ega "IV 3.3.6" "affine case, X = S"]
public theorem associatedPrimes.tensorProduct_of_flat_fiberRing {R S M N : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] [Module.Flat R N] :
    (⋃ p ∈ {p : PrimeSpectrum R | ∃ m : M, (⊥ : Submodule R M).colon {m} = p.asIdeal},
        PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
          {Q | Q.asIdeal ∈ associatedPrimes (S ⊗[R] p.asIdeal.ResidueField)
            ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N)}) ⊆
      {q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)} ∧
    (IsNoetherianRing R →
      {q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)} =
        ⋃ p ∈ {p : PrimeSpectrum R | p.asIdeal ∈ associatedPrimes R M},
          PrimeSpectrum.comap (algebraMap S (S ⊗[R] p.asIdeal.ResidueField)) ''
            {Q | Q.asIdeal ∈ associatedPrimes (S ⊗[R] p.asIdeal.ResidueField)
              ((S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N)}) :=
                by apply Stacks.AssociatedPrimes.FibreRings.solution
