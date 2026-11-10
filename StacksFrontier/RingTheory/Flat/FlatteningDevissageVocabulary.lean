module

public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# The flatness condition of Stacks 05ML read on a dévissage stage algebra

In the situation of Stacks Tag 05MK the algebra `B` is **local**, and the flatness condition of
Stacks Tag 05ML quantifies over the primes of `B ⊗[A] R` containing `𝔪_R B' + 𝔪_B B'`. The stage
algebras `B₁, …, B_n` of a complete dévissage are **not** local: the source's proof of
Stacks Tag 05PG runs the dévissage over `B₁` and only then localizes at the stage prime `q₁`, so
`B` is `(B₁)_{q₁}` and `M` is `(M₁)_{q₁}`.

This file translates between the two vocabularies. The primes of `B ⊗[A] R` are the primes of
`B₁ ⊗[A] R` that contract into `q₁`, and among those the ones containing `𝔪_B B'` are the ones
contracting *onto* `q₁`; so the condition of Stacks Tag 05ML over `R` is flatness of the base
change of `M₁` at every prime of `B₁ ⊗[A] R` which contains `𝔪_R` and contracts to `q₁` in `B₁`.

The two halves of the translation are:

* the analytic half, `Module.flat_localizedModule_atPrime_comap_tensor_iff` in
  `StacksFrontier.RingTheory.Flat.Stratification`, which identifies the two localized modules; and
* the combinatorial half, proved here: the primes the condition tests are exactly the primes of
  `B₁ ⊗[A] R` contracting to `q₁`.

## Main results

* `Module.FlatAtPointSituation.comap_eq_iff_le_and_disjoint`: for a prime of `B₁ ⊗[A] R`,
  contracting to `q₁` is the same as containing `q₁(B₁ ⊗[A] R)` and missing the image of
  `B₁ ∖ q₁`.
* `Module.FlatAtPointSituation.conditionOn_iff_forall_prime_comap`: **the translation.** The
  flatness condition of Stacks Tag 05ML over `R` holds exactly when the base change of `M₁` is
  flat over `R` at every prime of `B₁ ⊗[A] R` which contains the extension of `𝔪_R` and contracts
  to `q₁`.

## Implementation notes

The algebra `B₁` is called `C` and the module `M₁` is called `N` below, matching
`Module.flat_localizedModule_atPrime_comap_tensor_iff`.

The `R`-algebra structure on `C ⊗[A] R` is `Algebra.TensorProduct.rightAlgebra`, introduced by a
`letI` in the statement exactly as `Module.IsFlatAtPrimesOver` introduces it on `B ⊗[A] R`; the
`R`-module structure on the localized module is read off it. The `(C ⊗[A] R)`-algebra structure on
`B ⊗[A] R` is the base change of `C → B`, which is what makes `B ⊗[A] R` a localization of
`C ⊗[A] R` by `IsLocalization.tensorProduct_tensorProduct`.

Nothing here carries a Stacks tag: this is an input to Stacks Tag 05PG, not a proof of any tag.

## References

* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x y z

namespace Module.FlatAtPointSituation

variable {S : FlatAtPointSituation.{u, v, w}} {C : Type y} [CommRing C] [Algebra S.A C]
  [Algebra C S.B] [IsScalarTower S.A C S.B] (q₁ : Ideal C) [q₁.IsPrime]
  [IsLocalization q₁.primeCompl S.B]

section Primes

variable (R : Type x) [CommRing R] [Algebra S.A R]

omit [IsScalarTower S.A C S.B] in
/-- **Contracting onto the stage prime is containment plus disjointness.** A prime of
`C ⊗[A] R` contracts to `q₁` in `C` exactly when it contains the extension of `q₁` and misses the
image of the complement of `q₁`.

The two halves of the right-hand side are the two halves of the equality of ideals: containment of
the extension is one inclusion, and missing the image of the complement is the other. -/
theorem comap_eq_iff_le_and_disjoint (𝔮 : Ideal (C ⊗[S.A] R)) :
    letI : Algebra R (C ⊗[S.A] R) := Algebra.TensorProduct.rightAlgebra
    𝔮.comap (algebraMap C (C ⊗[S.A] R)) = q₁ ↔
      Ideal.map (algebraMap C (C ⊗[S.A] R)) q₁ ≤ 𝔮 ∧
        Disjoint
          ((Algebra.algebraMapSubmonoid (C ⊗[S.A] R) q₁.primeCompl : Submonoid (C ⊗[S.A] R)) :
            Set (C ⊗[S.A] R)) (𝔮 : Set (C ⊗[S.A] R)) := by
  constructor
  · rintro rfl
    refine ⟨Ideal.map_le_iff_le_comap.mpr le_rfl, Set.disjoint_left.mpr ?_⟩
    rintro _ ⟨c, hc, rfl⟩ hmem
    exact hc hmem
  · rintro ⟨hle, hdisj⟩
    refine le_antisymm (fun c hc ↦ ?_) (Ideal.map_le_iff_le_comap.mp hle)
    by_contra hcon
    exact Set.disjoint_left.mp hdisj ⟨c, hcon, rfl⟩ hc

end Primes

section Translation

variable {N : Type z} [AddCommGroup N] [Module C N] [Module C S.M] [IsScalarTower C S.B S.M]

/-- **The flatness condition of Stacks Tag 05ML, read on a dévissage stage algebra.** Let `B` be
the localization of `C` at a prime `q₁` and let `M` be the corresponding localization of a
`C`-module `N`. Then the condition of Stacks Tag 05ML over a local `A`-algebra `R` holds exactly
when the base change of `N` is flat over `R` at every prime of `C ⊗[A] R` which contains the
extension of `𝔪_R` and contracts to `q₁` in `C`.

`B ⊗[A] R` is the localization of `C ⊗[A] R` at the image of `C ∖ q₁`
(`IsLocalization.tensorProduct_tensorProduct`), so its primes are the primes of `C ⊗[A] R` missing
that image; and `𝔪_B = q₁ B`, so the ones containing `𝔪_B B'` are the ones containing
`q₁ (C ⊗[A] R)`. Together — `Module.FlatAtPointSituation.comap_eq_iff_le_and_disjoint` — these are
the primes contracting to `q₁`. The two localized modules are identified by
`Module.flat_localizedModule_atPrime_comap_tensor_iff`.

This is the translation the source's proof of Stacks Tag 05PG performs silently when it runs the
dévissage over `B₁` and reads the functor `F_lf` of the local situation `((B₁)_{q₁}, (M₁)_{q₁})`
off it. -/
theorem conditionOn_iff_forall_prime_comap (g : N →ₗ[C] S.M)
    [IsLocalizedModule q₁.primeCompl g] (R : Type x) [CommRing R] [IsLocalRing R]
    [Algebra S.A R] :
    letI : Algebra R (C ⊗[S.A] R) := Algebra.TensorProduct.rightAlgebra
    S.ConditionOn R ↔ ∀ (𝔮 : Ideal (C ⊗[S.A] R)) (_ : 𝔮.IsPrime),
      Ideal.map (algebraMap R (C ⊗[S.A] R)) (maximalIdeal R) ≤ 𝔮 →
      𝔮.comap (algebraMap C (C ⊗[S.A] R)) = q₁ →
        Module.Flat R (LocalizedModule 𝔮.primeCompl ((C ⊗[S.A] R) ⊗[C] N)) := by
  let : Algebra R (C ⊗[S.A] R) := Algebra.TensorProduct.rightAlgebra
  let : Algebra R (S.B ⊗[S.A] R) := Algebra.TensorProduct.rightAlgebra
  let τ : (C ⊗[S.A] R) →ₐ[S.A] (S.B ⊗[S.A] R) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom S.A C S.B) (AlgHom.id S.A R)
  let : Algebra (C ⊗[S.A] R) (S.B ⊗[S.A] R) := τ.toRingHom.toAlgebra
  have : IsScalarTower C (C ⊗[S.A] R) (S.B ⊗[S.A] R) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- The right-hand inclusion is compatible with the base change of `C → B`.
  have hrightHom : (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)).comp
      (algebraMap R (C ⊗[S.A] R)) = algebraMap R (S.B ⊗[S.A] R) := by
    ext r
    change τ ((1 : C) ⊗ₜ[S.A] r) = (1 : S.B) ⊗ₜ[S.A] r
    simpa only [map_one, AlgHom.id_apply] using
      Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom S.A C S.B) (AlgHom.id S.A R) 1 r
  -- The left-hand inclusion is `C → B` followed by the inclusion of `B`.
  have hleftHom : (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)).comp
      (algebraMap C (C ⊗[S.A] R)) =
      (algebraMap S.B (S.B ⊗[S.A] R)).comp (algebraMap C S.B) := RingHom.ext fun c ↦ by
    change τ (c ⊗ₜ[S.A] (1 : R)) = _
    rw [Algebra.TensorProduct.map_tmul]
    simp [Algebra.TensorProduct.algebraMap_apply]
  -- The two spellings of the inclusions of `B` and of `R` into `B ⊗[A] R`.
  have hLHom : (algebraMap S.B (S.B ⊗[S.A] R)) =
      (Algebra.TensorProduct.includeLeftRingHom (R := S.A) (A := S.B) (B := R)) := by
    ext b
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hRHom : (algebraMap R (S.B ⊗[S.A] R)) =
      (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := R)).toRingHom := by
    ext r
    rfl
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (C ⊗[S.A] R) q₁.primeCompl) (S.B ⊗[S.A] R) :=
    IsLocalization.tensorProduct_tensorProduct S.A R q₁.primeCompl S.B (by rwa [← hRHom])
  -- `𝔪_B` is the extension of the stage prime.
  have hmB : Ideal.map (algebraMap C S.B) q₁ = maximalIdeal S.B := by
    conv_lhs => rw [← IsLocalization.AtPrime.under_maximalIdeal S.B q₁]
    exact IsLocalization.map_under q₁.primeCompl S.B _
  -- The same comparison with the prime of `C ⊗[A] R` named, so that no dependent rewrite of a
  -- prime is needed at either use site.
  have htrans' : ∀ (q : Ideal (S.B ⊗[S.A] R)) (_ : q.IsPrime) (𝔭 : Ideal (C ⊗[S.A] R))
      (_ : 𝔭.IsPrime), q.comap (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)) = 𝔭 →
      (Module.Flat R (LocalizedModule q.primeCompl ((S.B ⊗[S.A] R) ⊗[S.B] S.M)) ↔
        Module.Flat R (LocalizedModule 𝔭.primeCompl ((C ⊗[S.A] R) ⊗[C] N))) := by
    rintro q hq _ _ rfl
    exact Module.flat_localizedModule_atPrime_comap_tensor_iff (R := S.A) (C := C) (S := S.B)
      (A := R) (N := N) (M := S.M) q₁.primeCompl g
      (IsLocalizedModule.isBaseChange q₁.primeCompl S.B g) q
  -- The closed-fibre ideal of `B ⊗[A] R` lies in `q` iff its two summands' preimages do.
  have hsum : ∀ q : Ideal (S.B ⊗[S.A] R),
      Ideal.map (Algebra.TensorProduct.includeRight (R := S.A) (A := S.B) (B := R)).toRingHom
          (maximalIdeal R) +
        Ideal.map (Algebra.TensorProduct.includeLeftRingHom (R := S.A) (A := S.B) (B := R))
          (maximalIdeal S.B) ≤ q ↔
        Ideal.map (algebraMap R (C ⊗[S.A] R)) (maximalIdeal R) ≤
            q.comap (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)) ∧
          Ideal.map (algebraMap C (C ⊗[S.A] R)) q₁ ≤
            q.comap (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)) := fun q ↦ by
    simp only [Submodule.add_eq_sup, sup_le_iff, ← Ideal.map_le_iff_le_comap, Ideal.map_map,
      hrightHom, hleftHom, ← hRHom, ← hLHom, ← hmB]
  constructor
  · intro h 𝔮 h𝔮 hmR hcomap
    obtain ⟨hle𝔮, hdisj⟩ := (comap_eq_iff_le_and_disjoint q₁ R 𝔮).mp hcomap
    have hqp : (Ideal.map (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)) 𝔮).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid (C ⊗[S.A] R) q₁.primeCompl) (S.B ⊗[S.A] R) 𝔮 h𝔮 hdisj
    have hqcomap :
        (Ideal.map (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)) 𝔮).comap
          (algebraMap (C ⊗[S.A] R) (S.B ⊗[S.A] R)) = 𝔮 :=
      IsLocalization.under_map_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid (C ⊗[S.A] R) q₁.primeCompl) (S.B ⊗[S.A] R) h𝔮 hdisj
    have hcont := (hsum _).mpr ⟨by rwa [hqcomap], by rwa [hqcomap]⟩
    exact (htrans' _ hqp 𝔮 h𝔮 hqcomap).mp (h _ hqp hcont)
  · intro h q hq hcont
    rw [hsum] at hcont
    obtain ⟨hc1, hc2⟩ := hcont
    obtain ⟨h𝔮, hdisj⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint
      (Algebra.algebraMapSubmonoid (C ⊗[S.A] R) q₁.primeCompl) (S.B ⊗[S.A] R) q).mp hq
    exact (htrans' q hq _ h𝔮 rfl).mpr (h _ h𝔮 hc1
      ((comap_eq_iff_le_and_disjoint q₁ R _).mpr ⟨hc2, hdisj⟩))

end Translation

end Module.FlatAtPointSituation

end
