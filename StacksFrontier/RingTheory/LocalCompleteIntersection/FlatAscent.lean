module

public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteIntersection.FieldGlobalToRingMap
public import StacksFrontier.RingTheory.EssFiniteType.TensorLocalization
public import StacksFrontier.RingTheory.Flat.NormalFibres
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatDescent
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Localization
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local complete intersections ascend along flat maps with complete intersection fibres

Let `R → S` be a flat map of Noetherian rings. If `R` is a local complete intersection and every
localization at a prime of every fibre ring `κ(𝔭) ⊗_R S` is a complete intersection, then `S` is
a local complete intersection. Consequently a syntomic algebra over a local complete intersection
ring is a local complete intersection ring, and a Noetherian algebra over a field which is a local
complete intersection stays one after base change along a finitely generated extension of the
ground field.

## Main results

* `LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_ringEquiv`: the condition
  transports along an isomorphism of Noetherian rings.
* `LocalCompleteIntersection.isCompleteIntersectionRing_of_isRegularLocalRing` and
  `LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_isRegularRing`: a regular local
  ring is a complete intersection and a regular ring is a local complete intersection.
* `LocalCompleteIntersection.isCompleteIntersectionRing_of_isLocalCompleteIntersectionRing`: a
  Noetherian local ring which is a local complete intersection ring is a complete intersection.
* `LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_isLocalization`: the condition
  passes to localizations.
* `LocalCompleteIntersection.isLocalCompleteIntersectionRing_iff_forall_localization`: it is
  detected by the localizations at the primes.
* `LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_flat_of_fiber`: the flat ascent.
* `LocalCompleteIntersection.isLocalCompleteIntersectionRing_of_syntomic`: its syntomic case.
* `LocalCompleteIntersection.isLocalCompleteIntersectionRing_tensorProduct_of_essFiniteType`:
  stability under a finitely generated extension of the ground field.

## References

* [Stacks Project, Tag 09Q7](https://stacks.math.columbia.edu/tag/09Q7)
* [Stacks Project, Tag 0339](https://stacks.math.columbia.edu/tag/0339)
* [Stacks Project, Tag 0AGX](https://stacks.math.columbia.edu/tag/0AGX)
* [Stacks Project, Tag 00SW](https://stacks.math.columbia.edu/tag/00SW)
* [Stacks Project, Tag 07BV](https://stacks.math.columbia.edu/tag/07BV)
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

open scoped TensorProduct

universe u

namespace LocalCompleteIntersection

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A regular local ring is a complete intersection. -/
@[ega "IV 19.3.1"]
theorem isCompleteIntersectionRing_of_isRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] : IsCompleteIntersectionRing A := by
  let C := AdicCompletion (maximalIdeal A) A
  let : IsRegularLocalRing C :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp inferInstance
  refine ⟨C, inferInstance, inferInstance, RingHom.id C, Function.surjective_id,
    isLocalHom_id C, [], IsRegular.nil C C, ?_⟩
  simp only [Ideal.ofList_nil]
  exact ((RingHom.injective_iff_ker_eq_bot (RingHom.id C)).mp fun _ _ h => h).symm

/-- A regular ring is a local complete intersection. -/
@[ega "IV 19.3.1" "more general"]
theorem isLocalCompleteIntersectionRing_of_isRegularRing (A : Type u) [CommRing A]
    [IsRegularRing A] : IsLocalCompleteIntersectionRing A := by
  intro p hp
  exact isCompleteIntersectionRing_of_isRegularLocalRing (Localization.AtPrime p)

/-- A Noetherian local ring which is a local complete intersection ring is a complete
intersection. -/
theorem isCompleteIntersectionRing_of_isLocalCompleteIntersectionRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (h : IsLocalCompleteIntersectionRing A) :
    IsCompleteIntersectionRing A := by
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl (fun x ↦ by simpa using! fun a ↦ a)
  exact isCompleteIntersectionRing_of_ringEquiv e.toRingEquiv.symm (h (maximalIdeal A))

/-- Being a local complete intersection transports along an isomorphism of Noetherian rings. -/
theorem isLocalCompleteIntersectionRing_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] (e : A ≃+* B)
    (hA : IsLocalCompleteIntersectionRing A) :
    letI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
    IsLocalCompleteIntersectionRing B := by
  let : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
  intro q hq
  exact isCompleteIntersectionRing_of_ringEquiv
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (q.comap e))
      (Localization.AtPrime q) e (e.map_primeCompl_comap_eq q))
    (hA (q.comap e))

/-- A localization of a local complete intersection ring is a local complete intersection ring. -/
theorem isLocalCompleteIntersectionRing_of_isLocalization {A : Type u} [CommRing A]
    [IsNoetherianRing A] (hA : IsLocalCompleteIntersectionRing A) (M : Submonoid A)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization M B] :
    letI : IsNoetherianRing B := IsLocalization.isNoetherianRing M B inferInstance
    IsLocalCompleteIntersectionRing B := by
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing M B inferInstance
  intro q hq
  let : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap A B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q
  exact isCompleteIntersectionRing_of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap A B)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q)).toRingEquiv
    (hA (q.comap (algebraMap A B)))

/-- Being a local complete intersection is detected by the localizations at the primes. -/
theorem isLocalCompleteIntersectionRing_iff_forall_localization (A : Type u) [CommRing A]
    [IsNoetherianRing A] :
    (∀ p : PrimeSpectrum A,
        IsLocalCompleteIntersectionRing (Localization.AtPrime p.asIdeal)) ↔
      IsLocalCompleteIntersectionRing A := by
  refine ⟨fun h p hp => ?_, fun h p => ?_⟩
  · exact isCompleteIntersectionRing_of_isLocalCompleteIntersectionRing
      (Localization.AtPrime p) (h ⟨p, hp⟩)
  · exact isLocalCompleteIntersectionRing_of_isLocalization h p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)

/-- Local complete intersections ascend along a flat map with complete intersection fibres: if
`R → S` is a flat map of Noetherian rings, `R` is a local complete intersection and every
localization of every fibre ring `κ(𝔭) ⊗_R S` at a prime is a complete intersection, then `S` is
a local complete intersection. -/
@[ega "IV 19.3.10" "partial"]
theorem isLocalCompleteIntersectionRing_of_flat_of_fiber {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsLocalCompleteIntersectionRing R)
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      letI : IsNoetherianRing (p.Fiber S) :=
        Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p
      IsLocalCompleteIntersectionRing (p.Fiber S)) :
    IsLocalCompleteIntersectionRing S := by
  intro q hq
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  let : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have hflatRq : Module.Flat R (Localization.AtPrime q) :=
    Module.Flat.trans R S (Localization.AtPrime q)
  have : Module.Flat (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R))
      (q.under R).primeCompl _).mpr hflatRq
  set Q : Ideal ((q.under R).Fiber S) :=
    ((PrimeSpectrum.primesOverOrderIsoFiber R S (q.under R))
      ⟨q, inferInstance, inferInstance⟩).asIdeal with hQdef
  have : Q.IsPrime := inferInstance
  have hrq : Q.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] (q.under R).Fiber S) = q := by
    rw [hQdef, ← PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply, OrderIso.symm_apply_apply]
  have hIeq : (maximalIdeal (Localization.AtPrime (q.under R))).map
      (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) =
      ((q.under R).map (algebraMap R S)).map (algebraMap S (Localization.AtPrime q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : Nontrivial (Localization.AtPrime q ⧸
      (maximalIdeal (Localization.AtPrime (q.under R))).map
        (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top _).ne
  have : IsLocalRing (Localization.AtPrime q ⧸
      (maximalIdeal (Localization.AtPrime (q.under R))).map
        (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  let : IsNoetherianRing ((q.under R).Fiber S) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber (q.under R)
  let : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  obtain ⟨E⟩ := Stacks.Flatness.NormalFibreAscent.nonempty_ringEquiv_localization_fiber
    (q.under R) Q q hrq
  exact (isCompleteIntersectionRing_iff_of_flat (Localization.AtPrime (q.under R))
    (Localization.AtPrime q)).mpr ⟨hR (q.under R), isCompleteIntersectionRing_of_ringEquiv
      (E.trans (Ideal.quotEquivOfEq hIeq).symm) (hfib (q.under R) Q)⟩

/-- A syntomic algebra over a local complete intersection ring is a local complete intersection
ring. -/
@[ega "IV 19.3.10" "affine case"]
theorem isLocalCompleteIntersectionRing_of_syntomic (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.Syntomic R S]
    (hR : IsLocalCompleteIntersectionRing R) :
    letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
    IsLocalCompleteIntersectionRing S := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine isLocalCompleteIntersectionRing_of_flat_of_fiber hR fun p _ => ?_
  let : IsNoetherianRing (p.Fiber S) :=
    Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p
  exact (isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing p.ResidueField
    (p.Fiber S)).mp (Algebra.Syntomic.isLocalCompleteIntersection_fiber p)

/-- A local complete intersection over a field stays one after a finitely generated extension of
the ground field: if `k` is a field, `R` a Noetherian `k`-algebra which is a local complete
intersection and `K/k` a field extension which is finitely generated as a field extension, then
`R ⊗_k K` is a local complete intersection. -/
theorem isLocalCompleteIntersectionRing_tensorProduct_of_essFiniteType
    (k R K : Type u) [Field k] [CommRing R] [Field K] [Algebra k R] [Algebra k K]
    [IsNoetherianRing R] [Algebra.EssFiniteType k K]
    (hR : IsLocalCompleteIntersectionRing R) :
    letI : IsNoetherianRing (R ⊗[k] K) :=
      Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
    IsLocalCompleteIntersectionRing (R ⊗[k] K) := by
  let : IsNoetherianRing (R ⊗[k] K) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
  obtain ⟨C, M, _, hC, _, _⟩ :=
    Stacks.EssFiniteType.exists_isGlobalCompleteIntersectionOver_isLocalization_tensorProduct
      k K R
  have : Algebra.IsRelativeGlobalCompleteIntersection k C :=
    Algebra.IsRelativeGlobalCompleteIntersection.of_isGlobalCompleteIntersectionOver k C hC
  have : Algebra.IsRelativeGlobalCompleteIntersection R (R ⊗[k] C) :=
    Algebra.IsRelativeGlobalCompleteIntersection.baseChange k C R (R ⊗[k] C)
  have : Algebra.Syntomic R (R ⊗[k] C) :=
    Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection R (R ⊗[k] C)
  have : IsNoetherianRing (R ⊗[k] C) := Algebra.FiniteType.isNoetherianRing R (R ⊗[k] C)
  exact isLocalCompleteIntersectionRing_of_isLocalization
    (isLocalCompleteIntersectionRing_of_syntomic R (R ⊗[k] C) hR)
    (Algebra.algebraMapSubmonoid (R ⊗[k] C) M) (R ⊗[k] K)

end LocalCompleteIntersection

end
