module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiniteLocalDimension
public import StacksFrontier.RingTheory.Support.Basic
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of a module on a fibre

Let `R → S` be a ring map, let `M` be a finite `S`-module and let `r` be a prime of `R`. The
support of the fibre module `M ⊗_R κ(r)` over the fibre ring `κ(r) ⊗_R S` is the subject of
this file. Two descriptions of it are proved.

The first is a *dictionary*: `Spec(κ(r) ⊗_R S)` is the fibre of `Spec(S) → Spec(R)` over `r`,
by `PrimeSpectrum.preimageHomeomorphFiber`, and under that identification the support of the
fibre module is the part of `Supp_S(M)` lying over `r`. That part is `Module.fiberSupport`, and
the identification is `Module.fiberSupportHomeomorph`. The point of the dictionary is that the
fibre support is a subspace of `Spec(S)` and so can be compared along a map of `R`-algebras
without base changing the map; the price is that it is not closed, being an intersection of a
closed set with a fibre.

The second is the behaviour of the fibre support along an *integral* extension `B → A` of
`R`-algebras: at a prime of `B` over which there is exactly one prime of `A`, the fibre support
upstairs and the fibre support downstairs have the same local dimension. This is
`Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`, the fibre-by-fibre form of
`Module.topologicalKrullDimAt_support_eq_of_isIntegral`.

## Main definitions

* `Module.fiberSupport R S M r` is the part of `Supp_S(M)` lying over the prime `r` of `R`.
* `Module.fiberSupportHomeomorph` identifies the support of the fibre module over the fibre
  ring with `Module.fiberSupport`.

## Main results

* `Module.support_tensorProduct_eq_preimage_comap`: the support of `S ⊗_R M` for a finite
  `R`-module `M` is the inverse image of `Supp_R(M)`.
* `Module.image_comap_support_fiber`: **the support of the fibre module, pushed into `Spec(S)`,
  is the part of the support of `M` lying over `r`.**
* `Module.topologicalKrullDimAt_support_fiber`: the local dimension of the support of the fibre
  module at a prime of the fibre ring is the local dimension of `Module.fiberSupport` at the
  corresponding prime of `S`.
* `Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`: **the local dimension of the
  fibre support is unchanged by an integral extension at a prime with a unique prime above
  it.**

## Implementation notes

The `S`-algebra structure on the fibre ring `κ(r) ⊗_R S` is `Algebra.TensorProduct.rightAlgebra`,
made a local instance here. It is not a global instance — the action of `S` on `S ⊗_R S` would
be ambiguous — and it is the structure in which `Module.DevissageStageData.Pointed` records the
conditions of Stacks 05HZ that mention the fibre module, so the statements below are directly
applicable there.

The map `Spec(κ(r) ⊗_R S) → Spec(S)` used throughout is contraction along
`algebraMap S (κ(r) ⊗_R S)`, which is `Algebra.TensorProduct.includeRight`. That it is a
topological embedding with image the fibre is read off `PrimeSpectrum.preimageHomeomorphFiber`,
whose inverse is that contraction by `rfl`.

`IsClosedMap.restrictOfIsClosedOfPreimage` takes the subset of the source as a set `U'`
together with an equation `U' = f ⁻¹' U` rather than as the inverse image itself: the set a
consumer has in hand is the fibre of a *composite* map, equal to but not syntactically the
inverse image of the fibre downstairs.

## References

* [Stacks Project, Tag 00L1](https://stacks.math.columbia.edu/tag/00L1)
* [Stacks Project, Tag 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
-/

@[expose] public section

open TensorProduct TopologicalSpace

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A closed map restricts to a closed map from the part of a closed subset `T` of its source
lying over a subset `U` of its target, into any subset `V ⊆ U` of the target containing the
image of that part.

The subset of the source is given as a set `U'` together with the equation identifying it with
`f ⁻¹' U`, so that a consumer whose set is the fibre of a composite map need not transport
along that equation. -/
public theorem IsClosedMap.restrictOfIsClosedOfPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsClosedMap f) {T : Set X} (hT : IsClosed T)
    {U V : Set Y} {U' : Set X} (hU' : U' = f ⁻¹' U) (hV : V ⊆ U)
    (hmaps : ∀ x ∈ T ∩ U', f x ∈ V) :
    IsClosedMap (fun z : ↥(T ∩ U') ↦ (⟨f z.1, hmaps z.1 z.2⟩ : ↥V)) := by
  intro C hC
  obtain ⟨C₀, hC₀, hCeq⟩ := isClosed_induced_iff.mp hC
  rw [isClosed_induced_iff]
  refine ⟨f '' (C₀ ∩ T), hf _ (hC₀.inter hT), ?_⟩
  ext w
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨z, ⟨hzC₀, hzT⟩, hzw⟩
    have hzU' : z ∈ U' := by rw [hU', Set.mem_preimage, hzw]; exact hV w.2
    refine ⟨⟨z, hzT, hzU'⟩, ?_, Subtype.ext hzw⟩
    rw [← hCeq]
    exact hzC₀
  · rintro ⟨z, hzC, rfl⟩
    exact ⟨z.1, ⟨by rw [← hCeq] at hzC; exact hzC, z.2.1⟩, rfl⟩

/-- **Stacks 0BUR for the tensor model of a base change.** The support of `S ⊗_R M` for a
finite `R`-module `M` is the inverse image of `Supp_R(M)` under `Spec(S) → Spec(R)`. -/
public theorem Module.support_tensorProduct_eq_preimage_comap {R S M : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.support S (TensorProduct R S M) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' Module.support R M :=
  (IsBaseChange.of_equiv (LinearEquiv.refl S (TensorProduct R S M))
    (f := TensorProduct.mk R S M 1) (fun _ => rfl)).support_eq_preimage_comap

namespace PrimeSpectrum

section Fiber

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Contraction along `S → κ(r) ⊗_R S` is a topological embedding: it is the inverse of the
homeomorphism `PrimeSpectrum.preimageHomeomorphFiber` followed by the inclusion of the fibre. -/
@[ega "I 1.2.4" "φ, special case"]
public theorem isEmbedding_comap_algebraMap_fiber (r : Ideal R) [r.IsPrime] :
    Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap S (r.Fiber S))) :=
  Topology.IsEmbedding.subtypeVal.comp
    (PrimeSpectrum.preimageHomeomorphFiber R S ⟨r, ‹_›⟩).symm.isEmbedding

/-- The image of `Spec(κ(r) ⊗_R S)` in `Spec(S)` is the fibre of `Spec(S) → Spec(R)` over
`r`. -/
public theorem range_comap_algebraMap_fiber (r : Ideal R) [r.IsPrime] :
    Set.range (PrimeSpectrum.comap (algebraMap S (r.Fiber S))) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨r, ‹_›⟩ : PrimeSpectrum R)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ((PrimeSpectrum.preimageHomeomorphFiber R S ⟨r, ‹_›⟩).symm q).2
  · intro hp
    exact ⟨PrimeSpectrum.preimageHomeomorphFiber R S ⟨r, ‹_›⟩ ⟨p, hp⟩,
      congrArg Subtype.val ((PrimeSpectrum.preimageHomeomorphFiber R S
        ⟨r, ‹_›⟩).symm_apply_apply ⟨p, hp⟩)⟩

/-- The prime of the fibre ring attached to a prime of `S` over `r` contracts back to that
prime. -/
public theorem comap_primesOverOrderIsoFiber (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (r : Ideal R) [r.IsPrime] (q : Ideal S) [q.IsPrime] (hover : q.LiesOver r) :
    PrimeSpectrum.comap (algebraMap S (r.Fiber S))
        (PrimeSpectrum.primesOverOrderIsoFiber R S r ⟨q, ‹_›, hover⟩) =
      (⟨q, ‹_›⟩ : PrimeSpectrum S) := by
  refine PrimeSpectrum.ext ?_
  have h := congrArg (fun z : r.primesOver S => (z : Ideal S))
    ((PrimeSpectrum.primesOverOrderIsoFiber R S r).symm_apply_apply ⟨q, ‹_›, hover⟩)
  rwa [PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply] at h

end Fiber

section Tower

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
  [Algebra B A] [IsScalarTower R B A]

/-- Contracting a prime of `A` to `B` and then to `R` contracts it to `R`. -/
public theorem comap_comap_algebraMap (z : PrimeSpectrum A) :
    PrimeSpectrum.comap (algebraMap R B) (PrimeSpectrum.comap (algebraMap B A) z) =
      PrimeSpectrum.comap (algebraMap R A) z := by
  rw [IsScalarTower.algebraMap_eq R B A, PrimeSpectrum.comap_comp]
  rfl

/-- The fibre of `Spec(A) → Spec(R)` over a prime is the inverse image, along
`Spec(A) → Spec(B)`, of the fibre of `Spec(B) → Spec(R)` over that prime. -/
public theorem preimage_comap_algebraMap_eq (p : PrimeSpectrum R) :
    PrimeSpectrum.comap (algebraMap R A) ⁻¹' {p} =
      PrimeSpectrum.comap (algebraMap B A) ⁻¹'
        (PrimeSpectrum.comap (algebraMap R B) ⁻¹' {p}) := by
  rw [← Set.preimage_comp, ← PrimeSpectrum.comap_comp, ← IsScalarTower.algebraMap_eq]

end Tower

end PrimeSpectrum

namespace Module

section Fiber

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (M : Type*) [AddCommGroup M] [Module S M] (r : Ideal R) [r.IsPrime]

/-- The support of `M` on the fibre over `r`: the primes of `S` in the support of `M` that lie
over `r`. It is the part of `Supp_S(M)` that the support of the fibre module
`M ⊗_R κ(r)` describes, by `Module.image_comap_support_fiber`. -/
public def fiberSupport : Set (PrimeSpectrum S) :=
  Module.support S M ∩
    PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨r, ‹_›⟩ : PrimeSpectrum R)}

/-- Membership in the fibre support, spelled out. -/
public theorem mem_fiberSupport_iff (q : PrimeSpectrum S) :
    q ∈ Module.fiberSupport R S M r ↔
      q ∈ Module.support S M ∧ q.asIdeal.comap (algebraMap R S) = r :=
  Iff.and Iff.rfl ⟨fun h => congrArg PrimeSpectrum.asIdeal h, fun h => PrimeSpectrum.ext h⟩

/-- The fibre module of a finite module is finite over the fibre ring. -/
public theorem finite_tensorProduct_fiber [Module.Finite S M] :
    Module.Finite (r.Fiber S) (TensorProduct S (r.Fiber S) M) :=
  Module.Finite.base_change S (r.Fiber S) M

/-- **The support of the fibre module, pushed into `Spec(S)`, is the part of the support of `M`
lying over `r`.** This is the dictionary between the two descriptions of the fibre support: as
a closed subset of the spectrum of the fibre ring, and as a subspace of `Spec(S)`. -/
public theorem image_comap_support_fiber [Module.Finite S M] :
    PrimeSpectrum.comap (algebraMap S (r.Fiber S)) ''
        Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M) =
      Module.fiberSupport R S M r := by
  rw [Module.support_tensorProduct_eq_preimage_comap, Set.image_preimage_eq_inter_range,
    PrimeSpectrum.range_comap_algebraMap_fiber]
  rfl

/-- A prime of the fibre ring in the support of the fibre module contracts into the fibre
support. -/
public theorem comap_mem_fiberSupport [Module.Finite S M] {Q : PrimeSpectrum (r.Fiber S)}
    (hQ : Q ∈ Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M)) :
    PrimeSpectrum.comap (algebraMap S (r.Fiber S)) Q ∈ Module.fiberSupport R S M r :=
  Module.image_comap_support_fiber R S M r ▸ Set.mem_image_of_mem _ hQ

/-- **The prime of the fibre ring attached to a prime `q` of `S` over `r` lies in the support of
the fibre module exactly when `q` lies in the support of `M`.** -/
public theorem primesOverOrderIsoFiber_mem_support_iff [Module.Finite S M] (q : Ideal S)
    [q.IsPrime] (hover : q.LiesOver r) :
    (PrimeSpectrum.primesOverOrderIsoFiber R S r ⟨q, ‹_›, hover⟩) ∈
        Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M) ↔
      (⟨q, ‹_›⟩ : PrimeSpectrum S) ∈ Module.support S M := by
  rw [Module.support_tensorProduct_eq_preimage_comap, Set.mem_preimage,
    PrimeSpectrum.comap_primesOverOrderIsoFiber R S r q hover]

/-- The support of the fibre module over the fibre ring is homeomorphic to the part of the
support of `M` lying over `r`. -/
public noncomputable def fiberSupportHomeomorph [Module.Finite S M] :
    ↥(Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M)) ≃ₜ
      ↥(Module.fiberSupport R S M r) :=
  ((PrimeSpectrum.isEmbedding_comap_algebraMap_fiber (S := S) r).homeomorphImage
      (Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M))).trans
    (Homeomorph.setCongr (Module.image_comap_support_fiber R S M r))

/-- The local dimension of the support of the fibre module at a prime of the fibre ring is the
local dimension of the fibre support at the corresponding prime of `S`. -/
public theorem topologicalKrullDimAt_support_fiber [Module.Finite S M]
    {Q : PrimeSpectrum (r.Fiber S)}
    (hQ : Q ∈ Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M)) :
    topologicalKrullDimAt
        ↥(Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M)) ⟨Q, hQ⟩ =
      topologicalKrullDimAt ↥(Module.fiberSupport R S M r)
        ⟨PrimeSpectrum.comap (algebraMap S (r.Fiber S)) Q,
          Module.comap_mem_fiberSupport R S M r hQ⟩ := by
  refine (topologicalKrullDimAt_eq_of_homeomorph
    (Module.fiberSupportHomeomorph R S M r) ⟨Q, hQ⟩).trans ?_
  exact congrArg _ (Subtype.ext rfl)

/-- Isomorphic modules have the same fibre support. -/
public theorem fiberSupport_congr {N : Type*} [AddCommGroup N] [Module S N]
    (e : M ≃ₗ[S] N) : Module.fiberSupport R S M r = Module.fiberSupport R S N r := by
  unfold Module.fiberSupport
  rw [e.support_eq]

/-- The fibre support is quasi-sober: it is homeomorphic to a closed subset of the spectrum of
the fibre ring. -/
public instance quasiSober_fiberSupport [Module.Finite S M] :
    QuasiSober ↥(Module.fiberSupport R S M r) := by
  have := Module.finite_tensorProduct_fiber R S M r
  have : QuasiSober ↥(Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) M)) :=
    (Module.isClosed_support (R := r.Fiber S)
      (M := TensorProduct S (r.Fiber S) M)).isClosedEmbedding_subtypeVal.quasiSober
  exact (Module.fiberSupportHomeomorph R S M r).symm.isOpenEmbedding.quasiSober

end Fiber

section Tower

variable {R B A M : Type*} [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]

/-- The contraction to `B` of the annihilator of `M` over `A` lies in every prime of `B` in the
support of `M`. -/
private theorem comap_annihilator_le_of_mem_support [Module.Finite B M] [Module.Finite A M]
    {w : PrimeSpectrum B} (hw : w ∈ Module.support B M) :
    (Module.annihilator A M).comap (algebraMap B A) ≤ w.asIdeal := by
  rw [← Module.annihilator_eq_comap_annihilator (S := A) (M := M)]
  exact Module.mem_support_iff_of_finite.mp hw

/-- A prime in the fibre support of `M` over `A` contracts into the fibre support of `M` over
`B`. -/
public theorem comap_mem_fiberSupport_of_mem [Module.Finite B M] [Module.Finite A M]
    (r : Ideal R) [r.IsPrime] {z : PrimeSpectrum A} (hz : z ∈ Module.fiberSupport R A M r) :
    PrimeSpectrum.comap (algebraMap B A) z ∈ Module.fiberSupport R B M r :=
  ⟨Module.comap_mem_support hz.1, (PrimeSpectrum.comap_comap_algebraMap z).trans hz.2⟩

/-- Along a *surjective* algebra map, a prime of `A` whose contraction to `B` is in the support
of `M` over `B` is itself in the support of `M` over `A`: the annihilators correspond, and
contraction along a surjection reflects inclusions of ideals. -/
public theorem mem_support_of_comap_mem_support_of_surjective [Module.Finite B M]
    [Module.Finite A M] (hsurj : Function.Surjective (algebraMap B A)) {z : PrimeSpectrum A}
    (hz : PrimeSpectrum.comap (algebraMap B A) z ∈ Module.support B M) :
    z ∈ Module.support A M := by
  exact Module.mem_support_iff_of_finite.mpr
    ((Ideal.comap_le_comap_iff_of_surjective _ hsurj _ _).1
      (Module.comap_annihilator_le_of_mem_support hz))

/-- Along a surjective algebra map, a prime of `A` whose contraction to `B` is in the fibre
support of `M` over `B` is itself in the fibre support of `M` over `A`. -/
public theorem mem_fiberSupport_of_comap_mem_fiberSupport_of_surjective [Module.Finite B M]
    [Module.Finite A M] (hsurj : Function.Surjective (algebraMap B A)) (r : Ideal R)
    [r.IsPrime] {z : PrimeSpectrum A}
    (hz : PrimeSpectrum.comap (algebraMap B A) z ∈ Module.fiberSupport R B M r) :
    z ∈ Module.fiberSupport R A M r :=
  ⟨Module.mem_support_of_comap_mem_support_of_surjective hsurj hz.1,
    (PrimeSpectrum.comap_comap_algebraMap (B := B) z).symm.trans hz.2⟩

/-- **The local dimension of the fibre support is unchanged by an integral extension at a prime
with a unique prime above it.**

Let `R → B → A` be ring maps with `B → A` integral, let `M` be a module finite over both `B`
and `A`, let `r` be a prime of `R`, let `q` be a prime of `B` over `r` in the support of `M`
and let `p` be the *only* prime of `A` contracting to `q`. Then the part of `Supp_A(M)` lying
over `r` has at `p` the local Krull dimension that the part of `Supp_B(M)` lying over `r` has
at `q`.

This is `Module.topologicalKrullDimAt_support_eq_of_isIntegral` read fibre by fibre. The fibre
support is not closed in the spectrum, so the closedness of contraction along an integral map
is restricted to it by `IsClosedMap.restrictOfIsClosedOfPreimage` rather than by
`IsClosedMap.restrictOfIsClosed`; soberness, which for the whole support comes from its being
closed, comes here from `Module.quasiSober_fiberSupport`. -/
public theorem topologicalKrullDimAt_fiberSupport_eq_of_isIntegral [Module.Finite B M]
    [Module.Finite A M] [Algebra.IsIntegral B A] (r : Ideal R) [r.IsPrime]
    {p : PrimeSpectrum A} {q : PrimeSpectrum B}
    (hpq : PrimeSpectrum.comap (algebraMap B A) p = q)
    (huniq : ∀ p' : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap B A) p' = q → p' = p)
    (hp : p ∈ Module.fiberSupport R A M r) (hq : q ∈ Module.fiberSupport R B M r) :
    topologicalKrullDimAt ↥(Module.fiberSupport R A M r) ⟨p, hp⟩ =
      topologicalKrullDimAt ↥(Module.fiberSupport R B M r) ⟨q, hq⟩ := by
  subst hpq
  have hintegral : (algebraMap B A).IsIntegral := fun a => Algebra.IsIntegral.isIntegral a
  have hQA : QuasiSober ↥(Module.fiberSupport R A M r) := inferInstance
  have hQB : QuasiSober ↥(Module.fiberSupport R B M r) := inferInstance
  refine @Topology.topologicalKrullDimAt_eq_of_isClosedMap_of_specializes_injective
    ↥(Module.fiberSupport R A M r) ↥(Module.fiberSupport R B M r) _ _ hQA hQB _ _
    (fun z : ↥(Module.fiberSupport R A M r) =>
      (⟨PrimeSpectrum.comap (algebraMap B A) z.1,
        Module.comap_mem_fiberSupport_of_mem r z.2⟩ : ↥(Module.fiberSupport R B M r)))
    (continuous_induced_rng.mpr
      ((PrimeSpectrum.continuous_comap (algebraMap B A)).comp continuous_subtype_val))
    (IsClosedMap.restrictOfIsClosedOfPreimage
      (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap B A) hintegral)
      (Module.isClosed_support (R := A) (M := M))
      (PrimeSpectrum.preimage_comap_algebraMap_eq (B := B) (⟨r, ‹_›⟩ : PrimeSpectrum R))
      Set.inter_subset_right (fun z hz => Module.comap_mem_fiberSupport_of_mem r hz))
    (fun w => ?_) (fun z w hzw hEq => ?_) ⟨p, hp⟩ ?_
  · -- Going up: every prime of the fibre support downstairs is the contraction of one upstairs.
    have hann := Module.comap_annihilator_le_of_mem_support (A := A) w.2.1
    have hwp : w.1.asIdeal.IsPrime := w.1.isPrime
    obtain ⟨P, hPge, hPprime, hPcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral w.1.asIdeal (Module.annihilator A M) hann
    have hw1 : PrimeSpectrum.comap (algebraMap B A) (⟨P, hPprime⟩ : PrimeSpectrum A) = w.1 :=
      PrimeSpectrum.ext hPcomap
    have hmemP : (⟨P, hPprime⟩ : PrimeSpectrum A) ∈ Module.fiberSupport R A M r :=
      ⟨Module.mem_support_iff_of_finite.mpr hPge,
        (PrimeSpectrum.comap_comap_algebraMap (B := B) _).symm.trans (hw1 ▸ w.2.2)⟩
    exact ⟨⟨⟨P, hPprime⟩, hmemP⟩, Subtype.ext hw1⟩
  · -- Contraction along an integral map is strictly monotone on primes.
    have hle : z.1 ≤ w.1 := (PrimeSpectrum.le_iff_specializes z.1 w.1).mpr
      ((subtype_specializes_iff z w).mp hzw)
    rcases eq_or_lt_of_le hle with h | hlt
    · exact Subtype.ext h
    · have hzp : z.1.asIdeal.IsPrime := z.1.isPrime
      exact absurd (congrArg (fun v : ↥(Module.fiberSupport R B M r) => v.1.asIdeal) hEq)
        (Ideal.IsIntegral.comap_lt_comap (R := B)
          ((PrimeSpectrum.asIdeal_lt_asIdeal z.1 w.1).mpr hlt)).ne
  · -- The fibre of the contraction over `q` is the single prime `p`.
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => Subtype.ext (huniq z.1
        (congrArg (fun v : ↥(Module.fiberSupport R B M r) => v.1) h)),
      fun h => by rw [h]⟩

end Tower

end Module

end
