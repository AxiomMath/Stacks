module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RelativeDimension.Defs

/-!
# The affine fibre dictionary

The scheme-theoretic fibre of `Spec B ⟶ Spec A` over a prime `𝔭` of `A` is `Spec (κ(𝔭) ⊗[A] B)`.
This identification is recorded here as a homeomorphism, together with two consequences: the
dimension of the fibre is the Krull dimension of the fibre ring, and the part of the fibre lying
in a subset of `Spec B` is the preimage of that subset along `B → κ(𝔭) ⊗[A] B`. The dimension of
the fibre *at a point* is `Algebra.relativeDimensionAt`.

## Main definitions

* `AlgebraicGeometry.fiberSpecHomeo` is the homeomorphism from the scheme-theoretic fibre of
  `Spec B ⟶ Spec A` over a prime `𝔭` of `A` to `Spec (κ(𝔭) ⊗[A] B)`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_fiber_specMap_eq`: the dimension of the fibre of
  `Spec B ⟶ Spec A` over `𝔭` is `ringKrullDim (κ(𝔭) ⊗[A] B)`.
* `AlgebraicGeometry.topologicalKrullDim_fiber_specMap_genericPoint_eq`: for `A` a domain, the
  dimension of the generic fibre is `ringKrullDim (K ⊗[A] B)`, where `K = κ(⊥)` is a fraction
  field of `A`.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_specMap_eq`: the local form, equal to
  `Algebra.relativeDimensionAt`.
* `AlgebraicGeometry.fiberι_eq_comap_fiberSpecHomeo`: the image in `Spec B` of a point of the
  fibre is the contraction of the prime of the fibre ring naming it.
* `AlgebraicGeometry.fiberSpecHomeo_image_preimage`: the homeomorphism carries the part of the
  fibre lying in a subset `W` of `Spec B` onto the preimage of `W` along `B → κ(𝔭) ⊗[A] B`.
* `PrimeSpectrum.exists_comap_eq_iff_comap_algebraMap_eq`: the primes of `κ(𝔭) ⊗[A] B` contract
  along `B → κ(𝔭) ⊗[A] B` exactly onto the primes of `B` lying over `𝔭`.

## Implementation notes

The algebra structure of `κ(𝔭) ⊗[A] B` over `B` is Mathlib's
`Algebra.TensorProduct.rightAlgebra`, which is not a global instance; it is a local instance in
this file.

## References

* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
* [Stacks Project, Tag 00QD](https://stacks.math.columbia.edu/tag/00QD)
-/

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace PrimeSpectrum

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A)

/-- The prime of `B` underlying `(PrimeSpectrum.preimageHomeomorphFiber A B 𝔭).symm q` is the
contraction of `q` along `B → κ(𝔭) ⊗[A] B`. -/
public theorem preimageHomeomorphFiber_symm_apply_coe (q : PrimeSpectrum (p.asIdeal.Fiber B)) :
    ((preimageHomeomorphFiber A B p).symm q : PrimeSpectrum B) =
      comap (algebraMap B (p.asIdeal.Fiber B)) q :=
  rfl

/-- A prime of `B` is the contraction of a prime of the fibre ring `κ(𝔭) ⊗[A] B` exactly when it
lies over `𝔭`. -/
public theorem exists_comap_eq_iff_comap_algebraMap_eq (𝔮 : PrimeSpectrum B) :
    (∃ q : PrimeSpectrum (p.asIdeal.Fiber B),
        comap (algebraMap B (p.asIdeal.Fiber B)) q = 𝔮) ↔
      comap (algebraMap A B) 𝔮 = p := by
  refine ⟨?_, fun h => ⟨preimageHomeomorphFiber A B p ⟨𝔮, h⟩, ?_⟩⟩
  · rintro ⟨q, rfl⟩
    exact ((preimageHomeomorphFiber A B p).symm q).2
  · rw [← preimageHomeomorphFiber_symm_apply_coe, Homeomorph.symm_apply_apply]

end PrimeSpectrum

namespace AlgebraicGeometry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (p : PrimeSpectrum A)

/-- **The affine fibre.** The scheme-theoretic fibre of `Spec B ⟶ Spec A` over a prime `𝔭` of `A`
is homeomorphic to `Spec (κ(𝔭) ⊗[A] B)`. -/
public noncomputable def fiberSpecHomeo :
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber p ≃ₜ
      PrimeSpectrum (p.asIdeal.Fiber B) :=
  ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberHomeo p).trans
    (PrimeSpectrum.preimageHomeomorphFiber A B p)

/-- The image in `Spec B` of a point of the fibre named by a prime `q` of the fibre ring is the
contraction of `q` along `B → κ(𝔭) ⊗[A] B`. -/
public theorem fiberι_fiberSpecHomeo_symm (q : PrimeSpectrum (p.asIdeal.Fiber B)) :
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ((fiberSpecHomeo A B p).symm q) =
      PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) q :=
  (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι_fiberHomeo_symm p _

/-- The image in `Spec B` of a point of the fibre is the contraction, along
`B → κ(𝔭) ⊗[A] B`, of the prime of the fibre ring naming it. -/
public theorem fiberι_eq_comap_fiberSpecHomeo
    (x : (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber p) :
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p x =
      PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) (fiberSpecHomeo A B p x) :=
  (congrArg ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p)
      ((fiberSpecHomeo A B p).symm_apply_apply x)).symm.trans
    (fiberι_fiberSpecHomeo_symm A B p (fiberSpecHomeo A B p x))

/-- The part of the fibre lying in a subset `W` of `Spec B` corresponds, under
`AlgebraicGeometry.fiberSpecHomeo`, to the preimage of `W` along `B → κ(𝔭) ⊗[A] B`. -/
public theorem fiberSpecHomeo_image_preimage (W : Set (PrimeSpectrum B)) :
    fiberSpecHomeo A B p ''
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ⁻¹' W) =
      PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) ⁻¹' W :=
  calc fiberSpecHomeo A B p ''
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ⁻¹' W)
      = (fiberSpecHomeo A B p).symm ⁻¹'
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ⁻¹' W) :=
        congrFun (Set.image_eq_preimage_of_inverse
          (fiberSpecHomeo A B p).symm_apply_apply (fiberSpecHomeo A B p).apply_symm_apply) _
    _ = ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι p ∘
          (fiberSpecHomeo A B p).symm) ⁻¹' W := (Set.preimage_comp ..).symm
    _ = PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) ⁻¹' W :=
        congrArg (· ⁻¹' W) (funext (fiberι_fiberSpecHomeo_symm A B p))

/-- **The dimension dictionary.** The dimension of the fibre of `Spec B ⟶ Spec A` over a prime
`𝔭` of `A` is the Krull dimension of the fibre ring `κ(𝔭) ⊗[A] B`. -/
public theorem topologicalKrullDim_fiber_specMap_eq :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber p)
      = ringKrullDim (p.asIdeal.Fiber B) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ (fiberSpecHomeo A B p).isHomeomorph

/-- The generic fibre of `Spec B ⟶ Spec A` for `A` a domain has dimension
`ringKrullDim (K ⊗[A] B)`, where `K = κ(⊥)` is a fraction field of `A`. -/
public theorem topologicalKrullDim_fiber_specMap_genericPoint_eq [IsDomain A] :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
        (genericPoint (Spec (.of A))))
      = ringKrullDim ((⊥ : Ideal A).Fiber B) := by
  have : IsDomain (CommRingCat.of A) := ‹IsDomain A›
  rw [genericPoint_eq_bot_of_affine (CommRingCat.of A)]
  exact topologicalKrullDim_fiber_specMap_eq A B ⊥

/-- The local form of the dimension dictionary: the dimension of the fibre of `Spec B ⟶ Spec A`
at a point `𝔮` of `Spec B` is the relative dimension of `B/A` at `𝔮`. -/
public theorem topologicalKrullDimAt_fiber_specMap_eq (q : PrimeSpectrum B) :
    topologicalKrullDimAt
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))) q))
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).asFiber q) =
      Algebra.relativeDimensionAt A q.asIdeal := by
  rw [topologicalKrullDimAt_eq_of_homeomorph
    ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberHomeo _) _]
  unfold Algebra.relativeDimensionAt
  congr 1
  exact Subtype.ext ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberι_asFiber q)

end AlgebraicGeometry

end
