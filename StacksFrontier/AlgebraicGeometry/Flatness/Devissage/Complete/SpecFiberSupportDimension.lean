module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.RingTheory.Support.Fiber
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# The fibre-support dimension of a dévissage stage, on a spectrum and on rings

Let `N` be a finite module over an `R`-algebra `S` and let `r` be a prime of `R`. Two dimensions
meet in the passage from an algebraic complete dévissage of `N/S/R` over `r` (Stacks 05HZ) to the
scheme-theoretic one of `Ñ/Spec S/Spec R` (Stacks 05H4): the dimension of the support of the
fibre of `Ñ` over the point `r` of `Spec R`, which is what the geometric notion constrains, and
the dimension of `Module.fiberSupport R S N r`, the part of `Supp_S(N)` lying over `r`, which is
what the algebraic one records. This file identifies them, and then follows the second through one
stage of a dévissage.

The identification is the affine fibre dictionary. The scheme-theoretic fibre of
`Spec S → Spec R` over `r` is `Spec(κ(r) ⊗_R S)`, by `AlgebraicGeometry.fiberSpecHomeo`; the
support of the pullback of `Ñ` to that fibre is the support of the fibre module over the fibre
ring, because the support of a pullback is the inverse image of the support
(`Stacks.Modules.supp_pullback`), the support of `Ñ` is `Supp_S(N)`
(`AlgebraicGeometry.supp_tilde`) and the support of a base change is the inverse image of the
support (`Module.support_tensorProduct_eq_preimage_comap`); and the support of the fibre module
over the fibre ring is `Module.fiberSupport R S N r`, by `Module.fiberSupportHomeomorph`. The
composite is `AlgebraicGeometry.suppPullbackFiberιTildeHomeomorph`, and a dimension is a
homeomorphism invariant.

A stage of a dévissage of `N/S/R` presents `N` as a finite module `M` over an `R`-algebra `A`
which is a quotient of `S`, and `A` as a finite algebra over a smooth `R`-algebra `B`. Neither
map moves the dimension of the fibre support: along the surjection `S → A` contraction is a
closed embedding carrying the fibre support of `M` over `A` onto the fibre support of `N` over
`S`, and along the finite map `B → A` contraction is a closed surjection between the two fibre
supports which is injective on specialisations. The fibre support over `B` finally sits inside
the whole fibre of `Spec B → Spec R`, whose dimension is the relative dimension of `R → B`.

## Main results

* `AlgebraicGeometry.mem_supp_pullback_fiberι_tilde_iff`: **a point of the fibre of
  `Spec S → Spec R` over `r` lies in the support of the fibre of `Ñ` exactly when its image in
  `Spec S` lies in `Supp_S(N)`.**
* `AlgebraicGeometry.topologicalKrullDim_supp_pullback_fiberι_tilde` and
  `AlgebraicGeometry.topologicalKrullDimAt_supp_pullback_fiberι_tilde`: **the dimension, and the
  local dimension at the point named by a prime `q` of `S` over `r`, of the support of the fibre
  of `Ñ` are those of `Module.fiberSupport R S N r`.**
* `AlgebraicGeometry.specFiberPoint` and `AlgebraicGeometry.fiberι_specFiberPoint`: the point of
  the fibre named by a prime of `S` lying over `r`, and its image in `Spec S`.
* `Module.topologicalKrullDim_fiberSupport_eq_of_surjective`: **a surjection of algebras does not
  move the dimension of the fibre support.**
* `Module.topologicalKrullDim_fiberSupport_eq_of_finite`: **a finite map of algebras does not move
  it either.**
* `Module.topologicalKrullDim_fiberSupport_le_fiber`: the fibre support sits inside the fibre, so
  its dimension is at most the dimension of the fibre.
* `Module.topologicalKrullDimAt_fiberSupport_eq_of_stage`: **the local dimension of the fibre
  support is unchanged through one stage of a dévissage**, at a prime of the lower algebra with a
  unique prime above it.

## Implementation notes

The point of the fibre named by a prime `q` of `S` over `r` is `AlgebraicGeometry.specFiberPoint`,
the prime of the fibre ring attached to `q` by `PrimeSpectrum.primesOverOrderIsoFiber` read
through `AlgebraicGeometry.fiberSpecHomeo`, rather than `AlgebraicGeometry.Scheme.Hom.asFiber` of
the prime: the latter is a point of the fibre over the *contraction* of `q`, and using it would
mean transporting through a dependent type along the equation identifying that contraction with
`r`. Its image under `Scheme.Hom.fiberι` is `q` by
`AlgebraicGeometry.fiberι_specFiberPoint`, which with
`AlgebraicGeometry.mem_supp_pullback_fiberι_tilde_iff` also places it in the support of the fibre
module whenever `q` lies in the fibre support.

The two algebra maps of a stage are taken as `Algebra` instances together with the scalar towers
they satisfy, as in the `Tower` section of `StacksFrontier/RingTheory/Support/Fiber.lean`, rather
than as the algebra homomorphisms `S →ₐ[R] A` and `B →ₐ[R] A` of
`Module.DevissageStageData`: a consumer holding those installs `RingHom.toAlgebra` and the towers
are one-liners, as in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/FiberSupportDictionary.lean`.
Finiteness of `M` over the quotient algebra is *derived* from finiteness over `A` and the
surjection, not assumed.

The comparison along the finite map is the pair of inequalities
`Topology.topologicalKrullDim_le_of_continuous_of_specializes_injective` and
`Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap`, the two
halves that `Topology.topologicalKrullDimAt_eq_of_isClosedMap_of_specializes_injective` packages
for a single point; the closedness of the restricted map and the lifting of primes are the same
arguments as in `Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`, whose proof this
mirrors globally.

The `S`-algebra structure on the fibre ring `κ(r) ⊗_R S` is
`Algebra.TensorProduct.rightAlgebra`, a local instance here as in
`StacksFrontier/RingTheory/Support/Fiber.lean`.

## References

* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace AlgebraicGeometry

/-- **A point of the fibre of `Spec S → Spec R` over a prime `r` lies in the support of the fibre
of `Ñ` exactly when its image in `Spec S` lies in `Supp_S(N)`.** The support of a pullback is the
inverse image of the support (Stacks 056J), and the support of `Ñ` is the support of `N`. -/
public theorem mem_supp_pullback_fiberι_tilde_iff {R S N : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (r : Ideal R) [r.IsPrime]
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
      (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R))) :
    w ∈ SheafOfModules.supp ((Scheme.Modules.pullback
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
          (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N)))
      ↔ ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
          (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)) w) ∈ Module.support S N := by
  rw [Stacks.Modules.supp_pullback, Set.mem_preimage, supp_tilde]
  exact Iff.rfl

/-- The same membership read on the fibre ring: a point of the fibre lies in the support of the
fibre of `Ñ` exactly when the prime of `κ(r) ⊗_R S` naming it lies in the support of the fibre
module `κ(r) ⊗_R N`, the support of a base change being the inverse image of the support. -/
public theorem mem_supp_pullback_fiberι_tilde_iff_fiberSpecHomeo {R S N : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (r : Ideal R) [r.IsPrime]
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
      (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R))) :
    w ∈ SheafOfModules.supp ((Scheme.Modules.pullback
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
          (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N)))
      ↔ fiberSpecHomeo R S (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R) w ∈
          Module.support (r.Fiber S) (TensorProduct S (r.Fiber S) N) := by
  refine (mem_supp_pullback_fiberι_tilde_iff r w).trans ?_
  rw [Module.support_tensorProduct_eq_preimage_comap]
  exact iff_of_eq (congrArg (fun z : PrimeSpectrum S => z ∈ Module.support S N)
    (fiberι_eq_comap_fiberSpecHomeo R S (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R) w))

/-- **The support of the fibre of `Ñ` over a prime `r` of `R` is the part of `Supp_S(N)` lying
over `r`.** The fibre is the spectrum of the fibre ring, on which the support of the fibre of `Ñ`
is the support of the fibre module; and that support contracts homeomorphically onto
`Module.fiberSupport R S N r`. -/
public def suppPullbackFiberιTildeHomeomorph (R S N : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module S N] [Module.Finite S N] (r : Ideal R) [r.IsPrime] :
    ↥(SheafOfModules.supp ((Scheme.Modules.pullback
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
            (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N)))) ≃ₜ ↥(Module.fiberSupport R S N r) :=
  (Homeomorph.subtype (fiberSpecHomeo R S (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R))
      (mem_supp_pullback_fiberι_tilde_iff_fiberSpecHomeo r)).trans
    (Module.fiberSupportHomeomorph R S N r)

/-- The homeomorphism `AlgebraicGeometry.suppPullbackFiberιTildeHomeomorph` carries a point of
the fibre to its image in `Spec S`. -/
public theorem coe_suppPullbackFiberιTildeHomeomorph (R S N : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module S N] [Module.Finite S N] (r : Ideal R) [r.IsPrime]
    (w : ↥(SheafOfModules.supp ((Scheme.Modules.pullback
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
            (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N))))) :
    (suppPullbackFiberιTildeHomeomorph R S N r w : PrimeSpectrum S) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
        (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)) w.1 :=
  (fiberι_eq_comap_fiberSpecHomeo R S (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R) w.1).symm

/-- **The dimension of the support of the fibre of `Ñ` over a prime `r` of `R` is the dimension
of the part of `Supp_S(N)` lying over `r`.** -/
public theorem topologicalKrullDim_supp_pullback_fiberι_tilde {R S N : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (r : Ideal R) [r.IsPrime] :
    topologicalKrullDim ↥(SheafOfModules.supp ((Scheme.Modules.pullback
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
            (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N)))) =
      topologicalKrullDim ↥(Module.fiberSupport R S N r) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (suppPullbackFiberιTildeHomeomorph R S N r).isHomeomorph

/-- The point of the fibre of `Spec S → Spec R` over `r` named by a prime `q` of `S` lying over
`r`: the prime of the fibre ring attached to `q`, read on the fibre through
`AlgebraicGeometry.fiberSpecHomeo`. -/
public def specFiberPoint (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : Ideal R)
    [r.IsPrime] (q : Ideal S) [q.IsPrime] (hr : q.under R = r) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
      (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)) :=
  (fiberSpecHomeo R S (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R)).symm
    (PrimeSpectrum.primesOverOrderIsoFiber R S r ⟨q, ‹q.IsPrime›, ⟨hr.symm⟩⟩)

/-- The image in `Spec S` of the point of the fibre named by a prime `q` over `r` is `q`. -/
public theorem fiberι_specFiberPoint (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (r : Ideal R) [r.IsPrime] (q : Ideal S) [q.IsPrime] (hr : q.under R = r) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
        (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)) (specFiberPoint R S r q hr) =
      (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) :=
  (fiberι_fiberSpecHomeo_symm R S (⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R) _).trans
    (PrimeSpectrum.comap_primesOverOrderIsoFiber R S r q ⟨hr.symm⟩)

/-- The point of the fibre named by a prime `q` in the fibre support lies in the support of the
fibre of `Ñ`. -/
public theorem specFiberPoint_mem_supp_pullback_fiberι_tilde {R S N : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (r : Ideal R) [r.IsPrime] (q : Ideal S) [q.IsPrime] (hr : q.under R = r)
    (hmem : (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) ∈ Module.fiberSupport R S N r) :
    specFiberPoint R S r q hr ∈ SheafOfModules.supp ((Scheme.Modules.pullback
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
            (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N))) :=
  (mem_supp_pullback_fiberι_tilde_iff r (specFiberPoint R S r q hr)).2
    ((fiberι_specFiberPoint R S r q hr) ▸ hmem.1)

/-- **The local dimension of the support of the fibre of `Ñ` at the point named by a prime `q` of
`S` over `r` is the local dimension of the part of `Supp_S(N)` lying over `r` at `q`.** -/
public theorem topologicalKrullDimAt_supp_pullback_fiberι_tilde {R S N : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (r : Ideal R) [r.IsPrime] (q : Ideal S) [q.IsPrime] (hr : q.under R = r)
    (hmem : (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) ∈ Module.fiberSupport R S N r)
    (hw : specFiberPoint R S r q hr ∈ SheafOfModules.supp ((Scheme.Modules.pullback
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
            (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N)))) :
    topologicalKrullDimAt ↥(SheafOfModules.supp ((Scheme.Modules.pullback
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι
            (⟨r, ‹r.IsPrime›⟩ : Spec (CommRingCat.of R)))).obj
        (tilde (ModuleCat.of (CommRingCat.of S) N)))) ⟨specFiberPoint R S r q hr, hw⟩ =
      topologicalKrullDimAt ↥(Module.fiberSupport R S N r) ⟨⟨q, ‹q.IsPrime›⟩, hmem⟩ := by
  refine (topologicalKrullDimAt_eq_of_homeomorph (suppPullbackFiberιTildeHomeomorph R S N r)
    ⟨specFiberPoint R S r q hr, hw⟩).trans (congrArg _ (Subtype.ext ?_))
  exact (coe_suppPullbackFiberιTildeHomeomorph R S N r ⟨specFiberPoint R S r q hr, hw⟩).trans
    (fiberι_specFiberPoint R S r q hr)

end AlgebraicGeometry

namespace Module

/-- **Along a surjection of algebras, the fibre support upstairs contracts onto the fibre support
downstairs.** One inclusion is that contraction carries the fibre support of `M` over `A` into
that of `M` over `S`; for the other, a prime of `S` in the support of `M` contains the annihilator
of `M`, hence the kernel of the surjection, and so is a contraction. -/
public theorem image_comap_fiberSupport_of_surjective {R S A N M : Type*} [CommRing R]
    [CommRing S] [CommRing A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M] [Module A M]
    [IsScalarTower S A M] [Module.Finite A M] (hsurj : Function.Surjective (algebraMap S A))
    (e : N ≃ₗ[S] M) (r : Ideal R) [r.IsPrime] :
    PrimeSpectrum.comap (algebraMap S A) '' Module.fiberSupport R A M r =
      Module.fiberSupport R S N r := by
  have : Module.Finite S A := Module.Finite.of_surjective (Algebra.linearMap S A) hsurj
  have : Module.Finite S M := Module.Finite.trans A M
  rw [Module.fiberSupport_congr R S N r e]
  ext z
  refine ⟨?_, fun hz => ?_⟩
  · rintro ⟨w, hw, rfl⟩
    exact Module.comap_mem_fiberSupport_of_mem r hw
  · have hk : RingHom.ker (algebraMap S A) ≤ z.asIdeal := by
      refine le_trans ?_ (Module.mem_support_iff_of_finite.mp hz.1)
      rw [Module.annihilator_eq_comap_annihilator (R := S) (S := A) (M := M)]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
      exact Submodule.zero_mem _
    obtain ⟨w, hw⟩ : z ∈ Set.range (PrimeSpectrum.comap (algebraMap S A)) := by
      rw [_root_.range_comap_of_surjective A (algebraMap S A) hsurj]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (SetLike.coe_subset_coe.mpr hk)
    exact ⟨w, Module.mem_fiberSupport_of_comap_mem_fiberSupport_of_surjective hsurj r
      (hw ▸ hz), hw⟩

/-- **A surjection of algebras does not move the dimension of the fibre support.** Contraction
along a surjection is a closed embedding, so it is a homeomorphism of the fibre support of `M`
over `A` onto its image, which is the fibre support of `N` over `S`. -/
public theorem topologicalKrullDim_fiberSupport_eq_of_surjective {R S A N M : Type*}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M]
    [Module A M] [IsScalarTower S A M] [Module.Finite A M]
    (hsurj : Function.Surjective (algebraMap S A)) (e : N ≃ₗ[S] M) (r : Ideal R) [r.IsPrime] :
    topologicalKrullDim ↥(Module.fiberSupport R S N r) =
      topologicalKrullDim ↥(Module.fiberSupport R A M r) :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (((PrimeSpectrum.isClosedEmbedding_comap_of_surjective A (algebraMap S A)
            hsurj).isEmbedding.homeomorphImage (Module.fiberSupport R A M r)).trans
      (Homeomorph.setCongr
        (Module.image_comap_fiberSupport_of_surjective hsurj e r))).isHomeomorph).symm

/-- **A finite map of algebras does not move the dimension of the fibre support.** Contraction
along an integral map restricts to a continuous closed surjection from the fibre support over `A`
onto the fibre support over `B` which is injective on specialisations, since an integral extension
has no inclusions between primes with the same contraction. The two inequalities are the global
counterparts of `Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`. -/
public theorem topologicalKrullDim_fiberSupport_eq_of_finite (R B A M : Type*) [CommRing R]
    [CommRing B] [CommRing A] [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M] [Module.Finite B M]
    [Module.Finite A M] [Module.Finite B A] (r : Ideal R) [r.IsPrime] :
    topologicalKrullDim ↥(Module.fiberSupport R A M r) =
      topologicalKrullDim ↥(Module.fiberSupport R B M r) := by
  have hintegral : (algebraMap B A).IsIntegral := fun a => Algebra.IsIntegral.isIntegral a
  have hmaps : ∀ z ∈ Module.fiberSupport R A M r,
      PrimeSpectrum.comap (algebraMap B A) z ∈ Module.fiberSupport R B M r :=
    fun _ hz => Module.comap_mem_fiberSupport_of_mem r hz
  have hcont : Continuous (fun z : ↥(Module.fiberSupport R A M r) =>
      (⟨PrimeSpectrum.comap (algebraMap B A) z.1, hmaps z.1 z.2⟩ :
        ↥(Module.fiberSupport R B M r))) :=
    continuous_induced_rng.mpr
      ((PrimeSpectrum.continuous_comap (algebraMap B A)).comp continuous_subtype_val)
  have hclosed : IsClosedMap (fun z : ↥(Module.fiberSupport R A M r) =>
      (⟨PrimeSpectrum.comap (algebraMap B A) z.1, hmaps z.1 z.2⟩ :
        ↥(Module.fiberSupport R B M r))) :=
    IsClosedMap.restrictOfIsClosedOfPreimage
      (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap B A) hintegral)
      (Module.isClosed_support (R := A) (M := M))
      (PrimeSpectrum.preimage_comap_algebraMap_eq (B := B) (⟨r, ‹_›⟩ : PrimeSpectrum R))
      Set.inter_subset_right hmaps
  have hlift : ∀ w : ↥(Module.fiberSupport R B M r), ∃ z : ↥(Module.fiberSupport R A M r),
      PrimeSpectrum.comap (algebraMap B A) z.1 = w.1 := by
    intro w
    have hann : (Module.annihilator A M).comap (algebraMap B A) ≤ w.1.asIdeal := by
      rw [← Module.annihilator_eq_comap_annihilator (R := B) (S := A) (M := M)]
      exact Module.mem_support_iff_of_finite.mp w.2.1
    obtain ⟨P, hPge, hPprime, hPcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral w.1.asIdeal (Module.annihilator A M) hann
    have hw1 : PrimeSpectrum.comap (algebraMap B A) (⟨P, hPprime⟩ : PrimeSpectrum A) = w.1 :=
      PrimeSpectrum.ext hPcomap
    refine ⟨⟨⟨P, hPprime⟩, Module.mem_support_iff_of_finite.mpr hPge, ?_⟩, hw1⟩
    rw [Set.mem_preimage, ← PrimeSpectrum.comap_comap_algebraMap (B := B), hw1]
    exact w.2.2
  have hinj : ∀ z w : PrimeSpectrum A, z ≤ w →
      PrimeSpectrum.comap (algebraMap B A) z = PrimeSpectrum.comap (algebraMap B A) w → z = w := by
    intro z w hle heq
    rcases eq_or_lt_of_le hle with h | hlt
    · exact h
    · exact absurd (congrArg PrimeSpectrum.asIdeal heq)
        (Ideal.IsIntegral.comap_lt_comap (R := B)
          ((PrimeSpectrum.asIdeal_lt_asIdeal z w).mpr hlt)).ne
  refine le_antisymm
    (Topology.topologicalKrullDim_le_of_continuous_of_specializes_injective _ hcont
      fun z w hzw hEq => Subtype.ext (hinj z.1 w.1
        ((PrimeSpectrum.le_iff_specializes z.1 w.1).mpr ((subtype_specializes_iff z w).mp hzw))
        (congrArg Subtype.val hEq)))
    (Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap _ hcont
      (fun w => (hlift w).imp fun _ h => Subtype.ext h) (Or.inl hclosed.specializingMap))

/-- **The fibre support sits inside the fibre**, so its dimension is at most the dimension of the
fibre of `Spec B → Spec R` over `r`. -/
public theorem topologicalKrullDim_fiberSupport_le_fiber (R B M : Type*) [CommRing R]
    [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] (r : Ideal R) [r.IsPrime] :
    topologicalKrullDim ↥(Module.fiberSupport R B M r) ≤
      topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R B) ⁻¹'
        {(⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R)}) :=
  topologicalKrullDim_le_of_subset fun _ hz => hz.2

/-- **The local dimension of the fibre support is unchanged through one stage of a dévissage.**

Let `S → A` be a surjection of `R`-algebras, let `B → A` be finite, let `M` be a finite
`A`-module identified with an `S`-module `N`, let `r` be a prime of `R`, let `lp` be a prime of
`B` in the fibre support of `M` over `r`, let `up` be the *only* prime of `A` contracting to `lp`
and let `q` be the contraction of `up` to `S`. Then the part of `Supp_S(N)` lying over `r` has at
`q` the local Krull dimension that the part of `Supp_B(M)` lying over `r` has at `lp`.

Both steps are `Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`: a surjection is
integral and the prime above `q` is unique because contraction along a surjection is injective. -/
public theorem topologicalKrullDimAt_fiberSupport_eq_of_stage {R S A B N M : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S] [Algebra R A]
    [Algebra R B] [Algebra S A] [Algebra B A] [IsScalarTower R S A] [IsScalarTower R B A]
    [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M] [Module A M] [Module B M]
    [IsScalarTower S A M] [IsScalarTower B A M] [Module.Finite A M] [Module.Finite B M]
    [Module.Finite B A] (hsurj : Function.Surjective (algebraMap S A)) (e : N ≃ₗ[S] M)
    (r : Ideal R) [r.IsPrime] {up : PrimeSpectrum A} {q : PrimeSpectrum S} {lp : PrimeSpectrum B}
    (hq : PrimeSpectrum.comap (algebraMap S A) up = q)
    (hlp : PrimeSpectrum.comap (algebraMap B A) up = lp)
    (huniq : ∀ p' : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap B A) p' = lp → p' = up)
    (hqmem : q ∈ Module.fiberSupport R S N r) (hlpmem : lp ∈ Module.fiberSupport R B M r) :
    topologicalKrullDimAt ↥(Module.fiberSupport R S N r) ⟨q, hqmem⟩ =
      topologicalKrullDimAt ↥(Module.fiberSupport R B M r) ⟨lp, hlpmem⟩ := by
  have : Module.Finite S A := Module.Finite.of_surjective (Algebra.linearMap S A) hsurj
  have : Module.Finite S M := Module.Finite.trans A M
  have hNM : Module.fiberSupport R S N r = Module.fiberSupport R S M r :=
    Module.fiberSupport_congr R S N r e
  have hqmem' : q ∈ Module.fiberSupport R S M r := hNM ▸ hqmem
  have hupmem : up ∈ Module.fiberSupport R A M r :=
    Module.mem_fiberSupport_of_comap_mem_fiberSupport_of_surjective hsurj r
      (by rw [hq]; exact hqmem')
  calc topologicalKrullDimAt ↥(Module.fiberSupport R S N r) ⟨q, hqmem⟩
      = topologicalKrullDimAt ↥(Module.fiberSupport R S M r) ⟨q, hqmem'⟩ :=
        (topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hNM) ⟨q, hqmem⟩).trans
          (congrArg _ (Subtype.ext rfl))
    _ = topologicalKrullDimAt ↥(Module.fiberSupport R A M r) ⟨up, hupmem⟩ :=
        (Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral r hq
          (fun _ hp' ↦ PrimeSpectrum.comap_injective_of_surjective _ hsurj (hp'.trans hq.symm))
          hupmem hqmem').symm
    _ = topologicalKrullDimAt ↥(Module.fiberSupport R B M r) ⟨lp, hlpmem⟩ :=
        Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral r hlp huniq hupmem hlpmem

end Module

end
