module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.Flat.GeometricFibresStage
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs
public import StacksFrontier.RingTheory.Module.Projective.NilpotentIdeal

/-!
# The hypothesis of Stacks 05FS, and the quotient steps of its Noetherian induction

Stacks 05FS says that a finite type flat algebra `S` over a Noetherian ring `R` whose fibre
rings `S ⊗_R κ(𝔭)` are geometrically integral over `κ(𝔭)` is projective as an `R`-module. Its
proof is a Noetherian induction over the ideals of `R`, carried out on the reductions
`S/IS = (R ⧸ I) ⊗_R S`. This file collects what the induction needs before the completion step
of `StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresCompletion`:

* the fibre hypothesis in a shape that is transparently stable under base change, so that the
  reductions `R ⧸ I`, the localizations `R_f` and the completion `R^∧` inherit it, and the two
  consequences of it that the proof spends; and
* the transport of projectivity between the base change `(A ⧸ J) ⊗_A C` and the reduction
  `C ⧸ JC`, together with the step of the induction that discharges a non-radical ideal by
  Stacks 05CG.

## Main results

* `AlgebraicGeometry.geometricallyIntegral_algebraMap_iff_residueField`: that condition is the
  source's hypothesis, that each fibre ring `S ⊗_R κ(𝔭)` is geometrically integral over `κ(𝔭)`.
* `AlgebraicGeometry.GeometricallyIntegral.baseChange_algebraMap`: stability under an arbitrary
  base change `R → A`, in the ring-theoretic shape the induction uses.
* `associatedPrimes.eq_singleton_ker`: an `S`-algebra which is a domain has exactly one
  associated prime as an `S`-module, the kernel of its structure map.
* `Algebra.ker_algebraMap_tensorProduct_residueField`: for a flat algebra the kernel of the
  structure map of the fibre at `𝔭` is `𝔭C`.
* `AlgebraicGeometry.GeometricallyIntegral.map_sup_ne_top`: the associated-prime hypothesis of
  Stacks 05DP, discharged by geometric integrality of the fibres.
* `TensorProduct.quotTensorEquivQuotSMulBase`: the `A ⧸ J`-linear refinement of
  `TensorProduct.quotTensorEquivQuotSMul`.
* `Module.Flat.projective_of_projective_tensorProduct_quotient_nilradical`: the non-radical step
  of the induction, Stacks 05CG applied to the nilradical of a Noetherian ring.
* `RingHom.ker_lt_ker_of_tower`: passing from a quotient `A` of `R` to a proper quotient of `A`
  strictly enlarges the kernel over `R`, which is what makes the induction decrease.

## Implementation notes

The fibre hypothesis is Mathlib's morphism property
`AlgebraicGeometry.GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))`, for
which stability under base change is already an instance. Over a field base it is
`Algebra.IsGeometricallyIntegral`; over a general commutative base ring it unfolds, by
`Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct`, to `S ⊗_R K` being a domain for
every
field `K` carrying an `R`-algebra structure, which is the form the induction consumes. No new
predicate is introduced.

`AlgebraicGeometry.GeometricallyIntegral.baseChange_algebraMap` is proved through
`Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct` rather than through
`MorphismProperty.IsStableUnderBaseChange`, to avoid having to exhibit the ring-theoretic base
change as a pullback square of schemes; the two tensor cancellations it uses are
`Algebra.TensorProduct.cancelBaseChange` and `Algebra.TensorProduct.comm`.

The tensor factors are written with the field on the right, `S ⊗[R] K`, which is the order
`AlgebraicGeometry.pullbackSpecIso` and the source both use; `Algebra.TensorProduct.comm`
mediates where the opposite order is needed.

All of `R`, `S` and the test fields are taken in one universe, as they are in
`Algebra.IsGeometricallyIntegral`, which passes through `Spec`.

## References

* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 05DX](https://stacks.math.columbia.edu/tag/05DX)
* [Stacks Project, Tag 05CG](https://stacks.math.columbia.edu/tag/05CG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

open scoped TensorProduct

universe u v

/-! ### The fibre hypothesis -/

namespace AlgebraicGeometry

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The fibre `S ⊗_R K` of a geometrically integral algebra at a field-valued point is a
domain. -/
theorem GeometricallyIntegral.isDomain_tensorProduct
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))) (K : Type u) [Field K]
    [Algebra R K] : IsDomain (S ⊗[R] K) :=
  (Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct R S).mp h K

/-- The fibre `S ⊗_R K` of a geometrically integral algebra at a field-valued point is
nonzero. -/
theorem GeometricallyIntegral.nontrivial_tensorProduct
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))) (K : Type u) [Field K]
    [Algebra R K] : Nontrivial (S ⊗[R] K) :=
  let := h.isDomain_tensorProduct K
  inferInstance

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Flipping the tensor factors is an isomorphism of `B`-algebras from `A ⊗[R] B`, with the
algebra structure on the right factor, to `B ⊗[R] A`, with the algebra structure on the left
factor. -/
private noncomputable def commRight (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : (A ⊗[R] B) ≃ₐ[B] (B ⊗[R] A) :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A B).toRingEquiv) fun b => by
    simp [Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply]

/-- For an `R`-algebra `A` and an `A`-algebra `K` over `R`, the base change to `K` of `A ⊗_R S` is
`S ⊗_R K`. -/
private noncomputable def baseChangeTensorEquiv (A K : Type u) [CommRing A] [CommRing K]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] :
    ((A ⊗[R] S) ⊗[A] K) ≃+* (S ⊗[R] K) :=
  ((commRight A (A ⊗[R] S) K).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange R A K K S).toRingEquiv).trans
      (Algebra.TensorProduct.comm R K S).toRingEquiv

/-- For a field `k` over `R` and a field `K` over `k`, the base change to `K` of the fibre
`S ⊗_R k` is the fibre `S ⊗_R K`. -/
private noncomputable def fibreBaseChange (k : Type u) [Field k] [Algebra R k] (K : Type u)
    [Field K] [Algebra k K] [Algebra R K] [IsScalarTower R k K] :
    ((S ⊗[R] k) ⊗[k] K) ≃+* (S ⊗[R] K) :=
  (Algebra.TensorProduct.congr (commRight R S k) AlgEquiv.refl).toRingEquiv.trans
    (baseChangeTensorEquiv k K)

/-- Geometric integrality of `Spec S → Spec R` is the hypothesis of Stacks 05FS: every fibre
ring `S ⊗_R κ(𝔭)` is geometrically integral over `κ(𝔭)`.

A field `K` with an `R`-algebra structure is a field extension of `κ(𝔭)` for
`𝔭 = ker (R → K)`, through the fraction field of `R ⧸ 𝔭`, and
`(S ⊗_R κ(𝔭)) ⊗_{κ(𝔭)} K ≅ S ⊗_R K`, so quantifying over all field-valued points of `Spec R`
and quantifying over the primes of `R` give the same condition. -/
theorem geometricallyIntegral_algebraMap_iff_residueField :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap R S))) ↔ ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField) := by
  rw [Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct]
  constructor
  · intro h p _
    rw [Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct]
    intro k' _ _
    let : Algebra R k' :=
      ((algebraMap p.ResidueField k').comp (algebraMap R p.ResidueField)).toAlgebra
    have : IsScalarTower R p.ResidueField k' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have := h k'
    exact (fibreBaseChange (S := S) p.ResidueField k').toMulEquiv.isDomain _
  · intro h K _ _
    have hp : (RingHom.ker (algebraMap R K)).IsPrime := RingHom.ker_isPrime _
    set p := RingHom.ker (algebraMap R K) with hpdef
    let g : (R ⧸ p) →+* K := Ideal.Quotient.lift p (algebraMap R K) fun _ ha => ha
    have hg : Function.Injective g := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, ← hpdef]
      exact Ideal.map_quotient_self _
    let : Algebra p.ResidueField K := (IsFractionRing.lift hg).toAlgebra
    have : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R K r = IsFractionRing.lift hg (algebraMap R p.ResidueField r)
      rw [← Ideal.algebraMap_quotient_residueField_mk, IsFractionRing.lift_algebraMap]
      exact (Ideal.Quotient.lift_mk _ _ _).symm
    have := (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct _ _).mp (h p) K
    exact (fibreBaseChange (S := S) p.ResidueField K).toMulEquiv.symm.isDomain _

/-- Geometric integrality of the fibres is stable under base change: if `S ⊗_R K` is a domain
for every field `K` over `R`, the same holds for `(A ⊗_R S) ⊗_A K` over any `R`-algebra `A`,
because a field over `A` is a field over `R` and `K ⊗_A (A ⊗_R S) ≅ K ⊗_R S`.

Mathlib knows that the morphism property is stable under base change; this is that statement
transported to the ring-theoretic base change `A ⊗_R S`, which is the shape the Noetherian
induction of Stacks 05FS uses. -/
theorem GeometricallyIntegral.baseChange_algebraMap
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))) (A : Type u) [CommRing A]
    [Algebra R A] :
    GeometricallyIntegral (Spec.map (ofHom (algebraMap A (A ⊗[R] S)))) := by
  rw [Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct]
  intro K _ _
  let : Algebra R K := ((algebraMap A K).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := h.isDomain_tensorProduct K
  exact (baseChangeTensorEquiv (R := R) (S := S) A K).toMulEquiv.isDomain _

end AlgebraicGeometry

/-- An `S`-algebra `N` which is a domain has exactly one associated prime as an `S`-module,
namely the kernel of its structure map: the annihilator of a nonzero element of `N` is that
kernel, and the annihilator of `0` is not prime. -/
theorem associatedPrimes.eq_singleton_ker (S N : Type*) [CommRing S] [CommRing N] [Algebra S N]
    [IsDomain N] : associatedPrimes S N = {RingHom.ker (algebraMap S N)} := by
  have hcolon : ∀ x : N, x ≠ 0 →
      (⊥ : Submodule S N).colon {x} = RingHom.ker (algebraMap S N) := by
    intro x hx
    ext s
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, RingHom.mem_ker, Algebra.smul_def,
      mul_eq_zero]
    simp [hx]
  have hann : ∀ x : N, x ≠ 0 →
      ((⊥ : Submodule S N).colon {x}).radical = RingHom.ker (algebraMap S N) := fun x hx => by
    rw [hcolon x hx, (RingHom.ker_isPrime (algebraMap S N)).radical]
  refine Set.eq_singleton_iff_unique_mem.2
    ⟨⟨RingHom.ker_isPrime _, 1, (hann 1 one_ne_zero).symm⟩, ?_⟩
  rintro I ⟨hI, x, rfl⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact absurd (by simp) hI.ne_top
  · exact hann x hx

namespace Algebra

/-- For a flat algebra `C` over `A` and a prime `𝔭` of `A`, the kernel of the structure map
`C → C ⊗_A κ(𝔭)` of the fibre is the ideal `𝔭C`: the map factors as
`C → C ⊗_A (A ⧸ 𝔭) → C ⊗_A κ(𝔭)`, the first map has kernel `𝔭C` because
`C ⧸ 𝔭C ≅ C ⊗_A (A ⧸ 𝔭)`, and the second is injective because `C` is flat and
`A ⧸ 𝔭 → κ(𝔭)` is injective. -/
theorem ker_algebraMap_tensorProduct_residueField {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [Module.Flat A C] (p : Ideal A) [p.IsPrime] :
    RingHom.ker (algebraMap C (C ⊗[A] p.ResidueField)) = p.map (algebraMap A C) := by
  set f : (A ⧸ p) →ₗ[A] p.ResidueField :=
    (Algebra.linearMap (A ⧸ p) p.ResidueField).restrictScalars A with hf
  have hinj : Function.Injective (LinearMap.lTensor C f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f
      p.injective_algebraMap_quotient_residueField
  have hfactor : ∀ c : C, algebraMap C (C ⊗[A] p.ResidueField) c
      = LinearMap.lTensor C f (algebraMap C (C ⊗[A] (A ⧸ p)) c) := fun c => by
    simp [Algebra.TensorProduct.algebraMap_apply, hf]
  have hquot : ∀ c : C, algebraMap C (C ⊗[A] (A ⧸ p)) c = 0 ↔ c ∈ p.map (algebraMap A C) := by
    intro c
    rw [show algebraMap C (C ⊗[A] (A ⧸ p)) c
        = Algebra.TensorProduct.quotIdealMapEquivTensorQuot C p (Ideal.Quotient.mk _ c) from rfl,
      map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C p).injective,
      Ideal.Quotient.eq_zero_iff_mem]
  ext c
  rw [RingHom.mem_ker, hfactor, ← hquot]
  exact ⟨fun hc => hinj (by simpa using hc), fun hc => by simp [hc]⟩

end Algebra

namespace AlgebraicGeometry

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]

/-- For a geometrically integral algebra `C` over `A` and a maximal ideal `𝔪` of `A`, the ideal
`𝔪C` is proper: `C ⧸ 𝔪C ≅ C ⊗_A (A ⧸ 𝔪) ≅ C ⊗_A κ(𝔪)` is a domain, hence nonzero. -/
theorem GeometricallyIntegral.map_maximal_ne_top
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap A C)))) (m : Ideal A) [m.IsMaximal] :
    m.map (algebraMap A C) ≠ ⊤ := by
  let e : (A ⧸ m) ≃ₐ[A] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom A (A ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  have h2 : Nontrivial (C ⊗[A] (A ⧸ m)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := C)) e).nontrivial_congr.mpr
      (h.nontrivial_tensorProduct m.ResidueField)
  rw [← Ideal.Quotient.nontrivial_iff]
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C m).nontrivial_congr.mpr h2

/-- **The associated-prime hypothesis of Stacks 05DP, discharged by geometric integrality of
the fibres.** Let `C` be a flat `A`-algebra whose fibres are geometrically integral and let `I`
be an ideal of `A` contained in the Jacobson radical. If a prime `𝔮` of `C` is an associated
prime of the fibre `C ⊗_A κ(𝔭)` over its own contraction `𝔭`, then `IC + 𝔮 ≠ C`.

Geometric integrality enters twice. It makes the fibre a domain, so that `𝔮` is forced to be
the kernel `𝔭C` of the structure map of the fibre — this is the source's statement that `𝔭C`
is "the unique associated prime". And it makes every fibre nonzero, so that `𝔪C ≠ C` for the
maximal ideal `𝔪` of `A` containing `𝔭` and `I`; such an `𝔪` exists because `I` lies in every
maximal ideal. Then `IC + 𝔮 = (I + 𝔭)C ⊆ 𝔪C ≠ C`. -/
theorem GeometricallyIntegral.map_sup_ne_top [Module.Flat A C]
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap A C)))) (I : Ideal A)
    (hI : I ≤ Ideal.jacobson ⊥) (q : PrimeSpectrum C)
    (hq : q.asIdeal ∈ associatedPrimes C
      (C ⊗[A] (PrimeSpectrum.comap (algebraMap A C) q).asIdeal.ResidueField)) :
    I.map (algebraMap A C) ⊔ q.asIdeal ≠ ⊤ := by
  set p := (PrimeSpectrum.comap (algebraMap A C) q).asIdeal with hpdef
  have : p.IsPrime := (PrimeSpectrum.comap (algebraMap A C) q).isPrime
  have : IsDomain (C ⊗[A] p.ResidueField) := h.isDomain_tensorProduct p.ResidueField
  have hqker : q.asIdeal = p.map (algebraMap A C) := by
    rw [← Algebra.ker_algebraMap_tensorProduct_residueField (C := C) p]
    exact Set.eq_of_mem_singleton (by rwa [← associatedPrimes.eq_singleton_ker C])
  obtain ⟨m, hm, hle⟩ := (I ⊔ p).exists_le_maximal (by
    obtain ⟨m, hm, hle⟩ := p.exists_le_maximal ‹p.IsPrime›.ne_top
    have hjm : Ideal.jacobson (⊥ : Ideal A) ≤ m := sInf_le ⟨bot_le, hm⟩
    exact fun hc => hm.ne_top (top_unique (hc.ge.trans (sup_le (hI.trans hjm) hle))))
  refine fun hc => h.map_maximal_ne_top m (top_unique ?_)
  rw [← hc, hqker, ← Ideal.map_sup]
  exact Ideal.map_mono hle

end AlgebraicGeometry

/-! ### Quotients and base change -/

/-- A module with at most one element is projective: the zero splitting works. -/
theorem Module.Projective.of_subsingleton (R : Type u) (M : Type v) [Semiring R]
    [AddCommMonoid M] [Module R M] [Subsingleton M] : Module.Projective R M :=
  Module.projective_def'.mpr ⟨0, LinearMap.ext fun _ => Subsingleton.elim _ _⟩

/-- The `A ⧸ J`-linear refinement of `TensorProduct.quotTensorEquivQuotSMul`: for an ideal `J`
of `A` and an `A`-module `M`, the base change `(A ⧸ J) ⊗_A M` is the reduction `M ⧸ JM`, and the
canonical isomorphism between them is linear over `A ⧸ J` and not merely over `A`. -/
noncomputable def TensorProduct.quotTensorEquivQuotSMulBase (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] (J : Ideal A) :
    ((A ⧸ J) ⊗[A] M) ≃ₗ[A ⧸ J] M ⧸ (J • (⊤ : Submodule A M)) :=
  (TensorProduct.quotTensorEquivQuotSMul M J).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- **The non-radical step of the Noetherian induction of Stacks 05FS.** Let `A` be a
Noetherian ring and `C` a flat `A`-module whose base change to `A ⧸ nilradical A` is projective.
Then `C` is projective over `A`.

This is Stacks 05CG, `Module.Flat.projective_of_isNilpotent_of_projective_quotient_smul_top`,
with the reduction `C ⧸ (nilradical A)C` presented as the base change
`(A ⧸ nilradical A) ⊗_A C`; the nilradical of a Noetherian ring is nilpotent. -/
theorem Module.Flat.projective_of_projective_tensorProduct_quotient_nilradical (A : Type u)
    [CommRing A] [IsNoetherianRing A] (C : Type v) [AddCommGroup C] [Module A C]
    [Module.Flat A C]
    (h : Module.Projective (A ⧸ nilradical A) ((A ⧸ nilradical A) ⊗[A] C)) :
    Module.Projective A C :=
  have := h
  Module.Flat.projective_of_isNilpotent_of_projective_quotient_smul_top
    (IsNoetherianRing.isNilpotent_nilradical A)
    (Module.Projective.of_equiv (TensorProduct.quotTensorEquivQuotSMulBase A C (nilradical A)))

/-- Passing from a quotient `A` of `R` to a proper quotient `D` of `A` strictly enlarges the
kernel over `R`. This is what makes the Noetherian induction of Stacks 05FS decrease: the
induction is over the kernel of `R → A`, and every step replaces `A` by a proper quotient. -/
theorem RingHom.ker_lt_ker_of_tower {R A D : Type u} [CommRing R] [CommRing A] [CommRing D]
    [Algebra R A] [Algebra A D] [Algebra R D] [IsScalarTower R A D]
    (hRA : Function.Surjective (algebraMap R A)) (hD : RingHom.ker (algebraMap A D) ≠ ⊥) :
    RingHom.ker (algebraMap R A) < RingHom.ker (algebraMap R D) := by
  have hcomp : RingHom.ker (algebraMap R D)
      = (RingHom.ker (algebraMap A D)).comap (algebraMap R A) := by
    rw [IsScalarTower.algebraMap_eq R A D, RingHom.comap_ker]
  refine lt_of_le_of_ne (hcomp ▸ fun x hx => ?_) fun hEq => hD ?_
  · simp [RingHom.mem_ker.mp hx]
  · rw [← Ideal.map_comap_of_surjective _ hRA (RingHom.ker (algebraMap A D)), ← hcomp, ← hEq,
      Ideal.map_eq_bot_iff_le_ker]

end
