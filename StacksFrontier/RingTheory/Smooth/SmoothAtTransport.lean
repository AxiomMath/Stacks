module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Localization.Basic

/-!
# Transporting smoothness at a prime along isomorphisms

`Algebra.IsSmoothAt R p`, formal smoothness of `Localization.AtPrime p` over `R`, is invariant
under replacing the algebra by an isomorphic one and under replacing the base by an isomorphic
one.  Neither is in Mathlib, and both are needed whenever a geometric statement about a scheme
over `Spec R` is read on a chart: the sections of the structure sheaf are only *isomorphic* to
the ring one computes with, and the base of the chart comparison is `Γ(Spec R, ⊤)` rather than
`R` itself.

## Main results

* `Algebra.isSmoothAt_congr`: smoothness at a prime transports along an algebra isomorphism.
* `Algebra.formallySmooth_iff_of_bijective_algebraMap` and
  `Algebra.isSmoothAt_iff_of_bijective_algebraMap`: the base may be replaced by an isomorphic
  one.

## Implementation notes

For the base, the two directions have different proofs: an isomorphic base is formally smooth,
so `Algebra.FormallySmooth.comp` gives one direction, and it is formally unramified, so
`Algebra.FormallySmooth.of_restrictScalars` gives the other.

For the algebra, the localizations at corresponding primes are identified by
`IsLocalization.ringEquivOfRingEquiv`, whose compatibility with the structure maps makes it an
algebra isomorphism over the base; `Algebra.FormallySmooth.iff_of_equiv` then applies.
-/

@[expose] public noncomputable section

namespace Algebra

universe u v w

section Base

variable (R : Type u) (S : Type v) (A : Type w) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  (hRS : Function.Bijective (algebraMap R S))

include hRS

/-- The base of a formally smooth algebra may be replaced by an isomorphic ring. -/
public theorem formallySmooth_iff_of_bijective_algebraMap :
    Algebra.FormallySmooth R A ↔ Algebra.FormallySmooth S A := by
  have e : R ≃ₐ[R] S := AlgEquiv.ofBijective (Algebra.ofId R S) hRS
  have : Algebra.FormallySmooth R S := Algebra.FormallySmooth.of_equiv e
  have : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.of_equiv e
  exact ⟨fun _ => Algebra.FormallySmooth.of_restrictScalars R S A,
    fun _ => Algebra.FormallySmooth.comp R S A⟩

/-- Smoothness at a prime does not depend on which of two isomorphic base rings is used. -/
public theorem isSmoothAt_iff_of_bijective_algebraMap (p : Ideal A) [p.IsPrime] :
    Algebra.IsSmoothAt R p ↔ Algebra.IsSmoothAt S p :=
  formallySmooth_iff_of_bijective_algebraMap R S (Localization.AtPrime p) hRS

end Base

section Congr

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (ε : A ≃ₐ[R] B) (p : Ideal A) (Q : Ideal B)
  [p.IsPrime] [Q.IsPrime] (hpQ : p = Q.comap (ε : A →+* B))

include hpQ

/-- An algebra isomorphism `ε : A ≃ₐ[R] B` maps the complement of `p` onto the complement of `Q`,
where `p` is the preimage of `Q` under `ε`. -/
theorem map_primeCompl_of_comap :
    Submonoid.map (ε : A ≃+* B).toMonoidHom p.primeCompl = Q.primeCompl := by
  ext b
  simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_compl_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, rfl⟩ hb
    exact ha (by rwa [hpQ])
  · intro hb
    refine ⟨ε.symm b, fun hmem => hb ?_, by simp⟩
    rw [hpQ] at hmem
    simpa using hmem

/-- **Smoothness at a prime transports along an algebra isomorphism.** -/
theorem isSmoothAt_congr :
    Algebra.IsSmoothAt R p ↔ Algebra.IsSmoothAt R Q := by
  have hmap : Submonoid.map (ε : A ≃+* B).toMonoidHom p.primeCompl = Q.primeCompl :=
    map_primeCompl_of_comap ε p Q hpQ
  let φ : Localization.AtPrime p ≃+* Localization.AtPrime Q :=
    IsLocalization.ringEquivOfRingEquiv (M := p.primeCompl) (T := Q.primeCompl)
      (Localization.AtPrime p) (Localization.AtPrime Q) (ε : A ≃+* B) hmap
  have hcomm : ∀ r : R, φ (algebraMap R (Localization.AtPrime p) r) =
      algebraMap R (Localization.AtPrime Q) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p),
      IsScalarTower.algebraMap_apply R B (Localization.AtPrime Q),
      show φ ((algebraMap A (Localization.AtPrime p)) (algebraMap R A r)) =
        algebraMap B (Localization.AtPrime Q) ((ε : A ≃+* B) (algebraMap R A r)) from
      IsLocalization.ringEquivOfRingEquiv_eq _ _]
    exact congrArg (algebraMap B (Localization.AtPrime Q)) (ε.commutes r)
  exact Algebra.FormallySmooth.iff_of_equiv { φ with commutes' := hcomm }

end Congr

end Algebra

end
