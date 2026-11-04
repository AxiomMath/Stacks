module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Instances.ZMod
public import StacksFrontier.RingTheory.AdicCompletion.PadicIntFinite
public import StacksFrontier.RingTheory.Flat.PadicInt

/-!
# The universal deformation ring of a residual representation with fixed determinant

Let `π` be a topological group and let `ρ₀ : π → GLₙ(𝐅_ℓ)` be a continuous residual
representation. Fix a continuous character `δ : π → ℤ_[ℓ]ˣ` lifting `det ρ₀`. A *deformation of
`ρ₀` with determinant `δ`* over a local `ℤ_[ℓ]`-algebra `R` which is complete for the topology
defined by the powers of its maximal ideal and comes with a surjective continuous reduction map
`R → 𝐅_ℓ` over `ℤ_[ℓ] → 𝐅_ℓ` is a continuous representation `ρ : π → GLₙ(R)` whose reduction is
conjugate to `ρ₀` and whose determinant is induced by `δ`. The deformation `ρuniv` over `R` is
*universal* when every deformation arises from it along a unique continuous `ℤ_[ℓ]`-algebra
homomorphism.

This file sets up that universal property and records the two ring-theoretic consequences that
turn information about the special fibre of `R` into finiteness and flatness of `R` over
`ℤ_[ℓ]`.

## Main definitions

* `Deformation.IsConjugate` — two matrix representations are conjugate, i.e. isomorphic.
* `Deformation.IsAbsolutelyIrreducible` — a matrix representation over a field is absolutely
  irreducible, in the form given by Burnside's theorem: its image spans the matrix algebra.
* `Deformation.IsUniversalFixedDeterminantDeformation` — the universal property of the
  deformation ring of `ρ₀` with determinant fixed to `δ`.

## Main results

* `Deformation.IsUniversalFixedDeterminantDeformation.not_isUnit_algebraMap` — `ℓ` is not
  invertible in a universal deformation ring.
* `Deformation.IsUniversalFixedDeterminantDeformation.finite` — a universal deformation ring
  with finite special fibre is finite over `ℤ_[ℓ]`.
* `Deformation.IsUniversalFixedDeterminantDeformation.flat` — a universal deformation ring in
  which `ℓ` is a nonzerodivisor is flat over `ℤ_[ℓ]`.

## Implementation notes

Absolute irreducibility is phrased through Burnside's theorem, as the image of the
representation spanning the full matrix algebra over the base field. This is equivalent to
irreducibility of the base change of the representation to every extension field, and avoids
quantifying over extension fields.

Three points where the usual informal description of the universal property is imprecise are
made explicit. The test representations are restricted to *deformations* of `ρ₀`, that is, to
those whose reduction is conjugate to `ρ₀`: for a representation with any other reduction no
classifying map can exist, so the unrestricted reading is false. The classifying map is required
to be *unique*, which is what makes `R` represent the deformation functor rather than merely map
to all deformations; without uniqueness the power series ring `R⟦s⟧`, carrying the pushforward of
`ρuniv`, satisfies every other condition and is not finite over `ℤ_[ℓ]`. And the topology of a
test algebra is pinned to its maximal-adic one, which is the topology that "local complete ring"
refers to; left arbitrary it would admit test algebras with non-adic topologies, for which the
classifying map need neither exist nor be unique.

The test algebras range over the same universe as `R`, so that `R` is itself a test algebra and
the universal property determines it up to isomorphism.

The `ℤ_[ℓ]`-algebra structure is a hypothesis rather than a construction: a complete local ring
whose residue field is `𝐅_ℓ` carries a canonical one, but producing it needs completion
machinery that is not assumed here. Compatibility with the reduction map is required, which pins
it down to that canonical one.

Fixing the determinant is essential: without it the deformation functor of a residual
representation admits unramified twists, which already in rank one produce infinitely many
deformations, and the deformation ring is then not finite over `ℤ_[ℓ]`.
-/

@[expose] public noncomputable section

universe u v

namespace Deformation

/-- Two matrix representations of a group over a commutative ring are isomorphic exactly when
they are conjugate by an invertible matrix. -/
public def IsConjugate {G : Type u} {n : ℕ} {R : Type v} [CommRing R]
    (ρ σ : G → Matrix.GeneralLinearGroup (Fin n) R) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup (Fin n) R, ∀ g, σ g = P * ρ g * P⁻¹

/-- A matrix representation over a field is absolutely irreducible when the span of its image is
the whole matrix algebra. By Burnside's theorem this is equivalent to irreducibility of the base
change of the representation to every extension field. -/
public def IsAbsolutelyIrreducible {G : Type u} {n : ℕ} {F : Type v} [Field F]
    (ρ : G → Matrix.GeneralLinearGroup (Fin n) F) : Prop :=
  Submodule.span F (Set.range fun g => (ρ g : Matrix (Fin n) (Fin n) F)) = ⊤

/-- The universal property of the deformation ring of a residual representation `ρ₀` of a
topological group `π` with determinant fixed to a character `δ` lifting `det ρ₀`: the ring `R` is
local and complete for the topology defined by the powers of its maximal ideal, with residue
field `ZMod ℓ` cut out by the surjective continuous reduction map `reduce` lying over
`ℤ_[ℓ] → ZMod ℓ`; the continuous representation `ρuniv` over `R` reduces to `ρ₀` and has
determinant induced by `δ`; and every continuous deformation of `ρ₀` with determinant `δ` over
such an algebra is the pushforward of `ρuniv` along a unique continuous `ℤ_[ℓ]`-algebra map. -/
public structure IsUniversalFixedDeterminantDeformation
    (ℓ n : ℕ) [Fact ℓ.Prime] (π : Type u) [Group π]
    [TopologicalSpace π] (ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (δ : π →ₜ* ℤ_[ℓ]ˣ)
    (R : Type v) [CommRing R] [IsLocalRing R] [tR : TopologicalSpace R] [Algebra ℤ_[ℓ] R]
    (reduce : R →+* ZMod ℓ)
    (ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R) : Prop where
  /-- The prescribed determinant lifts that of the residual representation. -/
  delta_reduce : ∀ g, Units.map (PadicInt.toZMod : ℤ_[ℓ] →+* ZMod ℓ).toMonoidHom (δ g) =
    Matrix.GeneralLinearGroup.det (ρ₀ g)
  /-- The topology of `R` is the one defined by the powers of its maximal ideal. -/
  isAdicTopology : tR = (IsLocalRing.maximalIdeal R).adicTopology
  /-- `R` is complete for the topology defined by the powers of its maximal ideal. -/
  isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R
  /-- The reduction map is surjective, so it identifies the residue field of `R` with
  `ZMod ℓ`. -/
  reduce_surjective : Function.Surjective reduce
  /-- The reduction map is continuous. -/
  reduce_continuous : Continuous reduce
  /-- The reduction map lies over the reduction `ℤ_[ℓ] → ZMod ℓ`. -/
  reduce_algebraMap : ∀ a : ℤ_[ℓ], reduce (algebraMap ℤ_[ℓ] R a) = PadicInt.toZMod a
  /-- The universal representation is a deformation of `ρ₀`. -/
  reduce_rep : IsConjugate (fun g => Matrix.GeneralLinearGroup.map reduce (ρuniv g))
    (fun g => ρ₀ g)
  /-- The universal representation has the prescribed determinant. -/
  det_rep : ∀ g, Matrix.GeneralLinearGroup.det (ρuniv g) =
    Units.map (algebraMap ℤ_[ℓ] R) (δ g)
  /-- Every continuous deformation of `ρ₀` with determinant `δ` over a local algebra complete for
  its maximal-adic topology and with residue field `ZMod ℓ` is the pushforward of `ρuniv` along a
  unique continuous `ℤ_[ℓ]`-algebra homomorphism. -/
  universal : ∀ (S : Type v) [CommRing S] [IsLocalRing S] [tS : TopologicalSpace S]
      [Algebra ℤ_[ℓ] S], tS = (IsLocalRing.maximalIdeal S).adicTopology →
      IsAdicComplete (IsLocalRing.maximalIdeal S) S →
      ∀ red : S →+* ZMod ℓ, Function.Surjective red → Continuous red →
      (∀ a : ℤ_[ℓ], red (algebraMap ℤ_[ℓ] S a) = PadicInt.toZMod a) →
      ∀ ρ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) S,
        IsConjugate (fun g => Matrix.GeneralLinearGroup.map red (ρ g)) (fun g => ρ₀ g) →
        (∀ g, Matrix.GeneralLinearGroup.det (ρ g) = Units.map (algebraMap ℤ_[ℓ] S) (δ g)) →
        ∃! ψ : R →ₐ[ℤ_[ℓ]] S, Continuous (ψ : R → S) ∧
          IsConjugate (fun g => Matrix.GeneralLinearGroup.map ψ.toRingHom (ρuniv g))
            (fun g => ρ g)

namespace IsUniversalFixedDeterminantDeformation

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

/-- The image of `ℓ` in a universal deformation ring is not invertible: it is killed by the
reduction map, whose target `ZMod ℓ` is not the zero ring. -/
public theorem not_isUnit_algebraMap
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv) :
    ¬ IsUnit (algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ])) := by
  intro hu
  have hz : reduce (algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ])) = 0 := by
    rw [h.reduce_algebraMap, map_natCast, ZMod.natCast_self]
  exact (hz ▸ hu.map reduce : IsUnit (0 : ZMod ℓ)).ne_zero rfl

/-- **Finiteness of a universal deformation ring with finite special fibre.** A universal
deformation ring whose special fibre `R/ℓR` is finite is a finite `ℤ_[ℓ]`-module.

The ring is complete for its maximal-adic topology and `ℓ` lies in its maximal ideal, so it is
separated for the `ℓ`-adic filtration; Stacks Tag 031D applies over the precomplete ring
`ℤ_[ℓ]`. -/
public theorem finite
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (hfin : Finite (R ⧸ (IsLocalRing.maximalIdeal ℤ_[ℓ] • (⊤ : Submodule ℤ_[ℓ] R)))) :
    Module.Finite ℤ_[ℓ] R :=
  PadicInt.finite_of_isAdicComplete_of_finite_quotient R h.isAdicComplete
    h.not_isUnit_algebraMap hfin

/-- **Flatness of a universal deformation ring in which `ℓ` is a nonzerodivisor.** Flatness over
the Bézout domain `ℤ_[ℓ]` is torsion freeness, and every nonzero `p`-adic integer is a unit times
a power of `ℓ`. -/
public theorem flat
    (_h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (hreg : algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∈ nonZeroDivisors R) :
    Module.Flat ℤ_[ℓ] R := by
  refine PadicInt.flat_of_forall_smul_eq_zero fun x hx => ?_
  rw [Algebra.smul_def] at hx
  exact (mem_nonZeroDivisors_iff.mp hreg).1 x hx

end IsUniversalFixedDeterminantDeformation

end Deformation

end
