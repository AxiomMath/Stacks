module

public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelAnnihilation
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to rational singularities from annihilation of the trace cokernel

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two carrying a dualizing module
`ω_A`. For a modification `f : X ⟶ Spec A` with `X` normal, the dualizing module `ω_X` of `X`
normalized relative to `ω_A` carries a trace map `Γ(X, ω_X) ⟶ ω_A`, and duality identifies the
cokernel of that trace with the Matlis dual `Hom_A(H¹(X, 𝒪_X), E)` of the first cohomology of
the structure sheaf. Hence a nonzero `d ∈ A` annihilating every such cokernel annihilates every
`H¹(X, 𝒪_X)`, and the lengths of those modules are then bounded uniformly in `X`: reduction to
rational singularities is possible for `A`.

## Main definitions

* `Stacks.ResolutionOfSurfaces.TraceCokernelDuality` collects the duality input of the argument:
  the dualizing module `ω_X` of each scheme over `Spec A`, the trace map `Γ(X, ω_X) ⟶ ω_A`, and
  the presentation of the Matlis dual of `H¹(X, 𝒪_X)` as a quotient of the cokernel of the trace
  for every normal modification.

## Main results

* `isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero`, in the namespace
  `Stacks.ResolutionOfSurfaces`, is [Stacks, Tag 0B4S]: reduction to rational singularities is
  possible for a local normal Nagata domain of dimension two with a dualizing module as soon as
  a nonzero element of the ring annihilates the cokernel of the trace map of every normal
  modification of its spectrum.

## Implementation notes

The chain of the source's proof is realized by the two results of this directory it passes
through. The annihilation of the Matlis dual is carried to the module itself by
`Dualizing.smul_eq_zero_of_matlisDual_smul_eq_zero`, and the bound on the lengths of the
`d`-torsion submodules of `H¹(X, 𝒪_X)` is assembled into the conclusion by
`Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_matlisDual_smul_eq_zero`.
The bound is taken in the shape in which [Stacks, Tag 0AXJ] produces it — a bound on the lengths
of the cokernels of `A ⟶ H⁰(Z, 𝒪_Z)`, for `Z ⊂ X` cut out by `d` — and translated into a bound
on the `d`-torsion of `H¹(X, 𝒪_X)` by the identification [Stacks, Tag 0AXK],
`AlgebraicGeometry.length_quotient_baseToZeroSchemeSections_eq`, which is where the hypothesis
`d ≠ 0` is used.

The dualizing modules of the schemes over `Spec A` are a parameter rather than a construction,
as in `Stacks.ResolutionOfSurfaces.BlowupDualizingData`: their existence is [Stacks, Tag 0B4R]
and the normalization relative to `ω_A` is the construction of [Stacks, Section 0AU3], and a
dualizing module is pinned only up to shift and an invertible twist, so nothing identifies a
particular module with `ω_X` except that normalization. The trace map `Rf_*ω_X ⟶ ω_A`
([Stacks, Section 0AWG]) is a map on global sections because Grauert–Riemenschneider vanishing
([Stacks, Tag 0AXD]) gives `Rf_*ω_X = f_*ω_X`, and it is in that form — a map
`Γ(X, ω_X) ⟶ ω_A` — that it appears as a field.

The identification of the cokernel of the trace with the Matlis dual of `H¹(X, 𝒪_X)` is the
remaining field. It is the composite of three steps of the source: duality
`Rf_*ω_X = RHom_A(Rf_*𝒪_X, ω_A)` ([Stacks, Tag 0AUE]) applied to the triangle
`A ⟶ Rf_*𝒪_X ⟶ R¹f_*𝒪_X[-1] ⟶ A[1]`, which produces the short exact sequence
`0 ⟶ f_*ω_X ⟶ ω_A ⟶ Ext²_A(R¹f_*𝒪_X, ω_A) ⟶ 0`; local duality ([Stacks, Tag 0AAK]), which
identifies that `Ext²` with `Hom_A(R¹f_*𝒪_X, E)` because `R¹f_*𝒪_X` is supported at `𝔪`; and the
affineness of the base, which makes `R¹f_*𝒪_X` the module `H¹(X, 𝒪_X)`. Only surjectivity onto
the Matlis dual is asked for, since that is what transports the annihilation of the cokernel.

The data fields are given for every morphism to `Spec A` and the two conditions only for the
normal modifications, which is the generality in which the source uses them: data on the normal
modifications alone extends to all morphisms by the zero module and the zero map.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces

/-- The duality input to the argument of [Stacks, Tag 0B4S], for a ring `A` with dualizing module
`ω_A` and `E` an injective hull of the residue field of `A`.

The first two fields are the dualizing module `ω_X` of a scheme over `Spec A`, normalized
relative to `ω_A` ([Stacks, Tags 0B4R] and [Section 0AU3]), and the trace map
`Γ(X, ω_X) ⟶ ω_A`, which is a map on global sections because Grauert–Riemenschneider vanishing
([Stacks, Tag 0AXD]) makes `Rf_*ω_X = f_*ω_X`.

The last two express the cokernel of the trace of a normal modification as a presentation of the
Matlis dual `Hom_A(H¹(X, 𝒪_X), E)`: duality ([Stacks, Tag 0AUE]) places the trace in a short
exact sequence `0 ⟶ f_*ω_X ⟶ ω_A ⟶ Ext²_A(R¹f_*𝒪_X, ω_A) ⟶ 0`, and local duality
([Stacks, Tag 0AAK]) identifies that `Ext²` with the Matlis dual, `R¹f_*𝒪_X` being supported at
the maximal ideal. -/
structure TraceCokernelDuality (A : Type u) [CommRing A] [IsDomain A]
    (E ωA : ModuleCat.{u} A) where
  /-- The dualizing module `ω_X` of a scheme over `Spec A`, normalized relative to `ω_A`. -/
  dualizingSheaf : (X : Scheme.{u}) → (X ⟶ Spec (.of A)) → X.Modules
  /-- On a normal modification the assigned module is indeed a dualizing module. -/
  isDualizingModule : ∀ (X : Scheme.{u}) [IsNormal X] [IsLocallyNoetherian X]
      (f : X ⟶ Spec (.of A)), IsModification f →
    Stacks.Duality.IsDualizingModule (dualizingSheaf X f)
  /-- The trace map `Γ(X, ω_X) ⟶ ω_A` on global sections. -/
  trace : (X : Scheme.{u}) → (f : X ⟶ Spec (.of A)) →
    (globalSectionsAsBaseModule X f (dualizingSheaf X f) ⟶ ωA)
  /-- The Matlis dual `Hom_A(H¹(X, 𝒪_X), E)` as a quotient of the cokernel of the trace. -/
  matlisDualOfCokernel : (X : Scheme.{u}) → (f : X ⟶ Spec (.of A)) →
    (↥ωA ⧸ LinearMap.range (trace X f).hom) →ₗ[A]
      ↥(ModuleCat.of A (firstCohomologyAsBaseModule X f ⟶ E))
  /-- For a normal modification the cokernel of the trace covers the Matlis dual. -/
  surjective_matlisDualOfCokernel : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)),
    IsModification f → Function.Surjective (matlisDualOfCokernel X f)

/-- **Stacks Project, Tag 0B4S.** Let `A` be a local normal Nagata domain of dimension two with a
dualizing module `ω_A`. If some nonzero `d ∈ A` annihilates the cokernel of the trace map
`Γ(X, ω_X) ⟶ ω_A` for every modification `f : X ⟶ Spec A` with `X` normal, then reduction to
rational singularities is possible for `A`: the `A`-module lengths of `H¹(X, 𝒪_X)` admit a common
finite bound over all such `X`.

Duality presents the Matlis dual `Hom_A(H¹(X, 𝒪_X), E)` as a quotient of the cokernel of the
trace — the field `TraceCokernelDuality.matlisDualOfCokernel` of `D` — so `d` annihilates that
dual, and an injective hull of the residue field being a cogenerator, `d` then annihilates
`H¹(X, 𝒪_X)` itself. Each `H¹(X, 𝒪_X)` is therefore its own `d`-torsion submodule, and the
uniform bound `hbound` on the lengths of the cokernels of `A ⟶ H⁰(Z, 𝒪_Z)`, for `Z ⊂ X` cut out
by `d`, bounds their lengths through the identification [Stacks, Tag 0AXK]. -/
@[stacks 0B4S "reduction to rational singularities from a nonzero element annihilating the \
cokernel of the trace map of every normal modification; the identification of that cokernel with \
the Matlis dual of H¹(X, 𝒪_X) — Grauert–Riemenschneider vanishing (Tag 0AXD) with duality \
(Tag 0AUE) and local duality (Tag 0AAK) — is the field matlisDualOfCokernel of the hypothesis D, \
and the uniform bound on the lengths of the cokernels of A ⟶ H⁰(Z, 𝒪_Z) (Tag 0AXJ) is the \
hypothesis hbound"]
theorem isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
    (_hdim : ringKrullDim A = 2)
    (E : ModuleCat.{u} A) (i : Dualizing.residueFieldModule.{u, u} A ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (ωA : ModuleCat.{u} A) (_hωA : Stacks.Duality.IsDualizingRingModule A ωA)
    (D : TraceCokernelDuality A E ωA) (d : A) (hd : d ≠ 0)
    (hcoker : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ z : ↥ωA ⧸ LinearMap.range (D.trace X f).hom, d • z = 0)
    (hbound : ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)),
      IsModification f →
      Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f d) ⧸
        LinearMap.range (baseToZeroSchemeSections X f d)) ≤ N) :
    IsReductionToRationalSingularitiesPossible A := by
  obtain ⟨N, hN⟩ := hbound
  refine isReductionToRationalSingularitiesPossible_of_matlisDual_smul_eq_zero A E i hi d N
    ?_ ?_
  · intro X _ f hf φ
    obtain ⟨z, hz⟩ := D.surjective_matlisDualOfCokernel X f hf φ
    rw [← hz, ← map_smul, hcoker X f hf z, map_zero]
  · intro X _ f hf
    rw [← length_quotient_baseToZeroSchemeSections_eq X f hf hd]
    exact hN X f hf

end Stacks.ResolutionOfSurfaces

end
