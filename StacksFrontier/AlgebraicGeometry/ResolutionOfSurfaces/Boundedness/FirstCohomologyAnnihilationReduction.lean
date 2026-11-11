module

public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelAnnihilation
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsNormalization
public import StacksFrontier.RingTheory.Nagata.Defs

/-!
# A uniform annihilator of `H¹(X, 𝒪_X)` bounds its length, with no bound assumed

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two and let `d ∈ A` be nonzero. If
`d` annihilates `H¹(X, 𝒪_X)` for every modification `f : X ⟶ Spec A` with `X` normal, then
reduction to rational singularities is possible for `A`. This is the whole of the argument of
[Stacks, Tag 0B4S] downstream of its duality step, and it is unconditional: the uniform bound on
lengths which
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero`
of `ResolutionOfSurfaces/Boundedness/TraceCokernelReduction.lean` carries as the hypothesis
`hbound` is [Stacks, Tag 0AXJ], which the source cites rather than assumes, and it is discharged
here from the dimension hypothesis; and no injective hull of the residue field appears, the
existence of one being [Stacks, Tag 08Y3].

## Main results

All in the namespace `Stacks.ResolutionOfSurfaces`.

* `isReductionToRationalSingularitiesPossible_of_forall_smul_firstCohomology_eq_zero` — a nonzero
  element annihilating `H¹(X, 𝒪_X)` for every normal modification makes reduction to rational
  singularities possible. No bound and no injective hull are assumed.
* `smul_eq_zero_of_exists_surjective_matlisDual` — if a module `C` annihilated by `d` covers the
  Matlis dual `Hom_A(M, E)` for some injective hull `E` of the residue field, then `d`
  annihilates `M`. The hull is produced rather than assumed.
* `isReductionToRationalSingularitiesPossible_of_traceCokernel_matlisDual` —
  [Stacks, Tag 0B4S] with both `hbound` and the injective hull discharged, so that the duality
  step is the only input left.

## What is proved, and what the duality step still owes

The source's proof runs: Grauert–Riemenschneider vanishing ([Stacks, Tag 0AXD]) makes
`Rf_*ω_X = f_*ω_X`, so the trace is a map `Γ(X, ω_X) ⟶ ω_A`; duality ([Stacks, Tag 0AUE]) applied
to the triangle `A ⟶ Rf_*𝒪_X ⟶ R¹f_*𝒪_X[-1] ⟶ A[1]` places it in a short exact sequence
`0 ⟶ f_*ω_X ⟶ ω_A ⟶ Ext²_A(R¹f_*𝒪_X, ω_A) ⟶ 0`; local duality ([Stacks, Tag 0AAK]) identifies
that `Ext²` with the Matlis dual `Hom_A(R¹f_*𝒪_X, E)`, the module being supported at `𝔪`; `E`
being a cogenerator, `d` then annihilates `R¹f_*𝒪_X = H¹(X, 𝒪_X)` itself; and the lengths are
bounded by [Stacks, Tag 0AXJ] through the identification [Stacks, Tag 0AXK].

Everything from the cogenerator step onwards is proved here outright. The sole remaining input is
the short exact sequence, and in the form in which it is consumed — a surjection of the cokernel
of the trace onto the Matlis dual of `H¹(X, 𝒪_X)` — it is the hypothesis `hduality` of the last
statement below. That sequence is proved nowhere in this development: it is the only content of
the fields `matlisDualOfCokernel` and `surjective_matlisDualOfCokernel` of
`Stacks.ResolutionOfSurfaces.TraceCokernelDuality`, and of the fields `obstruction` and `exact`
of `AlgebraicGeometry.RationalSingularitySituation.DualizingTraceSequence`, both of which carry
it rather than derive it. Its scheme-level ingredient *is* available —
`Stacks.Duality.NormalizedOnOpens.sheafHomDualizingIsoOfMinusCohNagata` is [Stacks, Tag 0AUE]
part (6), and `Stacks.Duality.derivedPushforwardUnitIsoSheafHomPushforwardOfIsDualizingComplex`
is `Rf_*𝒪_X ≅ R𝓗om_{𝒪_Y}(Rf_*ω_X^•, K)` — but neither is read over the affine base as a
statement about `A`-modules, and the dualization of the triangle is not performed.

**No `@[stacks 0B4S]` attribute is placed here.** The last statement still carries `hduality`,
which is a result the source cites, so it is not an unconditional statement of the tag; the
tag is registered on
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_smul_baseTraceCokernel_eq_zero`
of `TraceCokernelImageLift.lean`, where the duality step is proved. What the statements here
remove from
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero`
of `TraceCokernelReduction.lean` is `hbound` and the injective hull, neither of which is a
hypothesis of the tag.

## Implementation notes

`hduality` quantifies over every injective hull of the residue field rather than fixing one. That
costs nothing: hulls are unique up to isomorphism ([Stacks, Tag 08Y4],
`Module.exists_iso_of_isInjectiveHull`), so a surjection onto the Matlis dual against one hull
transports to any other. Quantifying is what lets the hull be produced inside the proof instead
of appearing in the statement, and it is the only reason `E` is absent from
`isReductionToRationalSingularitiesPossible_of_traceCokernel_matlisDual`.

The dualizing modules `ω_X` of the schemes over `Spec A` and their traces are plain data —
a family of modules and a family of maps — with no condition attached to either. They are what
is needed to *state* the tag's hypothesis on `d`, and nothing about them is used: the proof only
moves the annihilation of the cokernel of the trace across `hduality`.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 08Y3](https://stacks.math.columbia.edu/tag/08Y3)
* [Stacks Project, Tag 08Y4](https://stacks.math.columbia.edu/tag/08Y4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **A nonzero element annihilating every `H¹(X, 𝒪_X)` makes reduction to rational singularities
possible.** Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two and let `d ∈ A` be
nonzero. If `d` annihilates `H¹(X, 𝒪_X)` for every modification `f : X ⟶ Spec A` with `X`
normal, then the `A`-module lengths of those `H¹(X, 𝒪_X)` admit a common finite bound.

Each `H¹(X, 𝒪_X)` is its own `d`-torsion submodule, whose length is that of the cokernel of
`A ⟶ H⁰(Z, 𝒪_Z)` for `Z ⊂ X` cut out by `d` ([Stacks, Tag 0AXK],
`AlgebraicGeometry.length_quotient_baseToZeroSchemeSections_eq`, which is where `d ≠ 0` is used),
and those lengths are uniformly bounded by [Stacks, Tag 0AXJ],
`AlgebraicGeometry.exists_uniform_bound_length_quotient_baseToZeroSchemeSections`, which is where
the dimension hypothesis is used. -/
public theorem isReductionToRationalSingularitiesPossible_of_forall_smul_firstCohomology_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
    (hdim : ringKrullDim A = 2) (d : A) (hd : d ≠ 0)
    (hkill : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ x : firstCohomologyAsBaseModule X f, d • x = 0) :
    IsReductionToRationalSingularitiesPossible A := by
  obtain ⟨N, hN⟩ := exists_uniform_bound_length_quotient_baseToZeroSchemeSections hdim hd
  refine ⟨N, fun X _ f hf => ?_⟩
  have htop : Submodule.torsionBy A (firstCohomologyAsBaseModule X f) d = ⊤ :=
    eq_top_iff.mpr fun x _ => (Submodule.mem_torsionBy_iff _ _).mpr (hkill X f hf x)
  have hb := hN X f hf
  rwa [length_quotient_baseToZeroSchemeSections_eq X f hf hd, htop, Module.length_top] at hb

/-- **A module annihilated by `d` which covers a Matlis dual of `M` makes `d` annihilate `M`.**
Let `(A, 𝔪, κ)` be local, let `M` be an `A`-module and let `C` be an `A`-module annihilated by
`d`. If for some injective hull `E` of `κ` there is a surjection `C → Hom_A(M, E)`, then `d`
annihilates `M`.

The hull is not a hypothesis: one exists by [Stacks, Tag 08Y3],
`Module.exists_isInjectiveHull`, and `hsurj` is asked of every hull, so it applies to the one
produced. Surjectivity carries the annihilation of `C` to `Hom_A(M, E)`, and
`Dualizing.smul_eq_zero_of_matlisDual_smul_eq_zero` carries it from there to `M`, an injective
hull of the residue field being a cogenerator. -/
public theorem smul_eq_zero_of_exists_surjective_matlisDual
    (A : Type u) [CommRing A] [IsLocalRing A] (M : ModuleCat.{u} A)
    (C : Type u) [AddCommGroup C] [Module A C] (d : A)
    (hC : ∀ z : C, d • z = 0)
    (hsurj : ∀ (E : ModuleCat.{u} A) (i : Dualizing.residueFieldModule.{u, u} A ⟶ E)
      (_ : Mono i), Module.IsInjectiveHull i →
      ∃ ψ : C →ₗ[A] ↥(ModuleCat.of A (M ⟶ E)), Function.Surjective ψ)
    (x : M) : d • x = 0 := by
  obtain ⟨E, i, hmono, hi⟩ :=
    Module.exists_isInjectiveHull A (Dualizing.residueFieldModule.{u, u} A)
  let : Mono i := hmono
  have hi' : Module.IsInjectiveHull i := hi
  obtain ⟨ψ, hψ⟩ := hsurj E i hmono hi'
  refine Dualizing.smul_eq_zero_of_matlisDual_smul_eq_zero.{u, u} A E i hi' M d ?_ x
  intro φ
  obtain ⟨z, hz⟩ := hψ φ
  rw [← hz, ← map_smul, hC z, map_zero]

/-- **Stacks Project, Tag 0B4S, with the uniform length bound and the injective hull discharged.**
Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two, let `ω_A` be an `A`-module, let
`ω_X` be a module on each scheme over `Spec A` with a trace `Γ(X, ω_X) ⟶ ω_A`, and let `d ∈ A` be
nonzero annihilating the cokernel of every such trace at a normal modification. If for each
normal modification the cokernel of the trace covers the Matlis dual of `H¹(X, 𝒪_X)`, then
reduction to rational singularities is possible for `A`.

This is
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero`
with its hypothesis `hbound` supplied from `ringKrullDim A = 2` by [Stacks, Tag 0AXJ] and with
the injective hull `E` of the residue field produced by [Stacks, Tag 08Y3] rather than assumed.
Neither is a hypothesis of the tag. What remains, `hduality`, is the short exact sequence
`0 ⟶ f_*ω_X ⟶ ω_A ⟶ Ext²_A(R¹f_*𝒪_X, ω_A) ⟶ 0` of [Stacks, Tag 0AUE] composed with the local
duality of [Stacks, Tag 0AAK]; it is a result the source cites, it is not proved in this file,
and it is why no `@[stacks 0B4S]` attribute is placed on this statement. The tag is
`Stacks.ResolutionOfSurfaces`
`.isReductionToRationalSingularitiesPossible_of_smul_baseTraceCokernel_eq_zero`
of `TraceCokernelImageLift.lean`. -/
public theorem isReductionToRationalSingularitiesPossible_of_traceCokernel_matlisDual
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
    (hdim : ringKrullDim A = 2) (ωA : ModuleCat.{u} A)
    (ω : (X : Scheme.{u}) → (X ⟶ Spec (.of A)) → X.Modules)
    (T : (X : Scheme.{u}) → (f : X ⟶ Spec (.of A)) →
      (globalSectionsAsBaseModule X f (ω X f) ⟶ ωA))
    (d : A) (hd : d ≠ 0)
    (hcoker : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ z : ↥ωA ⧸ LinearMap.range (T X f).hom, d • z = 0)
    (hduality : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ (E : ModuleCat.{u} A) (i : Dualizing.residueFieldModule.{u, u} A ⟶ E) (_ : Mono i),
      Module.IsInjectiveHull i →
      ∃ ψ : (↥ωA ⧸ LinearMap.range (T X f).hom) →ₗ[A]
        ↥(ModuleCat.of A (firstCohomologyAsBaseModule X f ⟶ E)), Function.Surjective ψ) :
    IsReductionToRationalSingularitiesPossible A :=
  isReductionToRationalSingularitiesPossible_of_forall_smul_firstCohomology_eq_zero A hdim d hd
    fun X _ f hf =>
      smul_eq_zero_of_exists_surjective_matlisDual A (firstCohomologyAsBaseModule X f)
        (↥ωA ⧸ LinearMap.range (T X f).hom) d (hcoker X f hf) (hduality X f hf)

end Stacks.ResolutionOfSurfaces

end
