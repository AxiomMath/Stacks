module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.DualizingTrace

/-!
# What the dualizing trace datum of Tag 0BBU contains

`AlgebraicGeometry.RationalSingularitySituation.DualizingTraceSequence` is the hypothesis that
`AlgebraicGeometry.RationalSingularitySituation.bijective_trace` — [Stacks, Tag 0BBU] — carries:
a trace map `H⁰(X, ω_X) ⟶ ω_A`, its injectivity, an obstruction map
`ω_A ⟶ Ext²_A(H¹(X, 𝒪_X), ω_A)`, and exactness of the two. It stands for the two results the
source's proof quotes: Grauert–Riemenschneider vanishing [Stacks, Tag 0AXD] and the duality
exact sequence [Stacks, Tag 0B4S].

This file measures that datum exactly, and the measurement is that it contains nothing but the
conclusion of `bijective_trace` itself. `H¹(X, 𝒪_X) = 0` is part of Situation
[Stacks, Tag 0B4W] — it is `isZero_firstCohomologyStructureSheafModule`, proved from the
rational singularity hypothesis — so the obstruction group `Ext²_A(H¹(X, 𝒪_X), ω_A)` is a
subsingleton in *every* `RationalSingularitySituation`. Its two obstruction fields therefore
carry no information: the obstruction map can be taken to be zero, and exactness against a zero
map is surjectivity of the trace. What is left is an injective and surjective trace map, i.e. an
isomorphism `H⁰(X, ω_X) ≅ ω_A`, which is what [Stacks, Tag 0BBU] asserts.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation.dualizingTraceSequenceOfIso`: an isomorphism
  `H⁰(X, ω_X) ≅ ω_A` alone builds the whole datum, with no hypothesis on `A`, on `ω_A` or on
  `ω_X`.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.nonempty_dualizingTraceSequence_iff`: the datum
  exists if and only if `H⁰(X, ω_X) ≅ ω_A`. Together with
  `AlgebraicGeometry.RationalSingularitySituation.bijective_trace` this says that the hypothesis
  of `bijective_trace` and its conclusion are the same statement. The reading of
  [Stacks, Tag 0BBU] that keeps the source's `ω_X` — the normalized one — is
  `AlgebraicGeometry.RationalSingularitySituation.bijective_trace_of_normalized`, which has no
  such datum; see the implementation notes.
* `AlgebraicGeometry.RationalSingularitySituation`
  `.nonempty_iso_globalSectionsModule_of_dualizingTraceSequence`: a datum over a fixed `ω_A` pins
  the global sections of its second argument down up to isomorphism — two modules on `X` both
  admitting the datum over the same `ω_A` have isomorphic global sections.

## Implementation notes

**Why the datum cannot be removed from the dualizing hypotheses alone.** The last result above
is an obstruction to proving `Nonempty (S.DualizingTraceSequence ωA ωX)` from the hypotheses that
`bijective_trace` already has, namely that `ω_A` and `ω_X` are *some* dualizing modules
(`Stacks.Duality.IsDualizingRingModule`, `Stacks.Duality.IsDualizingModule`): such a proof would
force any two dualizing modules on `X` to have isomorphic global sections. On the blowup of
`Spec(A)` in the maximal ideal they do not, and no hypothesis on `ω_A` repairs that, the
obstruction above holding `ω_A` fixed.

Being a dualizing complex on a scheme is the local condition
`Stacks.Duality.IsDualizingComplex`, and over a ring an invertible twist of a dualizing complex
is dualizing again ([Stacks, Tag 0A7F] read backwards,
`Dualizing.isDualizingComplex_tensor_of_isInvertible`), so the dualizing modules on `X` form an
orbit under the invertible `𝒪_X`-modules, among which `ℐ_E` — the exceptional divisor being an
effective Cartier divisor — is one. Take `A = k[[x, y, z]]/(xy - z²)`, the cone over a smooth
conic: a two-dimensional local normal Nagata domain defining a rational singularity, not regular.
Its blowup `X` at the maximal ideal is the total space of the tautological bundle of that conic,
so it is *regular*; over a regular ring the ring itself is a dualizing complex, so `𝒪_X` is a
dualizing module on `X`, and therefore so is the invertible `ℐ_E`. But
`AlgebraicGeometry.isIso_globalFunctions_blowUpToBase_residuePoint` gives `H⁰(X, 𝒪_X) ≅ A` and
`AlgebraicGeometry.ker_exceptionalIdeal_subschemeι_appTop` gives `H⁰(X, ℐ_E) ≅ 𝔪` — both
[Stacks, Tag 0B4Y] — while `𝔪 ≅ A` would make `𝔪` principal and force dimension at most one.

Pinning `ω_X` down is exactly the normalization that the source performs: its `ω_X` is the
dualizing module of `X` *normalized relative to* `ω_A`, not an arbitrary dualizing module. That
normalization is `AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule` of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities`
`/NormalizedDualizingModule.lean`, and with it the datum *is* removed:
`AlgebraicGeometry.RationalSingularitySituation.dualizingTraceSequenceOfNormalized` constructs
it. **The normalization does not require constructing `f^!`.** It is the condition that the
duality pairing of the trace be bijective against every quasi-coherent module with vanishing
first cohomology, which is the shape Grothendieck duality takes for `ω_X[2] = f^!(ω_A[2])` with
the shift removed; [Stacks, Tag 0A9E] is needed to *produce* an `ω_X` satisfying it, not to state
it, nor to derive [Stacks, Tag 0BBU] from it, nor to prove that it determines `ω_X` up to a
unique trace-compatible isomorphism
(`AlgebraicGeometry.RationalSingularitySituation.normalizedDualizingIso`). This file
therefore tests the generality of `bijective_trace`, not
[Stacks, Tag 0BBU].

**Nothing is registered here.** Neither [Stacks, Tag 0AXD] nor [Stacks, Tag 0B4S] is proved or
restated below; what is examined is the shape of a hypothesis of this development, which is not
the content of any tag.

## References

* [Stacks Project, Tag 0BBU](https://stacks.math.columbia.edu/tag/0BBU)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-- **An isomorphism `H⁰(X, ω_X) ≅ ω_A` builds the dualizing trace datum.** The trace is the
isomorphism, injectivity is one half of its bijectivity, the obstruction map is zero — the
obstruction group `Ext²_A(H¹(X, 𝒪_X), ω_A)` is zero in every `RationalSingularitySituation` — and
exactness against the zero map is the other half of the bijectivity. -/
public def dualizingTraceSequenceOfIso (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules)
    (e : S.globalSectionsModule ωX ≅ ωA) : S.DualizingTraceSequence ωA ωX where
  trace := e.hom
  injective_trace := (ConcreteCategory.bijective_of_isIso e.hom).1
  obstruction := 0
  exact b := iff_of_true (AddMonoidHom.zero_apply b)
    ((ConcreteCategory.bijective_of_isIso e.hom).2 b)

/-- **The dualizing trace datum is exactly [Stacks, Tag 0BBU].** Forwards it is
`bijective_trace` with the two dualizing hypotheses dropped, both being unused there: the trace
is injective by hypothesis and surjective because the obstruction group vanishes, hence
invertible. Backwards it is `dualizingTraceSequenceOfIso`. -/
public theorem nonempty_dualizingTraceSequence_iff (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules) :
    Nonempty (S.DualizingTraceSequence ωA ωX) ↔
      Nonempty (S.globalSectionsModule ωX ≅ ωA) :=
  ⟨fun ⟨D⟩ => ⟨@asIso _ _ _ _ D.trace ((ConcreteCategory.isIso_iff_bijective D.trace).2
      ⟨D.injective_trace, S.surjective_trace ωA ωX D⟩)⟩,
    fun ⟨e⟩ => ⟨S.dualizingTraceSequenceOfIso ωA ωX e⟩⟩

/-- **The dualizing trace datum determines the global sections of the module on `X`.** Two
`𝒪_X`-modules admitting the datum over the same `ω_A` have isomorphic global sections, both
being `ω_A`. -/
public theorem nonempty_iso_globalSectionsModule_of_dualizingTraceSequence
    (ωA : ModuleCat.{u} S.A) (ωX ωX' : S.X.Modules)
    (D : S.DualizingTraceSequence ωA ωX) (D' : S.DualizingTraceSequence ωA ωX') :
    Nonempty (S.globalSectionsModule ωX ≅ S.globalSectionsModule ωX') := by
  obtain ⟨e⟩ := (S.nonempty_dualizingTraceSequence_iff ωA ωX).1 ⟨D⟩
  obtain ⟨e'⟩ := (S.nonempty_dualizingTraceSequence_iff ωA ωX').1 ⟨D'⟩
  exact ⟨e ≪≫ e'.symm⟩

end AlgebraicGeometry.RationalSingularitySituation

end

end
