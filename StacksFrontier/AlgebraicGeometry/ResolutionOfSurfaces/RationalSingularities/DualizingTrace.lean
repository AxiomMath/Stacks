module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.StructureSheafCohomology

/-!
# The dualizing module of a rational surface singularity

In Situation [Stacks, Tag 0B4W] — a two-dimensional local normal Nagata domain `A` defining a
rational singularity and a modification `f : X ⟶ Spec(A)` with `X` normal — and for `A` carrying a
dualizing module `ω_A`, [Stacks, Tag 0BBU] asserts that the trace map `H⁰(X, ω_X) ⟶ ω_A` on the
dualizing module of `X` is an isomorphism.

**[Stacks, Tag 0BBU] itself is not proved here.** It is
`AlgebraicGeometry.RationalSingularitySituation.bijective_normalizedTrace`
(`NormalizedDualizingTrace.lean`), for the dualizing module normalized relative to `ω_A`
([Stacks, Remark 0B4R]) and the trace of Grothendieck duality, with nothing carried. This file
keeps the duality-sequence form of the argument, `bijective_trace`, whose hypothesis `D` is
equivalent to the conclusion (`nonempty_dualizingTraceSequence_iff`); it carries no tag.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation.globalSectionsModule` is `H⁰(X, ℱ)` as an
  `A`-module.
* `AlgebraicGeometry.RationalSingularitySituation.firstCohomologyStructureSheafModule` is
  `H¹(X, 𝒪_X)` as an `A`-module.
* `AlgebraicGeometry.RationalSingularitySituation.DualizingTraceSequence` is the duality exact
  sequence that the source's proof starts from.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.isZero_firstCohomologyStructureSheafModule`:
  `H¹(X, 𝒪_X) = 0`, because `A` defines a rational singularity.
* `AlgebraicGeometry.RationalSingularitySituation.surjective_trace`: the trace of a
  `DualizingTraceSequence` is surjective, the obstruction group being zero.
* `AlgebraicGeometry.RationalSingularitySituation.bijective_trace`: the trace of a
  `DualizingTraceSequence` is bijective. This is the last step of the source's proof of
  [Stacks, Tag 0BBU], not the tag, which is `bijective_normalizedTrace`.

## Implementation notes

Cohomology is `Hⁱ(X, ℱ) = ((moduleGlobalSections X).rightDerivedPlus i).obj ℱ`, a module over
`Γ(X, 𝒪_X)`; the `A`-module structure is obtained by restricting scalars along the ring map
`A ⟶ Γ(X, 𝒪_X)` induced by `f`, exactly as `AlgebraicGeometry.cohomologyOverField` does for a
base field.

**The hypothesis `DualizingTraceSequence`.** The source's proof of [Stacks, Tag 0BBU] is:
Grauert–Riemenschneider vanishing, [Stacks, Tag 0AXD], gives `Rf_*ω_X = f_*ω_X`; duality — the
argument of [Stacks, Tag 0B4S] — then places the trace in a short exact sequence
`0 ⟶ f_*ω_X ⟶ ω_A ⟶ Ext²_A(R¹f_*𝒪_X, ω_A) ⟶ 0`;
and `R¹f_*𝒪_X = 0` because `A` defines a rational singularity, so the trace is an isomorphism.
The output of the first two steps is the data of a `DualizingTraceSequence`: the injectivity of
the trace together with exactness of `H⁰(X, ω_X) ⟶ ω_A ⟶ Ext²_A(H¹(X, 𝒪_X), ω_A)`. Tag 0AXD is
`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_of_properRightAdjoint_isoShiftTwo`,
proved in the vanishing situation of [Stacks, Tag 0AX8] for `ω_X` normalized by
`f^×(ω̃_A^•) ≅ ω_X[2]`, and Tag 0B4S is
`isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero` in the namespace
`Stacks.ResolutionOfSurfaces`, under hypotheses of its own; neither is stated in this situation,
so neither produces the datum. Nothing in the
datum mentions the vanishing of `H¹(X, 𝒪_X)`, which is proved here.

**For the `ω_X` the source names, the datum is a theorem.** The source's `ω_X` is the dualizing
module normalized relative to `ω_A`, and that normalization is
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule`: relative duality in
degree zero for the trace. From it,
`AlgebraicGeometry.RationalSingularitySituation.bijective_trace_of_normalized` gives
[Stacks, Tag 0BBU] outright and
`AlgebraicGeometry.RationalSingularitySituation.dualizingTraceSequenceOfNormalized` builds the
datum below. So `D` is what remains of [Stacks, Tag 0BBU] once `ω_X` is weakened from *the*
dualizing module to *a* dualizing module, which is the generality of `bijective_trace`.

**The datum does, however, amount to the conclusion.** The vanishing of `H¹(X, 𝒪_X)` is a
consequence of Situation [Stacks, Tag 0B4W] itself, so the obstruction group
`Ext²_A(H¹(X, 𝒪_X), ω_A)` is a subsingleton in *every* `RationalSingularitySituation` and the
datum's obstruction fields carry no information: an isomorphism `H⁰(X, ω_X) ≅ ω_A` builds the
whole datum back. This is
`AlgebraicGeometry.RationalSingularitySituation.nonempty_dualizingTraceSequence_iff`, and the
obstruction to constructing the datum from the dualizing hypotheses alone — `ω_X` is not
normalized relative to `ω_A` there — is
`nonempty_iso_globalSectionsModule_of_dualizingTraceSequence`, in the same namespace.

**The base is affine**, so `R¹f_*𝒪_X` is the quasi-coherent module associated with `H¹(X, 𝒪_X)`
and its vanishing is the vanishing of `H¹(X, 𝒪_X)`; the latter is the spelling used here, and it
is `AlgebraicGeometry.RationalSingularitySituation.isZero_firstCohomologyStructureSheaf`.

**The second clause of the tag.** The source adds that the inverse of the trace induces a
canonical map `f^*ω_A ⟶ ω_X`. That is
`AlgebraicGeometry.RationalSingularitySituation.dualizingPullbackMap`, the adjunct of the inverse
trace under the composite of the affine comparison and the pullback–pushforward adjunction for
module sheaves; it takes the same hypothesis `D` as the trace isomorphism, which is all the
inverse trace needs.

## References

* [Stacks Project, Tag 0BBU](https://stacks.math.columbia.edu/tag/0BBU)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

attribute [local instance] HasDerivedCategory.standard

/-- The ring map `A ⟶ Γ(X, 𝒪_X)` induced by the modification `f : X ⟶ Spec(A)`. -/
public def structureRingHom : S.A →+* Γ(S.X, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.A)).inv ≫ S.f.appTop).hom

/-- The global sections of a module on `X`, as a module over `A` through `f`. -/
public def globalSectionsModule (F : S.X.Modules) : ModuleCat.{u} S.A :=
  (ModuleCat.restrictScalars S.structureRingHom).obj ((moduleGlobalSections S.X).obj F)

/-- `H¹(X, 𝒪_X)`, as a module over `A` through `f`. On the affine base `Spec(A)` this is the
module whose associated quasi-coherent module is `R¹f_*𝒪_X`. -/
public def firstCohomologyStructureSheafModule : ModuleCat.{u} S.A :=
  (ModuleCat.restrictScalars S.structureRingHom).obj
    (((moduleGlobalSections S.X).rightDerivedPlus 1).obj (SheafOfModules.unit S.X.ringCatSheaf))

/-- In Situation [Stacks, Tag 0B4W] the first cohomology of the structure sheaf vanishes, because
`A` defines a rational singularity. -/
public theorem isZero_firstCohomologyStructureSheafModule :
    IsZero S.firstCohomologyStructureSheafModule :=
  Functor.map_isZero (ModuleCat.restrictScalars S.structureRingHom)
    S.isZero_firstCohomologyStructureSheaf

/-- The duality input to the proof of [Stacks, Tag 0BBU]: a trace map from the global sections of
a dualizing module on `X` to a dualizing module of `A`, injective and with the obstruction to its
surjectivity landing in `Ext²_A(H¹(X, 𝒪_X), ω_A)`.

This packages the output of the two results the source's proof quotes: Grauert–Riemenschneider
vanishing [Stacks, Tag 0AXD], which makes `Rf_*ω_X = f_*ω_X`, and the duality exact sequence of
[Stacks, Tag 0B4S]. -/
public structure DualizingTraceSequence (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules) where
  /-- The trace map on global sections. -/
  trace : S.globalSectionsModule ωX ⟶ ωA
  /-- The trace is injective. -/
  injective_trace : Function.Injective trace.hom
  /-- The obstruction map to `Ext²_A(H¹(X, 𝒪_X), ω_A)`. -/
  obstruction : ωA →+ Abelian.Ext.{u} S.firstCohomologyStructureSheafModule ωA 2
  /-- The trace and the obstruction form an exact sequence. -/
  exact : Function.Exact trace.hom obstruction

/-- **The trace of a `DualizingTraceSequence` is surjective.** `H¹(X, 𝒪_X)` vanishes because `A`
defines a rational singularity, so it is a projective `A`-module and
`Ext²_A(H¹(X, 𝒪_X), ω_A)` vanishes; the obstruction to surjectivity therefore vanishes, and
exactness makes the trace surjective.

No hypothesis on `ω_A` or on `ω_X` enters, and no Noetherian hypothesis on `X`. -/
public theorem surjective_trace (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules)
    (D : S.DualizingTraceSequence ωA ωX) : Function.Surjective D.trace.hom := by
  intro z
  have hproj : Projective S.firstCohomologyStructureSheafModule :=
    Projective.of_iso S.isZero_firstCohomologyStructureSheafModule.isoZero.symm
      Projective.zero_projective
  have hsub : Subsingleton
      (Abelian.Ext.{u} S.firstCohomologyStructureSheafModule ωA 2) := by
    have h := Abelian.Ext.subsingleton_of_projective.{u}
      S.firstCohomologyStructureSheafModule ωA 1
    simpa using h
  exact (D.exact z).mp (Subsingleton.elim _ _)

/-- **The last step of the source's proof of [Stacks, Tag 0BBU].** In Situation
[Stacks, Tag 0B4W] with a dualizing module `ω_A` for `A`, a dualizing module `ω_X` on `X` and a
`DualizingTraceSequence` `D`, the map `D.trace : H⁰(X, ω_X) ⟶ ω_A` is an isomorphism.

This is not [Stacks, Tag 0BBU]: `D.trace` is any injective map fitting in the duality sequence,
not the trace of duality, `ω_X` is any dualizing module, not the one normalized relative to
`ω_A`, and `D` exists exactly when `H⁰(X, ω_X) ≅ ω_A` (`nonempty_dualizingTraceSequence_iff`).
The tag is `AlgebraicGeometry.RationalSingularitySituation.bijective_normalizedTrace`, proved
unconditionally for the normalized `ω_X` and its genuine trace.

`H¹(X, 𝒪_X)` vanishes because `A` defines a rational singularity, so it is a projective
`A`-module and `Ext²_A(H¹(X, 𝒪_X), ω_A)` vanishes; the trace is then surjective by exactness and
injective by hypothesis. The two results the source quotes are Grauert–Riemenschneider vanishing
[Stacks, Tag 0AXD] and the duality exact sequence [Stacks, Tag 0B4S], and they enter here
together as the hypothesis `D`. Tag 0AXD is
`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_of_properRightAdjoint_isoShiftTwo`,
in the vanishing situation of [Stacks, Tag 0AX8], and Tag 0B4S is
`isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero` in the namespace
`Stacks.ResolutionOfSurfaces`, under a `TraceCokernelDuality` datum and a uniform bound. Neither
is stated in this situation, so neither produces `D`. -/
public theorem bijective_trace [IsLocallyNoetherian S.X] (ωA : ModuleCat.{u} S.A)
    (_hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) (ωX : S.X.Modules)
    (_hωX : Stacks.Duality.IsDualizingModule ωX) (D : S.DualizingTraceSequence ωA ωX) :
    Function.Bijective D.trace.hom :=
  ⟨D.injective_trace, S.surjective_trace ωA ωX D⟩

end AlgebraicGeometry.RationalSingularitySituation

end

end
