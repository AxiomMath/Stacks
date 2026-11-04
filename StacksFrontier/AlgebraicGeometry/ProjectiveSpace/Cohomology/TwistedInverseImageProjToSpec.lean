module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CanonicalTwistDerived

/-!
# The twisted inverse image of `ℙⁿ_R ⟶ Spec R`

Let `R` be a commutative ring, `n ≥ 0`, `X = ℙⁿ_R = Proj R[T₀, …, Tₙ]` and let
`f : X ⟶ Spec R` be the structure morphism. This file records that `f` satisfies the hypotheses
of [Stacks, Tag 0A9E] with no assumption on `R`, so that

`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec R})`

has a right adjoint, and names that right adjoint `a = f^×`. It is the functor whose value at
`𝒪_{Spec R}` the computation of [Stacks, Tag 0A9W] identifies with `𝒪_X(-n-1)[n]`.

The three hypotheses of Tag 0A9E are all available: `Spec R` is quasi-compact, and `f` is
quasi-compact and quasi-separated because it is proper —
`Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff`, which holds over an arbitrary
commutative ring.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec` — **`a = f^×`, the right
  adjoint of `Rf_*` on `D_QCoh` for the structure morphism of `ℙⁿ_R`.**
* `Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpecStructureSheaf` —
  `a(𝒪_{Spec R})`, the object [Stacks, Tag 0A9W] computes.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.quasiCompact_projToSpecCoeff` and
  `Stacks.ProjectiveSpace.Cohomology.quasiSeparated_projToSpecCoeff` — the structure morphism of
  `ℙⁿ_R` is quasi-compact and quasi-separated, over any commutative ring.
* `Stacks.ProjectiveSpace.Cohomology.isLeftAdjoint_quasiCoherentDerivedPushforward_projToSpecCoeff`
  — **[Stacks, Tag 0A9E] for `ℙⁿ_R ⟶ Spec R`**: `Rf_*` on `D_QCoh` has a right adjoint.
* `Stacks.ProjectiveSpace.Cohomology.adjunction_quasiCoherentDerivedPushforward_projToSpecCoeff` —
  the adjunction itself, which is what produces a map into `a(𝒪_{Spec R})` from a map out of
  `Rf_*`.

## Implementation notes

What is *not* here is the comparison map `c : 𝒪_X(-n-1)[n] → a(𝒪_{Spec R})` of
[Stacks, Tag 0A9W], nor the statement that it is an isomorphism. The adjunction below turns that
map into a map `Rf_*(𝒪_X(-n-1)[n]) → 𝒪_{Spec R}` in `D_QCoh(𝒪_{Spec R})`, and what this library
has towards it is the same statement for *derived global sections* rather than for `Rf_*`:
`Stacks.ProjectiveSpace.Cohomology.nonempty_derivedGlobalSections_twistQcoh_canonical_iso_single`
says `RΓ(X, 𝒪(-n-1)) ≅ R[-n]` in `D(R)`. Crossing from `RΓ` to `Rf_*` is
`AlgebraicGeometry.derivedGlobalSectionsOverIsoDerivedPushforward`, which needs exactness of
`Scheme.Modules.pullback f`, and then `D(R) ≌ D_QCoh(𝒪_{Spec R})` is [Stacks, Tag 06Z0]. Neither
step is taken here.

The quasi-compactness and quasi-separatedness are stated as theorems rather than instances: they
are consequences of properness, which is not an instance for this morphism either, so making them
instances would only move the failure. Callers pass them by `haveI`, which is what the adjointness
statement below does.

No `@[stacks]` attribute is attached to the adjointness statement: the covering set of
[Stacks, Tag 0A9E] is already registered on
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`, and this is one instance of
it, not a new reading.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The structure morphism is quasi-compact and quasi-separated -/

/-- **The structure morphism `ℙⁿ_R ⟶ Spec R` is quasi-compact**, over any commutative ring: it is
proper. -/
theorem quasiCompact_projToSpecCoeff : QuasiCompact (projToSpecCoeff R n) :=
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R n
  inferInstance

/-- **The structure morphism `ℙⁿ_R ⟶ Spec R` is quasi-separated**, over any commutative ring: it
is proper, hence separated. -/
theorem quasiSeparated_projToSpecCoeff : QuasiSeparated (projToSpecCoeff R n) :=
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R n
  inferInstance

/-! ### `Rf_*` on `D_QCoh`, and its right adjoint -/

/-- `Rf_* : D_QCoh(𝒪_{ℙⁿ_R}) ⥤ D_QCoh(𝒪_{Spec R})` for the structure morphism. Derived direct
image preserves quasi-coherence of the cohomology sheaves because the structure morphism is
quasi-compact and quasi-separated, which is part (1) of [Stacks, Tag 08D5]. -/
def quasiCoherentDerivedPushforwardProjToSpec :
    Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading R n)) ⥤
      Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of R)) :=
  haveI := quasiCompact_projToSpecCoeff R n
  haveI := quasiSeparated_projToSpecCoeff R n
  Stacks.Duality.quasiCoherentDerivedPushforward (projToSpecCoeff R n)
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff R n))

/-- **[Stacks, Tag 0A9E] for the structure morphism of `ℙⁿ_R`.** Derived direct image
`Rf_* : D_QCoh(𝒪_{ℙⁿ_R}) ⥤ D_QCoh(𝒪_{Spec R})` has a right adjoint, over any commutative ring:
`Spec R` is quasi-compact and `f` is quasi-compact and quasi-separated, being proper. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_projToSpecCoeff :
    (quasiCoherentDerivedPushforwardProjToSpec R n).IsLeftAdjoint :=
  have := quasiCompact_projToSpecCoeff R n
  have := quasiSeparated_projToSpecCoeff R n
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (projToSpecCoeff R n)

/-- **`a = f^×`, the twisted inverse image of the structure morphism `f : ℙⁿ_R ⟶ Spec R`**: the
right adjoint of `Rf_*` on the quasi-coherent derived categories. This is the functor
[Stacks, Tag 0A9W] evaluates at `𝒪_{Spec R}`. -/
def twistedInverseImageProjToSpec :
    Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of R)) ⥤
      Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading R n)) :=
  haveI := isLeftAdjoint_quasiCoherentDerivedPushforward_projToSpecCoeff R n
  (quasiCoherentDerivedPushforwardProjToSpec R n).rightAdjoint

/-- **The adjunction `Rf_* ⊣ a`** for the structure morphism of `ℙⁿ_R`. A map
`𝒪_X(-n-1)[n] ⟶ a(𝒪_{Spec R})` — the comparison map `c` of [Stacks, Tag 0A9W] — is by this
adjunction the same thing as a map `Rf_*(𝒪_X(-n-1)[n]) ⟶ 𝒪_{Spec R}`. -/
def adjunction_quasiCoherentDerivedPushforward_projToSpecCoeff :
    quasiCoherentDerivedPushforwardProjToSpec R n ⊣ twistedInverseImageProjToSpec R n :=
  haveI := isLeftAdjoint_quasiCoherentDerivedPushforward_projToSpecCoeff R n
  Adjunction.ofIsLeftAdjoint (quasiCoherentDerivedPushforwardProjToSpec R n)

/-- **`a(𝒪_{Spec R})`**, the object of `D_QCoh(𝒪_{ℙⁿ_R})` that [Stacks, Tag 0A9W] identifies with
`𝒪_X(-n-1)[n]`. -/
def twistedInverseImageProjToSpecStructureSheaf :
    Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading R n)) :=
  (twistedInverseImageProjToSpec R n).obj
    (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of R)))

end Stacks.ProjectiveSpace.Cohomology

end
