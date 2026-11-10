module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme

/-!
# The normalization of a scheme

Mathlib constructs the *relative* normalization `Scheme.Hom.fromNormalization` of a qcqs
morphism `f : X ⟶ Y`.  The absolute normalization of a scheme `X` is the relative
normalization of `X` in the canonical morphism from the spectra of the residue fields at the
generic points of the irreducible components of `X`.  This file builds that morphism, checks
the two finiteness hypotheses Mathlib's construction needs, and records the resulting
normalization morphism.

## Main definitions

* `genericPointResidueSpectrum X`: the coproduct `⨿_{η ∈ X⁰} Spec κ(η)` of the spectra of the
  residue fields at the generic points of `X`.
* `fromGenericPointResidueFields X`: the canonical morphism `⨿_{η ∈ X⁰} Spec κ(η) ⟶ X`.
* `normalizationScheme X hX` and `normalization X hX`: the normalization of `X` and the
  normalization morphism, for a scheme all of whose quasi-compact opens have finitely many
  irreducible components.

## Main results

* `quasiCompact_fromGenericPointResidueFields` and
  `quasiSeparated_fromGenericPointResidueFields`: the two hypotheses of Mathlib's relative
  normalization hold for `fromGenericPointResidueFields X`, the first under the hypothesis
  that quasi-compact opens of `X` have finitely many irreducible components.
* `isDominant_fromGenericPointResidueFields`: the canonical morphism from the generic-point
  residue fields is dominant.  Its set-theoretic range is `genericPoints X`, which is dense in
  any quasi-sober space, in particular in a scheme.
* `finite_irreducibleComponents_of_isNagataScheme`: a Nagata scheme satisfies the finiteness
  hypothesis, because it is locally the spectrum of a Noetherian ring.

## Implementation notes

The source of `fromGenericPointResidueFields X` is a coproduct of spectra of fields, so it is
quasi-separated unconditionally; the morphism is quasi-compact exactly because only finitely
many generic points meet a given quasi-compact open, which is the finiteness hypothesis.

`normalization` is an `abbrev` for `Scheme.Hom.fromNormalization` of
`fromGenericPointResidueFields`, with its quasi-compactness instance supplied by `letI`, so that
Mathlib's API for the relative normalization applies to it directly with no comparison theorem.

## References

* [Stacks Project, Tag 035M](https://stacks.math.columbia.edu/tag/035M)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Normalization

/-- The coproduct of the spectra of the residue fields at the generic points of the irreducible
components of `X`.  This is the scheme denoted `⨿_{η ∈ X⁰} Spec κ(η)` in the source. -/
public noncomputable abbrev genericPointResidueSpectrum (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))

/-- The canonical morphism from the spectra of the residue fields at the generic points of `X`
to `X`, assembled from the morphisms `Spec κ(η) ⟶ X`. -/
public noncomputable def fromGenericPointResidueFields (X : Scheme.{u}) :
    genericPointResidueSpectrum X ⟶ X :=
  Sigma.desc fun η : genericPoints X ↦ X.fromSpecResidueField η.1

/-- The canonical morphism from the generic-point residue fields restricts on the summand
indexed by `η` to the residue-field morphism at `η`. -/
@[simp, reassoc]
public theorem ι_fromGenericPointResidueFields (X : Scheme.{u}) (η : genericPoints X) :
    Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ≫
      fromGenericPointResidueFields X = X.fromSpecResidueField η.1 :=
  Sigma.ι_comp_desc _ _

/-- The canonical morphism from the generic-point residue fields is dominant: its range is the
set of generic points of `X`, and that set is dense because a scheme is quasi-sober. -/
public instance isDominant_fromGenericPointResidueFields (X : Scheme.{u}) :
    IsDominant (fromGenericPointResidueFields X) := by
  refine ⟨Dense.mono (fun η hη ↦ ?_) (dense_iff_closure_eq.mpr genericPoints.closure)⟩
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (X.residueField η))) := inferInstance
  refine ⟨(Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
    ⟨η, hη⟩).base p, ?_⟩
  rw [← Scheme.Hom.comp_apply, ι_fromGenericPointResidueFields]
  exact X.fromSpecResidueField_apply _ _

/-- Only finitely many generic points of `X` lie in a quasi-compact open `U`, when every
quasi-compact open of `X` has finitely many irreducible components.  The generic points lying
in `U` inject into the generic points of `U`, of which there are finitely many. -/
private alias finite_genericPoints_mem := AlgebraicGeometry.Scheme.finite_genericPoints_mem

/-- The canonical morphism from the generic-point residue fields is quasi-compact when every
quasi-compact open of `X` has finitely many irreducible components: the preimage of such an
open is the disjoint union of the finitely many summands it meets. -/
public theorem quasiCompact_fromGenericPointResidueFields (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    QuasiCompact (fromGenericPointResidueFields X) := by
  refine ⟨fun U hU hUc ↦ ?_⟩
  unfold fromGenericPointResidueFields
  let e := sigmaMk (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1)))
  apply e.isCompact_preimage.mp
  convert Set.isCompact_sigma (finite_genericPoints_mem X ⟨U, hU⟩ hUc hX)
    (fun _ _ ↦ isCompact_univ) using 1
  · ext z
    obtain ⟨η, z⟩ := z
    simp only [Set.mem_preimage, Set.mem_sigma_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    rw [show e ⟨η, z⟩ =
      Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η z by simp [e]]
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc, X.fromSpecResidueField_apply]
    rfl
  · intro η _
    infer_instance

/-- The canonical morphism from the generic-point residue fields is quasi-separated: its source
is a coproduct of affine schemes, hence a quasi-separated space. -/
public instance quasiSeparated_fromGenericPointResidueFields (X : Scheme.{u}) :
    QuasiSeparated (fromGenericPointResidueFields X) := by
  let F := fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))
  have : QuasiSeparatedSpace (genericPointResidueSpectrum X) := by
    refine Scheme.quasiSeparatedSpace_of_isOpenCover (fun η ↦ (Sigma.ι F η).opensRange)
      (sigmaOpenCover F).isOpenCover_opensRange (fun η ↦ isAffineOpen_opensRange _) fun η ξ ↦ ?_
    by_cases h : η = ξ
    · subst ξ
      simpa using (isAffineOpen_opensRange (Sigma.ι F η)).isCompact
    · rw [← Opens.coe_inf, disjoint_iff.mp (disjoint_opensRange_sigmaι F η ξ h)]
      exact isCompact_empty
  infer_instance

/-- The normalization of a scheme all of whose quasi-compact opens have finitely many
irreducible components: the relative normalization of `X` in the canonical morphism from the
spectra of the residue fields at its generic points. -/
@[ega "II 7.4.6" "scheme X' for A = R(X)"]
public noncomputable abbrev normalizationScheme (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    Scheme.{u} :=
  letI := quasiCompact_fromGenericPointResidueFields X hX
  (fromGenericPointResidueFields X).normalization

/-- The normalization morphism `ν : X^ν ⟶ X` of a scheme all of whose quasi-compact opens have
finitely many irreducible components. -/
public noncomputable abbrev normalization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    normalizationScheme X hX ⟶ X :=
  letI := quasiCompact_fromGenericPointResidueFields X hX
  (fromGenericPointResidueFields X).fromNormalization

/-- A Nagata scheme is locally the spectrum of a Noetherian ring, hence has a locally
Noetherian underlying space. -/
public theorem isLocallyNoetherianSpace_of_isNagataScheme (X : Scheme.{u})
    (hX : IsNagataScheme X) : IsLocallyNoetherianSpace X := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hX x
  have : IsNoetherianRing Γ(X, U.1) := hU.1
  exact ⟨(U.1 : Set X), U.1.isOpen, hxU, noetherianSpace_of_isAffineOpen U.1 U.2⟩

/-- A Nagata scheme satisfies the finiteness hypothesis used to construct its normalization: a
quasi-compact open of a locally Noetherian space is a Noetherian space, and a Noetherian space
has finitely many irreducible components. -/
@[ega "0 2.2.5" "special case", ega "I 7.1.6" "special case"]
public theorem finite_irreducibleComponents_of_isNagataScheme (X : Scheme.{u})
    (hX : IsNagataScheme X) :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  intro U hU
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : NoetherianSpace U := noetherianSpace_of_isLocallyNoetherianSpace U
    ((isLocallyNoetherianSpace_of_isNagataScheme X hX).subtype (U : Set X))
  exact NoetherianSpace.finite_irreducibleComponents

end Stacks.AlgebraicGeometry.Normalization
