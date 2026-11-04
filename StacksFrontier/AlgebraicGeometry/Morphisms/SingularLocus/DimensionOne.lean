module

public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoCriteria
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksFrontier.AlgebraicGeometry.NormalizationQuotientDirectSum.RegularLocusOpen

/-!
# The singular locus of a one-dimensional Nagata scheme

On a Nagata scheme of dimension at most one the regular locus is open, and on a *reduced* such
scheme its complement, the singular locus, is a closed discrete set of closed points.  This is
the geometry of the dimension hypothesis of
[Stacks, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R): a one-dimensional reduced Nagata
scheme is regular away from finitely many closed points on each affine open, which is what makes
a sheaf supported on the singular locus a direct sum of skyscrapers.

Openness is the J-2 property.  The section ring of an affine open is a Nagata ring of Krull
dimension at most one, hence J-2 by Tag 07PJ, and the J-2 condition on an affine open cover
gives it on the scheme (Tag 07R4), whence the regular locus of the scheme itself is open.

Reducedness enters through the generic points: the local ring at the generic point of an
irreducible component of a reduced scheme is a field, so no irreducible component is contained
in the singular locus.  Combined with `topologicalKrullDim ≤ 1` that forces every singular point
to be closed and the singular locus to be finite on each affine open, which is discreteness.

## Main results

* `isOpen_regularLocus_of_isNagataScheme`: the regular locus of a Nagata scheme of dimension at
  most one is open.
* `isClosed_singleton_of_notMem_regularLocus`: on a reduced scheme of dimension at most one every
  singular point is closed.
* `finite_singularLocus_of_isAffine` and `finite_singularLocus_inter_of_isAffineOpen`: the
  singular locus of an affine such scheme is finite, and on a general one it meets every affine
  open in a finite set.
* `discreteTopology_singularLocus_of_isNagataScheme`: the singular locus is discrete.

## Implementation notes

The dimension hypothesis is `topologicalKrullDim X ≤ 1` rather than `= 1`, which is what every
proof here uses and what passes to open subschemes; a zero-dimensional scheme is covered too, and
that is not vacuous, since an affine open of a one-dimensional scheme may itself be
zero-dimensional.  For the same reason the J-2 input is taken in the form
`isJ2_of_isNagataRing_of_krullDimLE_one`, stated with `Ring.KrullDimLE 1`, rather than the
`ringKrullDim R = 1` form bundled in `isJ2_of_standard_classes_and_finiteType`.

The closed-point and finiteness statements are the purely topological results of
`StacksFrontier.Topology.Dimension.DimensionLEOne` — a closed subset of a space of Krull dimension
at most one containing no irreducible component consists of closed points, and is finite when the
space is Noetherian and sober — specialised by the one geometric input, that the generic points of
a reduced scheme are regular.

Passing between a scheme and an affine open of it is done on the level of schemes, through
`mem_regularLocus_opens_iff`, so that the irreducible components in play are always those of a
scheme and never those of a bare subspace.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 07PJ](https://stacks.math.columbia.edu/tag/07PJ) for a one-dimensional
  Nagata ring being J-2
* [Stacks Project, Tag 07R4](https://stacks.math.columbia.edu/tag/07R4) for the J-2 condition
  being local on an affine open cover
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-- A point of an open subscheme is regular exactly when it is regular on the ambient scheme:
the stalks agree. -/
public theorem mem_regularLocus_opens_iff {X : Scheme.{u}} (U : X.Opens) (y : U.toScheme) :
    y ∈ regularLocus U.toScheme ↔ y.1 ∈ regularLocus X := by
  constructor
  · intro h
    have _ : IsRegularLocalRing (U.toScheme.presheaf.stalk y) := h
    exact IsRegularLocalRing.of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv
  · intro h
    have _ : IsRegularLocalRing (X.presheaf.stalk y.1) := h
    exact IsRegularLocalRing.of_ringEquiv (U.stalkIso y).commRingCatIsoToRingEquiv.symm

/-- The generic point of an irreducible component of a reduced scheme is a regular point, its
local ring being a field. -/
public theorem mem_regularLocus_of_closure_mem_irreducibleComponents (X : Scheme.{u})
    [IsReduced X] (x : X) (hx : closure ({x} : Set X) ∈ irreducibleComponents X) :
    x ∈ regularLocus X := by
  let _ : Field (X.presheaf.stalk x) :=
    (isField_stalk_of_closure_mem_irreducibleComponents X x hx).toField
  exact (inferInstance : IsRegularLocalRing (X.presheaf.stalk x))

/-- No irreducible component of a reduced scheme is contained in its singular locus: the generic
point of the component is regular. -/
public theorem not_subset_singularLocus_of_mem_irreducibleComponents (X : Scheme.{u})
    [IsReduced X] {C : Set X} (hC : C ∈ irreducibleComponents X) : ¬ C ⊆ singularLocus X := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  have hcl : closure ({η} : Set X) = C := isGenericPoint_def.mp hη
  have hreg : η ∈ regularLocus X :=
    mem_regularLocus_of_closure_mem_irreducibleComponents X η (hcl ▸ hC)
  exact fun hsub => (hsub (hcl ▸ subset_closure (Set.mem_singleton η))) hreg

/-- A Nagata scheme is locally Noetherian. -/
private theorem isLocallyNoetherian_of_isNagataScheme_aux {X : Scheme.{u}}
    (hNagata : IsNagataScheme X) : IsLocallyNoetherian X :=
  ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme X).mp hNagata).1

/-- An open subscheme of a scheme of topological Krull dimension at most one has dimension at most
one. -/
private theorem topologicalKrullDim_opens_le_one {X : Scheme.{u}} (hdim : topologicalKrullDim X ≤ 1)
    (U : X.Opens) : topologicalKrullDim U ≤ 1 :=
  (topologicalKrullDim_subspace_le X (U : Set X)).trans hdim

/-- **Stacks Project, Tag 07PJ and Tag 07R4.** The regular locus of a Nagata scheme of dimension
at most one is open: the section ring over every affine open is a Nagata ring of Krull dimension
at most one, hence J-2, and the J-2 condition is local on an affine open cover. -/
public theorem isOpen_regularLocus_of_isNagataScheme (X : Scheme.{u})
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 1) :
    IsOpen (regularLocus X) := by
  have _ : IsLocallyNoetherian X := isLocallyNoetherian_of_isNagataScheme_aux hNagata
  have hsections : ∀ U : X.affineOpens, _root_.IsJ2 Γ(X, (U : X.Opens)) := by
    intro U
    have hdimR : ringKrullDim Γ(X, (U : X.Opens)) ≤ 1 := by
      have heq : topologicalKrullDim (↥(U : X.Opens)) = ringKrullDim Γ(X, (U : X.Opens)) := by
        rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
        exact IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph
      rw [← heq]
      exact topologicalKrullDim_opens_le_one hdim _
    have _ : Ring.KrullDimLE 1 Γ(X, (U : X.Opens)) := Ring.krullDimLE_iff.mpr hdimR
    exact isJ2_of_isNagataRing_of_krullDimLE_one _ (hNagata.isNagataRing_sections U)
  exact Scheme.IsJ2.isOpen_regularLocus (((Scheme.isJ2_tfae X).out 3 1).mp hsections) (𝟙 X)

/-- The singular locus of a reduced affine Nagata scheme of dimension at most one is finite: it
is a closed subset of a Noetherian sober space of dimension at most one containing no irreducible
component. -/
public theorem finite_singularLocus_of_isAffine (X : Scheme.{u}) [IsReduced X] [IsAffine X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 1) :
    (singularLocus X).Finite := by
  have _ : IsLocallyNoetherian X := isLocallyNoetherian_of_isNagataScheme_aux hNagata
  have _ : IsNoetherianRing Γ(X, (⊤ : X.Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have _ : NoetherianSpace X := noetherianSpace_of_isAffine
  exact Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim
    (isOpen_regularLocus_of_isNagataScheme X hNagata hdim).isClosed_compl
    fun _ hC => not_subset_singularLocus_of_mem_irreducibleComponents X hC

/-- The singular locus of a reduced Nagata scheme of dimension at most one meets every affine
open in a finite set. -/
public theorem finite_singularLocus_inter_of_isAffineOpen (X : Scheme.{u}) [IsReduced X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 1) (U : X.Opens)
    (hU : IsAffineOpen U) :
    ((U : Set X) ∩ singularLocus X).Finite := by
  have _ : IsAffine U.toScheme := hU
  have himg : (Subtype.val : U.toScheme → X) '' singularLocus U.toScheme =
      (U : Set X) ∩ singularLocus X := by
    ext z
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun hreg => hy ((mem_regularLocus_opens_iff U y).mpr hreg)⟩
    · rintro ⟨hzU, hzs⟩
      exact ⟨⟨z, hzU⟩, fun hreg => hzs ((mem_regularLocus_opens_iff U ⟨z, hzU⟩).mp hreg), rfl⟩
  rw [← himg]
  exact (finite_singularLocus_of_isAffine U.toScheme (isNagataScheme_open hNagata U)
    (topologicalKrullDim_opens_le_one hdim U)).image _

/-- The singular locus of a reduced Nagata scheme of dimension at most one carries the discrete
topology: around a singular point an affine open meets the singular locus in a finite set of
closed points, and removing the others leaves an open meeting it only in that point. -/
public theorem discreteTopology_singularLocus_of_isNagataScheme (X : Scheme.{u}) [IsReduced X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 1) :
    DiscreteTopology (singularLocus X) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  obtain ⟨-, ⟨U, hUaff, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x.1) isOpen_univ
  have hFfin : ((U : Set X) ∩ singularLocus X).Finite :=
    finite_singularLocus_inter_of_isAffineOpen X hNagata hdim U hUaff
  have hother : IsClosed (((U : Set X) ∩ singularLocus X) \ {x.1}) := by
    rw [← Set.biUnion_of_singleton (((U : Set X) ∩ singularLocus X) \ {x.1})]
    open Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum in
    exact hFfin.sdiff.isClosed_biUnion fun y hy =>
      isClosed_singleton_of_not_mem_regularLocus X hdim y hy.1.2
  have hW : (Subtype.val : singularLocus X → X) ⁻¹'
      ((U : Set X) \ (((U : Set X) ∩ singularLocus X) \ {x.1})) = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨hyU, hy⟩
      exact Subtype.ext (Classical.byContradiction fun hne => hy ⟨⟨hyU, y.2⟩, hne⟩)
    · rintro rfl
      exact ⟨hxU, fun h => h.2 rfl⟩
  rw [← hW]
  exact (U.isOpen.sdiff hother).preimage continuous_subtype_val

end AlgebraicGeometry

end
