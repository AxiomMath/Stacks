module

public import StacksFrontier.AlgebraicGeometry.Conormal.CommonCharts
public import StacksFrontier.AlgebraicGeometry.Constructions.AssociatedGradedSectionsRing
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections

/-!
# `Γ(i⁻¹U, 𝒞_{Z/X,*})` is the associated graded ring of the chart ideal

Let `i : Z ⟶ X` be an immersion of schemes and `U ⊆ X` an affine open over which `i` restricts to
a closed immersion, with `I = chartIdeal i U ⊆ Γ(X, U)` the kernel of `Γ(X, U) ⟶ Γ(Z, i⁻¹U)`.
Degreewise the sections of the conormal algebra over `i⁻¹U` are `Iⁿ/Iⁿ⁺¹` — that is
[Stacks, Tag 0633], `AlgebraicGeometry.affineSectionsEquiv`. This file assembles those
identifications into a single **ring** isomorphism

`Gr_I(Γ(X, U)) ≃+* Γ(i⁻¹U, 𝒞_{Z/X,*})`

between the associated graded ring of the chart ideal and the ring of sections of the ungraded
realization of the conormal algebra, carrying the structure map of `Gr_I(Γ(X, U))` to the
structural ring map of the algebra sheaf.

The instantiation at `Spec(A ⧸ I) ⟶ Spec A` and `U = ⊤` is the fibre-side input of part (2) of
[Stacks, Tag 0897]; it is
`StacksFrontier/AlgebraicGeometry/Conormal/ConormalSectionsRingSpec.lean`, whose
`Stacks.Conormal.specConormalSectionsRingEquiv` and `specConormalSectionsRingEquiv_algebraMap`
are the `ρ` and `hρ` of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedAlgebraSections`,
with `k = A ⧸ I` and `R = Gr_I(A)`.

## The assembly is not here

The passage from a degreewise additive identification with the pieces `Iⁿ/Iⁿ⁺¹` of an
associated graded ring to a ring isomorphism onto the sections of an algebra sheaf is
`Stacks.AssociatedGradedSections.sectionsRingEquiv`, which is about an arbitrary sheaf of graded
algebras and is shared with
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/GradedPullbackSectionsRing.lean`. What
this file does is supply its inputs for the conormal algebra: the degreewise identification is
[Stacks, Tag 0633], commutativity of the homogeneous multiplication and vanishing in negative
degrees are the fields `mul_comm_int` and `negative_isZero` of
`Stacks.Conormal.ConormalAlgebraData`, and affineness of `i⁻¹U` is
`Stacks.Conormal.isAffineOpen_preimage_of_closedRestriction`.

## Main definitions

* `Stacks.Conormal.conormalSectionsRingEquiv`: **`Gr_I(Γ(X, U)) ≃+* Γ(i⁻¹U, 𝒞_{Z/X,*})`.**

## Main results

* `Stacks.Conormal.conormalSectionsRingEquiv_gradeZeroRingHom`: **the identification carries the
  structure map of `Gr_I(Γ(X, U))` to the structural ring map of the algebra sheaf**, composed
  with `Γ(X, U) ⟶ Γ(Z, i⁻¹U)`. So the structural ring map of the conormal algebra over a chart
  *is* the structure map of an associated graded ring, and not merely isomorphic to one in a way
  that forgets the base.

The form `algebraMap (A ⧸ I) (Gr_I(A)) ↦ ` the structure map, which is what
`Stacks.RelativeSpec.AlgebraSheaf.specAlgebraSheafIsoOfSectionsRingEquiv` consumes, is the
instantiation in the companion module.

## Implementation notes

**`AlgebraicGeometry.affineSectionsEquiv` is used, and nothing is re-derived from it.** The
private `chartSectionsEquiv` of
`StacksFrontier/AlgebraicGeometry/Divisors/NormalCone/BaseChange.lean` is literally
`(affineSectionsEquiv i U hU).equiv n`, so there is nothing there to expose.

**The ungraded realization `Stacks.Conormal.conormalAlgebraSheaf i` *is*
`Stacks.RelativeSpec.gradedAlgebraSheaf _ (conormalAlgebra i).algebra
(conormalAlgebra i).mul_comm_int` by definition**, which is what lets the shared assembly's
conclusion be read at the conormal algebra sheaf with no transport.

**The four fields of `AlgebraicGeometry.AffineSectionsEquiv` are passed as they stand.** The
graded unit and the graded product of `fun n => AssociatedGraded.piece I n` are
`AssociatedGraded.mk I 0 ⟨1, _⟩` and `AssociatedGraded.homogeneousSMul I` by `rfl`, so `map_one`
and `map_mul` discharge the shared assembly's hypotheses directly; the two subtype proofs of
`1 ∈ I⁰` differ, and proof irrelevance makes that free.

**No `@[stacks]` attribute is attached.** The degreewise identification is Tag 0633, carried by
`AlgebraicGeometry.affineSectionsEquiv`; what is added here is that it is a ring isomorphism on
the nose, which is not the assertion of a numbered result.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec
open scoped DirectSum

universe u

namespace Stacks.Conormal

/-! ### The chart-level comparison -/

section Chart

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (U : X.affineOpens)
  (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
/-- **`Γ(i⁻¹U, 𝒞_{Z/X,*}) ≅ Gr_I(Γ(X, U))`** for `I = chartIdeal i U` the kernel ideal of the
immersion on an affine chart over which it restricts to a closed immersion: the sections of the
ungraded realization of the conormal algebra over `i⁻¹U` are the associated graded ring of `I`.

The degreewise identification is [Stacks, Tag 0633], `AlgebraicGeometry.affineSectionsEquiv`,
and the assembly of those identifications into a ring isomorphism is
`Stacks.AssociatedGradedSections.sectionsRingEquiv`; the conormal algebra supplies its three
remaining inputs — commutativity of the homogeneous multiplication, vanishing in negative
degrees, and affineness of `i⁻¹U`. -/
def conormalSectionsRingEquiv :
    AssociatedGraded.gradedRing (chartIdeal i U) ≃+*
      ↥(AlgebraSheaf.sections (conormalAlgebraSheaf i) (i ⁻¹ᵁ U.1)) :=
  Stacks.AssociatedGradedSections.sectionsRingEquiv (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (chartIdeal i U)
    (AlgebraicGeometry.affineSectionsEquiv i U hU).equiv
    (AlgebraicGeometry.affineSectionsEquiv i U hU).map_one
    (fun n m a b => (AlgebraicGeometry.affineSectionsEquiv i U hU).map_mul n m a b)
    (conormalAlgebra i).negative_isZero
    (isAffineOpen_preimage_of_closedRestriction i U hU)

/-- **The identification carries the structure map of `Gr_I(Γ(X, U))` to the structural ring map
of the conormal algebra sheaf**, composed with `Γ(X, U) ⟶ Γ(Z, i⁻¹U)`. So the structural ring
map of the conormal algebra over a chart *is* the structure map of an associated graded ring,
and not merely isomorphic to one in a way that forgets the base.

`Stacks.AssociatedGradedSections.sectionsRingEquiv_gradeZeroRingHom` at the `map_smul` field of
`AlgebraicGeometry.AffineSectionsEquiv`. -/
theorem conormalSectionsRingEquiv_gradeZeroRingHom (r : Γ(X, U)) :
    conormalSectionsRingEquiv i U hU (AssociatedGraded.gradeZeroRingHom (chartIdeal i U) r) =
      ((conormalAlgebraSheaf i).hom.hom.app (op (i ⁻¹ᵁ U.1))).hom ((i.app U.1).hom r) :=
  Stacks.AssociatedGradedSections.sectionsRingEquiv_gradeZeroRingHom (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int (chartIdeal i U) (i.app U.1).hom
    (AlgebraicGeometry.affineSectionsEquiv i U hU).equiv
    (AlgebraicGeometry.affineSectionsEquiv i U hU).map_one
    (fun n m a b => (AlgebraicGeometry.affineSectionsEquiv i U hU).map_mul n m a b)
    (conormalAlgebra i).negative_isZero
    (isAffineOpen_preimage_of_closedRestriction i U hU)
    (fun n s a => (AlgebraicGeometry.affineSectionsEquiv i U hU).map_smul n s a) r

end Chart

end Stacks.Conormal

end
