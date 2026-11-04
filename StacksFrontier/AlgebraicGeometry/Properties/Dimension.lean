module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.KrullDimension.Defs
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Separation.IsolatedPoint

/-!
# The dimension of a scheme

The dimension of a scheme is the Krull dimension of its underlying topological space, and its
dimension at a point is the local Krull dimension of that space at the point. The global
dimension is the supremum of the dimensions at all points, and also the supremum of the Krull
dimensions of all the local rings.

A locally Noetherian scheme of dimension at most zero is the disjoint union of the spectra of its
local rings, which are Artinian; and a point of a locally Noetherian scheme has local dimension
zero exactly when it is isolated.

## Main definitions

* `AlgebraicGeometry.sigmaFromSpecStalk` is the canonical map from the coproduct of the spectra
  of all stalks to the scheme.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_eq_iSup_krullDimOfRing_stalk` identifies the dimension
  of a scheme with the supremum of the dimensions of its local rings.
* `AlgebraicGeometry.isArtinianRing_stalk_of_topologicalKrullDim_le_zero` says that every stalk
  of a locally Noetherian scheme of dimension at most zero is Artinian.
* `AlgebraicGeometry.isIso_sigmaFromSpecStalk_of_topologicalKrullDim_le_zero` says that the
  canonical map from the disjoint union of their spectra is an isomorphism.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint` characterizes the points
  of local dimension zero as the isolated points.
* `AlgebraicGeometry.mem_genericPoints_iff_isMax` characterizes the generic points of the
  irreducible components as the maximal points of the specialization order.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_zero_iff_mem_genericPoints` says that the local ring
  at a point has dimension zero exactly when the point is such a generic point.

## Implementation notes

Schemes coerce to their types of points and carry the topology of their underlying spaces, so the
general topological definitions `topologicalKrullDim` and `topologicalKrullDimAt` state the
dimension and the dimension at a point directly; they are adopted rather than duplicated by
scheme-specific aliases. The dimension of a local ring is `ringKrullDim`, and the supremum is
taken in `WithBot ℕ∞`, the common codomain of the two notions.

For the dimension-zero decomposition we use the points of the scheme as the canonical indexing
type for the disjoint union and its stalks as the summand rings; scheme stalks carry their
canonical local-ring instances. The source assumes dimension equal to zero, and dimension at most
zero is a useful generalization which also includes the empty scheme. Isolation is the
topological predicate `IsIsolatedPoint`.

## References

* [Stacks Project, Tag 04MT](https://stacks.math.columbia.edu/tag/04MT)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
* [Stacks Project, Tag 0AAX](https://stacks.math.columbia.edu/tag/0AAX)
* [Stacks Project, Tag 0H7C](https://stacks.math.columbia.edu/tag/0H7C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The dimension of a scheme is the supremum of the Krull dimensions of its local rings. -/
@[stacks 04MU "dimension_sup_local_rings", ega "IV 5.1.4"]
theorem topologicalKrullDim_eq_iSup_krullDimOfRing_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
  simp_rw [ringKrullDim_stalk_eq_coheight]
  rw [← Equiv.iSup_comp (e := (irreducibleSetEquivPoints (α := X)).toEquiv.symm)]
  exact iSup_congr fun x => by
    simpa using congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞))
      (Order.coheight_orderIso (irreducibleSetEquivPoints (α := X))
        ((irreducibleSetEquivPoints (α := X)).symm x)).symm

/-- The canonical map from the coproduct of the spectra of the local rings of `X` to `X`. -/
noncomputable def sigmaFromSpecStalk (X : Scheme.{u}) :
    (∐ fun x : X ↦ Spec (X.presheaf.stalk x)) ⟶ X :=
  Sigma.desc fun x ↦ X.fromSpecStalk x

/-- The local rings of a locally Noetherian scheme of dimension at most zero are Artinian. -/
@[stacks 0AAX "the summands are spectra of Artinian local rings"]
lemma isArtinianRing_stalk_of_topologicalKrullDim_le_zero
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X ≤ 0) (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  let : Ring.KrullDimLE 0 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr <| by
    exact le_trans (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x)
      (by rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
          exact hX)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- A locally Noetherian scheme of dimension at most zero is the coproduct of the spectra of its
local rings. -/
@[stacks 0AAX "the disjoint-union decomposition"]
lemma isIso_sigmaFromSpecStalk_of_topologicalKrullDim_le_zero
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X ≤ 0) :
    IsIso (sigmaFromSpecStalk X) := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hX
  have hsub (x : X) : Subsingleton (Spec (X.presheaf.stalk x)) := by
    let : IsArtinianRing (X.presheaf.stalk x) :=
      isArtinianRing_stalk_of_topologicalKrullDim_le_zero X hX x
    exact Ring.KrullDimLE.subsingleton_primeSpectrum _
  have hopen (x : X) : IsOpenImmersion (X.fromSpecStalk x) := by
    have : IsIso ((X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint _) ≫
        (stalkClosedPointIso _).hom) := by
      change IsIso (Scheme.stalkClosedPointTo (X.fromSpecStalk x))
      rw [Scheme.stalkClosedPointTo_fromSpecStalk]
      infer_instance
    have : IsIso ((X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint _)) :=
      IsIso.of_isIso_comp_right _ (stalkClosedPointIso _).hom
    let : Subsingleton (Spec (X.presheaf.stalk x)) := hsub x
    let : ∀ z : Spec (X.presheaf.stalk x),
        IsIso ((X.fromSpecStalk x).stalkMap z) := fun z ↦ by
      obtain rfl : z = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
      infer_instance
    apply IsOpenImmersion.of_isIso_stalkMap
    refine .of_continuous_injective_isOpenMap (by fun_prop) ?_ ?_
    · intro a b _
      exact Subsingleton.elim _ _
    · intro U hU
      exact isOpen_discrete _
  let : ∀ x : X, IsOpenImmersion (X.fromSpecStalk x) := hopen
  have hdisj : Pairwise (Function.onFun Disjoint fun x : X =>
      Set.range (X.fromSpecStalk x)) := by
    intro x y hxy
    change Disjoint (Set.range (X.fromSpecStalk x)) (Set.range (X.fromSpecStalk y))
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hz'
    have ha : a = IsLocalRing.closedPoint _ := @Subsingleton.elim _ (hsub x) _ _
    have hb' : b = IsLocalRing.closedPoint _ := @Subsingleton.elim _ (hsub y) _ _
    subst a
    subst b
    apply hxy
    simpa using hb.symm
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨isOpenImmersion_sigmaDesc _ _ hdisj, ?_⟩
  rw [TopCat.epi_iff_surjective]
  intro x
  let p : Spec (X.presheaf.stalk x) := IsLocalRing.closedPoint _
  refine ⟨Sigma.ι (fun x : X ↦ Spec (X.presheaf.stalk x)) x
      p, ?_⟩
  change (Sigma.desc (fun x : X ↦ X.fromSpecStalk x))
      ((Sigma.ι (fun x : X ↦ Spec (X.presheaf.stalk x)) x)
        p) = x
  rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  exact Scheme.fromSpecStalk_closedPoint

/-- A space with an open singleton has local dimension zero at that point. -/
@[ega "0 14.1.10" "more general"]
private lemma topologicalKrullDimAt_eq_zero_of_isOpen_singleton
    {Y : Type*} [TopologicalSpace Y] (y : Y) (hy : IsOpen ({y} : Set Y)) :
    topologicalKrullDimAt Y y = 0 := by
  obtain ⟨⟨U, hyU, hU, hdim⟩, hle⟩ := topologicalKrullDimAt_isLeast Y y
  refine le_antisymm ?_ ?_
  · have : Subsingleton ({y} : Set Y) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    exact (hle ⟨{y}, rfl, hy, rfl⟩).trans
      (topologicalKrullDim_zero_of_discreteTopology ({y} : Set Y))
  · let : Nonempty (IrreducibleCloseds U) :=
      ⟨⟨closure {⟨y, hyU⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact hdim ▸ Order.krullDim_nonneg

/-- A point of a locally Noetherian scheme has local dimension zero exactly when it is an
isolated point. -/
@[stacks 0H7C, ega "0 14.1.10" "loc. Noetherian scheme"]
public lemma topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint
    (X : Scheme) [IsLocallyNoetherian X] (x : X) :
    topologicalKrullDimAt X x = 0 ↔ IsIsolatedPoint x := by
  constructor
  · intro h
    obtain ⟨⟨U, hxU, hU, hdim⟩, _⟩ := topologicalKrullDimAt_isLeast X x
    let V : X.Opens := ⟨U, hU⟩
    let : IsLocallyArtinian V.toScheme :=
      IsLocallyArtinian.of_topologicalKrullDim_le_zero
        (show topologicalKrullDim U ≤ 0 from hdim ▸ h.le)
    let : DiscreteTopology U := by
      change DiscreteTopology (↥V.toScheme)
      infer_instance
    change IsOpen ({x} : Set X)
    simpa using hU.isOpenMap_subtype_val ({⟨x, hxU⟩} : Set U) (isOpen_discrete _)
  · intro h
    exact topologicalKrullDimAt_eq_zero_of_isOpen_singleton x h

/-- A point of a scheme is the generic point of an irreducible component exactly when it is
maximal for the specialization order, that is, when it has no proper generalization. -/
theorem mem_genericPoints_iff_isMax (X : Scheme.{u}) (x : X) :
    x ∈ genericPoints X ↔ IsMax x := by
  constructor
  · intro hx b hb
    refine Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr ?_)
    exact hx.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp (Scheme.le_iff_specializes.mp hb))
      (subset_closure (Set.mem_singleton b))
  · intro hx
    obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({x} : Set X)) isIrreducible_singleton.closure
    have hη : IsGenericPoint (genericPoints.ofComponent (α := X) ⟨C, hC⟩ : X) C :=
      genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩
    have hηx : (genericPoints.ofComponent (α := X) ⟨C, hC⟩ : X) ⤳ x :=
      hη.specializes_iff_mem.mpr (hxC (subset_closure (Set.mem_singleton x)))
    change closure ({x} : Set X) ∈ irreducibleComponents X
    rw [Set.Subset.antisymm (specializes_iff_closure_subset.mp hηx)
      (specializes_iff_closure_subset.mp
        (Scheme.le_iff_specializes.mp (hx (Scheme.le_iff_specializes.mpr hηx))))]
    exact (genericPoints.ofComponent (α := X) ⟨C, hC⟩).2

/-- The local ring of a scheme at a point has Krull dimension zero exactly when the point is
the generic point of an irreducible component. -/
@[ega "I 2.4.3"]
theorem ringKrullDim_stalk_eq_zero_iff_mem_genericPoints (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) = (0 : WithBot ℕ∞) ↔ x ∈ genericPoints X := by
  rw [ringKrullDim_stalk_eq_coheight, ← WithBot.coe_zero, WithBot.coe_eq_coe,
    Order.coheight_eq_zero, ← mem_genericPoints_iff_isMax]

end AlgebraicGeometry

add_to_stacks 04MT "dimension of a scheme" topologicalKrullDim
add_to_ega "0 14.1.2" topologicalKrullDim
add_to_stacks 04MT "dimension of a scheme at a point" topologicalKrullDimAt
add_to_stacks 04MU "dimension_sup_at_points"
  TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim
add_to_stacks 04MU "dimension_sup_at_points" TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim

end
