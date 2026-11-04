module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.RingTheory.DedekindDomain.ClosedSubsetFinite
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseGenericFibre
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Finitely many fibre generic points in a closed set

Let `f : X ⟶ Spec A` be of finite type and quasi-compact over a Dedekind domain `A`, and let
`Z ⊆ X` be a closed subset which is nowhere dense in the generic fibre. Then only finitely many
points of `Z` are generic points of irreducible components of their own fibre: by Tag 054X the
set `Z` stays nowhere dense in every fibre over some nonempty open `V ⊆ Spec A`, and a nowhere
dense closed subset of a Noetherian space contains no irreducible component, so such a point
lies over the finite complement of `V`, where each fibre contributes only its finitely many
generic points.

## Main results

* `AlgebraicGeometry.noetherianSpace_fiber`: a fibre of a quasi-compact morphism locally of
  finite type is a Noetherian space.
* `AlgebraicGeometry.notMem_of_mem_genericPoints_fiber`: a closed set containing a generic point
  of an irreducible component of a fibre is not nowhere dense in that fibre.
* `AlgebraicGeometry.finite_setOf_mem_genericPoints_fiber`: the finiteness statement above.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **A fibre of a quasi-compact morphism locally of finite type is a Noetherian space.** The
fibre is locally of finite type over the residue field of its image, hence locally Noetherian,
and it is quasi-compact. -/
theorem noetherianSpace_fiber (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) :
    NoetherianSpace (f.fiber y) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y)))
  have : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  have : IsNoetherian (f.fiber y) := ⟨⟩
  infer_instance

/-- **A closed set containing a generic point of an irreducible component of a fibre is not
nowhere dense in that fibre.** The closure of such a point is an irreducible component of the
fibre, and a nowhere dense closed subset of a Noetherian space contains no irreducible
component. -/
theorem notMem_of_mem_genericPoints_fiber (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : Set X} (hZ : IsClosed Z) {x : X} (hxZ : x ∈ Z)
    (hxg : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    ¬ IsNowhereDense ((f.fiberι (f x)) ⁻¹' Z) := by
  have hclosed : IsClosed ((f.fiberι (f x)) ⁻¹' Z) :=
    hZ.preimage (f.fiberι (f x)).continuous
  have : NoetherianSpace (f.fiber (f x)) := noetherianSpace_fiber f (f x)
  intro hnd
  refine (hclosed.isNowhereDense_iff_forall_irreducibleComponents_not_subset.mp hnd)
    (closure {f.asFiber x}) hxg (hclosed.closure_subset_iff.mpr ?_)
  simpa using hxZ

/-- **Only finitely many points of a closed set nowhere dense in the generic fibre are generic
points of components of their own fibre.** Here `A` is a Dedekind domain and `f` is quasi-compact
and locally of finite type, so that Tag 054X applies and the proper closed subsets of `Spec A`
are finite. -/
theorem finite_setOf_mem_genericPoints_fiber {A : Type u} [CommRing A] [IsDedekindDomain A]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : Set X} (hZ : IsClosed Z)
    (hη : IsNowhereDense ((f.fiberι (genericPoint (Spec (.of A)))) ⁻¹' Z)) :
    {x : X | x ∈ Z ∧ f.asFiber x ∈ genericPoints (f.fiber (f x))}.Finite := by
  obtain ⟨V, hVopen, hVne, hVfib⟩ :=
    exists_open_isNowhereDense_fiber f Z hZ (genericPoint _) (genericPoint_spec _) hη
  have hVc : (Vᶜ : Set (Spec (.of A))).Finite :=
    IsDedekindDomain.finite_of_isClosed_of_ne_univ (A := A) hVopen.isClosed_compl
      (Set.compl_ne_univ.mpr hVne)
  refine Set.Finite.subset (hVc.biUnion
    (t := fun s ↦ (f.fiberι s).base '' genericPoints (f.fiber s)) fun s _ ↦ ?_) ?_
  · have : NoetherianSpace (f.fiber s) := noetherianSpace_fiber f s
    exact (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image _
  rintro x ⟨hxZ, hxg⟩
  exact Set.mem_biUnion
    (fun hxV ↦ notMem_of_mem_genericPoints_fiber f hZ hxZ hxg (hVfib (f x) hxV))
    ⟨f.asFiber x, hxg, f.fiberι_asFiber x⟩

end AlgebraicGeometry

end
