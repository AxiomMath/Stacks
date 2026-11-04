module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.StalkOneComponent
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PushoutContraction
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.MinimalPrimeTransversality
public import StacksCore.Tactic.StacksAttribute

/-!
# A rational bridge meets the closure of its complement transversally

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge. At each point `x` of
`C ∩ X'` the ideal sheaf cutting out the intersection has stalk the whole maximal ideal of
`𝒪_{X, x}`: the two branches of the node at `x` — the bridge and the closure of the complement —
meet transversally.

## Main results

* `Stacks.Curves.stalk_intersection_bridge_eq_maximalIdeal` — the stalk of the ideal sheaf of
  `C ∩ X'` at a point of `C ∩ X'` is the maximal ideal.

## Implementation notes

The point `x` is a node of `X`, so `A = 𝒪_{X, x}` is reduced with delta invariant one and has
exactly two geometric branches, by
`Stacks.Curves.isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode`.
Exactly two irreducible components of `X` pass through `x`, namely the bridge and one component
`D` of the closure of the complement, so `A` has exactly two minimal primes
(`AlgebraicGeometry.encard_minimalPrimes_stalk_eq_two`) and they are the stalks of the vanishing
ideals of those two components: for the bridge because it is integral, and for the closure of
the complement because near `x` it agrees with `D`
(`Stacks.Curves.stalk_complementaryCurveIdeal_eq_stalk_vanishingIdeal`).

The two are distinct. Were they equal, the stalk of the ideal sheaf of `C ∩ X'` would be the
minimal prime of the bridge, so the local ring of `C ∩ X'` at `x` would be the one-dimensional
domain `A ⧸ p`; but `C ∩ X'` is zero-dimensional
(`Stacks.Curves.topologicalKrullDim_intersection_bridge_eq_zero`), which would force `p` to be
the maximal ideal, impossible with two minimal primes.

Two distinct minimal primes of a reduced local ring of delta invariant one sum to the maximal
ideal (`Ring.sup_eq_maximalIdeal_of_deltaInvariant_eq_one`), and the stalk of a join of ideal
sheaves is the join of the stalks.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- A point of the intersection of a rational bridge with the closure of its complement lies on
the bridge and on that closure. -/
theorem mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection
    {C : X.IdealSheafData} {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    x ∈ (C.support : Set X) ∧ x ∈ ((complementaryCurveIdeal C).support : Set X) := by
  simpa only [intersectionWithComplementaryCurveIdeal, Scheme.IdealSheafData.support_sup,
    TopologicalSpace.Closeds.coe_inf, Set.mem_inter_iff] using hx

/-- A point of the support of the intersection of a rational bridge with the closure of its
complement is a node of the ambient curve. -/
theorem isNode_of_mem_support_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    IsNode k X x := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨w, rfl⟩ := hx
  exact isNode_of_mem_intersection_bridge k X hdim hnodal C hC w

/-- **Exactly one irreducible component of the closure of the complement of a rational bridge
passes through a point of the intersection, and the local ring there has exactly two minimal
primes.** The point is a node, so it has two geometric branches, and the bridge is a second
component through it. -/
theorem exists_unique_component_complementaryCurve_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    ∃ D : Closeds X, ((D : Set X) ∈ irreducibleComponents X) ∧
      (¬ (D : Set X) ⊆ (C.support : Set X)) ∧ (x ∈ (D : Set X)) ∧
      (∀ E ∈ irreducibleComponents X, x ∈ E → ¬ E ⊆ (C.support : Set X) → E = (D : Set X)) ∧
      Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2 := by
  classical
  have := hC.isIntegral
  obtain ⟨hxC, hxJ⟩ := mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection hx
  obtain ⟨-, -, hbr⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim x (isNode_of_mem_support_intersection_bridge hdim hnodal hC hx)
  obtain ⟨D, hD, hDC, hxD, -⟩ :=
    exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal hnodal C hxJ
  have hCD : (C.support : Set X) ≠ (D : Set X) := fun h => hDC (h ▸ subset_rfl)
  have htwo : Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2 :=
    encard_minimalPrimes_stalk_eq_two X x hC.support_mem_irreducibleComponents hD hCD hxC hxD hbr
  have hcompsTwo : Set.encard {Z ∈ irreducibleComponents X | x ∈ Z} = 2 := by
    rw [encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk X x]; exact htwo
  have hfinPair : ({(C.support : Set X), (D : Set X)} : Set (Set X)).Finite :=
    (Set.finite_singleton _).insert _
  have hpairComps : ({(C.support : Set X), (D : Set X)} : Set (Set X)) =
      {Z ∈ irreducibleComponents X | x ∈ Z} := by
    refine hfinPair.eq_of_subset_of_encard_le ?_ ?_
    · rintro E (rfl | rfl)
      · exact ⟨hC.support_mem_irreducibleComponents, hxC⟩
      · exact ⟨hD, hxD⟩
    · rw [hcompsTwo, Set.encard_pair hCD]
  refine ⟨D, hD, hDC, hxD, ?_, htwo⟩
  intro E hE hxE hEC
  have hmem : E ∈ ({(C.support : Set X), (D : Set X)} : Set (Set X)) := by
    rw [hpairComps]; exact ⟨hE, hxE⟩
  rcases hmem with h | h
  · exact absurd (h ▸ (subset_rfl : E ⊆ E)) hEC
  · exact h

/-- **A prime stalk of the ideal sheaf of the intersection of a rational bridge with the closure
of its complement is the maximal ideal.** The quotient by that stalk is the local ring of the
intersection, which is zero-dimensional; a zero-dimensional local domain is a field. -/
theorem eq_maximalIdeal_of_isPrime_stalk_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X))
    (hprime : (IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x).IsPrime) :
    IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  classical
  have := hprime
  have : IsDomain (X.presheaf.stalk x ⧸
      IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x) :=
    Ideal.Quotient.isDomain _
  have : IsLocalRing (X.presheaf.stalk x ⧸
      IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hdim0 : ringKrullDim (X.presheaf.stalk x ⧸
      IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x) ≤ (0 : ℕ) := by
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx
    obtain ⟨w, rfl⟩ := hx
    have hker : RingHom.ker
          ((intersectionWithComplementaryCurveIdeal C).subschemeι.stalkMap w).hom =
        IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C)
          ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w) :=
      (IdealSheafData.stalk_ker_of_isClosedImmersion
        (intersectionWithComplementaryCurveIdeal C).subschemeι w).symm.trans
        (congrArg (fun I : X.IdealSheafData => IdealSheafData.stalk I
          ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w))
          (Scheme.IdealSheafData.ker_subschemeι _))
    have e : (X.presheaf.stalk
          ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w) ⧸
          IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C)
            ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w)) ≃+*
        (intersectionWithComplementaryCurveIdeal C).subscheme.presheaf.stalk w :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective
        ((intersectionWithComplementaryCurveIdeal C).subschemeι.stalkMap_surjective w))
    rw [ringKrullDim_eq_of_ringEquiv e, Nat.cast_zero,
      ← topologicalKrullDim_intersection_bridge_eq_zero hdim hnodal hC]
    exact ringKrullDim_stalk_le_topologicalKrullDim w
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x ⧸
      IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x) :=
    Ring.krullDimLE_iff.mpr hdim0
  exact IsLocalRing.eq_maximalIdeal
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
      Ring.KrullDimLE.isField_of_isDomain)

omit [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] in
/-- **The stalk of a rational bridge at a point of its support is a minimal prime of the local
ring there.** A rational bridge is integral, hence the reduced closed subscheme on its support,
which is an irreducible component. -/
theorem stalk_mem_minimalPrimes_of_isRationalBridge
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ (C.support : Set X)) :
    IdealSheafData.stalk C x ∈ minimalPrimes (X.presheaf.stalk x) := by
  have := hC.isIntegral
  have hCeq : C = Scheme.IdealSheafData.vanishingIdeal C.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme C C.support rfl
  rw [congrArg (fun I : X.IdealSheafData => IdealSheafData.stalk I x) hCeq]
  exact stalk_vanishingIdeal_mem_minimalPrimes x
    ⟨(C.support : Set X), hC.support_mem_irreducibleComponents⟩ hx

/-- **At a point of the intersection, the stalk of a rational bridge differs from the stalk of
the closure of its complement.** Were they equal, the stalk of the ideal sheaf of the
intersection would be that one minimal prime, hence the maximal ideal by
`Stacks.Curves.eq_maximalIdeal_of_isPrime_stalk_intersection_bridge`; but a local ring with two
minimal primes has none equal to its maximal ideal. -/
theorem stalk_bridge_ne_stalk_complementaryCurveIdeal
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    IdealSheafData.stalk C x ≠ IdealSheafData.stalk (complementaryCurveIdeal C) x := by
  intro h
  obtain ⟨hxC, -⟩ := mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection hx
  have hp := stalk_mem_minimalPrimes_of_isRationalBridge hC hxC
  obtain ⟨-, -, -, -, -, htwo⟩ :=
    exists_unique_component_complementaryCurve_bridge hdim hnodal hC hx
  have hpm := ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard hp (by rw [htwo]; decide)
  have hsup : IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x =
      IdealSheafData.stalk C x := by
    rw [IdealSheafData.stalk_sup, ← h, sup_idem]
  exact hpm (hsup ▸ eq_maximalIdeal_of_isPrime_stalk_intersection_bridge hdim hnodal hC hx
    (hsup ▸ hp.1.1))

/-- **A rational bridge meets the closure of its complement transversally.** At a point of
`C ∩ X'` the stalk of the ideal sheaf cutting out the intersection is the whole maximal ideal of
the local ring of the ambient curve. -/
theorem stalk_intersection_bridge_eq_maximalIdeal
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal C) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  classical
  obtain ⟨hxC, -⟩ := mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection hx
  obtain ⟨hred, hδ, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim x (isNode_of_mem_support_intersection_bridge hdim hnodal hC hx)
  have : _root_.IsReduced (X.presheaf.stalk x) := hred
  obtain ⟨D, hD, hDC, hxD, huniq, htwo⟩ :=
    exists_unique_component_complementaryCurve_bridge hdim hnodal hC hx
  have hp := stalk_mem_minimalPrimes_of_isRationalBridge hC hxC
  have hq : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D) x ∈
      minimalPrimes (X.presheaf.stalk x) :=
    stalk_vanishingIdeal_mem_minimalPrimes x ⟨(D : Set X), hD⟩ hxD
  have hJ : IdealSheafData.stalk (complementaryCurveIdeal C) x =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D) x :=
    stalk_complementaryCurveIdeal_eq_stalk_vanishingIdeal hnodal C D hD hDC hxD huniq
  have hfin : (minimalPrimes (X.presheaf.stalk x)).Finite :=
    Set.encard_ne_top_iff.mp (by rw [htwo]; decide)
  have hne' : IdealSheafData.stalk C x ≠
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal D) x := fun hEq =>
    stalk_bridge_ne_stalk_complementaryCurveIdeal hdim hnodal hC hx (hEq.trans hJ.symm)
  rw [IdealSheafData.stalk_sup, hJ]
  exact Ring.sup_eq_maximalIdeal_of_mem_minimalPrimes_of_deltaInvariant_eq_one
    (X.presheaf.stalk x) hfin hp hq hne' hδ

end Stacks.Curves

end
