module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.IntersectionSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The closure of the complement of a rational bridge is at worst nodal, and smooth where it meets
the bridge

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge (Tag 0E3M). Write `X'` for
the scheme-theoretic closure of `X \ C`. At each point of `C ∩ X'` the curve `X'` is one branch
of a node of `X`, hence smooth over `k`; away from `C` it agrees with `X`. So `X'` again has
at-worst-nodal singularities.

## Main results

* `Stacks.Curves.stalk_complementaryCurveIdeal_mem_minimalPrimes_bridge` — at a point of
  `C ∩ X'` the stalk of the ideal sheaf cutting out `X'` is a minimal prime of `𝒪_{X, x}`.
* `Stacks.Curves.isRegularLocalRing_stalk_complementaryCurve_bridge` — `𝒪_{X', p}` is a regular
  local ring there.
* `Stacks.Curves.smoothAt_complementaryCurve_intersection_bridge` — so `X'` is smooth over `k`
  at `p`.
* `Stacks.Curves.hasAtWorstNodalSingularities_complementaryCurve_bridge` — `X'` has
  at-worst-nodal singularities.

## Implementation notes

The point `x` of `C ∩ X'` is a node of `X`, so `𝒪_{X, x}` is reduced with delta invariant one
and exactly two minimal primes; one is the stalk of the bridge, the other the stalk of the ideal
sheaf of `X'`, which near `x` agrees with the vanishing ideal of the single irreducible component
of `X'` through `x`
(`Stacks.Curves.stalk_complementaryCurveIdeal_eq_stalk_vanishingIdeal`). The local ring of `X'`
at the point over `x` is the quotient of `𝒪_{X, x}` by that minimal prime, and such a quotient of
a reduced local ring of delta invariant one is a discrete valuation ring once it is
one-dimensional
(`Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one`). Smoothness over
`k` at a point with separable residue field is regularity of the local ring
(`AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk`), and the residue field is separable
because `x` is a node.

Away from `C` the open complement of `C` in `X` is an open subscheme of `X'`
(`Stacks.Curves.tailComplementIso`), so the dichotomy "smooth or a node" transports from `X` by
`Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm`. A point of `X'` lying over `C` lies in the
scheme-theoretic intersection, which is where the smoothness assertion applies.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0C57](https://stacks.math.columbia.edu/tag/0C57)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **At a point where a rational bridge meets the closure of its complement, the stalk of the
ideal sheaf cutting out that closure is a minimal prime of the ambient local ring.** Near such a
point the closure agrees with the single irreducible component of it passing through the point,
and the stalk of the vanishing ideal of an irreducible component is a minimal prime. -/
theorem stalk_complementaryCurveIdeal_mem_minimalPrimes_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    IdealSheafData.stalk (complementaryCurveIdeal C) x ∈
      minimalPrimes (X.presheaf.stalk x) := by
  obtain ⟨D, hD, hDC, hxD, huniq, -⟩ :=
    exists_unique_component_complementaryCurve_bridge hdim hnodal hC hx
  rw [stalk_complementaryCurveIdeal_eq_stalk_vanishingIdeal hnodal C D hD hDC hxD huniq]
  exact stalk_vanishingIdeal_mem_minimalPrimes x ⟨(D : Set X), hD⟩ hxD

/-- **At a point where a rational bridge meets the closure of its complement, the stalk of the
ideal sheaf cutting out that closure is not the maximal ideal.** The ambient local ring has two
distinct minimal primes there, and no minimal prime of such a local ring is the maximal
ideal. -/
theorem stalk_complementaryCurveIdeal_ne_maximalIdeal_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    IdealSheafData.stalk (complementaryCurveIdeal C) x ≠
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨-, -, -, -, -, htwo⟩ :=
    exists_unique_component_complementaryCurve_bridge hdim hnodal hC hx
  exact ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard
    (stalk_complementaryCurveIdeal_mem_minimalPrimes_bridge hdim hnodal hC hx)
    (by rw [htwo]; decide)

/-- A point of the closure of the complement of a rational bridge lying over the bridge lies over
a point of the scheme-theoretic intersection of the two. -/
theorem mem_support_intersection_of_mem_support_bridge
    {C : X.IdealSheafData} (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y ∈ (C.support : Set X)) :
    (complementaryCurveι C).base y ∈
      ((intersectionWithComplementaryCurveIdeal C).support : Set X) := by
  have hy' : (complementaryCurveι C).base y ∈
      ((complementaryCurveIdeal C).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  simp only [intersectionWithComplementaryCurveIdeal, Scheme.IdealSheafData.support_sup,
    TopologicalSpace.Closeds.coe_inf, Set.mem_inter_iff]
  exact ⟨hy, hy'⟩

/-- The closure of the complement of a rational bridge is one-dimensional. -/
private theorem topologicalKrullDim_complementaryCurve_eq_one_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    topologicalKrullDim (complementaryCurve C) = 1 :=
  topologicalKrullDim_complementaryCurve_eq_one
    (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim) hdim
    hnodal C hC.complementaryCurve_nonempty

/-- The local ring of the closure at `y` is the ambient local ring modulo the stalk of the ideal
sheaf cutting out the closure. -/
private theorem nonempty_ringEquiv_quotient_stalk_complementaryCurve_bridge
    (C : X.IdealSheafData) (y : complementaryCurve C) :
    Nonempty (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y) ≃+*
        (complementaryCurve C).presheaf.stalk y) := by
  obtain ⟨e⟩ := nonempty_ringEquiv_stalk_complementaryCurve C y
  rw [ker_stalkMap_complementaryCurveι C y] at e
  exact ⟨e⟩

/-- **The local ring of the closure of the complement of a rational bridge at a point over the
intersection is one-dimensional.** The closure is one-dimensional, which bounds the dimension
above; and the local ring is the quotient of the ambient local ring by a minimal prime which is
not the maximal ideal, so it is a local domain which is not a field. -/
theorem ringKrullDim_stalk_complementaryCurve_bridge_eq_one
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y ∈ (C.support : Set X)) :
    ringKrullDim ((complementaryCurve C).presheaf.stalk y) = 1 := by
  have hx := mem_support_intersection_of_mem_support_bridge y hy
  have hJmin := stalk_complementaryCurveIdeal_mem_minimalPrimes_bridge hdim hnodal hC hx
  have hJne := stalk_complementaryCurveIdeal_ne_maximalIdeal_bridge hdim hnodal hC hx
  have : (IdealSheafData.stalk (complementaryCurveIdeal C)
      ((complementaryCurveι C).base y)).IsPrime := hJmin.1.1
  have : IsDomain (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    Ideal.Quotient.isDomain _
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_stalk_complementaryCurve_bridge C y
  have hone : 1 ≤ ringKrullDim (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) := by
    have hnk : ¬ Ring.KrullDimLE 0 (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
        IdealSheafData.stalk (complementaryCurveIdeal C)
          ((complementaryCurveι C).base y)) := fun _ =>
      hJne (IsLocalRing.eq_maximalIdeal ((Ideal.Quotient.maximal_ideal_iff_isField_quotient
        _).mpr Ring.KrullDimLE.isField_of_isDomain))
    rw [Ring.krullDimLE_iff] at hnk
    exact (WithBot.one_le_iff_pos _).2 (lt_of_not_ge hnk)
  rw [ringKrullDim_eq_of_ringEquiv e] at hone
  refine le_antisymm ?_ hone
  rw [← topologicalKrullDim_complementaryCurve_eq_one_bridge hdim hnodal hC]
  exact ringKrullDim_stalk_le_topologicalKrullDim y

/-- **The local ring of the closure of the complement of a rational bridge at a point over the
intersection is a regular local ring.** The ambient local ring is reduced with delta invariant
one and exactly two minimal primes, and the quotient of such a ring by a minimal prime is a
discrete valuation ring once it is one-dimensional. -/
theorem isRegularLocalRing_stalk_complementaryCurve_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y ∈ (C.support : Set X)) :
    IsRegularLocalRing ((complementaryCurve C).presheaf.stalk y) := by
  have hx := mem_support_intersection_of_mem_support_bridge y hy
  obtain ⟨hred, hδ, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim ((complementaryCurveι C).base y)
      (isNode_of_mem_support_intersection_bridge hdim hnodal hC hx)
  obtain ⟨-, -, -, -, -, htwo⟩ :=
    exists_unique_component_complementaryCurve_bridge hdim hnodal hC hx
  have := hred
  have : IsNagataRing (X.presheaf.stalk ((complementaryCurveι C).base y)) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) _
  have hJmin := stalk_complementaryCurveIdeal_mem_minimalPrimes_bridge hdim hnodal hC hx
  have : (IdealSheafData.stalk (complementaryCurveIdeal C)
      ((complementaryCurveι C).base y)).IsPrime := hJmin.1.1
  have : IsDomain (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    Ideal.Quotient.isDomain _
  have : IsLocalRing (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_stalk_complementaryCurve_bridge C y
  have hdimq : ringKrullDim (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C)
        ((complementaryCurveι C).base y)) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact ringKrullDim_stalk_complementaryCurve_bridge_eq_one hdim hnodal hC y hy
  obtain ⟨a, b, hab, hset⟩ := Set.encard_eq_two.mp htwo
  have ha : a ∈ minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y)) := by
    rw [hset]; exact Set.mem_insert _ _
  have hb : b ∈ minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y)) := by
    rw [hset]; exact Set.mem_insert_of_mem _ rfl
  have hNag : IsNagataRing (X.presheaf.stalk ((complementaryCurveι C).base y)) := inferInstance
  have hfin : (minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y))).Finite :=
    Set.encard_ne_top_iff.mp (by rw [htwo]; decide)
  have hab' : (⟨a, ha⟩ : minimalPrimes (X.presheaf.stalk ((complementaryCurveι C).base y))) ≠
      ⟨b, hb⟩ := fun h => hab (Subtype.ext_iff.mp h)
  obtain ⟨hdom, hdvr⟩ :=
    Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one
      (X.presheaf.stalk ((complementaryCurveι C).base y)) hNag hfin hab' hδ ⟨_, hJmin⟩ hdimq
  have := hdom
  have : IsRegularLocalRing (X.presheaf.stalk ((complementaryCurveι C).base y) ⧸
      IdealSheafData.stalk (complementaryCurveIdeal C) ((complementaryCurveι C).base y)) :=
    ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one _ hdimq).out 3 1).mp hdvr
  exact IsRegularLocalRing.of_ringEquiv e

/-- **The residue field of the closure of the complement of a rational bridge at a point over the
intersection is separable over the base field.** The image of the point in `X` is a node, so the
residue field there is separable over `k`, and the closed immersion of the closure into `X`
identifies the two residue fields as extensions of `k`. -/
theorem isSeparableExtension_residueField_complementaryCurve_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y ∈ (C.support : Set X)) :
    letI : Algebra k ((complementaryCurve C).residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop ≫
          (complementaryCurve C).Γevaluation y).hom.toAlgebra
    Algebra.IsSeparableExtension k ((complementaryCurve C).residueField y) := by
  have hx := mem_support_intersection_of_mem_support_bridge y hy
  let algX : Algebra k (X.residueField ((complementaryCurveι C).base y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.Γevaluation ((complementaryCurveι C).base y)).hom.toAlgebra
  have hsepX : Algebra.IsSeparableExtension k
      (X.residueField ((complementaryCurveι C).base y)) :=
    isSeparableExtension_residueField_of_isNode k X hdim _
      (isNode_of_mem_support_intersection_bridge hdim hnodal hC hx)
  let algX' : Algebra k ((complementaryCurve C).residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop ≫
        (complementaryCurve C).Γevaluation y).hom.toAlgebra
  exact Algebra.IsSeparableExtension.of_algEquiv
    { __ := RingEquiv.ofBijective ((complementaryCurveι C).residueFieldMap y).hom
        (bijective_residueFieldMap_of_isClosedImmersion (complementaryCurveι C) y)
      commutes' := fun r => by
        simp only [algX, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.coe_comp,
          Function.comp_apply, Scheme.Hom.comp_appTop]
        exact Scheme.Γevaluation_naturality_apply (complementaryCurveι C) y _ }

/-- **The closure of the complement of a rational bridge is smooth over the base field at every
point over the intersection.** Its local ring there is regular and its residue field is separable
over `k`, and over a field smoothness at a point with separable residue field is exactly
regularity of the local ring. -/
theorem smoothAt_complementaryCurve_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y ∈ (C.support : Set X)) :
    InfinitesimalLifting.SmoothAt (complementaryCurveι C ≫ (X ↘ Spec (.of k))) y := by
  have : IsProper (complementaryCurveι C ≫ (X ↘ Spec (.of k))) :=
    isProper_complementaryCurve k X C
  rw [smoothAt_iff_isRegularLocalRing_stalk (complementaryCurveι C ≫ (X ↘ Spec (.of k))) y
    (isSeparableExtension_residueField_complementaryCurve_bridge hdim hnodal hC y hy)]
  exact isRegularLocalRing_stalk_complementaryCurve_bridge hdim hnodal hC y hy

/-- **Away from the bridge, the closure of the complement of a rational bridge is smooth over the
base field or has a node.** The open complement of `C` in `X` is an open subscheme of both `X`
and `X'`, so the dichotomy transports étale-locally. -/
theorem smoothAt_or_isNode_complementaryCurve_bridge_of_notMem_support
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : complementaryCurve C) (hyc : IsClosed ({y} : Set (complementaryCurve C)))
    (hy : (complementaryCurveι C).base y ∈ (C.support.compl : X.Opens)) :
    letI : (complementaryCurve C).Over (Spec (.of k)) :=
      ⟨complementaryCurveι C ≫ (X ↘ Spec (.of k))⟩
    InfinitesimalLifting.SmoothAt (complementaryCurveι C ≫ (X ↘ Spec (.of k))) y ∨
      IsNode k (complementaryCurve C) y := by
  have hdim' := topologicalKrullDim_complementaryCurve_eq_one_bridge hdim hnodal hC
  have hyV : y ∈ (complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens) := hy
  have hιeq : Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)) ≫
        complementaryCurveι C =
      (tailComplementIso k X C).inv ≫ Scheme.Opens.ι (C.support.compl : X.Opens) :=
    (((tailComplementIso k X C).inv_comp_eq).2 (tailComplementIso_hom_ι k X C).symm).symm
  have hcomm : Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)) ≫
        (complementaryCurveι C ≫ (X ↘ Spec (.of k))) =
      ((tailComplementIso k X C).inv ≫ Scheme.Opens.ι (C.support.compl : X.Opens)) ≫
        (X ↘ Spec (.of k)) := by
    rw [← Category.assoc, hιeq]
  have hab : ((tailComplementIso k X C).inv ≫
        Scheme.Opens.ι (C.support.compl : X.Opens)).base ⟨y, hyV⟩ =
      (complementaryCurveι C).base y := by
    rw [← hιeq]
    rfl
  have hxclosed : IsClosed ({(complementaryCurveι C).base y} : Set X) := by
    have h := (complementaryCurveι C).isClosedEmbedding.isClosedMap _ hyc
    rwa [Set.image_singleton] at h
  have hX := hnodal ((complementaryCurveι C).base y) hxclosed
  rw [← hab] at hX
  exact smoothAt_or_isNode_of_etale_of_comm k (X ↘ Spec (.of k))
    (complementaryCurveι C ≫ (X ↘ Spec (.of k))) hdim hdim'
    ((tailComplementIso k X C).inv ≫ Scheme.Opens.ι (C.support.compl : X.Opens))
    (Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)))
    hcomm ⟨y, hyV⟩ hX

/-- **The closure of the complement of a rational bridge again has at-worst-nodal
singularities.** Over the bridge it is in fact smooth over `k`
(`Stacks.Curves.smoothAt_complementaryCurve_intersection_bridge`); away from the bridge the
dichotomy transports from `X`. -/
theorem hasAtWorstNodalSingularities_complementaryCurve_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    letI : (complementaryCurve C).Over (Spec (.of k)) :=
      ⟨complementaryCurveι C ≫ (X ↘ Spec (.of k))⟩
    HasAtWorstNodalSingularities k (complementaryCurve C) := by
  intro y hyc
  by_cases hy : (complementaryCurveι C).base y ∈ (C.support : Set X)
  · exact Or.inl (smoothAt_complementaryCurve_intersection_bridge hdim hnodal hC y hy)
  · exact smoothAt_or_isNode_complementaryCurve_bridge_of_notMem_support hdim hnodal hC y hyc hy

end Stacks.Curves

end
