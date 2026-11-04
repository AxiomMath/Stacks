module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.UnionOfClosedSubschemes
public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ComplementaryNodal
public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The intersection of a rational bridge with the closure of its complement is smooth on both

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge (Tag 0E3M). Write `X'` for
the scheme-theoretic closure of `X \ C`. This file proves the assertion of [Stacks, Tag 0E3M]
that the points of `C ∩ X'` are smooth points of `C` and smooth points of `X'`.

## Main results

* `Stacks.Curves.isRegularLocalRing_stalk_subscheme_of_mem_minimalPrimes` — the local ring of a
  closed subscheme at a point where its stalk is one of exactly two minimal primes of a reduced
  ambient local ring of delta invariant one is a regular local ring.
* `Stacks.Curves.smoothAt_bridge_intersection` — the bridge is smooth over `k` at a point of
  `C ∩ X'`; the closure of the complement is so by
  `Stacks.Curves.smoothAt_complementaryCurve_intersection_bridge`.
* `Stacks.Curves.smoothAt_bridge_and_complementaryCurve_of_mem_intersection` — both at once,
  which is the clause of [Stacks, Tag 0E3M].

## Implementation notes

The argument is the one of `Curves/CanonicalContraction/SmoothAtAttaching.lean`, run twice and
symmetrically in the two branches. At a point `x` of `C ∩ X'` the curve `X` has a node, so
`A = 𝒪_{X, x}` is reduced with delta invariant one and exactly two minimal primes; those two are
the stalk of the bridge and the stalk of the ideal sheaf of `X'`
(`Stacks.Curves.stalk_mem_minimalPrimes_of_isRationalBridge` and
`Stacks.Curves.stalk_complementaryCurveIdeal_mem_minimalPrimes_bridge`), and they are distinct
(`Stacks.Curves.stalk_bridge_ne_stalk_complementaryCurveIdeal`). The local ring of either branch
at `x` is the quotient of `A` by the corresponding minimal prime, by
`AlgebraicGeometry.IdealSheafData.subschemeStalkQuotEquiv`, and
`Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one` makes such a
quotient a discrete valuation ring once it is one-dimensional. So no distinction between the two
branches is needed and both halves are instances of one lemma about an arbitrary closed
subscheme, which is where the work is done; the two clauses differ only in the ideal sheaf fed
to it and in the source of the one-dimensionality of the branch.

The residue field of either branch at `x` is the residue field of `X` at `x`, a closed immersion
inducing an isomorphism on residue fields
(`Stacks.Curves.bijective_residueFieldMap_of_isClosedImmersion`), and that field is separable
over `k` because `x` is a node
(`Stacks.Curves.isSeparableExtension_residueField_of_isNode`). Over a field, smoothness at a
point with separable residue field is regularity of the local ring,
`AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0C35](https://stacks.math.columbia.edu/tag/0C35)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-! ### The local ring of a branch through a point with two minimal primes -/

section Branch

variable {X : Scheme.{u}}

/-- **The local ring of the closed subscheme cut out by `I` at a point where the stalk of `I` is
one of exactly two minimal primes of the ambient local ring is one-dimensional.** The subscheme
is one-dimensional, which bounds the dimension above; and the local ring is the quotient of the
ambient local ring by a minimal prime which is not the maximal ideal — two minimal primes leave
no minimal prime maximal — so it is a local domain which is not a field. -/
theorem ringKrullDim_stalk_subscheme_eq_one {I : X.IdealSheafData} (z : I.subscheme) {x : X}
    (hzx : I.subschemeι.base z = x)
    (hmin : IdealSheafData.stalk I x ∈ minimalPrimes (X.presheaf.stalk x))
    (htwo : Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2)
    (hdim : topologicalKrullDim I.subscheme = 1) :
    ringKrullDim (I.subscheme.presheaf.stalk z) = 1 := by
  subst hzx
  have hne := ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard hmin (by rw [htwo]; decide)
  have : (IdealSheafData.stalk I (I.subschemeι.base z)).IsPrime := hmin.1.1
  have : IsDomain (X.presheaf.stalk (I.subschemeι.base z) ⧸
      IdealSheafData.stalk I (I.subschemeι.base z)) := Ideal.Quotient.isDomain _
  have hone : 1 ≤ ringKrullDim (X.presheaf.stalk (I.subschemeι.base z) ⧸
      IdealSheafData.stalk I (I.subschemeι.base z)) := by
    have hnk : ¬ Ring.KrullDimLE 0 (X.presheaf.stalk (I.subschemeι.base z) ⧸
        IdealSheafData.stalk I (I.subschemeι.base z)) := fun _ =>
      hne (IsLocalRing.eq_maximalIdeal ((Ideal.Quotient.maximal_ideal_iff_isField_quotient
        _).mpr Ring.KrullDimLE.isField_of_isDomain))
    rw [Ring.krullDimLE_iff] at hnk
    exact (WithBot.one_le_iff_pos _).2 (lt_of_not_ge hnk)
  rw [ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I z)] at hone
  refine le_antisymm ?_ hone
  rw [← hdim]
  exact ringKrullDim_stalk_le_topologicalKrullDim z

/-- **The local ring of a branch through a node is a regular local ring.** Precisely: let `I` cut
out a one-dimensional closed subscheme of `X` through a point `x` at which the local ring of `X`
is reduced with delta invariant one and has exactly two minimal primes, one of them the stalk of
`I`. Then the local ring of that subscheme at `x` is regular.

The quotient of such an ambient local ring by a minimal prime is a discrete valuation ring once
it is one-dimensional
(`Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one`), and a
one-dimensional Noetherian local domain is regular exactly when it is a discrete valuation ring,
`AlgebraicGeometry.isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one`. -/
theorem isRegularLocalRing_stalk_subscheme_of_mem_minimalPrimes
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    {I : X.IdealSheafData} (z : I.subscheme) {x : X}
    (hzx : I.subschemeι.base z = x)
    (hred : _root_.IsReduced (X.presheaf.stalk x))
    (hδ : Ring.deltaInvariant (X.presheaf.stalk x) = 1)
    (htwo : Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2)
    (hmin : IdealSheafData.stalk I x ∈ minimalPrimes (X.presheaf.stalk x))
    (hdim : topologicalKrullDim I.subscheme = 1) :
    IsRegularLocalRing (I.subscheme.presheaf.stalk z) := by
  subst hzx
  have : IsNagataRing (X.presheaf.stalk (I.subschemeι.base z)) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) _
  have : (IdealSheafData.stalk I (I.subschemeι.base z)).IsPrime := hmin.1.1
  have : IsDomain (X.presheaf.stalk (I.subschemeι.base z) ⧸
      IdealSheafData.stalk I (I.subschemeι.base z)) := Ideal.Quotient.isDomain _
  have : IsLocalRing (X.presheaf.stalk (I.subschemeι.base z) ⧸
      IdealSheafData.stalk I (I.subschemeι.base z)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hdimq : ringKrullDim (X.presheaf.stalk (I.subschemeι.base z) ⧸
      IdealSheafData.stalk I (I.subschemeι.base z)) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I z)]
    exact ringKrullDim_stalk_subscheme_eq_one z rfl hmin htwo hdim
  obtain ⟨a, b, hab, hset⟩ := Set.encard_eq_two.mp htwo
  have ha : a ∈ minimalPrimes (X.presheaf.stalk (I.subschemeι.base z)) := by
    simp [hset]
  have hb : b ∈ minimalPrimes (X.presheaf.stalk (I.subschemeι.base z)) := by
    simp [hset]
  have hfin : (minimalPrimes (X.presheaf.stalk (I.subschemeι.base z))).Finite :=
    Set.encard_ne_top_iff.mp (by rw [htwo]; decide)
  have hab' : (⟨a, ha⟩ : minimalPrimes (X.presheaf.stalk (I.subschemeι.base z))) ≠ ⟨b, hb⟩ :=
    fun h => hab (Subtype.ext_iff.mp h)
  obtain ⟨hdom, hdvr⟩ :=
    Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one
      (X.presheaf.stalk (I.subschemeι.base z)) inferInstance hfin hab' hδ ⟨_, hmin⟩ hdimq
  have : IsRegularLocalRing (X.presheaf.stalk (I.subschemeι.base z) ⧸
      IdealSheafData.stalk I (I.subschemeι.base z)) :=
    ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one _ hdimq).out 3 1).mp hdvr
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I z)

/-- **The residue field of a closed subscheme at a point is the residue field of the ambient
scheme there**, as an extension of the ground field; so separability over the ground field
transfers. The closed immersion induces an isomorphism on residue fields
(`Stacks.Curves.bijective_residueFieldMap_of_isClosedImmersion`) compatible with the structure
maps. -/
theorem isSeparableExtension_residueField_subscheme (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] {I : X.IdealSheafData} (z : I.subscheme)
    (hsep : letI : Algebra k (X.residueField (I.subschemeι.base z)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
          X.Γevaluation (I.subschemeι.base z)).hom.toAlgebra
      Algebra.IsSeparableExtension k (X.residueField (I.subschemeι.base z))) :
    letI : Algebra k (I.subscheme.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
        I.subscheme.Γevaluation z).hom.toAlgebra
    Algebra.IsSeparableExtension k (I.subscheme.residueField z) := by
  let algX : Algebra k (X.residueField (I.subschemeι.base z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.Γevaluation (I.subschemeι.base z)).hom.toAlgebra
  have hsepX : @Algebra.IsSeparableExtension k (X.residueField (I.subschemeι.base z)) _ _ algX :=
    hsep
  let algZ : Algebra k (I.subscheme.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
      I.subscheme.Γevaluation z).hom.toAlgebra
  exact Algebra.IsSeparableExtension.of_algEquiv
    { __ := RingEquiv.ofBijective (I.subschemeι.residueFieldMap z).hom
        (bijective_residueFieldMap_of_isClosedImmersion I.subschemeι z)
      commutes' := fun r => by
        simp only [algX, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.coe_comp,
          Function.comp_apply, Scheme.Hom.comp_appTop]
        exact Scheme.Γevaluation_naturality_apply I.subschemeι z _ }

/-- **A branch through a node is smooth over the ground field there.** The local ring of the
branch is regular (`Stacks.Curves.isRegularLocalRing_stalk_subscheme_of_mem_minimalPrimes`) and
its residue field is separable over `k`, which over a field is exactly smoothness
(`AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk`). -/
theorem smoothAt_subscheme_of_mem_minimalPrimes
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    {I : X.IdealSheafData} (z : I.subscheme) {x : X}
    (hzx : I.subschemeι.base z = x)
    (hred : _root_.IsReduced (X.presheaf.stalk x))
    (hδ : Ring.deltaInvariant (X.presheaf.stalk x) = 1)
    (htwo : Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2)
    (hmin : IdealSheafData.stalk I x ∈ minimalPrimes (X.presheaf.stalk x))
    (hdim : topologicalKrullDim I.subscheme = 1)
    (hsep : letI : Algebra k (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
          X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparableExtension k (X.residueField x)) :
    InfinitesimalLifting.SmoothAt (I.subschemeι ≫ (X ↘ Spec (.of k))) z := by
  subst hzx
  rw [smoothAt_iff_isRegularLocalRing_stalk (I.subschemeι ≫ (X ↘ Spec (.of k))) z
    (isSeparableExtension_residueField_subscheme k X z hsep)]
  exact isRegularLocalRing_stalk_subscheme_of_mem_minimalPrimes k X z rfl hred hδ htwo hmin hdim

end Branch

/-! ### The two branches at a point of the intersection -/

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- The local ring of the ambient curve at a point of the intersection of a rational bridge with
the closure of its complement is reduced, of delta invariant one, and has exactly two minimal
primes: the point is a node. -/
theorem isReduced_deltaInvariant_encard_minimalPrimes_stalk_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    _root_.IsReduced (X.presheaf.stalk x) ∧
      Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
        Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2 := by
  obtain ⟨hred, hδ, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim x (isNode_of_mem_support_intersection_bridge hdim hnodal hC hx)
  obtain ⟨-, -, -, -, -, htwo⟩ :=
    exists_unique_component_complementaryCurve_bridge hdim hnodal hC hx
  exact ⟨hred, hδ, htwo⟩

/-- The image of a point of a closed subscheme lies in the support of its ideal sheaf. -/
private theorem subschemeι_base_mem_support {I : X.IdealSheafData} (w : I.subscheme) :
    I.subschemeι.base w ∈ (I.support : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩

/-- **A rational bridge is smooth over the ground field at each point of its intersection with
the closure of its complement.** The point is a node of `X`; the bridge is one of its two
branches, so its local ring is a discrete valuation ring, and the residue field is separable. -/
theorem smoothAt_bridge_intersection
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (w : intersectionWithComplementaryCurve C) :
    InfinitesimalLifting.SmoothAt (C.subschemeι ≫ (X ↘ Spec (.of k)))
      ((Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).base w) := by
  set z := (Scheme.IdealSheafData.inclusion
    (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).base w
  have hbase : C.subschemeι.base z =
      (intersectionWithComplementaryCurveIdeal C).subschemeι.base w :=
    Stacks.Chow.inclusion_subschemeι_base
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) w
  have hx := subschemeι_base_mem_support (I := intersectionWithComplementaryCurveIdeal C) w
  obtain ⟨hred, hδ, htwo⟩ :=
    isReduced_deltaInvariant_encard_minimalPrimes_stalk_intersection_bridge hdim hnodal hC hx
  obtain ⟨hxC, -⟩ := mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection hx
  have hdimC : topologicalKrullDim C.subscheme = 1 :=
    (isReduced_and_equidimensional_and_dim_bridge hdim hC).2.2
  have hminC := stalk_mem_minimalPrimes_of_isRationalBridge hC hxC
  have hsepC := isSeparableExtension_residueField_of_isNode k X hdim
    ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w)
    (isNode_of_mem_support_intersection_bridge hdim hnodal hC hx)
  exact smoothAt_subscheme_of_mem_minimalPrimes k X z hbase hred hδ htwo hminC hdimC hsepC

/-- **The points of `C ∩ X'` are smooth points on both `C` and `X'`.** This is the clause of
[Stacks, Tag 0E3M] which the source draws from [Stacks, Tag 0E38] after observing that the
points of the intersection are nodes of `X`: a node has two branches, and here they are the
bridge and the closure of the complement, each smooth at the point. -/
@[stacks 0E3M "the points of C ∩ X' are smooth points of C and of X'"]
theorem smoothAt_bridge_and_complementaryCurve_of_mem_intersection
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
    (w : intersectionWithComplementaryCurve C) :
    InfinitesimalLifting.SmoothAt (C.subschemeι ≫ (X ↘ Spec (.of k)))
        ((Scheme.IdealSheafData.inclusion
          (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).base w) ∧
      InfinitesimalLifting.SmoothAt (complementaryCurveι C ≫ (X ↘ Spec (.of k)))
        ((Scheme.IdealSheafData.inclusion
          (le_sup_right : complementaryCurveIdeal C ≤
            intersectionWithComplementaryCurveIdeal C)).base w) :=
  ⟨smoothAt_bridge_intersection hdim hnodal hC w,
    smoothAt_complementaryCurve_intersection_bridge hdim hnodal hC _ (by
      obtain ⟨hxC, -⟩ := mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection
        (subschemeι_base_mem_support (I := intersectionWithComplementaryCurveIdeal C) w)
      rw [Stacks.Chow.inclusion_subschemeι_base
        (le_sup_right : complementaryCurveIdeal C ≤
          intersectionWithComplementaryCurveIdeal C) w]
      exact hxC)⟩

end Stacks.Curves

end
