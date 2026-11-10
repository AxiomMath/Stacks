module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionStalks
public import StacksFrontier.AlgebraicGeometry.Curves.NodeMinimalPrimesSup
public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local structure of a complementary curve decomposition at an intersection point

**Stacks 0E38, parts (1), (2)(a) and (2)(c).** Let `k` be a field, let `X` be a locally algebraic
`k`-scheme, equidimensional of dimension one, whose singularities are at worst nodal, and let
`Y ⊆ X` be a reduced closed subscheme equidimensional of dimension one, cut out by the ideal sheaf
`I`. Let `Z` be the scheme-theoretic closure of `X \ Y`, cut out by
`AlgebraicGeometry.complementaryCurveIdeal I`. Then

1. the singularities of `Y` are at worst nodal;
2. (a) the scheme-theoretic intersection `Y ∩ Z` is a disjoint union of spectra of finite
   separable extensions of `k`, and (c) `Y → Spec k` is smooth at every point of `Y ∩ Z`.

Part (2)(b), that every point of `Y ∩ Z` is a node of `X`, is
`Stacks.Curves.isNode_of_mem_intersection_complementaryCurve`.

## The local picture

Let `x ∈ Y ∩ Z`. It lies on an irreducible component `C` of `X` contained in `Y` and on one, `D`,
not contained in `Y`, so it is a node of `X` by part (2)(b); hence the local ring `A = 𝒪_{X,x}` is
reduced with delta invariant one and exactly two minimal primes, and only the two components `C`
and `D` pass through `x`.

The components of `X` are locally finite, so `x` has an open neighbourhood met only by `C` and
`D`. There the support of `I` is `C` and the support of the complementary ideal is `D`, and the
stalk of a vanishing ideal only depends on the closed set near the point. So the stalks of the two
ideal sheaves at `x` are the stalks of the vanishing ideals of `C` and of `D`, which are precisely
the two minimal primes `p ≠ q` of `A`. Two consequences:

* `p + q = 𝔪` (`Stacks.Curves.sup_eq_maximalIdeal_of_isNodalAlgebra`), so the local ring of
  `Y ∩ Z` at `x` is the residue field `κ(x)`, which is a finite separable extension of `k` because
  `x` is a node (Tag 0C4D). That is part (2)(a).
* `𝒪_{Y,x} = A ⧸ p` is a discrete valuation ring
  (`Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one`), hence a regular
  local ring, and `κ(x)/k` is separable, so `Y` is smooth over `k` at `x`. That is part (2)(c).

Away from `Z` the subscheme `Y` is nothing new: the stalk of `I` vanishes on the open complement
of `Z`, so the inclusion of the preimage of that open in `Y` into `X` is an open immersion, and
the dichotomy "smooth over `k` or a node" transports along the resulting pair of étale morphisms
(`Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm`). Together with part (2)(c) at the points of
`Y ∩ Z` this gives part (1).

## Main results

* `Stacks.Curves.stalk_mem_minimalPrimes_and_sup_eq_maximalIdeal_of_mem_intersection` — the local
  computation at an intersection point.
* `Stacks.Curves.isFiniteSeparable_residueField_of_mem_intersection_complementaryCurve` — the
  residue field at a point of `Y ∩ Z` is a finite separable extension of `k`.
* `Stacks.Curves.isDiscrete_and_residueField_intersectionWithComplementaryCurve` — part (2)(a).
* `Stacks.Curves.smoothAt_of_mem_support_complementaryCurveIdeal` — part (2)(c).
* `Stacks.Curves.hasAtWorstNodalSingularities_subscheme` — part (1).
* `Stacks.Curves.topologicalKrullDim_le_zero_of_forall_isClosed_singleton` and
  `Stacks.Curves.discreteTopology_of_forall_isClosed_singleton` — a locally Noetherian scheme all
  of whose points are closed is discrete.
* `Stacks.Curves.isOpenImmersion_ι_preimage_compl_comp_subschemeι` — away from the closure of its
  complement the subcurve is an open subscheme of the ambient curve.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0E20](https://stacks.math.columbia.edu/tag/0E20)
* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-! ### The local computation at a point of the intersection -/

/-- A point of the closed subscheme cut out by `I` maps into the support of `I`. -/
private theorem subschemeι_base_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (y : I.subscheme) : I.subschemeι.base y ∈ (I.support : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨y, rfl⟩

/-- A point of the scheme-theoretic intersection maps into the supports of both ideal sheaves. -/
private theorem subschemeι_base_mem_supports_intersection {X : Scheme.{u}} (I : X.IdealSheafData)
    (w : (intersectionWithComplementaryCurveIdeal I).subscheme) :
    (intersectionWithComplementaryCurveIdeal I).subschemeι.base w ∈ (I.support : Set X) ∧
      (intersectionWithComplementaryCurveIdeal I).subschemeι.base w ∈
        ((complementaryCurveIdeal I).support : Set X) := by
  simpa only [intersectionWithComplementaryCurveIdeal, Scheme.IdealSheafData.support_sup,
    TopologicalSpace.Closeds.coe_inf, Set.mem_inter_iff] using
    subschemeι_base_mem_support (intersectionWithComplementaryCurveIdeal I) w

/-- **At a point where a reduced closed subcurve meets the closure of its complement, the stalks of
the two ideal sheaves are the two minimal primes of the local ring, and they sum to the maximal
ideal.** The point lies on an irreducible component inside the subcurve and on one outside it, and
on no others, the local ring having exactly two minimal primes there; so near the point the two
supports are those two components and the two stalks are the stalks of their vanishing ideals.
Those are the two minimal primes, and two distinct minimal primes of a node sum to the maximal
ideal. -/
theorem stalk_mem_minimalPrimes_and_sup_eq_maximalIdeal_of_mem_intersection
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    {x : X} (hxI : x ∈ (I.support : Set X))
    (hxJ : x ∈ ((complementaryCurveIdeal I).support : Set X)) :
    IsNode k X x ∧ Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2 ∧
      IdealSheafData.stalk I x ∈ minimalPrimes (X.presheaf.stalk x) ∧
      IdealSheafData.stalk (complementaryCurveIdeal I) x ∈
        minimalPrimes (X.presheaf.stalk x) ∧
      IdealSheafData.stalk I x ≠ IdealSheafData.stalk (complementaryCurveIdeal I) x ∧
      IdealSheafData.stalk I x ⊔ IdealSheafData.stalk (complementaryCurveIdeal I) x =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  classical
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  obtain ⟨C, hC, hxC, hCI⟩ := exists_component_subset_support_of_mem (k := k)
    hX_equidimensional hX_dimension I hY_equidimensional hY_dimension hxI
  obtain ⟨D, hD, hDI, hxD, -⟩ :=
    exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal hX_nodal I hxJ
  have hCD : C ≠ (D : Set X) := fun h => hDI (h ▸ hCI)
  have hxsup : x ∈ ((I ⊔ complementaryCurveIdeal I).support : Set X) := by
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨hxI, hxJ⟩
  have hnode : IsNode k X x := by
    obtain ⟨w, rfl⟩ : ∃ w : (I ⊔ complementaryCurveIdeal I).subscheme,
        (I ⊔ complementaryCurveIdeal I).subschemeι.base w = x := by
      rwa [← Scheme.IdealSheafData.range_subschemeι] at hxsup
    exact isNode_of_mem_intersection_complementaryCurve hX_equidimensional hX_dimension
      hX_nodal I hY_equidimensional hY_dimension w
  obtain ⟨hredA, -, hbr⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hX_dimension x hnode
  have := hredA
  have htwo : Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2 :=
    encard_minimalPrimes_stalk_eq_two X x hC hD hCD hxC hxD hbr
  have hthrough : {Z ∈ irreducibleComponents X | x ∈ Z} = {C, (D : Set X)} :=
    irreducibleComponentsThrough_eq_pair hC hD hCD hxC hxD
      (by rwa [encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk X x])
  have hcomponents : LocallyFinite (fun C : irreducibleComponents X => (C : Set X)) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  obtain ⟨V, hVopen, hxV, hVonly⟩ :=
    exists_isOpen_mem_forall_mem_of_locallyFinite_irreducibleComponents hcomponents x
  let Vo : X.Opens := ⟨V, hVopen⟩
  have hxVo : x ∈ Vo := hxV
  have hIeq : IdealSheafData.stalk I x =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩) x := by
    have hIv : I = Scheme.IdealSheafData.vanishingIdeal I.support :=
      Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I I.support rfl
    rw [hIv]
    refine IdealSheafData.stalk_vanishingIdeal_congr (V := Vo) hxVo ?_
    refine Set.Subset.antisymm (fun z hz => ⟨?_, hz.2⟩) (fun z hz => ⟨hCI hz.1, hz.2⟩)
    obtain ⟨E, hE, hzE, hEI⟩ := exists_component_subset_support_of_mem (k := k)
      hX_equidimensional hX_dimension I hY_equidimensional hY_dimension hz.1
    have hxE : x ∈ E := hVonly E hE ⟨z, hzE, hz.2⟩
    have hEmem : E ∈ ({C, (D : Set X)} : Set (Set X)) := by
      rw [← hthrough]
      exact ⟨hE, hxE⟩
    rcases hEmem with h | h
    · exact h ▸ hzE
    · exact absurd (h ▸ hEI) hDI
  let Zcomps := {C : Set X // C ∈ irreducibleComponents X ∧ ¬ C ⊆ (I.support : Set X)}
  have hZcomp : complementaryCurveIdeal I = Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : Zcomps, Closeds.closure C.1) :=
    complementaryCurveIdeal_eq_union_irreducibleComponents hX_nodal I
  have hZcomps_closed : IsClosed (⋃ C : Zcomps, (C.1 : Set X)) :=
    (locallyFinite_component_subfamily hcomponents _).isClosed_iUnion fun C =>
      isClosed_of_mem_irreducibleComponents C.1 C.2.1
  have hZsup : (↑(⨆ C : Zcomps, Closeds.closure C.1) : Set X) = ⋃ C : Zcomps, (C.1 : Set X) :=
    coe_iSup_closure_eq_iUnion_of_isClosed (fun C : Zcomps => C.1)
      (fun C => isClosed_of_mem_irreducibleComponents C.1 C.2.1) hZcomps_closed
  have hJeq : IdealSheafData.stalk (complementaryCurveIdeal I) x =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨(D : Set X), isClosed_of_mem_irreducibleComponents (D : Set X) hD⟩) x := by
    rw [hZcomp]
    refine IdealSheafData.stalk_vanishingIdeal_congr (V := Vo) hxVo ?_
    rw [hZsup]
    refine Set.Subset.antisymm (fun z hz => ⟨?_, hz.2⟩) (fun z hz => ⟨?_, hz.2⟩)
    · obtain ⟨E, hzE⟩ := Set.mem_iUnion.mp hz.1
      have hxE : x ∈ (E.1 : Set X) := hVonly E.1 E.2.1 ⟨z, hzE, hz.2⟩
      have hEmem : (E.1 : Set X) ∈ ({C, (D : Set X)} : Set (Set X)) := by
        rw [← hthrough]
        exact ⟨E.2.1, hxE⟩
      rcases hEmem with h | h
      · exact absurd (h ▸ hCI) E.2.2
      · exact h ▸ hzE
    · exact Set.mem_iUnion.mpr ⟨⟨(D : Set X), hD, hDI⟩, hz.1⟩
  have hpmin : IdealSheafData.stalk I x ∈ minimalPrimes (X.presheaf.stalk x) := by
    rw [hIeq]
    exact stalk_vanishingIdeal_mem_minimalPrimes x ⟨C, hC⟩ hxC
  have hqmin : IdealSheafData.stalk (complementaryCurveIdeal I) x ∈
      minimalPrimes (X.presheaf.stalk x) := by
    rw [hJeq]
    exact stalk_vanishingIdeal_mem_minimalPrimes x ⟨(D : Set X), hD⟩ hxD
  have hne : IdealSheafData.stalk I x ≠
      IdealSheafData.stalk (complementaryCurveIdeal I) x := by
    rw [hIeq, hJeq]
    exact stalk_vanishingIdeal_ne_of_ne hC hD hCD hxC hxD
  refine ⟨hnode, htwo, hpmin, hqmin, hne, ?_⟩
  let algStalk : Algebra k (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  exact sup_eq_maximalIdeal_of_isNodalAlgebra k (X.presheaf.stalk x)
    ((isNode_iff_isNodalAlgebra_stalk k X hX_dimension x).mp hnode) hpmin hqmin hne

/-! ### Part (2)(a): the intersection is a disjoint union of spectra of finite separable
extensions -/

/-- **Stacks 0E38, part (2)(a): the residue field at a point where a reduced closed subcurve meets
the closure of its complement is a finite separable extension of the base field.** Such a point is
a node of `X` by part (2)(b), and the residue field extension at a node is separable (Tag 0C4D)
and finite because the point is closed and `X` is locally of finite type over `k`. -/
@[stacks 0E38 "part (2)(a), the residue fields of the intersection are finite separable over k"]
theorem isFiniteSeparable_residueField_of_mem_intersection_complementaryCurve
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    {x : X} (hxI : x ∈ (I.support : Set X))
    (hxJ : x ∈ ((complementaryCurveIdeal I).support : Set X)) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    Module.Finite k (X.residueField x) ∧ Algebra.IsSeparableExtension k (X.residueField x) := by
  intro kToStalk
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  obtain ⟨hnode, -⟩ := stalk_mem_minimalPrimes_and_sup_eq_maximalIdeal_of_mem_intersection
    hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hxI hxJ
  have hsep : Algebra.IsSeparableExtension k (X.residueField x) :=
    isSeparableExtension_residueField_of_isNode k X hX_dimension x hnode
  refine ⟨?_, hsep⟩
  let f : X ⟶ Spec (.of k) := X ↘ Spec (.of k)
  have hxclosed : IsClosed ({x} : Set X) := hnode.1
  have : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hxclosed
    infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have : Algebra.FiniteType k (X.residueField x) := by
    change RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom = _
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  exact finite_of_finite_type_of_isJacobsonRing _ _

/-- **The scheme-theoretic intersection of a reduced closed subcurve with the closure of its
complement is reduced of dimension zero at each of its points: the stalk there of the ideal sheaf
cutting it out is the maximal ideal.** The two stalks are the two minimal primes of the local ring
of `X`, and they sum to the maximal ideal. -/
theorem stalk_intersectionWithComplementaryCurveIdeal_eq_maximalIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    {x : X} (hxI : x ∈ (I.support : Set X))
    (hxJ : x ∈ ((complementaryCurveIdeal I).support : Set X)) :
    IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal I) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨-, -, -, -, -, hsup⟩ :=
    stalk_mem_minimalPrimes_and_sup_eq_maximalIdeal_of_mem_intersection
      hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hxI hxJ
  rw [show intersectionWithComplementaryCurveIdeal I = I ⊔ complementaryCurveIdeal I from rfl,
    IdealSheafData.stalk_sup]
  exact hsup

/-! ### Part (2)(c): the subcurve is smooth at the intersection points -/

/-- **Stacks 0E38, part (2)(c): a reduced closed subcurve of a one-dimensional equidimensional
at-worst-nodal curve is smooth over the base field at every point where it meets the closure of
its complement.** At such a point the local ring of `X` is reduced with delta invariant one and
exactly two minimal primes, and the stalk of the ideal sheaf of the subcurve is one of them; the
quotient of such a local ring by a minimal prime is a discrete valuation ring, hence a regular
local ring, and over a field regularity with separable residue field is smoothness. -/
@[stacks 0E38 "part (2)(c)"]
theorem smoothAt_of_mem_support_complementaryCurveIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    (y : I.subscheme)
    (hy : I.subschemeι.base y ∈ ((complementaryCurveIdeal I).support : Set X)) :
    InfinitesimalLifting.SmoothAt (I.subschemeι ≫ (X ↘ Spec (.of k))) y := by
  classical
  set x := I.subschemeι.base y
  have hxI : x ∈ (I.support : Set X) := subschemeι_base_mem_support I y
  obtain ⟨hnode, htwo, hpmin, hqmin, hne, -⟩ :=
    stalk_mem_minimalPrimes_and_sup_eq_maximalIdeal_of_mem_intersection
      hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hxI hy
  obtain ⟨hredA, hδ, -⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hX_dimension x hnode
  have := hredA
  have : IsNagataRing (X.presheaf.stalk x) :=
    isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x
  have : (IdealSheafData.stalk I x).IsPrime := hpmin.1.1
  have : IsDomain (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) :=
    Ideal.Quotient.isDomain _
  have : IsLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (I.subschemeι.stalkMap y).hom = IdealSheafData.stalk I x := by
    rw [← IdealSheafData.stalk_ker_of_isClosedImmersion I.subschemeι y,
      Scheme.IdealSheafData.ker_subschemeι]
  obtain ⟨e⟩ : Nonempty ((X.presheaf.stalk x ⧸ RingHom.ker (I.subschemeι.stalkMap y).hom) ≃+*
      I.subscheme.presheaf.stalk y) :=
    ⟨RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective y)⟩
  rw [hker] at e
  have hone : 1 ≤ ringKrullDim (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) := by
    have hJne : IdealSheafData.stalk I x ≠ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      ne_maximalIdeal_of_mem_minimalPrimes_of_one_lt_encard hpmin (by rw [htwo]; decide)
    have hnk : ¬ Ring.KrullDimLE 0 (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) := fun _ =>
      hJne (IsLocalRing.eq_maximalIdeal ((Ideal.Quotient.maximal_ideal_iff_isField_quotient
        _).mpr Ring.KrullDimLE.isField_of_isDomain))
    rw [Ring.krullDimLE_iff] at hnk
    exact (WithBot.one_le_iff_pos _).2 (lt_of_not_ge hnk)
  have hdimq : ringKrullDim (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) = 1 := by
    refine le_antisymm ?_ hone
    rw [ringKrullDim_eq_of_ringEquiv e, ← hY_dimension]
    exact ringKrullDim_stalk_le_topologicalKrullDim y
  have hfin : (minimalPrimes (X.presheaf.stalk x)).Finite :=
    Set.encard_ne_top_iff.mp (by rw [htwo]; decide)
  have hab' : (⟨_, hpmin⟩ : minimalPrimes (X.presheaf.stalk x)) ≠ ⟨_, hqmin⟩ :=
    fun h => hne (Subtype.ext_iff.mp h)
  obtain ⟨hdom, hdvr⟩ :=
    Ring.isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one
      (X.presheaf.stalk x) inferInstance hfin hab' hδ ⟨IdealSheafData.stalk I x, hpmin⟩ hdimq
  have := hdom
  have : IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x) :=
    ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one _ hdimq).out 3 1).mp hdvr
  let algX : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hsepX : Algebra.IsSeparableExtension k (X.residueField x) :=
    isSeparableExtension_residueField_of_isNode k X hX_dimension x hnode
  let algY : Algebra k (I.subscheme.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop ≫
      I.subscheme.Γevaluation y).hom.toAlgebra
  have hsepY : Algebra.IsSeparableExtension k (I.subscheme.residueField y) :=
    Algebra.IsSeparableExtension.of_algEquiv
      { __ := RingEquiv.ofBijective (I.subschemeι.residueFieldMap y).hom
          (bijective_residueFieldMap_of_isClosedImmersion I.subschemeι y)
        commutes' := fun r => by
          simp only [algX, algY, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
            RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop]
          exact Scheme.Γevaluation_naturality_apply I.subschemeι y _ }
  exact (smoothAt_iff_isRegularLocalRing_stalk (I.subschemeι ≫ (X ↘ Spec (.of k))) y
    hsepY).mpr (IsRegularLocalRing.of_ringEquiv e)

/-! ### Part (2)(a): the intersection is discrete -/

/-- **A quasi-sober space all of whose points are closed has topological Krull dimension at most
zero.** An irreducible closed subset has a generic point, and its closure is both that subset and
the single point, so every irreducible closed subset is a singleton and no two of them are nested
properly. -/
theorem topologicalKrullDim_le_zero_of_forall_isClosed_singleton
    {Y : Type u} [TopologicalSpace Y] [QuasiSober Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y)) : topologicalKrullDim Y ≤ 0 := by
  have key : ∀ S : IrreducibleCloseds Y, ∃ y : Y, (S : Set Y) = {y} := by
    intro S
    refine ⟨S.isIrreducible'.genericPoint, ?_⟩
    have hg := S.isIrreducible'.isGenericPoint_genericPoint S.isClosed'
    exact hg.symm.trans (h _).closure_eq
  rw [topologicalKrullDim]
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun S => ?_
  intro T hST
  obtain ⟨y, hy⟩ := key S
  obtain ⟨z, hz⟩ := key T
  have hyz : y = z := by
    have hsub : ({y} : Set Y) ⊆ ({z} : Set Y) := by
      rw [← hy, ← hz]
      exact hST
    simpa using hsub
  exact le_of_eq (IrreducibleCloseds.ext (by rw [hy, hz, hyz]) : S = T).symm

/-- **A locally Noetherian scheme all of whose points are closed has discrete underlying space.**
On an affine neighbourhood of a point the space is Noetherian, quasi-sober and of dimension at
most zero, hence discrete, so the point is open in that neighbourhood and therefore in the whole
scheme. -/
@[ega "I 6.2.2" "more general"]
theorem discreteTopology_of_forall_isClosed_singleton (W : Scheme.{u})
    [IsLocallyNoetherian W] (h : ∀ w : W, IsClosed ({w} : Set W)) :
    DiscreteTopology (W : Type u) := by
  have : T1Space (W : Type u) := ⟨h⟩
  refine discreteTopology_iff_isOpen_singleton.mpr fun w => ?_
  obtain ⟨U, hUaff, hwU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W) (x := w) (U := ⊤) (by trivial)
  have : IsNoetherianRing Γ(W, U) := IsLocallyNoetherian.component_noetherian ⟨U, hUaff⟩
  have : NoetherianSpace (U : Type u) := noetherianSpace_of_isAffineOpen U hUaff
  have : QuasiSober (U : Type u) := U.2.isOpenEmbedding_subtypeVal.quasiSober
  have : T1Space (U : Type u) := Subtype.t1Space
  have : DiscreteTopology (U : Type u) :=
    discrete_of_noetherian_topologicalKrullDim_le_zero
      (topologicalKrullDim_le_zero_of_forall_isClosed_singleton fun _ => isClosed_singleton)
  have hopen : IsOpen ({(⟨w, hwU⟩ : (U : Type u))} : Set (U : Type u)) := isOpen_discrete _
  have himg : IsOpen (Subtype.val '' ({(⟨w, hwU⟩ : (U : Type u))} : Set (U : Type u))) :=
    U.2.isOpenEmbedding_subtypeVal.isOpenMap _ hopen
  have hset : Subtype.val '' ({(⟨w, hwU⟩ : (U : Type u))} : Set (U : Type u)) =
      ({w} : Set (W : Type u)) := Set.image_singleton
  rwa [hset] at himg

/-- **Every point of the scheme-theoretic intersection of a reduced closed subcurve with the
closure of its complement is closed.** Its image in `X` is a node of `X`, hence a closed point,
and the intersection is a closed subscheme of `X`. -/
theorem isClosed_singleton_intersectionWithComplementaryCurve
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    (w : (intersectionWithComplementaryCurveIdeal I).subscheme) :
    IsClosed ({w} : Set (intersectionWithComplementaryCurveIdeal I).subscheme) := by
  have hxIJ := subschemeι_base_mem_supports_intersection I w
  obtain ⟨hnode, -⟩ := stalk_mem_minimalPrimes_and_sup_eq_maximalIdeal_of_mem_intersection
    hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension
    hxIJ.1 hxIJ.2
  have hinj : Function.Injective (intersectionWithComplementaryCurveIdeal I).subschemeι.base :=
    (intersectionWithComplementaryCurveIdeal I).subschemeι.isClosedEmbedding.injective
  have hpre : (intersectionWithComplementaryCurveIdeal I).subschemeι.base ⁻¹'
      {(intersectionWithComplementaryCurveIdeal I).subschemeι.base w} = {w} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hv => hinj hv, fun hv => by rw [hv]⟩
  rw [← hpre]
  exact hnode.1.preimage (intersectionWithComplementaryCurveIdeal I).subschemeι.continuous

/-- **Stacks 0E38, part (2)(a): the scheme-theoretic intersection of a reduced closed subcurve with
the closure of its complement is the disjoint union of the spectra of finite separable extensions
of the base field.** Its underlying space is discrete, so it is the disjoint union of its points;
at each point the stalk of the ideal sheaf cutting it out is the maximal ideal of the local ring of
`X`, so the local ring there is the residue field `κ(x)`; and that residue field is a finite
separable extension of `k`. -/
@[stacks 0E38 "part (2)(a)"]
theorem isDiscrete_and_residueField_intersectionWithComplementaryCurve
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) :
    DiscreteTopology ((intersectionWithComplementaryCurveIdeal I).subscheme : Type u) ∧
      ∀ w : (intersectionWithComplementaryCurveIdeal I).subscheme,
        let x := (intersectionWithComplementaryCurveIdeal I).subschemeι.base w
        let kToStalk : k →+* X.presheaf.stalk x :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
            X.presheaf.germ ⊤ x (by simp)).hom
        letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
        letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
        IdealSheafData.stalk (intersectionWithComplementaryCurveIdeal I) x =
            IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
          Module.Finite k (X.residueField x) ∧
            Algebra.IsSeparableExtension k (X.residueField x) := by
  have : IsLocallyNoetherian (intersectionWithComplementaryCurveIdeal I).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((intersectionWithComplementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k)))
  refine ⟨discreteTopology_of_forall_isClosed_singleton _ fun w =>
    isClosed_singleton_intersectionWithComplementaryCurve hX_equidimensional hX_dimension
      hX_nodal I hY_equidimensional hY_dimension w, fun w => ?_⟩
  intro x kToStalk
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  have hxIJ := subschemeι_base_mem_supports_intersection I w
  exact ⟨stalk_intersectionWithComplementaryCurveIdeal_eq_maximalIdeal hX_equidimensional
    hX_dimension hX_nodal I hY_equidimensional hY_dimension hxIJ.1 hxIJ.2,
    isFiniteSeparable_residueField_of_mem_intersection_complementaryCurve
      hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hxIJ.1 hxIJ.2⟩

/-! ### Part (1): the subcurve has at-worst-nodal singularities -/

/-- **Away from the closure of its complement, a reduced closed subcurve of a nodal curve is an
open subscheme of the ambient curve.** The open complement of that closure is contained in the
subcurve, the stalk of the ideal sheaf of the subcurve vanishes there, so the inclusion of the
preimage of that open into the ambient curve is an embedding with open range inducing
isomorphisms on stalks. -/
theorem isOpenImmersion_ι_preimage_compl_comp_subschemeι
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme] :
    IsOpenImmersion (Scheme.Opens.ι
      (I.subschemeι ⁻¹ᵁ ((complementaryCurveIdeal I).support.compl : X.Opens)) ≫
        I.subschemeι) := by
  classical
  have hsub := compl_support_complementaryCurveIdeal_subset_support hX_nodal I
  have hrange : Set.range (Scheme.Opens.ι
      (I.subschemeι ⁻¹ᵁ ((complementaryCurveIdeal I).support.compl : X.Opens)) ≫
        I.subschemeι).base =
      (((complementaryCurveIdeal I).support.compl : X.Opens) : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    have hpre : ((I.subschemeι ⁻¹ᵁ ((complementaryCurveIdeal I).support.compl : X.Opens)) :
        Set I.subscheme) =
        I.subschemeι.base ⁻¹' (((complementaryCurveIdeal I).support.compl : X.Opens) : Set X) :=
      rfl
    rw [hpre, Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι]
    exact Set.inter_eq_left.mpr hsub
  refine IsOpenImmersion.iff_isIso_stalkMap.mpr
    ⟨⟨(Scheme.Opens.ι (I.subschemeι ⁻¹ᵁ
      ((complementaryCurveIdeal I).support.compl : X.Opens)) ≫ I.subschemeι).isEmbedding, ?_⟩,
      fun z => ?_⟩
  · rw [hrange]
    exact ((complementaryCurveIdeal I).support.compl : X.Opens).2
  · rw [Scheme.Hom.stalkMap_comp]
    refine IsIso.comp_isIso' ?_ inferInstance
    have hzV : I.subschemeι.base ((Scheme.Opens.ι (I.subschemeι ⁻¹ᵁ
        ((complementaryCurveIdeal I).support.compl : X.Opens))).base z) ∉
        ((complementaryCurveIdeal I).support : Set X) := z.2
    have hker : RingHom.ker (I.subschemeι.stalkMap ((Scheme.Opens.ι (I.subschemeι ⁻¹ᵁ
        ((complementaryCurveIdeal I).support.compl : X.Opens))).base z)).hom = ⊥ := by
      rw [← IdealSheafData.stalk_ker_of_isClosedImmersion I.subschemeι _,
        Scheme.IdealSheafData.ker_subschemeι]
      exact stalk_eq_bot_of_notMem_support_complementaryCurveIdeal hX_nodal I hzV
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(RingHom.injective_iff_ker_eq_bot _).mpr hker, I.subschemeι.stalkMap_surjective _⟩

/-- **Stacks 0E38, part (1): a reduced closed subscheme, equidimensional of dimension one, of a
one-dimensional equidimensional locally algebraic curve with at-worst-nodal singularities again has
at-worst-nodal singularities.** At a point where the subcurve meets the closure of its complement
it is in fact smooth over the base field, by part (2)(c). At any other point the subcurve agrees
with the ambient curve on an open neighbourhood, and the dichotomy "smooth over `k` or a node"
transports along the two étale morphisms from that open subscheme. -/
@[stacks 0E38 "part (1)"]
theorem hasAtWorstNodalSingularities_subscheme
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) :
    letI : I.subscheme.Over (Spec (.of k)) := ⟨I.subschemeι ≫ (X ↘ Spec (.of k))⟩
    HasAtWorstNodalSingularities k I.subscheme := by
  intro y hyc
  by_cases hy : I.subschemeι.base y ∈ ((complementaryCurveIdeal I).support : Set X)
  · exact Or.inl (smoothAt_of_mem_support_complementaryCurveIdeal hX_equidimensional
      hX_dimension hX_nodal I hY_equidimensional hY_dimension y hy)
  · have hyW : y ∈ (I.subschemeι ⁻¹ᵁ
        ((complementaryCurveIdeal I).support.compl : X.Opens)) := hy
    have := isOpenImmersion_ι_preimage_compl_comp_subschemeι hX_nodal I
    have : Etale (Scheme.Opens.ι (I.subschemeι ⁻¹ᵁ
        ((complementaryCurveIdeal I).support.compl : X.Opens)) ≫ I.subschemeι) := inferInstance
    have hxclosed : IsClosed ({I.subschemeι.base y} : Set X) := by
      have h := I.subschemeι.isClosedEmbedding.isClosedMap _ hyc
      rwa [Set.image_singleton] at h
    have hab : (Scheme.Opens.ι (I.subschemeι ⁻¹ᵁ
        ((complementaryCurveIdeal I).support.compl : X.Opens)) ≫ I.subschemeι).base
          ⟨y, hyW⟩ = I.subschemeι.base y := rfl
    have hX := hX_nodal (I.subschemeι.base y) hxclosed
    rw [← hab] at hX
    exact smoothAt_or_isNode_of_etale_of_comm k (X ↘ Spec (.of k))
      (I.subschemeι ≫ (X ↘ Spec (.of k))) hX_dimension hY_dimension
      (Scheme.Opens.ι (I.subschemeι ⁻¹ᵁ
        ((complementaryCurveIdeal I).support.compl : X.Opens)) ≫ I.subschemeι)
      (Scheme.Opens.ι (I.subschemeι ⁻¹ᵁ
        ((complementaryCurveIdeal I).support.compl : X.Opens)))
      (Category.assoc _ _ _).symm ⟨y, hyW⟩ hX

end Stacks.Curves

end
