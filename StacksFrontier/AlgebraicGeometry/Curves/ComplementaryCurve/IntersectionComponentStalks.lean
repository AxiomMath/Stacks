module

public import Mathlib.AlgebraicGeometry.Artinian
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionLocalStructure
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDeltaBranchesDescent
public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothAtPoint
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchCount
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.MinimalPrimeTransversality
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing

/-!
# The two components through a point where a subcurve meets the closure of its complement

Let `X` be an equidimensional curve of dimension one, locally of finite type over a field `k` and
with at worst nodal singularities, let `Y ⊆ X` be a reduced equidimensional closed subscheme of
dimension one, and let `Z` be the scheme-theoretic closure of `X ∖ Y`. A point of `Y ∩ Z` lies on
an irreducible component of `X` contained in `Y` and on one not contained in `Y`; it is a node of
`X`, and the stalks of the ideal sheaves of `Y` and of `Z` there are the two minimal primes of the
local ring. Those two primes sum to the maximal ideal, the delta invariant being one, so every
local ring of `Y ∩ Z` is a field, which presents `Y ∩ Z` as a coproduct of spectra of finite
separable extensions of `k` ([Stacks, Tag 0E38] (2)(a)).

## Main results

* `Curves.exists_irreducibleComponents_of_mem_support_of_mem_support_complementaryCurveIdeal`:
  the two components through a point of `Y ∩ Z`.
* `Stacks.Curves.isNode_of_mem_support_of_mem_support_complementaryCurveIdeal`: such a point is a
  node of `X`.
* `Stacks.Curves.exists_stalk_eq_of_mem_support_of_mem_support_complementaryCurveIdeal`: at such
  a point the stalks of the ideal sheaves of `Y` and `Z` are the two minimal primes of the local
  ring.
* `Stacks.Curves.exists_iso_sigma_spec_intersectionWithComplementaryCurve`: `Y ∩ Z` is, over `k`,
  a coproduct of spectra of finite separable extensions of `k`.

## Implementation notes

Clause (2)(a) is stated as an isomorphism over `k` from a coproduct `∐ᵢ Spec Kᵢ` of finite
separable extensions onto `Y ∩ Z`, the index type being arbitrary: `X` is only locally of finite
type, so `Y ∩ Z` need not be finite. The extensions are the residue fields of `Y ∩ Z`.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-! ### The components of the two complementary curves through a point -/

/-- **A point where a reduced equidimensional subcurve meets the closure of its complement lies
on an ambient irreducible component inside the subcurve and on one not inside it.** The first is
`AlgebraicGeometry.exists_component_subset_support_of_mem`, the second
`Stacks.Curves.exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal`. -/
theorem exists_irreducibleComponents_of_mem_support_of_mem_support_complementaryCurveIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData)
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) {x : X}
    (hxI : x ∈ (I.support : Set X)) (hxZ : x ∈ ((complementaryCurveIdeal I).support : Set X)) :
    ∃ C ∈ irreducibleComponents X, ∃ D : Closeds X, C ⊆ (I.support : Set X) ∧ x ∈ C ∧
      (D : Set X) ∈ irreducibleComponents X ∧ ¬ (D : Set X) ⊆ (I.support : Set X) ∧
        x ∈ (D : Set X) ∧ complementaryCurveIdeal I ≤ Scheme.IdealSheafData.vanishingIdeal D := by
  obtain ⟨C, hC, hxC, hCI⟩ := exists_component_subset_support_of_mem (k := k)
    hX_equidimensional hX_dimension I hY_equidimensional hY_dimension hxI
  obtain ⟨D, hD, hDI, hxD, hle⟩ :=
    exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal hX_nodal I hxZ
  exact ⟨C, hC, D, hCI, hxC, hD, hDI, hxD, hle⟩

/-- **A point where a reduced equidimensional subcurve meets the closure of its complement is a
node of the ambient curve.** It lies on two distinct irreducible components, so it is a closed
point (`Stacks.Curves.closed_of_mem_distinct_irreducibleComponents`), and the local ring there
is not a domain, so the point is not a smooth point. -/
theorem isNode_of_mem_support_of_mem_support_complementaryCurveIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData)
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) {x : X}
    (hxI : x ∈ (I.support : Set X)) (hxZ : x ∈ ((complementaryCurveIdeal I).support : Set X)) :
    IsNode k X x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  obtain ⟨C, hC, D, hCI, hxC, hD, hDI, hxD, -⟩ :=
    exists_irreducibleComponents_of_mem_support_of_mem_support_complementaryCurveIdeal
      hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hxI hxZ
  have hCD : C ≠ (D : Set X) := fun h => hDI (h ▸ hCI)
  exact (hX_nodal x (closed_of_mem_distinct_irreducibleComponents (k := k) hX_dimension
    hC hD hCD hxC hxD)).resolve_left fun hxsmooth => hCD (irreducibleComponents_eq_of_stalkDomain
      (stalk_isDomain_of_smoothAt k X x hxsmooth) hC hD hxC hxD)

/-- **At a node lying on two distinct irreducible components, every irreducible component
through the point is one of the two.** The components through a point are at most as many as the
geometric branches there, and a node has two. -/
theorem eq_or_eq_of_mem_irreducibleComponents_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1) {x : X} (hnode : IsNode k X x)
    {C D E : Set X} (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    (hCD : C ≠ D) (hxC : x ∈ C) (hxD : x ∈ D)
    (hE : E ∈ irreducibleComponents X) (hxE : x ∈ E) : E = C ∨ E = D := by
  obtain ⟨-, -, hbr⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
      k X hdim x hnode
  by_contra hcon
  push Not at hcon
  have hle : Set.encard {Z ∈ irreducibleComponents X | x ∈ Z} ≤ 2 :=
    (encard_irreducibleComponentsThrough_le_numberOfBranches X x).trans
      ((numberOfBranches_le_numberOfGeometricBranches X x).trans hbr.le)
  have hsub : ({E, C, D} : Set (Set X)) ⊆ {Z ∈ irreducibleComponents X | x ∈ Z} := by
    rintro Z (rfl | rfl | rfl)
    · exact ⟨hE, hxE⟩
    · exact ⟨hC, hxC⟩
    · exact ⟨hD, hxD⟩
  have hthree : ({E, C, D} : Set (Set X)).encard = 3 := by
    rw [Set.encard_insert_of_notMem (by simpa using hcon), Set.encard_pair hCD]
    rfl
  have := (Set.encard_le_encard hsub).trans hle
  rw [hthree] at this
  exact absurd this (by decide)

/-- **Distinct irreducible components through a point have distinct stalks of vanishing ideals
there.** The stalk of the vanishing ideal of a component through `x` is the minimal prime of
`𝒪_{X, x}` which `AlgebraicGeometry.irreducibleComponentsEquivMinimalPrimes` attaches to it. -/
theorem stalk_vanishingIdeal_injective {X : Scheme.{u}} (x : X)
    {C D : Set X} (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    (hxC : x ∈ C) (hxD : x ∈ D)
    (h : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩) x =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨D, isClosed_of_mem_irreducibleComponents D hD⟩) x) : C = D := by
  let e := irreducibleComponentsEquivMinimalPrimes x
  have hval : ∀ (W : irreducibleComponents X) (hxW : x ∈ (W : Set X)),
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩) x = (e ⟨W, hxW⟩).1.asIdeal :=
    fun W hxW => stalk_vanishingIdeal_eq_of_mem_minimalPrimes x W hxW _ (e ⟨W, hxW⟩).2
      (by
        rw [fromSpecStalk_irreducibleComponentsEquivMinimalPrimes x ⟨W, hxW⟩]
        exact (genericPoints.isGenericPoint_ofComponent W).mem)
  have heq : e ⟨⟨C, hC⟩, hxC⟩ = e ⟨⟨D, hD⟩, hxD⟩ := Subtype.ext
    (PrimeSpectrum.ext ((hval ⟨C, hC⟩ hxC).symm.trans (h.trans (hval ⟨D, hD⟩ hxD))))
  exact congrArg (fun W : {W : irreducibleComponents X // x ∈ (W : Set X)} => (W.1 : Set X))
    (e.injective heq)

/-! ### The local ring of a reduced closed subscheme along a single component -/

/-- **A reduced ring with a single minimal prime is a domain.** The minimal prime is the
nilradical, which is `⊥`. -/
private theorem isDomain_of_encard_minimalPrimes_eq_one {R : Type*} [CommRing R]
    [_root_.IsReduced R] (h : (minimalPrimes R).encard = 1) : IsDomain R := by
  obtain ⟨P, hP⟩ := Set.encard_eq_one.mp h
  have hPmem : P ∈ minimalPrimes R := by simp [hP]
  have hPbot : P = ⊥ := by
    have h1 : sInf (minimalPrimes R) = (⊥ : Ideal R).radical := Ideal.sInf_minimalPrimes
    rw [hP, sInf_singleton] at h1
    rw [h1]
    exact nilradical_eq_zero _
  have : (⊥ : Ideal R).IsPrime := hPbot ▸ hPmem.1.1
  exact IsDomain.of_bot_isPrime _

/-- **The stalk of a reduced closed subscheme at a point all of whose generalizations in it lie
on one irreducible component is the minimal prime of that component.** Let `K` cut out a reduced
closed subscheme containing an irreducible component `C₀` through `x`, and suppose every point of
`K` specializing to `x` lies on `C₀`. Every irreducible component of the subscheme through the
point `y` over `x` then lies in the preimage of `C₀`, which is the closure of a point and so
irreducible: the subscheme has a single irreducible component through `y`. Its local ring there
is reduced with a single minimal prime, hence a domain, so the stalk of `K` — the kernel of the
surjection onto that local ring — is prime. It lies below the stalk of the vanishing ideal of
`C₀`, a minimal prime, and so equals it. -/
theorem stalk_eq_stalk_vanishingIdeal_of_forall_mem_closure {X : Scheme.{u}}
    (K : X.IdealSheafData) [IsReduced K.subscheme] {C₀ : Set X}
    (hC₀ : C₀ ∈ irreducibleComponents X) (hC₀K : C₀ ⊆ (K.support : Set X)) {x : X}
    (hx : x ∈ C₀)
    (h : ∀ z ∈ (K.support : Set X), x ∈ closure ({z} : Set X) → z ∈ C₀) :
    IdealSheafData.stalk K x = IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
      ⟨C₀, isClosed_of_mem_irreducibleComponents C₀ hC₀⟩) x := by
  classical
  have hC₀cl : IsClosed C₀ := isClosed_of_mem_irreducibleComponents C₀ hC₀
  have hle : K ≤ Scheme.IdealSheafData.vanishingIdeal ⟨C₀, hC₀cl⟩ := by
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme K K.support rfl]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono hC₀K
  have hmin := stalk_vanishingIdeal_mem_minimalPrimes x ⟨C₀, hC₀⟩ hx
  have hstalk_le := IdealSheafData.stalk_mono hle x
  obtain ⟨y, rfl⟩ : x ∈ Set.range K.subschemeι.base := K.range_subschemeι ▸ hC₀K hx
  obtain ⟨η, hη⟩ := QuasiSober.sober hC₀.1 hC₀cl
  obtain ⟨w₀, hw₀⟩ : η ∈ Set.range K.subschemeι.base := K.range_subschemeι ▸ hC₀K hη.mem
  let T : Set K.subscheme := closure {w₀}
  have hTirr : IsIrreducible T := isIrreducible_singleton.closure
  have hT : ∀ W ∈ irreducibleComponents K.subscheme, y ∈ W → W = T := by
    intro W hW hyW
    obtain ⟨w, hw⟩ := QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)
    have hxw : K.subschemeι.base y ∈ closure ({K.subschemeι.base w} : Set X) := by
      simpa only [Set.image_singleton] using image_closure_subset_closure_image
        (s := ({w} : Set K.subscheme)) K.subschemeι.continuous ⟨y, hw.def ▸ hyW, rfl⟩
    have hwC₀ : K.subschemeι.base w ∈ C₀ :=
      h _ (by rw [← K.range_subschemeι]; exact ⟨w, rfl⟩) hxw
    have hwT : w ∈ T := by
      change w ∈ closure ({w₀} : Set K.subscheme)
      rw [K.subschemeι.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image,
        Set.image_singleton, Set.mem_preimage, hw₀, hη.def]
      exact hwC₀
    have hWT : W ⊆ T := by
      rw [← hw.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hwT) isClosed_closure
    exact Set.Subset.antisymm hWT (hW.2 hTirr hWT)
  have hset : {Z ∈ irreducibleComponents K.subscheme | y ∈ Z} = {T} := by
    ext Z
    refine ⟨fun ⟨hZ, hyZ⟩ => hT Z hZ hyZ, ?_⟩
    rintro rfl
    rw [← hT _ (irreducibleComponent_mem_irreducibleComponents y) mem_irreducibleComponent]
    exact ⟨irreducibleComponent_mem_irreducibleComponents y, mem_irreducibleComponent⟩
  have hone : Set.encard (minimalPrimes (K.subscheme.presheaf.stalk y)) = 1 := by
    rw [← encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk, hset, Set.encard_singleton]
  have := isDomain_of_encard_minimalPrimes_eq_one hone
  have hprime : (IdealSheafData.stalk K (K.subschemeι.base y)).IsPrime := by
    rw [← AlgebraicGeometry.IdealSheafData.ker_stalkMap_subschemeι_eq_stalk K y]
    exact RingHom.ker_isPrime _
  exact le_antisymm hstalk_le (hmin.2 ⟨hprime, bot_le⟩ hstalk_le)

/-- **At a point where a reduced equidimensional subcurve `Y` meets the closure `Z` of its
complement, the stalks of the two ideal sheaves are two distinct minimal primes of the local
ring.** The point is a node lying on a component `C ⊆ Y` and a component `D ⊄ Y`, and on no
other (`Stacks.Curves.eq_or_eq_of_mem_irreducibleComponents_of_isNode`). Every point of `Y`
specializing to the node lies on a component inside `Y` through it, hence on `C`; every point of
`Z` specializing to it lies on a component outside `Y` through it, hence on `D`. So
`Stacks.Curves.stalk_eq_stalk_vanishingIdeal_of_forall_mem_closure` identifies the stalks of `Y`
and `Z` with the minimal primes of `C` and of `D`, which differ because `C ≠ D`. -/
theorem exists_stalk_eq_of_mem_support_of_mem_support_complementaryCurveIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) {x : X}
    (hxI : x ∈ (I.support : Set X)) (hxZ : x ∈ ((complementaryCurveIdeal I).support : Set X)) :
    IsNode k X x ∧ ∃ p q : minimalPrimes (X.presheaf.stalk x), p ≠ q ∧
      IdealSheafData.stalk I x = p ∧ IdealSheafData.stalk (complementaryCurveIdeal I) x = q := by
  have hnode := isNode_of_mem_support_of_mem_support_complementaryCurveIdeal
    hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hxI hxZ
  obtain ⟨C, hC, D, hCI, hxC, hD, hDI, hxD, hle⟩ :=
    exists_irreducibleComponents_of_mem_support_of_mem_support_complementaryCurveIdeal
      hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hxI hxZ
  have hCD : C ≠ (D : Set X) := fun h => hDI (h ▸ hCI)
  have htwo : ∀ {E : Set X}, E ∈ irreducibleComponents X → ∀ {z}, z ∈ E →
      x ∈ closure ({z} : Set X) → E = C ∨ E = (D : Set X) :=
    fun hE _ hz hxz => eq_or_eq_of_mem_irreducibleComponents_of_isNode k X hX_dimension hnode
      hC hD hCD hxC hxD hE (closure_minimal (Set.singleton_subset_iff.mpr hz)
        (isClosed_of_mem_irreducibleComponents _ hE) hxz)
  have hYstalk := stalk_eq_stalk_vanishingIdeal_of_forall_mem_closure I hC hCI hxC
    (fun z hz hxz => by
      obtain ⟨C', hC', hzC', hC'I⟩ := exists_component_subset_support_of_mem (k := k)
        hX_equidimensional hX_dimension I hY_equidimensional hY_dimension hz
      rcases htwo hC' hzC' hxz with rfl | rfl
      · exact hzC'
      · exact absurd hC'I hDI)
  have : IsReduced (complementaryCurveIdeal I).subscheme := by
    rw [show complementaryCurveIdeal I = _ from
      complementaryCurveIdeal_eq_union_irreducibleComponents hX_nodal I]
    infer_instance
  have hDZ : (D : Set X) ⊆ ((complementaryCurveIdeal I).support : Set X) := by
    rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal D]
    exact Scheme.IdealSheafData.support_antitone hle
  have hZstalk := stalk_eq_stalk_vanishingIdeal_of_forall_mem_closure
    (complementaryCurveIdeal I) hD hDZ hxD
    (fun z hz hxz => by
      obtain ⟨D', hD', hD'I, hzD', -⟩ :=
        exists_irreducibleComponent_complementaryCurveIdeal_le_vanishingIdeal hX_nodal I hz
      rcases htwo hD' hzD' hxz with h | h
      · exact absurd (h ▸ hCI) hD'I
      · exact h ▸ hzD')
  exact ⟨hnode, ⟨_, stalk_vanishingIdeal_mem_minimalPrimes x ⟨C, hC⟩ hxC⟩,
    ⟨_, stalk_vanishingIdeal_mem_minimalPrimes x ⟨D, hD⟩ hxD⟩,
    fun hpq => hCD (stalk_vanishingIdeal_injective x hC hD hxC hxD (congrArg Subtype.val hpq)),
    hYstalk, hZstalk⟩

/-! ### Residue fields at a node -/

/-- **The residue field at a closed point of a scheme locally of finite type over a field is a
finite extension of the field.** The composite `Spec κ(y) ⟶ Spec k` is locally of finite type
between spectra of fields, hence finite, `Spec k` being Jacobson; and it is the spectrum of the
evaluation map `k ⟶ κ(y)` (`AlgebraicGeometry.fromSpecResidueField_comp`). -/
theorem module_finite_residueField_of_isClosed {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : Y) (hy : IsClosed ({y} : Set Y)) :
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y).hom.toAlgebra
    Module.Finite k (Y.residueField y) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hy
  have hfin : IsFinite (Y.fromSpecResidueField y ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rwa [fromSpecResidueField_comp, IsFinite.SpecMap_iff] at hfin

/-- **A closed subscheme has separable residue field over `k` at a point lying over a node.**
The residue field of the ambient curve at a node is separable over `k`
(`Stacks.Curves.isSeparableExtension_residueField_of_isNode`), and a closed immersion identifies
the two residue fields as extensions of `k`. -/
theorem isSeparableExtension_residueField_of_isClosedImmersion_of_isNode
    (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (hX : topologicalKrullDim X = 1)
    (π : Y ⟶ X) [IsClosedImmersion π] (y : Y) (hnode : IsNode k X (π.base y)) :
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ (X ↘ Spec (.of k))).appTop ≫
        Y.Γevaluation y).hom.toAlgebra
    Algebra.IsSeparableExtension k (Y.residueField y) := by
  let algX : Algebra k (X.residueField (π.base y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.Γevaluation (π.base y)).hom.toAlgebra
  have hsepX : Algebra.IsSeparableExtension k (X.residueField (π.base y)) :=
    isSeparableExtension_residueField_of_isNode k X hX (π.base y) hnode
  let algY : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ (X ↘ Spec (.of k))).appTop ≫
      Y.Γevaluation y).hom.toAlgebra
  exact Algebra.IsSeparableExtension.of_algEquiv
    { __ := RingEquiv.ofBijective (π.residueFieldMap y).hom
        (bijective_residueFieldMap_of_isClosedImmersion π y)
      commutes' := fun r => by
        simp only [algX, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.coe_comp,
          Function.comp_apply, Scheme.Hom.comp_appTop]
        exact Scheme.Γevaluation_naturality_apply π y _ }

/-! ### The intersection as a coproduct of spectra -/

/-- **A point of `Y ∩ Z` lies on both `Y` and `Z`.** -/
private theorem mem_support_of_intersectionWithComplementaryCurve {X : Scheme.{u}}
    (I : X.IdealSheafData) (w : intersectionWithComplementaryCurve I) :
    (intersectionWithComplementaryCurveIdeal I).subschemeι.base w ∈ (I.support : Set X) ∧
      (intersectionWithComplementaryCurveIdeal I).subschemeι.base w ∈
        ((complementaryCurveIdeal I).support : Set X) := by
  have hw : (intersectionWithComplementaryCurveIdeal I).subschemeι.base w ∈
      ((intersectionWithComplementaryCurveIdeal I).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [Scheme.IdealSheafData.support_sup] at hw
  exact ⟨hw.1, hw.2⟩

/-- **The local rings of `Y ∩ Z` are fields.** The stalk of the ideal sheaf of `Y ∩ Z` is the
maximal ideal of the local ring of `X`. -/
private theorem isField_stalk_intersectionWithComplementaryCurve
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    (w : intersectionWithComplementaryCurve I) :
    IsField ((intersectionWithComplementaryCurve I).presheaf.stalk w) := by
  have hmem := mem_support_of_intersectionWithComplementaryCurve I w
  let e := (Ideal.quotEquivOfEq
      ((AlgebraicGeometry.IdealSheafData.ker_stalkMap_subschemeι_eq_stalk _ w).trans
        (stalk_intersectionWithComplementaryCurveIdeal_eq_maximalIdeal hX_equidimensional
          hX_dimension hX_nodal I hY_equidimensional hY_dimension hmem.1 hmem.2)).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      ((intersectionWithComplementaryCurveIdeal I).subschemeι.stalkMap_surjective w))
  exact MulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance) e.symm.toMulEquiv

/-- **Stacks Project, Tag 0E38, clause (2)(a).** Let `X` be a one-dimensional equidimensional
curve locally of finite type over a field `k` with at worst nodal singularities, let `Y ⊆ X` be a
reduced equidimensional closed subscheme of dimension one, and let `Z` be the scheme-theoretic
closure of `X ∖ Y`. Then the scheme-theoretic intersection `Y ∩ Z` is, over `k`, a disjoint union
of spectra of finite separable extensions of `k`.

At each point of `Y ∩ Z` the stalks of the ideal sheaves of `Y` and `Z` are the two minimal primes
of the local ring of the node there
(`Stacks.Curves.exists_stalk_eq_of_mem_support_of_mem_support_complementaryCurveIdeal`), and these
sum to the maximal ideal, the delta invariant being one
(`Ring.sup_eq_maximalIdeal_of_deltaInvariant_eq_one`). So every local ring of `Y ∩ Z` is a field:
`Y ∩ Z` is reduced, and its points are closed, so it is discrete. Each `Spec κ(w) ⟶ Y ∩ Z` is then
an open and closed immersion, and together they present `Y ∩ Z` as the coproduct of the spectra
of its residue fields, which are finite (closed points) and separable (nodes) over `k`. -/
@[stacks 0E38 "intersection_is_disjoint_union_of_spectra_of_finite_separable_extensions"]
theorem exists_iso_sigma_spec_intersectionWithComplementaryCurve
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) :
    ∃ (ι : Type u) (K : ι → Type u) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra k (K i)),
      (∀ i, Module.Finite k (K i) ∧ Algebra.IsSeparable k (K i)) ∧
      ∃ e : (∐ fun i => Spec (.of (K i))) ≅ intersectionWithComplementaryCurve I,
        ∀ i, Limits.Sigma.ι (fun i => Spec (.of (K i))) i ≫ e.hom ≫
            (intersectionWithComplementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k)) =
          Spec.map (CommRingCat.ofHom (algebraMap k (K i))) := by
  classical
  let J := intersectionWithComplementaryCurveIdeal I
  let W := intersectionWithComplementaryCurve I
  let g : W ⟶ Spec (.of k) := J.subschemeι ≫ (X ↘ Spec (.of k))
  have hfield := isField_stalk_intersectionWithComplementaryCurve hX_equidimensional
    hX_dimension hX_nodal I hY_equidimensional hY_dimension
  have hclosed := isClosed_singleton_intersectionWithComplementaryCurve hX_equidimensional
    hX_dimension hX_nodal I hY_equidimensional hY_dimension
  have : ∀ w : W, _root_.IsReduced (W.presheaf.stalk w) := fun w => by
    let := (hfield w).toField
    infer_instance
  have : IsReduced W := isReduced_of_isReduced_stalk W
  have : T1Space W := ⟨hclosed⟩
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsLocallyArtinian W := .of_topologicalKrullDim_le_zero
    Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space
  have : DiscreteTopology W := inferInstance
  have hopen : ∀ w : W, IsOpenImmersion (W.fromSpecResidueField w) := fun w => by
    have := isClosed_singleton_iff_isClosedImmersion.mp (hclosed w)
    exact StacksTag09NE.isOpenImmersion_of_closedImmersion_of_open_range _
      (by rw [Scheme.range_fromSpecResidueField]; exact isOpen_discrete _)
  let K : W → Type u := fun w => W.residueField w
  let alg : ∀ w, Algebra k (K w) := fun w =>
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ W.Γevaluation w).hom.toAlgebra
  let f : ∀ w : W, Spec (.of (K w)) ⟶ W := fun w => W.fromSpecResidueField w
  have : IsIso (Limits.Sigma.desc f) := by
    refine StacksTag09NE.isIso_sigmaDesc_of_disjointOpenCover _ f ?_ ?_
    · intro a b hab
      change Disjoint (Set.range (W.fromSpecResidueField a)) (Set.range (W.fromSpecResidueField b))
      rw [Scheme.range_fromSpecResidueField, Scheme.range_fromSpecResidueField]
      exact Set.disjoint_singleton.mpr hab
    · intro w
      exact ⟨w, IsLocalRing.closedPoint (W.residueField w), Scheme.fromSpecResidueField_apply w _⟩
  refine ⟨W, K, fun w => inferInstance, alg, fun w => ?_, asIso (Limits.Sigma.desc f), fun w => ?_⟩
  · have hfin : Module.Finite k (K w) := module_finite_residueField_of_isClosed g w (hclosed w)
    have hmem := mem_support_of_intersectionWithComplementaryCurve I w
    have hsep : Algebra.IsSeparableExtension k (K w) :=
      isSeparableExtension_residueField_of_isClosedImmersion_of_isNode k hX_dimension
        J.subschemeι w (isNode_of_mem_support_of_mem_support_complementaryCurveIdeal
          hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension hmem.1 hmem.2)
    have : Algebra.IsAlgebraic k (K w) := Algebra.IsAlgebraic.of_finite k (K w)
    exact ⟨hfin,
      Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension_of_isAlgebraic
        k (K w)⟩
  · rw [asIso_hom, Limits.Sigma.ι_comp_desc_assoc]
    exact fromSpecResidueField_comp w g

end Stacks.Curves

end
