module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing

/-!
# Intersection points of complementary curves are nodes

Let `X` be an equidimensional curve of dimension one, locally of finite type over a field and
with at worst nodal singularities, and let `Y ⊆ X` be a reduced equidimensional closed subscheme
of dimension one. Then every point where `Y` meets the scheme-theoretic closure of its
complement is a node of `X`.

Such a point lies on an irreducible component contained in `Y` and on one not contained in `Y`,
hence on two distinct components. Two distinct components of a one-dimensional curve meet only
in closed points, so nodality applies at the point; and the local ring there is not a domain,
since two minimal primes pass through it, so the point is not a smooth point.

## Main results

* `Stacks.Curves.isNode_of_mem_intersection_complementaryCurve`: every intersection point of the
  two complementary closed curves is a node of the ambient curve.

## Implementation notes

A closed subscheme is given by its ideal sheaf `I`; the scheme-theoretic closure of the open
complement is cut out by `Stacks.Curves.complementaryCurveIdeal I`, so the scheme-theoretic
intersection of the two is cut out by the supremum of the two ideal sheaves, and its canonical
closed immersion into `X` sends an intersection point to the ambient point at which nodality is
asserted.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-- **A point lying on two distinct irreducible components of a one-dimensional curve over a
field is closed.** Were it not, its closure, a non-closed point below it and an ambient component
above it would form a chain of three irreducible closed subsets. -/
theorem closed_of_mem_distinct_irreducibleComponents
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hXdim : topologicalKrullDim X = 1) {x : X} {C D : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    (hCD : C ≠ D) (hxC : x ∈ C) (hxD : x ∈ D) : IsClosed ({x} : Set X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  by_contra hxClosed
  have hcl {E : Set X} (hE : E ∈ irreducibleComponents X) (hxE : x ∈ E) :
      closure ({x} : Set X) ⊆ E :=
    closure_minimal (Set.singleton_subset_iff.mpr hxE) (isClosed_of_mem_irreducibleComponents E hE)
  have hclC := hcl hC hxC
  have hproper : closure ({x} : Set X) ≠ C := by
    intro heq
    have hCD' : C ⊆ D := by simpa [heq] using hcl hD hxD
    exact hCD (hCD'.antisymm fun z hz => hC.2 hD.1 hCD' hz)
  obtain ⟨z, hz⟩ : ((closure ({x} : Set X)) ∩ closedPoints X).Nonempty :=
    closure_nonempty_iff.mp ⟨x, by
      rw [JacobsonSpace.closure_inter_closedPoints
        (isClosed_closure : IsClosed (closure ({x} : Set X)))]
      exact subset_closure (Set.mem_singleton x)⟩
  have hz' : IsClosed ({z} : Set X) := by simpa [closedPoints] using hz.2
  have hzx : z ≠ x := fun h => hxClosed (h ▸ hz')
  let S₀ : IrreducibleCloseds X := ⟨{z}, isIrreducible_singleton, hz'⟩
  let S₁ : IrreducibleCloseds X := ⟨closure ({x} : Set X),
    isIrreducible_singleton.closure, isClosed_closure⟩
  let S₂ : IrreducibleCloseds X := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have h01 : S₀ < S₁ := by
    refine ⟨Set.singleton_subset_iff.mpr hz.1, fun h => ?_⟩
    exact hzx (Set.mem_singleton_iff.mp (h (subset_closure (Set.mem_singleton x)))).symm
  have h12 : S₁ < S₂ := ⟨hclC, fun h =>
    hproper (congrArg (fun A : IrreducibleCloseds X => (A : Set X)) (le_antisymm hclC h))⟩
  let p : LTSeries (IrreducibleCloseds X) :=
    RelSeries.fromListIsChain [S₀, S₁, S₂] (by simp)
      (List.IsChain.cons_cons h01 (List.isChain_pair.mpr h12))
  have hdim' : Order.krullDim (IrreducibleCloseds X) = 1 := by
    simpa [topologicalKrullDim] using hXdim
  have hdimlt : Order.krullDim (IrreducibleCloseds X) < 2 := by
    rw [hdim']
    decide
  have hp : p.length < 2 :=
    (Order.krullDim_lt_coe_iff (α := IrreducibleCloseds X) (n := 2)).mp hdimlt p
  have hplen : p.length = 2 := by simp [p]
  omega

/-- **The local ring at a smooth point of a scheme over a field is a domain.** Smoothness at the
point makes the local ring a regular local ring. -/
theorem stalk_isDomain_of_smoothAt (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X)
    (hsm : InfinitesimalLifting.SmoothAt (X ↘ Spec (.of k)) x) :
    IsDomain (X.presheaf.stalk x) := by
  let f := X ↘ Spec (.of k)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : (Spec (.of k)).Opens := ⊤
  have hV : IsAffineOpen V := isAffineOpen_top _
  have hVU : U ≤ f ⁻¹ᵁ V := by simp [V]
  let A := Γ(Spec (.of k), V)
  let B := Γ(X, U)
  let _ : Field A :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.isField (Field.toIsField k)).toField
  let _ : Algebra A B := (f.appLE V U hVU).hom.toAlgebra
  have : Algebra.FiniteType A B := f.finiteType_appLE hV hU hVU
  let q := hU.primeIdealOf ⟨x, hxU⟩
  let _ : Algebra B (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hform : Algebra.IsSmoothAt A q.asIdeal :=
    (AlgebraicGeometry.formallySmooth_stalkMap_iff V hV U hU hVU hxU).symm.mpr
      (hsm.formallySmooth_stalkMap f x)
  exact ((Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing q
      (X.presheaf.stalk x)).2 hform).isDomain _

/-- An irreducible set meeting an open set lies in any closed set containing that intersection. -/
private theorem subset_of_isPreirreducible_of_inter_subset {X : Type*} [TopologicalSpace X]
    {Z W O : Set X} (hZ : IsPreirreducible Z) (hW : IsClosed W) (hO : IsOpen O)
    (hZO : (Z ∩ O).Nonempty) (h : Z ∩ O ⊆ W) : Z ⊆ W :=
  (subset_closure_inter_of_isPreirreducible_of_isOpen hZ hO hZO).trans (closure_minimal h hW)

/-- Two irreducible components that agree on an open set meeting one of them coincide. -/
private theorem eq_of_inter_eq_of_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    {Z W O : Set X} (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (hO : IsOpen O) (hZO : (Z ∩ O).Nonempty) (h : Z ∩ O = W ∩ O) : Z = W :=
  (subset_of_isPreirreducible_of_inter_subset hZ.1.2
    (isClosed_of_mem_irreducibleComponents W hW) hO hZO (h.le.trans Set.inter_subset_left)).antisymm
    (subset_of_isPreirreducible_of_inter_subset hW.1.2
      (isClosed_of_mem_irreducibleComponents Z hZ) hO (h ▸ hZO) (h.ge.trans Set.inter_subset_left))

/-- The vanishing ideal of an irreducible component of a prime spectrum is a minimal prime. -/
private theorem vanishingIdeal_mem_minimalPrimes_of_mem_irreducibleComponents {R : Type*}
    [CommRing R] {Z : Set (PrimeSpectrum R)} (hZ : Z ∈ irreducibleComponents (PrimeSpectrum R)) :
    PrimeSpectrum.vanishingIdeal Z ∈ minimalPrimes R := by
  apply PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr
  simpa [PrimeSpectrum.vanishingIdeal_closure,
    (isClosed_of_mem_irreducibleComponents Z hZ).closure_eq] using hZ

/-- Two minimal primes contained in a prime `q` coincide when the localization at `q` is a
domain. -/
private theorem eq_of_mem_minimalPrimes_of_isDomain_localization {R : Type*} [CommRing R]
    (q : Ideal R) [q.IsPrime] (L : Type*) [CommRing L] [Algebra R L]
    [IsLocalization.AtPrime L q] [IsDomain L] {p r : Ideal R}
    (hp : p ∈ minimalPrimes R) (hr : r ∈ minimalPrimes R) (hpq : p ≤ q) (hrq : r ≤ q) :
    p = r := by
  have hdisj {s : Ideal R} (hsq : s ≤ q) : Disjoint (q.primeCompl : Set R) (s : Set R) :=
    Set.disjoint_left.mpr fun _ ha hs => ha (hsq hs)
  have hbot {s : Ideal R} (hs : s ∈ minimalPrimes R) (hsq : s ≤ q) :
      Ideal.map (algebraMap R L) s = ⊥ := by
    have hunder : Ideal.under R (Ideal.map (algebraMap R L) s) = s :=
      IsLocalization.under_map_of_isPrime_disjoint q.primeCompl L hs.isPrime (hdisj hsq)
    have hmem : Ideal.under R (Ideal.map (algebraMap R L) s) ∈
        (⊥ : Ideal R).minimalPrimes := by simpa [hunder] using hs
    have hmap : Ideal.map (algebraMap R L) s ∈
        ((⊥ : Ideal R).map (algebraMap R L)).minimalPrimes := by
      rwa [IsLocalization.minimalPrimes_map q.primeCompl L (⊥ : Ideal R)]
    simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hmap
  have hm := congrArg (Ideal.under R) ((hbot hp hpq).trans (hbot hr hrq).symm)
  rwa [IsLocalization.under_map_of_isPrime_disjoint q.primeCompl L hp.isPrime (hdisj hpq),
    IsLocalization.under_map_of_isPrime_disjoint q.primeCompl L hr.isPrime (hdisj hrq)] at hm

/-- **Two irreducible components through a point whose local ring is a domain coincide.** The
minimal primes of the local ring correspond to the components through the point, and a domain
has only one. -/
theorem irreducibleComponents_eq_of_stalkDomain {X : Scheme.{u}} [IsLocallyNoetherian X]
    {x : X} (hD : IsDomain (X.presheaf.stalk x)) {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let f := hU.fromSpec
  have : IsOpenImmersion f := IsAffineOpen.isOpenImmersion_fromSpec hU
  let q := hU.primeIdealOf ⟨x, hxU⟩
  have hq : f q = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have key {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hxZ : x ∈ Z) :
      f.base ⁻¹' Z ∈ irreducibleComponents (PrimeSpectrum Γ(X, U)) ∧
      PrimeSpectrum.vanishingIdeal (f.base ⁻¹' Z) ∈ minimalPrimes Γ(X, U) ∧
      PrimeSpectrum.vanishingIdeal (f.base ⁻¹' Z) ≤ q.asIdeal := by
    have h := preimage_mem_irreducibleComponents hZ f.isOpenEmbedding ⟨x, hxZ, ⟨q, hq⟩⟩
    exact ⟨h, vanishingIdeal_mem_minimalPrimes_of_mem_irreducibleComponents h, fun _ ha =>
      (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha q (by change f q ∈ Z; rwa [hq])⟩
  obtain ⟨hZ', hp, hpq⟩ := key hZ hxZ
  obtain ⟨hW', hr, hrq⟩ := key hW hxW
  let _ : Algebra (Γ(X, U)) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  have hpr := eq_of_mem_minimalPrimes_of_isDomain_localization q.asIdeal (X.presheaf.stalk x)
    hp hr hpq hrq
  have hzero {A : Set (PrimeSpectrum Γ(X, U))} (hA : A ∈ irreducibleComponents _) :
      PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal A : Set Γ(X, U)) = A := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      (isClosed_of_mem_irreducibleComponents A hA).closure_eq]
  have hZW' : f.base ⁻¹' Z = f.base ⁻¹' W := by
    have hz := congrArg
      (fun I : Ideal (Γ(X, U)) => PrimeSpectrum.zeroLocus (I : Set (Γ(X, U)))) hpr
    exact (hzero hZ').symm.trans (hz.trans (hzero hW'))
  have hZU : Z ∩ Set.range f.base = W ∩ Set.range f.base := by
    have hz := congrArg (f.base '' ·) hZW'
    simpa [Set.image_preimage_eq_inter_range] using hz
  exact eq_of_inter_eq_of_mem_irreducibleComponents hZ hW f.isOpenEmbedding.isOpen_range
    ⟨x, hxZ, ⟨q, hq⟩⟩ hZU

/-- A point in the support of the vanishing ideal of a union of irreducible components satisfying
`P` lies on one of those components. -/
private theorem exists_mem_irreducibleComponents_of_mem_support_vanishingIdeal
    {X : Scheme.{u}} [IsLocallyNoetherian X] (P : Set X → Prop) {x : X}
    (hx : x ∈ (Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : {C : Set X // C ∈ irreducibleComponents X ∧ P C}, Closeds.closure C.1)).support) :
    ∃ C ∈ irreducibleComponents X, P C ∧ x ∈ C := by
  let S := {C : Set X // C ∈ irreducibleComponents X ∧ P C}
  have hcomponents : LocallyFinite (fun C : irreducibleComponents X => (C : Set X)) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  have hclosed : IsClosed (⋃ C : S, (C.1 : Set X)) :=
    (locallyFinite_component_subfamily hcomponents P).isClosed_iUnion fun C =>
      isClosed_of_mem_irreducibleComponents C.1 C.2.1
  change x ∈ ((Scheme.IdealSheafData.vanishingIdeal
    (⨆ C : S, Closeds.closure C.1)).support : Set X) at hx
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, coe_iSup_closure_eq_iUnion_of_isClosed
    (fun C : S => C.1) (fun C => isClosed_of_mem_irreducibleComponents C.1 C.2.1) hclosed] at hx
  obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
  exact ⟨C.1, C.2.1, C.2.2, hxC⟩

/-- **Stacks Project, Tag 0E38.** Every point where a reduced equidimensional closed subcurve
meets the scheme-theoretic closure of its complement, in a one-dimensional equidimensional curve
over a field with at worst nodal singularities, is a node of the ambient curve. -/
@[stacks 0E38 "intersection_points_are_nodes"]
theorem isNode_of_mem_intersection_complementaryCurve
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) :
    let U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
    ∀ y : (I ⊔ U.ι.ker).subscheme, IsNode k X ((I ⊔ U.ι.ker).subschemeι.base y) := by
  intro U y
  let x := (I ⊔ U.ι.ker).subschemeι.base y
  have hx : x ∈ (I ⊔ U.ι.ker).support := by
    change x ∈ ((I ⊔ U.ι.ker).support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have hx_inter : x ∈ I.support ⊓ U.ι.ker.support := by
    simpa only [Scheme.IdealSheafData.support_sup] using hx
  have hZcomp : U.ι.ker = Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : {C : Set X // C ∈ irreducibleComponents X ∧ ¬ C ⊆ (I.support : Set X)},
        Closeds.closure C.1) :=
    complementaryCurveIdeal_eq_union_irreducibleComponents hX_nodal I
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  obtain ⟨C, hC, hCI, hxC⟩ := exists_mem_irreducibleComponents_of_mem_support_vanishingIdeal
    (fun C => C ⊆ (I.support : Set X))
    (eq_union_irreducibleComponents hX_equidimensional hX_dimension hX_nodal I
      hY_equidimensional hY_dimension ▸ hx_inter.1)
  obtain ⟨D, hD, hDI, hxD⟩ := exists_mem_irreducibleComponents_of_mem_support_vanishingIdeal
    (fun C => ¬ C ⊆ (I.support : Set X)) (hZcomp ▸ hx_inter.2)
  have hCD : C ≠ D := fun h => hDI (h ▸ hCI)
  have hxClosed := closed_of_mem_distinct_irreducibleComponents (k := k) hX_dimension
    hC hD hCD hxC hxD
  rcases hX_nodal x hxClosed with hxsmooth | hxnode
  · exact absurd (irreducibleComponents_eq_of_stalkDomain
      (stalk_isDomain_of_smoothAt k X x hxsmooth) hC hD hxC hxD) hCD
  · exact hxnode

end Stacks.Curves

end
