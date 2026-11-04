module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentIndex
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength
public import StacksFrontier.Topology.Sober.Generization
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionComponentAlgebra
public import StacksFrontier.RingTheory.LocalRing.TotalFractionsAway

/-!
# The local ring of a chart and the irreducible components through a point

Let `X` be a decent algebraic space, `U` an étale scheme chart of `X` and `u` a point of `U`. The
minimal primes of `O = 𝒪_{U, u}` are the generic points of `U` specializing to `u`
(`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot`), and those lie over the generic points of
the irreducible components of `|X|`, an étale chart carrying generic points to generic points and
nothing else (Stacks 0ABV). For an integral closed subspace `W ⊆ X` whose point set is an
irreducible component, the base change `U_W = U ×_X W` is a closed subscheme of `U`; at a point
`u_W` of `U_W` over `u` the stalk map `π : O → O_W = 𝒪_{U_W, u_W}` is surjective and this file
records how it meets the minimal primes:

* the minimal primes of `O_W` contract to minimal primes of `O`
  (`AlgebraicGeometry.Space.comap_closedSubspaceBaseChangeStalkMap_mem_minimalPrimes`),
  so `π` carries nonzerodivisors to nonzerodivisors;
* a minimal prime `𝔭` of `O` contains `ker π` exactly when its point lies over a point of `|W|`
  (`AlgebraicGeometry.Space.ker_closedSubspaceBaseChangeStalkMap_le_iff`);
* the length of `O_𝔭` is the multiplicity of the structure sheaf at the image of its point
  (`AlgebraicGeometry.Space.minimalPrimeLength_eq_toNat_geometricLength`), which is the
  multiplicity of Stacks 0EE9 of the component of `|X|` through it.

## References

* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Generic points of a scheme and maximal generizations -/

/-- The image of a minimal prime of a local ring of a scheme is a generic point of an irreducible
component. -/
theorem fromSpecStalk_mem_genericPoints {T : Scheme.{u}} (x : T)
    (p : PrimeSpectrum (T.presheaf.stalk x)) (hp : p.asIdeal ∈ minimalPrimes (T.presheaf.stalk x)) :
    T.fromSpecStalk x p ∈ genericPoints T :=
  TopologicalSpace.mem_genericPoints_of_forall_specializes_eq
    ((Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot x).mapsTo hp).2

/-- A prime of a local ring of a scheme whose image is a generic point of an irreducible
component is a minimal prime. -/
theorem mem_minimalPrimes_of_fromSpecStalk_mem_genericPoints {T : Scheme.{u}} (x : T)
    (p : PrimeSpectrum (T.presheaf.stalk x)) (hp : T.fromSpecStalk x p ∈ genericPoints T) :
    p.asIdeal ∈ minimalPrimes (T.presheaf.stalk x) := by
  have hpx : T.fromSpecStalk x p ⤳ x := (Scheme.range_fromSpecStalk (x := x)).subset ⟨p, rfl⟩
  obtain ⟨q, hq, hqp⟩ := (Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot x).surjOn
    ⟨hpx, forall_specializes_eq_of_mem_genericPoints hp⟩
  exact (T.fromSpecStalk x).isEmbedding.injective hqp ▸ hq

/-! ### Generic points of a chart -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X)

include hX hXdec in
/-- **A point of an étale chart is a generic point of an irreducible component of the chart
exactly when its image in `|X|` is one of `|X|`** (Stacks 0ABV). -/
theorem mem_genericPoints_chartScheme_iff (U : SmallEtale B S hS X) (q : chartScheme U) :
    q ∈ genericPoints (chartScheme U) ↔
      chartSchemeToPoints B S hS X U q ∈ genericPoints (points B S hS X) := by
  have hEt : IsEtale B S hS U.obj.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).mpr U.property
  have hcp := chartPoint_chartSchemeToPoints B S hS ⟨X, hX⟩ U q
  rw [mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hXdec]
  exact ⟨fun hq => (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).mpr
      ⟨U.obj.left, U.obj.hom, q, hEt, hcp, hq⟩,
    fun h => (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX _).mp h
      U.obj.left U.obj.hom q hEt hcp⟩

/-! ### The base change of a chart to an irreducible component -/

variable (W : IntegralClosedSubspace B S hS X)
    (hWcomp : subspacePointSet B S hS X W.subspace ∈ irreducibleComponents (points B S hS X))

include hXdec hWcomp in
/-- **The base change of a chart to an irreducible component carries generic points to generic
points.** -/
theorem closedSubspaceBaseChangeChartProj_mem_genericPoints (U : SmallEtale B S hS X)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))
    (hq : q ∈ genericPoints
      (chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))) :
    closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U q ∈
      genericPoints (chartScheme U) := by
  have hWdec : IsDecentSpace B S hS W.subspace.toFunctor :=
    W.isIntegralSpace.isDecentSpace
  have hW1 : IsAlgebraicSpace B S hS W.subspace.toFunctor := W.isClosedSubspace.1
  have hqW := (mem_genericPoints_chartScheme_iff B S hS hW1 hWdec _ q).mp hq
  have : QuasiSober (points B S hS W.subspace.toFunctor) :=
    quasiSober_points_of_isDecentSpace B S hS hW1 hWdec
  have : T0Space (points B S hS W.subspace.toFunctor) :=
    t0Space_points_of_isDecentSpace B S hS hW1 hWdec
  have : IrreducibleSpace (points B S hS W.subspace.toFunctor) := W.isIntegralSpace.2.2
  have hgen : chartSchemeToPoints B S hS W.subspace.toFunctor
      (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U) q =
      W.genericPoint B S hS := by
    rw [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton] at hqW
    exact (show IsGenericPoint _ Set.univ from hqW).eq
      (show IsGenericPoint (W.genericPoint B S hS) Set.univ from
        W.closure_singleton_genericPoint B S hS)
  rw [mem_genericPoints_chartScheme_iff B S hS hX hXdec,
    chartSchemeToPoints_closedSubspaceBaseChangeChartProj, hgen]
  change closure ({W.ambientGenericPoint B S hS} : Set (points B S hS X)) ∈
    irreducibleComponents (points B S hS X)
  rwa [(W.isGenericPoint_ambientGenericPoint B S hS hX).def]

/-- The stalk map of the projection `U ×_X W → U` at a point `q` over `u`, from the local ring at
`u`. -/
def closedSubspaceBaseChangeStalkMap (U : SmallEtale B S hS X) (u : chartScheme U)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))
    (hq : closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U q = u) :
    (chartScheme U).presheaf.stalk u →+*
      (chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace
        U)).presheaf.stalk q :=
  ((closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace
    U).stalkMap q).hom.comp
    ((chartScheme U).presheaf.stalkCongr (Inseparable.of_eq hq.symm)).hom.hom

/-- The stalk map of a closed immersion is surjective. -/
theorem surjective_closedSubspaceBaseChangeStalkMap (U : SmallEtale B S hS X)
    (u : chartScheme U)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))
    (hq : closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U q = u) :
    Function.Surjective (closedSubspaceBaseChangeStalkMap B S hS hX W U u q hq) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX W.subspace
    W.isClosedSubspace U
  exact ((closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace
    U).stalkMap_surjective q).comp ((chartScheme U).presheaf.stalkCongr
      (Inseparable.of_eq hq.symm)).commRingCatIsoToRingEquiv.surjective

/-- The stalk map at a point of `U ×_X W` over `u`, computed at the point itself, is the stalk
map of the projection. -/
theorem closedSubspaceBaseChangeStalkMap_rfl (U : SmallEtale B S hS X)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U)) :
    closedSubspaceBaseChangeStalkMap B S hS hX W U _ q rfl =
      ((closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace
        U).stalkMap q).hom := by
  ext a
  simp [closedSubspaceBaseChangeStalkMap]

/-- On the spectra of the local rings, the stalk map of the projection is compatible with the
canonical morphisms to the charts. -/
theorem fromSpecStalk_comap_closedSubspaceBaseChangeStalkMap (U : SmallEtale B S hS X)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))
    (p' : PrimeSpectrum ((chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace
      W.isClosedSubspace U)).presheaf.stalk q)) :
    (chartScheme U).fromSpecStalk _
        (PrimeSpectrum.comap ((closedSubspaceBaseChangeChartProj B S hS hX W.subspace
          W.isClosedSubspace U).stalkMap q).hom p') =
      closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U
        ((chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace
          U)).fromSpecStalk q p') :=
  congrArg (fun φ => φ.base p') (Scheme.SpecMap_stalkMap_fromSpecStalk
    (closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U) (x := q))

include hXdec hWcomp in
/-- **The minimal primes of the local ring of `U ×_X W` contract to minimal primes of the local
ring of `U`.** -/
theorem comap_closedSubspaceBaseChangeStalkMap_mem_minimalPrimes (U : SmallEtale B S hS X)
    (u : chartScheme U)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))
    (hq : closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U q = u)
    (J : Ideal ((chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace
      W.isClosedSubspace U)).presheaf.stalk q))
    (hJ : J ∈ minimalPrimes _) :
    Ideal.comap (closedSubspaceBaseChangeStalkMap B S hS hX W U u q hq) J ∈
      minimalPrimes ((chartScheme U).presheaf.stalk u) := by
  subst hq
  rw [closedSubspaceBaseChangeStalkMap_rfl]
  have hproj := closedSubspaceBaseChangeChartProj_mem_genericPoints B S hS hX hXdec W hWcomp U _
    (fromSpecStalk_mem_genericPoints q ⟨J, hJ.1.1⟩ hJ)
  rw [← fromSpecStalk_comap_closedSubspaceBaseChangeStalkMap] at hproj
  exact mem_minimalPrimes_of_fromSpecStalk_mem_genericPoints _ _ hproj

include hXdec hWcomp in
/-- The stalk map of `U ×_X W → U` carries nonzerodivisors to nonzerodivisors: the local ring of
`U ×_X W` is reduced, `W` being integral, and its minimal primes contract to minimal primes, which
consist of zerodivisors. -/
theorem nonZeroDivisors_le_comap_closedSubspaceBaseChangeStalkMap (U : SmallEtale B S hS X)
    (u : chartScheme U)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))
    (hq : closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U q = u) :
    ((chartScheme U).presheaf.stalk u)⁰ ≤
      ((chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace
        U)).presheaf.stalk q)⁰.comap (closedSubspaceBaseChangeStalkMap B S hS hX W U u q hq) := by
  have : IsReduced (chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace
      W.isClosedSubspace U)) :=
    (exists_atlas_iff_forall_etale B S hS W.subspace.toFunctor (fun Y : Scheme.{u} => IsReduced Y)
      W.isClosedSubspace.1).mp W.isIntegralSpace.1 _ _
      (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U).property
  exact fun x hx => mem_nonZeroDivisors_of_forall_notMem_minimalPrimes fun J hJ hxJ =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.mem_comap.mpr hxJ)
    (comap_closedSubspaceBaseChangeStalkMap_mem_minimalPrimes B S hS hX hXdec W hWcomp U u q hq J
      hJ) hx

/-- **A prime of the local ring of `U` contains the kernel of the stalk map of `U ×_X W → U`
exactly when its point lies over `|W|`.** -/
theorem ker_closedSubspaceBaseChangeStalkMap_le_iff (U : SmallEtale B S hS X)
    (u : chartScheme U)
    (q : chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace U))
    (hq : closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U q = u)
    (p : PrimeSpectrum ((chartScheme U).presheaf.stalk u)) :
    RingHom.ker (closedSubspaceBaseChangeStalkMap B S hS hX W U u q hq) ≤ p.asIdeal ↔
      chartSchemeToPoints B S hS X U ((chartScheme U).fromSpecStalk u p) ∈
        subspacePointSet B S hS X W.subspace := by
  have hsurj := surjective_closedSubspaceBaseChangeStalkMap B S hS hX W U u q hq
  subst hq
  rw [closedSubspaceBaseChangeStalkMap_rfl] at hsurj ⊢
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX W.subspace
    W.isClosedSubspace U
  rw [← Set.mem_preimage, ← range_closedSubspaceBaseChangeChartProj B S hS hX W.subspace
    W.isClosedSubspace U]
  constructor
  · intro hker
    refine ⟨(chartScheme (closedSubspaceBaseChangeChart B S hS hX W.subspace W.isClosedSubspace
      U)).fromSpecStalk q ⟨_, Ideal.map_isPrime_of_surjective hsurj hker⟩, ?_⟩
    rw [← fromSpecStalk_comap_closedSubspaceBaseChangeStalkMap]
    congr 1
    exact PrimeSpectrum.ext <| (Ideal.comap_map_of_surjective' _ hsurj _).trans (sup_eq_left.2 hker)
  · rintro ⟨Q, hQ⟩
    have hspec : (chartScheme U).fromSpecStalk _ p ⤳
        closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace U q :=
      Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩
    rw [← hQ] at hspec
    obtain ⟨p', rfl⟩ : Q ∈ Set.range ((chartScheme (closedSubspaceBaseChangeChart B S hS hX
        W.subspace W.isClosedSubspace U)).fromSpecStalk q) := by
      rw [Scheme.range_fromSpecStalk]
      exact ((closedSubspaceBaseChangeChartProj B S hS hX W.subspace W.isClosedSubspace
        U).isClosedEmbedding.isInducing.specializes_iff).mp hspec
    have heq : PrimeSpectrum.comap ((closedSubspaceBaseChangeChartProj B S hS hX W.subspace
        W.isClosedSubspace U).stalkMap q).hom p' = p :=
      ((chartScheme U).fromSpecStalk _).isEmbedding.injective
        ((fromSpecStalk_comap_closedSubspaceBaseChangeStalkMap B S hS hX W U q p').trans hQ)
    rw [← heq]
    exact Ideal.comap_mono bot_le

/-! ### The length of the local ring at a minimal prime -/

/-- The localization of a local ring of a scheme at a prime has the length of the local ring at
the image of that prime: the canonical morphism `Spec 𝒪_{T, x} ⟶ T` is an isomorphism on stalks
(`AlgebraicGeometry.isIso_stalkMap_fromSpecStalk`). -/
theorem length_localizationAtPrime_eq_length_stalk_fromSpecStalk {T : Scheme.{u}} (x : T)
    (p : PrimeSpectrum (T.presheaf.stalk x)) :
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) =
      Module.length (T.presheaf.stalk (T.fromSpecStalk x p))
        (T.presheaf.stalk (T.fromSpecStalk x p)) := by
  have : IsIso ((T.fromSpecStalk x).stalkMap p) := isIso_stalkMap_fromSpecStalk x p
  let e : T.presheaf.stalk (T.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal :=
    (asIso ((T.fromSpecStalk x).stalkMap p)).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso (CommRingCat.of (T.presheaf.stalk x)) p).commRingCatIsoToRingEquiv
  exact (length_self_eq_of_ringEquiv (RingHom.id _) rfl e).symm

include hX in
/-- **The multiplicity of a branch of a chart is the multiplicity of the structure sheaf at its
image.** For a minimal prime `𝔭` of the local ring `𝒪_{U, u}` of an étale chart, the length of
`(𝒪_{U, u})_𝔭` is the length of `𝒪_X` at any geometric point over the image in `|X|` of the
point of `𝔭` (Stacks 0EE1 on the chart,
`AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_length_chartStalk`). -/
theorem minimalPrimeLength_eq_toNat_geometricLength (U : SmallEtale B S hS X) (u : chartScheme U)
    (p : minimalPrimes ((chartScheme U).presheaf.stalk u))
    (xbar : GeometricPoint B S hS X)
    (hxbar : xbar.image = chartSchemeToPoints B S hS X U
      ((chartScheme U).fromSpecStalk u ⟨p, p.2.1.1⟩)) :
    Ring.minimalPrimeLength p =
      ((geometricLength B S hS ⟨X, hX⟩ xbar (structureSheafModule B S hS ⟨X, hX⟩)).toNat : ℤ) := by
  rw [geometricLength_structureSheafModule_eq_length_chartStalk B S hS ⟨X, hX⟩ xbar U _
    hxbar.symm, ← length_localizationAtPrime_eq_length_stalk_fromSpecStalk u ⟨p, p.2.1.1⟩]
  rfl

end AlgebraicGeometry.Space

end
