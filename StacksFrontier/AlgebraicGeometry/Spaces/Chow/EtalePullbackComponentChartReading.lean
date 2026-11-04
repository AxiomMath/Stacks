module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleOfClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackOrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPreimageDominance
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimensionOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding

/-!
# Chart readings along étale charts and along the irreducible components of a chart

This file collects the chart-level lemmas which the proof of Stacks 0EQ2 and of the component
clause of Stacks 0EQA use, and which do not depend on the bookkeeping of the cycles on the
irreducible components:

* `Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes` and
  `AlgebraicGeometry.Scheme.Hom.nonZeroDivisors_le_comap_appTop`: restriction along a map
  carrying minimal primes (generic points) to minimal primes (generic points) preserves
  nonzerodivisors, the source being reduced.
* `AlgebraicGeometry.Space.mem_irreducibleComponents_of_maximal_subset_preimage`,
  `AlgebraicGeometry.Space.mem_irreducibleComponents_image_closedSubspaceBaseChangeChartProj`,
  `AlgebraicGeometry.Space.mapsTo_genericPoints_closedSubspaceBaseChangeChartProj` and
  `AlgebraicGeometry.Space.nonZeroDivisors_le_comap_chartGlobalSectionsRestrict`: the irreducible
  components of the chart `W ×_X X'` of an irreducible component `X'` of `X` are irreducible
  components of the chart `W`.
* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionMap_componentChart`
  states that the chart reading of `g ∘ f|_{X'}` on `W ×_X X'` is the restriction of the reading
  of `g`.
* `AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`:
  the restriction of an étale morphism to an irreducible component of the source is dominant.

## Implementation notes

The declarations here supplement
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor`, which this module
imports. The material on `etaleChartComp` and the étale pullback of the order of vanishing is
in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackOrderOfVanishing`, which this module
also imports.

## References

* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology


/-! ### The irreducible components of the inverse image of an irreducible component on a chart -/

/-- **A ring homomorphism into a reduced ring under which the minimal primes contract to minimal
primes carries nonzerodivisors to nonzerodivisors.** If `φ(a)` were a zerodivisor it would lie in
a minimal prime `𝔮` of the reduced target, so `a` would lie in `φ^{-1}(𝔮)`, a minimal prime of the
source, and an element of a minimal prime is a zerodivisor. -/
theorem _root_.Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes {A C : Type*}
    [CommRing A] [CommRing C] [_root_.IsReduced C] (φ : A →+* C)
    (h : ∀ q ∈ minimalPrimes C, Ideal.comap φ q ∈ minimalPrimes A) :
    nonZeroDivisors A ≤ (nonZeroDivisors C).comap φ := by
  intro a ha
  by_contra hcon
  obtain ⟨q, hq, haq⟩ := _root_.exists_mem_minimalPrimes_of_notMem_nonZeroDivisors C
    (a := φ a) (fun hmem => hcon (Submonoid.mem_comap.2 hmem))
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.mem_comap.2 haq) (h q hq) ha

/-- **Restriction of global sections along a morphism of affine schemes carrying generic points
to generic points carries nonzerodivisors to nonzerodivisors**, the source being reduced.

For an affine scheme the minimal primes of the ring of global sections are the generic points of
the irreducible components (`AlgebraicGeometry.mem_genericPoints_fromSpec_of_mem_minimalPrimes`
and `AlgebraicGeometry.primeIdealOf_mem_minimalPrimes_of_mem_genericPoints`), and the prime of a
point moves by contraction along restriction of sections
(`AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`). So the hypothesis says exactly that
the minimal primes of `Γ(T, 𝒪_T)` contract to minimal primes of `Γ(V, 𝒪_V)`, and
`Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes` applies. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.nonZeroDivisors_le_comap_appTop
    {T V : Scheme.{u}} [IsAffine T] [IsAffine V] [IsReduced T] (π : T ⟶ V)
    (hπ : Set.MapsTo π (genericPoints T) (genericPoints V)) :
    nonZeroDivisors Γ(V, ⊤) ≤ (nonZeroDivisors Γ(T, ⊤)).comap π.appTop.hom := by
  refine Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes _ fun q hq => ?_
  have hqp : q.IsPrime := hq.isPrime
  have hprime : (isAffineOpen_top T).primeIdealOf
      ⟨(isAffineOpen_top T).fromSpec ⟨q, hqp⟩, trivial⟩ = ⟨q, hqp⟩ :=
    primeIdealOf_fromSpec (isAffineOpen_top T) ⟨q, hqp⟩
  have hnat := IsAffineOpen.comap_primeIdealOf_appLE (f := π)
    (x := (isAffineOpen_top T).fromSpec ⟨q, hqp⟩) (⊤ : V.Opens) (isAffineOpen_top V)
    (⊤ : T.Opens) (isAffineOpen_top T) le_top trivial
  rw [hprime, show π.appLE ⊤ ⊤ le_top = π.appTop from Scheme.Hom.appLE_eq_app π] at hnat
  rw [show Ideal.comap π.appTop.hom q =
    ((isAffineOpen_top V).primeIdealOf
      ⟨π ((isAffineOpen_top T).fromSpec ⟨q, hqp⟩), trivial⟩).asIdeal from
    congrArg PrimeSpectrum.asIdeal hnat]
  exact primeIdealOf_mem_minimalPrimes_of_mem_genericPoints ⊤ (isAffineOpen_top V) _ trivial
    (hπ (mem_genericPoints_fromSpec_of_mem_minimalPrimes (isAffineOpen_top T) q hq))

section ChartPreimageComponents

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)

/-- The inverse image on a chart of an irreducible component of `|X|` is closed. -/
private theorem isClosed_preimage_chartSchemeToPoints_of_mem_irreducibleComponents
    (W : SmallEtale B S hS X) {T : Set (points B S hS X)}
    (hT : T ∈ irreducibleComponents (points B S hS X)) :
    IsClosed (chartSchemeToPoints B S hS X W ⁻¹' T) :=
  (isClosed_of_mem_irreducibleComponents T hT).preimage (continuous_chartSchemeToPoints B S hS W)

include hX hdec in
/-- **A maximal irreducible subset of the inverse image of an irreducible component of `|X|` on
an étale chart is an irreducible component of the chart.** Let `X` be a decent algebraic space
over `S`, let `W` be an étale scheme chart of `X` and let `T ⊆ |X|` be an irreducible component.
Then a subset of the inverse image of `T` in the scheme of `W` which is irreducible and maximal
among the irreducible subsets of that inverse image is an irreducible component of the scheme of
`W` itself.

So the inverse image of an irreducible component of `|X|` on a chart is *cut out by components of
the chart*, and not merely by closed subsets of them: no component of the inverse image is a
proper subset of a component of the chart. This is what the proof of Stacks 0EQ2 uses when it
groups the branches at a point over the irreducible components through it and reads each group as
an order of vanishing computed on the component — the ideal of `W ×_X X'` in `W` is then an
intersection of *minimal* primes, so restriction along `W ×_X X' → W` carries nonzerodivisors to
nonzerodivisors and the minimal primes of the two local rings correspond.

The inverse image is closed, so a maximal irreducible subset `C` of it is closed and has a
generic point `c`. The component `T` of `|X|` contains the image of `c`, so by
`AlgebraicGeometry.Space.surjective_componentOfChartComponent` some irreducible component `C'` of
the chart contains `c` and has the closure of the image of its generic point equal to `T`. Then
`C'` lies in the inverse image of `T`, being the closure of that generic point, and it contains
`C`, being closed and containing `c`; maximality of `C` makes the two equal. -/
theorem mem_irreducibleComponents_of_maximal_subset_preimage
    (W : SmallEtale B S hS X) {T : Set (points B S hS X)}
    (hT : T ∈ irreducibleComponents (points B S hS X)) {C : Set (chartScheme W)}
    (hCirr : IsIrreducible C) (hCsub : C ⊆ chartSchemeToPoints B S hS X W ⁻¹' T)
    (hCmax : ∀ D : Set (chartScheme W), IsIrreducible D →
      D ⊆ chartSchemeToPoints B S hS X W ⁻¹' T → C ⊆ D → D ⊆ C) :
    C ∈ irreducibleComponents (chartScheme W) := by
  have hpre := isClosed_preimage_chartSchemeToPoints_of_mem_irreducibleComponents B S hS W hT
  have hCcl : closure C = C :=
    subset_antisymm (hCmax _ hCirr.closure (hpre.closure_subset_iff.2 hCsub) subset_closure)
      subset_closure
  obtain ⟨c, hc⟩ := QuasiSober.sober hCirr (closure_subset_iff_isClosed.1 hCcl.le)
  have hcC : c ∈ C := hc ▸ subset_closure rfl
  obtain ⟨⟨⟨C', hC'⟩, hcC'⟩, hmap⟩ :=
    surjective_componentOfChartComponent B S hS hX hdec W c ⟨⟨T, hT⟩, hCsub hcC⟩
  have hgen : closure ({chartSchemeToPoints B S hS X W
        (genericPoints.ofComponent (⟨C', hC'⟩ : irreducibleComponents (chartScheme W))).1} :
      Set (points B S hS X)) = T := by
    rw [← coe_componentOfChartComponent B S hS hX hdec W c ⟨⟨C', hC'⟩, hcC'⟩]
    exact congrArg (fun V => (V.1.1 : Set (points B S hS X))) hmap
  have hC'sub : C' ⊆ chartSchemeToPoints B S hS X W ⁻¹' T := fun x hx => by
    rw [Set.mem_preimage, ← hgen]
    exact (((genericPoints.isGenericPoint_ofComponent
          (⟨C', hC'⟩ : irreducibleComponents (chartScheme W))).specializes hx).map
      (continuous_chartSchemeToPoints B S hS W)).mem_closure
  have hCC' : C ⊆ C' := by
    rw [← hc]
    exact (isClosed_of_mem_irreducibleComponents C' hC').closure_subset_iff.2
      (Set.singleton_subset_iff.2 hcC')
  rwa [subset_antisymm hCC' (hCmax C' hC'.1 hC'sub hCC')]

include hX hdec in
/-- **The irreducible components of the chart `W ×_X X'` of an irreducible component `X'` of `X`
are irreducible components of the chart `W`.** Let `X` be a decent algebraic space over `S`, let
`X' ⊆ X` be a closed subspace whose set of points is an irreducible component of `|X|`, and let
`W` be an étale scheme chart of `X`. Then the image in the scheme of `W` of an irreducible
component of the scheme of the chart `W ×_X X'` of `X'`
(`AlgebraicGeometry.Space.closedSubspaceBaseChangeChart`) is an irreducible component of the
scheme of `W`.

This is the form in which the proof of Stacks 0EQ2 needs
`AlgebraicGeometry.Space.mem_irreducibleComponents_of_maximal_subset_preimage`: the closed
immersion `W ×_X X' → W` of Stacks 03G2 has image the inverse image of `|X'|`
(`AlgebraicGeometry.Space.range_closedSubspaceBaseChangeChartProj`), so a component of `W ×_X X'`
is carried to a maximal irreducible subset of that inverse image — maximal because a larger
irreducible subset has a generic point, which lies in the image, so the whole subset is the image
of the closure of a point of `W ×_X X'` and the component is maximal there. -/
theorem mem_irreducibleComponents_image_closedSubspaceBaseChangeChartProj
    (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y)
    (hYcomp : subspacePointSet B S hS X Y ∈ irreducibleComponents (points B S hS X))
    (W : SmallEtale B S hS X)
    {C : Set (chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W))}
    (hC : C ∈ irreducibleComponents
      (chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W))) :
    closedSubspaceBaseChangeChartProj B S hS hX Y hY W '' C ∈
      irreducibleComponents (chartScheme W) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX Y hY W
  have hemb := (closedSubspaceBaseChangeChartProj B S hS hX Y hY W).isClosedEmbedding
  have hrange := range_closedSubspaceBaseChangeChartProj B S hS hX Y hY W
  have hpre := isClosed_preimage_chartSchemeToPoints_of_mem_irreducibleComponents B S hS W hYcomp
  refine mem_irreducibleComponents_of_maximal_subset_preimage B S hS hX hdec W hYcomp
    (hC.1.image _ hemb.continuous.continuousOn)
    ((Set.image_subset_range _ _).trans hrange.le) ?_
  intro D hD hDsub hsub
  obtain ⟨d, hd⟩ := QuasiSober.sober hD.closure isClosed_closure
  obtain ⟨e, he⟩ : d ∈ Set.range (closedSubspaceBaseChangeChartProj B S hS hX Y hY W) := by
    rw [hrange]
    exact hpre.closure_subset_iff.2 hDsub (hd ▸ subset_closure rfl)
  have hDcl : closure D =
      closedSubspaceBaseChangeChartProj B S hS hX Y hY W '' closure {e} := by
    rw [← hemb.closure_image_eq, Set.image_singleton, he, hd]
  have hCE : C ⊆ closure {e} := by
    rw [← Set.image_subset_image_iff hemb.injective, ← hDcl]
    exact hsub.trans subset_closure
  calc D ⊆ closure D := subset_closure
    _ = closedSubspaceBaseChangeChartProj B S hS hX Y hY W '' closure {e} := hDcl
    _ ⊆ _ := Set.image_mono (hC.2 isIrreducible_singleton.closure hCE)

include hX hdec in
/-- **The projection `W ×_X X' → W` carries generic points to generic points**, for `X' ⊆ X` a
closed subspace whose set of points is an irreducible component of `|X|`. A generic point of
`W ×_X X'` is the generic point of an irreducible component of it; that component is carried by
the closed immersion to its closure, which is an irreducible component of the scheme of `W` by
`AlgebraicGeometry.Space.mem_irreducibleComponents_image_closedSubspaceBaseChangeChartProj`. -/
theorem mapsTo_genericPoints_closedSubspaceBaseChangeChartProj
    (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y)
    (hYcomp : subspacePointSet B S hS X Y ∈ irreducibleComponents (points B S hS X))
    (W : SmallEtale B S hS X) :
    Set.MapsTo (closedSubspaceBaseChangeChartProj B S hS hX Y hY W)
      (genericPoints (chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W)))
      (genericPoints (chartScheme W)) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX Y hY W
  have hemb := (closedSubspaceBaseChangeChartProj B S hS hX Y hY W).isClosedEmbedding
  intro t ht
  have himg := mem_irreducibleComponents_image_closedSubspaceBaseChangeChartProj B S hS hX hdec
    Y hY hYcomp W ht
  rwa [← hemb.closure_image_eq, Set.image_singleton] at himg

include hX hdec in
/-- **Restriction of global sections along `W ×_X X' → W` carries nonzerodivisors to
nonzerodivisors**, for `X' ⊆ X` a closed subspace whose set of points is an irreducible component
of `|X|`, `W` an affine étale chart of `X` and the scheme of `W ×_X X'` affine and reduced.

This is the hypothesis `hj` of
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionMap` at the
cartesian square `AlgebraicGeometry.Space.closedSubspaceBaseChangeChartDiagram`. The projection
carries generic points to generic points, because the irreducible components of `W ×_X X'` are
irreducible components of `W`; on rings of global sections that says the minimal primes contract
to minimal primes, and in a reduced ring an element lying in no minimal prime is a
nonzerodivisor — `AlgebraicGeometry.Scheme.Hom.nonZeroDivisors_le_comap_appTop`. -/
theorem nonZeroDivisors_le_comap_chartGlobalSectionsRestrict
    (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y)
    (hYcomp : subspacePointSet B S hS X Y ∈ irreducibleComponents (points B S hS X))
    (W : SmallEtale B S hS X) [IsAffine W.obj.left.left.1]
    [IsAffine (closedSubspaceBaseChangeChart B S hS hX Y hY W).obj.left.left.1]
    [IsReduced (closedSubspaceBaseChangeChart B S hS hX Y hY W).obj.left.left.1] :
    nonZeroDivisors Γ(((SmallEtale.toOver B S hS X).obj W).left.1, ⊤) ≤
      (nonZeroDivisors Γ(((SmallEtale.toOver B S hS Y.toFunctor).obj
          (closedSubspaceBaseChangeChart B S hS hX Y hY W)).left.1, ⊤)).comap
        (chartGlobalSectionsRestrict B S hS
          (closedSubspaceBaseChangeChartDiagram B S hS hX Y hY W).g) := by
  have : IsAffine (chartScheme W) := inferInstanceAs (IsAffine W.obj.left.left.1)
  have : IsAffine (chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W)) :=
    inferInstanceAs
      (IsAffine (closedSubspaceBaseChangeChart B S hS hX Y hY W).obj.left.left.1)
  have : IsReduced (chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W)) :=
    inferInstanceAs
      (IsReduced (closedSubspaceBaseChangeChart B S hS hX Y hY W).obj.left.left.1)
  exact Scheme.Hom.nonZeroDivisors_le_comap_appTop
    (closedSubspaceBaseChangeChartProj B S hS hX Y hY W)
    (mapsTo_genericPoints_closedSubspaceBaseChangeChartProj B S hS hX hdec Y hY hYcomp W)

end ChartPreimageComponents

/-! ### The chart reading of the pullback of a rational function to an irreducible component -/

section ComponentChartReading

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    {f : X ⟶ Y} (hetale : IsEtale B S hS f)
    (X' : Subfunctor X) (hX'cl : IsClosedSubspace B S hS X')
    (hX'comp : subspacePointSet B S hS X X' ∈ irreducibleComponents (points B S hS X))
    (hX'alg : IsAlgebraicSpace B S hS X'.toFunctor)
    (hintX' : IsIntegralSpace B S hS X'.toFunctor)

include hX hdec hY hintY hetale hX'comp hintX' in
/-- **The chart reading of `g ∘ f|_{X'}` on the chart `W ×_X X'` of an irreducible component.**
Let `f : X ⟶ Y` be a morphism of algebraic spaces with `Y` integral, let `X' ⊆ X` be a closed
subspace whose set of points is an irreducible component of `|X|` and which is integral, and
suppose `f|_{X'} : X' ⟶ Y` carries the generic point of `X'` to the generic point of `Y`. Let `W`
be an affine, reduced, locally Noetherian étale chart of `X` whose chart `W ×_X X'` of `X'` is
again affine, reduced and locally Noetherian. Then the reading of `g ∘ f|_{X'}` in
`Q(Γ(W ×_X X', 𝒪))` is the reading of `g` in `Q(Γ(W, 𝒪))` restricted along the projection
`W ×_X X' → W`.

This is `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionMap` at the
cartesian square `AlgebraicGeometry.Space.closedSubspaceBaseChangeChartDiagram`, `W` being read
as a chart of `Y` through the composite with `f`. **No flatness of `f|_{X'}` is used**: the only
hypothesis of that lemma beyond the commuting square is that restriction along the projection
carries nonzerodivisors to nonzerodivisors, which is
`AlgebraicGeometry.Space.nonZeroDivisors_le_comap_chartGlobalSectionsRestrict`. -/
theorem rationalFunctionsToTotalFractionRing_rationalFunctionMap_componentChart
    (hgen : pointsMap B S hS X'.toFunctor (X'.ι ≫ f)
        (genericPoint B S hS hX'alg hintX') = genericPoint B S hS hY hintY)
    (W : SmallEtale B S hS X) [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1]
    [IsAffine (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    [IsReduced (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    [IsLocallyNoetherian
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    (g : rationalFunctions B S hS hY) :
    rationalFunctionsToTotalFractionRing B S hS hX'alg
        (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left
        (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.hom
        ((isEtale_iff_presheaf_of_yoneda B S hS
            (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.hom).2
          (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).property)
        (rationalFunctionMap B S hS hX'alg hY hintX' hintY (X'.ι ≫ f) hgen g) =
      chartFractionMap B S hS (closedSubspaceBaseChangeChartDiagram B S hS hX X' hX'cl W).g
        (nonZeroDivisors_le_comap_chartGlobalSectionsRestrict B S hS hX hdec X' hX'cl hX'comp W)
        (rationalFunctionsToTotalFractionRing B S hS hY W.obj.left (W.obj.hom ≫ f)
          (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).2 W.property)
            hetale) g) :=
  rationalFunctionsToTotalFractionRing_rationalFunctionMap B S hS hX'alg hY hintX' hintY
    (X'.ι ≫ f) hgen
    (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.hom _
    (W.obj.hom ≫ f) _
    (closedSubspaceBaseChangeChartDiagram B S hS hX X' hX'cl W).g
    (((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ f)
      (closedSubspaceBaseChangeChartDiagram B S hS hX X' hX'cl W).comm.symm)).trans
      (Category.assoc _ _ _))
    (nonZeroDivisors_le_comap_chartGlobalSectionsRestrict B S hS hX hdec X' hX'cl hX'comp W) g

end ComponentChartReading

/-! ### Dominance of the restriction to an irreducible component -/

/-- **Stacks 0EQ2, the first step of the source, at an arbitrary irreducible component.** In
Situation 0EDT let `f : X ⟶ Y` be an étale morphism of good algebraic spaces over `B`, let `Y` be
integral and let `X' ⊆ X` be an irreducible component of `X`. Then `f|_{X'} : X' ⟶ Y` is
dominant: it carries the generic point of `X'` to the generic point of `Y`. This is what makes
the pullback `g ∘ f|_{X'}` of a rational function defined (Morphisms of Spaces, Section 0EML).

The source argues from the openness of `|X| → |Y|` together with the local finiteness of the
components of `|X|`, which makes `|X'|` carry a nonempty open subset of `|X|` whose image is a
nonempty open subset of the irreducible `|Y|` and therefore contains the generic point. The
weaker input that generizations *lift* along `|X| → |Y|` suffices and avoids local finiteness
altogether: an étale morphism is flat, so
`AlgebraicGeometry.Space.FlatPreimage.generalizingMap_pointsMap_of_isFlat` applies, and a
continuous generalizing map into a quasi-sober space carries the generic point of an irreducible
component to the generic point of an irreducible component of the target
(`GeneralizingMap.mem_irreducibleComponents_closure_singleton`). Since `|Y|` is irreducible its
only irreducible component is the whole of `|Y|`, so the image of the generic point of `X'` is a
generic point of `|Y|`, hence *the* generic point, `|Y|` being Kolmogorov by Stacks 03K3. -/
theorem pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace
    (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1) :
    pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor (W.1.subspace.ι ≫ f)
        (genericPoint D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX W.1).1 W.1.isIntegralSpace) =
      genericPoint D.site D.base D.base_mem hY.1 hintY := by
  have hQS : QuasiSober (points D.site D.base D.base_mem Y) := quasiSober_points_of_isGood D sY hY
  have hT0 : T0Space (points D.site D.base D.base_mem Y) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY)
  have hirrY : IrreducibleSpace (points D.site D.base D.base_mem Y) := hintY.2.2
  have hcomp := GeneralizingMap.mem_irreducibleComponents_closure_singleton
    (FlatPreimage.generalizingMap_pointsMap_of_isFlat D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sY hY) (isFlat_of_isEtale D.site D.base D.base_mem hetale))
    (continuous_pointsMap D.site D.base D.base_mem f) W.2.2.2
    (W.1.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1)
  have huniv : IsGenericPoint (pointsMap D.site D.base D.base_mem X f
        (W.1.ambientGenericPoint D.site D.base D.base_mem))
      (Set.univ : Set (points D.site D.base D.base_mem Y)) :=
    Set.eq_univ_of_univ_subset
      (hcomp.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
  rw [show pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor (W.1.subspace.ι ≫ f)
        (genericPoint D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX W.1).1 W.1.isIntegralSpace) =
      pointsMap D.site D.base D.base_mem X f
        (W.1.ambientGenericPoint D.site D.base D.base_mem) from
    congrFun (pointsMap_comp D.site D.base D.base_mem W.1.subspace.toFunctor
      W.1.subspace.ι f) _]
  exact huniv.eq (isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY)

end AlgebraicGeometry.Space

end
