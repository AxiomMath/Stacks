module

public import StacksFrontier.AlgebraicGeometry.Chow.ClosedImmersionStalkBranches
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponentChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.ClosedImmersionStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MinimalPrimeOrderQuotientTransport

/-!
# The branches on an irreducible component, read on a chart of that component

Let `X` be a decent algebraic space over `S`, let `X' ⊆ X` be a closed subspace whose set of
points is an irreducible component of `|X|`, let `W` be an étale chart of `X` and let `w'` be a
point of the chart `W ×_X X'` of `X'` over the point `w` of `W`. The branches of `X` at the image
of `w` visible on `W` are the minimal primes of `𝒪_{W, w}`, and the component of `|X|` on which
each lies is `AlgebraicGeometry.Space.componentOfBranch`. This file identifies the branches
visible on the chart `W ×_X X'` of the component with the branches on `W` lying on `X'`, and
transports the order of vanishing along a branch between the two.

## Main results

* `AlgebraicGeometry.Scheme.totalFractionRingToStalkFractionRing_map_appTop`: for a morphism
  `π : T ⟶ V` of affine schemes, reading a fraction of `Γ(V, 𝒪_V)` at a point of `T` after
  restricting along `π` is the same as restricting its reading at the image point along the
  stalk map.
* `AlgebraicGeometry.Space.comap_stalkMap_closedSubspaceBaseChangeChartProj_mem_minimalPrimes`:
  a minimal prime of `𝒪_{W ×_X X', w'}` contracts to a minimal prime of `𝒪_{W, w}`.
* `AlgebraicGeometry.Space.nonZeroDivisors_le_comap_stalkMap_closedSubspaceBaseChangeChartProj`:
  the stalk map `𝒪_{W, w} → 𝒪_{W ×_X X', w'}` carries nonzerodivisors to nonzerodivisors.
* `AlgebraicGeometry.Space.ker_stalkMap_closedSubspaceBaseChangeChartProj_le_iff`: a branch on
  `W` contains the kernel of that stalk map if and only if it lies on the component `X'`.
* `AlgebraicGeometry.Space.finsum_minimalPrimeOrd_stalkMap_eq_finsum_branch_on_component`: the
  sum of the orders of vanishing over the branches of `W ×_X X'` at `w'` is the sum over the
  branches of `W` at `w` lying on `X'`.
* `AlgebraicGeometry.Space.chartPointRationalFunctionMap_rationalFunctionMap_componentChart`: the
  reading of `g ∘ f|_{X'}` in `Q(𝒪_{W ×_X X', w'})` is the image, along the stalk map of the
  closed immersion `W ×_X X' → W`, of the reading of `g` in `Q(𝒪_{W, w})`.
* `AlgebraicGeometry.Space.chartPointRationalFunctionMap_etaleChartComp`: the reading of `g` at
  `w` on `W` read as a chart of `Y`, unfolded into the germ of its reading on global sections.
* `AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_finsum_branch_on_component`: the order of
  vanishing of `g ∘ f|_{X'}` along a prime divisor of `X'` is the subsum, over the branches lying
  on `X'`, of the orders of vanishing of the reading `ĝ` of `g` in `Q(𝒪_{W, w})`.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_finsum_minimalPrimeOrd_etaleChartComp`: the order
  of vanishing of `g` along a prime divisor of `Y` as the sum over all the branches of
  `𝒪_{W, w}`, written with the same `ĝ` as the previous result.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-! ### The reading of a fraction at a point, along a morphism of affine schemes -/

/-- For `π : T ⟶ V` a morphism of affine schemes and `t` a point of `T`, the reading at `t` of
the restriction along `π` of a fraction of `Γ(V, 𝒪_V)` is the image, along the stalk map
`𝒪_{V, π t} → 𝒪_{T, t}`, of its reading at `π t`:

`Q(Γ(V, 𝒪)) → Q(Γ(T, 𝒪)) → Q(𝒪_{T, t})` equals `Q(Γ(V, 𝒪)) → Q(𝒪_{V, π t}) → Q(𝒪_{T, t})`. -/
theorem Scheme.totalFractionRingToStalkFractionRing_map_appTop {T V : Scheme.{u}} [IsAffine T]
    [IsAffine V] (π : T ⟶ V) (t : T)
    (hj : (Γ(V, ⊤))⁰ ≤ ((Γ(T, ⊤))⁰).comap π.appTop.hom)
    (hst : (V.presheaf.stalk (π t))⁰ ≤ ((T.presheaf.stalk t)⁰).comap (π.stalkMap t).hom)
    (x : FractionRing Γ(V, ⊤)) :
    T.totalFractionRingToStalkFractionRing t
        (IsLocalization.map (FractionRing Γ(T, ⊤)) π.appTop.hom hj x) =
      IsLocalization.map (FractionRing (T.presheaf.stalk t)) (π.stalkMap t).hom hst
        (V.totalFractionRingToStalkFractionRing (π t) x) := by
  have key : (T.totalFractionRingToStalkFractionRing t).comp
        (IsLocalization.map (FractionRing Γ(T, ⊤)) π.appTop.hom hj) =
      (IsLocalization.map (FractionRing (T.presheaf.stalk t)) (π.stalkMap t).hom hst).comp
        (V.totalFractionRingToStalkFractionRing (π t)) := by
    refine IsLocalization.ringHom_ext (Γ(V, ⊤))⁰ (RingHom.ext fun a => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, IsLocalization.map_eq,
      Scheme.totalFractionRingToStalkFractionRing_algebraMap]
    exact congrArg (algebraMap _ _) (Scheme.Hom.germ_stalkMap_apply π ⊤ t trivial a).symm
  exact congrFun (congrArg
    (fun φ : FractionRing Γ(V, ⊤) →+* FractionRing (T.presheaf.stalk t) => (φ : _ → _)) key) x

namespace Space

attribute [local instance] pointTopology

section ComponentBranches

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (X' : Subfunctor X) (hX'cl : IsClosedSubspace B S hS X')
    (hX'comp : subspacePointSet B S hS X X' ∈ irreducibleComponents (points B S hS X))
    (W : SmallEtale B S hS X)
    (w' : chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W))

include hX hdec hX'comp in
/-- Let `X' ⊆ X` be a closed subspace whose set of points is an irreducible component of `|X|`,
let `W` be an étale chart of `X` and let `w'` be a point of the chart `W ×_X X'` of `X'`, lying
over the point `w` of `W`. Then every minimal prime of `𝒪_{W ×_X X', w'}` contracts along the
surjection `𝒪_{W, w} → 𝒪_{W ×_X X', w'}` to a minimal prime of `𝒪_{W, w}`. -/
theorem comap_stalkMap_closedSubspaceBaseChangeChartProj_mem_minimalPrimes
    (J : Ideal ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w'))
    (hJ : J ∈ minimalPrimes ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w')) :
    Ideal.comap ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom J ∈
      minimalPrimes ((chartScheme W).presheaf.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W
  exact Scheme.Hom.comap_stalkMap_mem_minimalPrimes
    (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W)
    (fun C hC => mem_irreducibleComponents_image_closedSubspaceBaseChangeChartProj
      B S hS hX hdec X' hX'cl hX'comp W hC) w' J hJ

include hX hdec hX'comp in
/-- For `X'` an irreducible component of `X` and the chart `W ×_X X'` reduced, the stalk map of
the projection `W ×_X X' → W` carries nonzerodivisors to nonzerodivisors. -/
theorem nonZeroDivisors_le_comap_stalkMap_closedSubspaceBaseChangeChartProj
    [IsReduced (chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W))] :
    ((chartScheme W).presheaf.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w'))⁰ ≤
      Submonoid.comap
        ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom
        ((chartScheme
          (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w')⁰ :=
  Ring.nonZeroDivisors_le_comap_of_comap_mem_minimalPrimes _ fun J hJ =>
    comap_stalkMap_closedSubspaceBaseChangeChartProj_mem_minimalPrimes B S hS hX hdec X' hX'cl
      hX'comp W w' J hJ

include hX hdec hX'comp in
/-- Let `X' ⊆ X` be a closed subspace whose set of points is an irreducible component of `|X|`,
let `W` be an étale chart of `X`, let `w'` be a point of `W ×_X X'` over the point `w` of `W` and
let `𝔭` be a minimal prime of `𝒪_{W, w}`. Then `𝔭` contains the kernel of
`𝒪_{W, w} → 𝒪_{W ×_X X', w'}` if and only if the component of `|X|` on which the branch `𝔭`
lies is `X'`. -/
theorem ker_stalkMap_closedSubspaceBaseChangeChartProj_le_iff
    (p : {p : PrimeSpectrum ((chartScheme W).presheaf.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')) //
      p.asIdeal ∈ minimalPrimes ((chartScheme W).presheaf.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w'))}) :
    RingHom.ker ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom ≤
        p.1.asIdeal ↔
      ((componentOfBranch B S hS hX hdec W
          (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w') p).1 :
        irreducibleComponents (points B S hS X)).1 = subspacePointSet B S hS X X' := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W
  have hgen := isGenericPoint_componentOfBranch B S hS hX hdec W
    (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w') p
  have hcomp := (componentOfBranch B S hS hX hdec W
    (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w') p).1.2
  have hclosed : IsClosed (subspacePointSet B S hS X X') :=
    isClosed_of_mem_irreducibleComponents _ hX'comp
  rw [Scheme.Hom.ker_stalkMap_le_iff_of_isClosedImmersion
      (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W) w' p.1,
    range_closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W, Set.mem_preimage]
  refine ⟨fun hmem => ?_, fun heq => ?_⟩
  · have hsub : ((componentOfBranch B S hS hX hdec W
        (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w') p).1 :
          irreducibleComponents (points B S hS X)).1 ⊆ subspacePointSet B S hS X X' := by
      rw [← hgen.def]
      exact hclosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
    exact subset_antisymm hsub (hcomp.2 hX'comp.1 hsub)
  · rw [← heq, ← hgen]
    exact subset_closure rfl

end ComponentBranches

/-! ### The sum over the branches on a component -/

section Sum

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (X' : Subfunctor X) (hX'cl : IsClosedSubspace B S hS X')
    (hX'comp : subspacePointSet B S hS X X' ∈ irreducibleComponents (points B S hS X))
    (W : SmallEtale B S hS X)
    (w' : chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W))

include hX hdec hX'comp in
/-- Let `X' ⊆ X` be a closed subspace whose set of points is an irreducible component of `|X|`,
let `W` be an étale chart of `X` whose chart `W ×_X X'` of `X'` is reduced, let `w'` be a point
of `W ×_X X'` over the point `w` of `W`, and suppose the two local rings are Noetherian of
dimension at most one. Then for a unit `f` of the total ring of fractions of `𝒪_{W, w}`

`∑_{𝔮 ⊂ 𝒪_{W ×_X X', w'} minimal} ord_𝔮(f) = ∑_{𝔭 ⊂ 𝒪_{W, w} minimal on X'} ord_𝔭(f)`,

the right-hand sum being over the branches of `X` at the image of `w` which lie on the component
`X'` (`AlgebraicGeometry.Space.componentOfBranch`) and the left-hand side being taken on the image
of `f` under the stalk map. -/
theorem finsum_minimalPrimeOrd_stalkMap_eq_finsum_branch_on_component
    [IsReduced (chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W))]
    [IsNoetherianRing ((chartScheme W).presheaf.stalk
      (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w'))]
    [Ring.KrullDimLE 1 ((chartScheme W).presheaf.stalk
      (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w'))]
    [IsNoetherianRing ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w')]
    [Ring.KrullDimLE 1 ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w')]
    (f : FractionRing ((chartScheme W).presheaf.stalk
      (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')))
    (hf : IsUnit f) :
    ∑ᶠ q : minimalPrimes ((chartScheme
          (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w'),
        Ring.minimalPrimeOrd q
          (IsLocalization.map
            (FractionRing ((chartScheme
              (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w'))
            ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom
            (nonZeroDivisors_le_comap_stalkMap_closedSubspaceBaseChangeChartProj
              B S hS hX hdec X' hX'cl hX'comp W w') f) (hf.map _) =
      ∑ᶠ p : {p : minimalPrimes ((chartScheme W).presheaf.stalk
          (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')) //
          ((componentOfBranch B S hS hX hdec W
              (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')
              ⟨⟨p.1, p.2.1.1⟩, p.2⟩).1 :
            irreducibleComponents (points B S hS X)).1 = subspacePointSet B S hS X X'},
        Ring.minimalPrimeOrd p.1 f hf := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W
  rw [Ring.finsum_minimalPrimeOrd_map_of_surjective
    ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom
    ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap_surjective w')
    (nonZeroDivisors_le_comap_stalkMap_closedSubspaceBaseChangeChartProj
      B S hS hX hdec X' hX'cl hX'comp W w')
    (fun J hJ => comap_stalkMap_closedSubspaceBaseChangeChartProj_mem_minimalPrimes
      B S hS hX hdec X' hX'cl hX'comp W w' J hJ) f hf]
  refine finsum_eq_of_bijective
    (Equiv.subtypeEquivRight (p := fun p : minimalPrimes ((chartScheme W).presheaf.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')) =>
      RingHom.ker ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom ≤
        (p : Ideal _))
      fun p =>
        ker_stalkMap_closedSubspaceBaseChangeChartProj_le_iff B S hS hX hdec X' hX'cl hX'comp
          W w' ⟨⟨p.1, p.2.1.1⟩, p.2⟩)
    (Equiv.subtypeEquivRight _).bijective fun p => rfl

end Sum

/-! ### The stalk-level chart reading of the pullback of a rational function to a component -/

section ComponentChartStalkReading

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    {f : X ⟶ Y} (hetale : IsEtale B S hS f)
    (X' : Subfunctor X) (hX'cl : IsClosedSubspace B S hS X')
    (hX'comp : subspacePointSet B S hS X X' ∈ irreducibleComponents (points B S hS X))
    (hX'alg : IsAlgebraicSpace B S hS X'.toFunctor)
    (hintX' : IsIntegralSpace B S hS X'.toFunctor)

/-- For `f : X ⟶ Y` étale, `W` an affine, reduced, locally Noetherian étale chart of `X` and `v`
a point of its scheme, the reading of `g ∈ R(Y)` at `v` on the chart
`AlgebraicGeometry.Space.etaleChartComp` of `Y` is the reading of `g` in `Q(Γ(W, 𝒪_W))` followed
by the germ at `v`. -/
theorem chartPointRationalFunctionMap_etaleChartComp (W : SmallEtale B S hS X)
    [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1] [IsAffine (chartScheme W)]
    [IsAffine (etaleChartComp B S hS hetale W).obj.left.left.1]
    [IsReduced (etaleChartComp B S hS hetale W).obj.left.left.1]
    [IsLocallyNoetherian (etaleChartComp B S hS hetale W).obj.left.left.1]
    (v : chartScheme W) (g : rationalFunctions B S hS hY) :
    chartPointRationalFunctionMap B S hS hY (etaleChartComp B S hS hetale W) v g =
      (chartScheme W).totalFractionRingToStalkFractionRing v
        (rationalFunctionsToTotalFractionRing B S hS hY W.obj.left (W.obj.hom ≫ f)
          (isEtale_comp B S hS
            ((isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).2 W.property) hetale) g) :=
  rfl

include hX hdec hY hintY hetale hX'comp hintX' in
/-- Let `f : X ⟶ Y` be an étale morphism of algebraic spaces with `Y` integral, let `X' ⊆ X` be a
closed subspace whose set of points is an irreducible component of `|X|` and which is integral,
and suppose `f|_{X'} : X' ⟶ Y` carries the generic point of `X'` to the generic point of `Y`. Let
`W` be an affine, reduced, locally Noetherian étale chart of `X` whose chart `W ×_X X'` of `X'`
is again affine, reduced and locally Noetherian, and let `w'` be a point of `W ×_X X'` over the
point `w` of `W`. Then the reading of `g ∘ f|_{X'}` in `Q(𝒪_{W ×_X X', w'})` is the image, along
the stalk map `𝒪_{W, w} → 𝒪_{W ×_X X', w'}` of the closed immersion `W ×_X X' → W`, of the
reading of `g` in `Q(𝒪_{W, w})`. -/
theorem chartPointRationalFunctionMap_rationalFunctionMap_componentChart
    (hgen : pointsMap B S hS X'.toFunctor (X'.ι ≫ f)
        (genericPoint B S hS hX'alg hintX') = genericPoint B S hS hY hintY)
    (W : SmallEtale B S hS X)
    [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1] [IsAffine (chartScheme W)]
    [IsAffine (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    [IsReduced (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    [IsLocallyNoetherian (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    (w' : chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W))
    (hst : ((chartScheme W).presheaf.stalk
        (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w'))⁰ ≤
      (((chartScheme
          (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w')⁰).comap
        ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom)
    (g : rationalFunctions B S hS hY) :
    chartPointRationalFunctionMap B S hS hX'alg
        (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W) w'
        (rationalFunctionMap B S hS hX'alg hY hintX' hintY (X'.ι ≫ f) hgen g) =
      IsLocalization.map (FractionRing ((chartScheme
          (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w'))
        ((closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W).stalkMap w').hom hst
        ((chartScheme W).totalFractionRingToStalkFractionRing
          (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')
          (rationalFunctionsToTotalFractionRing B S hS hY W.obj.left (W.obj.hom ≫ f)
            (isEtale_comp B S hS
              ((isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).2 W.property) hetale) g)) := by
  have : IsAffine (chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)) :=
    inferInstanceAs
      (IsAffine (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1)
  have key := rationalFunctionsToTotalFractionRing_rationalFunctionMap_componentChart
    B S hS hX hdec hY hintY hetale X' hX'cl hX'comp hX'alg hintX' hgen W g
  exact (congrArg ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).totalFractionRingToStalkFractionRing
        w') key).trans
    (Scheme.totalFractionRingToStalkFractionRing_map_appTop
      (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W) w'
      (nonZeroDivisors_le_comap_chartGlobalSectionsRestrict B S hS hX hdec X' hX'cl hX'comp W)
      hst _)

/-! ### The two orders of vanishing as sums over the branches -/

variable (hdecX' : IsDecentSpace B S hS X'.toFunctor)
    (hNX' : HasEtaleLocalProperty B S hS X'.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdecY : IsDecentSpace B S hS Y)
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))

include hX hdec hY hintY hetale hX'comp in
/-- Let `f : X ⟶ Y` be an étale morphism of algebraic spaces with `Y` integral, let `X' ⊆ X` be a
closed subspace whose set of points is an irreducible component of `|X|` and which is decent and
integral, and suppose `f|_{X'}` carries the generic point of `X'` to that of `Y`. Let `Z ⊆ X'` be
a prime divisor of `X'`, let `W` be an affine, reduced, locally Noetherian étale chart of `X`
whose chart `W ×_X X'` of `X'` is again affine, reduced and locally Noetherian, and let `w'` be a
point of `W ×_X X'` over the generic point of `Z`, lying over the point `w` of `W`. Then for an
invertible rational function `g` of `Y`

`ord_Z(g ∘ f|_{X'}) = ∑_{𝔭 ⊂ 𝒪_{W, w} minimal, componentOfBranch 𝔭 = X'} ord_𝔭(ĝ)`,

`ĝ` being the reading of `g` in `Q(𝒪_{W, w})` on `W` read as a chart of `Y`. -/
theorem ord_rationalFunctionMap_eq_finsum_branch_on_component
    (hgen : pointsMap B S hS X'.toFunctor (X'.ι ≫ f)
        (genericPoint B S hS hX'alg hintX') = genericPoint B S hS hY hintY)
    (Z : PrimeDivisor B S hS X'.toFunctor) (W : SmallEtale B S hS X)
    [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1] [IsAffine (chartScheme W)]
    [IsAffine (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    [IsReduced (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    [IsLocallyNoetherian (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1]
    (w' : chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W))
    (hw' : chartSchemeToPoints B S hS X'.toFunctor
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W) w' =
      Z.genericPoint B S hS X'.toFunctor)
    [IsNoetherianRing ((chartScheme W).presheaf.stalk
      (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w'))]
    [Ring.KrullDimLE 1 ((chartScheme W).presheaf.stalk
      (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w'))]
    [IsNoetherianRing ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w')]
    [Ring.KrullDimLE 1 ((chartScheme
      (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)).presheaf.stalk w')]
    (g : (rationalFunctions B S hS hY)ˣ) :
    (genericFractionEmbedding B S hS hX'alg hdecX' hintX' hNX').ord
        (Units.map (rationalFunctionMap B S hS hX'alg hY hintX' hintY (X'.ι ≫ f)
          hgen).toMonoidHom g) Z =
      ∑ᶠ p : {p : minimalPrimes ((chartScheme W).presheaf.stalk
          (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')) //
          ((componentOfBranch B S hS hX hdec W
              (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')
              ⟨⟨p.1, p.2.1.1⟩, p.2⟩).1 :
            irreducibleComponents (points B S hS X)).1 = subspacePointSet B S hS X X'},
        Ring.minimalPrimeOrd p.1
          ((chartScheme W).totalFractionRingToStalkFractionRing
            (closedSubspaceBaseChangeChartProj B S hS hX X' hX'cl W w')
            (rationalFunctionsToTotalFractionRing B S hS hY W.obj.left (W.obj.hom ≫ f)
              (isEtale_comp B S hS
                ((isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).2 W.property) hetale)
              (g : rationalFunctions B S hS hY)))
          (IsUnit.map _ (IsUnit.map _ g.isUnit)) := by
  have : IsReduced (chartScheme (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W)) :=
    inferInstanceAs
      (IsReduced (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W).obj.left.left.1)
  have := Z.krullDimLE_chartStalk B S hS hX'alg hdecX'
    (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W) w' hw'
  rw [Z.ord_eq_finsum_minimalPrimeOrd B S hS hX'alg hdecX' hintX' hNX'
    (closedSubspaceBaseChangeChart B S hS hX X' hX'cl W) w' hw' _]
  refine Eq.trans ?_ (finsum_minimalPrimeOrd_stalkMap_eq_finsum_branch_on_component
    B S hS hX hdec X' hX'cl hX'comp W w' _ (IsUnit.map _ (IsUnit.map _ g.isUnit)))
  exact finsum_congr fun p => Ring.minimalPrimeOrd_congr _ _ _
    (chartPointRationalFunctionMap_rationalFunctionMap_componentChart B S hS hX hdec hY hintY
      hetale X' hX'cl hX'comp hX'alg hintX' hgen W w' _ _)

include hY hintY hetale in
/-- For `f : X ⟶ Y` étale, `W` an affine, reduced, locally Noetherian étale chart of `X` and `v`
a point of its scheme lying, as a point of `W` read as a chart of `Y`, over the generic point of
a prime divisor `Z'` of the decent, locally Noetherian, integral `Y`,

`ord_{Z'}(g) = ∑_{𝔭 ⊂ 𝒪_{W, v} minimal} ord_𝔭(ĝ)`

for `ĝ` the reading of `g` in `Q(𝒪_{W, v})`. -/
theorem PrimeDivisor.ord_eq_finsum_minimalPrimeOrd_etaleChartComp
    (Z' : PrimeDivisor B S hS Y) (W : SmallEtale B S hS X)
    [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1] [IsAffine (chartScheme W)]
    [IsAffine (etaleChartComp B S hS hetale W).obj.left.left.1]
    [IsReduced (etaleChartComp B S hS hetale W).obj.left.left.1]
    [IsLocallyNoetherian (etaleChartComp B S hS hetale W).obj.left.left.1]
    (v : chartScheme W)
    (hv : chartSchemeToPoints B S hS Y (etaleChartComp B S hS hetale W) v =
      Z'.genericPoint B S hS Y)
    [IsNoetherianRing ((chartScheme W).presheaf.stalk v)]
    [Ring.KrullDimLE 1 ((chartScheme W).presheaf.stalk v)]
    (g : (rationalFunctions B S hS hY)ˣ) :
    (genericFractionEmbedding B S hS hY hdecY hintY hNY).ord g Z' =
      ∑ᶠ p : minimalPrimes ((chartScheme W).presheaf.stalk v),
        Ring.minimalPrimeOrd p
          ((chartScheme W).totalFractionRingToStalkFractionRing v
            (rationalFunctionsToTotalFractionRing B S hS hY W.obj.left (W.obj.hom ≫ f)
              (isEtale_comp B S hS
                ((isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).2 W.property) hetale)
              (g : rationalFunctions B S hS hY)))
          (IsUnit.map _ (IsUnit.map _ g.isUnit)) := by
  have := Z'.krullDimLE_chartStalk B S hS hY hdecY (etaleChartComp B S hS hetale W) v hv
  have : IsNoetherianRing
      ((etaleChartComp B S hS hetale W).obj.left.left.1.presheaf.stalk v) :=
    inferInstanceAs (IsNoetherianRing ((chartScheme W).presheaf.stalk v))
  rw [Z'.ord_eq_finsum_minimalPrimeOrd B S hS hY hdecY hintY hNY
    (etaleChartComp B S hS hetale W) v hv g]
  exact finsum_congr fun p => Ring.minimalPrimeOrd_congr _ _ _
    (chartPointRationalFunctionMap_etaleChartComp B S hS hY hetale W v
      (g : rationalFunctions B S hS hY))

end ComponentChartStalkReading

end Space

end AlgebraicGeometry

end
