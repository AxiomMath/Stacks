module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierComponentDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentGenericFractionFlatChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponentChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion

/-!
# Generic points of a chart of an irreducible component, for an arbitrary chart morphism

Let `X` be a decent algebraic space over `S` and let `W ⊆ X` be an integral closed subspace
whose set of points is an irreducible component of `|X|`. Let `cV : V → X` be an étale chart of
`X`, let `cU : U → W` be an étale chart of `W` and let `j : U ⟶ V` be **any** morphism of the
site over the inclusion `W ⟶ X`. This file proves that `j` carries generic points of
irreducible components of `U` to generic points of irreducible components of `V`, and hence —
`AlgebraicGeometry.Scheme.Hom.nonZeroDivisors_le_comap_appTop` — that restriction of global
sections along `j` carries nonzerodivisors to nonzerodivisors when `U` and `V` are affine and
`U` is reduced.

## Main results

* `mapsTo_genericPoints_of_chartSquare_irreducibleComponent`: a morphism of charts over the
  inclusion of an irreducible component carries generic points to generic points.
* `nonZeroDivisors_le_comap_chartGlobalSectionsRestrict_of_irreducibleComponent`: restriction of
  global sections along such a morphism carries nonzerodivisors to nonzerodivisors.
* `PrimeDivisor.exists_rationalFunctionsToGenericTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_of_irreducibleComponent`:
  the reading on an irreducible component of the pullback of a rational function along a flat
  morphism is a fraction of the classes of two global sections of a chart of the ambient space.
* `rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_of_eq`: the chart
  reading of the pullback as a fraction of two given global sections of the flat chart.
* `exists_sections_forall_rationalFunctionsToGenericTotalFractionRing_eq_mk'_of_isFlat`: one
  numerator and one denominator presenting the reading on every irreducible component at once.

## References

* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Generic points of an integral closed subspace -/

/-- A generic point of an irreducible component of the point space of an integral closed
subspace is its generic point. -/
theorem IntegralClosedSubspace.eq_genericPoint_of_mem_genericPoints
    (W : IntegralClosedSubspace B S hS X) {y : points B S hS W.subspace.toFunctor}
    (hy : y ∈ genericPoints (points B S hS W.subspace.toFunctor)) :
    y = W.genericPoint B S hS := by
  let := W.t0Space_points B S hS
  let := W.irreducibleSpace_points B S hS
  have hy' : closure ({y} : Set (points B S hS W.subspace.toFunctor)) ∈
    irreducibleComponents (points B S hS W.subspace.toFunctor) := hy
  have huniv : closure ({y} : Set (points B S hS W.subspace.toFunctor)) = Set.univ :=
    Set.univ_subset_iff.1
      (hy'.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
  exact (inseparable_iff_closure_eq.2
    (huniv.trans (W.closure_singleton_genericPoint B S hS).symm)).eq

/-- The ambient generic point of an integral closed subspace whose set of points is an
irreducible component of the ambient space is a generic point of the ambient space. -/
theorem IntegralClosedSubspace.mem_genericPoints_ambientGenericPoint_of_mem_irreducibleComponents
    (hX : IsAlgebraicSpace B S hS X) (W : IntegralClosedSubspace B S hS X)
    (hWcomp : subspacePointSet B S hS X W.subspace ∈
      irreducibleComponents (points B S hS X)) :
    W.ambientGenericPoint B S hS ∈ genericPoints (points B S hS X) := by
  show closure ({W.ambientGenericPoint B S hS} : Set (points B S hS X)) ∈
    irreducibleComponents (points B S hS X)
  rw [(W.isGenericPoint_ambientGenericPoint B S hS hX).def]
  exact hWcomp

/-! ### Generic points along a chart morphism over the inclusion of a component -/

/-- Let `X` be a decent algebraic space over `S`, let `W ⊆ X` be an integral closed subspace
whose set of points is an irreducible component of `|X|`, let `cU : U → W` and `cV : V → X` be
étale charts and let `j : U ⟶ V` be a morphism of the site with `j ≫ cV = cU ≫ (W ⟶ X)`. Then
`j` carries a generic point of an irreducible component of the scheme `U` to a generic point of
an irreducible component of the scheme `V`. -/
theorem mapsTo_genericPoints_of_chartSquare_irreducibleComponent
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (W : IntegralClosedSubspace B S hS X)
    (hWcomp : subspacePointSet B S hS X W.subspace ∈
      irreducibleComponents (points B S hS X))
    {U V : BigFppfOver B S hS} (cU : yoneda.obj U ⟶ W.subspace.toFunctor)
    (hcU : IsEtale B S hS cU) (cV : yoneda.obj V ⟶ X) (hcV : IsEtale B S hS cV) (j : U ⟶ V)
    (hsq : yoneda.map j ≫ cV = cU ≫ W.subspace.ι) :
    Set.MapsTo ((BigFppfOver.toScheme B S hS).map j)
      (genericPoints ((BigFppfOver.toScheme B S hS).obj U))
      (genericPoints ((BigFppfOver.toScheme B S hS).obj V)) := by
  intro u hu
  obtain ⟨p, rfl⟩ : ∃ p, pointsToScheme B S hS U p = u :=
    ⟨(schemePointsHomeomorph B S hS U).symm u, by
      rw [← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]⟩
  have hdimU : localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) cU p) = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS
      W.isClosedSubspace.1 _).2
      ⟨U, cU, pointsToScheme B S hS U p, hcU, chartPoint_pointsToScheme B S hS U cU p, hu⟩
  have hygen : pointsMap B S hS (yoneda.obj U) cU p ∈
      genericPoints (points B S hS W.subspace.toFunctor) :=
    mem_genericPoints_of_localRingDimension_eq_zero B S hS W.isClosedSubspace.1
      W.isIntegralSpace.2.1 hdimU
  have hximg : pointsMap B S hS (yoneda.obj V) cV
        (pointsMap B S hS (yoneda.obj U) (yoneda.map j) p) =
      W.ambientGenericPoint B S hS := by
    have h1 := congrFun (pointsMap_comp B S hS (yoneda.obj U) (yoneda.map j) cV) p
    have h2 := congrFun (pointsMap_comp B S hS (yoneda.obj U) cU W.subspace.ι) p
    have h3 : pointsMap B S hS (yoneda.obj U) (yoneda.map j ≫ cV) p =
        pointsMap B S hS (yoneda.obj U) (cU ≫ W.subspace.ι) p := by
      rw [hsq]
    rw [IntegralClosedSubspace.ambientGenericPoint,
      ← W.eq_genericPoint_of_mem_genericPoints B S hS hygen]
    exact (h1.symm.trans h3).trans h2
  have hdimX : localRingDimension B S hS (pointsMap B S hS (yoneda.obj V) cV
      (pointsMap B S hS (yoneda.obj U) (yoneda.map j) p)) = 0 :=
    localRingDimension_eq_zero_of_mem_genericPoints B S hS hX hdec
      (hximg ▸ W.mem_genericPoints_ambientGenericPoint_of_mem_irreducibleComponents B S hS hX
        hWcomp)
  have hchartV := chartPoint_pointsToScheme B S hS V cV
    (pointsMap B S hS (yoneda.obj U) (yoneda.map j) p)
  rw [pointsToScheme_pointsMap_yoneda_map B S hS j p] at hchartV
  exact (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX _).1 hdimX V cV _
    hcV hchartV

/-- Restriction of global sections along a morphism of charts over the inclusion of an
irreducible component carries nonzerodivisors to nonzerodivisors, the chart of the component
being affine and reduced and the chart of the ambient space affine. -/
theorem nonZeroDivisors_le_comap_chartGlobalSectionsRestrict_of_irreducibleComponent
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (W : IntegralClosedSubspace B S hS X)
    (hWcomp : subspacePointSet B S hS X W.subspace ∈
      irreducibleComponents (points B S hS X))
    {U V : BigFppfOver B S hS} [IsAffine U.left.1] [IsReduced U.left.1]
    [IsAffine V.left.1] (cU : yoneda.obj U ⟶ W.subspace.toFunctor) (hcU : IsEtale B S hS cU)
    (cV : yoneda.obj V ⟶ X) (hcV : IsEtale B S hS cV) (j : U ⟶ V)
    (hsq : yoneda.map j ≫ cV = cU ≫ W.subspace.ι) :
    (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := inferInstanceAs (IsAffine U.left.1)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := inferInstanceAs (IsAffine V.left.1)
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj U) :=
    inferInstanceAs (IsReduced U.left.1)
  exact Scheme.Hom.nonZeroDivisors_le_comap_appTop ((BigFppfOver.toScheme B S hS).map j)
    (mapsTo_genericPoints_of_chartSquare_irreducibleComponent B S hS hX hdec W hWcomp cU hcU
      cV hcV j hsq)

/-! ### The reading on a component, with the nonzerodivisor hypothesis discharged -/

/-- Let `X` be a decent algebraic space over `S`, let `V` be an affine, locally Noetherian
elementary étale neighborhood of a point `x` of `X`, let `W ⊆ X` be an integral closed subspace
whose set of points is an irreducible component of `|X|`, let `Z'` be a prime divisor of `W` and
let `U` be an affine elementary étale neighborhood of its generic point with a morphism
`j : U ⟶ V` over the inclusion carrying the distinguished point to the distinguished point and
surjective on Zariski stalks. For `f : X ⟶ Y` flat with `Y` integral and `g` a rational function
of `Y`, the reading of `g ∘ f|_W` in `Q(𝒪^h_{W, ξ'})` is the fraction of the images of two
global sections `s`, `t` of `𝒪_V` in a quotient of `𝒪^h_{X, x}` presenting `𝒪^h_{W, ξ'}`. -/
theorem PrimeDivisor.exists_rationalFunctionsToGenericTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_of_irreducibleComponent
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXd : IsDecentSpace B S hS X) {x : points B S hS X}
    (V : ElementaryEtaleNeighborhood B S hS X hX x) [IsAffine V.scheme.left.1]
    [IsLocallyNoetherian V.scheme.left.1] (W : IntegralClosedSubspace B S hS X)
    (hWcomp : subspacePointSet B S hS X W.subspace ∈
      irreducibleComponents (points B S hS X))
    (hWN : HasEtaleLocalProperty B S hS W.subspace.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (Z' : PrimeDivisor B S hS W.subspace.toFunctor)
    (hY : IsAlgebraicSpace B S hS Y) (hintY : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (hgen : pointsMap B S hS W.subspace.toFunctor (W.subspace.ι ≫ f)
        (_root_.AlgebraicGeometry.Space.genericPoint B S hS W.isClosedSubspace.1
          W.isIntegralSpace) =
      _root_.AlgebraicGeometry.Space.genericPoint B S hS hY hintY)
    (U : ElementaryEtaleNeighborhood B S hS W.subspace.toFunctor W.isClosedSubspace.1
      (Z'.genericPoint B S hS W.subspace.toFunctor))
    [IsAffine U.scheme.left.1] (j : U.scheme ⟶ V.scheme) (hj : j.left.1 U.point = V.point)
    (hsurj : Function.Surjective ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
      j.left.1.stalkMap U.point).hom)
    (hsq : yoneda.map j ≫ V.toSpace = U.toSpace ≫ W.subspace.ι)
    (g : rationalFunctions B S hS hY) :
    ∃ (s t : Γ(V.scheme.left.1, ⊤))
      (e : ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸
          (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
            j.left.1.stalkMap U.point).hom).map
            (stalkToHenselianLocalRing B S hS X hX x hXd V)) ≃+*
        ↥(Z'.genericHenselianLocalRing B S hS W.isClosedSubspace.1
          W.isIntegralSpace.isDecentSpace))
      (hb : e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
            ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom t))) ∈
          (↥(Z'.genericHenselianLocalRing B S hS W.isClosedSubspace.1
            W.isIntegralSpace.isDecentSpace))⁰),
      Z'.rationalFunctionsToGenericTotalFractionRing B S hS W.isClosedSubspace.1
          W.isIntegralSpace.isDecentSpace W.isIntegralSpace hWN
          (rationalFunctionMap B S hS W.isClosedSubspace.1 hY W.isIntegralSpace hintY
            (W.subspace.ι ≫ f) hgen g) =
        IsLocalization.mk' (Z'.genericTotalFractionRing B S hS W.isClosedSubspace.1
            W.isIntegralSpace.isDecentSpace)
          (e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
            ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom s))))
          ⟨_, hb⟩ := by
  let := Z'.isReduced_chart B S hS W.isClosedSubspace.1 W.isIntegralSpace U
  exact Z'.exists_rationalFunctionsToGenericTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat
    B S hS hX hXd V W.isClosedSubspace.1 W.isIntegralSpace hWN hY hintY W.subspace.ι f hf hgen
    U j hj hsurj hsq
    (nonZeroDivisors_le_comap_chartGlobalSectionsRestrict_of_irreducibleComponent B S hS hX hXd
      W hWcomp U.toSpace U.etale_toSpace V.toSpace V.etale_toSpace j hsq) g

/-! ### One numerator and denominator for every component -/

/-- For `f : X ⟶ Y` with `X` and `Y` integral, an étale chart `U` of `X`, a flat chart `V` of `Y`
and a morphism `j : U ⟶ V` over `f`, any pair `s`, `t` of global sections of `𝒪_V` presenting
the reading of `g` on `V` presents, after restriction along `j`, the reading of `g ∘ f` on
`U`. -/
theorem rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_of_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hintX : IsIntegralSpace B S hS X)
    (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y)
    (hgen : pointsMap B S hS X f
        (_root_.AlgebraicGeometry.Space.genericPoint B S hS hX hintX) =
      _root_.AlgebraicGeometry.Space.genericPoint B S hS hY hintY)
    {U V : BigFppfOver B S hS} [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] [IsAffine V.left.1] [IsLocallyNoetherian V.left.1]
    (cU : yoneda.obj U ⟶ X) (hcU : IsEtale B S hS cU) (cV : yoneda.obj V ⟶ Y)
    (hcV : IsFlat B S hS cV) (j : U ⟶ V) (hsq : yoneda.map j ≫ cV = cU ≫ f)
    (hj : (Γ(V.left.1, ⊤))⁰ ≤ ((Γ(U.left.1, ⊤))⁰).comap (chartGlobalSectionsRestrict B S hS j))
    (g : rationalFunctions B S hS hY) (s : Γ(V.left.1, ⊤)) (t : (Γ(V.left.1, ⊤))⁰)
    (ht : (j.left.1.appTop).hom (t : Γ(V.left.1, ⊤)) ∈ (Γ(U.left.1, ⊤))⁰)
    (hst : IsLocalization.mk' (FractionRing Γ(V.left.1, ⊤)) s t =
      rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V cV hcV g) :
    rationalFunctionsToTotalFractionRing B S hS hX U cU hcU
        (rationalFunctionMap B S hS hX hY hintX hintY f hgen g) =
      IsLocalization.mk' (FractionRing Γ(U.left.1, ⊤)) ((j.left.1.appTop).hom s)
        ⟨(j.left.1.appTop).hom (t : Γ(V.left.1, ⊤)), ht⟩ := by
  rw [rationalFunctionsToTotalFractionRing_rationalFunctionMap_of_isFlat B S hS hX hY hintX
    hintY f hgen cU hcU cV hcV j hsq hj g, ← hst]
  simp only [chartFractionMap, IsLocalization.map_mk']
  rfl

/-- Let `X` be a decent algebraic space over `S`, let `V` be an affine, locally Noetherian
elementary étale neighborhood of a point `x` of `X`, let `f : X ⟶ Y` be flat with `Y` integral
and let `g` be a rational function of `Y`. Then there are global sections `s`, `t` of `𝒪_V`, with
`t` a nonzerodivisor, such that for every integral closed subspace `W ⊆ X` whose set of points is
an irreducible component of `|X|`, every prime divisor `Z'` of `W` and every affine elementary
étale neighborhood `U` of its generic point with a morphism `j : U ⟶ V` over the inclusion
carrying the distinguished point to the distinguished point and surjective on Zariski stalks,

  `emb_{W}(g ∘ f|_W) = e [σ_V s] / e [σ_V t]`   in `Q(𝒪^h_{W, ξ'})`,

`σ_V` being the map of Stacks 0EMY on global sections of `V`, `[·]` the class modulo the ideal
generated by the kernel of the stalk map of `j`, and `e` the presentation of that quotient as
`𝒪^h_{W, ξ'}`. -/
theorem exists_sections_forall_rationalFunctionsToGenericTotalFractionRing_eq_mk'_of_isFlat
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXd : IsDecentSpace B S hS X) {x : points B S hS X}
    (V : ElementaryEtaleNeighborhood B S hS X hX x) [IsAffine V.scheme.left.1]
    [IsLocallyNoetherian V.scheme.left.1] (hY : IsAlgebraicSpace B S hS Y)
    (hintY : IsIntegralSpace B S hS Y) (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (g : rationalFunctions B S hS hY) :
    ∃ (s : Γ(V.scheme.left.1, ⊤)) (t : (Γ(V.scheme.left.1, ⊤))⁰),
      ∀ (W : IntegralClosedSubspace B S hS X)
        (_ : subspacePointSet B S hS X W.subspace ∈
          irreducibleComponents (points B S hS X))
        (hWN : HasEtaleLocalProperty B S hS W.subspace.toFunctor
          (fun T : Scheme.{u} => IsLocallyNoetherian T))
        (Z' : PrimeDivisor B S hS W.subspace.toFunctor)
        (hgen : pointsMap B S hS W.subspace.toFunctor (W.subspace.ι ≫ f)
            (_root_.AlgebraicGeometry.Space.genericPoint B S hS W.isClosedSubspace.1
              W.isIntegralSpace) =
          _root_.AlgebraicGeometry.Space.genericPoint B S hS hY hintY)
        (U : ElementaryEtaleNeighborhood B S hS W.subspace.toFunctor W.isClosedSubspace.1
          (Z'.genericPoint B S hS W.subspace.toFunctor))
        (_ : IsAffine U.scheme.left.1) (j : U.scheme ⟶ V.scheme)
        (hj : j.left.1 U.point = V.point)
        (_ : Function.Surjective ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
          j.left.1.stalkMap U.point).hom)
        (_ : yoneda.map j ≫ V.toSpace = U.toSpace ≫ W.subspace.ι),
      ∃ (e : ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸
            (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
              j.left.1.stalkMap U.point).hom).map
              (stalkToHenselianLocalRing B S hS X hX x hXd V)) ≃+*
          ↥(Z'.genericHenselianLocalRing B S hS W.isClosedSubspace.1
            W.isIntegralSpace.isDecentSpace))
        (hb : e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
              ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom
                (t : Γ(V.scheme.left.1, ⊤))))) ∈
            (↥(Z'.genericHenselianLocalRing B S hS W.isClosedSubspace.1
              W.isIntegralSpace.isDecentSpace))⁰),
        Z'.rationalFunctionsToGenericTotalFractionRing B S hS W.isClosedSubspace.1
            W.isIntegralSpace.isDecentSpace W.isIntegralSpace hWN
            (rationalFunctionMap B S hS W.isClosedSubspace.1 hY W.isIntegralSpace hintY
              (W.subspace.ι ≫ f) hgen g) =
          IsLocalization.mk' (Z'.genericTotalFractionRing B S hS W.isClosedSubspace.1
              W.isIntegralSpace.isDecentSpace)
            (e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
              ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom s))))
            ⟨_, hb⟩ := by
  have hcVf : IsFlat B S hS (V.toSpace ≫ f) :=
    isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS V.scheme) hX hY V.toSpace f
      (isFlat_of_isEtale B S hS V.etale_toSpace) hf
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective (Γ(V.scheme.left.1, ⊤))⁰
    (rationalFunctionsToTotalFractionRingOfFlat B S hS hY hintY V.scheme (V.toSpace ≫ f)
      hcVf g)
  refine ⟨s, t, fun W hWcomp hWN Z' hgen U hUaff j hj hsurj hsq => ?_⟩
  let := hUaff
  let := Z'.isReduced_chart B S hS W.isClosedSubspace.1 W.isIntegralSpace U
  let := Z'.isLocallyNoetherian_chart B S hS W.isClosedSubspace.1 hWN U
  have hnzd := nonZeroDivisors_le_comap_chartGlobalSectionsRestrict_of_irreducibleComponent
    B S hS hX hXd W hWcomp U.toSpace U.etale_toSpace V.toSpace V.etale_toSpace j hsq
  exact Z'.rationalFunctionsToGenericTotalFractionRing_eq_mk'_ringEquiv_quotient B S hS hX hXd V
    W.isClosedSubspace.1 W.isIntegralSpace hWN U j hj hsurj s (t : Γ(V.scheme.left.1, ⊤))
    (hnzd t.2) _
    (rationalFunctionsToTotalFractionRing_rationalFunctionMap_eq_mk'_of_isFlat_of_eq B S hS
      W.isClosedSubspace.1 hY W.isIntegralSpace hintY (W.subspace.ι ≫ f) hgen U.toSpace
      U.etale_toSpace (V.toSpace ≫ f) hcVf j
      (by rw [← Category.assoc, hsq, Category.assoc]) hnzd g s t (hnzd t.2) hst)

end AlgebraicGeometry.Space

end
