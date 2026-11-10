module

public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedGlobalFunctionsIntegral

/-!
# Global functions of a reduced space dominating an integral base are torsion free

Let `p : W ⟶ V` be a morphism from a reduced algebraic space to an integral scheme `V` of the
site, and assume that every generic point of every étale scheme chart of `W` lies over the
generic point of `V`.  Then the global functions of `W` form a torsion free module over the
global functions of `V`: a nonzero function `a` on `V` pulls back to a nonzerodivisor.

This is the torsion-freeness step of the proof of Stacks 0AYI, conclusion (1): there `V` is a
normal integral affine étale chart of `Y`, `W = X ×_Y V`, and torsion-freeness is what makes
`Γ(W, 𝒪) ⟶ K ⊗_A Γ(W, 𝒪)` injective for `K` the function field of `V`.  The source phrases it
as "every generic point of an irreducible component of `|Y'|` maps to `ξ`"; on the side of
global functions the content is the statement here.

The argument is on one reduced étale chart `U` of `W` to which restriction of global functions
is injective.  The pullback of `a` to `U` is invertible on the preimage of the basic open of
`a`, which contains every generic point of `U`, hence is dense; a function on `U` killed by the
pullback of `a` vanishes on that dense open, so its basic open is empty and, `U` being reduced,
it is zero.

## Main results

* `AlgebraicGeometry.Scheme.eq_zero_of_appTop_mul_eq_zero`: the scheme statement.
* `AlgebraicGeometry.Space.eq_zero_of_mul_eq_zero_of_forall_genericPoints`: the statement for
  algebraic spaces.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **On a reduced scheme dominating an integral scheme, a nonzero function of the base pulls
back to a nonzerodivisor.**  Let `g : U ⟶ V` with `U` reduced and `V` integral, every generic
point of an irreducible component of `U` mapping to the generic point of `V`.  If `a ≠ 0` on `V`
and `g^* a · t = 0` on `U`, then `t = 0`: the basic open of `t` is disjoint from that of
`g^* a`, which contains every generic point of `U`, and a nonempty open of `U` contains a
generic point. -/
theorem Scheme.eq_zero_of_appTop_mul_eq_zero {U V : Scheme.{u}} [IsReduced U] [IsIntegral V]
    (g : U ⟶ V) (hg : ∀ u ∈ genericPoints U, g u = genericPoint V) {a : Γ(V, ⊤)} (ha : a ≠ 0)
    {t : Γ(U, ⊤)} (h : g.appTop a * t = 0) : t = 0 := by
  refine eq_zero_of_basicOpen_eq_bot t ?_
  by_contra hne
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({x} : Set U) isIrreducible_singleton
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgenZ : IsGenericPoint hZ.1.genericPoint Z := by
    simpa only [hZcl.closure_eq] using hZ.1.isGenericPoint_genericPoint_closure
  have hz : hZ.1.genericPoint ∈ genericPoints U := by
    change closure {hZ.1.genericPoint} ∈ irreducibleComponents U
    rwa [hgenZ.def]
  have hzt : hZ.1.genericPoint ∈ U.basicOpen t :=
    (hgenZ.specializes (hxZ rfl)).mem_open (U.basicOpen t).isOpen hx
  have hVa : V.basicOpen a ≠ ⊥ := fun h0 => ha (eq_zero_of_basicOpen_eq_bot a h0)
  have hηa : genericPoint V ∈ V.basicOpen a := by
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hVa
    exact ((genericPoint_spec V).mem_open_set_iff (V.basicOpen a).isOpen).2
      ⟨y, Set.mem_univ y, hy⟩
  have hza : hZ.1.genericPoint ∈ U.basicOpen (g.appTop a) := by
    rw [← Scheme.preimage_basicOpen_top]
    change g hZ.1.genericPoint ∈ V.basicOpen a
    rwa [hg _ hz]
  have hmem : hZ.1.genericPoint ∈ U.basicOpen (g.appTop a * t) := by
    rw [Scheme.basicOpen_mul]
    exact ⟨hza, hzt⟩
  rwa [h, Scheme.basicOpen_zero] at hmem

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The global functions of a reduced algebraic space dominating an integral scheme are
torsion free.**  Let `p : W ⟶ V` be a morphism from a reduced algebraic space to an integral
scheme `V` of the site such that every generic point of every étale scheme chart of `W` maps to
the generic point of `V`, and let `ψ : Γ(V, 𝒪_V) ⟶ Γ(W, 𝒪_W)` be pullback of functions along
`p` on every étale chart.  If `a ≠ 0` and `ψ a · s = 0` then `s = 0`.

Restriction of global functions to a reduced étale chart `U` of `W` is injective
(`AlgebraicGeometry.Space.exists_isReduced_chart_injective_globalFunctions`), and on `U` the
statement is `AlgebraicGeometry.Scheme.eq_zero_of_appTop_mul_eq_zero`. -/
theorem eq_zero_of_mul_eq_zero_of_forall_genericPoints {W : AlgebraicSpaces B S hS}
    {V : BigFppfOver B S hS} [IsIntegral ((BigFppfOver.toScheme B S hS).obj V)]
    (p : W.obj ⟶ yoneda.obj V)
    (hred : HasEtaleLocalProperty B S hS W.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (hgen : ∀ c : SmallEtale B S hS W.obj,
      ∀ u ∈ genericPoints
          ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.obj).obj c)),
        (BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c) u =
          genericPoint ((BigFppfOver.toScheme B S hS).obj V))
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* globalFunctions B S hS W.obj)
    (hψ : ∀ c : SmallEtale B S hS W.obj,
      (globalFunctionsChartRestriction B S hS W c).comp ψ =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c)).appTop.hom)
    {a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)} (ha : a ≠ 0)
    {s : globalFunctions B S hS W.obj} (h : ψ a * s = 0) : s = 0 := by
  obtain ⟨c, hcred, hinj⟩ :=
    exists_isReduced_chart_injective_globalFunctions B S hS W.obj W.property hred
  have hr : globalFunctionsChartRestriction B S hS W c (ψ a * s) = 0 := by
    rw [h, map_zero]
  rw [map_mul, ← RingHom.comp_apply, hψ c] at hr
  exact hinj (Scheme.eq_zero_of_appTop_mul_eq_zero _ (hgen c) ha hr)

/-! ### The base change of `f` along a chart of an integral base -/

attribute [local instance] pointTopology

variable {X Y : AlgebraicSpaces B S hS}

/-- **The generic points of the charts of `X ×_Y V` lie over the generic point of `V`.**  Let
`f : X ⟶ Y` with `X` decent and `Y` integral with generic point `ξ`, such that every generic
point of an irreducible component of `|X|` maps to `ξ`, and let `V` be an étale scheme chart of
`Y` which is an integral scheme.  Then every generic point of an étale scheme chart of
`X ×_Y V` maps to the generic point of `V`.

A generic point `u` of such a chart gives a point of `X ×_Y V` whose local ring has dimension
zero (Stacks 0BAQ), hence so does its image in `X` (Stacks 0A4H, `X ×_Y V ⟶ X` being étale);
on the decent space `X` this image admits no proper generization, so it is a generic point of
an irreducible component and maps to `ξ`.  The image `v` of `u` in `V` maps to `ξ` as well, and
`ξ` has a local ring of dimension zero, so `v` is a generic point of the étale chart `V`
(Stacks 0BAQ, condition (3)), which is the generic point of the integral scheme `V`. -/
theorem chartBaseChange_map_genericPoint_eq (f : X ⟶ Y) (hXdec : IsDecentSpace B S hS X.1)
    (hYint : IsIntegralSpace B S hS Y.1) {ξ : points B S hS Y.1}
    (hξ : IsGenericPoint ξ Set.univ)
    (h5 : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (V : SmallEtale B S hS Y.1)
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))]
    (c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj)
    (u : (BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (chartBaseChangeSpace B S hS f V).obj).obj c))
    (hu : u ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (chartBaseChangeSpace B S hS f V).obj).obj c))) :
    (BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS
        (chartBaseChangeProjection B S hS f V).hom c) u =
      genericPoint ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) := by
  classical
  have hYdec : IsDecentSpace B S hS Y.1 := IsIntegralSpace.isDecentSpace B S hS Y.1 hYint
  have : IrreducibleSpace (points B S hS Y.1) := IsIntegralSpace.irreducibleSpace B S hS Y.1 hYint
  obtain ⟨w0, rfl⟩ : ∃ w0 : points B S hS (yoneda.obj c.obj.left),
      pointsToScheme B S hS c.obj.left w0 = u :=
    ⟨(schemePointsHomeomorph B S hS c.obj.left).symm u, by
      rw [← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]⟩
  have hcet : IsEtale B S hS c.obj.hom := (isEtale_iff_presheaf_of_yoneda B S hS _).2 c.property
  have hw : localRingDimension B S hS
      (pointsMap B S hS _ c.obj.hom w0) = 0 := by
    refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS
      (chartBaseChangeSpace B S hS f V).property _).2 ⟨c.obj.left, c.obj.hom, _, hcet,
        chartPoint_pointsToScheme B S hS c.obj.left c.obj.hom w0, hu⟩
  have hx : localRingDimension B S hS (pointsMap B S hS _
      (chartBaseChangeInclusion B S hS f V).hom (pointsMap B S hS _ c.obj.hom w0)) = 0 := by
    rwa [localRingDimension_pointsMap_of_etale B S hS (chartBaseChangeSpace B S hS f V).property
      X.property _ (isEtale_chartBaseChangeInclusion B S hS f V)]
  have hxgen : pointsMap B S hS _ (chartBaseChangeInclusion B S hS f V).hom
      (pointsMap B S hS _ c.obj.hom w0) ∈ genericPoints (points B S hS X.1) := by
    obtain ⟨x₀, hx₀, hx₀x⟩ := exists_mem_genericPoints_specializes B S hS X.2 hXdec
      (pointsMap B S hS _ (chartBaseChangeInclusion B S hS f V).hom
        (pointsMap B S hS _ c.obj.hom w0))
    rwa [eq_of_specializes_of_localRingDimension_eq_zero B S hS X.2 hXdec hx x₀ hx₀x] at hx₀
  have hv0 : pointsMap B S hS _ V.obj.hom (pointsMap B S hS _ (yoneda.map
      (smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS f V).hom c)) w0) =
      ξ := by
    rw [← h5 _ hxgen, ← pointsMap_comp_apply, ← pointsMap_comp_apply, ← pointsMap_comp_apply]
    refine congrArg (fun φ => pointsMap B S hS _ φ w0) ?_
    calc _ = (c.obj.hom ≫ (chartBaseChangeProjection B S hS f V).hom) ≫ V.obj.hom :=
          congrArg (· ≫ V.obj.hom) (yoneda_map_smallEtaleChartMapToBase B S hS
            (chartBaseChangeProjection B S hS f V).hom c)
      _ = c.obj.hom ≫ ((chartBaseChangeProjection B S hS f V).hom ≫ V.obj.hom) :=
          Category.assoc _ _ _
      _ = _ := congrArg (c.obj.hom ≫ ·) (isPullback_chartBaseChangeProjection B S hS f V).w
  have hξgen : ξ ∈ genericPoints (points B S hS Y.1) := by
    change closure {ξ} ∈ irreducibleComponents (points B S hS Y.1)
    rwa [irreducibleComponents_eq_singleton]
  have hξdim := localRingDimension_eq_zero_of_mem_genericPoints B S hS Y.2 hYdec hξgen
  have hch := chartPoint_pointsToScheme B S hS V.obj.left V.obj.hom
    (pointsMap B S hS _ (yoneda.map
      (smallEtaleChartMapToBase B S hS (chartBaseChangeProjection B S hS f V).hom c)) w0)
  rw [hv0] at hch
  have hgenv := (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS Y.2 ξ).1 hξdim
    V.obj.left V.obj.hom _ ((isEtale_iff_presheaf_of_yoneda B S hS _).2 V.property) hch
  rw [pointsToScheme_pointsMap_yoneda] at hgenv
  have hcl : closure {(BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS
      (chartBaseChangeProjection B S hS f V).hom c) (pointsToScheme B S hS c.obj.left w0)} ∈
        irreducibleComponents
          ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) := hgenv
  rw [irreducibleComponents_eq_singleton] at hcl
  exact IsGenericPoint.eq hcl (genericPoint_spec
    ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)))

/-- **Stacks 0AYI, the torsion-freeness step.**  Let `f : X ⟶ Y` with `X` decent and reduced
and `Y` integral with generic point `ξ`, every generic point of an irreducible component of
`|X|` mapping to `ξ`, and let `V` be an étale scheme chart of `Y` which is an integral scheme.
Then the global functions of `X ×_Y V` are torsion free over those of `V`: if `a ≠ 0` and
`ψ a · s = 0` then `s = 0`, for `ψ` pullback of functions along the projection.

`X ×_Y V` is reduced, being étale over `X`, and the generic points of its charts lie over the
generic point of `V` by `AlgebraicGeometry.Space.chartBaseChange_map_genericPoint_eq`, so this
is `AlgebraicGeometry.Space.eq_zero_of_mul_eq_zero_of_forall_genericPoints`. -/
theorem eq_zero_of_mul_eq_zero_chartBaseChange (f : X ⟶ Y) (hXdec : IsDecentSpace B S hS X.1)
    (hXred : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (hYint : IsIntegralSpace B S hS Y.1) {ξ : points B S hS Y.1}
    (hξ : IsGenericPoint ξ Set.univ)
    (h5 : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (V : SmallEtale B S hS Y.1)
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))]
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤) →+*
      globalFunctions B S hS (chartBaseChangeSpace B S hS f V).obj)
    (hψ : ∀ c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj,
      (globalFunctionsChartRestriction B S hS _ c).comp ψ =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS
          (chartBaseChangeProjection B S hS f V).hom c)).appTop.hom)
    {a : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)}
    (ha : a ≠ 0) {s : globalFunctions B S hS (chartBaseChangeSpace B S hS f V).obj}
    (h : ψ a * s = 0) : s = 0 := by
  have hWred : HasEtaleLocalProperty B S hS (chartBaseChangeSpace B S hS f V).obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T) := by
    refine (exists_atlas_iff_forall_etale B S hS _ _ (chartBaseChangeSpace B S hS f V).property).2
      fun U g hg => ?_
    refine (exists_atlas_iff_forall_etale B S hS _ _ X.property).1 hXred U
      (g ≫ (chartBaseChangeInclusion B S hS f V).hom) ?_
    exact (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS g).2 hg)
        (isEtale_chartBaseChangeInclusion B S hS f V))
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.inclusion B S hS Y.obj).obj V).left) :=
    ‹IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))›
  exact eq_zero_of_mul_eq_zero_of_forall_genericPoints B S hS
    (chartBaseChangeProjection B S hS f V).hom hWred
    (chartBaseChange_map_genericPoint_eq B S hS f hXdec hYint hξ h5 V) ψ hψ ha h

end Space

end AlgebraicGeometry

end
