module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimensionOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Stacks 0EPZ, part (2): the δ-dimension of a component of an effective Cartier divisor

In Situation 0EDT let `X/B` be good and let `X` be integral with `dim_δ(X) = n`.  If `Z` is an
irreducible component of an effective Cartier divisor `D ⊆ X`, then `dim_δ(Z) = n - 1`.

## Main results

* `AlgebraicGeometry.Space.codimension_closureSingleton_eq_one_of_isEffectiveCartierDivisor`:
  an irreducible component of an effective Cartier divisor on a decent, locally Noetherian
  algebraic space has codimension one in the ambient space.  No integrality and no dimension
  function enter; this is Krull's Hauptidealsatz read on an étale chart.
* `AlgebraicGeometry.Space.deltaDimensionIrreducible_closureSingleton_isEffectiveCartierDivisor`:
  **Stacks 0EPZ, part (2)**, at the hypotheses of the source.

## Implementation notes

The component is given by a generic point: an irreducible component `W` of the closed subset
`|D| ⊆ |X|` is the closure of a point `ξ`, and `dim_δ` of the component is
`AlgebraicGeometry.Space.deltaDimensionIrreducible` at the irreducible closed subset
`closure {ξ}` of `|X|`, which is exactly the summand `W` contributes to
`AlgebraicGeometry.Space.deltaDimensionClosed` of `|D|`.

### How part (2) is reduced to part (1)

Part (1) is available as the equivalence
`codimension_closureSingleton_eq_one_iff_dimensionFunction` between `codimension = 1` and the
unit drop of a dimension function, so part (2) is the statement that the component has
codimension one in `|X|`.  That is proved for an arbitrary decent, locally Noetherian algebraic
space, with no reference to `δ`:

* the codimension of `closure {ξ}` is the dimension of the local ring of `X` at `ξ`, by
  Stacks 0ED1, `AlgebraicGeometry.Space.codimension_eq_localRingDimension`;
* that dimension is the Krull dimension of the local ring of any étale scheme chart at any point
  above `ξ`, by Stacks 0BAM, `AlgebraicGeometry.Space.localRingDimension_eq_of_chartPoint`;
* on a chart the divisor is cut out by an effective Cartier ideal sheaf, by Stacks 083C (3),
  `AlgebraicGeometry.Space.hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier`, and the
  local ring of the chart at a generic point of a component of that closed subscheme has Krull
  dimension one, which is Stacks 0BCN (2),
  `AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor`.

### The step the library did not have: transporting the component to the chart

The last item needs its chart point to be a *generic point of a component of the chart
subscheme*, and that is the space-to-chart transport which was missing.  It is supplied here by
two observations, neither of which needs a chart of `D` itself.

*A point with no proper generization is a generic point of a component.* This is
`mem_irreducibleComponents_closure_singleton_of_forall_specializes_eq`, on any quasi-sober
space; on a scheme it turns minimality under generization into the hypothesis of Stacks 0BCN.
The converse direction, which carries a generic point of a chart component *down* to `|X|`, is
`GeneralizingMap.mem_irreducibleComponents_closure_singleton` of
`StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents`; that map is only surjective, not
injective, so it cannot be inverted, and the transport is done here in the other direction, by
minimality rather than by a bijection.

*A chart point above a minimal point of `|D|` is minimal in the chart subscheme.* A proper
generization of the chart point inside the chart subscheme maps to a point of `|D|`
generizing `ξ`, hence to `ξ` itself by maximality of the component
(`eq_of_specializes_val_of_isGenericPoint_mem_irreducibleComponents`); two points of an étale
chart with the same image in `|X|`, one a generization of the other, are equal by Stacks 03K5,
`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers`, which is
where decency is used.

The identification of the chart points lying over `|D|` with the points of the chart subscheme
is `AlgebraicGeometry.Space.subspacePointSet_preimage` together with condition (3) of
Stacks 083C, whose data is an object `R` of the site, a closed immersion `j : R ⟶ U` whose range
is `D ×_X U`, and an isomorphism of the scheme of `R` with the subscheme cut out by the ideal
sheaf; `AlgebraicGeometry.Space.range_pointsMap_ι_range` passes from the range subfunctor to
`j`, and `AlgebraicGeometry.Space.schemePoint_map_yoneda` reads the resulting point on the
scheme.

The scheme-level statement of both parts of Stacks 0EPZ is Stacks 02RK,
`Stacks.Chow.deltaDimension_irreducibleComponent_isEffectiveCartierDivisor`; it is stated for an
integral scheme and so cannot be applied to the chart of a merely good algebraic space, but the
`[IsIntegral]` hypothesis is harmless at the *space* level here, because Stacks 0EPZ itself
assumes `X` integral.  It is nevertheless not what is used: the chart is not integral, and what
the chart supplies is Stacks 0BCN (2) alone.

## References

* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

/-! ### Minimality under generization and the components of a space -/

/-- **A point with no proper generization is a generic point of an irreducible component.**  On a
quasi-sober space, if every point specializing to `ζ` equals `ζ`, then `closure {ζ}` is an
irreducible component.

An irreducible set containing `closure {ζ}` has a generic point `η` for its closure, and `ζ` lies
in that closure, so `η` specializes to `ζ` and is therefore `ζ`; hence the set is contained in
`closure {ζ}`. -/
theorem mem_irreducibleComponents_closure_singleton_of_forall_specializes_eq {α : Type*}
    [TopologicalSpace α] [QuasiSober α] {ζ : α} (hmin : ∀ z : α, z ⤳ ζ → z = ζ) :
    closure ({ζ} : Set α) ∈ irreducibleComponents α := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hsub => ?_⟩
  obtain ⟨η, hη⟩ := QuasiSober.sober hT.closure isClosed_closure
  calc T ⊆ closure T := subset_closure
    _ = closure ({η} : Set α) := hη.def.symm
    _ = closure ({ζ} : Set α) := by
      rw [hmin η (hη.specializes (subset_closure (hsub (subset_closure rfl))))]

/-- **A generic point of an irreducible component of a subset has no proper generization inside
that subset.**  If `W` is an irreducible component of `T ⊆ α` with generic point `ξ`, then every
point of `T` specializing to `ξ` in `α` is `ξ`.

The closure in `T` of such a point is an irreducible subset of `T` containing `W`, hence equals
`W` by maximality; so the point lies in `W` and specializes to `ξ` and conversely, and `T` is
Kolmogorov because `α` is. -/
theorem eq_of_specializes_val_of_isGenericPoint_mem_irreducibleComponents {α : Type*}
    [TopologicalSpace α] [T0Space α] {T : Set α} {W : Set T}
    (hW : W ∈ irreducibleComponents T) {ξ : T} (hξ : IsGenericPoint ξ W) {y : α} (hy : y ∈ T)
    (hspec : y ⤳ (ξ : α)) : y = (ξ : α) := by
  have hspec' : (⟨y, hy⟩ : T) ⤳ ξ :=
    Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
  have hsub : W ⊆ closure ({(⟨y, hy⟩ : T)} : Set T) := by
    rw [← hξ.def]
    exact hspec'.closure_subset
  have hmem : (⟨y, hy⟩ : T) ∈ W :=
    hW.2 isIrreducible_singleton.closure hsub (subset_closure rfl)
  exact congrArg Subtype.val ((hspec'.antisymm (hξ.specializes hmem)).eq)

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The scheme point under a point of a represented presheaf -/

/-- The scheme point underlying the image of a point of a represented presheaf along a morphism
of the site is the image of its scheme point. -/
alias pointsToScheme_pointsMap_yoneda_map := pointsToScheme_pointsMap_yoneda

/-! ### An irreducible component of an effective Cartier divisor has codimension one -/

/-- **An irreducible component of an effective Cartier divisor has codimension one.**  Let `X` be
a decent, locally Noetherian algebraic space over `S`, let `D ⊆ X` be an effective Cartier
divisor, and let `W` be an irreducible component of the closed subset `|D| ⊆ |X|` with generic
point `ξ`.  Then `closure {ξ}` has codimension one in `|X|`.

This is Krull's Hauptidealsatz read on an étale chart.  The codimension is the dimension of the
local ring of `X` at `ξ` (Stacks 0ED1), which is the Krull dimension of the local ring of any
étale scheme chart at any point above `ξ` (Stacks 0BAM).  On a chart `U` the divisor is cut out
by an effective Cartier ideal sheaf `I` (Stacks 083C (3)), and the chart point chosen above `ξ`
is a generic point of an irreducible component of the subscheme cut out by `I`: a proper
generization of it inside that subscheme would map to a point of `|D|` properly generizing `ξ`,
which maximality of `W` forbids, and two points of an étale chart with the same image in `|X|`,
one a generization of the other, are equal by Stacks 03K5.  Stacks 0BCN (2) then gives Krull
dimension one. -/
theorem codimension_closureSingleton_eq_one_of_isEffectiveCartierDivisor (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hdec : IsDecentSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (E : ClosedSubspaces B S hS X.1) (hE : IsEffectiveCartierDivisor B S hS X E)
    {W : Set (subspacePointSet B S hS X.1 E.1)}
    (hW : W ∈ irreducibleComponents (subspacePointSet B S hS X.1 E.1))
    {ξ : subspacePointSet B S hS X.1 E.1} (hξ : IsGenericPoint ξ W) :
    codimension (IrreducibleCloseds.closureSingleton (ξ : points B S hS X.1)) = 1 := by
  have ht0 : T0Space (points B S hS X.1) := t0Space_points_of_isDecentSpace B S hS X.2 hdec
  -- an étale chart of `X` through `ξ`
  obtain ⟨U, g, hg, p, hp⟩ := exists_etale_chart_at_point B S hS X.1 X.2 (ξ : points B S hS X.1)
  have hLN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun Y : Scheme.{u} => IsLocallyNoetherian Y)
      X.2).mp hN U g hg
  -- the divisor is cut out on it by an effective Cartier ideal sheaf
  obtain ⟨I, R, j, e, hI, hmap, hpre⟩ :=
    hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X E hE U g
      (isEtale_of_presheaf_etale B S hS hg)
  have hciR : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := by
    rw [hmap]
    infer_instance
  have hmonoj : Mono j :=
    Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) inferInstance
  have : Mono (yoneda.map j) := Functor.map_mono yoneda j
  -- the chart points lying over `|D|` are the points of the chart subscheme
  have hrange : ∀ v : points B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) g v ∈ subspacePointSet B S hS X.1 E.1 ↔
        v ∈ Set.range (pointsMap B S hS (yoneda.obj R) (yoneda.map j)) := by
    intro v
    have h : v ∈ subspacePointSet B S hS (yoneda.obj U) (E.1.preimage g) ↔
        pointsMap B S hS (yoneda.obj U) g v ∈ subspacePointSet B S hS X.1 E.1 := by
      rw [subspacePointSet_preimage, Set.mem_preimage]
    rw [← h, hpre]
    exact Set.ext_iff.1 (range_pointsMap_ι_range B S hS (yoneda.map j)) v
  -- the chart point above `ξ`, read on the chart subscheme
  obtain ⟨w, hw⟩ := (hrange (p.class B S hS (yoneda.obj U))).1 (by rw [hp]; exact ξ.2)
  obtain ⟨q, rfl⟩ := Quot.exists_rep w
  set qU := FieldValuedPoint.map B S hS (yoneda.obj R) (yoneda.map j) q with hqU
  set yI : I.subscheme := e.hom (schemePoint B S hS R q) with hyI
  have hpointI : I.subschemeι yI = schemePoint B S hS U qU := by
    rw [hyI, show I.subschemeι (e.hom (schemePoint B S hS R q)) =
      (e.hom ≫ I.subschemeι) (schemePoint B S hS R q) from rfl, ← hmap, hqU]
    exact (schemePoint_map_yoneda B S hS j q).symm
  have hvξ : pointsMap B S hS (yoneda.obj U) g (qU.class B S hS (yoneda.obj U)) =
      (ξ : points B S hS X.1) := (congrArg _ hw).trans hp
  have hscheme : pointsToScheme B S hS U (qU.class B S hS (yoneda.obj U)) =
      I.subschemeι yI := by rw [pointsToScheme_class, hpointI]
  -- `yI` has no proper generization inside the chart subscheme
  have hmin : ∀ z : I.subscheme, z ⤳ yI → z = yI := by
    intro z hz
    -- the point of the chart below `z`
    set z' := pointsMap B S hS (yoneda.obj R) (yoneda.map j)
      ((schemePointsHomeomorph B S hS R).symm (e.inv z)) with hz'
    have hz'scheme : pointsToScheme B S hS U z' = I.subschemeι z := by
      rw [hz', pointsToScheme_pointsMap_yoneda_map, ← schemePointsHomeomorph_apply,
        Homeomorph.apply_symm_apply, hmap]
      change I.subschemeι ((e.inv ≫ e.hom) z) = I.subschemeι z
      rw [e.inv_hom_id]
      rfl
    -- it specializes to the chart point above `ξ`, and lies over `|D|`
    have hz'spec : z' ⤳ qU.class B S hS (yoneda.obj U) := by
      refine (schemePointsHomeomorph B S hS U).isEmbedding.isInducing.specializes_iff.1 ?_
      rw [schemePointsHomeomorph_apply, schemePointsHomeomorph_apply, hz'scheme, hscheme]
      exact hz.map I.subschemeι.continuous
    have hz'mem : pointsMap B S hS (yoneda.obj U) g z' ∈ subspacePointSet B S hS X.1 E.1 :=
      (hrange z').2 ⟨_, rfl⟩
    -- so it has the same image as the chart point above `ξ`
    have himage : pointsMap B S hS (yoneda.obj U) g (qU.class B S hS (yoneda.obj U)) =
        pointsMap B S hS (yoneda.obj U) g z' := by
      rw [hvξ]
      refine (eq_of_specializes_val_of_isGenericPoint_mem_irreducibleComponents hW hξ hz'mem
        ?_).symm
      rw [← hvξ]
      exact hz'spec.map (continuous_pointsMap B S hS g)
    have heq : qU.class B S hS (yoneda.obj U) = z' :=
      eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS X.2
        (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) U g hg _ _ himage
        hz'spec
    exact I.subschemeι.isEmbedding.injective (by rw [← hz'scheme, ← hscheme, heq])
  -- Krull's Hauptidealsatz on the chart
  have hdim1 : ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
      (schemePoint B S hS U qU)) = 1 := by
    rw [← hpointI]
    exact _root_.AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor I hI yI
      ⟨⟨_, mem_irreducibleComponents_closure_singleton_of_forall_specializes_eq hmin⟩, rfl⟩
  have hchartdim := localRingDimension_eq_of_chartPoint B S hS X.2 U g hg
    (schemePoint B S hS U qU) (ξ : points B S hS X.1) ⟨qU, rfl, hvξ⟩
  rw [hdim1] at hchartdim
  rw [codimension_eq_localRingDimension B S hS X.2 hdec
    (IrreducibleCloseds.closureSingleton (ξ : points B S hS X.1)) (ξ : points B S hS X.1) rfl]
  exact_mod_cast hchartdim

/-! ### Stacks 0EPZ, part (2) -/

/-- **Stacks 0EPZ, part (2).** In Situation 0EDT let `X/B` be good and assume `X` integral with
`dim_δ(X) = n`.  If `Z` is an irreducible component of an effective Cartier divisor `D ⊆ X`,
then `dim_δ(Z) = n - 1`.

The component is presented by a generic point `ξ` of an irreducible component `W` of the closed
subset `|D| ⊆ |X|`, and `dim_δ(Z)` is the `δ`-dimension of Stacks 0EDX of the irreducible closed
subset `closure {ξ}` of `|X|`, the summand `W` contributes to `dim_δ(D)`.

By part (1) the equality is equivalent to the component having codimension one in `|X|`, which
is `AlgebraicGeometry.Space.codimension_closureSingleton_eq_one_of_isEffectiveCartierDivisor`;
the passage between the two is the topological equivalence
`codimension_closureSingleton_eq_one_iff_dimensionFunction` for the dimension function `δ_{X/B}`
of Stacks 0EDN, which is where integrality of `X` and `dim_δ(X) = n` are used. -/
@[stacks 0EPZ "part (2)"]
theorem deltaDimensionIrreducible_closureSingleton_isEffectiveCartierDivisor
    (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hX.1⟩ E)
    {W : Set (subspacePointSet D.site D.base D.base_mem X E.1)}
    (hW : W ∈ irreducibleComponents (subspacePointSet D.site D.base D.base_mem X E.1))
    {ξ : subspacePointSet D.site D.base D.base_mem X E.1} (hξ : IsGenericPoint ξ W) :
    deltaDimensionIrreducible D sX hX
        (IrreducibleCloseds.closureSingleton (ξ : points D.site D.base D.base_mem X)) =
      n - 1 := by
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  have _ht0 : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)
  have _hirr : IrreducibleSpace (points D.site D.base D.base_mem X) := hint.2.2
  obtain ⟨d, hd⟩ := exists_dimensionFunction_inducedDimensionValue D.site D.base D.base_mem
    D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta hX.1 (isDecentSpace_of_isGood D sX hX) sX
    hX.2.2
  -- the value of `δ` at the generic point of `|X|` is `n`
  have hη : d (genericPoint (points D.site D.base D.base_mem X)) = n := by
    let Tuniv : IrreducibleCloseds (points D.site D.base D.base_mem X) :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    have h2 : deltaDimensionIrreducible D sX hX Tuniv =
        D.deltaValue sX (genericPoint (points D.site D.base D.base_mem X)) :=
      deltaDimensionIrreducible_eq_of_isGenericPoint D sX hX Tuniv
        (genericPoint_spec (points D.site D.base D.base_mem X))
    have h3 : ((D.deltaValue sX (genericPoint (points D.site D.base D.base_mem X)) : ℤ) :
        EInt) = (n : EInt) := by
      rw [← h2, ← deltaDimensionClosed_eq_deltaDimensionIrreducible D sX hX Tuniv]
      exact hn
    rw [hd]
    exact WithBotTop.coe_injective h3
  -- the component has codimension one
  have hcod := codimension_closureSingleton_eq_one_of_isEffectiveCartierDivisor D.site D.base
    D.base_mem ⟨X, hX.1⟩ (isDecentSpace_of_isGood D sX hX)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem
      hX.1 D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian)
    E hE hW hξ
  have hδ := (codimension_closureSingleton_eq_one_iff_dimensionFunction d
    (ξ : points D.site D.base D.base_mem X)).1 hcod
  rw [hη] at hδ
  have hval : deltaDimensionIrreducible D sX hX
      (IrreducibleCloseds.closureSingleton (ξ : points D.site D.base D.base_mem X)) =
      d (ξ : points D.site D.base D.base_mem X) := by
    rw [deltaDimensionIrreducible_eq_of_isGenericPoint D sX hX
      (IrreducibleCloseds.closureSingleton (ξ : points D.site D.base D.base_mem X)) rfl]
    exact (hd _).symm
  exact hval.trans hδ

end AlgebraicGeometry.Space

end
