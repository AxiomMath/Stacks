module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChartStalk

/-!
# The base change of an étale chart to an integral closed subspace, and its local rings

Let `X` be an algebraic space, `V ⊆ X` an integral closed subspace with generic point `η`, `W`
an étale scheme chart of `X` and `π : W ×_X V → W` the projection, a closed immersion of
schemes. For a point `y` of `W ×_X V` over `u ∈ W`, write `A = 𝒪_{W, u}`. Then

* the minimal primes of `𝒪_{W ×_X V, y}` pull back exactly to the primes of `A` whose point of
  `W` lies over `η`;
* the kernel `I_V` of the surjective stalk map `A → 𝒪_{W ×_X V, y}` is the intersection of
  those primes.

So `I_V` is the radical ideal of `A` cutting out the branches of `V` through `u`. These are the
statements `StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChartStalk`
makes for a prime divisor of an integral space; nothing about codimension one is used, and they
are needed here for the irreducible components of an arbitrary space.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.baseChangeChart`: the étale chart `W ×_X V`
  of `V`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.baseChangeChartProj`: the projection
  `W ×_X V → W`.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.range_baseChangeChartProj`: the image of the
  projection is the preimage of `|V|`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.image_comap_minimalPrimes_stalk_baseChangeChart`:
  the minimal primes of `𝒪_{W ×_X V, y}` are the primes of `A` over `η`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.ker_stalkMap_baseChangeChartProj_eq_sInf`:
  `I_V` is the intersection of the primes of `A` over `η`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : IntegralClosedSubspace B S hS X)

/-- **The étale chart `W ×_X V` of an integral closed subspace `V`**, the base change of an
étale chart `W` of `X` along the closed immersion `V → X` (Stacks 03G2, part (4)). -/
abbrev IntegralClosedSubspace.baseChangeChart (W : SmallEtale B S hS X) :
    SmallEtale B S hS V.subspace.toFunctor :=
  (smallBaseChange B S hS (closedSubspaceHom B S hS hX V.subspace V.isClosedSubspace)
    (isClosedImmersion_closedSubspaceHom B S hS hX V.subspace V.isClosedSubspace).rep).obj W

/-- The cartesian square of charts over the inclusion of an integral closed subspace at the base
change of an étale chart `W` of `X`. -/
abbrev IntegralClosedSubspace.baseChangeChartDiagram (W : SmallEtale B S hS X) :
    ChartDiagram B S hS V.subspace.toFunctor X
      (closedSubspaceHom B S hS hX V.subspace V.isClosedSubspace).hom where
  U := V.baseChangeChart B S hS hX W
  V := W
  g := (isClosedImmersion_closedSubspaceHom B S hS hX V.subspace V.isClosedSubspace).rep.snd
    W.obj.hom
  comm := ((isClosedImmersion_closedSubspaceHom B S hS hX V.subspace
    V.isClosedSubspace).rep.isPullback W.obj.hom).w

/-- The projection of schemes `W ×_X V → W`. -/
abbrev IntegralClosedSubspace.baseChangeChartProj (W : SmallEtale B S hS X) :
    chartScheme (V.baseChangeChart B S hS hX W) ⟶ chartScheme W :=
  (BigFppfOver.toScheme B S hS).map (V.baseChangeChartDiagram B S hS hX W).g

/-- **The projection `W ×_X V → W` is a closed immersion of schemes.** -/
theorem IntegralClosedSubspace.isClosedImmersion_baseChangeChartProj (W : SmallEtale B S hS X) :
    _root_.AlgebraicGeometry.IsClosedImmersion (V.baseChangeChartProj B S hS hX W) :=
  (isClosedImmersion_closedSubspaceHom B S hS hX V.subspace V.isClosedSubspace).property_snd
    W.obj.hom

/-- The projection `W ×_X V → W` is compatible with the maps to `|X|`. -/
theorem IntegralClosedSubspace.chartSchemeToPoints_baseChangeChartProj (W : SmallEtale B S hS X)
    (y : chartScheme (V.baseChangeChart B S hS hX W)) :
    chartSchemeToPoints B S hS X W (V.baseChangeChartProj B S hS hX W y) =
      pointsMap B S hS V.subspace.toFunctor V.subspace.ι
        (chartSchemeToPoints B S hS V.subspace.toFunctor (V.baseChangeChart B S hS hX W) y) :=
  chartSchemeToPoints_map_chartDiagram B S hS (V.baseChangeChartDiagram B S hS hX W) y

/-- **A point of the chart over a point of `V` lifts to `W ×_X V`** (Stacks 03H4). -/
theorem IntegralClosedSubspace.exists_baseChangeChartProj_eq (W : SmallEtale B S hS X)
    (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X W u ∈ subspacePointSet B S hS X V.subspace) :
    ∃ y : chartScheme (V.baseChangeChart B S hS hX W),
      V.baseChangeChartProj B S hS hX W y = u := by
  obtain ⟨a, ha⟩ := hu
  set b := (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj W)).symm u with hb
  have hab : pointsMap B S hS V.subspace.toFunctor
        (closedSubspaceHom B S hS hX V.subspace V.isClosedSubspace).hom a =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.obj.hom b :=
    ha.trans (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X W u)
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    ((isClosedImmersion_closedSubspaceHom B S hS hX V.subspace
      V.isClosedSubspace).rep.isPullback W.obj.hom) a b hab
  refine ⟨pointsToScheme B S hS _ w, ?_⟩
  refine (pointsToScheme_pointsMap_yoneda B S hS
    ((isClosedImmersion_closedSubspaceHom B S hS hX V.subspace V.isClosedSubspace).rep.snd
      W.obj.hom) w).symm.trans ?_
  rw [hw, hb]
  exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj W)).apply_symm_apply u

/-- **The image of `W ×_X V → W` is the preimage of `|V|`.** -/
theorem IntegralClosedSubspace.range_baseChangeChartProj (W : SmallEtale B S hS X) :
    Set.range (V.baseChangeChartProj B S hS hX W) =
      chartSchemeToPoints B S hS X W ⁻¹' subspacePointSet B S hS X V.subspace := by
  ext u
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage, V.chartSchemeToPoints_baseChangeChartProj B S hS hX W y]
    exact ⟨_, rfl⟩
  · exact V.exists_baseChangeChartProj_eq B S hS hX W u

/-- **The scheme of `W ×_X V` is reduced**, `V` being an integral algebraic space. -/
theorem IntegralClosedSubspace.isReduced_chartScheme_baseChangeChart (W : SmallEtale B S hS X) :
    IsReduced (chartScheme (V.baseChangeChart B S hS hX W)) :=
  isReduced_chartScheme_of_isIntegralSpace V.isClosedSubspace.1 V.isIntegralSpace _

/-- **A point of `W ×_X V` has coheight zero exactly when it lies over the generic point of
`|V|`.** -/
theorem IntegralClosedSubspace.coheight_eq_zero_iff_baseChangeChart (W : SmallEtale B S hS X)
    (y : chartScheme (V.baseChangeChart B S hS hX W)) :
    Order.coheight y = 0 ↔
      chartSchemeToPoints B S hS V.subspace.toFunctor (V.baseChangeChart B S hS hX W) y =
        V.genericPoint B S hS := by
  have : QuasiSober (points B S hS V.subspace.toFunctor) := V.quasiSober_points B S hS
  have : IrreducibleSpace (points B S hS V.subspace.toFunctor) := V.irreducibleSpace_points B S hS
  have : T0Space (points B S hS V.subspace.toFunctor) := V.t0Space_points B S hS
  rw [coheight_eq_codimension_chartSchemeToPoints B S hS V.isClosedSubspace.1
    V.isIntegralSpace.2.1]
  exact codimension_closureSingleton_eq_zero_iff _

/-- **The pullbacks of the minimal primes of the local ring of `W ×_X V` are the primes of
`A = 𝒪_{W, u}` over the generic point of `V`.** -/
theorem IntegralClosedSubspace.image_comap_minimalPrimes_stalk_baseChangeChart
    (W : SmallEtale B S hS X) (y : chartScheme (V.baseChangeChart B S hS hX W)) :
    Ideal.comap ((V.baseChangeChartProj B S hS hX W).stalkMap y).hom ''
        minimalPrimes ((chartScheme (V.baseChangeChart B S hS hX W)).presheaf.stalk y) =
      {𝔮 : Ideal ((chartScheme W).presheaf.stalk (V.baseChangeChartProj B S hS hX W y)) |
        ∃ h : 𝔮.IsPrime, chartSchemeToPoints B S hS X W
          ((chartScheme W).fromSpecStalk (V.baseChangeChartProj B S hS hX W y) ⟨𝔮, h⟩) =
            V.ambientGenericPoint B S hS} := by
  have := V.isClosedImmersion_baseChangeChartProj B S hS hX W
  set π := V.baseChangeChartProj B S hS hX W with hπ
  ext 𝔮
  constructor
  · rintro ⟨𝔭, h𝔭, rfl⟩
    have : 𝔭.IsPrime := h𝔭.1.1
    refine ⟨Ideal.comap_isPrime _ _, ?_⟩
    have hcoh : Order.coheight
        ((chartScheme (V.baseChangeChart B S hS hX W)).fromSpecStalk y ⟨𝔭, inferInstance⟩) =
          0 :=
      (Stacks.Chow.coheight_fromSpecStalk_eq_height y _).trans
        (Ideal.height_eq_zero_iff.mpr h𝔭)
    have hpt := Scheme.Hom.fromSpecStalk_comap_stalkMap π y ⟨𝔭, inferInstance⟩
    refine (congrArg (chartSchemeToPoints B S hS X W) hpt).trans ?_
    rw [V.chartSchemeToPoints_baseChangeChartProj B S hS hX W,
      (V.coheight_eq_zero_iff_baseChangeChart B S hS hX W _).mp hcoh]
    rfl
  · rintro ⟨h𝔮, hq⟩
    set q := (chartScheme W).fromSpecStalk (π y) ⟨𝔮, h𝔮⟩ with hqdef
    have hqV : chartSchemeToPoints B S hS X W q ∈ subspacePointSet B S hS X V.subspace :=
      hq ▸ (V.isGenericPoint_ambientGenericPoint B S hS hX).mem
    obtain ⟨y', hy'⟩ := V.exists_baseChangeChartProj_eq B S hS hX W q hqV
    have hy'y : y' ⤳ y := by
      rw [← π.isClosedEmbedding.isInducing.specializes_iff, hy']
      exact Stacks.Chow.specializes_fromSpecStalk (π y) ⟨𝔮, h𝔮⟩
    obtain ⟨P, hP⟩ := Stacks.Chow.exists_fromSpecStalk_eq hy'y
    have himg : chartSchemeToPoints B S hS V.subspace.toFunctor
        (V.baseChangeChart B S hS hX W) y' = V.genericPoint B S hS := by
      refine (V.isClosedEmbedding_pointsMap B S hS hX).injective ?_
      rw [← V.chartSchemeToPoints_baseChangeChartProj B S hS hX W, hy', hq]
      rfl
    have hcoh0 : Order.coheight y' = 0 :=
      (V.coheight_eq_zero_iff_baseChangeChart B S hS hX W y').mpr himg
    have hmin : P.asIdeal ∈ minimalPrimes
        ((chartScheme (V.baseChangeChart B S hS hX W)).presheaf.stalk y) := by
      have := P.isPrime
      refine Ideal.height_eq_zero_iff.mp ?_
      exact (Stacks.Chow.coheight_fromSpecStalk_eq_height y P).symm.trans (hP ▸ hcoh0)
    refine ⟨P.asIdeal, hmin, ?_⟩
    have heq : (chartScheme W).fromSpecStalk (π y) (PrimeSpectrum.comap (π.stalkMap y).hom P) =
        (chartScheme W).fromSpecStalk (π y) ⟨𝔮, h𝔮⟩ :=
      (Scheme.Hom.fromSpecStalk_comap_stalkMap π y P).trans (by rw [hP, hy'])
    exact congrArg PrimeSpectrum.asIdeal
      (((chartScheme W).fromSpecStalk (π y)).isEmbedding.injective heq)

/-- The minimal primes of `I_V` are the primes of `A` over the generic point of `V`. -/
private theorem IntegralClosedSubspace.minimalPrimes_ker_eq_primes_over
    (W : SmallEtale B S hS X) (y : chartScheme (V.baseChangeChart B S hS hX W)) :
    (RingHom.ker ((V.baseChangeChartProj B S hS hX W).stalkMap y).hom).minimalPrimes =
      {𝔮 : Ideal ((chartScheme W).presheaf.stalk (V.baseChangeChartProj B S hS hX W y)) |
        ∃ h : 𝔮.IsPrime, chartSchemeToPoints B S hS X W
          ((chartScheme W).fromSpecStalk (V.baseChangeChartProj B S hS hX W y) ⟨𝔮, h⟩) =
            V.ambientGenericPoint B S hS} := by
  have := V.isClosedImmersion_baseChangeChartProj B S hS hX W
  rw [← V.image_comap_minimalPrimes_stalk_baseChangeChart B S hS hX W y,
    ← Ideal.comap_minimalPrimes_eq_of_surjective
      ((V.baseChangeChartProj B S hS hX W).stalkMap_surjective y),
    ← RingHom.ker_eq_comap_bot]

/-- **The kernel `I_V` of the stalk map `A → 𝒪_{W ×_X V, y}` is the intersection of the primes
of `A` over the generic point of `V`.** -/
theorem IntegralClosedSubspace.ker_stalkMap_baseChangeChartProj_eq_sInf (W : SmallEtale B S hS X)
    (y : chartScheme (V.baseChangeChart B S hS hX W)) :
    RingHom.ker ((V.baseChangeChartProj B S hS hX W).stalkMap y).hom =
      sInf {𝔮 : Ideal ((chartScheme W).presheaf.stalk (V.baseChangeChartProj B S hS hX W y)) |
        ∃ h : 𝔮.IsPrime, chartSchemeToPoints B S hS X W
          ((chartScheme W).fromSpecStalk (V.baseChangeChartProj B S hS hX W y) ⟨𝔮, h⟩) =
            V.ambientGenericPoint B S hS} := by
  have := V.isClosedImmersion_baseChangeChartProj B S hS hX W
  have := V.isReduced_chartScheme_baseChangeChart B S hS hX W
  rw [← V.minimalPrimes_ker_eq_primes_over B S hS hX W y, Ideal.sInf_minimalPrimes,
    (Scheme.Hom.isRadical_ker_stalkMap_of_isClosedImmersion _ y).radical]

/-- **The kernel `I_V` is radical**, the scheme `W ×_X V` being reduced. -/
theorem IntegralClosedSubspace.isRadical_ker_stalkMap_baseChangeChartProj
    (W : SmallEtale B S hS X) (y : chartScheme (V.baseChangeChart B S hS hX W)) :
    (RingHom.ker ((V.baseChangeChartProj B S hS hX W).stalkMap y).hom).IsRadical := by
  have := V.isClosedImmersion_baseChangeChartProj B S hS hX W
  have := V.isReduced_chartScheme_baseChangeChart B S hS hX W
  exact Scheme.Hom.isRadical_ker_stalkMap_of_isClosedImmersion _ y

/-- **The minimal primes of `I_V` are the primes of `A` over the generic point of `V`.** -/
theorem IntegralClosedSubspace.minimalPrimes_ker_stalkMap_baseChangeChartProj
    (W : SmallEtale B S hS X) (y : chartScheme (V.baseChangeChart B S hS hX W)) :
    (RingHom.ker ((V.baseChangeChartProj B S hS hX W).stalkMap y).hom).minimalPrimes =
      {𝔮 : Ideal ((chartScheme W).presheaf.stalk (V.baseChangeChartProj B S hS hX W y)) |
        ∃ h : 𝔮.IsPrime, chartSchemeToPoints B S hS X W
          ((chartScheme W).fromSpecStalk (V.baseChangeChartProj B S hS hX W y) ⟨𝔮, h⟩) =
            V.ambientGenericPoint B S hS} := by
  exact V.minimalPrimes_ker_eq_primes_over B S hS hX W y

end AlgebraicGeometry.Space

end
