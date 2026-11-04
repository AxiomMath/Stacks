module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentZeroCycleChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ModulePullbackEvaluationIdealTrivialChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart of `Z(s|_W)` as a closed subscheme of the chart of `X`

Let `X/B` be a good algebraic space over a scheme `S` contained in a big fppf site `B`, let `ℒ`
be an invertible `𝒪_X`-module with a global section `s`, let `W ⊆ X` be an integral closed
subspace and let `V` be an affine étale scheme chart of `X`.  The zero scheme `Z(s|_W)` of
Stacks 0845 on `W` has an étale chart obtained by base changing `V` twice,
`(V ×_X W) ×_W Z(s|_W)`, and the composite of the two base-change projections presents it as a
closed subscheme of `V`
(`AlgebraicGeometry.Space.componentVanishingLocusChartImmersion`).

When `V` trivialises `ℒ`, in the sense of carrying a compatible family of free generators of `ℒ`
over the charts above it, the kernel of that composite is the sum of the ideal sheaf of `V ×_X W`
and the ideal sheaf induced by the evaluation ideal of `s` at `V`. Equivalently, the chart of
`Z(s|_W)` is cut out of the chart of `X` by the equations of `W` together with the equations of
`Z(s)`, which is the compatibility of Stacks 0845 with base change along `W → X` read on the chart.

## Main results

* `AlgebraicGeometry.Space.ker_componentVanishingLocusChartImmersion`: **the chart of `Z(s|_W)` is
  cut out of the chart of `X` by the ideal sheaf of `V ×_X W` together with the evaluation ideal
  of `s`.**
* `AlgebraicGeometry.Space.cycleAssociatedToClosedSubscheme_componentVanishingLocusChartImmersion`:
  the same identity read on the cycles of Stacks 02QU.
* `AlgebraicGeometry.Space.schemeDeltaDimension_id_chartChowSituation_le`: the δ-dimension bound
  `dim_δ(X) ≤ k` of Situation 0EDT, transported to the δ-dimension of Stacks 02QS of the chart
  scheme over the situation on the chart.
* `cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart_of_trivialisingChart`: the local
  identity of Stacks 0EQL at a point of a surjective affine étale chart trivialising `ℒ`, given the
  local data of Stacks 0EPI at that point.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

/-- The ideal sheaf induced on an affine scheme by a sum of two ideals of global sections is the
sum of the two induced ideal sheaves. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_sup {Y : Scheme.{u}} [IsAffine Y]
    (I J : Ideal Γ(Y, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J :=
  Scheme.IdealSheafData.ext_of_isAffine (by
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.IdealSheafData.ideal_sup,
      Ideal.map_sup, Pi.sup_apply])

/-- If the kernel of a morphism `p` to an affine scheme is the ideal sheaf induced by an ideal `I`
of global sections, then the kernel of `p` on global sections is `I`. -/
theorem AlgebraicGeometry.Scheme.ker_appTop_of_ker_eq_ofIdealTop {T M : Scheme.{u}} [IsAffine M]
    (p : T ⟶ M) (I : Ideal Γ(M, ⊤)) (h : p.ker = Scheme.IdealSheafData.ofIdealTop I) :
    RingHom.ker (Scheme.Hom.appTop p).hom = I := by
  rw [Scheme.ker_of_isAffine p] at h
  simpa using congrArg
    (fun K : Scheme.IdealSheafData M => K.ideal ⟨⊤, isAffineOpen_top M⟩) h

/-- **The kernel of a composite of closed immersions into an affine scheme.**  Let
`p₂ : T ⟶ M` and `p₁ : M ⟶ Y` be morphisms of schemes with `Y` and `M` affine and `p₁` a closed
immersion, and let `E` be an ideal of `Γ(Y, ⊤)` whose extension along `p₁` is the kernel of `p₂`
on global sections.  Then the kernel of `p₂ ≫ p₁` is the kernel of `p₁` together with the ideal
sheaf induced by `E`. -/
theorem AlgebraicGeometry.Scheme.ker_comp_eq_sup_ofIdealTop {T M Y : Scheme.{u}}
    (p₂ : T ⟶ M) (p₁ : M ⟶ Y) [IsAffine Y] [IsAffine M] [IsClosedImmersion p₁]
    (E : Ideal Γ(Y, ⊤))
    (h : RingHom.ker (Scheme.Hom.appTop p₂).hom =
      Ideal.map (Scheme.Hom.appTop p₁).hom E) :
    (p₂ ≫ p₁).ker = p₁.ker ⊔ Scheme.IdealSheafData.ofIdealTop E := by
  have hsurj : Function.Surjective (Scheme.Hom.appTop p₁).hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine p₁).2
  rw [Scheme.ker_of_isAffine (p₂ ≫ p₁), Scheme.ker_of_isAffine p₁,
    show (Scheme.Hom.appTop (p₂ ≫ p₁)).hom =
      RingHom.comp (Scheme.Hom.appTop p₂).hom (Scheme.Hom.appTop p₁).hom from rfl,
    ← RingHom.comap_ker, h, Ideal.comap_map_of_surjective _ hsurj,
    ← RingHom.ker_eq_comap_bot, sup_comm, Scheme.IdealSheafData.ofIdealTop_sup]

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections)

/-- **The chart of `Z(s|_W)` is cut out of the chart of `X` by the equations of `W` and the
equations of `Z(s)`.**  Let `X/B` be a good algebraic space, let `ℒ` be an invertible
`𝒪_X`-module with a global section `s`, let `W ⊆ X` be an integral closed subspace and let `V` be
an affine étale scheme chart of `X` trivialising `ℒ`, in the sense of carrying a compatible family
`e` of free generators of `ℒ` over the charts above it.  Then the kernel of the closed immersion
`(V ×_X W) ×_W Z(s|_W) ⟶ V` is the sum of the kernel of `V ×_X W ⟶ V` and the ideal sheaf
induced by the evaluation ideal of `s` at `V`.

This is the compatibility of the zero scheme of Stacks 0845 with base change along the closed
immersion `W → X`, read on the chart `V` and on ideal sheaves. -/
@[sga "6 XIII 7.5" "partial"]
theorem ker_componentVanishingLocusChartImmersion
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings D.site D.base D.base_mem ⟨X, hX.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨X, hX.1⟩).property L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) [IsAffine (chartScheme V)]
    (e : (T : SmallEtale D.site D.base D.base_mem X) → (T ⟶ V) → L.val.obj (op T))
    (hcompat : ∀ (T T' : SmallEtale D.site D.base D.base_mem X) (j : T ⟶ V) (g : T' ⟶ T),
      (L.val.map g.op).hom (e T j) = e T' (g ≫ j))
    (hfree : ∀ (T : SmallEtale D.site D.base D.base_mem X) (j : T ⟶ V),
      Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 T ↦ r • e T j) :
    (componentVanishingLocusChartImmersion D sX hX L s W V).ker =
      (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
          W.isClosedSubspace V).ker ⊔
        Scheme.IdealSheafData.ofIdealTop
          (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V) := by
  have hci₁ := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    hX.1 W.subspace W.isClosedSubspace V
  have hMaff : IsAffine (chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem
      hX.1 W.subspace W.isClosedSubspace V)) :=
    isAffine_of_isAffineHom (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
      hX.1 W.subspace W.isClosedSubspace V)
  have hci₂ := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
    W.isClosedSubspace.1 (componentVanishingLocus D sX hX L s W).1
    (componentVanishingLocus D sX hX L s W).2
    (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V)
  refine Scheme.ker_comp_eq_sup_ofIdealTop _ _ _ ?_
  refine Eq.trans ?_ (sectionEvaluationIdealAt_modulePullback_eq_map D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) L
    (closedSubspaceBaseChangeChartDiagram D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace V) e s hL hMaff hcompat hfree)
  exact Scheme.ker_appTop_of_ker_eq_ofIdealTop _ _
    (ker_closedSubspaceBaseChangeChartProj_zeroScheme D.site D.base D.base_mem
      ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩
      (integralClosedSubspaceRestrict D sX hX L W)
      (isInvertible_modulePullback_obj D.site D.base D.base_mem
        (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace) L hL)
      (integralClosedSubspaceRestrictSection D sX hX L s W)
      (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
        W.isClosedSubspace V))

/-- **The cycle of Stacks 02QU of the chart of `Z(s|_W)`, read on the ideal-sheaf
presentation.**  The `k`-cycle of the chart `(V ×_X W) ×_W Z(s|_W)` of the zero scheme of `s|_W`,
read as a closed subscheme of the chart `V` of `X`, is the `k`-cycle of the closed subscheme of
`V` cut out by the sum of the ideal sheaf of `V ×_X W` and the evaluation ideal of `s` at `V`. -/
theorem cycleAssociatedToClosedSubscheme_componentVanishingLocusChartImmersion
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings D.site D.base D.base_mem ⟨X, hX.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨X, hX.1⟩).property L)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : SmallEtale D.site D.base D.base_mem X) [IsAffine (chartScheme V)]
    (e : (T : SmallEtale D.site D.base D.base_mem X) → (T ⟶ V) → L.val.obj (op T))
    (hcompat : ∀ (T T' : SmallEtale D.site D.base D.base_mem X) (j : T ⟶ V) (g : T' ⟶ T),
      (L.val.map g.op).hom (e T j) = e T' (g ≫ j))
    (hfree : ∀ (T : SmallEtale D.site D.base D.base_mem X) (j : T ⟶ V),
      Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 T ↦ r • e T j)
    (C : Stacks.Chow.ChowSituation.{u}) (g : chartScheme V ⟶ C.S) [LocallyOfFiniteType g]
    (k : ℤ) :
    haveI := isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s W V
    Stacks.Chow.cycleAssociatedToClosedSubscheme C g
        (componentVanishingLocusChartImmersion D sX hX L s W V) k =
      Stacks.Chow.cycleAssociatedToClosedSubscheme C g
        (((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
            W.isClosedSubspace V).ker ⊔ Scheme.IdealSheafData.ofIdealTop
              (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V)).subschemeι)
        k := by
  have hci := isClosedImmersion_componentVanishingLocusChartImmersion D sX hX L s W V
  have hk : (((closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
          W.isClosedSubspace V).ker ⊔ Scheme.IdealSheafData.ofIdealTop
            (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V)).subschemeι).ker =
      (componentVanishingLocusChartImmersion D sX hX L s W V).ker :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans
      (ker_componentVanishingLocusChartImmersion D sX hX L s hL W V e hcompat hfree).symm
  have := IsClosedImmersion.isIso_lift _ _ hk
  exact Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso C g _ _
    (asIso (IsClosedImmersion.lift _ _ hk.le)) (IsClosedImmersion.lift_fac _ _ _) k

/-- **The δ-dimension bound of Stacks 0EQL, transported to the chart.**  If the good algebraic
space `X/B` has `dim_δ(X) ≤ k` then the δ-dimension of Stacks 02QS of the chart scheme over the
situation on the chart is at most `k`. -/
theorem schemeDeltaDimension_id_chartChowSituation_le
    (V : SmallEtale D.site D.base D.base_mem X)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (k : ℤ) (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ ≤ (k : EInt)) :
    haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        (𝟙 (chartScheme V)) ≤ (k : EInt) := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  have h := (deltaDimensionClosed_le_coe_iff D sX hX Set.univ isClosed_univ k).1 hdim
  have hle := Stacks.Chow.schemeDeltaDimension_le_of_forall_relativeDimension_le
    (chartChowSituation D sX hX V hs) (f := 𝟙 (chartScheme V)) (j := 𝟙 (chartScheme V))
    (k := k) fun w =>
      (relativeDimension_id_chartChowSituation D sX hX V hs w).trans_le
        (h _ (Set.mem_univ _))
  simpa using hle

/-- **The local identity of Stacks 0EQL at a point of a chart trivialising `ℒ`.**  Let `X/B` be a
good algebraic space with `dim_δ(X) ≤ k + 1` (`hdim`), let `ℒ` be an invertible `𝒪_X`-module with
a global section `s`, let `V` be a surjective affine étale chart of `X` carrying a compatible
family `(e, hcompat, hfree)` of free generators of `ℒ` over the charts above it, and let `Z ⊆ X`
be an integral closed subspace with `dim_δ(Z) = k` (`hZdim`). Let `v` be a point of `V` over the
generic point of `Z` at which the local data of Stacks 0EPI hold for the closed subscheme of `V`
cut out by the evaluation ideal of `s`: it lies in that subscheme (`hvD`), which has δ-dimension
at most `k` (`hDdim`) and is generated at `v` by the germ of `a` (`haD`), a nonzerodivisor (`ha`)
in the maximal ideal (`ham`) of finite colength (`hfinite`). Then the coefficient of `Z` in
`[Z(s)]_k` is its coefficient in `∑ n_i [Z(s|_{X_i})]_k`. -/
theorem cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart_of_trivialisingChart
    (k : ℤ) (hL : IsInvertibleSheaf D sX hX L)
    (hEgood : D.IsGood ((vanishingLocus D sX hX L s).1.ι ≫ sX))
    (hVLgood : ∀ W : ComponentsOfDeltaDimension D sX hX (k + 1),
      D.IsGood ((componentVanishingLocus D sX hX L s W.1).1.ι ≫ W.1.subspace.ι ≫ sX))
    (V : SmallEtale D.site D.base D.base_mem X) [IsAffine (chartScheme V)]
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme D.site D.base D.base_mem))) V.obj.hom)
    (e : (T : SmallEtale D.site D.base D.base_mem X) → (T ⟶ V) → L.val.obj (op T))
    (hcompat : ∀ (T T' : SmallEtale D.site D.base D.base_mem X) (j : T ⟶ V) (g : T' ⟶ T),
      (L.val.map g.op).hom (e T j) = e T' (g ≫ j))
    (hfree : ∀ (T : SmallEtale D.site D.base D.base_mem X) (j : T ⟶ V),
      Function.Bijective fun r : chartRing D.site D.base D.base_mem X hX.1 T ↦ r • e T j)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγ : ∀ x, (γ x).image = x)
    (γW : ComponentGeometricRepresentatives D sX hX L s k)
    (hγW : ∀ (W : ComponentsOfDeltaDimension D sX hX (k + 1)) y, (γW W y).image = y)
    (γZ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hγZ : ∀ y, (γZ y).image = y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (v : chartScheme V)
    (hv : chartSchemeToPoints D.site D.base D.base_mem X V v =
      Z.ambientGenericPoint D.site D.base D.base_mem)
    (hvD : v ∈ (Scheme.IdealSheafData.ofIdealTop
      (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V)).support)
    (U : (chartScheme V).affineOpens) (hvU : v ∈ U.1) (a : Γ(chartScheme V, U.1))
    (haD : AlgebraicGeometry.IdealSheafData.stalk (Scheme.IdealSheafData.ofIdealTop
        (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V)) v =
      Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a})
    (ha : IsSMulRegular ((chartScheme V).presheaf.stalk v)
      (((chartScheme V).presheaf.germ U.1 v hvU).hom a))
    (ham : ((chartScheme V).presheaf.germ U.1 v hvU).hom a ∈
      IsLocalRing.maximalIdeal ((chartScheme V).presheaf.stalk v))
    (hfinite : Module.length ((chartScheme V).presheaf.stalk v)
      ((chartScheme V).presheaf.stalk v ⧸
        Ideal.span {((chartScheme V).presheaf.germ U.1 v hvU).hom a}) ≠ ⊤)
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ ≤ ((k + 1 : ℤ) : EInt))
    (hZdim : deltaDimension D sX Z = k) :
    haveI := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
    haveI := locallyOfFiniteType_subschemeι_comp_id_chartChowSituation D sX hX V hs
      (Scheme.IdealSheafData.ofIdealTop
        (sectionEvaluationIdealAt D.site D.base D.base_mem ⟨X, hX.1⟩ L s V))
    Stacks.Chow.schemeDeltaDimension (chartChowSituation D sX hX V hs)
        ((Scheme.IdealSheafData.ofIdealTop (sectionEvaluationIdealAt D.site D.base D.base_mem
          ⟨X, hX.1⟩ L s V)).subschemeι ≫ 𝟙 (chartScheme V)) ≤ (k : EInt) →
    cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 k γZ Z =
      componentZeroCycleSumCoeff D sX hX L s k γ γW Z := by
  have hft := locallyOfFiniteType_id_chartChowSituation D sX hX V hs
  intro hDdim
  refine cycleCoeffOfClosedSubspace_eq_componentZeroCycleSumCoeff_chart D sX hX L s k hL hEgood
    hVLgood V hs γ hγ γW hγW γZ hγZ Z v hv hvD U hvU a haD ha ham hfinite (fun Xi => ?_) ?_
    hDdim
    ((deltaDimension_eq_relativeDimension_id_chartChowSituation D sX hX V hs Z v hv).symm.trans
      hZdim)
  · rw [cycleAssociatedToClosedSubscheme_componentVanishingLocusChartImmersion D sX hX L s hL
      Xi.1 V e hcompat hfree (chartChowSituation D sX hX V hs) (𝟙 (chartScheme V)) k]
  · exact_mod_cast schemeDeltaDimension_id_chartChowSituation_le D sX hX V hs (k + 1) hdim

end AlgebraicGeometry.Space

end
