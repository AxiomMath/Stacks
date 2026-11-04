module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeComponentCycles

/-!
# The zero scheme of a regular section drops the δ-dimension

In Situation 0EDT let `X/B` be good with `dim_δ(X) ≤ k + 1`, let `ℒ` be an invertible
`𝒪_X`-module and let `s ∈ Γ(X, ℒ)` be a regular section. Then the zero scheme `Z(s)` of
Stacks 0845 has `dim_δ(Z(s)) ≤ k`, so that the cycle `[Z(s)]_k` of Stacks 0EE9 is defined.

A point `x ∈ |X|` with `δ(x) = k + 1` is a generic point of an irreducible component of `|X|`,
`δ` dropping strictly along every nontrivial specialization. On an affine étale chart `W` through
`x` on which `ℒ` is free, the local ring `A = 𝒪_{W, w}` therefore has dimension zero (Stacks 04NA),
so it is Artinian, being Noetherian. The germ `f` of the coordinate of `s` is a nonzerodivisor of
`A`, `s` being regular, hence a unit; and `(f)` is the ideal of `Z(s)` in `A` (Stacks 0846), so
`x ∉ |Z(s)|`.

## Main results

* `TopologicalSpace.codimension_closureSingleton_eq_zero`: a point at which a dimension function
  attains its maximum has codimension zero.
* `AlgebraicGeometry.Space.map_germ_definingIdealAt_ne_top`: at a chart point over a point of a
  closed subspace, the ideal of the subspace is a proper ideal of the local ring.
* `AlgebraicGeometry.Space.notMem_vanishingLocus_of_deltaValue_eq`: a point of δ-value `k + 1` is
  not on `Z(s)`.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_vanishingLocus_le_of_isRegularSection`:
  `dim_δ(Z(s)) ≤ k`.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_preimage_le_of_isLocallyQuasiFinite`: the
  inverse image of a closed subspace of δ-dimension at most `k` along a locally quasi-finite
  morphism over the base has δ-dimension at most `k`.
* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_closedSubspace_le`: the δ-dimension of a
  closed subspace computed on the subspace itself.

## References

* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQN](https://stacks.math.columbia.edu/tag/0EQN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

open TopologicalSpace.IrreducibleCloseds (closureSingleton)

universe u

namespace TopologicalSpace

/-- **A point at which a dimension function attains its maximum has codimension zero.** If
`d ≤ k` everywhere and `d z = k`, then an irreducible closed set `Z ⊋ {z}‾` would have a generic
point `ζ ⤳ z` with `ζ ≠ z`, so `d ζ > k`. -/
theorem codimension_closureSingleton_eq_zero {A : Type*} [TopologicalSpace A] [QuasiSober A]
    (d : DimensionFunction A) {k : ℤ} (hd : ∀ y, d y ≤ k) (z : A) (hz : d z = k) :
    codimension (closureSingleton z) = 0 := by
  rw [codimension_eq_coheight, Order.coheight_eq_zero]
  intro Z hZ
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
  have hzZ : z ∈ (Z : Set A) := hZ (subset_closure rfl)
  have hspec : ζ ⤳ z := hζ.specializes hzZ
  by_cases hne : ζ = z
  · subst hne
    intro x hx
    show x ∈ closure {ζ}
    rw [hζ]
    exact hx
  · have := d.strictAnti_specializes hspec hne
    have := hd ζ
    omega

end TopologicalSpace

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Chart points over a closed subspace -/

section ChartPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)

include hY in
/-- **A chart point over a point of a closed subspace lifts to the base-changed chart**
(Stacks 03H4): if the point of `|Y|` carried by `u ∈ W` lies on the closed subspace `Z`, then `u`
is in the image of `Z ×_Y W → W`. -/
theorem exists_rep_snd_eq_of_chartSchemeToPoints_mem (Z : ClosedSubspaces B S hS Y)
    (W : SmallEtale B S hS Y) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS Y W u ∈ subspacePointSet B S hS Y Z.1) :
    u ∈ Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.obj.hom)) := by
  obtain ⟨a, ha⟩ := hu
  set b := (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS Y).obj W)).symm u with hb
  have hab : pointsMap B S hS Z.1.toFunctor (closedSubspaceHom B S hS hY Z.1 Z.2).hom a =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y).obj W)) W.obj.hom b :=
    ha.trans (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS Y W u)
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    ((isClosedImmersion_closedSubspaceHom B S hS hY Z.1 Z.2).rep.isPullback W.obj.hom) a b hab
  refine ⟨pointsToScheme B S hS _ w, ?_⟩
  refine (pointsToScheme_pointsMap_yoneda B S hS
    ((isClosedImmersion_closedSubspaceHom B S hS hY Z.1 Z.2).rep.snd W.obj.hom) w).symm.trans ?_
  rw [hw, hb]
  exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS Y).obj W)).apply_symm_apply u

/-- **At a chart point over a point of a closed subspace the ideal of the subspace is proper**:
the chart point lies in the zero locus of the defining ideal over the chart, so the germs of the
elements of that ideal lie in the maximal ideal of the local ring. -/
theorem map_germ_definingIdealAt_ne_top (Z : ClosedSubspaces B S hS Y) (W : SmallEtale B S hS Y)
    [IsAffine (chartScheme W)] (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS Y W u ∈ subspacePointSet B S hS Y Z.1) :
    Ideal.map ((chartScheme W).presheaf.germ ⊤ u trivial).hom
        (definingIdealAt B S hS ⟨Y, hY⟩ Z (op W)) ≠ ⊤ := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W.obj.left) := ‹IsAffine (chartScheme W)›
  have hmem := exists_rep_snd_eq_of_chartSchemeToPoints_mem hY Z W u hu
  rw [range_rep_snd_eq_zeroLocus_definingIdealAt B S hS ⟨Y, hY⟩ Z W,
    Scheme.mem_zeroLocus_iff] at hmem
  refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    (Ideal.map_le_iff_le_comap.2 fun g hg => ?_)
  exact (IsLocalRing.mem_maximalIdeal _).2 fun hunit =>
    hmem g hg ((Scheme.mem_basicOpen _ g u trivial).2 hunit)

end ChartPoints

/-! ### The δ-dimension of the zero scheme of a regular section -/

section DeltaDimension

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- **The local ring of an étale chart at a point over a point of maximal δ-value has dimension
zero**, on a good space of δ-dimension at most `k`: its dimension is the codimension of the
closure of the image point (Stacks 04NA, 0ED1), which is zero by
`TopologicalSpace.codimension_closureSingleton_eq_zero`. -/
theorem ringKrullDim_stalk_chartScheme_le_zero {k : ℤ}
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ ≤ (k : EInt))
    (W : SmallEtale D.site D.base D.base_mem X) (w : chartScheme W)
    (hw : D.deltaValue sX (chartSchemeToPoints D.site D.base D.base_mem X W w) = k) :
    ringKrullDim ((chartScheme W).presheaf.stalk w) ≤ 0 := by
  have : QuasiSober (points D.site D.base D.base_mem X) := quasiSober_points_of_isGood D sX hX
  rw [ringKrullDim_stalk_eq_coheight w,
    coheight_eq_codimension_chartSchemeToPoints D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) W w]
  have h := codimension_closureSingleton_eq_zero (deltaDimensionFunction D sX hX)
    (k := k) (fun y => by
      rw [deltaDimensionFunction_apply]
      exact (deltaDimensionClosed_le_coe_iff D sX hX Set.univ isClosed_univ k).mp hdim y
        (Set.mem_univ y))
    (chartSchemeToPoints D.site D.base D.base_mem X W w)
    (by rw [deltaDimensionFunction_apply]; exact hw)
  rw [h]
  rfl

/-- **A regular section does not vanish at a point of maximal δ-value.** In Situation 0EDT let
`X/B` be good with `dim_δ(X) ≤ k + 1`, let `ℒ` be invertible and `s ∈ Γ(X, ℒ)` regular. A point
`x ∈ |X|` with `δ(x) = k + 1` does not lie on the zero scheme `Z(s)`.

On an affine étale chart through `x` on which `ℒ` is free, the local ring `A` at a point over `x`
has dimension zero (`AlgebraicGeometry.Space.ringKrullDim_stalk_chartScheme_le_zero`) and is
Noetherian, hence Artinian; the germ `f` of the coordinate of `s` is a nonzerodivisor of `A`,
hence a unit, and `(f)` is the ideal of `Z(s)` in `A` (Stacks 0846), which is therefore the unit
ideal. -/
theorem notMem_vanishingLocus_of_deltaValue_eq (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleSheaf D sX hX L) (s : L.sections)
    (hs : AlgebraicGeometry.IsRegularSection (structureCommRings D.site D.base D.base_mem ⟨X, hX.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨X, hX.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ ≤ ((k + 1 : ℤ) : EInt))
    (x : points D.site D.base D.base_mem X) (hx : D.deltaValue sX x = k + 1) :
    x ∉ subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1 := by
  intro hmem
  obtain ⟨C, x', hx'⟩ := exists_chartSchemeToPoints_eq D.site D.base D.base_mem ⟨X, hX.1⟩ x
  obtain ⟨W, κ, hWaff, w, e, hcompat, hfree, hwx⟩ := exists_affine_chart_free_of_chart D.site
    D.base D.base_mem ⟨X, hX.1⟩ L (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL)
    C x'
  have := hWaff
  have hw : chartSchemeToPoints D.site D.base D.base_mem X W w = x := by
    rw [← chartSchemeToPoints_map D.site D.base D.base_mem X κ w, hwx, hx']
  let eW := LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (e W (𝟙 W))) (hfree W (𝟙 W))
  let l₀ : Module.Dual (chartRing D.site D.base D.base_mem X hX.1 W) (L.val.obj (op W)) :=
    eW.symm.toLinearMap
  have hb : ∀ y, l₀ y • e W (𝟙 W) = y := fun y => eW.apply_symm_apply y
  have hreg := (isRegularSection_iff_forall_injective_smul D.site D.base D.base_mem ⟨X, hX.1⟩ L
    s).1 hs (op W)
  have hinjg := (injective_smul_eval_iff_injective_mul_generator D.site D.base D.base_mem
    ⟨X, hX.1⟩ L s W (e W (𝟙 W)) l₀ hb).1 hreg
  -- the coordinate of `s` is a nonzerodivisor, and so is its germ
  have hg : l₀ (s.eval (op W)) ∈ nonZeroDivisors Γ(chartScheme W, ⊤) :=
    mem_nonZeroDivisors_iff_right.mpr fun r hr => hinjg (hr.trans (zero_mul _).symm)
  let : Algebra Γ(chartScheme W, ⊤) ((chartScheme W).presheaf.stalk w) :=
    (chartScheme W).presheaf.algebra_section_stalk (U := ⊤) ⟨w, trivial⟩
  have hloc := (isAffineOpen_top (chartScheme W)).isLocalization_stalk ⟨w, trivial⟩
  have hf : ((chartScheme W).presheaf.germ ⊤ w trivial).hom (l₀ (s.eval (op W))) ∈
      nonZeroDivisors ((chartScheme W).presheaf.stalk w) :=
    IsLocalization.nonZeroDivisors_le_comap
      ((isAffineOpen_top (chartScheme W)).primeIdealOf ⟨w, trivial⟩).asIdeal.primeCompl
      ((chartScheme W).presheaf.stalk w) hg
  -- the local ring is Artinian, so the germ is a unit
  have : IsNoetherianRing ((chartScheme W).presheaf.stalk w) :=
    isNoetherianRing_stalk_chartScheme_of_isGood D sX hX W w
  have hA := ringKrullDim_stalk_chartScheme_le_zero D sX hX hdim W w (by rw [hw]; exact hx)
  have : Ring.KrullDimLE 0 ((chartScheme W).presheaf.stalk w) := by
    rw [Ring.krullDimLE_iff]
    exact_mod_cast hA
  have := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    (R := (chartScheme W).presheaf.stalk w)
  have hunit := IsArtinianRing.isUnit_iff_mem_nonZeroDivisors.mpr hf
  refine map_germ_definingIdealAt_ne_top hX.1 (vanishingLocus D sX hX L s) W w (hw ▸ hmem) ?_
  rw [map_germ_definingIdealAt_zeroScheme_eq_span hX.1 W L hL s (e W (𝟙 W)) l₀ hb w]
  exact Ideal.span_singleton_eq_top.mpr hunit

/-- **The zero scheme of a regular section has δ-dimension at most `k`.** In Situation 0EDT let
`X/B` be good with `dim_δ(X) ≤ k + 1`, let `ℒ` be an invertible `𝒪_X`-module and `s ∈ Γ(X, ℒ)` a
regular section. Then `dim_δ(Z(s)) ≤ k`: every point of `|Z(s)|` has δ-value at most `k + 1`, and
the value `k + 1` is excluded by
`AlgebraicGeometry.Space.notMem_vanishingLocus_of_deltaValue_eq`. -/
theorem deltaDimensionSubspace_vanishingLocus_le_of_isRegularSection
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleSheaf D sX hX L) (s : L.sections)
    (hs : AlgebraicGeometry.IsRegularSection (structureCommRings D.site D.base D.base_mem ⟨X, hX.1⟩)
      (structureRingSheaf D.site D.base D.base_mem ⟨X, hX.1⟩).property s) {k : ℤ}
    (hdim : deltaDimensionClosed D sX hX Set.univ isClosed_univ ≤ ((k + 1 : ℤ) : EInt)) :
    deltaDimensionSubspace D sX hX (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2 ≤
      (k : EInt) := by
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed]
  refine (deltaDimensionClosed_le_coe_iff D sX hX _ _ k).2 fun t ht => ?_
  have hle : D.deltaValue sX t ≤ k + 1 :=
    (deltaDimensionClosed_le_coe_iff D sX hX Set.univ isClosed_univ (k + 1)).mp hdim t
      (Set.mem_univ t)
  have hne : D.deltaValue sX t ≠ k + 1 := fun h =>
    notMem_vanishingLocus_of_deltaValue_eq D sX hX L hL s hs hdim t h ht
  show D.deltaValue sX t ≤ k
  omega

/-- **The inverse image of a closed subspace along a locally quasi-finite morphism does not raise
the δ-dimension.** Let `j : T → Y` be a locally quasi-finite morphism of good algebraic spaces over
the base, compatible with the structure morphisms, and let `Z ⊆ Y` be a closed subspace with
`dim_δ(Z) ≤ k`. Then `dim_δ(j⁻¹(Z)) ≤ k`: a point of `|j⁻¹(Z)|` maps to a point of `|Z|`, and the
dimension function does not change along `j`. -/
theorem deltaDimensionSubspace_preimage_le_of_isLocallyQuasiFinite
    {T Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (j : T ⟶ Y) (sT : T ⟶ D.space) (hT : D.IsGood sT) (hjs : j ≫ sY = sT)
    (hj : IsLocallyQuasiFinite D.site D.base D.base_mem j) (Z : Subfunctor Y)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) {k : ℤ}
    (hd : deltaDimensionSubspace D sY hY Z hZ ≤ (k : EInt)) :
    deltaDimensionSubspace D sT hT (Z.preimage j)
        (isClosedSubspace_preimage D.site D.base D.base_mem j Z hY.1 hT.1 hZ) ≤ (k : EInt) := by
  subst hjs
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed] at hd ⊢
  refine (deltaDimensionClosed_le_coe_iff D (j ≫ sY) hT _ _ k).2 fun t ht => ?_
  rw [subspacePointSet_preimage D.site D.base D.base_mem j Z] at ht
  have hcomp := D.deltaValue_comp_of_isLocallyQuasiFinite hT.1 hY.1 j sY hj hY.2.2 t
  show D.deltaValue (j ≫ sY) t ≤ k
  rw [hcomp]
  exact (deltaDimensionClosed_le_coe_iff D sY hY _ _ k).1 hd _ ht

end DeltaDimension

end AlgebraicGeometry.Space

end
