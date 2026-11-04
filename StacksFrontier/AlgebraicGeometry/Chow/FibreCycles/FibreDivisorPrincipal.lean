module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreFamilyReduction
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.LineChartDifference

/-!
# The two distinguished divisors of an integral family cut out a principal divisor

Let `f : X ⟶ S` and let `W ⊆ X ×_S ℙ¹_S` be an integral closed subscheme contained in neither
the image of the zero section nor the image of the infinity section. Part (1) of Stacks Tag 02S4
says that the two closed subschemes `W₀ = W ∩ D₀` and `W_∞ = W ∩ D_∞` are effective Cartier
divisors on `W`. This file proves the next step, the identity

  `div_W(t) = [W₀]_{n-1} - [W_∞]_{n-1}`   as cycles on `W`,

where `n = dim_δ(W)` and `t` is the coordinate of the first affine chart of `ℙ¹_S`, read as a
rational function on `W` along the second projection.

The identity is `Stacks.Chow.principalDivisorCycle_eq_sub_lineFibreCycles` for `A = W` and `q`
the second projection. For reduced `W` the inverse images of `D₀` and `D_∞` along `q` are the two
divisors `Stacks.Chow.zeroDivisor` and `Stacks.Chow.infinityDivisor` of Tag 02S4, and the generic
point of `W` lies on both affine charts of `ℙ¹_S` and off the support of both divisors.

## Main definitions

* `Stacks.Chow.fibreLineProjection` — the second projection `W ⟶ ℙ¹_S` of a closed subscheme of
  `X ×_S ℙ¹_S`, with `Stacks.Chow.fibreLineProjection_def` its defining equation.
* `Stacks.Chow.fibreCoordinate` — the coordinate of the first chart of `ℙ¹_S` as a rational
  function on an integral `W` not contained in the infinity section.

## Main results

* `Stacks.Chow.compl_range_projectiveLineYChart` and `Stacks.Chow.compl_range_affineYChart` — the
  image of the zero section is exactly the complement of the second affine chart, the mirror of
  `Stacks.Chow.compl_range_affineChart`.
* `Stacks.Chow.notMem_support_genericPoint_of_ne_bot` — on an integral scheme the generic point
  avoids the support of every ideal sheaf other than the trivial one.
* `Stacks.Chow.zeroDivisor_eq_comap_lineZeroDivisor` and
  `Stacks.Chow.infinityDivisor_eq_comap_lineInfinityDivisor` — for reduced `W` the two divisors
  of Tag 02S4 are the inverse images of `D₀` and `D_∞` along the second projection.
* `Stacks.Chow.schemeDeltaDimension_familyBase` — the delta-dimension of an integral `W`, read at
  its generic point, which is the form Tag 02S4 states its dimension hypothesis in.
* `Stacks.Chow.principalDivisorCycle_eq_sub_fibreDivisorCycles` — the identity
  `div_W(t) = [W₀]_{n-1} - [W_∞]_{n-1}` on `W`.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The complement of the second affine chart -/

/-- The coordinate of the first chart of `ℙ¹_ℤ` vanishes at every point of `ℙ¹_ℤ` off the second
chart. -/
theorem X_mem_of_notMem_range_projectiveLineYChart
    {x : AlgebraicGeometry.Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))}
    (hx : (projectiveLineXChart (ULift.{u} ℤ)).base x ∉
      Set.range (projectiveLineYChart (ULift.{u} ℤ))) :
    (Polynomial.X : Polynomial (ULift.{u} ℤ)) ∈
      (x : PrimeSpectrum (Polynomial (ULift.{u} ℤ))).asIdeal := by
  by_contra hXn
  obtain ⟨y, hy⟩ := mem_range_puncturedChart_of_X_notMem hXn
  refine hx ⟨(AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)).base y, ?_⟩
  calc (projectiveLineYChart (ULift.{u} ℤ)).base
        ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom)).base y)
      = (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (projectiveLineOverlapInverseCoordinate (ULift.{u} ℤ)).toRingHom) ≫
          projectiveLineYChart (ULift.{u} ℤ)).base y :=
        (Scheme.Hom.comp_apply _ _ y).symm
    _ = (projectiveLinePuncturedChart (ULift.{u} ℤ) ≫
          projectiveLineXChart (ULift.{u} ℤ)).base y := by
        rw [(isPullback_projectiveLineCharts (ULift.{u} ℤ)).w]
    _ = (projectiveLineXChart (ULift.{u} ℤ)).base
          ((projectiveLinePuncturedChart (ULift.{u} ℤ)).base y) :=
        Scheme.Hom.comp_apply _ _ y
    _ = (projectiveLineXChart (ULift.{u} ℤ)).base x := by rw [hy]

/-- The point `0` of `ℙ¹_ℤ` does not lie on the second chart: it is the origin of the first
chart, and the coordinate of the second chart vanishes there. -/
theorem disjoint_range_integralZeroSection_projectiveLineYChart :
    Disjoint (Set.range (integralZeroSection.{u}))
      (Set.range (projectiveLineYChart (ULift.{u} ℤ))) := by
  rw [Set.disjoint_left]
  rintro p hp hx
  rw [range_integralZeroSection] at hp
  obtain ⟨y, hy, rfl⟩ := hp
  exact notMem_range_ι_of_X_mem (ULift.{u} ℤ) _ _
    (projectiveLineXIndex_ne_projectiveLineYIndex (ULift.{u} ℤ)) y
    (X_mem_of_mem_range_specMap_evalRingHom_zero hy) hx

/-- The zero point is the only point of `ℙ¹_ℤ` off the second chart. -/
theorem compl_range_projectiveLineYChart :
    (Set.range (projectiveLineYChart (ULift.{u} ℤ)))ᶜ = Set.range (integralZeroSection.{u}) := by
  refine Set.eq_of_subset_of_subset (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨x, rfl⟩ : p ∈ Set.range (projectiveLineXChart (ULift.{u} ℤ)) := by
      rcases Set.eq_univ_iff_forall.mp
        (range_projectiveLineXChart_union_range_projectiveLineYChart (ULift.{u} ℤ)) p with h | h
      · exact h
      · exact absurd h hp
    rw [range_integralZeroSection]
    exact ⟨x, mem_range_specMap_evalRingHom_zero_of_X_mem
      (X_mem_of_notMem_range_projectiveLineYChart hp), rfl⟩
  · exact Set.disjoint_left.mp
      disjoint_range_integralZeroSection_projectiveLineYChart hp

/-- The image of the zero section of `ℙ¹_S ⟶ S` is exactly the complement of the second affine
chart of `ℙ¹_S`. -/
theorem compl_range_affineYChart (S : Scheme.{u}) :
    (Set.range (affineYChart S))ᶜ = Set.range (lineZeroSection S) := by
  rw [range_affineYChart, ← Set.preimage_compl, compl_range_projectiveLineYChart,
    lineZeroSection, range_lineConstantSection]

/-! ### The generic point of an integral scheme avoids every nontrivial support -/

/-- On an integral scheme the generic point avoids the support of every ideal sheaf other than
the trivial one. -/
theorem notMem_support_genericPoint_of_ne_bot {Y : Scheme.{u}} [IsIntegral Y]
    {I : Y.IdealSheafData} (hI : I ≠ ⊥) :
    genericPoint Y ∉ (I.support : Set Y) := by
  intro hmem
  refine hI (le_bot_iff.mp ?_)
  have htop : (⊤ : Closeds Y) ≤ I.support := by
    refine fun y _ ↦ ?_
    have hcl : closure ({genericPoint Y} : Set Y) ⊆ (I.support : Set Y) :=
      I.support.2.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
    exact hcl (by rw [genericPoint_spec Y |>.def]; trivial)
  have hle := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp htop
  rwa [show Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y) = ⊥ from by
    rw [show (⊤ : Closeds Y) = (⊥ : Y.IdealSheafData).support from
      (Scheme.IdealSheafData.support_bot).symm,
      Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.nilradical_eq_bot] at hle

/-! ### The second projection of a closed subscheme of the family -/

section Projection

variable {X S : Scheme.{u}} (f : X ⟶ S) (W : (projectiveLineProduct f).IdealSheafData)

/-- The second projection `W ⟶ ℙ¹_S` of a closed subscheme `W ⊆ X ×_S ℙ¹_S`. -/
def fibreLineProjection : W.subscheme ⟶ relativeProjectiveLine S :=
  W.subschemeι ≫ pullback.snd f (relativeProjectiveLine S ↘ S)

/-- The second projection of `W` is the inclusion of `W` followed by the second projection of
the family. -/
theorem fibreLineProjection_def :
    fibreLineProjection f W =
      W.subschemeι ≫ pullback.snd f (relativeProjectiveLine S ↘ S) :=
  rfl

/-- For reduced `W` the zero divisor of `W` is the inverse image of `D₀ ⊆ ℙ¹_S` along the second
projection. -/
theorem zeroDivisor_eq_comap_lineZeroDivisor [IsReduced W.subscheme] :
    zeroDivisor f W = (lineZeroDivisor S).comap (fibreLineProjection f W) := by
  rw [zeroDivisor_eq_comap_ker f W, ker_zeroSection f, fibreLineProjection_def f W,
    Scheme.IdealSheafData.comap_comp]

/-- For reduced `W` the infinity divisor of `W` is the inverse image of `D_∞ ⊆ ℙ¹_S` along the
second projection. -/
theorem infinityDivisor_eq_comap_lineInfinityDivisor [IsReduced W.subscheme] :
    infinityDivisor f W = (lineInfinityDivisor S).comap (fibreLineProjection f W) := by
  rw [infinityDivisor_eq_comap_ker f W, ker_infinitySection f, fibreLineProjection_def f W,
    Scheme.IdealSheafData.comap_comp]

/-- An integral `W` not contained in the image of the zero section has its generic point off the
zero divisor. -/
theorem notMem_support_zeroDivisor_genericPoint [IsIntegral W.subscheme]
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f)) :
    genericPoint W.subscheme ∉ ((zeroDivisor f W).support : Set W.subscheme) :=
  notMem_support_genericPoint_of_ne_bot (zeroDivisor_ne_bot f W h₀)

/-- An integral `W` not contained in the image of the infinity section has its generic point off
the infinity divisor. -/
theorem notMem_support_infinityDivisor_genericPoint [IsIntegral W.subscheme]
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    genericPoint W.subscheme ∉ ((infinityDivisor f W).support : Set W.subscheme) :=
  notMem_support_genericPoint_of_ne_bot (infinityDivisor_ne_bot f W hInf)

/-- The generic point of an integral scheme lies over an open `U` as soon as it is off the
inverse image of a divisor `D` whose support is the complement of `U`. -/
private theorem genericPoint_mem_preimage_of_notMem_support_comap {Y Z : Scheme.{u}}
    [IsIntegral Y] (g : Y ⟶ Z) (D : Z.IdealSheafData) (U : Z.Opens)
    (hU : (U : Set Z)ᶜ = D.support) (h : genericPoint Y ∉ (D.comap g).support) :
    genericPoint Y ∈ g ⁻¹ᵁ U := by
  rw [Scheme.IdealSheafData.support_comap] at h
  by_contra hc
  exact h (show g.base (genericPoint Y) ∈ (D.support : Set Z) by rw [← hU]; exact hc)

/-- The second projection carries the generic point of an integral `W` not contained in the
infinity section into the first affine chart of `ℙ¹_S`: the complement of that chart is the image
of the infinity section, which is the support of `D_∞`. -/
theorem genericPoint_mem_preimage_chartOpen [IsIntegral W.subscheme]
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    genericPoint W.subscheme ∈ (fibreLineProjection f W) ⁻¹ᵁ chartOpen S := by
  refine genericPoint_mem_preimage_of_notMem_support_comap _ (lineInfinityDivisor S) _ ?_ ?_
  · rw [coe_support_lineInfinityDivisor, ← compl_range_affineChart S]
    simp
  · rw [← infinityDivisor_eq_comap_lineInfinityDivisor f W]
    exact notMem_support_infinityDivisor_genericPoint f W hInf

/-- The second projection carries the generic point of an integral `W` not contained in the zero
section into the second affine chart of `ℙ¹_S`: the complement of that chart is the image of the
zero section, which is the support of `D₀`. -/
theorem genericPoint_mem_preimage_yChartOpen [IsIntegral W.subscheme]
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f)) :
    genericPoint W.subscheme ∈ (fibreLineProjection f W) ⁻¹ᵁ yChartOpen S := by
  refine genericPoint_mem_preimage_of_notMem_support_comap _ (lineZeroDivisor S) _ ?_ ?_
  · rw [coe_support_lineZeroDivisor, ← compl_range_affineYChart S]
    simp
  · rw [← zeroDivisor_eq_comap_lineZeroDivisor f W]
    exact notMem_support_zeroDivisor_genericPoint f W h₀

end Projection

/-! ### The principal divisor of the chart coordinate on the family -/

section Principal

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (W : (projectiveLineProduct f).IdealSheafData)

/-- **The dimension hypothesis of Stacks Tag 02S4, read as a delta-dimension.** For an integral
`W` the delta-dimension of `W` over the base is its relative dimension at the generic point, so
the hypothesis of the tag — that every generic point of `W` has relative dimension `k + 1` —
says exactly that `dim_δ(W) = k + 1`. -/
theorem schemeDeltaDimension_familyBase [IsIntegral W.subscheme] {n : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = n) :
    schemeDeltaDimension C (familyBase f W) = (n : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint C (familyBase f W)]
  exact congrArg _ (hDim ⟨genericPoint W.subscheme,
    genericPoint_mem_genericPoints W.subscheme⟩)

/-- The coordinate of the first affine chart of `ℙ¹_S`, read along the second projection as a
rational function on an integral `W` not contained in the image of the infinity section. -/
def fibreCoordinate [IsIntegral W.subscheme]
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    W.subscheme.functionField :=
  lineChartFunction (fibreLineProjection f W)
    (genericPoint_mem_preimage_chartOpen f W hInf)

/-- **The principal divisor of the chart coordinate on an integral family over the projective
line.** Let `W ⊆ X ×_S ℙ¹_S` be integral of delta-dimension `n` over the base, contained in
neither the image of the zero section nor the image of the infinity section. Then the principal
divisor on `W` of the coordinate of the first chart of `ℙ¹_S` is the difference of the cycles of
the two divisors of `W`:

  `div_W(t) = [W₀]_{n-1} - [W_∞]_{n-1}`.

The two divisors are those of part (1) of Stacks Tag 02S4. -/
theorem principalDivisorCycle_eq_sub_fibreDivisorCycles [IsIntegral W.subscheme] {n : ℤ}
    (hdim : schemeDeltaDimension C (familyBase f W) = (n : EInt))
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    principalDivisorCycle C (familyBase f W) hdim (fibreCoordinate C f W hInf) =
      cycleAssociatedToClosedSubscheme C (familyBase f W) (zeroDivisor f W).subschemeι (n - 1) -
        cycleAssociatedToClosedSubscheme C (familyBase f W)
          (infinityDivisor f W).subschemeι (n - 1) := by
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (familyBase f W)
  have hgen0 : genericPoint W.subscheme ∉
      Set.range ((lineZeroDivisor C.S).comap (fibreLineProjection f W)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, ← zeroDivisor_eq_comap_lineZeroDivisor f W]
    exact notMem_support_zeroDivisor_genericPoint f W h₀
  have hgenInf : genericPoint W.subscheme ∉
      Set.range ((lineInfinityDivisor C.S).comap (fibreLineProjection f W)).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      ← infinityDivisor_eq_comap_lineInfinityDivisor f W]
    exact notMem_support_infinityDivisor_genericPoint f W hInf
  have hmain := principalDivisorCycle_eq_sub_lineFibreCycles C (familyBase f W)
    (fibreLineProjection f W) hdim (genericPoint_mem_preimage_chartOpen f W hInf)
    (genericPoint_mem_preimage_yChartOpen f W h₀) hgen0 hgenInf
  rw [← zeroDivisor_eq_comap_lineZeroDivisor f W,
    ← infinityDivisor_eq_comap_lineInfinityDivisor f W] at hmain
  exact hmain

end Principal

end Stacks.Chow

end
