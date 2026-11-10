module

public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityAscent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FiniteChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksCore.Tactic.StacksAttribute

/-!
# A weighting vanishing over a generalization of a point vanishes at that point

Let `f : X ⟶ Y` be locally quasi-finite and locally of finite type and let `w` be a weighting
of `f`. If `y` is a generalization of `f x` and `w` vanishes at every point of `X` over `y`,
then `w` vanishes at `x`.

## Main results

* `AlgebraicGeometry.IsWeighting.eq_zero_of_specializes` — the statement just made.
* `AlgebraicGeometry.IsWeighting.eq_zero_of_eq_zero_over_genericPoint` — over an irreducible
  base, a weighting vanishing above the generic point is identically zero.

## Implementation notes

The point `x` is seen inside a finite open chart `g : V ⟶ U.scheme` over an étale
neighbourhood `U` of `f x` whose fibre over the distinguished point is the single point above
`x`, with purely inseparable residue-field extension; there the weighted fibre sum of the chart
at the distinguished point is exactly `w x`. An étale morphism is flat, hence generalizing, so
the generalization `y` of `f x` is the image of a generalization `u'` of the distinguished
point. The weighted fibre sum of the chart is locally constant, so it takes the same value at
`u'` as at the distinguished point; at `u'` every point of the chart's fibre maps into `X` over
`y`, where `w` vanishes, so the value is zero.

The hypothesis is only that `w` vanishes on the fibre `f ⁻¹' {y}` of the *given*
generalization, not on a whole open or constructible piece of `Y`, because the generalizing
property of the étale neighbourhood produces a point over exactly that `y`.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0H5P**, the step the source leaves as "details omitted" in the proof
of its converse. A weighting of a locally quasi-finite morphism which vanishes at every point
of the source lying over a generalization `y` of `f x` vanishes at `x`.

The source states this only for the base the spectrum of a discrete valuation ring, where `y`
is the generic point and `f x` the closed point; the argument needs nothing of the base beyond
the specialization `y ⤳ f x`. -/
theorem IsWeighting.eq_zero_of_specializes {X Y : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {w : X → ℤ} (hw : IsWeighting f w)
    (x : X) {y : Y} (hy : y ⤳ f x) (hzero : ∀ z : X, f z = y → w z = 0) :
    w x = 0 := by
  classical
  obtain ⟨U, m, D, a, hdata, hcover⟩ := exists_finite_opens_chart_at_point f x
  obtain ⟨p, hpf, hpu⟩ :=
    Scheme.Pullback.exists_preimage_pullback x U.point U.map_point.symm
  obtain ⟨j₀, -⟩ := hcover p hpu hpf
  let V := D j₀
  let fst : pullback f U.toBase ⟶ X := pullback.fst f U.toBase
  let π : pullback f U.toBase ⟶ U.scheme := pullback.snd f U.toBase
  let g := V.ι ≫ π
  let j := V.ι ≫ fst
  obtain ⟨hfinite, hfiber, hsource, ⟨ha, hpure⟩⟩ := hdata j₀
  have : IsFinite g := hfinite
  have hcomm : j ≫ f = g ≫ U.toBase := by
    dsimp [g, j, fst, π]
    have hh := congrArg (fun k : pullback f U.toBase ⟶ Y => V.ι ≫ k)
      (pullback.condition (f := f) (g := U.toBase))
    simpa only [Category.assoc] using hh
  have hlift : pullback.lift j g hcomm = V.ι := by
    apply pullback.hom_ext
    · change pullback.lift j g hcomm ≫ fst = V.ι ≫ fst
      rw [pullback.lift_fst]
    · change pullback.lift j g hcomm ≫ π = V.ι ≫ π
      rw [pullback.lift_snd]
  have hcenter : separableDegreeWeightedFiberSum g (w ∘ j) U.point = w x := by
    rw [separableDegreeWeightedFiberSum_eq_of_fiber_singleton g (w ∘ j) U.point (a j₀)
      hfiber ha hpure]
    change w (j (a j₀)) = w x
    rw [hsource]
  have hLC := hw.isLocallyConstant j g U.toBase hcomm inferInstance
    (by rw [hlift]; infer_instance) hfinite
  obtain ⟨u', hu'spec, hu'map⟩ :=
    exists_specializes_of_isFlatAt U.toBase U.point (Flat.stalkMap _ _)
      (show y ⤳ U.toBase U.point by rw [U.map_point]; exact hy)
  have hterm : ∀ q : (V : Scheme.{u}), separableDegreeWeightedFiberTerm g (w ∘ j) u' q = 0 := by
    intro q
    by_cases hq : g q = u'
    · rw [separableDegreeWeightedFiberTerm_of_mem_fiber g (w ∘ j) hq]
      have hjy : f (j q) = y := by
        have h1 : f (j q) = U.toBase (g q) := by
          rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
        rw [h1, hq, hu'map]
      simp only [Function.comp_apply, hzero (j q) hjy, zero_mul]
    · exact separableDegreeWeightedFiberTerm_of_notMem_fiber g (w ∘ j) hq
  have hzeroAt : separableDegreeWeightedFiberSum g (w ∘ j) u' = 0 := by
    rw [separableDegreeWeightedFiberSum_eq_finsum_term]
    simp only [hterm, finsum_zero]
  exact (hu'spec.mem_open (hLC.isOpen_fiber (w x)) hcenter).symm.trans hzeroAt

/-- **Stacks Project, Tag 0H5P**, the step omitted in the source's converse, in the shape the
source uses it: over an irreducible base a weighting vanishing at every point of the source
above the generic point of the base is identically zero.

The source takes the base to be the spectrum of a discrete valuation ring, whose generic point
is a generalization of both of its points; irreducibility of the base is all that is used. -/
theorem IsWeighting.eq_zero_of_eq_zero_over_genericPoint {X Y : Scheme.{u}}
    [IrreducibleSpace Y] {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    {w : X → ℤ} (hw : IsWeighting f w)
    (hzero : ∀ x : X, f x = genericPoint ↥Y → w x = 0) : w = 0 := by
  funext x
  exact hw.eq_zero_of_specializes x (genericPoint_specializes (f x)) hzero

end AlgebraicGeometry

end
