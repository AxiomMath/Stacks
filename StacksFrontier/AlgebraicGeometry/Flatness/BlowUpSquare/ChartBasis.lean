module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.AffineChartRestrict
import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexCharts

/-!
# The affine opens carrying a chart form a basis of the topology

Let `(X, D, M)` be a triple as in Situation 0F8S. Every point of `X` lies in the domain of an
affine chart for the triple, and that domain may be taken inside any prescribed open neighbourhood
of the point, so the domains of the affine charts form a basis of the topology of `X`. Shrinking a
chart is `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.restrictBasicOpen`, the chart
over a standard open `D(g) ⊆ U` of the domain of a chart.

On a chart whose domain misses the support of `D` the determinantal ideals `I_i(M^•, f)` are the
unit ideal, so every point off the divisor lies in the domain of a chart whose determinantal ideals
are principal.

## Main results

* `AffineChart.exists_mem_le`: a chart whose domain meets a given open `W` at `x` restricts to a
  chart whose domain contains `x` and lies inside `W`.
* `exists_chart_mem_le`: every point of `X` lies in the domain of a chart whose domain is contained
  in any prescribed open neighbourhood of the point.
* `exists_chart_mem`: every point of `X` lies in the domain of a chart.
* `isTopologicalBasis_chartOpens`: the domains of the charts form a basis of the topology of `X`.
* `AffineChart.determinantalIdeal_eq_top_of_ideal_eq_top` and
  `AffineChart.isPrincipal_determinantalIdeal_of_ideal_eq_top`: on a chart whose domain misses the
  divisor the determinantal ideals `I_i(M^•, f)` are the unit ideal, hence principal.
* `exists_chart_isPrincipal_determinantalIdeal_of_notMem_supportSet`: every point off the divisor
  lies in the domain of a chart with principal determinantal ideals.

## Implementation notes

The object `M` of the situation lives in whatever model of the derived category of `𝒪_X`-modules
the situation carries, whereas
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_affineChart_ofPerfect` is stated at the
standard model. `CategoryTheory.Localization.uniq` carries `M` between the two —
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj` carries its
perfectness — and the equivalence, being fully faithful, carries the resulting identification of
the representing complex back, which is what the `represents` field of a chart of the situation
asks for.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : ComplexAndDivisorSituation.{u, d}}

/-! ### Shrinking a chart -/

namespace AffineChart

/-- **A chart may be shrunk into any open neighbourhood of a point of its domain.** If `x` lies in
the domain of a chart `C` and in an open `W`, then some chart has `x` in its domain and has its
domain inside `W`. -/
theorem exists_mem_le (C : AffineChart S) {W : S.X.Opens} {x : S.X}
    (hxC : x ∈ (C.U : Set S.X)) (hxW : x ∈ W) :
    ∃ C' : AffineChart S, x ∈ (C'.U : Set S.X) ∧ (C'.U : S.X.Opens) ≤ W := by
  obtain ⟨g, hgle, hxg⟩ := C.U.2.exists_basicOpen_le
    (⟨x, ⟨hxW, hxC⟩⟩ : (W ⊓ (C.U : S.X.Opens) : S.X.Opens)) hxC
  refine ⟨C.restrictBasicOpen g, ?_, ?_⟩
  · simpa using hxg
  · simpa using hgle.trans inf_le_left

end AffineChart

/-! ### Producing a chart around a point -/

/-- A generator of the ideal of an ideal sheaf on an affine open restricts to a generator of its
ideal on a smaller affine open. -/
private theorem ideal_eq_span_map {X : Scheme.{u}} (I : X.IdealSheafData) {U V : X.affineOpens}
    (h : (U : X.Opens) ≤ (V : X.Opens)) {g : Γ(X, (V : X.Opens))}
    (hg : I.ideal V = Ideal.span {g}) :
    I.ideal U = Ideal.span {(X.presheaf.map (homOfLE h).op) g} := by
  rw [← Scheme.IdealSheafData.map_ideal I h, hg, Ideal.map_span, Set.image_singleton]
  rfl

/-- **A chart around every point, inside any prescribed neighbourhood.** Every point `x` of `X`
lies in the domain of an affine chart for the triple `(X, D, M)`, and the domain may be taken
inside any open neighbourhood `W` of `x`. -/
theorem exists_chart_mem_le (S : ComplexAndDivisorSituation.{u, d}) (x : S.X) (W : S.X.Opens)
    (hxW : x ∈ W) :
    ∃ C : AffineChart S, x ∈ (C.U : Set S.X) ∧ (C.U : S.X.Opens) ≤ W := by
  obtain ⟨U₀, hU₀, hxU₀, f₀, hf₀, hspan₀⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor S.D
      S.isEffectiveCartierDivisor x
  let Q₂ := @DerivedCategory.Q _ _ _
    (HasDerivedCategory.standard (OXMod.{u, u} S.X.toRingedSpace))
  let qis := HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace) (ComplexShape.up ℤ)
  let L := Localization.uniq (@DerivedCategory.Q _ _ _ S.hasDerivedCategory) Q₂ qis
  have hperf : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (L.functor.obj S.M) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj S.hasDerivedCategory
      (HasDerivedCategory.standard (OXMod.{u, u} S.X.toRingedSpace)) S.M S.isPerfect
  obtain ⟨C, hxC, hCle⟩ := exists_affineChart_ofPerfect hperf x (W ⊓ U₀) ⟨hxW, hxU₀⟩
  have hCU₀ : (C.U : S.X.Opens) ≤ U₀ := hCle.trans inf_le_right
  obtain ⟨E, ⟨hE⟩, hrest⟩ := C.represents
  refine ⟨{ U := C.U
            f := (S.X.presheaf.map (homOfLE hCU₀).op) f₀
            regular := IsAffineOpen.isRegular_presheaf_map_of_le hU₀ C.U.2 hCU₀ hf₀
            divisor_ideal := ideal_eq_span_map S.D (V := ⟨U₀, hU₀⟩) hCU₀ hspan₀
            complex := C.complex
            represents := ⟨E, ⟨?_⟩, hrest⟩ },
    hxC, hCle.trans inf_le_left⟩
  exact L.functor.preimageIso
    ((Localization.compUniqFunctor (@DerivedCategory.Q _ _ _ S.hasDerivedCategory) Q₂ qis).app E
      ≪≫ hE)

/-- **Every point of `X` lies in the domain of an affine chart for the triple.** -/
theorem exists_chart_mem (S : ComplexAndDivisorSituation.{u, d}) (x : S.X) :
    ∃ C : AffineChart S, x ∈ (C.U : Set S.X) := by
  obtain ⟨C, hxC, -⟩ := S.exists_chart_mem_le x ⊤ trivial
  exact ⟨C, hxC⟩

/-! ### The basis -/

/-- **The domains of the charts form a basis of the topology of `X`.** -/
theorem isTopologicalBasis_chartOpens (S : ComplexAndDivisorSituation.{u, d}) :
    IsTopologicalBasis (Set.range fun C : AffineChart S => (C.U : Set S.X)) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨C, rfl⟩
    exact (C.U : S.X.Opens).isOpen
  · intro x O hxO hO
    obtain ⟨C, hxC, hle⟩ := S.exists_chart_mem_le x ⟨O, hO⟩ hxO
    exact ⟨(C.U : Set S.X), ⟨C, rfl⟩, hxC, hle⟩

/-! ### Charts off the divisor -/

namespace AffineChart

/-- **A chart whose domain misses the divisor has unit determinantal ideals.** If the ideal of `D`
on the domain of a chart `C` is the unit ideal, then so is each determinantal ideal `I_i(M^•, f)`
of `C`. -/
theorem determinantalIdeal_eq_top_of_ideal_eq_top (C : AffineChart S)
    (h : S.D.ideal C.U = ⊤) (i : ℤ) : C.determinantalIdeal i = ⊤ := by
  have hu : IsUnit C.f := by
    rw [← Ideal.span_singleton_eq_top, ← C.divisor_ideal, h]
  exact Ideal.eq_top_of_isUnit_mem _ (C.pow_rank_mem_determinantalIdeal i) (hu.pow _)

/-- The determinantal ideals of a chart whose domain misses the divisor are principal. -/
theorem isPrincipal_determinantalIdeal_of_ideal_eq_top (C : AffineChart S)
    (h : S.D.ideal C.U = ⊤) (i : ℤ) : (C.determinantalIdeal i).IsPrincipal := by
  rw [C.determinantalIdeal_eq_top_of_ideal_eq_top h i]
  exact ⟨1, by simp⟩

end AffineChart

/-- **Off the divisor every point lies in a chart with principal determinantal ideals.** A point
outside the support of `D` lies in the domain of a chart all of whose determinantal ideals are
principal. -/
theorem exists_chart_isPrincipal_determinantalIdeal_of_notMem_supportSet
    (S : ComplexAndDivisorSituation.{u, d}) {x : S.X} (hx : x ∉ S.D.supportSet) :
    ∃ C : AffineChart S, x ∈ (C.U : Set S.X) ∧
      ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal := by
  obtain ⟨V, hxV, hV⟩ :=
    Stacks.CartierAffineLocalConverse.exists_affineOpen_ideal_eq_top S.D hx
  obtain ⟨C, hxC, hCV⟩ := S.exists_chart_mem_le x V.1 hxV
  have htop : S.D.ideal C.U = ⊤ := by
    rw [← Scheme.IdealSheafData.map_ideal S.D (U := C.U) (V := V) hCV, hV, Ideal.map_top]
  exact ⟨C, hxC, fun i => C.isPrincipal_determinantalIdeal_of_ideal_eq_top htop i⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
