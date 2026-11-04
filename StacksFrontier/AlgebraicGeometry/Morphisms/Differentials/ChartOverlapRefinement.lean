module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections

/-!
# Refining the overlap of two affine charts of a fibre product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes. The affine charts of `X ×_S Y` are the
opens `pr₁⁻¹U ∩ pr₂⁻¹V` for affine opens `U ⊆ X`, `V ⊆ Y` lying over an affine open of `S`; they
are not a basis of the topology, since inside such a chart the principal open of a section of
`Γ(X, U) ⊗ Γ(Y, V)` is not of that shape. The overlap of two charts is, however, covered by charts
whose two factors are principal opens of the factors of *both* charts at once, and the range of
such a chart is a principal open of each of the two charts. For a quasi-coherent module the
sections over it are therefore the localization of the sections over either chart.

## Main definitions

* `Stacks.FibreProductAffineChart.Chart.basicOpenChart`: the chart cut out of a chart by a section
  of the structure sheaf on each of its two factors.
* `Stacks.FibreProductAffineChart.Chart.basicOpenSection`: the section of the structure sheaf of
  `X ×_S Y` over a chart whose principal open is that smaller chart.

## Main results

* `Stacks.FibreProductAffineChart.Chart.isAffineOpen_opensRange_ι`: the range of a chart is an
  affine open.
* `Stacks.FibreProductAffineChart.Chart.basicOpen_basicOpenSection`: the range of
  `Chart.basicOpenChart` is the principal open of `Chart.basicOpenSection` in `X ×_S Y`.
* `Stacks.FibreProductAffineChart.Chart.isLocalizedModule_restriction_basicOpenSection`:
  restriction of the sections of a quasi-coherent module from a chart to the smaller chart realizes
  them as the localization away from `Chart.basicOpenSection`.
* `Stacks.FibreProductAffineChart.Chart.exists_basicOpenChart_mem_inter`: a point in the overlap of
  two charts lies in a chart which is cut out of each of the two by sections of the structure sheaf
  on their factors.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry CommRingCat

namespace Stacks.FibreProductAffineChart

universe u

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

/-- The range of a chart is an affine open of the fibre product. -/
theorem isAffineOpen_opensRange_ι : IsAffineOpen c.ι.opensRange :=
  isAffineOpen_opensRange c.ι

variable (f : Γ(X, c.left)) (g : Γ(Y, c.right))

/-- The chart cut out of a chart by a section `f` of the structure sheaf of `X` on its first factor
and a section `g` on its second factor: the two factors are shrunk to their principal opens, the
base is unchanged. -/
def basicOpenChart : Chart a b where
  base := c.base
  left := X.basicOpen f
  right := Y.basicOpen g
  isAffineOpen_base := c.isAffineOpen_base
  isAffineOpen_left := c.isAffineOpen_left.basicOpen f
  isAffineOpen_right := c.isAffineOpen_right.basicOpen g
  le_left := (X.basicOpen_le f).trans c.le_left
  le_right := (Y.basicOpen_le g).trans c.le_right

/-- The range of `Stacks.FibreProductAffineChart.Chart.basicOpenChart`. -/
theorem opensRange_basicOpenChart :
    (c.basicOpenChart f g).ι.opensRange =
      pullback.fst a b ⁻¹ᵁ X.basicOpen f ⊓ pullback.snd a b ⁻¹ᵁ Y.basicOpen g :=
  opensRange_ι _

/-- The chart cut out by two sections is contained in the chart it is cut out of. -/
theorem opensRange_basicOpenChart_le :
    (c.basicOpenChart f g).ι.opensRange ≤ c.ι.opensRange := by
  rw [opensRange_basicOpenChart, c.opensRange_ι]
  exact inf_le_inf (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
    (Scheme.Hom.preimage_mono _ (Y.basicOpen_le g))

/-- The section of the structure sheaf of `X ×_S Y` over a chart which cuts out the chart
`Stacks.FibreProductAffineChart.Chart.basicOpenChart`: the product of the restrictions of the
inverse images of `f` and of `g` under the two projections. -/
def basicOpenSection : Γ(pullback a b, c.ι.opensRange) :=
  (pullback a b).presheaf.map (homOfLE (c.opensRange_ι.le.trans inf_le_left)).op
      ((pullback.fst a b).app c.left f) *
    (pullback a b).presheaf.map (homOfLE (c.opensRange_ι.le.trans inf_le_right)).op
      ((pullback.snd a b).app c.right g)

/-- **The chart cut out by two sections is a principal open of the chart.** -/
theorem basicOpen_basicOpenSection :
    (pullback a b).basicOpen (c.basicOpenSection f g) =
      (c.basicOpenChart f g).ι.opensRange := by
  rw [basicOpenSection, Scheme.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res,
    ← Scheme.preimage_basicOpen, ← Scheme.preimage_basicOpen, inf_inf_inf_comm, inf_idem,
    ← c.opensRange_basicOpenChart f g, inf_eq_right]
  exact c.opensRange_basicOpenChart_le f g

/-- **The sections of a quasi-coherent module on the chart cut out by two sections are a
localization.** Restriction from a chart to the principal open of
`Stacks.FibreProductAffineChart.Chart.basicOpenSection` realizes the sections of a quasi-coherent
module over the smaller chart as the localization of the sections over the chart away from that
section. -/
theorem isLocalizedModule_restriction_basicOpenSection (M : (pullback a b).Modules)
    [M.IsQuasicoherent] :
    letI : Module Γ(pullback a b, c.ι.opensRange)
        Γ(M, (pullback a b).basicOpen (c.basicOpenSection f g)) :=
      Module.compHom _ ((pullback a b).presheaf.map
        (homOfLE ((pullback a b).basicOpen_le (c.basicOpenSection f g))).op).hom
    IsLocalizedModule.Away (c.basicOpenSection f g)
      (Scheme.Modules.restrictionLinearMap M
        (homOfLE ((pullback a b).basicOpen_le (c.basicOpenSection f g)))) :=
  isLocalizedModule_restriction_basicOpen_of_qcqs M c.isAffineOpen_opensRange_ι.isCompact
    c.isAffineOpen_opensRange_ι.isQuasiSeparated (c.basicOpenSection f g)

/-- **The overlap of two charts is covered by charts cut out of both of them.** A point lying in
two charts lies in a chart whose two factors are principal opens of the corresponding factors of
each of the two charts; the two descriptions have the same range. -/
theorem exists_basicOpenChart_mem_inter (c c' : Chart a b) (p : ↥(pullback a b))
    (hc : p ∈ c.ι.opensRange) (hc' : p ∈ c'.ι.opensRange) :
    ∃ (f : Γ(X, c.left)) (g : Γ(Y, c.right)) (f' : Γ(X, c'.left)) (g' : Γ(Y, c'.right)),
      X.basicOpen f = X.basicOpen f' ∧ Y.basicOpen g = Y.basicOpen g' ∧
        p ∈ (c.basicOpenChart f g).ι.opensRange ∧
        (c.basicOpenChart f g).ι.opensRange = (c'.basicOpenChart f' g').ι.opensRange := by
  rw [c.opensRange_ι] at hc
  rw [c'.opensRange_ι] at hc'
  obtain ⟨f, f', hf, hfp⟩ := exists_basicOpen_le_affine_inter c.isAffineOpen_left
    c'.isAffineOpen_left ((pullback.fst a b).base p) ⟨hc.1, hc'.1⟩
  obtain ⟨g, g', hg, hgp⟩ := exists_basicOpen_le_affine_inter c.isAffineOpen_right
    c'.isAffineOpen_right ((pullback.snd a b).base p) ⟨hc.2, hc'.2⟩
  refine ⟨f, g, f', g', hf, hg, mem_range_ι _ p hfp hgp, ?_⟩
  rw [opensRange_basicOpenChart, opensRange_basicOpenChart, hf, hg]

end Chart

end Stacks.FibreProductAffineChart

end
