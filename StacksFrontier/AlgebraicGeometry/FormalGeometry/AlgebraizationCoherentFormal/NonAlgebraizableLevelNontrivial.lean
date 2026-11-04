module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableChartSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizablePicard
public import StacksFrontier.AlgebraicGeometry.NormInvertible.CocycleTrivial
public import StacksFrontier.AlgebraicGeometry.PicardTrivialOpenUFD.Basic

/-!
# `𝓛₂` is not trivial, and no line bundle on an open of `Spec(A)` pulls back to it

The last two lines of the proof sketch of [Stacks, Tag 0EHE] are: an algebraizing coherent
module would be invertible near `U ∩ Y`, hence trivial there because `A = k[x,y][[t]]` is a
UFD, "which would imply `𝓛ₙ ≅ 𝒪_U/Iⁿ𝒪_U`. Since `𝓛₂ ≇ 𝒪_U/I²𝒪_U` by construction we get a
contradiction as desired." This file proves both halves of that.

**`𝓛₂ ≇ 𝒪`.** A trivialization of a module glued from a unit cocycle makes the cocycle a
coboundary (`Stacks.SheafOfModules.exists_units_overlapUnit_of_iso_unit`), so a trivialization
of `𝓛ₙ` produces a pair of invertible chart functions matched by the transition element —
an element of `Stacks.Algebraization.NonAlgebraizableExample.gluedSections` with invertible
components. At `n = 2` that is exactly what
`Stacks.Algebraization.NonAlgebraizableExample.not_isUnit_of_mem_gluedSections_two` forbids, for
every choice of the coefficients `aₘ` and the exponents `φ(m)`.

**Nothing on `Spec(A)` restricts to it.** Every invertible module on an open of `Spec(A)` is
trivial (`Stacks.Algebraization.NonAlgebraizableExample.isTrivial_of_isInvertible_ambientOpen`),
and pulling back a trivial module gives a trivial module, so no invertible module on an open
`V ⊆ Spec(A)` pulls back to `𝓛₂` along any morphism from the punctured spectrum of `A/t²A` to
`V`. The two morphisms the argument uses are
`Stacks.Algebraization.NonAlgebraizableExample.levelStructureMap` into `U` and its composite
with an open immersion into a smaller `V` containing `U ∩ Y`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.exists_isUnit_mem_gluedSections_of_iso_unit` —
  a trivialization of `𝓛ₙ` gives a pair of invertible chart functions matched by the transition
  element.
* `Stacks.Algebraization.NonAlgebraizableExample.not_isTrivial_levelModule_two` — **`𝓛₂` is not
  trivial**, for every choice of `a` and `φ`.
* `Stacks.Algebraization.NonAlgebraizableExample.not_nonempty_pullback_iso_levelModule_two` —
  **no invertible module on an open of `Spec(A)` pulls back to `𝓛₂`.**
* `Stacks.Algebraization.NonAlgebraizableExample.not_nonempty_pullback_levelStructureMap_iso` —
  the same for the structure map of the level-two punctured spectrum into `U`: the Picard class
  of `𝓛₂` is not in the image of `Pic(U)`.

## Implementation notes

The parameters `a` and `φ` are *unconstrained* in all of this, as they are in the source: the
obstruction lives modulo `t²`, where the transition element is `1 + t/(xy)` whatever `a` and `φ`
are (`Stacks.Algebraization.NonAlgebraizableExample.transitionElement_two`). The choice
`aₘ = 1`, `φ(m) = 2ᵐ` of the source's second paragraph is needed only for its *second* proof of
non-algebraizability, through the vanishing of `lim H⁰(U, 𝓛ₙ)`; see
`Stacks.Algebraization.NonAlgebraizableExample.sectionsLimit_eq_bot`.

The cancellation at the end is carried out on ring elements rather than on units: the unit
equation `u · g| = f|` on the overlap is read as an equation of chart functions, and the pair
exhibited is `(f⁻¹, g⁻¹)` — matching requires `h| = u · f|` with `f` the function on `D(x̄)`,
which is the equation for the inverses, not for `f` and `g` themselves.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- The overlap of the two charts is contained in the chart of `x̄`. -/
public theorem chartOpen_mul_le_left (n : ℕ) :
    chartOpen k (xVar k * yVar k) n ≤ chartOpen k (xVar k) n := by
  rw [chartOpen_mul]; exact inf_le_left

/-- The overlap of the two charts is contained in the chart of `ȳ`. -/
public theorem chartOpen_mul_le_right (n : ℕ) :
    chartOpen k (xVar k * yVar k) n ≤ chartOpen k (yVar k) n := by
  rw [chartOpen_mul]; exact inf_le_right

/-- **Stacks Project, Tag 0EHE (a trivialization of `𝓛ₙ` is a pair of invertible chart
functions).** If the glued module `𝓛ₙ` is isomorphic to the structure sheaf of the punctured
spectrum of `A/tⁿA`, then the transition element matches a pair consisting of an invertible
function on `D(x̄)` and an invertible function on `D(ȳ)`. -/
@[stacks 0EHE "a trivialization of L_n is a matched pair of invertible chart functions"]
public theorem exists_isUnit_mem_gluedSections_of_iso_unit (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (n : ℕ) (e : levelModule k a φ n ≅ Stacks.Ample.unitModule (levelOpen k n).toScheme) :
    ∃ s : chartRing k (xVar k) n × chartRing k (yVar k) n,
      s ∈ gluedSections k n (transitionElement k a φ n) ∧ IsUnit s.1 ∧ IsUnit s.2 := by
  obtain ⟨f, g, hfg⟩ := Stacks.SheafOfModules.exists_units_overlapUnit_of_iso_unit
    (X := (levelOpen k n).toScheme.toRingedSpace) (U₀ := levelChart k (xVar k) n)
    (U₁ := levelChart k (yVar k) n) (sup_levelChart k n) (levelOverlapUnit k a φ n) e
  obtain ⟨F, hF⟩ := (levelChartRingEquiv k (xVar k) n le_sup_left).surjective f.val
  obtain ⟨G, hG⟩ := (levelChartRingEquiv k (yVar k) n le_sup_right).surjective g.val
  have hFu : IsUnit F := (MulEquiv.isUnit_map _).1 (hF ▸ f.isUnit)
  have hGu : IsUnit G := (MulEquiv.isUnit_map _).1 (hG ▸ g.isUnit)
  have hu : (levelOverlapUnit k a φ n).val =
      levelOverlapRingEquiv k n (transitionElement k a φ n) := by
    show levelOverlapRingEquiv k n ((isUnit_transitionElement k a φ n).unit.val) = _
    rw [IsUnit.unit_spec]
  have hstar : transitionElement k a φ n * yChartToOverlap k n G = xChartToOverlap k n F := by
    refine (levelOverlapRingEquiv k n).injective ?_
    rw [map_mul,
      ← map_levelChartRingEquiv_overlap k (yVar k) n (dvd_mul_left _ _) le_sup_right
        (chartOpen_mul_le_right k n) inf_le_right G,
      ← map_levelChartRingEquiv_overlap k (xVar k) n (dvd_mul_right _ _) le_sup_left
        (chartOpen_mul_le_left k n) inf_le_left F,
      hF, hG, ← hu]
    have hval := congrArg Units.val hfg
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hval
    exact hval
  obtain ⟨p, hp⟩ := hFu.exists_left_inv
  obtain ⟨q, hq⟩ := hGu.exists_left_inv
  have hxF : IsUnit (xChartToOverlap k n F) := hFu.map _
  refine ⟨(p, q), ?_, ?_, ?_⟩
  · rw [mem_gluedSections_iff]
    refine hxF.mul_right_cancel ?_
    calc yChartToOverlap k n q * xChartToOverlap k n F
        = yChartToOverlap k n q * (transitionElement k a φ n * yChartToOverlap k n G) := by
          rw [hstar]
      _ = transitionElement k a φ n * yChartToOverlap k n (q * G) := by rw [map_mul]; ring
      _ = transitionElement k a φ n := by rw [hq, map_one, mul_one]
      _ = transitionElement k a φ n * xChartToOverlap k n (p * F) := by
          rw [hp, map_one, mul_one]
      _ = transitionElement k a φ n * xChartToOverlap k n p * xChartToOverlap k n F := by
          rw [map_mul]; ring
  · exact .of_mul_eq_one F hp
  · exact .of_mul_eq_one G hq

/-- **Stacks Project, Tag 0EHE (`𝓛₂ ≇ 𝒪`).** The glued module at order two is not trivial, for
every choice of the coefficients `aₘ` and the exponents `φ(m)`: a trivialization would match a
pair of invertible chart functions by the transition element `1 + t/(xy)`, and
`not_isUnit_of_mem_gluedSections_two` rules that out. This is the source's "`𝓛₂ ≇ 𝒪_U/I²𝒪_U` by
construction". -/
@[stacks 0EHE "L_2 is not isomorphic to the structure sheaf"]
public theorem not_isTrivial_levelModule_two (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) :
    ¬ Nonempty (levelModule k a φ 2 ≅ Stacks.Ample.unitModule (levelOpen k 2).toScheme) := by
  rintro ⟨e⟩
  obtain ⟨s, hs, hs1, hs2⟩ := exists_isUnit_mem_gluedSections_of_iso_unit k a φ 2 e
  exact not_isUnit_of_mem_gluedSections_two k a φ s hs ⟨hs1, hs2⟩

/-- **Stacks Project, Tag 0EHE (no line bundle on an open of `Spec(A)` pulls back to `𝓛₂`).**
Let `V` be an open subscheme of `Spec(A)`, `A = k[x,y][[t]]`, let `L` be an invertible
`𝒪_V`-module, and let `f` be any morphism from the punctured spectrum of `A/t²A` to `V`. Then
the pullback of `L` along `f` is not isomorphic to `𝓛₂`: the pullback is trivial, because `L`
itself is trivial — `A` being a UFD — and `𝓛₂` is not. -/
@[stacks 0EHE "no invertible module on an open of Spec(A) pulls back to L_2"]
public theorem not_nonempty_pullback_iso_levelModule_two (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    {V : (Spec (CommRingCat.of (AmbientRing k))).Opens}
    (f : (levelOpen k 2).toScheme ⟶ V.toScheme) (L : V.toScheme.Modules)
    (hL : Stacks.Ample.IsInvertibleModule V.toScheme L) :
    ¬ Nonempty ((Scheme.Modules.pullback f).obj L ≅ levelModule k a φ 2) := by
  rintro ⟨e⟩
  obtain ⟨eL⟩ := isTrivial_of_isInvertible_ambientOpen k L hL
  exact not_isTrivial_levelModule_two k a φ
    ⟨e.symm ≪≫ (Scheme.Modules.pullback f).mapIso eL ≪≫
      Stacks.PicardTrivialOpenUFD.pullbackUnitIso f⟩

/-- **Stacks Project, Tag 0EHE (the class of `𝓛₂` is not in the image of `Pic(U)`).** The
specialization of `not_nonempty_pullback_iso_levelModule_two` to the structure map of the
punctured spectrum of `A/t²A` over the punctured spectrum `U` of `A`: no invertible
`𝒪_U`-module restricts to `𝓛₂`. -/
@[stacks 0EHE "no invertible module on U restricts to L_2"]
public theorem not_nonempty_pullback_levelStructureMap_iso (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (L : (situation k).U.toScheme.Modules)
    (hL : Stacks.Ample.IsInvertibleModule (situation k).U.toScheme L) :
    ¬ Nonempty ((Scheme.Modules.pullback (levelStructureMap k 2)).obj L ≅ levelModule k a φ 2) :=
  not_nonempty_pullback_iso_levelModule_two k a φ (levelStructureMap k 2) L hL

end Stacks.Algebraization.NonAlgebraizableExample

end
