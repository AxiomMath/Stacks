module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleNeighborhoodBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullback

/-!
# The geometric length of the structure sheaf of a closed subspace, as a colength on a chart

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces, `z̄` a geometric point of `Z` and `A`
a small étale neighbourhood of `i(z̄)` in `X`. The base change `Z ×_X A` is a small étale
neighbourhood of `z̄` in `Z`, and the cartesian projection `j_A : Z ×_X A ⟶ A` is a closed
immersion of *schemes*. So the geometric length of `𝒪_Z` at `z̄` — which is what the
multiplicity of a component of a closed subspace is — becomes a colength of an ideal in the
local ring of the ambient chart:

  `length_{𝒪_{Z, z̄}}(𝒪_{Z, z̄})  =  length_{𝒪_{A, a}}(𝒪_{A, a} / 𝓘_a)`.

## Main results

* `AlgebraicGeometry.Space.snd_point_baseChange`: the chosen lift of `z̄` into `Z ×_X A`
  composes with the cartesian projection to the chosen lift of `i(z̄)` into `A`.
* `AlgebraicGeometry.Space.chartPoint_baseChange`: consequently the projection carries the
  marked point of `Z ×_X A` to the marked point of `A`.
* `AlgebraicGeometry.Space.length_chartLocalRing_baseChange`: the length of the chart local ring
  of the base-changed neighbourhood, over itself, is the colength in `𝒪_{A, a}` of the kernel of
  the stalk map of `j_A`.
The step from here to the geometric length of `𝒪_Z` at `z̄` is Stacks 0EE1 for the structure
sheaf, `AlgebraicGeometry.Space.length_etaleLocalRing_eq_length_chartLocalRing`, together with
one further identification that this library does not yet have: that
`AlgebraicGeometry.Space.geometricModuleStalk` of the unit module is the étale local ring, so
that `geometricLength _ _ (SheafOfModules.unit _)` is the length of the étale local ring over
itself.  That is an isomorphism of modules over a colimit and is not a definitional unfolding;
it is the one piece still between the results below and
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`.

## Implementation notes

The point compatibility is not a new fact: `AlgebraicGeometry.Space.smallBaseChangeFiberMap`
acts on lifts of a geometric point by composing with the cartesian projection, and
`AlgebraicGeometry.Space.smallBaseChangeFiberMap_smallBaseChangeFiberInv` says that the lift
`Z ×_X A` is given carries back to the lift `A` carries. Reading that equality of subtypes on
the underlying morphisms is exactly `snd_point_baseChange`.

From there `chartPoint_baseChange` is functoriality of `BigFppfOver.toScheme` plus the
observation that the point being pushed forward is the closed point of the spectrum of the
residue field of the geometric point, which is the same field for `z̄` and for `i(z̄)`; a
spectrum of a field is a subsingleton, so no compatibility of the chosen closed points is
needed.

The length statement is then `AlgebraicGeometry.length_stalk_self_eq_length_quotient_stalk_ker`
for the scheme-level closed immersion `j_A`, whose `IsClosedImmersion` instance is
`hi.property_snd` — the representability of `i` evaluated at the chart, which is the same
morphism `AlgebraicGeometry.Space.definingIdealAt_eq_ker` is stated against.

No quasi-coherence hypothesis appears anywhere below, because the module whose length is taken
is the structure sheaf of `Z` itself rather than a pushforward of it to `X`.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X : AlgebraicSpaces B S hS}

/-- **The chosen lift into a base-changed chart projects to the chosen lift.** -/
theorem snd_point_baseChange (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom)
    (z : GeometricPoint B S hS Z.1)
    (A : SmallEtaleNeighborhood (geometricPointMap i.hom z)) :
    ((SmallEtaleNeighborhood.baseChange B S hS i hi z).obj A).point ≫
        hi.snd A.chart.1.hom = A.point :=
  congrArg Subtype.val
    (smallBaseChangeFiberMap_smallBaseChangeFiberInv B S hS i hi z A.chart
      ⟨A.point, A.point_comp⟩)

/-- **The cartesian projection carries the marked point of the base-changed chart to the marked
point of the chart.** -/
theorem chartPoint_baseChange (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom)
    (z : GeometricPoint B S hS Z.1)
    (A : SmallEtaleNeighborhood (geometricPointMap i.hom z)) :
    ((BigFppfOver.toScheme B S hS).map (hi.snd A.chart.1.hom)).base
        (chartPoint B S hS Z.1 ((SmallEtaleNeighborhood.baseChange B S hS i hi z).obj A)) =
      chartPoint B S hS X.1 A := by
  have hcomp := snd_point_baseChange B S hS i hi z A
  have hmap : (BigFppfOver.toScheme B S hS).map
        (((SmallEtaleNeighborhood.baseChange B S hS i hi z).obj A).point ≫
          hi.snd A.chart.1.hom) =
      (BigFppfOver.toScheme B S hS).map
          ((SmallEtaleNeighborhood.baseChange B S hS i hi z).obj A).point ≫
        (BigFppfOver.toScheme B S hS).map (hi.snd A.chart.1.hom) :=
    (BigFppfOver.toScheme B S hS).map_comp _ _
  have hA := (congrArg (BigFppfOver.toScheme B S hS).map hcomp).symm.trans hmap
  show ((BigFppfOver.toScheme B S hS).map
      ((SmallEtaleNeighborhood.baseChange B S hS i hi z).obj A).point ≫
      (BigFppfOver.toScheme B S hS).map (hi.snd A.chart.1.hom)).base _ = _
  rw [← hA]
  exact congrArg ((BigFppfOver.toScheme B S hS).map A.point).base
    (Subsingleton.elim (α := PrimeSpectrum (geometricPointMap i.hom z).val.carrier) _ _)

/-- **The length of the chart local ring of a base-changed neighbourhood is a colength in the
ambient chart's local ring**, the ideal being the stalk of the ideal sheaf of the closed
immersion of chart schemes.

Here `a` is the point of the ambient chart scheme which, by `ha`, is the image of the marked
point of the base change; `AlgebraicGeometry.Space.chartPoint_baseChange` supplies `ha` when `a`
is the marked point of `A`. -/
theorem length_chartLocalRing_baseChange (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (z : GeometricPoint B S hS Z.1)
    (A : SmallEtaleNeighborhood (geometricPointMap i.hom z))
    (a : chartScheme A.chart)
    (ha : ((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.chart.1.hom)).base
      (chartPoint B S hS Z.1
        ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj A)) = a)
    (U : (chartScheme A.chart).Opens) (hU : IsAffineOpen U) (hmem : a ∈ U) :
    letI : AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.chart.1.hom)) :=
      hi.property_snd A.chart.1.hom
    Module.length
        ↥(chartLocalRing B S hS Z.1
          ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj A))
        ↥(chartLocalRing B S hS Z.1
          ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj A)) =
      Module.length ↥((chartScheme A.chart).presheaf.stalk a)
        (↥((chartScheme A.chart).presheaf.stalk a) ⧸
          AlgebraicGeometry.IdealSheafData.stalk
            ((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.chart.1.hom)).ker a) := by
  let : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.chart.1.hom)) :=
    hi.property_snd A.chart.1.hom
  subst ha
  exact AlgebraicGeometry.length_stalk_self_eq_length_quotient_stalk_ker
    ((BigFppfOver.toScheme B S hS).map (hi.rep.snd A.chart.1.hom))
    (chartPoint B S hS Z.1 ((SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj A))
    U hU hmem

end AlgebraicGeometry.Space

end
