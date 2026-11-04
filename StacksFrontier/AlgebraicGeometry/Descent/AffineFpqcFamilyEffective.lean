module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityGluingCompat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective fpqc descent for affine morphisms

Let `S` be a scheme, let `{X i ⟶ S}` be a covering family of `S` for the fpqc topology, and let
`D` be a descent datum relative to that family all of whose structure morphisms `V i ⟶ X i` are
affine. Then `D` is effective: it is isomorphic to the canonical descent datum of a scheme over
`S`.

## Main results

* `AlgebraicGeometry.DescentData.nonempty_chart_of_restrictBase_isFamilyEffective`: a descent
  datum relative to a covering family for the fpqc topology whose restriction to every affine
  open of the base is effective carries a chart in the sense of
  `AlgebraicGeometry.DescentData.Chart`: a scheme over `S` exhibiting every component of the
  datum as its base change, compatibly with the gluing isomorphisms.
* `AlgebraicGeometry.DescentData.nonempty_chart_of_isAffineHom`: a datum whose structure
  morphisms are affine carries a chart.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom`: a datum whose structure
  morphisms are affine is effective.

## Implementation notes

Effectivity is deduced from the existence of a chart
(`AlgebraicGeometry.DescentData.Chart.isFamilyEffective`). Over each affine open `U` of `S` the
restricted datum is effective, by
`AlgebraicGeometry.DescentData.isFamilyEffective_restrictBase_of_isAffineHom`, which gives a chart
over `U`; these charts are glued along the affine opens of `S` into a single scheme over `S`,
together with the projections of the components of the datum onto it
(`AlgebraicGeometry.DescentData.globalProj`).

The covering family is indexed in the universe of the schemes.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits MorphismOfSchemeFamilies

namespace DescentData

variable {S : Scheme.{u}} {𝒰 : PreZeroHypercover.{u} S}
  (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S) (D : DescentData 𝒰.f)

section

variable (hD : ∀ U : S.affineOpens, ((MorphismOfSchemeFamilies.pullbackFunctor
  (MorphismOfSchemeFamilies.ofRestrictBase 𝒰 U.1)).functor.obj D).IsFamilyEffective)

include h𝒰 hD in
/-- **A descent datum relative to a covering family for the fpqc topology whose restriction to
every affine open of the base is effective carries a chart**: a scheme over the base exhibiting
every component of the datum as its base change, compatibly with the gluing isomorphisms. -/
theorem nonempty_chart_of_restrictBase_isFamilyEffective : Nonempty D.Chart := by
  obtain ⟨Y, p, c, hc, hcres⟩ := exists_glued_chart h𝒰 D hD
  exact ⟨{ base := Over.mk p
           proj := globalProj h𝒰 D hD c hcres
           isPullback := isPullback_globalProj h𝒰 D hD p c hcres hc
           compat := compat_globalProj h𝒰 D hD c hcres }⟩

end

variable (hD : ∀ i, IsAffineHom (D.obj i).hom)

include h𝒰 hD in
/-- **A descent datum relative to a covering family for the fpqc topology whose structure
morphisms are affine carries a chart**: a scheme over the base exhibiting every component of the
datum as its base change, compatibly with the gluing isomorphisms. -/
theorem nonempty_chart_of_isAffineHom : Nonempty D.Chart :=
  nonempty_chart_of_restrictBase_isFamilyEffective h𝒰 D
    fun U ↦ isFamilyEffective_restrictBase_of_isAffineHom h𝒰 D hD U.1 U.2

end DescentData

/-- Let `S` be a scheme, let `{X i ⟶ S}` be a covering family of `S` for the fpqc topology, and
let `D` be a descent datum relative to that family all of whose structure morphisms `V i ⟶ X i`
are affine. Then `D` is effective: it is isomorphic to the canonical descent datum of a scheme over
`S`. -/
@[stacks 0245 "for a covering family indexed in the universe of the schemes",
  sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "more general",
  sga "3 X 5.4" "special case",
  sga "3 XXIV 3.11.2" "partial"]
theorem DescentData.isFamilyEffective_of_isAffineHom {S : Scheme.{u}} {I : Type u}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S) (D : DescentData f)
    (hD : ∀ i, IsAffineHom (D.obj i).hom) :
    D.IsFamilyEffective :=
  (DescentData.nonempty_chart_of_isAffineHom (𝒰 := ⟨I, X, f⟩) hf D hD).elim
    fun C ↦ C.isFamilyEffective

end AlgebraicGeometry

end

end
