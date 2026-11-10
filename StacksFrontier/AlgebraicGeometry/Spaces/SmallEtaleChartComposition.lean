module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartRingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.CompositionOfLocallyRingedMorphisms

/-!
# The composition law for the chart morphisms of a morphism of small étale ringed topoi

Let `ψ : (Sh(P_étale), 𝒪_P) ⟶ (Sh(Q_étale), 𝒪_Q)` and
`χ : (Sh(Q_étale), 𝒪_Q) ⟶ (Sh(R_étale), 𝒪_R)` be morphisms of the small étale ringed topoi of
algebraic spaces over a base scheme `S`.  A section `t` over an étale chart `V` of `Q` of
`χ⁻¹h_W` and a section `s` over an étale chart `U` of `P` of `ψ⁻¹h_V` together produce a section
of `(χ ∘ ψ)⁻¹h_W` over `U`, and the chart morphism of schemes attached to that section is the
composite of the two chart morphisms:

  `f_{t ∘ s} = f_s ≫ f_t : U ⟶ V ⟶ W`.

This is the composition law for `AlgebraicGeometry.Space.chartSchemeHom`, recorded as missing by
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/RecoveryFromChartBase.lean` and by the
docstring of `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`.  It is one of the two things
those two files name as standing between the 2-compatibility hypothesis of
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` — which is stated with
`AlgebraicGeometry.Space.smallEtaleComp`, the composite used here — and
`AlgebraicGeometry.Space.IsChartOverBase`, from which Tag 04KL over a base follows by
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_isChartOverBase`.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionComp`: the section of `(χ ∘ ψ)⁻¹h_W` over `U` built from
  `t` and `s`.

## Main results

* `AlgebraicGeometry.Space.invCoord_smallEtaleComp`: the coordinate map of a composite is the
  inverse image under `ψ⁻¹` of the coordinate map of `χ`, followed by the structure map of `ψ`.
* `AlgebraicGeometry.Space.chartRingHom_smallEtaleComp`: the composition law on global
  functions, for arbitrary charts.
* `AlgebraicGeometry.Space.chartSchemeHom_smallEtaleComp`: the composition law for the chart
  morphisms of schemes, for affine charts of the two targets.

## Implementation notes

The ring-level law needs no affineness: it is the identity
`b ↦ (χ ∘ ψ)♯((χ ∘ ψ)⁻¹(b)(t ∘ s)) = ψ♯(ψ⁻¹(χ♯(χ⁻¹(b)(t)))(s))`, which comes out of
`AlgebraicGeometry.RingedToposHom.fSharpSet_comp` — the structure map of a composite in
inverse-image form — together with the naturality in the sheaf of the Yoneda bijection of a
subcanonical topology.  Affineness of the two targets enters only in passing from the ring map
to the morphism of schemes it induces, which is where
`AlgebraicGeometry.Space.chartSchemeHom` is defined.

The composite is spelled `AlgebraicGeometry.Space.smallEtaleComp` rather than
`AlgebraicGeometry.RingedToposHom.comp`: the universe parameters of a morphism of ringed topoi
between the small étale ringed topoi of algebraic spaces are not inferable from the composite's
arguments, and naming the three ringed topoi is what pins them down.  It is also the spelling in
which the 2-compatibility of `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` is stated.

The composite section `AlgebraicGeometry.Space.chartSectionComp` is the evaluation at `s` of
`ψ⁻¹` applied to the map `h_V ⟶ χ⁻¹h_W` that `t` is.  Its type typechecks on the nose because
the inverse image of a composite morphism of topoi is the composite of the inverse images, which
is a field of `CategoryTheory.MorphismOfTopoi.comp`.

What this does *not* do is relate `chartSectionComp` to an arbitrary section of
`(χ ∘ ψ)⁻¹h_W` over `U`: such a section need only factor through a chart of `Q` étale-locally on
`U`, so reading a 2-isomorphism of `χ ∘ ψ` with a third morphism at the charts needs that local
factorization as well.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P Q R : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

variable (χ : RingedToposHom (smallEtaleRingedTopos B S hS Q) (smallEtaleRingedTopos B S hS R))
  (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q))

/-- **The composite of two chart sections.** A section `t` over an étale chart `V` of `Q` of
`χ⁻¹h_W` is a map `h_V ⟶ χ⁻¹h_W`; applying `ψ⁻¹` to it and evaluating at a section `s` over an
étale chart `U` of `P` of `ψ⁻¹h_V` gives a section of `(χ ∘ ψ)⁻¹h_W` over `U`. -/
def chartSectionComp (W : SmallEtale B S hS R.1) (V : SmallEtale B S hS Q.1)
    (U : SmallEtale B S hS P.1) (t : (invRep χ W).obj.obj (op V))
    (s : (invRep ψ V).obj.obj (op U)) :
    (invRep (smallEtaleComp B S hS χ ψ) W).obj.obj (op U) :=
  (ψ.toToposHom.inverseImage.map
    ((SmallEtale.topology B S hS Q.1).yonedaEquiv.symm t)).hom.app (op U) s

/-- **The coordinate map of a composite.** For a regular function `b` on an étale chart `W` of
`R`, the map `(χ ∘ ψ)⁻¹h_W ⟶ 𝒪_P` attached to `b` is the inverse image under `ψ⁻¹` of the map
`χ⁻¹h_W ⟶ 𝒪_Q` attached to `b`, followed by the inverse-image form of the structure map of
`ψ`. -/
theorem invCoord_smallEtaleComp (W : SmallEtale B S hS R.1) (b : (setO R).obj.obj (op W)) :
    invCoord (smallEtaleComp B S hS χ ψ) W b =
      ψ.toToposHom.inverseImage.map (invCoord χ W b) ≫ ψ.fSharpSet := by
  rw [invCoord, invCoord, Functor.map_comp, Category.assoc]
  exact congrArg (fun m ↦ ψ.toToposHom.inverseImage.map
    (χ.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS R.1).yonedaEquiv.symm b)) ≫ m)
    (RingedToposHom.fSharpSet_comp χ ψ)

/-- **The composition law on global functions.** The ring map attached to the composite section
`AlgebraicGeometry.Space.chartSectionComp` is the ring map of `χ` at `t` followed by the ring map
of `ψ` at `s`. -/
theorem chartRingHom_smallEtaleComp (W : SmallEtale B S hS R.1) (V : SmallEtale B S hS Q.1)
    (U : SmallEtale B S hS P.1) (t : (invRep χ W).obj.obj (op V))
    (s : (invRep ψ V).obj.obj (op U)) :
    chartRingHom (smallEtaleComp B S hS χ ψ) W U (chartSectionComp χ ψ W V U t s) =
      chartRingHom χ W V t ≫ chartRingHom ψ V U s := by
  ext b
  change (chartRingHom (smallEtaleComp B S hS χ ψ) W U (chartSectionComp χ ψ W V U t s)).hom b =
    (chartRingHom ψ V U s).hom ((chartRingHom χ W V t).hom b)
  rw [chartRingHom_apply (smallEtaleComp B S hS χ ψ) W U (chartSectionComp χ ψ W V U t s) b,
    chartRingHom_apply χ W V t b,
    chartRingHom_apply ψ V U s ((invCoord χ W b).hom.app (op V) t),
    invCoord_smallEtaleComp χ ψ W b]
  change ((ψ.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Q.1).yonedaEquiv.symm t) ≫
        ψ.toToposHom.inverseImage.map (invCoord χ W b) ≫ ψ.fSharpSet)).hom.app (op U) s = _
  rw [← Category.assoc, ← Functor.map_comp,
    (SmallEtale.topology B S hS Q.1).yonedaEquiv_symm_naturality_right V (invCoord χ W b) t]
  rfl

/-- **The composition law for the chart morphisms of schemes.** For affine étale charts `W` of
`R` and `V` of `Q`, the morphism of schemes attached to the composite section
`AlgebraicGeometry.Space.chartSectionComp` is the composite `U ⟶ V ⟶ W` of the two chart
morphisms. -/
theorem chartSchemeHom_smallEtaleComp (W : SmallEtale B S hS R.1) [IsAffine (chartSch W)]
    (V : SmallEtale B S hS Q.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS P.1)
    (t : (invRep χ W).obj.obj (op V)) (s : (invRep ψ V).obj.obj (op U)) :
    chartSchemeHom (smallEtaleComp B S hS χ ψ) W U (chartSectionComp χ ψ W V U t s) =
      chartSchemeHom ψ V U s ≫ chartSchemeHom χ W V t := by
  apply ext_of_isAffine
  rw [chartSchemeHom_appTop, Scheme.Hom.comp_appTop, chartSchemeHom_appTop,
    chartRingHom_smallEtaleComp, ← chartSchemeHom_appTop ψ V U s]

end AlgebraicGeometry.Space
