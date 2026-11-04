module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOne

/-!
# `θ` of Stacks 0D2Z on `U(ψ)` from a compatible family at the scheme points: clauses (1) and (3)

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849, the map `θ` of [Stacks, Tag 0D2Z] on the algebraic space `U(ψ)` is
descended, degree by degree, from a compatible family `χ_w` of maps indexed by the scheme points
`w : W ⟶ U(ψ)` (`AlgebraicGeometry.Space.pointFamilyDescendedHom` along a presentation of
`U(ψ)`); the family the source uses is the family of chart maps of `θ` of
[Stacks, Tag 01O9] on the schemes `W`
(`…InvertibleTwistingRestriction.chartMap`).

This file records the two clauses of the tag that only use the descent, for an arbitrary
compatible family:

* **Clause (1)** is a triangle through `θ` out of the quasi-coherent module `π_{U(ψ)}^*𝒜_d`
  (`…InvertibleTwistingRestriction.ClauseOneHom`), so it holds as soon as it holds after
  restriction to every scheme point `w`, with `χ_w` in place of `θ`
  (`AlgebraicGeometry.Space.comp_pointFamilyDescendedHom_eq`); the section form the tag states
  follows (`…InvertibleTwistingRestriction.clauseOneSections_of_clauseOneHom`).
* **Clause (3)**, `θ'` is the pullback of `θ`: the restriction of `θ` to a scheme point
  `w : W ⟶ U(ψ)` (for instance the inclusion of `U(ψ')` for a scheme `X' ⟶ X`) is the member `χ_w`
  of the family (`AlgebraicGeometry.Space.modulePullback_map_pointHom_pointFamilyDescendedHom`);
  for the family of chart maps this is `θ` of Tag 01O9 on `W`, read through the identifications of
  its source and target.

## Main definitions

* `…InvertibleTwistingRestriction.thetaOfFamily`: the map `θ` of a compatible family, in every
  degree.

## Main results

* `…InvertibleTwistingRestriction.clauseOneHom_thetaOfFamily`,
  `…InvertibleTwistingRestriction.clauseOneSections_thetaOfFamily`: **clause (1) for `θ` from
  clause (1) at the scheme points.**
* `…InvertibleTwistingRestriction.modulePullback_map_pointHom_thetaOfFamily`: **clause (3): the
  restriction of `θ` to a scheme point is the member of the family there.**
* `…InvertibleTwistingRestriction.modulePullback_map_pointHom_thetaOfFamily_chartMap`: for the
  family of chart maps, the restriction of `θ` to a scheme point `w` is `θ` of Tag 01O9 on `W`
  (`…InvertibleTwistingRestriction.chartSchemeTheta`) through the identifications of its source
  and target.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (P : Presentation s.shrink.site s.shrink.base s.shrink.containsBase
    (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property)

/-- A family of maps `χ_w : w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` indexed by the degrees `d` and
the scheme points `w : W ⟶ U(ψ)`: the shape of the family from which `θ` is descended. -/
abbrev ThetaPointFamily :=
  ∀ (d : ℤ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).obj
        (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).obj
        (thetaTarget s f L ψ d).obj

variable {s f L ψ Px} {χ : ThetaPointFamily s f L ψ Px}
  (hχ : ∀ d : ℤ, PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj
    (thetaTarget s f L ψ d).obj (χ d))

/-- **The map `θ` of a compatible family**, in every degree `d`: the morphism
`r^*𝒪(d) ⟶ ℒ^{⊗ d}|_{U(ψ)}` of quasi-coherent `𝒪_{U(ψ)}`-modules descended along the presentation
`P` of `U(ψ)` from the members `χ_w` at the scheme points (Stacks 03M3). -/
def thetaOfFamily (d : ℤ) :
    (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj :=
  pointFamilyDescendedHom P (hχ d)

/-- **Clause (3) of [Stacks, Tag 0D2Z]: the restriction of `θ` to a scheme point is the member of
the family there.**  For every scheme point `w : W ⟶ U(ψ)` (for instance the inclusion of
`U(ψ') = (g')^{-1}(U(ψ))` for a scheme `X' ⟶ X`), the inverse image of `θ` along `w` is `χ_w`. -/
theorem modulePullback_map_pointHom_thetaOfFamily (d : ℤ)
    {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (thetaOfFamily P hχ d) = χ d T w :=
  modulePullback_map_pointHom_pointFamilyDescendedHom P (hχ d) w

/-- `θ` is the only morphism with the restrictions `χ_w` at the scheme points. -/
theorem eq_thetaOfFamily (d : ℤ)
    (g : (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj)
    (hg : ∀ (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map g =
        χ d T w) :
    g = thetaOfFamily P hχ d :=
  eq_pointFamilyDescendedHom_of_modulePullback_map_pointHom P (hχ d) g hg

/-- **Clause (1) of [Stacks, Tag 0D2Z] in morphism form, from clause (1) at the scheme points**:
if at every scheme point `w : W ⟶ U(ψ)` and in every degree `d ≥ 0` the inverse image along `w` of
the `ψ_P` leg followed by `χ_w` is the inverse image of the `ψ` leg, then the `ψ_P` leg followed by
`θ` is the `ψ` leg. -/
theorem clauseOneHom_thetaOfFamily
    (h : ∀ (d : ℕ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOneProjLeg s f L ψ Px d) ≫ χ (d : ℤ) T w =
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
    ClauseOneHom s f L ψ Px (thetaOfFamily P hχ) := fun d => by
  have := isQuasicoherentOnSite_clauseOneSource s f L ψ (d : ℤ)
  exact comp_pointFamilyDescendedHom_eq P (hχ (d : ℤ)) _ _ (h d)

/-- **Clause (1) of [Stacks, Tag 0D2Z] in the section form the tag states, from clause (1) at the
scheme points**: for every étale `V ⟶ Y`, `d ≥ 0` and section `a` of `𝒜_d` over `V`, the images of
`a` in `Γ(V ×_Y U(ψ), ℒ^{⊗ d})` along `ψ_P` followed by `θ` and along `ψ` agree. -/
theorem clauseOneSections_thetaOfFamily
    (h : ∀ (d : ℕ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOneProjLeg s f L ψ Px d) ≫ χ (d : ℤ) T w =
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
    ClauseOneSections s f L ψ Px (thetaOfFamily P hχ) :=
  clauseOneSections_of_clauseOneHom s f L ψ Px _ (clauseOneHom_thetaOfFamily P hχ h)

/-- **Clause (3) of [Stacks, Tag 0D2Z] for the family of chart maps**: when `θ` is descended from
the chart maps `χ_w` (`…InvertibleTwistingRestriction.chartMap`), its restriction to a scheme
point `w : W ⟶ U(ψ)` is `θ` of [Stacks, Tag 01O9] on `W` for the restriction `w^*ψ`
(`…InvertibleTwistingRestriction.chartSchemeTheta`), read through the identifications
`…chartSourceIso` and `…chartTargetIso` of its source and target. -/
theorem modulePullback_map_pointHom_thetaOfFamily_chartMap
    (hχ : ∀ d : ℤ, PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj
      (thetaTarget s f L ψ d).obj (fun _ w => chartMap Px w d)) (d : ℤ)
    {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (thetaOfFamily (χ := fun d _ w => chartMap Px w d) P hχ d) =
      (chartSourceIso Px w (locusOpen_locusPoint w) d).hom ≫
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.map
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom ≫
        (chartTargetIso w d).hom :=
  modulePullback_map_pointHom_thetaOfFamily P hχ d w

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
