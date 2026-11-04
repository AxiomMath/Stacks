module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSourceSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaDescent

/-!
# The chart maps of `θ` of Stacks 0D2Z are compatible along the scheme points

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849 and a morphism `τ : T' ⟶ T` of the site, the chart maps
`χ_w = (chartTargetIso w) ∘ θ_w^a ∘ (chartSourceIso w)` at a scheme point `w : T ⟶ U(ψ)` and at
`w' = w ∘ τ` form a square along `τ` (`AlgebraicGeometry.Space.PullbackTransportSquare`), as soon
as `θ` of [Stacks, Tag 01O9] on `T` and on `T'` form a square with the comparisons of the sources
and of the targets.  The square is assembled from the squares of the three factors
(`AlgebraicGeometry.Space.pullbackTransportSquare_of_squares`).

## Main results

* `…InvertibleTwistingRestriction.chartTargetIso_square`: the square of the target factor in the
  spelling of the chart maps.
* `…InvertibleTwistingRestriction.pullbackTransportSquare_chartMap_of_square`: the square of the
  chart maps from the square of `θ` on the schemes.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

section Target

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.modulePullback_map_eq_of_square` for a module `H` equal to `ι^*M`
and morphisms `x`, `x'` into `p^*H`, `p'^*H` heterogeneously equal to the composites
`E ≅ q^*M ≅ (p ≫ ι)^*M ≅ p^*(ι^*M)`. -/
theorem modulePullback_map_eq_of_square_of_heq {U Y Z : AlgebraicSpaces B S hS} (ι : U ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (r : Z ⟶ Y) {q : Y ⟶ X} {q' : Z ⟶ X}
    {E : Modules.{u, u} B S hS Y.1 Y.2} {E' : Modules.{u, u} B S hS Z.1 Z.2}
    (t : (modulePullback B S hS q).obj M ≅ E) (t' : (modulePullback B S hS q').obj M ≅ E')
    (c : (modulePullback B S hS r).obj E ⟶ E') (hrq : r ≫ q = q')
    (hN : (modulePullback B S hS r).map t.hom ≫ c =
      ((modulePullbackCompIso B S hS r q).hom.app M ≫ pullbackTransport M hrq) ≫ t'.hom)
    (p : Y ⟶ U) (p' : Z ⟶ U) (hp : r ≫ p = p') (hq : q = p ≫ ι) (hq' : q' = p' ≫ ι)
    (H : Modules.{u, u} B S hS U.1 U.2) (hH : (modulePullback B S hS ι).obj M = H)
    (x : E ⟶ (modulePullback B S hS p).obj H)
    (hx : HEq x (t.symm ≪≫ eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) hq) ≪≫
        ((modulePullbackCompIso B S hS p ι).app M).symm).hom)
    (x' : E' ⟶ (modulePullback B S hS p').obj H)
    (hx' : HEq x' (t'.symm ≪≫ eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) hq') ≪≫
        ((modulePullbackCompIso B S hS p' ι).app M).symm).hom) :
    (modulePullback B S hS r).map x ≫
        ((modulePullbackCompIso B S hS r p).hom.app H ≫ pullbackTransport H hp) = c ≫ x' := by
  subst hH
  exact modulePullback_map_eq_of_square ι M r t t' c hrq hN p p' hp hq hq' x (eq_of_heq hx) x'
    (eq_of_heq hx')

end Target

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase} (τ : T' ⟶ T)
  {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
  {w' : yoneda.obj T' ⟶ (locusSpaceOfUnitalHom s f L ψ).obj} (hw : yoneda.map τ ≫ w = w')

set_option maxHeartbeats 400000 in
-- elaborating the `type_of%` statement below takes more than the default heartbeats
include hw in
/-- **The square of the target factor of the chart maps along `τ : T' ⟶ T`, in the spelling of
the chart maps**: `τ^*` of `…chartTargetIso w`, followed by the comparison of Stacks 03LU for `τ`
and `w` and the transport along `w ∘ τ = w'` of `ℒ^{⊗ d}|_{U(ψ)}` (`…thetaTarget`), is
`τ^*(M^a) ≅ (τ^*M)^a` followed by the module attached to
`τ^*((w^*ℒ)^{⊗ d}) ⟶ ((w ∘ τ)^*ℒ)^{⊗ d}` and `…chartTargetIso w'`.

The statement is the instance of `AlgebraicGeometry.Space.modulePullback_map_eq_of_square_of_heq`
(`type_of%`) at `H = ℒ^{⊗ d}|_{U(ψ)}` and the target factors `…chartTargetIso w`, `…w'`. -/
theorem chartTargetIso_square (d : ℤ) :
    type_of% (modulePullback_map_eq_of_square_of_heq (locusInclusionOfUnitalHom s f L ψ)
      (SheafOfModules.GradedAlgebra.piece
          (R := structureRingSheaf s.shrink.site s.shrink.base s.shrink.containsBase X)
          (Stacks.SheafOfModules.TensorPower.laurentAlgebra
            (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase
                X).O).property
              L) d)
      (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase τ)
      (pointTargetIso L T (locusPoint w) d)
      (pointTargetIso L T' (locusPoint w') d) _ (pointHom_comp τ (map_comp_locusPoint τ hw))
      (pointTargetIso_hom_naturality_of_eq L τ (locusPoint w) (locusPoint w')
        (map_comp_locusPoint τ hw) d _ rfl)
      (pointHom w) (pointHom w') (pointHom_comp τ hw) (pointHom_locusPoint w)
      (pointHom_locusPoint w') (thetaTarget s f L ψ d).obj rfl (chartTargetIso w d).hom HEq.rfl
      (chartTargetIso w' d).hom HEq.rfl) :=
  modulePullback_map_eq_of_square_of_heq (locusInclusionOfUnitalHom s f L ψ)
    (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.shrink.site s.shrink.base s.shrink.containsBase X)
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property
            L) d)
    (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase τ)
    (pointTargetIso L T (locusPoint w) d)
    (pointTargetIso L T' (locusPoint w') d) _ (pointHom_comp τ (map_comp_locusPoint τ hw))
    (pointTargetIso_hom_naturality_of_eq L τ (locusPoint w) (locusPoint w')
      (map_comp_locusPoint τ hw) d _ rfl)
    (pointHom w) (pointHom w') (pointHom_comp τ hw) (pointHom_locusPoint w)
    (pointHom_locusPoint w') (thetaTarget s f L ψ d).obj rfl (chartTargetIso w d).hom HEq.rfl
    (chartTargetIso w' d).hom HEq.rfl

include Px hw in
/-- **The square of the chart maps along `τ : T' ⟶ T`, from the square of `θ` on the schemes**:
for scheme points `w` of `U(ψ)` at `T` and `w' = w ∘ τ` at `T'`, a morphism
`y : T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` lying over `τ`, and the comparison `σ` of the sources of
`θ_w` and `θ_{w'}` along `y`, if `τ^*θ_w` followed by the comparison
`τ^*((w^*ℒ)^{⊗ d}) ⟶ ((w ∘ τ)^*ℒ)^{⊗ d}` of the targets is `σ` followed by `θ_{w'}`, then the chart
maps `χ_w` and `χ_{w'}` form a square along `τ`
(`AlgebraicGeometry.Space.PullbackTransportSquare`). -/
theorem pullbackTransportSquare_chartMap_of_square (d : ℤ)
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (hfy : representedSpaceMap s.site s.base s.containsBase y ≫
        s.fibreToSpaceHom T (locusPoint w ≫ f.hom) =
      s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom))
    (σ : quasicoherentPullbackObj s.site s.base s.containsBase τ
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceQcoh T' (locusPoint w' ≫ f.hom) d))
    (hσ : σ = (quasicoherentPullbackCompIso s.site s.base s.containsBase τ
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).hom ≫
      quasicoherentPullbackEqToHom s.site s.base s.containsBase
        (comp_chartSection_locusPoint τ hw y hy) (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d) ≫
      (quasicoherentPullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d).hom)
    (hθ : quasicoherentPullbackMap s.site s.base s.containsBase τ
        (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d) ≫
          (pointLaurentPiecePullbackHom L τ (locusPoint w) d ≫
            eqToHom (congrArg (fun k => pointLaurentPieceQcoh L T' k d)
              (map_comp_locusPoint τ hw))) =
      σ ≫ chartSchemeTheta s f L ψ (locusPoint w') (locusOpen_locusPoint w') d) :
    PullbackTransportSquare (Y := yonedaSpace _ _ _ T) (Z := yonedaSpace _ _ _ T')
      (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase τ)
      (pointHom w) (pointHom w') (pointHom_comp τ hw)
      (thetaSourceOfUnitalHom s f L ψ Px d).obj (thetaTarget s f L ψ d).obj
      (chartMap Px w d) (chartMap Px w' d) :=
  pullbackTransportSquare_of_squares
    (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase τ)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w') (pointHom_comp τ hw)
    (thetaSourceOfUnitalHom s f L ψ Px d).obj (thetaTarget s f L ψ d).obj
    (chartSourceIso Px w (locusOpen_locusPoint w) d).hom
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase T).functor.map
      (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom
    _ (chartSourceIso Px w' (locusOpen_locusPoint w') d).hom
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase T').functor.map
      (chartSchemeTheta s f L ψ (locusPoint w') (locusOpen_locusPoint w') d)).hom
    _ _ _
    (chartSource_square_shrink Px τ hw d y hy hfy σ hσ)
    (modulePullback_map_functor_map_comp_eq_of_square (B := s.shrink.site) (S := s.shrink.base)
      (hS := s.shrink.containsBase) τ _ _ σ _ hθ)
    (chartTargetIso_square τ hw d)
    (chartMap Px w d) (chartMap Px w' d) rfl rfl

omit Px in
/-- The morphism `T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` of base changes along `τ` used for the
squares of the chart maps: the comparison of Stacks 084B (3) along `τ`, read on the base change
along `f ∘ w' = (f ∘ w) ∘ τ`. -/
abbrev chartFibreMap :
    s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom) :=
  eqToHom (congrArg (s.relativeProjPoints.fibre T') (map_comp_locusPoint_comp τ hw).symm) ≫
    s.relativeProjPoints.fibreComparison T (locusPoint w ≫ f.hom) τ

omit Px in
/-- `…chartFibreMap τ hw` lies over `τ`. -/
theorem liesOver_chartFibreMap : s.relativeProjPoints.LiesOver (chartFibreMap τ hw) τ :=
  RelativeProjPoints.LiesOver.eqToHom_comp (map_comp_locusPoint_comp τ hw).symm
    (RelativeProjPoints.liesOver_fibreComparison (d := s.relativeProjPoints) T _ τ)

/-- **The chart maps of `θ` form a compatible family, from the squares of `θ` on the schemes**:
if for every `τ : T' ⟶ T`, scheme points `w` of `U(ψ)` at `T` and `w' = w ∘ τ` at `T'`, and
`y : T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` lying over `τ`, the maps `θ_w` and `θ_{w'}` of
[Stacks, Tag 01O9] form a square with the comparisons `σ` of their sources and the comparison
`τ^*((w^*ℒ)^{⊗ d}) ⟶ ((w ∘ τ)^*ℒ)^{⊗ d}` of their targets, then the chart maps `χ_w` in degree `d`
form a compatible family (`AlgebraicGeometry.Space.PointFamilyNatural`). -/
theorem pointFamilyNatural_chartMap_of_square (d : ℤ)
    (hm : ∀ ⦃T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase⦄ (τ : T' ⟶ T)
      {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
      {w' : yoneda.obj T' ⟶ (locusSpaceOfUnitalHom s f L ψ).obj} (hw : yoneda.map τ ≫ w = w')
      (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
        s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
      (hy : s.relativeProjPoints.LiesOver y τ)
      (σ : quasicoherentPullbackObj s.site s.base s.containsBase τ
          (quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)) ⟶
        quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
          (s.twistPieceQcoh T' (locusPoint w' ≫ f.hom) d)),
      σ = (quasicoherentPullbackCompIso s.site s.base s.containsBase τ
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).hom ≫
        quasicoherentPullbackEqToHom s.site s.base s.containsBase
          (comp_chartSection_locusPoint τ hw y hy) (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d) ≫
        (quasicoherentPullbackCompIso s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
          (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d).hom →
      quasicoherentPullbackMap s.site s.base s.containsBase τ
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d) ≫
            (pointLaurentPiecePullbackHom L τ (locusPoint w) d ≫
              eqToHom (congrArg (fun k => pointLaurentPieceQcoh L T' k d)
                (map_comp_locusPoint τ hw))) =
        σ ≫ chartSchemeTheta s f L ψ (locusPoint w') (locusOpen_locusPoint w') d) :
    PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj (thetaTarget s f L ψ d).obj
      (fun _ w => chartMap Px w d) :=
  ⟨fun _ _ τ _ _ hw => pullbackTransportSquare_chartMap_of_square Px τ hw d
    (chartFibreMap τ hw) (liesOver_chartFibreMap τ hw)
    (ObjectProperty.hom_ext _ (liesOver_chartFibreMap τ hw).2) _ rfl
    (hm τ hw (chartFibreMap τ hw) (liesOver_chartFibreMap τ hw) _ rfl)⟩

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
