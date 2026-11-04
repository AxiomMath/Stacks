module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramTensorComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartSchemeBourbakiTransport
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassin.TensorPullbackWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ChartSchemeNoetherian

/-!
# Bourbaki's formula on a locally Noetherian algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓕` be a quasi-coherent
`𝒪_X`-module flat over `Y` and let `𝓖` be a quasi-coherent `𝒪_Y`-module. With `X` and `Y`
locally Noetherian and the fibres of `f` locally Noetherian, Stacks 0CV1 asserts

`Ass_X(𝓕 ⊗_{𝒪_X} f^*𝓖) = {x ∈ Ass_{X/Y}(𝓕) such that f(x) ∈ Ass_Y(𝓖)}`.

## Main results

* `AlgebraicGeometry.Space.exists_chartDiagram_chartSchemeToPoints_eq`: every point of `|X|` is
  cut out by a point of the source chart scheme of some commuting square of étale scheme charts
  over `f`.
* `AlgebraicGeometry.Space.locallyNoetherianFibers_chartDiagramSchemeMap`: the chart morphism of
  every commuting square of étale scheme charts over a morphism with locally Noetherian fibres
  again has locally Noetherian fibres.
* `AlgebraicGeometry.Space.relativeAssassin_chartDiagram_eq_relativeWeaklyAssociatedPoints`: on
  such a square the Zariski relative assassin of Stacks 05AT of the chart morphism is its
  relative weak assassin of Stacks 05AV.
* `Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram_of_locallyNoetherian`:
  Bourbaki's formula at a point cut out by a chart diagram, over locally Noetherian `X` and `Y`
  and with `𝓕` flat over `Y`.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_tensor_modulePullback_eq`: the set equality
  above.

## References

* [Stacks Project, Tag 0CV1](https://stacks.math.columbia.edu/tag/0CV1)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CUY](https://stacks.math.columbia.edu/tag/0CUY)
* [Stacks Project, Tag 0CUS](https://stacks.math.columbia.edu/tag/0CUS)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 05DB](https://stacks.math.columbia.edu/tag/05DB)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Every point of `|X|` is cut out by a point of the source chart scheme of some commuting square
of étale scheme charts over `f`. -/
theorem exists_chartDiagram_chartSchemeToPoints_eq (f : X ⟶ Y) (x : points B S hS X.1) :
    ∃ (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U),
      chartSchemeToPoints B S hS X.1 d.U w = x := by
  obtain ⟨d, u, hu⟩ := exists_chartDiagram_pointOfEtaleChart B S hS X.2 Y.2 f.hom x
  exact ⟨d, u,
    (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 d.U u).trans hu⟩

/-- If the fibres of `f : X ⟶ Y` are locally Noetherian in the sense of Stacks 0CUY, then so are
the fibres of the vertical morphism of chart schemes `q : U ⟶ V` of every commuting square of étale
scheme charts over `f`. -/
theorem locallyNoetherianFibers_chartDiagramSchemeMap (f : X ⟶ Y)
    (hfib : HasLocallyNoetherianFibersAtPoints B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ∀ v : chartScheme d.V, IsLocallyNoetherian ((chartDiagramSchemeMap B S hS f d).fiber v) := by
  let _ := AlgebraicGeometry.etale_isStableUnderComposition.{u}
  set a : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj d.U) ⟶
      Limits.pullback f.hom d.V.1.hom :=
    Limits.pullback.lift d.U.1.hom (yoneda.map d.g) d.comm with ha
  have hafst : a ≫ Limits.pullback.fst f.hom d.V.1.hom = d.U.1.hom :=
    Limits.pullback.lift_fst _ _ _
  have hasnd : a ≫ Limits.pullback.snd f.hom d.V.1.hom = yoneda.map d.g :=
    Limits.pullback.lift_snd _ _ _
  have hfst := presheafProperty_pullback_fst B S hS (@AlgebraicGeometry.Etale.{u})
    f.hom d.V.1.hom d.V.property
  have haEtale : IsEtale B S hS a :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_pullback B S hS f.hom d.V.1.hom X.2
        (isAlgebraicSpace_yoneda B S hS _) Y.2)
      X.2 a d.U.1.hom (Limits.pullback.fst f.hom d.V.1.hom)
      ((isEtale_iff_presheaf_of_yoneda B S hS d.U.1.hom).2 d.U.property)
      (fun _ φ hφ => presheafProperty_comp B S hS _ φ _ hφ hfst) hafst
  exact locallyNoetherianFibers_of_etale_pullback_chart B S hS X.2 Y.2 f.hom hfib
    ((SmallEtale.toOver B S hS Y.1).obj d.V) d.V.1.hom d.V.property
    ((SmallEtale.toOver B S hS X.1).obj d.U) a d.g hasnd
    ((isEtale_iff_presheaf_of_yoneda B S hS a).1 haEtale)

/-- On a chart diagram over a morphism with locally Noetherian fibres, the Zariski relative
assassin of Stacks 05AT of the chart morphism and its relative weak assassin of Stacks 05AV
agree. -/
theorem relativeAssassin_chartDiagram_eq_relativeWeaklyAssociatedPoints (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hfib : HasLocallyNoetherianFibersAtPoints B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
        (chartDiagramRestrictSource B S hS f F d) =
      _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d) :=
  (relativeWeaklyAssociatedPoints_eq_relativeAssassin_of_isLocallyNoetherian
    (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d)
    (locallyNoetherianFibers_chartDiagramSchemeMap B S hS f hfib d)).symm

/-- Let `X` and `Y` be locally Noetherian, let `𝓕` be flat over `Y` in the sense of Stacks 05VV,
let `d` be a commuting square of étale scheme charts over `f` with vertical morphism of chart
schemes `q`, and let `w` be a point of the source chart scheme. Then the point of `|X|` cut out by
`w` is weakly associated to `𝓕 ⊗_{𝒪_X} f^*𝓖` exactly when its image is weakly associated to `𝓖` and
it lies in the relative weak assassin `WeakAss_{X/Y}(𝓕)` of Stacks 0CV0. -/
theorem isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram_of_locallyNoetherian
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    [hGqc : G.IsQuasicoherentOnSite]
    (hLNX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hLNY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (hFqc : F.IsQuasicoherentOnSite)
    (hfib : HasLocallyNoetherianFibersAtPoints B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (w : chartScheme d.U) :
    IsWeaklyAssociatedPoint B S hS X (F ⊗ (modulePullback B S hS f).obj G)
        (chartSchemeToPoints B S hS X.1 d.U w) ↔
      (IsWeaklyAssociatedPoint B S hS Y G
          (pointsMap B S hS X.1 f.hom (chartSchemeToPoints B S hS X.1 d.U w)) ∧
        IsRelativeWeaklyAssociatedPoint B S hS f F
          (chartSchemeToPoints B S hS X.1 d.U w)) := by
  have hFGqc : (F ⊗ (modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_tensorObj_modulePullback_of_isQuasicoherentOnSite B S hS f F G
  obtain ⟨cmp⟩ := nonempty_restrictToChart_tensor_modulePullback_chartDiagram B S hS f F G
    hFqc hGqc hFGqc d
  have : IsLocallyNoetherian (chartScheme d.U) :=
    isLocallyNoetherian_chartScheme B S hS X hLNX d.U
  have : IsLocallyNoetherian (chartScheme d.V) :=
    isLocallyNoetherian_chartScheme B S hS Y hLNY d.V
  have : (chartDiagramRestrictSource B S hS f F d).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F hFqc d.U
  have : (chartDiagramRestrictTarget B S hS f G d).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS Y G hGqc d.V
  have hset := weaklyAssociatedPoints_tensor_pullback_eq_relativeAssassin
    (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d)
    (chartDiagramRestrictTarget B S hS f G d) (hF d)
  have hw : Stacks.Divisors.IsWeaklyAssociatedPoint
        (chartDiagramTensorPullback B S hS f F G d) w ↔
      (w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
          (chartDiagramRestrictSource B S hS f F d) ∧
        Stacks.Divisors.IsWeaklyAssociatedPoint (chartDiagramRestrictTarget B S hS f G d)
          (chartDiagramSchemeMap B S hS f d w)) := Set.ext_iff.mp hset w
  have hrel' : IsRelativeWeaklyAssociatedPoint B S hS f F
        (chartSchemeToPoints B S hS X.1 d.U w) →
      w ∈ Stacks.Divisors.relativeAssassin (chartDiagramSchemeMap B S hS f d)
        (chartDiagramRestrictSource B S hS f F d) := fun hx => by
    rw [relativeAssassin_chartDiagram_eq_relativeWeaklyAssociatedPoints B S hS f F hfib d]
    exact mem_relativeWeaklyAssociatedPoints_chartDiagram B S hS f F hFqc d w hx
  exact isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram B S hS f F G d w
    cmp (hw.trans and_comm)
    ⟨isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram B S hS f F hFqc d w,
      hrel'⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓕` be a
quasi-coherent `𝒪_X`-module and `𝓖` a quasi-coherent `𝒪_Y`-module. Assume `𝓕` is flat over `Y`,
that `X` and `Y` are locally Noetherian and that the fibres of `f` are locally Noetherian. Then

`Ass_X(𝓕 ⊗_{𝒪_X} f^*𝓖) = {x ∈ Ass_{X/Y}(𝓕) such that f(x) ∈ Ass_Y(𝓖)}`,

where `Ass` and `Ass_{X/Y}` are `AlgebraicGeometry.Space.weaklyAssociatedPoints` and
`AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints`. -/
@[stacks 0CV1]
theorem weaklyAssociatedPoints_tensor_modulePullback_eq (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    [hFqc : F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite]
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (hLNX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hLNY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hfib : HasLocallyNoetherianFibersAtPoints B S hS f.hom) :
    weaklyAssociatedPoints B S hS X (F ⊗ (modulePullback B S hS f).obj G) =
      {x | x ∈ relativeWeaklyAssociatedPoints B S hS f F ∧
        pointsMap B S hS X.1 f.hom x ∈ weaklyAssociatedPoints B S hS Y G} := by
  have : (F ⊗ (modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_tensorObj_modulePullback_of_isQuasicoherentOnSite B S hS f F G
  ext x
  obtain ⟨d, w, rfl⟩ := exists_chartDiagram_chartSchemeToPoints_eq B S hS f x
  exact ((isWeaklyAssociatedPoint_tensor_modulePullback_iff_of_chartDiagram_of_locallyNoetherian
    B S hS f F G hLNX hLNY hF hFqc hfib d w).trans and_comm)

end AlgebraicGeometry.Space

end
