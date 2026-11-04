module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageGeometricStalk

/-!
# Sections of a direct image over a chart with cartesian base change

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, not assumed representable,
and let `F` be an `𝒪_X`-module.  For a diagram of étale scheme charts `U → V` over `f` whose
square is cartesian, that is for which `U` represents the base change `X ×_Y V`, the canonical
map of sections `(f_*F)(V) → F(U)` is bijective.

## Main results

* `AlgebraicGeometry.Space.isIso_chartLift_of_isPullback`: for a cartesian chart diagram, the
  morphism from the source chart to `X ×_Y V` in the spaces-étale site of `X` is an
  isomorphism.
* `AlgebraicGeometry.Space.isInitialIndexOfChartDiagram`: the étale scheme chart of `X` above
  `X ×_Y V` named by a cartesian chart diagram is an initial index for the limit computing the
  sections of the direct image over `V`.
* `AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback`: the canonical
  map of sections `(f_*F)(V) → F(U)` is bijective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.StructuredArrow

variable {C D : Type*} [Category* C] [Category* D] {S : D} {T : C ⥤ D}

/-- A structured arrow whose structure morphism is an isomorphism is initial, when the functor
is fully faithful. -/
noncomputable def isInitialOfIsIsoHom [T.Full] [T.Faithful] (j : StructuredArrow S T)
    [IsIso j.hom] : IsInitial j where
  desc c := homMk (T.preimage (inv j.hom ≫ c.pt.hom)) (by
    rw [Functor.map_preimage]
    exact IsIso.hom_inv_id_assoc j.hom _)
  uniq c m _ := StructuredArrow.hom_ext _ _ (T.map_injective (by
    change T.map m.right = T.map (T.preimage (inv j.hom ≫ c.pt.hom))
    rw [Functor.map_preimage, ← StructuredArrow.w m]
    exact (IsIso.inv_hom_id_assoc j.hom _).symm))

end CategoryTheory.StructuredArrow

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- A chart diagram whose square of presheaves is cartesian gives a cartesian square of
algebraic spaces. -/
theorem isPullback_chartDiagramSpaceMap (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f.hom d.V.1.hom) :
    IsPullback (chartDiagramSpaceMap B S hS f d) ((comparisonFunctor B S hS X).obj d.U).1.hom
      ((comparisonFunctor B S hS Y).obj d.V).1.hom f :=
  IsPullback.of_map (ObjectProperty.ι _) (chartDiagramSpaceMap_w B S hS f d) hd.flip

/-- **The cartesian form of a cartesian chart diagram is an isomorphism.**  When the source
chart `U` represents `X ×_Y V`, the morphism `U → X ×_Y V` of the spaces-étale site of `X`
induced by the chart diagram is an isomorphism. -/
theorem isIso_chartLift_of_isPullback (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f.hom d.V.1.hom) :
    IsIso (chartLift B S hS f d) := by
  have h := isPullback_chartDiagramSpaceMap B S hS f d hd
  have h' := (spacesBaseChange B S hS f).isPullback ((comparisonFunctor B S hS Y).obj d.V)
  have hL : IsIso (h'.lift (chartDiagramSpaceMap B S hS f d)
      ((comparisonFunctor B S hS X).obj d.U).1.hom (chartDiagramSpaceMap_w B S hS f d)) := by
    have e : h'.lift (chartDiagramSpaceMap B S hS f d)
        ((comparisonFunctor B S hS X).obj d.U).1.hom (chartDiagramSpaceMap_w B S hS f d) =
        (h.isoIsPullback _ _ h').hom :=
      h'.hom_ext (by simp) (by simp)
    exact e ▸ inferInstance
  have : IsIso ((ObjectProperty.ι _ ⋙ Over.forget X).map (chartLift B S hS f d)) := hL
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _ ⋙ Over.forget X)

/-- **The chart named by a cartesian chart diagram is an initial index.**  Every étale scheme
chart of `X` above `X ×_Y V` factors uniquely through the source chart of a cartesian chart
diagram over `V`. -/
noncomputable def isInitialIndexOfChartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f.hom d.V.1.hom) :
    IsInitial (indexOfChartDiagram B S hS f d) :=
  have := comparisonFunctor_full B S hS X
  have := comparisonFunctor_faithful B S hS X
  have := isIso_chartLift_of_isPullback B S hS f d hd
  have : IsIso (indexOfChartDiagram B S hS f d).hom :=
    inferInstanceAs (IsIso (chartLift B S hS f d).op)
  StructuredArrow.isInitialOfIsIsoHom _

/-- **Sections of a direct image over a chart with cartesian base change.**  For any morphism
of algebraic spaces `f : X ⟶ Y` and a chart diagram `U → V` over `f` whose square is cartesian,
so that `U` represents `X ×_Y V`, the canonical map of sections `(f_*F)(V) → F(U)` is
bijective. -/
theorem bijective_modulePushforwardCounitApp_of_isPullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f.hom d.V.1.hom) :
    Function.Bijective (modulePushforwardCounitApp B S hS f F d) := by
  have h₁ : Function.Bijective
      ((ranChartCone B S hS X (moduleSetSheaf B S hS X F).obj
        (chartBaseChange B S hS f d.V)).π.app (indexOfChartDiagram B S hS f d)) :=
    (isIso_iff_bijective _).mp ((ranChartIsLimit B S hS X _ _).isIso_π_app_of_isInitial _
      (isInitialIndexOfChartDiagram B S hS f d hd))
  have h₂ : Function.Bijective (((smallEtaleDirectImageRanIso B S hS f).hom.app
      (moduleSetSheaf B S hS X F)).hom.app (op d.V)) :=
    (isIso_iff_bijective _).mp (inferInstanceAs (IsIso
      (((sheafToPresheaf _ _).mapIso ((smallEtaleDirectImageRanIso B S hS f).app
        (moduleSetSheaf B S hS X F))).app (op d.V)).hom))
  have e : modulePushforwardCounitApp B S hS f F d =
      (ranChartCone B S hS X (moduleSetSheaf B S hS X F).obj
        (chartBaseChange B S hS f d.V)).π.app (indexOfChartDiagram B S hS f d) ∘
      ((smallEtaleDirectImageRanIso B S hS f).hom.app
        (moduleSetSheaf B S hS X F)).hom.app (op d.V) :=
    funext fun x => moduleChartProjection_app B S hS f d.V (indexOfChartDiagram B S hS f d)
      (moduleSetSheaf B S hS X F) x
  exact e ▸ h₁.comp h₂

end AlgebraicGeometry.Space

end
