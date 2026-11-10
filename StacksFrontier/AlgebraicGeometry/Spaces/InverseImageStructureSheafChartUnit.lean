module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap

/-!
# The unit of `f⁻¹ ⊣ f_*` on charts, and its germs

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a commutative
diagram of étale scheme charts over `f`, with chart `V` of `X`, chart `W` of `Y` and vertical
morphism `g : V ⟶ W`.  The unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y` of the adjunction between the inverse image
and the direct image of sheaves of commutative rings along the morphism of small étale ringed
topoi of Stacks 03G8, read through the chart correspondence of Stacks 03G3, is a map

`𝒪_Y(W) ⟶ (f⁻¹𝒪_Y)(V)`.

This file computes its germs: at a geometric point `x` of `X` with a lift `v` to `V`, and the
lift `g ∘ v` of `f ∘ x` to `W`, the germ at `v` of the image of a regular function `s` on `W` is
the image of the germ of `s` at `g ∘ v` under the fibre comparison
`(f⁻¹𝒪_Y)_x ≅ (𝒪_Y)_{f ∘ x}` of Stacks 04K2 (4).  It is the companion of
`AlgebraicGeometry.Space.stalkStructureMap_toPresheafFiber`, which is the same computation for
the structure map `𝒪_Y ⟶ f_*𝒪_X` in place of the unit.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageUnitFMap`: the unit, as a map of sections over chart
  diagrams.

## Main results

* `AlgebraicGeometry.Space.inverseImageUnitFMap_toPresheafFiber`: the germ formula above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y` of the adjunction between the inverse image and the direct image
of sheaves of commutative rings along the morphism of small étale ringed topoi of `f`. -/
abbrev inverseImageUnit :
    (smallEtaleRingedTopos B S hS Y).O ⟶
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.obj
        (inverseImageStructureSheaf B S hS f) :=
  (smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.unit.app
    (smallEtaleRingedTopos B S hS Y).O

/-- **The unit on charts.**  The unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y` read through the chart correspondence of
Stacks 03G3 as a map of sections over every diagram of étale scheme charts over `f`. -/
abbrev inverseImageUnitFMap :
    FMap B S hS X.1 Y.1 f.hom
      ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f)).obj
      ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O).obj :=
  (fMapEquivPushforwardHom_ringUniverse B S hS f
      ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f))
      ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)).symm
    ((smallEtaleRingedTopos B S hS Y).forgetRing.map (inverseImageUnit B S hS f))

/-- **The chartwise formula for a map out of `f⁻¹𝒪_Y` pushed forward after the unit.**  For a
homomorphism `α` from `f⁻¹𝒪_Y` into the restriction of a spaces-étale sheaf of commutative rings
`H`, restricting the section of `f_*` attached to the unit followed by `f_*α` along a diagram of
charts is `α` applied to the value of the unit on charts.

This is `AlgebraicGeometry.Space.structureSheafHom_postcomp_chart` with the unit in place of the
structure map; no chartwise formula for the unit itself is needed, since its value on charts is
*defined* through the correspondence. -/
theorem inverseImageUnit_postcomp_chart
    (H : Sheaf (SpacesEtale.topology B S hS X) CommRingCat.{u})
    (α : inverseImageStructureSheaf B S hS f ⟶
      ((comparisonFunctor B S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj H)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : (comparisonFunctor B S hS X).obj d.U ⟶ chartBaseChange B S hS f d.V)
    (hh : HEq (((SpacesEtale.toSpaces B S hS X).map h) ≫
        (spacesBaseChange B S hS f).projection.app
          ((comparisonFunctor B S hS Y).obj d.V)).hom
      (yoneda.map d.g))
    (s : ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj (op d.V)) :
    letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
    H.obj.map h.op
        ((inverseImageUnit B S hS f ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map α ≫
          (smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app H).hom.app (op d.V) s) =
      α.hom.app (op d.U) ((inverseImageUnitFMap B S hS f).app d s) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hc := chartCorrespondence_postcomp B S hS f
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f))
    ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
    (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H)
    ((smallEtaleRingedTopos B S hS X).forgetRing.map α)
    (inverseImageUnitFMap B S hS f) d h hh s
  have he : fMapEquivPushforwardHom_ringUniverse B S hS f
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f))
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
      (inverseImageUnitFMap B S hS f) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map (inverseImageUnit B S hS f) :=
    Equiv.apply_symm_apply _ _
  rw [he] at hc
  have h1 : (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map α) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
        ((smallEtaleRingedTopos B S hS X).forgetRing.map α) :=
    MorphismOfTopoi.pushforwardRing_map_forget _ α
  have h2 := smallEtaleRingedToposHom_pushforwardRing_forget B S hS f H
  refine Eq.trans (congrArg (fun z => H.obj.map h.op z) ?_) hc.symm
  refine Eq.trans (congrArg (fun k => k.hom.app (op d.V)
      (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map α).hom.app (op d.V)
        ((inverseImageUnit B S hS f).hom.app (op d.V) s))) h2) ?_
  exact congrArg (fun w => ((smallEtaleRingedToposHom_pushforward B S hS f).hom.app
      (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS X) H)).hom.app (op d.V) w)
    (congrArg (fun k => k.hom.app (op d.V)
      ((inverseImageUnit B S hS f).hom.app (op d.V) s)) h1)

variable (x : GeometricPoint B S hS X.1)

/-- The fibre of `f⁻¹𝒪_Y` at a geometric point. -/
abbrev inverseImageStalkRing : CommRingCat.{u} :=
  ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).obj
    (inverseImageStructureSheaf B S hS f)

/-- Germ formation at `x` on `f⁻¹𝒪_Y`, as a homomorphism into the skyscraper with value the
fibre. -/
abbrev inverseImageSkyscraperUnit :
    inverseImageStructureSheaf B S hS f ⟶
      (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor.obj
        (inverseImageStalkRing B S hS f x) :=
  ((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction (A := CommRingCat.{u})).homEquiv
    (inverseImageStructureSheaf B S hS f) (inverseImageStalkRing B S hS f x) (𝟙 _)

/-- The fibre comparison `(𝒪_Y)_{f ∘ x} ⟶ (f⁻¹𝒪_Y)_x` of Stacks 04K2 (4). -/
abbrev inverseImageFiberComparison :
    ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).sheafFiber
        (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O ⟶
      inverseImageStalkRing B S hS f x :=
  (smallEtaleInverseImageFiberRingIso B S hS f x).hom.app (smallEtaleRingedTopos B S hS Y).O

/-- The fibre comparison is the transpose, across the skyscraper adjunction at the image point,
of the unit followed by the direct image of germ formation at `x` and the skyscraper comparison
of Stacks 03G8. -/
theorem inverseImageFiberComparison_eq :
    inverseImageFiberComparison B S hS f x =
      (((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction
            (A := CommRingCat.{u})).homEquiv (smallEtaleRingedTopos B S hS Y).O
          (inverseImageStalkRing B S hS f x)).symm
        (inverseImageUnit B S hS f ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
            (inverseImageSkyscraperUnit B S hS f x) ≫
          (smallEtaleSkyscraperRingIso B S hS f x).hom.app (inverseImageStalkRing B S hS f x)) := by
  have hk : ((smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.homEquiv
        (smallEtaleRingedTopos B S hS Y).O (inverseImageStructureSheaf B S hS f)).symm
      (inverseImageUnit B S hS f) = 𝟙 _ := by
    rw [Adjunction.homEquiv_counit]
    exact (smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.left_triangle_components _
  have h := Adjunction.conjugate_comp
    (smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction
    ((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction (A := CommRingCat.{u}))
    ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction
      (A := CommRingCat.{u}))
    (smallEtaleSkyscraperRingIso B S hS f x) (inverseImageUnit B S hS f) (𝟙 _) _
    (Equiv.apply_symm_apply _ _).symm
  rw [hk] at h
  refine Eq.trans ?_ h
  change _ = _ ≫ (etaleSitePoint B S hS X.1 x X.2).sheafFiber.map (𝟙 _) ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm.trans (Category.comp_id _).symm

/-- **The germ formula for the unit on charts.**  Given a commutative diagram of étale scheme
charts over `f` and compatible lifts of `x` and of its image into its two charts, the germ of the
value of the unit on charts at a regular function `s` of the lower chart is the fibre comparison
of Stacks 04K2 (4) applied to the germ of `s`. -/
theorem inverseImageUnitFMap_toPresheafFiber (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (p : GeometricFiber B S hS X.1 x d.U)
    (q : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V) (hpq : p.1 ≫ d.g = q.1)
    (s : (structurePresheaf B S hS Y.1).obj (op d.V)) :
    inverseImageFiberComparison B S hS f x
        ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V q
          (smallEtaleRingedTopos B S hS Y).O.obj s) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber d.U p
        (inverseImageStructureSheaf B S hS f).obj ((inverseImageUnitFMap B S hS f).app d s) := by
  have := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  have hgerm : (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V q
        (smallEtaleRingedTopos B S hS Y).O.obj ≫ inverseImageFiberComparison B S hS f x =
      (inverseImageUnit B S hS f ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
            (inverseImageSkyscraperUnit B S hS f x) ≫
          (smallEtaleSkyscraperRingIso B S hS f x).hom.app
            (inverseImageStalkRing B S hS f x)).hom.app (op d.V) ≫
        Pi.π (fun _ : GeometricFiber B S hS Y.1 (geometricPointMap f.hom x) d.V =>
          inverseImageStalkRing B S hS f x) q := by
    rw [inverseImageFiberComparison_eq]
    exact Point.toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleRingedTopos B S hS Y).O (inverseImageStalkRing B S hS f x) _ d.V q
  refine Eq.trans (ConcreteCategory.congr_hom hgerm s) ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (smallEtaleSkyscraperRingIso_hom_app_π B S hS f x (inverseImageStalkRing B S hS f x) d.V q)
    (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
        (inverseImageSkyscraperUnit B S hS f x)).hom.app (op d.V)
      ((inverseImageUnit B S hS f).hom.app (op d.V) s))) ?_
  rw [spacesBaseChangeFiberIso_inv_app B S hS f x d p q hpq]
  refine Eq.trans (ConcreteCategory.congr_hom (Point.skyscraperPresheaf_map_π
    (spacesEtaleSitePoint x) (baseChangeArrowOfChartDiagram B S hS f d)
    (inverseImageStalkRing B S hS f x) p) _).symm ?_
  refine Eq.trans (congrArg (fun z =>
    Pi.π (fun _ : GeometricFiber B S hS X.1 x d.U => inverseImageStalkRing B S hS f x) p z)
    (inverseImageUnit_postcomp_chart B S hS f
      ((spacesEtaleSitePoint x).skyscraperSheafFunctor.obj (inverseImageStalkRing B S hS f x))
      (inverseImageSkyscraperUnit B S hS f x) d (baseChangeArrowOfChartDiagram B S hS f d)
      (heq_of_eq (yoneda_map_baseChangeArrowOfChartDiagram B S hS f d)) s)) ?_
  exact ConcreteCategory.congr_hom (Point.skyscraperSheafAdjunction_unit_π
    (etaleSitePoint B S hS X.1 x X.2) (inverseImageStructureSheaf B S hS f) d.U p)
    ((inverseImageUnitFMap B S hS f).app d s)

end AlgebraicGeometry.Space

end
