module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpChartPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullbackSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# Chart projections of the direct image of a sheaf of commutative rings

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and `𝒜` a sheaf of commutative rings
on the small étale site of `X`. The sections of the direct image `f_*𝒜`, in its right Kan
extension form, over an étale chart `V` of `Y` are a limit over the étale scheme charts of `X`
above `X ×_Y V`, and the projection to each of them is a homomorphism of commutative rings.

This is the statement `AlgebraicGeometry.Space.meromorphicChartProjection` makes for the sheaf of
meromorphic functions, for an arbitrary sheaf of commutative rings. It is the first step of
reading a map `f⁻¹𝒪_Y ⟶ 𝒜` chart by chart as ring maps `𝒪_Y(V) ⟶ 𝒜(U)`, which the proof of
Stacks 05ZT uses to map the chart thickenings of a square-zero extension to the base.

## Main definitions

* `AlgebraicGeometry.Space.ringDirectImageRan`: `f_*𝒜` in its right Kan extension form, as a
  sheaf of commutative rings.
* `AlgebraicGeometry.Space.ringDirectImageRanChartProjection`: a chart projection of it, as a ring
  homomorphism.
* `AlgebraicGeometry.Space.pushforwardRingIsoRan`: the direct image of sheaves of commutative
  rings of Stacks 03G8 is the Ran form.
* `AlgebraicGeometry.Space.inverseImageHomChartRingHom`: the chart components
  `𝒪_Y(V) ⟶ 𝒜(U)` of a map `f⁻¹𝒪_Y ⟶ 𝒜` of sheaves of commutative rings.

## References

* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})

/-- `f_*𝒜`, with the direct image taken in its right Kan extension form. -/
noncomputable abbrev ringDirectImageRan : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} :=
  pullbackCommRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
    (smallEtaleDirectImageRan B S hS f) A

/-- The underlying sheaf of rings of `𝒜`. -/
noncomputable abbrev ringSheafOf : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj A

/-- The chart projection of `f_*𝒜`, as a homomorphism of commutative rings. -/
noncomputable def ringDirectImageRanChartProjection (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (ringDirectImageRan B S hS f A).obj.obj (op V) →+* A.obj.obj j.right where
  toFun := (chartProjection B S hS f V j).app
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).obj
      (ringSheafOf B S hS A))
  map_add' x y := (ringAddObj_naturality (ringSheafOf B S hS A)
      (chartProjection B S hS f V j) x y).trans
    (sectionsFunctor_map_ringAddHom (ringSheafOf B S hS A) j.right _ _)
  map_mul' x y := (ringMulObj_naturality (ringSheafOf B S hS A)
      (chartProjection B S hS f V j) x y).trans
    (sectionsFunctor_map_ringMulHom (ringSheafOf B S hS A) j.right _ _)
  map_zero' := (ringZeroObj_naturality (ringSheafOf B S hS A)
      (chartProjection B S hS f V j)).trans
    (sectionsFunctor_map_ringZeroHom (ringSheafOf B S hS A) j.right _)
  map_one' := (ringOneObj_naturality (ringSheafOf B S hS A)
      (chartProjection B S hS f V j)).trans
    (sectionsFunctor_map_ringOneHom (ringSheafOf B S hS A) j.right _)

/-- The direct image of sheaves of commutative rings along the morphism of small étale ringed
topoi of `f` is its right Kan extension form. -/
noncomputable def pushforwardRingIsoRan :
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.obj A ≅
      ringDirectImageRan B S hS f A :=
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCongr (SmallEtale.topology B S hS Y.1)
    (smallEtaleDirectImageRanIso B S hS f) A

/-- **The chart components of a map `f⁻¹𝒪_Y ⟶ 𝒜` of sheaves of commutative rings**: over an
étale chart `V` of `Y` and an étale chart of `X` above `X ×_Y V`, the ring homomorphism
`𝒪_Y(V) ⟶ 𝒜(U)` obtained from the adjoint `𝒪_Y ⟶ f_*𝒜` and the chart projection. -/
noncomputable def inverseImageHomChartRingHom
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V) →+* A.obj.obj j.right :=
  (ringDirectImageRanChartProjection B S hS f A V j).comp
    ((((smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.homEquiv _ _ φ) ≫
      (pushforwardRingIsoRan B S hS f A).hom).hom.app (op V)).hom

/-- The adjoint `𝒪_Y ⟶ f_*𝒜` of a map `φ : f⁻¹𝒪_Y ⟶ 𝒜` of sheaves of commutative rings, with the
direct image in its right Kan extension form, on underlying sheaves of sets. -/
noncomputable def inverseImageHomRanSet
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) :
    structureSetSheaf B S hS Y ⟶
      (smallEtaleDirectImageRan B S hS f).obj
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).obj
          (ringSheafOf B S hS A)) :=
  (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
    ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      ((smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.homEquiv _ _ φ ≫
        (pushforwardRingIsoRan B S hS f A).hom))

/-- The chart components of `φ` are the chart projections of its adjoint. -/
theorem inverseImageHomChartRingHom_apply
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS f A φ V j x =
      (chartProjection B S hS f V j).app _
        ((inverseImageHomRanSet B S hS f A φ).hom.app (op V) x) :=
  rfl

/-- On underlying sheaves of sets, composing with the comparison of the two forms of the direct
image of sheaves of commutative rings composes with the comparison of the sets-forms. -/
private theorem forget_map_comp_pushforwardRingIsoRan_hom
    {R : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}}
    (m : R ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.obj A) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        (m ≫ (pushforwardRingIsoRan B S hS f A).hom) =
      (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map m ≫
        (smallEtaleDirectImageRanIso B S hS f).hom.app
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj A) :=
  (Functor.map_comp _ _ _).trans (congrArg _
    (Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCongrMap_forget
      (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImageRanIso B S hS f).hom A))

/-- The adjoint of `φ` on underlying sheaves of sets is the adjoint, for sheaves of sets, of the
underlying map of `φ`, followed by the comparison of the two forms of the direct image. -/
theorem inverseImageHomRanSet_eq
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) :
    inverseImageHomRanSet B S hS f A φ =
      (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map φ) ≫
        (smallEtaleDirectImageRanIso B S hS f).hom.app _ := by
  rw [← MorphismOfTopoi.ringAdjunction_homEquiv_forget]
  exact forget_map_comp_pushforwardRingIsoRan_hom B S hS f A _

/-- The adjoint of a composite `φ ≫ ε` is the adjoint of `φ` followed by the direct image of
`ε`. -/
theorem inverseImageHomRanSet_comp
    {A' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (ε : A ⟶ A') :
    inverseImageHomRanSet B S hS f A' (φ ≫ ε) =
      inverseImageHomRanSet B S hS f A φ ≫ (smallEtaleDirectImageRan B S hS f).map
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ε) := by
  rw [inverseImageHomRanSet_eq, inverseImageHomRanSet_eq]
  refine (congrArg (· ≫ (smallEtaleDirectImageRanIso B S hS f).hom.app _)
    ((congrArg ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _)
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map_comp
        φ ε)).trans
      ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv_naturality_right _ _))).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((smallEtaleDirectImageRanIso B S hS f).hom.naturality _)).trans (Category.assoc _ _ _).symm)

/-- **The chart components of `φ` are natural in the target**: for `ε : 𝒜 ⟶ 𝒜'` the chart
components of `φ ≫ ε` are those of `φ` followed by `ε`. -/
theorem inverseImageHomChartRingHom_comp
    {A' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (ε : A ⟶ A') (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS f A' (φ ≫ ε) V j x =
      ε.hom.app j.right (inverseImageHomChartRingHom B S hS f A φ V j x) := by
  rw [inverseImageHomChartRingHom_apply, inverseImageHomChartRingHom_apply,
    inverseImageHomRanSet_comp]
  exact chartProjection_app_map B S hS f V
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ε) j _

/-- The adjoint of the inverse-image form of the structure map of `f` is the Kan-extension form
of the structure map. -/
theorem inverseImageHomRanSet_fSharpInverseImage :
    inverseImageHomRanSet B S hS f (smallEtaleRingedTopos B S hS X).O
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage =
      structureSharpRanSet B S hS f := by
  refine Eq.trans ?_ (structureSharpSet_comp_ranIso B S hS f)
  have h : (smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction.homEquiv _ _
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage =
        structureSharpCommRing B S hS f :=
    Equiv.apply_symm_apply ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
      (smallEtaleRingedToposHom B S hS f).toToposHom).homEquiv _ _)
      (smallEtaleRingedToposHom B S hS f).fSharp
  refine (congrArg (fun m ↦ (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
    ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (m ≫ (pushforwardRingIsoRan B S hS f (smallEtaleRingedTopos B S hS X).O).hom))) h).trans ?_
  exact (forget_map_comp_pushforwardRingIsoRan_hom B S hS f _ _).trans
    (congrArg (· ≫ _) (congrArg (sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget RingCat.{u})).map (map_structureSharpCommRing B S hS f)))

/-- **The chart components of the inverse-image form of the structure map are pullback of
functions along the induced morphisms of charts.** -/
theorem inverseImageHomChartRingHom_fSharpInverseImage (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS f (smallEtaleRingedTopos B S hS X).O
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage V j x =
      chartPullback B S hS f V j x := by
  refine (congrArg (fun m ↦ (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
    (m.hom.app (op V) x)) (inverseImageHomRanSet_fSharpInverseImage B S hS f)).trans ?_
  exact chartProjection_structureMapApp B S hS f V j x

/-- The chart component of `φ` at the cartesian form of a chart diagram is the component at
that diagram of the `f`-map (Stacks 03G4) of the adjoint of `φ`. -/
theorem inverseImageHomChartRingHom_eq_ranFmap
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) :
    inverseImageHomChartRingHom B S hS f A φ d.V (indexOfChartDiagram B S hS f d) x =
      (ranFmap B S hS f _ (structureSetSheaf B S hS Y)
        (inverseImageHomRanSet B S hS f A φ)).app d x :=
  chartProjection_app B S hS f _ d.V (indexOfChartDiagram B S hS f d) _

/-- **The chart components of `φ` are compatible with simultaneous étale restriction of the two
charts of a chart diagram.** -/
theorem inverseImageHomChartRingHom_naturality
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map j)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) :
    inverseImageHomChartRingHom B S hS f A φ d'.V (indexOfChartDiagram B S hS f d')
        ((smallEtaleRingedTopos B S hS Y).O.obj.map j.op x) =
      A.obj.map i.op (inverseImageHomChartRingHom B S hS f A φ d.V
        (indexOfChartDiagram B S hS f d) x) :=
  ((inverseImageHomChartRingHom_eq_ranFmap B S hS f A φ d' _).trans
      ((ranFmap B S hS f _ (structureSetSheaf B S hS Y)
        (inverseImageHomRanSet B S hS f A φ)).naturality d d' i j h x)).trans
    (congrArg (A.obj.map i.op)
      (inverseImageHomChartRingHom_eq_ranFmap B S hS f A φ d x).symm)

end AlgebraicGeometry.Space

end
