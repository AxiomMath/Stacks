module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartToBase

/-!
# The chart transport of a section of `f⁻¹h_V` along compositions and base change

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `d` a diagram of étale charts `U ⟶ V`
over `f`.  The section `AlgebraicGeometry.Space.chartDiagramSection` of `f⁻¹h_V` over `U`
gives, through `AlgebraicGeometry.Space.inverseImageSectionTransport`, a map
`(f_*P)(V) ⟶ P(U)` natural in the sheaf of sets `P` on `X_étale`.  This file computes it.

* It is the component at `d` of the `f`-map of Stacks 03G3 which the chart correspondence of
  Stacks 03G4/03G8 attaches to the identity of `f_*P`
  (`AlgebraicGeometry.Space.inverseImageSectionTransport_chartDiagramSection`).
* It is compatible with composition: for `a : X ⟶ Y`, `b : Y ⟶ Z` and a diagram over `a ≫ b`
  factoring through a chart of `Y`, the transport along `a ≫ b`, after the composition
  isomorphism `b_*a_* ≅ (a ≫ b)_*`, is the transport along `b` followed by the transport along
  `a` (`AlgebraicGeometry.Space.inverseImageSectionTransport_comp`, and its ring form
  `AlgebraicGeometry.Space.invRepRingHom_comp`).
* For a representable `a`, it is the comparison of the direct image with restriction along
  base change of charts, followed by restriction along the induced map of `U` into the
  base-changed chart (`AlgebraicGeometry.Space.inverseImageSectionTransport_representable`).

The key input is that the two constructions of the chart correspondence in this tree,
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse` and
`AlgebraicGeometry.Space.fmapDirectImageEquiv`, are equal: both satisfy the sectionwise
characterization `AlgebraicGeometry.Space.IsChartCorrespondence`, which determines the
bijection (`AlgebraicGeometry.Space.IsChartCorrespondence.symm_apply_eq`).  The composition
law then is the chart formula `AlgebraicGeometry.Space.FMap.comp_app`, and the base-change
formula is the description of the comparison as a chart projection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] smallEtaleTopology_subcanonical

/-! ### Uniqueness of the chart correspondence -/

section Unique

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The sectionwise characterization determines the chart correspondence.** Two bijections
between `f`-maps and homomorphisms into the direct image which both satisfy
`AlgebraicGeometry.Space.IsChartCorrespondence` have the same inverse. -/
theorem IsChartCorrespondence.symm_apply_eq
    {P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    {Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)}
    {e e' : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj ≃
      (Q ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj P)}
    (he : IsChartCorrespondence B S hS f P Q e) (he' : IsChartCorrespondence B S hS f P Q e')
    (ψ : Q ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj P) :
    e.symm ψ = e'.symm ψ := by
  refine FMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  let H := (smallEtaleComparisonRestriction B S hS X).objPreimage P
  let i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H :=
    ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso P).symm
  have hh : HEq (((SpacesEtale.toSpaces B S hS X).map (chartLift B S hS f d) ≫
      (spacesBaseChange B S hS f).projection.app
        ((comparisonFunctor B S hS Y).obj d.V)).hom) (yoneda.map d.g) :=
    heq_of_eq (congrArg (fun q ↦ q.hom) (chartLift_projection B S hS f d))
  have h1 := he H i (e.symm ψ) d (chartLift B S hS f d) hh s
  have h2 := he' H i (e'.symm ψ) d (chartLift B S hS f d) hh s
  simp only [Equiv.apply_symm_apply] at h1 h2
  have hi : ∀ t, i.inv.hom.app (op d.U) (i.hom.hom.app (op d.U) t) = t := fun t ↦
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k ↦ k.hom) i.hom_inv_id) (op d.U)) t
  exact (hi _).symm.trans
    ((congrArg (fun t ↦ i.inv.hom.app (op d.U) t) (h1.trans h2.symm)).trans (hi _))

/-- The two constructions of the chart correspondence agree:
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse` (through the spaces-étale
presentation) and `AlgebraicGeometry.Space.fmapDirectImageEquiv` (through the right Kan
extension) are the same bijection. -/
theorem fMapEquivPushforwardHom_ringUniverse_eq_fmapDirectImageEquiv
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) :
    fMapEquivPushforwardHom_ringUniverse B S hS f P Q = fmapDirectImageEquiv B S hS f P Q :=
  Equiv.symm_bijective.injective (Equiv.ext fun ψ ↦
    IsChartCorrespondence.symm_apply_eq B S hS f
      (fMapEquivPushforwardHom_ringUniverse_chart B S hS f P Q)
      (fmapDirectImageEquiv_isChartCorrespondence B S hS f P Q) ψ)

end Unique

/-! ### The transport is the canonical `f`-map -/

section Transport

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The transport attached to a diagram of charts is the canonical `f`-map.** For a diagram
`d` of étale charts over `f` and a sheaf of sets `P` on the small étale site of `X`, the
transport `(f_*P)(V) ⟶ P(U)` along the section `AlgebraicGeometry.Space.chartDiagramSection`
is the component at `d` of the `f`-map which the chart correspondence attaches to the
identity of `f_*P`. -/
theorem inverseImageSectionTransport_chartDiagramSection
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj P).obj.obj (op d.V)) :
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) d.V d.U
        (chartDiagramSection B S hS f d)).app P x =
      ((fmapDirectImageEquiv B S hS f P
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj P)).symm
          (𝟙 _)).app d x := by
  let g := smallEtaleRingedToposHom B S hS f
  let J := SmallEtale.topology B S hS Y.1
  let ε : invRep g d.V ⟶ P := (g.toToposHom.adj.homEquiv _ _).symm (J.yonedaEquiv.symm x)
  change ε.hom.app (op d.U) (chartDiagramSection B S hS f d) = _
  have h1 := fMapEquivPushforwardHom_ringUniverse_symm_app_map B S hS f (invRep g d.V) P
    (J.yoneda.obj d.V) ε (g.toToposHom.adj.unit.app _) d (J.yonedaEquiv (𝟙 _))
  have h2 : g.toToposHom.adj.unit.app (J.yoneda.obj d.V) ≫ g.toToposHom.pushforward.map ε =
      J.yonedaEquiv.symm x ≫ 𝟙 _ :=
    (g.toToposHom.adj.homEquiv_unit _ _ ε).symm.trans
      (((g.toToposHom.adj.homEquiv _ _).apply_symm_apply _).trans (Category.comp_id _).symm)
  refine h1.symm.trans ?_
  refine (congrArg (fun ψ ↦ ((fMapEquivPushforwardHom_ringUniverse B S hS f P
    (J.yoneda.obj d.V)).symm ψ).app d (J.yonedaEquiv (𝟙 _))) h2).trans ?_
  refine (fMapEquivPushforwardHom_ringUniverse_symm_comp_app B S hS f P
    (J.yonedaEquiv.symm x) (𝟙 _) d (J.yonedaEquiv (𝟙 _))).trans ?_
  have hx : (J.yonedaEquiv.symm x).hom.app (op d.V) (J.yonedaEquiv (𝟙 _)) = x :=
    FunctorToTypes.map_id_apply (g.toToposHom.pushforward.obj P).obj x
  rw [hx, fMapEquivPushforwardHom_ringUniverse_eq_fmapDirectImageEquiv]
  rfl

end Transport

/-! ### Composition -/

section Comp

variable {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The composition law for chart transport.** Let `d₁` be a diagram of étale charts
`U ⟶ V` over `a : X ⟶ Y`, and `g₂ : V ⟶ W'` a diagram of étale charts over `b : Y ⟶ Z`.  For a
sheaf of sets `P` on `X_étale`, the transport along the composite diagram `U ⟶ W'` over
`a ≫ b`, after the composition isomorphism `b_*(a_*P) ≅ (a ≫ b)_*P`, is the transport along
`V ⟶ W'` (for the sheaf `a_*P`) followed by the transport along `U ⟶ V`. -/
theorem inverseImageSectionTransport_comp (d₁ : ChartDiagram B S hS X.1 Y.1 a.hom)
    {W' : SmallEtale B S hS Z.1}
    (g₂ : (SmallEtale.toOver B S hS Y.1).obj d₁.V ⟶ (SmallEtale.toOver B S hS Z.1).obj W')
    (hg₂ : d₁.V.1.hom ≫ b.hom = yoneda.map g₂ ≫ W'.1.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleRingedToposHom B S hS b).toToposHom.pushforward.obj
      ((smallEtaleRingedToposHom B S hS a).toToposHom.pushforward.obj P)).obj.obj (op W')) :
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS (a ≫ b)) W' d₁.U
        (chartDiagramSection B S hS (a ≫ b)
          (ChartDiagram.comp B S hS a b d₁.g g₂ d₁.comm hg₂))).app P
        (((smallToposMorphismTypeU_comp B S hS a b).hom.app P).hom.app (op W') x) =
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS a) d₁.V d₁.U
          (chartDiagramSection B S hS a d₁)).app P
        ((inverseImageSectionTransport (smallEtaleRingedToposHom B S hS b) W' d₁.V
          (chartDiagramSection B S hS b ⟨d₁.V, W', g₂, hg₂⟩)).app
            ((smallEtaleRingedToposHom B S hS a).toToposHom.pushforward.obj P) x) := by
  let Q := (smallEtaleRingedToposHom B S hS a).toToposHom.pushforward.obj P
  let R := (smallEtaleRingedToposHom B S hS b).toToposHom.pushforward.obj Q
  let ξ : FMap B S hS Y.1 Z.1 b.hom Q.obj R.obj :=
    (fmapDirectImageEquiv B S hS b Q R).symm (𝟙 _)
  let η : FMap B S hS X.1 Y.1 a.hom P.obj Q.obj :=
    (fmapDirectImageEquiv B S hS a P Q).symm (𝟙 _)
  have hθ : (fmapDirectImageEquiv B S hS (a ≫ b) P R).symm
      ((smallToposMorphismTypeU_comp B S hS a b).hom.app P) =
        FMap.comp B S hS a b P Q R ξ η := by
    refine FMap.comp_unique B S hS a b P Q R ξ η _ ?_
    have e1 : fmapDirectImageEquiv B S hS b Q R ξ = 𝟙 R := Equiv.apply_symm_apply _ _
    have e2 : fmapDirectImageEquiv B S hS a P Q η = 𝟙 Q := Equiv.apply_symm_apply _ _
    refine (Equiv.apply_symm_apply _ _).trans ?_
    rw [e1, e2]
    exact (Category.id_comp _).symm.trans ((Category.id_comp _).symm.trans
      (congrArg (fun m ↦ 𝟙 R ≫ m ≫ (smallToposMorphismTypeU_comp B S hS a b).hom.app P)
        ((smallEtaleDirectImage B S hS b).map_id Q).symm))
  refine (inverseImageSectionTransport_chartDiagramSection B S hS (a ≫ b)
    (ChartDiagram.comp B S hS a b d₁.g g₂ d₁.comm hg₂) P _).trans ?_
  refine Eq.trans ?_ (inverseImageSectionTransport_chartDiagramSection B S hS a d₁ P _).symm
  refine Eq.trans ?_ (congrArg (fun t ↦ η.app d₁ t)
    (inverseImageSectionTransport_chartDiagramSection B S hS b ⟨d₁.V, W', g₂, hg₂⟩ Q x)).symm
  refine Eq.trans ?_ (FMap.comp_app B S hS a b d₁.g g₂ d₁.comm hg₂ P Q R ξ η x)
  refine Eq.trans ?_ (congrArg (fun θ : FMap B S hS X.1 Z.1 (a ≫ b).hom P.obj R.obj ↦
    θ.app (ChartDiagram.comp B S hS a b d₁.g g₂ d₁.comm hg₂) x) hθ)
  refine Eq.trans ?_ (congrArg (fun m ↦ ((fmapDirectImageEquiv B S hS (a ≫ b) P R).symm m).app
    (ChartDiagram.comp B S hS a b d₁.g g₂ d₁.comm hg₂) x)
      (Category.comp_id ((smallToposMorphismTypeU_comp B S hS a b).hom.app P)))
  rfl

/-- **The composition law for chart transport, for sheaves of commutative rings.** This is
`AlgebraicGeometry.Space.inverseImageSectionTransport_comp` on the underlying sheaf of sets:
the comparison `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` is, on underlying
sheaves of sets, the composition isomorphism
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`. -/
theorem invRepRingHom_comp (d₁ : ChartDiagram B S hS X.1 Y.1 a.hom)
    {W' : SmallEtale B S hS Z.1}
    (g₂ : (SmallEtale.toOver B S hS Y.1).obj d₁.V ⟶ (SmallEtale.toOver B S hS Z.1).obj W')
    (hg₂ : d₁.V.1.hom ≫ b.hom = yoneda.map g₂ ≫ W'.1.hom)
    (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (x : ToType (((pushforwardCommRingFunctor ((smallEtaleRingedToposHom B S hS b).comp
      (smallEtaleRingedToposHom B S hS a)).toToposHom).obj R).obj.obj (op W'))) :
    invRepRingHom B S hS (a ≫ b) R W' d₁.U
        (chartDiagramSection B S hS (a ≫ b)
          (ChartDiagram.comp B S hS a b d₁.g g₂ d₁.comm hg₂))
        (((smallEtaleRingedToposHom_compRingIso B S hS a b).hom.app R).hom.app (op W') x) =
      invRepRingHom B S hS a R d₁.V d₁.U (chartDiagramSection B S hS a d₁)
        (invRepRingHom B S hS b
          ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS a).toToposHom).obj R)
          W' d₁.V (chartDiagramSection B S hS b ⟨d₁.V, W', g₂, hg₂⟩) x) := by
  have h := congrArg (fun m ↦ m.hom.app (op W') x)
    (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Z.1) R (smallToposMorphismTypeU_comp B S hS a b))
  refine (congrArg (fun y ↦ (inverseImageSectionTransport
    (smallEtaleRingedToposHom B S hS (a ≫ b)) W' d₁.U
      (chartDiagramSection B S hS (a ≫ b)
        (ChartDiagram.comp B S hS a b d₁.g g₂ d₁.comm hg₂))).app
      (Stacks.underlyingRingSheaf (SmallEtale.topology B S hS X.1) R) y) h).trans ?_
  exact inverseImageSectionTransport_comp B S hS a b d₁ g₂ hg₂
    (Stacks.underlyingRingSheaf (SmallEtale.topology B S hS X.1) R) x

end Comp

/-! ### Representable morphisms -/

section Representable

variable {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y) (hf : yoneda.relativelyRepresentable a.hom)

/-- The morphism of étale charts of `X` from the upper chart `U` of a diagram of charts over a
representable `a` into the base-changed chart `X ×_Y V` of its lower chart: the lift into the
cartesian square of the structure map of `U` and the vertical morphism of the diagram. -/
def chartDiagramBaseChangeLift (d : ChartDiagram B S hS X.1 Y.1 a.hom) :
    d.U ⟶ (smallBaseChange B S hS a hf).obj d.V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (hf.lift d.U.1.hom d.g d.comm)
    (hf.lift_fst _ _ _))

/-- The lift into the base-changed chart, followed by the cartesian projection, is the vertical
morphism of the diagram. -/
theorem chartDiagramBaseChangeLift_snd (d : ChartDiagram B S hS X.1 Y.1 a.hom) :
    (SmallEtale.toOver B S hS X.1).map (chartDiagramBaseChangeLift B S hS a hf d) ≫
      hf.snd d.V.1.hom = d.g :=
  hf.lift_snd _ _ _

/-- A morphism of étale charts into the base-changed chart lying over the vertical morphism of a
diagram of charts is, after the comparison of the two base changes, the cartesian form
`AlgebraicGeometry.Space.chartLift` of the diagram. -/
theorem comparisonFunctor_map_comp_smallBaseChangeComparisonIso
    (d : ChartDiagram B S hS X.1 Y.1 a.hom) (k : d.U ⟶ (smallBaseChange B S hS a hf).obj d.V)
    (hk : (SmallEtale.toOver B S hS X.1).map k ≫ hf.snd d.V.1.hom = d.g) :
    (comparisonFunctor B S hS X).map k ≫ (smallBaseChangeComparisonIso B S hS a hf d.V).hom =
      chartLift B S hS a d := by
  refine chartLift_unique B S hS a d _ ?_
  have h3 : (SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k ≫
        (smallBaseChangeComparisonIso B S hS a hf d.V).hom) ≫
        (spacesBaseChange B S hS a).projection.app ((comparisonFunctor B S hS Y).obj d.V) =
      (SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k) ≫
        (smallBaseChange_projection B S hS a hf).app d.V := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS X).map
      ((comparisonFunctor B S hS X).map k) ≫ m)
      (smallBaseChangeComparisonIso_hom_projection B S hS a hf d.V)
  refine (congrArg (fun q ↦ q.hom) h3).trans ?_
  change ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k)).hom ≫
    yoneda.map (hf.snd d.V.1.hom) = _
  rw [toSpaces_comparisonFunctor_map_hom B S hS X k]
  exact (yoneda.map_comp _ _).symm.trans (congrArg (fun m ↦ yoneda.map m) hk)

/-- **The chart transport of a representable morphism is restriction along base change**, for
an arbitrary morphism `k` of étale charts from the upper chart into the base-changed chart lying
over the vertical morphism of the diagram. -/
theorem inverseImageSectionTransport_representable_of
    (d : ChartDiagram B S hS X.1 Y.1 a.hom) (k : d.U ⟶ (smallBaseChange B S hS a hf).obj d.V)
    (hk : (SmallEtale.toOver B S hS X.1).map k ≫ hf.snd d.V.1.hom = d.g)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (y : ((smallEtaleRingedToposHom B S hS a).toToposHom.pushforward.obj P).obj.obj (op d.V)) :
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS a) d.V d.U
        (chartDiagramSection B S hS a d)).app P y =
      P.obj.map k.op (((chartComparison B S hS a hf).hom.app P).hom.app (op d.V) y) := by
  refine (inverseImageSectionTransport_chartDiagramSection B S hS a d P y).trans ?_
  let φ : smallBaseChangeIndex B S hS a hf d.V ⟶ indexOfChartDiagram B S hS a d :=
    StructuredArrow.homMk k.op (congrArg Quiver.Hom.op
      (comparisonFunctor_map_comp_smallBaseChangeComparisonIso B S hS a hf d k hk))
  exact (ranChartCone_π_comp B S hS X P.obj (chartBaseChange B S hS a d.V) φ
    (((smallEtaleDirectImageRanIso B S hS a).hom.app P).hom.app (op d.V) y)).symm

/-- **The chart transport of a representable morphism is restriction along base change.** For a
representable `a : X ⟶ Y`, a diagram `d` of étale charts `U ⟶ V` over `a` and a sheaf of sets `P`
on `X_étale`, the transport `(a_*P)(V) ⟶ P(U)` is the comparison
`AlgebraicGeometry.Space.chartComparison` of `(a_*P)(V)` with `P(X ×_Y V)`, followed by
restriction along the lift `U ⟶ X ×_Y V`. -/
theorem inverseImageSectionTransport_representable
    (d : ChartDiagram B S hS X.1 Y.1 a.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (y : ((smallEtaleRingedToposHom B S hS a).toToposHom.pushforward.obj P).obj.obj (op d.V)) :
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS a) d.V d.U
        (chartDiagramSection B S hS a d)).app P y =
      P.obj.map (chartDiagramBaseChangeLift B S hS a hf d).op
        (((chartComparison B S hS a hf).hom.app P).hom.app (op d.V) y) :=
  inverseImageSectionTransport_representable_of B S hS a hf d _
    (chartDiagramBaseChangeLift_snd B S hS a hf d) P y

end Representable

end AlgebraicGeometry.Space

end
