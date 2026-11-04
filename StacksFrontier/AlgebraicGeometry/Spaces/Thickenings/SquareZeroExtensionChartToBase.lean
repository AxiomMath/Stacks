module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartRingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartSchemeHom

/-!
# The thickened charts of a square-zero extension over the charts of the base

WIP
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The component of `AlgebraicGeometry.Scheme.restrictFunctorΓ` at an open is `topIso`. -/
theorem _root_.AlgebraicGeometry.Scheme.restrictFunctorΓ_app_eq_topIso {T : Scheme.{u}}
    (Q : T.Opens) : (Scheme.restrictFunctorΓ (X := T)).app (op Q) = Q.topIso :=
  Iso.ext ((congrArg T.presheaf.map (Subsingleton.elim _ _)))

/-- Restricting a morphism of schemes to opens commutes, on global sections, with the
identification `topIso` of the global sections of an open subscheme with the sections over the
open. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.topIso_inv_resLE_appTop {T W : Scheme.{u}}
    (φ : T ⟶ W) (O : W.Opens) (Q : T.Opens) (h : Q ≤ φ ⁻¹ᵁ O) :
    O.topIso.inv ≫ (φ.resLE O Q h).appTop ≫ Q.topIso.hom = φ.appLE O Q h := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- `topIso` is natural in the open. -/
theorem _root_.AlgebraicGeometry.Scheme.topIso_inv_homOfLE_appTop {T : Scheme.{u}}
    {O₁ O₂ : T.Opens} (h : O₂ ≤ O₁) :
    O₁.topIso.inv ≫ (T.homOfLE h).appTop = T.presheaf.map (homOfLE h).op ≫ O₂.topIso.inv := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv]
  exact (T.presheaf.map_comp _ _).symm.trans
    ((congrArg T.presheaf.map (Subsingleton.elim _ _)).trans (T.presheaf.map_comp _ _))

/-- Restricting a composite of morphisms of schemes to opens factors through the restriction of
the second one. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.resLE_comp_eq {T V W : Scheme.{u}} (φ : T ⟶ V)
    (c : V ⟶ W) (O : W.Opens) (Q : T.Opens) (h₁ : Q ≤ (φ ≫ c) ⁻¹ᵁ O)
    (h₂ : Q ≤ φ ⁻¹ᵁ (c ⁻¹ᵁ O)) :
    (φ ≫ c).resLE O Q h₁ = φ.resLE (c ⁻¹ᵁ O) Q h₂ ≫ (c ∣_ O) := by
  refine (cancel_mono O.ι).mp ?_
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι, Category.assoc]

section RingHom

attribute [local instance] smallEtaleTopology_subcanonical

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The transformation `(g_*E)(V) ⟶ E(U)` of `AlgebraicGeometry.Space.inverseImageSectionTransport`
on an arbitrary sheaf of commutative rings `R` on the small étale site of `X`, as a ring map for
the transported ring structure on the sections of the direct image. -/
def invRepRingHom (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep (smallEtaleRingedToposHom B S hS f) V).obj.obj (op U)) :
    ToType (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        R).obj.obj (op V)) →+* ToType (R.obj.obj (op U)) where
  toFun x := (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V U s).app
    (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := SmallEtale.topology B S hS X.1) R)) x
  map_one' := (Sheaf.ringOneObj_naturality
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V U s)).trans
    (Sheaf.sectionsFunctor_map_ringOneHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (op U) default)
  map_mul' x y := (Sheaf.ringMulObj_naturality
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V U s) x y).trans
    (Sheaf.sectionsFunctor_map_ringMulHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (op U) _ _)
  map_zero' := (Sheaf.ringZeroObj_naturality
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V U s)).trans
    (Sheaf.sectionsFunctor_map_ringZeroHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (op U) default)
  map_add' x y := (Sheaf.ringAddObj_naturality
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V U s) x y).trans
    (Sheaf.sectionsFunctor_map_ringAddHom
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := SmallEtale.topology B S hS X.1) R)
      (op U) _ _)

/-- The chart correspondence of Stacks 03G8 is natural in the sheaf on the target: precomposing
the homomorphism into the direct image with a morphism of sheaves on the small étale site of `Y`
precomposes every map of sections of the `f`-map with it. -/
theorem fMapEquivPushforwardHom_ringUniverse_symm_comp_app
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {G G' : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)} (β : G' ⟶ G)
    (ψ : G ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (x : G'.obj.obj (op d.V)) :
    ((fMapEquivPushforwardHom_ringUniverse B S hS f F G').symm (β ≫ ψ)).app d x =
      ((fMapEquivPushforwardHom_ringUniverse B S hS f F G).symm ψ).app d (β.hom.app _ x) :=
  rfl

/-- **The section of `g⁻¹h_V` attached to a diagram of étale charts over `f`**, for
`g = (f_small, f♯)`: the image of the identity of `V` under the map of sections over the diagram
which the chart correspondence attaches to the unit `h_V ⟶ g_*g⁻¹h_V`. -/
def chartDiagramSection (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (invRep (smallEtaleRingedToposHom B S hS f) d.V).obj.obj (op d.U) :=
  ((fMapEquivPushforwardHom_ringUniverse B S hS f
      (invRep (smallEtaleRingedToposHom B S hS f) d.V)
      ((SmallEtale.topology B S hS Y.1).yoneda.obj d.V)).symm
    ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app _)).app d
    ((SmallEtale.topology B S hS Y.1).yonedaEquiv (𝟙 _))

/-- **The ring map attached to the section of a diagram of charts is pullback of functions along
its vertical morphism.** -/
theorem chartRingHom_chartDiagramSection (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartRingHom (smallEtaleRingedToposHom B S hS f) d.V d.U (chartDiagramSection B S hS f d) =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) := by
  ext b
  obtain ⟨b, rfl⟩ : ∃ b' : (setO Y).obj.obj (op d.V), b' = b := ⟨b, rfl⟩
  let g := smallEtaleRingedToposHom B S hS f
  let Φ := fMapEquivPushforwardHom_ringUniverse B S hS f
  let G := (SmallEtale.topology B S hS Y.1).yoneda.obj d.V
  refine (chartRingHom_apply g d.V d.U _ b).trans ?_
  have h2 : FMap.compSource B S hS f ((Φ (invRep g d.V) G).symm (g.toToposHom.adj.unit.app _))
      (invCoord g d.V b).hom =
      (Φ (setO X) G).symm (g.toToposHom.adj.unit.app _ ≫
        g.toToposHom.pushforward.map (invCoord g d.V b)) := by
    apply (Φ (setO X) G).injective
    rw [Equiv.apply_symm_apply, fMapEquivPushforwardHom_ringUniverse_source_map,
      Equiv.apply_symm_apply]
  have h3 : g.toToposHom.adj.unit.app G ≫ g.toToposHom.pushforward.map (invCoord g d.V b) =
      (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm b ≫ RingedToposHom.forgetFSharp g :=
    (g.toToposHom.adj.homEquiv_unit _ _ _).symm.trans
      ((congrArg (g.toToposHom.adj.homEquiv _ _) (homEquiv_symm_forgetFSharp g d.V b).symm).trans
        ((Equiv.apply_symm_apply _ _).trans
          (GrothendieckTopology.yonedaEquiv_symm_naturality_right _ _ _ _).symm))
  refine (congrArg (fun ξ : FMap B S hS X.1 Y.1 f.hom (setO X).obj G.obj =>
    ξ.app d ((SmallEtale.topology B S hS Y.1).yonedaEquiv (𝟙 _))) h2).trans ?_
  refine (congrArg (fun ψ => ((Φ (setO X) G).symm ψ).app d
    ((SmallEtale.topology B S hS Y.1).yonedaEquiv (𝟙 _))) h3).trans ?_
  refine (fMapEquivPushforwardHom_ringUniverse_symm_comp_app B S hS f _ _ _ d _).trans ?_
  have hb : ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm b).hom.app (op d.V)
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv (𝟙 _)) = b :=
    Functor.map_id_apply (setO Y).obj _ b
  refine (congrArg (((fMapEquivPushforwardHom_ringUniverse B S hS f (setO X) (setO Y)).symm
    g.forgetFSharp).app d) hb).trans ?_
  exact structureFMap_app B S hS f d b

/-- The transport of a section of `g⁻¹h_V` is natural in the sheaf of rings. -/
theorem invRepRingHom_naturality {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (φ : R ⟶ R') (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (s : (invRep (smallEtaleRingedToposHom B S hS f) V).obj.obj (op U))
    (x : ToType (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        R).obj.obj (op V))) :
    φ.hom.app (op U) (invRepRingHom B S hS f R V U s x) =
      invRepRingHom B S hS f R' V U s
        (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
            ((sheafCompose (SmallEtale.topology B S hS X.1)
              (forget₂ CommRingCat.{u} RingCat.{u})).map φ))).hom.app (op V) x) := by
  have h := NatTrans.naturality_apply
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V U s)
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      ((sheafCompose (SmallEtale.topology B S hS X.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) x
  exact h.symm

/-- The ring transport of a section of `g⁻¹h_V` is natural in the chart of the source. -/
theorem invRepRingHom_restrict (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (V : SmallEtale B S hS Y.1) {U U' : SmallEtale B S hS X.1} (i : U' ⟶ U)
    (s : (invRep (smallEtaleRingedToposHom B S hS f) V).obj.obj (op U))
    (x : ToType (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        R).obj.obj (op V))) :
    invRepRingHom B S hS f R V U'
        ((invRep (smallEtaleRingedToposHom B S hS f) V).obj.map i.op s) x =
      R.obj.map i.op (invRepRingHom B S hS f R V U s x) :=
  NatTrans.naturality_apply (((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _).symm
    ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x)).hom i.op s

/-- The transport of a section of `g⁻¹h_V` is natural in the chart of the target. -/
theorem inverseImageSectionTransport_map (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (U : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1} (c : V' ⟶ V)
    (s' : (invRep (smallEtaleRingedToposHom B S hS f) V').obj.obj (op U))
    (x : ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj.obj (op V)) :
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V U
        (((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
          ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U) s')).app F x =
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) V' U s').app F
        (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F).obj.map c.op x) := by
  let g := smallEtaleRingedToposHom B S hS f
  have key : g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map c) ≫
      (g.toToposHom.adj.homEquiv _ _).symm ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x) =
      (g.toToposHom.adj.homEquiv _ _).symm ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
        ((g.toToposHom.pushforward.obj F).obj.map c.op x)) := by
    rw [← Adjunction.homEquiv_naturality_left_symm,
      GrothendieckTopology.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun m => m.hom.app (op U) s') key

/-- The ring transport of a section of `g⁻¹h_V` is natural in the chart of the target. -/
theorem invRepRingHom_map (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (U : SmallEtale B S hS X.1) {V V' : SmallEtale B S hS Y.1} (c : V' ⟶ V)
    (s' : (invRep (smallEtaleRingedToposHom B S hS f) V').obj.obj (op U))
    (x : ToType (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        R).obj.obj (op V))) :
    invRepRingHom B S hS f R V U (((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U) s') x =
      invRepRingHom B S hS f R V' U s'
        (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
          R).obj.map c.op x) :=
  inverseImageSectionTransport_map B S hS f _ U c s' x

/-- **The section attached to a diagram of charts is natural in the diagram.** -/
theorem chartDiagramSection_naturality (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (a : d'.U ⟶ d.U) (b : d'.V ⟶ d.V)
    (hab : (SmallEtale.toOver B S hS X.1).map a ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map b) :
    ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map b)).hom.app (op d'.U)
        (chartDiagramSection B S hS f d') =
      (invRep (smallEtaleRingedToposHom B S hS f) d.V).obj.map a.op
        (chartDiagramSection B S hS f d) := by
  let g := smallEtaleRingedToposHom B S hS f
  let Φ := fMapEquivPushforwardHom_ringUniverse B S hS f
  let J := SmallEtale.topology B S hS Y.1
  let ξ := (Φ (invRep g d.V) (J.yoneda.obj d.V)).symm (g.toToposHom.adj.unit.app _)
  let ξ' := (Φ (invRep g d'.V) (J.yoneda.obj d'.V)).symm (g.toToposHom.adj.unit.app _)
  have h1 : FMap.compSource B S hS f ξ' (g.toToposHom.inverseImage.map (J.yoneda.map b)).hom =
      (Φ (invRep g d.V) (J.yoneda.obj d'.V)).symm
        (J.yoneda.map b ≫ g.toToposHom.adj.unit.app _) := by
    apply (Φ (invRep g d.V) (J.yoneda.obj d'.V)).injective
    rw [Equiv.apply_symm_apply, fMapEquivPushforwardHom_ringUniverse_source_map,
      Equiv.apply_symm_apply]
    exact (g.toToposHom.adj.unit.naturality (J.yoneda.map b)).symm
  refine (congrArg (fun ζ : FMap B S hS X.1 Y.1 f.hom (invRep g d.V).obj (J.yoneda.obj d'.V).obj =>
    ζ.app d' (J.yonedaEquiv (𝟙 _))) h1).trans ?_
  refine (fMapEquivPushforwardHom_ringUniverse_symm_comp_app B S hS f _ _ _ d' _).trans ?_
  exact ξ.naturality d d' a b hab (J.yonedaEquiv (𝟙 _))

end RingHom

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- The `f^{-1}𝒪_Y`-algebra structure of the extension in direct-image form,
`𝒪_Y ⟶ f_*𝒜`. -/
def toBaseDirectImage : (smallEtaleRingedTopos B S hS Y).O ⟶
    (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj E.A :=
  (commRingImageAdjunction (smallEtaleRingedToposHom B S hS f).toToposHom).homEquiv _ _ E.toBase

/-- The direct-image form of the algebra structure followed by the direct image of the reduction
is the direct-image form of the structure map. -/
theorem toBaseDirectImage_comp_π :
    toBaseDirectImage B S hS E ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).map E.π =
      (smallEtaleRingedToposHom B S hS f).fSharp := by
  rw [toBaseDirectImage, ← Adjunction.homEquiv_naturality_right, E.toBase_π]
  exact Equiv.apply_symm_apply _ _

/-- **The ring map attached to a diagram of étale charts over `f`**: `𝒪_Y(V) ⟶ 𝒜(U)`, the
algebra structure of the extension read on the chart diagram. -/
def chartRing (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    Γ(chartSch d.V, ⊤) ⟶ E.A.obj.obj (op d.U) :=
  (toBaseDirectImage B S hS E).hom.app (op d.V) ≫
    (show ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
        E.A).obj.obj (op d.V) ⟶ E.A.obj.obj (op d.U) from
      ConcreteCategory.ofHom (C := CommRingCat)
        (invRepRingHom B S hS f E.A d.V d.U (chartDiagramSection B S hS f d)))

/-- **The ring map attached to a chart diagram lifts pullback of functions along its vertical
morphism**: followed by the reduction it is `Γ` of that morphism. -/
theorem chartRing_comp_π (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartRing B S hS E d ≫ E.π.hom.app (op d.U) =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) := by
  rw [← chartRingHom_chartDiagramSection]
  ext x
  change E.π.hom.app (op d.U) (invRepRingHom B S hS f E.A d.V d.U (chartDiagramSection B S hS f d)
      ((toBaseDirectImage B S hS E).hom.app (op d.V) x)) =
    invRepRingHom B S hS f (smallEtaleRingedTopos B S hS X).O d.V d.U
      (chartDiagramSection B S hS f d)
      ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op d.V) x)
  refine (invRepRingHom_naturality B S hS f E.π d.V d.U _ _).trans ?_
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun k => k.hom) (toBaseDirectImage_comp_π B S hS E)) (op d.V)) x
  have h' := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k => k.hom)
    (Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap
      (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward E.π)) (op d.V))
    ((toBaseDirectImage B S hS E).hom.app (op d.V) x)
  exact congrArg (invRepRingHom B S hS f (smallEtaleRingedTopos B S hS X).O d.V d.U
    (chartDiagramSection B S hS f d)) (h'.symm.trans h)

/-- **The ring map of a chart diagram is natural in the diagram.** -/
theorem chartRing_naturality (d d' : ChartDiagram B S hS X.1 Y.1 f.hom)
    (a : d'.U ⟶ d.U) (b : d'.V ⟶ d.V)
    (hab : (SmallEtale.toOver B S hS X.1).map a ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Y.1).map b) :
    chartRing B S hS E d ≫ E.A.obj.map a.op =
      (smallEtaleRingedTopos B S hS Y).O.obj.map b.op ≫ chartRing B S hS E d' := by
  ext x
  change E.A.obj.map a.op (invRepRingHom B S hS f E.A d.V d.U (chartDiagramSection B S hS f d)
      ((toBaseDirectImage B S hS E).hom.app (op d.V) x)) =
    invRepRingHom B S hS f E.A d'.V d'.U (chartDiagramSection B S hS f d')
      ((toBaseDirectImage B S hS E).hom.app (op d'.V)
        ((smallEtaleRingedTopos B S hS Y).O.obj.map b.op x))
  rw [← invRepRingHom_restrict, ← chartDiagramSection_naturality B S hS f d d' a b hab,
    invRepRingHom_map]
  exact congrArg _ (ConcreteCategory.congr_hom
    ((toBaseDirectImage B S hS E).hom.naturality b.op) x).symm

/-- The inclusion of the top open chart into a chart, on global functions, is inverse to the
identification of the global functions of the top open subscheme with the global sections. -/
theorem appTop_openChartInclusion_top_restrictFunctorΓ (U : SmallEtale B S hS X.1) :
    (structurePresheaf B S hS X.1).map (openChartInclusion B S hS X.1 U ⊤).op ≫
      (Scheme.restrictFunctorΓ (X := chartScheme U)).hom.app (op ⊤) = 𝟙 _ := by
  change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (openChartInclusion B S hS X.1 U ⊤))).op ≫ _ = _
  rw [toScheme_map_toOver_map_openChartInclusion]
  change (⊤ : (chartScheme U).Opens).ι.appTop ≫ _ = _
  simp only [Scheme.Opens.ι_appTop, Scheme.restrictFunctorΓ_hom_app]
  exact ((chartScheme U).presheaf.map_comp _ _).symm.trans
    ((congrArg (chartScheme U).presheaf.map (Subsingleton.elim _ _)).trans
      ((chartScheme U).presheaf.map_id _))

/-- **The morphism `U' ⟶ V` of a chart diagram over `f` with affine lower chart**: the morphism
of schemes out of the thickened upper chart inducing the ring map of the diagram on global
functions. -/
def chartMap (d : ChartDiagram B S hS X.1 Y.1 f.hom) [IsAffine (chartSch d.V)] :
    chartThickening B S hS E d.U ⟶ chartSch d.V :=
  Stacks.EtaleCohomology.schemeHomOfAppTop _ _
    (chartRing B S hS E d ≫ E.A.obj.map (openChartInclusion B S hS X.1 d.U ⊤).op)

/-- On global functions, `chartMap` is the ring map of the chart diagram followed by restriction
to the top open chart. -/
theorem chartMap_appTop (d : ChartDiagram B S hS X.1 Y.1 f.hom) [IsAffine (chartSch d.V)] :
    (chartMap B S hS E d).appTop =
      chartRing B S hS E d ≫ E.A.obj.map (openChartInclusion B S hS X.1 d.U ⊤).op :=
  Stacks.EtaleCohomology.appTop_schemeHomOfAppTop _ _ _

/-- **`U' ⟶ V` extends the vertical morphism of the chart diagram** across `U ⊂ U'`. -/
theorem chartImmersion_comp_chartMap (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    [IsAffine (chartSch d.V)] :
    chartImmersion B S hS E d.U ≫ chartMap B S hS E d = (BigFppfOver.toScheme B S hS).map d.g := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, chartMap_appTop]
  ext x
  change (Scheme.restrictFunctorΓ (X := chartScheme d.U)).hom.app (op ⊤)
      (E.π.hom.app (op (openChart B S hS X.1 d.U ⊤))
        (E.A.obj.map (openChartInclusion B S hS X.1 d.U ⊤).op (chartRing B S hS E d x))) = _
  have h1 := ConcreteCategory.congr_hom
    (E.π.hom.naturality (openChartInclusion B S hS X.1 d.U ⊤).op) (chartRing B S hS E d x)
  have h2 := ConcreteCategory.congr_hom (chartRing_comp_π B S hS E d) x
  have h3 := ConcreteCategory.congr_hom (appTop_openChartInclusion_top_restrictFunctorΓ B S hS d.U)
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) x)
  exact (congrArg ((Scheme.restrictFunctorΓ (X := chartScheme d.U)).hom.app (op ⊤))
    (h1.trans (congrArg ((structurePresheaf B S hS X.1).map
      (openChartInclusion B S hS X.1 d.U ⊤).op) h2))).trans h3

/-- The chart diagram restricted to an open `O` of its lower chart and the preimage of `O`. -/
noncomputable abbrev chartDiagramRestrict (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (O : (chartScheme d.V).Opens) : ChartDiagram B S hS X.1 Y.1 f.hom :=
  d.restrictOpens ((BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ O) O le_rfl

/-- For opens `O₂ ≤ O₁` of the lower chart, the chart diagrams restricted to `O₁` and to `O₂`
commute with the inclusions of the corresponding open charts. -/
theorem chartDiagramRestrict_hab (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {O₁ O₂ : (chartScheme d.V).Opens} (h : O₂ ≤ O₁) :
    (SmallEtale.toOver B S hS X.1).map (openChartHomOfLE B S hS X.1 d.U
        (((BigFppfOver.toScheme B S hS).map d.g).preimage_mono h)) ≫
        (chartDiagramRestrict B S hS d O₁).g =
      (chartDiagramRestrict B S hS d O₂).g ≫
        (SmallEtale.toOver B S hS Y.1).map (openChartHomOfLE B S hS Y.1 d.V h) := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans
    (Eq.trans ?_ ((BigFppfOver.toScheme B S hS).map_comp _ _).symm)
  change (chartScheme d.U).homOfLE (((BigFppfOver.toScheme B S hS).map d.g).preimage_mono h) ≫
      (BigFppfOver.toScheme B S hS).map (openSubMap d.g _ O₁ le_rfl) =
    (BigFppfOver.toScheme B S hS).map (openSubMap d.g _ O₂ le_rfl) ≫ (chartScheme d.V).homOfLE h
  rw [toScheme_map_openSubMap, toScheme_map_openSubMap]
  change (chartScheme d.U).homOfLE (((BigFppfOver.toScheme B S hS).map d.g).preimage_mono h) ≫
      (((BigFppfOver.toScheme B S hS).map d.g).resLE O₁ _ le_rfl : _ ⟶ (O₁ : Scheme)) =
    ((BigFppfOver.toScheme B S hS).map d.g).resLE O₂ _ le_rfl ≫ (chartScheme d.V).homOfLE h
  rw [← cancel_mono O₁.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
    Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- The sheaf component of the morphism `U' ⟶ V` of a chart diagram: over an open `O` of `V`,
the ring map of the diagram restricted to `O` and its preimage. -/
def chartMapC (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartScheme d.V).presheaf ⟶
      ((BigFppfOver.toScheme B S hS).map d.g).base _*
        (chartThickenedSpace B S hS E d.U).presheaf where
  app O := (Scheme.Opens.topIso (X := chartScheme d.V) O.unop).inv ≫
    chartRing B S hS E (chartDiagramRestrict B S hS d O.unop)
  naturality O₁ O₂ i := by
    have hi : O₂.unop ≤ O₁.unop := i.unop.le
    have h1 := Scheme.topIso_inv_homOfLE_appTop hi
    have h2 := chartRing_naturality B S hS E (chartDiagramRestrict B S hS d O₁.unop)
      (chartDiagramRestrict B S hS d O₂.unop) _ _ (chartDiagramRestrict_hab B S hS d hi)
    ext x
    have e1 := ConcreteCategory.congr_hom h1 x
    have e2 := ConcreteCategory.congr_hom h2
      ((Scheme.Opens.topIso (X := chartScheme d.V) O₁.unop).inv x)
    exact (congrArg (chartRing B S hS E (chartDiagramRestrict B S hS d O₂.unop)) e1.symm).trans
      e2.symm

/-- The morphism of sheafed spaces `U' ⟶ V` of a chart diagram. -/
def chartMapSh (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartThickenedSpace B S hS E d.U ⟶ (chartSch d.V).toSheafedSpace :=
  InducedCategory.homMk
    { base := ((BigFppfOver.toScheme B S hS).map d.g).base, c := chartMapC B S hS E d }

/-- **The morphism `U' ⟶ V` extends the vertical morphism of the chart diagram**, as sheafed
spaces. -/
theorem chartZariskiInclusion_comp_chartMapSh (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartZariskiInclusion B S hS E d.U ≫ chartMapSh B S hS E d =
      ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom.toShHom := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  ext O x
  obtain ⟨O, rfl⟩ : ∃ O' : (chartScheme d.V).Opens, O' = O := ⟨O, rfl⟩
  let φ := (BigFppfOver.toScheme B S hS).map d.g
  change (Scheme.restrictFunctorΓ (X := chartScheme d.U)).hom.app (op (φ ⁻¹ᵁ O))
      (E.π.hom.app _ (chartRing B S hS E (chartDiagramRestrict B S hS d O)
        ((Scheme.Opens.topIso (X := chartScheme d.V) O).inv x))) = φ.app O x
  have h1 := ConcreteCategory.congr_hom
    (chartRing_comp_π B S hS E (chartDiagramRestrict B S hS d O))
    ((Scheme.Opens.topIso (X := chartScheme d.V) O).inv x)
  have h2 : (Scheme.restrictFunctorΓ (X := chartScheme d.U)).hom.app (op (φ ⁻¹ᵁ O)) =
      (Scheme.Opens.topIso (X := chartScheme d.U) (φ ⁻¹ᵁ O)).hom :=
    congrArg Iso.hom (Scheme.restrictFunctorΓ_app_eq_topIso (φ ⁻¹ᵁ O))
  have h3 := ConcreteCategory.congr_hom (Scheme.Hom.topIso_inv_resLE_appTop φ O (φ ⁻¹ᵁ O) le_rfl) x
  refine (congrArg ((Scheme.restrictFunctorΓ (X := chartScheme d.U)).hom.app
    (op (φ ⁻¹ᵁ O))) h1).trans ?_
  refine (ConcreteCategory.congr_hom h2 _).trans ?_
  refine (Eq.trans ?_ h3).trans ?_
  · change (Scheme.Opens.topIso (φ ⁻¹ᵁ O)).hom (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
      (openSubMap d.g (φ ⁻¹ᵁ O) O le_rfl))) ((Scheme.Opens.topIso O).inv x)) = _
    rw [toScheme_map_openSubMap]
    rfl
  · rw [← Scheme.Hom.app_eq_appLE]

/-- The stalk maps of the morphism `U' ⟶ V` of a chart diagram are local. -/
theorem isLocalHom_stalkMap_chartMapSh (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : chartScheme d.U) :
    IsLocalHom ((chartMapSh B S hS E d).hom.stalkMap x).hom := by
  have h1 : IsLocalHom ((((BigFppfOver.toScheme B S hS).map d.g).toLRSHom.toShHom).hom.stalkMap
      x).hom := ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom.prop x
  have h2 := LocallyRingedSpace.isLocalHom_stalkMap_congr _ _
    (chartZariskiInclusion_comp_chartMapSh B S hS E d).symm x h1
  rw [show (chartZariskiInclusion B S hS E d.U ≫ chartMapSh B S hS E d).hom =
    (chartZariskiInclusion B S hS E d.U).hom ≫ (chartMapSh B S hS E d).hom from rfl,
    PresheafedSpace.stalkMap.comp] at h2
  exact @isLocalHom_of_comp _ _ _ _ _ _ _ ((chartZariskiInclusion B S hS E d.U).hom.stalkMap x).hom
    h2

/-- **The morphism `U' ⟶ V` of a chart diagram over `f`**, for an arbitrary lower chart `V`:
the map of points is that of the vertical morphism of the diagram, and the map of sections over
an open `O` of `V` is the ring map of the diagram restricted to `O` and its preimage. -/
def chartMapGen (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartThickening B S hS E d.U ⟶ chartSch d.V :=
  Scheme.Hom.mk (LocallyRingedSpace.homMk (X := chartThickenedLRS B S hS E d.U)
    (Y := (chartSch d.V).toLocallyRingedSpace) (chartMapSh B S hS E d)
    (isLocalHom_stalkMap_chartMapSh B S hS E d))

/-- **`U' ⟶ V` extends the vertical morphism of the chart diagram** across `U ⊂ U'`. -/
theorem chartImmersion_comp_chartMapGen (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    chartImmersion B S hS E d.U ≫ chartMapGen B S hS E d =
      (BigFppfOver.toScheme B S hS).map d.g :=
  Scheme.Hom.ext' (LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (chartZariskiInclusion_comp_chartMapSh B S hS E d))

/-- A chart diagram precomposed with a morphism of charts of the source. -/
@[simps]
def _root_.AlgebraicGeometry.Space.ChartDiagram.precomp (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {U₁ : SmallEtale B S hS X.1} (h : U₁ ⟶ d.U) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := U₁
  V := d.V
  g := (SmallEtale.toOver B S hS X.1).map h ≫ d.g
  comm := by
    rw [Functor.map_comp, Category.assoc, ← d.comm, ← Category.assoc,
      yoneda_map_toOver_map_comp_hom]

/-- A chart diagram postcomposed with a morphism of charts of the target. -/
@[simps]
def _root_.AlgebraicGeometry.Space.ChartDiagram.postcomp' (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {V₂ : SmallEtale B S hS Y.1} (c : d.V ⟶ V₂) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := d.U
  V := V₂
  g := d.g ≫ (SmallEtale.toOver B S hS Y.1).map c
  comm := by
    rw [d.comm, Functor.map_comp, Category.assoc, yoneda_map_toOver_map_comp_hom]

/-- **`U' ⟶ V` is natural in the chart of the source.** -/
theorem chartThickeningMap_comp_chartMapGen (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {U₁ : SmallEtale B S hS X.1} (h : U₁ ⟶ d.U) :
    chartThickeningMap B S hS E h ≫ chartMapGen B S hS E d =
      chartMapGen B S hS E (ChartDiagram.precomp B S hS d h) := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  ext O x
  obtain ⟨O, rfl⟩ : ∃ O' : (chartScheme d.V).Opens, O' = O := ⟨O, rfl⟩
  let φ := (BigFppfOver.toScheme B S hS).map d.g
  have hab : (SmallEtale.toOver B S hS X.1).map (openChartRestrict B S hS X.1 h (φ ⁻¹ᵁ O)) ≫
      (chartDiagramRestrict B S hS d O).g =
      (chartDiagramRestrict B S hS (ChartDiagram.precomp B S hS d h) O).g ≫
        (SmallEtale.toOver B S hS Y.1).map (𝟙 _) := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans
      (Eq.trans ?_ ((BigFppfOver.toScheme B S hS).map_comp _ _).symm)
    change (chartSchemeMap h ∣_ (φ ⁻¹ᵁ O)) ≫
        (BigFppfOver.toScheme B S hS).map (openSubMap d.g (φ ⁻¹ᵁ O) O le_rfl) =
      (BigFppfOver.toScheme B S hS).map (openSubMap ((SmallEtale.toOver B S hS X.1).map h ≫ d.g)
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h ≫ d.g) ⁻¹ᵁ O)
        O le_rfl) ≫ 𝟙 _
    rw [Category.comp_id, toScheme_map_openSubMap, toScheme_map_openSubMap]
    change (chartSchemeMap h ∣_ (φ ⁻¹ᵁ O)) ≫ (φ.resLE O _ le_rfl : _ ⟶ (O : Scheme)) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h ≫ d.g)).resLE O _
        le_rfl
    refine (cancel_mono O.ι).mp ?_
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι_assoc]
    exact (Scheme.Hom.resLE_comp_ι _ _).symm
  exact ConcreteCategory.congr_hom
    (chartRing_naturality B S hS E (chartDiagramRestrict B S hS d O)
      (chartDiagramRestrict B S hS (ChartDiagram.precomp B S hS d h) O) _ _ hab)
    ((Scheme.Opens.topIso (X := chartScheme d.V) O).inv x)

/-- Restricting the chart diagram `d` postcomposed with `c` to an open `O` of `V₂` agrees with
restricting `d` to the preimage of `O` under `c`, up to an inclusion of open charts and the
restriction of `c` to `O`. -/
theorem chartDiagramRestrict_postcomp_hab (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {V₂ : SmallEtale B S hS Y.1} (c : d.V ⟶ V₂) (O : (chartScheme V₂).Opens)
    (i : (BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ (chartSchemeMap c ⁻¹ᵁ O) ⟶
      (BigFppfOver.toScheme B S hS).map (d.g ≫ (SmallEtale.toOver B S hS Y.1).map c) ⁻¹ᵁ O) :
    (SmallEtale.toOver B S hS X.1).map ((openChartFunctor B S hS X.1 d.U).map i) ≫
      (chartDiagramRestrict B S hS (ChartDiagram.postcomp' B S hS d c) O).g =
      (chartDiagramRestrict B S hS d (chartSchemeMap c ⁻¹ᵁ O)).g ≫
        (SmallEtale.toOver B S hS Y.1).map (openChartRestrict B S hS Y.1 c O) := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans
    (Eq.trans ?_ ((BigFppfOver.toScheme B S hS).map_comp _ _).symm)
  change (chartScheme d.U).homOfLE i.le ≫ (BigFppfOver.toScheme B S hS).map (openSubMap (d.g ≫
      (SmallEtale.toOver B S hS Y.1).map c) _ O le_rfl) =
    (BigFppfOver.toScheme B S hS).map (openSubMap d.g _ (chartSchemeMap c ⁻¹ᵁ O) le_rfl) ≫
      (chartSchemeMap c ∣_ O)
  rw [toScheme_map_openSubMap, toScheme_map_openSubMap]
  refine (cancel_mono O.ι).mp ?_
  have e1 := Scheme.Hom.resLE_comp_ι ((BigFppfOver.toScheme B S hS).map d.g)
    (U := chartSchemeMap c ⁻¹ᵁ O) (V := (BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ
      (chartSchemeMap c ⁻¹ᵁ O)) le_rfl
  have e2 := Scheme.Hom.resLE_comp_ι ((BigFppfOver.toScheme B S hS).map d.g ≫ chartSchemeMap c)
    (U := O) (V := ((BigFppfOver.toScheme B S hS).map d.g ≫ chartSchemeMap c) ⁻¹ᵁ O) le_rfl
  have e3 := Scheme.homOfLE_ι (chartScheme d.U) i.le
  have e4 := morphismRestrict_ι (chartSchemeMap c) O
  calc _ = (chartScheme d.U).homOfLE i.le ≫ (((BigFppfOver.toScheme B S hS).map d.g ≫
        chartSchemeMap c).resLE O _ le_rfl ≫ O.ι) := Category.assoc _ _ _
    _ = ((chartScheme d.U).homOfLE i.le ≫ Scheme.Opens.ι _) ≫
        ((BigFppfOver.toScheme B S hS).map d.g ≫ chartSchemeMap c) :=
      (congrArg ((chartScheme d.U).homOfLE i.le ≫ ·) e2).trans (Category.assoc _ _ _).symm
    _ = _ := (congrArg (· ≫ _) e3).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ chartSchemeMap c) e1.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e4.symm).trans (Category.assoc _ _ _).symm))))

/-- **`U' ⟶ V` is natural in the chart of the target.** -/
theorem chartMapGen_postcomp (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {V₂ : SmallEtale B S hS Y.1} (c : d.V ⟶ V₂) :
    chartMapGen B S hS E (ChartDiagram.postcomp' B S hS d c) =
      chartMapGen B S hS E d ≫ chartSchemeMap c := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  have hb : ((BigFppfOver.toScheme B S hS).map (d.g ≫ (SmallEtale.toOver B S hS Y.1).map c)).base =
      ((BigFppfOver.toScheme B S hS).map d.g).base ≫ (chartSchemeMap c).base := by
    rw [Functor.map_comp, Scheme.Hom.comp_base]
  refine SheafedSpace.ext _ _ hb ?_
  ext O x
  obtain ⟨O, rfl⟩ : ∃ O' : (chartScheme V₂).Opens, O' = O := ⟨O, rfl⟩
  rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app]
  let i : (BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ (chartSchemeMap c ⁻¹ᵁ O) ⟶
      (BigFppfOver.toScheme B S hS).map (d.g ≫ (SmallEtale.toOver B S hS Y.1).map c) ⁻¹ᵁ O :=
    homOfLE (le_of_eq (by rw [Functor.map_comp, Scheme.Hom.comp_preimage]))
  have hn := ConcreteCategory.congr_hom (chartRing_naturality B S hS E
    (chartDiagramRestrict B S hS (ChartDiagram.postcomp' B S hS d c) O)
    (chartDiagramRestrict B S hS d (chartSchemeMap c ⁻¹ᵁ O)) _ _
    (chartDiagramRestrict_postcomp_hab B S hS d c O i))
    ((Scheme.Opens.topIso (X := chartScheme V₂) O).inv x)
  have hΓ := ConcreteCategory.congr_hom
    (Scheme.Hom.topIso_inv_resLE_appTop (chartSchemeMap c) O (chartSchemeMap c ⁻¹ᵁ O) le_rfl) x
  rw [Scheme.Hom.resLE_eq_morphismRestrict, ← Scheme.Hom.app_eq_appLE] at hΓ
  refine hn.trans ?_
  change chartRing B S hS E (chartDiagramRestrict B S hS d (chartSchemeMap c ⁻¹ᵁ O))
      ((chartSchemeMap c ∣_ O).appTop ((Scheme.Opens.topIso (X := chartScheme V₂) O).inv x)) =
    chartRing B S hS E (chartDiagramRestrict B S hS d (chartSchemeMap c ⁻¹ᵁ O))
      ((Scheme.Opens.topIso (X := chartScheme d.V) (chartSchemeMap c ⁻¹ᵁ O)).inv
        ((chartSchemeMap c).app O x))
  rw [← hΓ]
  exact congrArg _ (Iso.hom_inv_id_apply _ _).symm

/-- `U' ⟶ V` depends on the vertical morphism of the chart diagram only. -/
theorem chartMapGen_mk_congr {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {g g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    (hc : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom)
    (hc' : U.1.hom ≫ f.hom = yoneda.map g' ≫ V.1.hom) (h : g = g') :
    chartMapGen B S hS E ⟨U, V, g, hc⟩ = chartMapGen B S hS E ⟨U, V, g', hc'⟩ := by
  subst h
  rfl

end SquareZeroExtension

end AlgebraicGeometry.Space

end
