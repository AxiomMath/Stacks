module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealization

/-!
# The algebra structure of the ambient space of a square-zero extension

For a square-zero extension of `X` over `Y` and a charted presentation of `f : X ⟶ Y`, the
comparison of the inverse image of the structure sheaf of the ambient space with the extension is
compatible with the algebra structures over the base, so the ambient space realizes the
extension.

## Main results

* `algebra_compatibility_ambient`: The ambient comparison is one of algebras over the base.
* `nonempty_realization`: The square-zero extension is realized by a first-order thickening.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

namespace SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **On global functions, the morphism of a thickened chart to the lower chart is the ring map
of the chart diagram.** -/
theorem chartMapGen_appTop (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (chartMapGen B S hS E d).appTop = chartRing B S hS E d ≫ (thickeningΓIso E d.U).hom := by
  change (Scheme.Opens.topIso (X := chartScheme d.V) ⊤).inv ≫
    chartRing B S hS E (chartDiagramRestrict B S hS d ⊤) = _
  have hn := chartRing_naturality B S hS E d (chartDiagramRestrict B S hS d ⊤)
    (openChartInclusion B S hS X.1 d.U ((BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ ⊤))
    (openChartInclusion B S hS Y.1 d.V ⊤) (openSubMap_comp_openSubHom d.g _ ⊤ le_rfl).symm
  have hT : (Scheme.Opens.topIso (X := chartScheme d.V) ⊤).inv =
      (smallEtaleRingedTopos B S hS Y).O.obj.map (openChartInclusion B S hS Y.1 d.V ⊤).op := by
    have h := appTop_openChartInclusion_top_restrictFunctorΓ B S hS d.V
    have h' : (Scheme.restrictFunctorΓ (X := chartScheme d.V)).hom.app (op ⊤) =
        (Scheme.Opens.topIso (X := chartScheme d.V) ⊤).hom :=
      congrArg Iso.hom (Scheme.restrictFunctorΓ_app_eq_topIso ⊤)
    rw [h'] at h
    exact ((Iso.comp_hom_eq_id _).1 h).symm
  refine (congrArg (· ≫ chartRing B S hS E (chartDiagramRestrict B S hS d ⊤)) hT).trans ?_
  exact hn.symm

attribute [local instance] hasSheafify_bigFppfOver

variable {E} {C : ChartedPresentation B S hS f}
  {hcU : B.Contains (chartThickening B S hS E (presentationChart C.P))}
  {hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P))}

section Generic

attribute [local instance] smallEtaleTopology_subcanonical

set_option maxHeartbeats 800000 in
-- long `refine`/`congrArg` chains through inverse images and adjunction transports of the
-- small étale ringed toposes.
/-- **The algebra compatibility of a realization, from chart transports.** -/
theorem algebra_compatibility_of_transport {X X' Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (E : SquareZeroExtension B S hS f) (i : X ⟶ X') (p : X' ⟶ Y) (h : i ≫ p = f)
    (ψ' : (smallEtaleRingedTopos B S hS X').O ⟶
      (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS i).toToposHom).obj E.A)
    (H : ∀ (d : ChartDiagram B S hS X.1 Y.1 f.hom)
      (y : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))),
      (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) d.V d.U
          (chartDiagramSection B S hS f d)).app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)
          (((smallEtaleRingedTopos B S hS Y).forgetRing.map (toBaseDirectImage B S hS E)).hom.app
            (op d.V) y) =
        (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS (i ≫ p)) d.V d.U
          (chartDiagramSection B S hS (i ≫ p) ⟨d.U, d.V, d.g, h ▸ d.comm⟩)).app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)
          (((smallToposMorphismTypeU_comp B S hS i p).hom.app
            ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)).hom.app (op d.V)
          (((smallEtaleRingedToposHom B S hS p).toToposHom.pushforward.map
              ((smallEtaleRingedTopos B S hS X').forgetRing.map ψ')).hom.app (op d.V)
            (((smallEtaleRingedTopos B S hS Y).forgetRing.map
              (smallEtaleRingedToposHom B S hS p).fSharp).hom.app (op d.V) y)))) :
    E.toBase = (canonicalBaseComparison B S hS i p f h).hom ≫
      (smallEtaleInverseImageRing B S hS i).map
        (smallEtaleRingedToposHom B S hS p).fSharpInverseImage ≫
      ((commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS i).toToposHom).homEquiv _ _).symm ψ' := by
  subst h
  have H' : (smallEtaleRingedTopos B S hS Y).forgetRing.map (toBaseDirectImage B S hS E) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map (smallEtaleRingedToposHom B S hS p).fSharp ≫
        (smallEtaleRingedToposHom B S hS p).toToposHom.pushforward.map
          ((smallEtaleRingedTopos B S hS X').forgetRing.map ψ') ≫
        (smallToposMorphismTypeU_comp B S hS i p).hom.app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A) :=
    pushforward_hom_ext_of_transport B S hS (i ≫ p) fun d y => H d y
  have hκ : ∀ O, (sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i p).hom.app O) =
      (((((smallEtaleRingedToposHom B S hS p).toToposHom.comp
        (smallEtaleRingedToposHom B S hS i).toToposHom).adj.ofNatIsoRight
          (smallToposMorphismTypeU_comp B S hS i p)).leftAdjointUniq
          (smallEtaleRingedToposHom B S hS (i ≫ p)).toToposHom.adj).hom.app
        ((sheafCompose (SmallEtale.topology B S hS Y.1)
          (CategoryTheory.forget CommRingCat.{u})).obj O)) := fun O => by
    have hfl := ((smallEtaleRingedToposHom B S hS p).toToposHom.comp
      (smallEtaleRingedToposHom B S hS i).toToposHom).preservesFiniteLimits
    have := (⟨fun _ ↦ hfl.preservesFiniteLimits _⟩ :
      Limits.PreservesFiniteProducts ((smallEtaleRingedToposHom B S hS p).toToposHom.comp
        (smallEtaleRingedToposHom B S hS i).toToposHom).inverseImage)
    have hfl' := (smallEtaleRingedToposHom B S hS (i ≫ p)).toToposHom.preservesFiniteLimits
    have := (⟨fun _ ↦ hfl'.preservesFiniteLimits _⟩ :
      Limits.PreservesFiniteProducts
        (smallEtaleRingedToposHom B S hS (i ≫ p)).toToposHom.inverseImage)
    refine Eq.trans ((smallEtaleRingedTopos B S hS X).forgetRing.map_comp _ _) ?_
    refine Eq.trans (congrArg₂ (fun a b ↦ a ≫ b)
      (forget_map_inverseImageCommRingComp_hom (smallEtaleRingedToposHom B S hS p).toToposHom
        (smallEtaleRingedToposHom B S hS i).toToposHom O)
      (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
        (smallEtaleRingedTopos B S hS X).J O
        (smallEtaleRingedToposHom_compInverseImageIso B S hS i p))) ?_
    exact Category.id_comp _
  have hτ : (sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget CommRingCat.{u})).map E.toBase =
      ((smallEtaleRingedToposHom B S hS (i ≫ p)).toToposHom.adj.homEquiv _ _).symm
        ((smallEtaleRingedTopos B S hS Y).forgetRing.map
          (smallEtaleRingedToposHom B S hS p).fSharp ≫
        (smallEtaleRingedToposHom B S hS p).toToposHom.pushforward.map
          ((smallEtaleRingedTopos B S hS X').forgetRing.map ψ') ≫
        (smallToposMorphismTypeU_comp B S hS i p).hom.app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)) := by
    have h0 := MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget
      (smallEtaleRingedToposHom B S hS (i ≫ p)).toToposHom _ _ (toBaseDirectImage B S hS E)
    have h1 : ((commRingImageAdjunction
        (smallEtaleRingedToposHom B S hS (i ≫ p)).toToposHom).homEquiv
        _ _).symm (toBaseDirectImage B S hS E) = E.toBase := Equiv.symm_apply_apply _ _
    exact (congrArg (sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget CommRingCat.{u})).map h1).symm.trans (h0.trans (congrArg _ H'))
  have key := MorphismOfTopoi.comp_eq_of_forget' (smallEtaleRingedToposHom B S hS i).toToposHom
    (smallEtaleRingedToposHom B S hS p).toToposHom
    (smallEtaleRingedToposHom B S hS (i ≫ p)).toToposHom
    (smallToposMorphismTypeU_comp B S hS i p)
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i p) hκ
    (smallEtaleRingedTopos B S hS Y).O (smallEtaleRingedTopos B S hS X').O E.A
    (smallEtaleRingedToposHom B S hS p).fSharp ψ' E.toBase hτ
  change E.toBase = ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS i p).app
    (smallEtaleRingedTopos B S hS Y).O).inv ≫ _
  exact (Iso.eq_inv_comp _).2 key

end Generic

section Charts

variable (C) (T : SmallEtale B S hS X.1)

/-- The base change of an étale chart of `X` to the presenting scheme. -/
def atlasChart : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk (yoneda.map (C.P.etale.rep.snd T.1.hom) ≫ T.1.hom),
    etale_comp_of_scheme B S hS _ _ (C.P.etale.property_snd T.1.hom) T.2⟩

/-- Its projection to the chart. -/
def atlasChartHom : atlasChart C T ⟶ T :=
  ObjectProperty.homMk (CostructuredArrow.homMk (C.P.etale.rep.snd T.1.hom) rfl)

/-- Its projection to the presenting scheme. -/
def atlasChartToP : (atlasChart C T).1.left ⟶ C.P.U :=
  yoneda.preimage (C.P.etale.rep.fst T.1.hom)

/-- The projection of the base-changed chart to the presenting scheme, followed by the presenting
map, is the structure morphism of the base-changed chart. -/
theorem atlasChartToP_toSpace :
    yoneda.map (atlasChartToP C T) ≫ C.P.toSpace = (atlasChart C T).1.hom :=
  (congrArg (· ≫ C.P.toSpace) (yoneda.map_preimage (C.P.etale.rep.fst T.1.hom))).trans
    (C.P.etale.rep.isPullback T.1.hom).w

/-- The base change to the presenting scheme covers the chart. -/
theorem atlasChart_covers :
    Sieve.ofArrows (fun _ : PUnit.{u + 1} => atlasChart C T) (fun _ => atlasChartHom C T) ∈
      SmallEtale.topology B S hS X.1 T := by
  refine SmallEtale.ofArrows_mem_topology B S hS _ _ _ ?_
  exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2
    ⟨fun x => ⟨⟨⟩, (C.P.surjective.property_snd T.1.hom).surj x⟩,
      fun _ => C.P.etale.property_snd T.1.hom⟩

end Charts

section TransportHelpers

attribute [local instance] smallEtaleTopology_subcanonical

/-- **Chart transport is natural in the upper chart.** -/
theorem transport_precomp {X' Y' : AlgebraicSpaces B S hS} (g : X' ⟶ Y')
    (P : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (d : ChartDiagram B S hS X'.1 Y'.1 g.hom) {U₁ : SmallEtale B S hS X'.1} (a : U₁ ⟶ d.U)
    (z : ((smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.obj P).obj.obj (op d.V)) :
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS g) d.V U₁
        (chartDiagramSection B S hS g (ChartDiagram.precomp B S hS d a))).app P z =
      P.obj.map a.op ((inverseImageSectionTransport (smallEtaleRingedToposHom B S hS g) d.V d.U
        (chartDiagramSection B S hS g d)).app P z) := by
  have hs := chartDiagramSection_naturality B S hS g d (ChartDiagram.precomp B S hS d a) a (𝟙 d.V)
    ((Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) ((SmallEtale.toOver B S hS Y'.1).map_id d.V).symm))
  have hid : ((smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y'.1).yoneda.map (𝟙 d.V))) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hs' : chartDiagramSection B S hS g (ChartDiagram.precomp B S hS d a) =
      (invRep (smallEtaleRingedToposHom B S hS g) d.V).obj.map a.op
        (chartDiagramSection B S hS g d) :=
    (congrArg (fun m => m.hom.app (op U₁)
      (chartDiagramSection B S hS g (ChartDiagram.precomp B S hS d a))) hid).symm.trans hs
  change _ = P.obj.map a.op
    (((((smallEtaleRingedToposHom B S hS g).toToposHom.adj.homEquiv _ _).symm
    ((SmallEtale.topology B S hS Y'.1).yonedaEquiv.symm z))).hom.app (op d.U)
      (chartDiagramSection B S hS g d))
  rw [← NatTrans.naturality_apply, ← hs']
  rfl

/-- Two sections of a sheaf of sets over an étale chart agree as soon as they agree on the base
change of the chart to the presenting scheme. -/
theorem eq_of_atlasChart {C : ChartedPresentation B S hS f}
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (T : SmallEtale B S hS X.1)
    {a b : P.obj.obj (op T)}
    (h : P.obj.map (atlasChartHom C T).op a = P.obj.map (atlasChartHom C T).op b) : a = b := by
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp P.2).isSeparated _ (atlasChart_covers C T)
  refine hsep.ext fun Z m hm => ?_
  obtain ⟨Y₀, n, k, ⟨_⟩, rfl⟩ := hm
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h]

end TransportHelpers

section Factor

variable (E C hcU hcR) (W : SmallEtale B S hS Y.1)

/-- The map of the thickened presenting chart to `Y`. -/
abbrev ambUToY : yoneda.obj (ambU E C hcU) ⟶ Y.1 :=
  yoneda.map (ambUToBase E C hcU) ≫ C.Q.toSpace

/-- The base change of an étale chart of `Y` to the thickened presenting chart, as an étale chart
of the ambient space. -/
def liftChart : SmallEtale B S hS (ambient E C hcU hcR).1 :=
  ⟨CostructuredArrow.mk (yoneda.map (W.2.rep.snd (ambUToY E C hcU)) ≫ ambQuot E C hcU hcR),
    etale_comp_of_scheme B S hS _ _ (W.2.property_snd (ambUToY E C hcU))
      (quotientMap_etale_unconditional B S hS _ _)⟩

/-- Its tautological factorization through the thickened presenting chart. -/
def liftChartFactor : ChartFactor (liftChart E C hcU hcR W) where
  v := W.2.rep.snd (ambUToY E C hcU)
  fac := rfl
  etale := W.2.property_snd (ambUToY E C hcU)

/-- Its projection to the chart of `Y`. -/
def liftChartToW : (liftChart E C hcU hcR W).1.left ⟶ W.1.left :=
  yoneda.preimage (W.2.rep.fst (ambUToY E C hcU))

/-- The projection of the lifted chart to the chart of `Y` is compatible with the maps of both to
`Y`. -/
theorem liftChartToW_fac : yoneda.map (liftChartToW E C hcU hcR W) ≫ W.1.hom =
    yoneda.map (W.2.rep.snd (ambUToY E C hcU)) ≫ ambUToY E C hcU :=
  (congrArg (· ≫ W.1.hom) (yoneda.map_preimage (W.2.rep.fst (ambUToY E C hcU)))).trans
    (W.2.rep.isPullback (ambUToY E C hcU)).w

/-- The lifted chart over the ambient space maps to the chart of `Y` over the structure morphism
`ambientToBase`. -/
theorem liftChart_comm :
    (liftChart E C hcU hcR W).1.hom ≫ (ambientToBase E C hcU hcR).hom =
      yoneda.map (liftChartToW E C hcU hcR W) ≫ W.1.hom := by
  rw [liftChartToW_fac]
  change (yoneda.map (W.2.rep.snd (ambUToY E C hcU)) ≫ ambQuot E C hcU hcR) ≫ _ = _
  rw [Category.assoc, ambientToBase_fac]

end Factor

section Lift

variable (E C hcU hcR) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-- The structure morphism of `X` to `Y` factors through the ambient space. -/
private theorem hom_eq_immersion_comp_toBase :
    f.hom = (ambientImmersion E C hcU hcR).hom ≫ (ambientToBase E C hcU hcR).hom :=
  (congrArg (fun k => k.hom) (ambientImmersion_comp_toBase E C hcU hcR)).symm

include hcR in
/-- The base-changed chart of `X` maps compatibly to the lower chart and to the thickened
presenting chart over `Y`. -/
theorem liftCond :
    yoneda.map ((atlasChartHom C d.U).hom.left ≫ d.g) ≫ d.V.1.hom =
      yoneda.map (atlasChartToP C d.U ≫ incU E C hcU) ≫ ambUToY E C hcU := by
  rw [Functor.map_comp, Category.assoc, ← d.comm, ← Category.assoc]
  refine (congrArg (fun k => (yoneda.map (atlasChartHom C d.U).hom.left ≫ d.U.1.hom) ≫ k)
    (hom_eq_immersion_comp_toBase E C hcU hcR)).trans ?_
  change (atlasChart C d.U).1.hom ≫ (ambientImmersion E C hcU hcR).hom ≫
    (ambientToBase E C hcU hcR).hom = _
  rw [← atlasChartToP_toSpace, Category.assoc, ← Category.assoc C.P.toSpace,
    ambientImmersion_fac, Category.assoc, ambientToBase_fac, Functor.map_comp, Category.assoc]

/-- The morphism of the base-changed chart of `X` to the lifted chart of the ambient space. -/
def liftChartMap : (atlasChart C d.U).1.left ⟶ (liftChart E C hcU hcR d.V).1.left :=
  d.V.2.rep.lift (yoneda.map ((atlasChartHom C d.U).hom.left ≫ d.g))
    (atlasChartToP C d.U ≫ incU E C hcU) (liftCond E C hcU hcR d)

/-- The map `liftChartMap`, followed by the projection to the lower chart, is the projection of the
base-changed chart followed by the chart map of the diagram. -/
theorem liftChartMap_toW :
    liftChartMap E C hcU hcR d ≫ liftChartToW E C hcU hcR d.V =
      (atlasChartHom C d.U).hom.left ≫ d.g := by
  refine yoneda.map_injective ((yoneda.map_comp _ _).trans ?_)
  refine (congrArg (yoneda.map (liftChartMap E C hcU hcR d) ≫ ·)
    (yoneda.map_preimage (d.V.2.rep.fst (ambUToY E C hcU)))).trans ?_
  exact Functor.relativelyRepresentable.lift_fst _ _ _ _

/-- The map `liftChartMap`, followed by the factorization through the thickened presenting chart,
is the projection to the presenting scheme followed by its inclusion into the thickening. -/
theorem liftChartMap_snd :
    liftChartMap E C hcU hcR d ≫ (liftChartFactor E C hcU hcR d.V).v =
      atlasChartToP C d.U ≫ incU E C hcU :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

/-- The map `liftChartMap` lies over the immersion `ambientImmersion` of `X` into the ambient
space. -/
theorem liftChartMap_comm :
    (atlasChart C d.U).1.hom ≫ (ambientImmersion E C hcU hcR).hom =
      yoneda.map (liftChartMap E C hcU hcR d) ≫ (liftChart E C hcU hcR d.V).1.hom := by
  change _ = yoneda.map (liftChartMap E C hcU hcR d) ≫
    yoneda.map (liftChartFactor E C hcU hcR d.V).v ≫ ambQuot E C hcU hcR
  rw [← Category.assoc, ← Functor.map_comp, liftChartMap_snd, ← atlasChartToP_toSpace,
    Category.assoc, ambientImmersion_fac, Functor.map_comp, Category.assoc]

/-- The diagram of étale charts over `X ⟶ X'`. -/
def liftDiagram : ChartDiagram B S hS X.1 (ambient E C hcU hcR).1
    (ambientImmersion E C hcU hcR).hom :=
  ⟨atlasChart C d.U, liftChart E C hcU hcR d.V, liftChartMap E C hcU hcR d,
    liftChartMap_comm E C hcU hcR d⟩

/-- The diagram of étale charts over `X' ⟶ Y`. -/
def liftDiagramBase : ChartDiagram B S hS (ambient E C hcU hcR).1 Y.1
    (ambientToBase E C hcU hcR).hom :=
  ⟨liftChart E C hcU hcR d.V, d.V, liftChartToW E C hcU hcR d.V, liftChart_comm E C hcU hcR d.V⟩

/-- The base change of the lower chart to the presenting scheme of `Y`. -/
def qChart : SmallEtale B S hS Y.1 :=
  ⟨CostructuredArrow.mk (yoneda.map (C.Q.etale.rep.snd d.V.1.hom) ≫ d.V.1.hom),
    etale_comp_of_scheme B S hS _ _ (C.Q.etale.property_snd d.V.1.hom) d.V.2⟩

/-- The projection of `qChart` to the lower chart. -/
def qChartHom₁ : qChart C d ⟶ d.V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (C.Q.etale.rep.snd d.V.1.hom) rfl)

/-- The projection of `qChart` to the presenting scheme of `Y`, followed by the presenting map, is
the structure morphism of `qChart`. -/
theorem qChart_w : yoneda.map (yoneda.preimage (C.Q.etale.rep.fst d.V.1.hom)) ≫ C.Q.toSpace =
    (qChart C d).1.hom :=
  (congrArg (· ≫ C.Q.toSpace) (yoneda.map_preimage (C.Q.etale.rep.fst d.V.1.hom))).trans
    (C.Q.etale.rep.isPullback d.V.1.hom).w

/-- The projection of `qChart` to the presenting chart of `Y`. -/
def qChartHom₂ : qChart C d ⟶ presentationChart C.Q :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage (C.Q.etale.rep.fst d.V.1.hom))
    (qChart_w C d))

/-- The lifted chart maps compatibly to the presenting scheme of `Y` and to the lower chart over
`Y`. -/
theorem liftQCond : yoneda.map ((liftChartFactor E C hcU hcR d.V).v ≫ ambUToBase E C hcU) ≫
    C.Q.toSpace = yoneda.map (liftChartToW E C hcU hcR d.V) ≫ d.V.1.hom := by
  rw [liftChartToW_fac, Functor.map_comp, Category.assoc]
  rfl

/-- The morphism of the lifted chart to `qChart`. -/
def liftQMap : (liftChart E C hcU hcR d.V).1.left ⟶ (qChart C d).1.left :=
  C.Q.etale.rep.lift (yoneda.map ((liftChartFactor E C hcU hcR d.V).v ≫ ambUToBase E C hcU))
    (liftChartToW E C hcU hcR d.V) (liftQCond E C hcU hcR d)

/-- The map `liftQMap`, followed by the projection to the presenting scheme of `Y`, is the
factorization through the thickened presenting chart followed by `ambUToBase`. -/
theorem liftQMap_fst : yoneda.map (liftQMap E C hcU hcR d) ≫ C.Q.etale.rep.fst d.V.1.hom =
    yoneda.map ((liftChartFactor E C hcU hcR d.V).v ≫ ambUToBase E C hcU) :=
  Functor.relativelyRepresentable.lift_fst _ _ _ _

/-- The map `liftQMap`, followed by the projection to the lower chart, is `liftChartToW`. -/
theorem liftQMap_snd : liftQMap E C hcU hcR d ≫ C.Q.etale.rep.snd d.V.1.hom =
    liftChartToW E C hcU hcR d.V :=
  Functor.relativelyRepresentable.lift_snd _ _ _ _

/-- The map `liftQMap`, followed by the projection of `qChart` to the presenting scheme of `Y`, is
the factorization through the thickened presenting chart followed by `ambUToBase`. -/
theorem liftQMap_toQ : liftQMap E C hcU hcR d ≫ yoneda.preimage (C.Q.etale.rep.fst d.V.1.hom) =
    (liftChartFactor E C hcU hcR d.V).v ≫ ambUToBase E C hcU := by
  refine yoneda.map_injective ((yoneda.map_comp _ _).trans ?_)
  refine (congrArg (yoneda.map (liftQMap E C hcU hcR d) ≫ ·)
    (yoneda.map_preimage (C.Q.etale.rep.fst d.V.1.hom))).trans ?_
  exact liftQMap_fst E C hcU hcR d

/-- The thickened base-changed chart of the lifted chart maps to the lower chart. -/
theorem liftChart_comm_f :
    (chartX (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V)).1.hom ≫ f.hom =
      yoneda.map (chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V) ≫ liftChartToW E C hcU hcR d.V) ≫ d.V.1.hom := by
  refine (congrArg (_ ≫ ·) (hom_eq_immersion_comp_toBase E C hcU hcR)).trans ?_
  change (ambRep _ (ambientImmersion_fac E C hcU hcR)).fst (liftChart E C hcU hcR d.V).1.hom ≫
    (ambientImmersion E C hcU hcR).hom ≫ (ambientToBase E C hcU hcR).hom = _
  rw [← Category.assoc, ((ambRep _ (ambientImmersion_fac E C hcU hcR)).isPullback
    (liftChart E C hcU hcR d.V).1.hom).w, Category.assoc, liftChart_comm, ← Category.assoc,
    ← Functor.map_comp]
  rfl

/-- The projection of the thickened base-changed lifted chart to the lower chart factors through
`qChart`. -/
private theorem chartXProj_comp_liftChartToW :
    chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V) ≫ liftChartToW E C hcU hcR d.V =
      (chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V) ≫ liftQMap E C hcU hcR d) ≫ C.Q.etale.rep.snd d.V.1.hom :=
  (congrArg (_ ≫ ·) (liftQMap_snd E C hcU hcR d)).symm.trans (Category.assoc _ _ _).symm

/-- The thickened base-changed chart of the lifted chart maps to `qChart` over `f`. -/
theorem liftChart_comm_q :
    (chartX (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V)).1.hom ≫ f.hom =
      yoneda.map (chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V) ≫ liftQMap E C hcU hcR d) ≫ (qChart C d).1.hom := by
  refine (liftChart_comm_f E C hcU hcR d).trans ?_
  rw [chartXProj_comp_liftChartToW E C hcU hcR d, Functor.map_comp, Category.assoc]
  rfl

/-- The diagram of the thickened base-changed lifted chart over the base change of the lower
chart to the presenting scheme of `Y`. -/
def liftQDiagram : ChartDiagram B S hS X.1 Y.1 f.hom :=
  ⟨chartX (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
      (liftChart E C hcU hcR d.V), qChart C d,
    chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
      (liftChart E C hcU hcR d.V) ≫ liftQMap E C hcU hcR d, liftChart_comm_q E C hcU hcR d⟩

/-- The morphism to the base-changed lower chart of the thickened base-changed lifted chart is
the comparison with the lifted chart followed by its map to the base-changed lower chart. -/
theorem chartMapGen_liftQDiagram :
    chartMapGen B S hS E (liftQDiagram E C hcU hcR d) =
      (liftChartFactor E C hcU hcR d.V).thickenHom (hi := ambientImmersion_fac E C hcU hcR) ≫
        (BigFppfOver.toScheme B S hS).map (liftQMap E C hcU hcR d) := by
  have := SmallEtale.etale_map B S hS _ (qChartHom₂ C d)
  refine eq_of_comp_eq_of_isFirstOrderThickening
    (chartImmersion B S hS E (liftQDiagram E C hcU hcR d).U)
    (isFirstOrderThickening_chartImmersion B S hS E (liftQDiagram E C hcU hcR d).U)
    (chartSchemeMap (qChartHom₂ C d)) inferInstance ?_ ?_
  · refine (chartImmersion_comp_chartMapGen B S hS E (liftQDiagram E C hcU hcR d)).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ (BigFppfOver.toScheme B S hS).map
      (liftQMap E C hcU hcR d)) (liftChartFactor E C hcU hcR d.V).immersion_thickenHom.symm)
    exact (BigFppfOver.toScheme B S hS).map_comp _ _
  · refine (chartMapGen_postcomp B S hS E (liftQDiagram E C hcU hcR d) (qChartHom₂ C d)).symm.trans
      ?_
    have e1 : ((liftChartFactor E C hcU hcR d.V).thickenHom
            (hi := ambientImmersion_fac E C hcU hcR) ≫
          (BigFppfOver.toScheme B S hS).map (liftQMap E C hcU hcR d)) ≫
          chartSchemeMap (qChartHom₂ C d) =
        chartThickeningMap B S hS E ((liftChartFactor E C hcU hcR d.V).hom
          (hi := ambientImmersion_fac E C hcU hcR)) ≫ chartMapGen B S hS E C.diagram := by
      rw [← (liftChartFactor E C hcU hcR d.V).thickenHom_comp]
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine congrArg (_ ≫ ·) ?_
      refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ?_
      exact congrArg (BigFppfOver.toScheme B S hS).map (liftQMap_toQ E C hcU hcR d)
    refine Eq.trans ?_ e1.symm
    refine Eq.trans ?_ (chartThickeningMap_comp_chartMapGen B S hS E C.diagram _).symm
    refine chartMapGen_mk_congr B S hS E _ _ ?_
    change (chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V) ≫ liftQMap E C hcU hcR d) ≫
        yoneda.preimage (C.Q.etale.rep.fst d.V.1.hom) =
      (liftChartFactor E C hcU hcR d.V).lift (hi := ambientImmersion_fac E C hcU hcR) ≫ C.α
    rw [Category.assoc, liftQMap_toQ, ← Category.assoc,
      ← (liftChartFactor E C hcU hcR d.V).lift_incU, Category.assoc, incU_comp_ambUToBase]

/-- **The key chart identity**: the morphism to the lower chart of the thickened base-changed
lifted chart, built from the algebra structure, is the comparison with the lifted chart followed by
its map to the lower chart, built from the structure morphism `X' ⟶ Y`. -/
theorem chartMapGen_liftChart :
    chartMapGen B S hS E ⟨chartX (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
        (liftChart E C hcU hcR d.V), d.V,
        chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
          (liftChart E C hcU hcR d.V) ≫ liftChartToW E C hcU hcR d.V,
        liftChart_comm_f E C hcU hcR d⟩ =
      (liftChartFactor E C hcU hcR d.V).thickenHom (hi := ambientImmersion_fac E C hcU hcR) ≫
        (BigFppfOver.toScheme B S hS).map (liftChartToW E C hcU hcR d.V) := by
  have h2 : chartMapGen B S hS E ⟨chartX (ambientImmersion E C hcU hcR)
        (ambientImmersion_fac E C hcU hcR) (liftChart E C hcU hcR d.V), d.V,
        chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
          (liftChart E C hcU hcR d.V) ≫ liftChartToW E C hcU hcR d.V,
        liftChart_comm_f E C hcU hcR d⟩ =
      chartMapGen B S hS E (ChartDiagram.postcomp' B S hS (liftQDiagram E C hcU hcR d)
        (qChartHom₁ C d)) := by
    refine chartMapGen_mk_congr B S hS E _ _ ?_
    exact chartXProj_comp_liftChartToW E C hcU hcR d
  refine h2.trans ((chartMapGen_postcomp B S hS E _ _).trans ?_)
  refine (congrArg (· ≫ chartSchemeMap (qChartHom₁ C d))
    (chartMapGen_liftQDiagram E C hcU hcR d)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ?_
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ?_
  exact congrArg (BigFppfOver.toScheme B S hS).map (liftQMap_snd E C hcU hcR d)

/-- The diagram of the base-changed lifted chart over the lower chart. -/
def liftChartDiagramF : ChartDiagram B S hS X.1 Y.1 f.hom :=
  ⟨chartX (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
      (liftChart E C hcU hcR d.V), d.V,
    chartXProj (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
      (liftChart E C hcU hcR d.V) ≫ liftChartToW E C hcU hcR d.V, liftChart_comm_f E C hcU hcR d⟩

/-- **The ring map of the base-changed lifted chart** is pullback of functions to the lifted chart
followed by the comparison of the structure sheaf of the ambient space with the extension. -/
theorem chartRing_liftChartDiagramF :
    chartRing B S hS E (liftChartDiagramF E C hcU hcR d) =
      ((BigFppfOver.toScheme B S hS).map (liftChartToW E C hcU hcR d.V)).appTop ≫
        ambientChartRingHom (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
          (liftChart E C hcU hcR d.V) (liftChartFactor E C hcU hcR d.V) := by
  have h := (chartMapGen_appTop E (liftChartDiagramF E C hcU hcR d)).symm.trans
    (congrArg Scheme.Hom.appTop (chartMapGen_liftChart E C hcU hcR d))
  rw [ambientChartRingHom, ← Category.assoc]
  exact (Iso.eq_comp_inv _).2 (h.trans (Scheme.Hom.comp_appTop _ _))

end Lift

section Transport

variable (E C hcU hcR) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-- Restricting a chart diagram to a smaller upper chart is compatible with its ring map. -/
private theorem chartRing_precomp_apply (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {U₁ : SmallEtale B S hS X.1} (a : U₁ ⟶ d.U)
    (y : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    E.A.obj.map a.op (chartRing B S hS E d y) =
      chartRing B S hS E (ChartDiagram.precomp B S hS d a) y := by
  refine (ConcreteCategory.congr_hom (chartRing_naturality B S hS E d
    (ChartDiagram.precomp B S hS d a) a (𝟙 d.V)
    ((Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) ((SmallEtale.toOver B S hS Y.1).map_id d.V).symm))) y).trans
    (ConcreteCategory.congr_hom ?_ y)
  exact (congrArg (· ≫ _) ((smallEtaleRingedTopos B S hS Y).O.obj.map_id (op d.V))).trans
    (Category.id_comp _)

/-- **The structure-morphism side of the algebra compatibility, on chart transports.** -/
theorem transport_directImage (y : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    (inverseImageSectionTransport
        (smallEtaleRingedToposHom B S hS (ambientImmersion E C hcU hcR ≫ ambientToBase E C hcU hcR))
        d.V (atlasChart C d.U)
        (chartDiagramSection B S hS (ambientImmersion E C hcU hcR ≫ ambientToBase E C hcU hcR)
          (ChartDiagram.comp B S hS (ambientImmersion E C hcU hcR) (ambientToBase E C hcU hcR)
            (U := atlasChart C d.U) (V := liftChart E C hcU hcR d.V) (W := d.V)
            (liftChartMap E C hcU hcR d) (liftChartToW E C hcU hcR d.V)
            (liftChartMap_comm E C hcU hcR d) (liftChart_comm E C hcU hcR d.V)))).app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)
        (((smallToposMorphismTypeU_comp B S hS (ambientImmersion E C hcU hcR)
            (ambientToBase E C hcU hcR)).hom.app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)).hom.app (op d.V)
        (((smallEtaleRingedToposHom B S hS (ambientToBase E C hcU hcR)).toToposHom.pushforward.map
            ((smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).forgetRing.map
              (ambientSharp (ambientImmersion E C hcU hcR)
                (ambientImmersion_fac E C hcU hcR)))).hom.app
            (op d.V)
          (((smallEtaleRingedTopos B S hS Y).forgetRing.map
            (smallEtaleRingedToposHom B S hS (ambientToBase E C hcU hcR)).fSharp).hom.app
              (op d.V) y))) =
      E.A.obj.map (chartDiagramBaseChangeLift B S hS (ambientImmersion E C hcU hcR)
          (ambRep _ (ambientImmersion_fac E C hcU hcR)) (liftDiagram E C hcU hcR d)).op
        (ambientChartRingHom (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR)
          (liftChart E C hcU hcR d.V) (liftChartFactor E C hcU hcR d.V)
          (((BigFppfOver.toScheme B S hS).map (liftChartToW E C hcU hcR d.V)).appTop y)) := by
  let i := ambientImmersion E C hcU hcR
  let p := ambientToBase E C hcU hcR
  let hi := ambientImmersion_fac E C hcU hcR
  let FA := (smallEtaleRingedTopos B S hS X).forgetRing.obj E.A
  let d₂ : ChartDiagram B S hS (ambient E C hcU hcR).1 Y.1 p.hom :=
    ⟨liftChart E C hcU hcR d.V, d.V, liftChartToW E C hcU hcR d.V, liftChart_comm E C hcU hcR d.V⟩
  refine (inverseImageSectionTransport_comp B S hS i p (liftDiagram E C hcU hcR d)
    (liftChartToW E C hcU hcR d.V) (liftChart_comm E C hcU hcR d.V) FA _).trans ?_
  have h2 := NatTrans.naturality_apply
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS p)
    d.V (liftChart E C hcU hcR d.V) (chartDiagramSection B S hS p d₂))
    ((smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).forgetRing.map (ambientSharp i hi))
    (((smallEtaleRingedTopos B S hS Y).forgetRing.map
      (smallEtaleRingedToposHom B S hS p).fSharp).hom.app (op d.V) y)
  have h3 : (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS p) d.V
      (liftChart E C hcU hcR d.V) (chartDiagramSection B S hS p d₂)).app
        ((smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).O)
        (((smallEtaleRingedTopos B S hS Y).forgetRing.map
          (smallEtaleRingedToposHom B S hS p).fSharp).hom.app (op d.V) y) =
      ((BigFppfOver.toScheme B S hS).map (liftChartToW E C hcU hcR d.V)).appTop y :=
    ConcreteCategory.congr_hom (chartRingHom_chartDiagramSection B S hS p d₂) y
  refine (congrArg _ (h2.trans (congrArg _ h3))).trans ?_
  refine (inverseImageSectionTransport_representable B S hS i (ambRep i hi)
    (liftDiagram E C hcU hcR d) FA _).trans ?_
  refine congrArg (FA.obj.map _) ?_
  let z := ((BigFppfOver.toScheme B S hS).map (liftChartToW E C hcU hcR d.V)).appTop y
  let w := (ambientSheafHom i hi).hom.app (op (liftChart E C hcU hcR d.V)) z
  change ((chartComparison B S hS i (ambRep i hi)).hom.app FA).hom.app _
      ((pushforwardRingIsoRestriction i hi E.A).inv.hom.app _ w) = _
  refine (pushforwardRingIsoRestriction_hom_app i hi E.A _
    ((pushforwardRingIsoRestriction i hi E.A).inv.hom.app _ w)).symm.trans ?_
  have e1 := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun k => k.hom) (pushforwardRingIsoRestriction i hi E.A).inv_hom_id)
    (op (liftChart E C hcU hcR d.V))) w
  refine e1.trans ?_
  have e2 := NatTrans.congr_app (whiskerLeft_ambientSheafHom i hi)
    (op ⟨liftChart E C hcU hcR d.V, ⟨liftChartFactor E C hcU hcR d.V⟩⟩)
  refine (ConcreteCategory.congr_hom e2 z).trans ?_
  change ambientChartRingHom i hi _ _ z = _
  rw [ambientChartRingHom_eq i hi _ _ (liftChartFactor E C hcU hcR d.V)]

/-- Restricting a chart diagram over `ambientImmersion ≫ ambientToBase` to the base-changed chart
is the composite of `liftDiagram` and `liftDiagramBase`. -/
theorem precomp_atlas_eq_comp :
    ChartDiagram.precomp B S hS (⟨d.U, d.V, d.g, (congrArg (fun k => d.U.1.hom ≫ k.hom)
            (ambientImmersion_comp_toBase E C hcU hcR)).trans d.comm⟩ :
      ChartDiagram B S hS X.1 Y.1 (ambientImmersion E C hcU hcR ≫ ambientToBase E C hcU hcR).hom)
        (atlasChartHom C d.U) =
      ChartDiagram.comp B S hS (ambientImmersion E C hcU hcR) (ambientToBase E C hcU hcR)
        (U := atlasChart C d.U) (V := liftChart E C hcU hcR d.V) (W := d.V)
        (liftChartMap E C hcU hcR d) (liftChartToW E C hcU hcR d.V)
        (liftChartMap_comm E C hcU hcR d) (liftChart_comm E C hcU hcR d.V) :=
  ChartDiagram.ext B S hS _ _ rfl rfl (heq_of_eq (liftChartMap_toW E C hcU hcR d).symm)

/-- Restricting `liftChartDiagramF` along the base-change lift of `liftDiagram` is restricting the
chart diagram to the base-changed chart. -/
theorem liftChartDiagramF_precomp :
    ChartDiagram.precomp B S hS (liftChartDiagramF E C hcU hcR d)
        (chartDiagramBaseChangeLift B S hS (ambientImmersion E C hcU hcR)
          (ambRep _ (ambientImmersion_fac E C hcU hcR)) (liftDiagram E C hcU hcR d)) =
      ChartDiagram.precomp B S hS d (atlasChartHom C d.U) := by
  refine ChartDiagram.ext B S hS _ _ rfl rfl (heq_of_eq ?_)
  change (SmallEtale.toOver B S hS X.1).map (chartDiagramBaseChangeLift B S hS
      (ambientImmersion E C hcU hcR) (ambRep _ (ambientImmersion_fac E C hcU hcR))
      (liftDiagram E C hcU hcR d)) ≫ (chartXProj (ambientImmersion E C hcU hcR)
        (ambientImmersion_fac E C hcU hcR) (liftChart E C hcU hcR d.V) ≫
      liftChartToW E C hcU hcR d.V) = _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ liftChartToW E C hcU hcR d.V)
    (chartDiagramBaseChangeLift_snd B S hS (ambientImmersion E C hcU hcR)
      (ambRep _ (ambientImmersion_fac E C hcU hcR)) (liftDiagram E C hcU hcR d))).trans
    (liftChartMap_toW E C hcU hcR d))

/-- Equal chart diagrams have heterogeneously equal sections. -/
theorem chartDiagramSection_heq {X' Y' : AlgebraicSpaces B S hS} {g : X' ⟶ Y'}
    {D₁ D₂ : ChartDiagram B S hS X'.1 Y'.1 g.hom} (h : D₁ = D₂) :
    HEq (chartDiagramSection B S hS g D₁) (chartDiagramSection B S hS g D₂) := by
  subst h
  rfl

/-- Equal chart diagrams have heterogeneously equal ring maps. -/
theorem chartRing_heq {D₁ D₂ : ChartDiagram B S hS X.1 Y.1 f.hom} (h : D₁ = D₂) :
    HEq (chartRing B S hS E D₁) (chartRing B S hS E D₂) := by
  subst h
  rfl

/-- **The algebra compatibility, on chart transports.** -/
theorem transport_algebra (y : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    (inverseImageSectionTransport (smallEtaleRingedToposHom B S hS f) d.V d.U
        (chartDiagramSection B S hS f d)).app ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)
        (((smallEtaleRingedTopos B S hS Y).forgetRing.map (toBaseDirectImage B S hS E)).hom.app
          (op d.V) y) =
      (inverseImageSectionTransport
          (smallEtaleRingedToposHom B S hS
            (ambientImmersion E C hcU hcR ≫ ambientToBase E C hcU hcR))
          d.V d.U
        (chartDiagramSection B S hS (ambientImmersion E C hcU hcR ≫ ambientToBase E C hcU hcR)
          ⟨d.U, d.V, d.g, (congrArg (fun k => d.U.1.hom ≫ k.hom)
            (ambientImmersion_comp_toBase E C hcU hcR)).trans d.comm⟩)).app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)
        (((smallToposMorphismTypeU_comp B S hS (ambientImmersion E C hcU hcR)
            (ambientToBase E C hcU hcR)).hom.app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)).hom.app (op d.V)
        (((smallEtaleRingedToposHom B S hS (ambientToBase E C hcU hcR)).toToposHom.pushforward.map
            ((smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).forgetRing.map
              (ambientSharp (ambientImmersion E C hcU hcR)
                (ambientImmersion_fac E C hcU hcR)))).hom.app
            (op d.V)
          (((smallEtaleRingedTopos B S hS Y).forgetRing.map
            (smallEtaleRingedToposHom B S hS (ambientToBase E C hcU hcR)).fSharp).hom.app
              (op d.V) y))) := by
  refine eq_of_atlasChart (C := C) _ d.U ?_
  have hL := chartRing_precomp_apply E d (atlasChartHom C d.U) y
  refine hL.trans ?_
  have hT := transport_precomp (ambientImmersion E C hcU hcR ≫ ambientToBase E C hcU hcR)
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)
    ⟨d.U, d.V, d.g, (congrArg (fun k => d.U.1.hom ≫ k.hom)
      (ambientImmersion_comp_toBase E C hcU hcR)).trans d.comm⟩ (atlasChartHom C d.U)
    (((smallToposMorphismTypeU_comp B S hS (ambientImmersion E C hcU hcR)
            (ambientToBase E C hcU hcR)).hom.app
          ((smallEtaleRingedTopos B S hS X).forgetRing.obj E.A)).hom.app (op d.V)
        (((smallEtaleRingedToposHom B S hS (ambientToBase E C hcU hcR)).toToposHom.pushforward.map
            ((smallEtaleRingedTopos B S hS (ambient E C hcU hcR)).forgetRing.map
              (ambientSharp (ambientImmersion E C hcU hcR)
                (ambientImmersion_fac E C hcU hcR)))).hom.app
            (op d.V)
          (((smallEtaleRingedTopos B S hS Y).forgetRing.map
            (smallEtaleRingedToposHom B S hS (ambientToBase E C hcU hcR)).fSharp).hom.app
              (op d.V) y)))
  refine Eq.trans ?_ hT
  have hsec₀ := chartDiagramSection_heq (precomp_atlas_eq_comp E C hcU hcR d)
  have hsec := eq_of_heq hsec₀
  have hcr₀ := chartRing_heq E (liftChartDiagramF_precomp E C hcU hcR d)
  have hcr := eq_of_heq hcr₀
  rw [hsec, transport_directImage, ← hcr]
  refine (chartRing_precomp_apply E (liftChartDiagramF E C hcU hcR d)
    (chartDiagramBaseChangeLift B S hS (ambientImmersion E C hcU hcR)
      (ambRep _ (ambientImmersion_fac E C hcU hcR)) (liftDiagram E C hcU hcR d)) y).symm.trans ?_
  rw [chartRing_liftChartDiagramF]
  rfl

/-- **The ambient comparison `i⁻¹𝒪_{X'} ⟶ 𝒜` is one of algebras over the base.** -/
theorem algebra_compatibility_ambient :
    E.toBase = (canonicalBaseComparison B S hS (ambientImmersion E C hcU hcR)
        (ambientToBase E C hcU hcR) f (ambientImmersion_comp_toBase E C hcU hcR)).hom ≫
      (smallEtaleInverseImageRing B S hS (ambientImmersion E C hcU hcR)).map
        (smallEtaleRingedToposHom B S hS (ambientToBase E C hcU hcR)).fSharpInverseImage ≫
      ambientSheafIsoHom (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR) :=
  algebra_compatibility_of_transport E _ _ (ambientImmersion_comp_toBase E C hcU hcR)
    (ambientSharp (ambientImmersion E C hcU hcR) (ambientImmersion_fac E C hcU hcR))
    (transport_algebra E C hcU hcR)

end Transport

section Core

variable (E C hcU hcR)

include C hcU hcR in
/-- **Core existence of a realization** ([Stacks Project, Tag 05ZT], on a fixed site): when the
site `B` contains the first-order thickenings of the presenting chart and of the relation chart
of a charted presentation, the square-zero extension is realized by a first-order thickening
`X ⊂ X'` over the base. -/
theorem nonempty_realization : Nonempty (Realization B S hS E) := by
  have := (isThickeningHom_ambientMap (ambientImmersion E C hcU hcR)
    (ambientImmersion_fac E C hcU hcR)).1
  exact ⟨{
    ambient := ambient E C hcU hcR
    closed := Subfunctor.range (ambientImmersion E C hcU hcR).hom
    firstOrder := isFirstOrderThickening_range_ambientMap (ambientImmersion E C hcU hcR)
      (ambientImmersion_fac E C hcU hcR)
    closedIso := asIso (Subfunctor.toRange (ambientImmersion E C hcU hcR).hom)
    immersion := ambientImmersion E C hcU hcR
    immersion_eq := (Subfunctor.toRange_ι _).symm
    toBase := ambientToBase E C hcU hcR
    over_base := ambientImmersion_comp_toBase E C hcU hcR
    sheafIso := asIso (ambientSheafIsoHom (ambientImmersion E C hcU hcR)
      (ambientImmersion_fac E C hcU hcR))
    quotient_compatibility := ambientSheafIsoHom_comp_π (ambientImmersion E C hcU hcR)
      (ambientImmersion_fac E C hcU hcR)
    baseComparison := canonicalBaseComparison B S hS (ambientImmersion E C hcU hcR)
      (ambientToBase E C hcU hcR) f (ambientImmersion_comp_toBase E C hcU hcR)
    baseComparison_canonical := rfl
    algebra_compatibility := algebra_compatibility_ambient E C hcU hcR }⟩

end Core


end SquareZeroExtension

end AlgebraicGeometry.Space

end
