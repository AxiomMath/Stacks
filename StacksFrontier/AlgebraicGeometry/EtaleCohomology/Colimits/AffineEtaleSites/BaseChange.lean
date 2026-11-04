module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.LimitDescent.Faithfulness
public import StacksFrontier.AlgebraicGeometry.LimitDescentFull.Fullness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStages
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ColimitsOfSites
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# Base change of affine étale objects along an inverse system of schemes

Base change of objects of the small affine étale sites of the `X_i` along the transition maps and
to the limit `X`, the structure `Stacks.EtaleCohomology.AffineEtaleSiteColimit` of coherent
base-change data, and the descent of affineness and étaleness of a model from the limit to a
finite stage (Stacks 0EYL).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

/-- Étaleness is stable under pre- and postcomposition with isomorphisms, an isomorphism being an
open immersion and hence étale.

This instance and the three below record facts that Mathlib has only at shapes instance synthesis
does not reach at `instances` transparency, where `MorphismProperty` may not be unfolded; they
restate them at the shape the elaborator looks for. -/
private instance etaleRespectsIso : MorphismProperty.RespectsIso (@Etale.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf => have := hf; Etale.etale_comp e.hom f)
    (fun e f hf => have := hf; Etale.etale_comp f e.hom)

/-- Being locally of finite presentation is Zariski-local at the source. -/
private instance locallyOfFinitePresentationIsZariskiLocalAtSource :
    IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)

/-- Being locally of finite presentation is Zariski-local at the target. -/
private instance locallyOfFinitePresentationIsZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget
    (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)

/-- Étaleness is local at the source for the open-immersion precoverage. -/
private instance etaleIsLocalAtSourceOpenImmersion :
    MorphismProperty.IsLocalAtSource (@Etale.{u}) (Scheme.precoverage (@IsOpenImmersion.{u})) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)

/-- An étale precovering family is jointly surjective. -/
private instance etalePrecoverageJointlySurjective :
    Scheme.JointlySurjective (Scheme.precoverage (@Etale.{u})) :=
  Scheme.instJointlySurjectivePrecoverage

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)

/-- The structure map of an object of the small affine étale site of `X_i`. -/
public abbrev affineEtaleStructureMorphism (i : Iᵒᵖ)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).obj Y ⟶ D.obj i :=
  B.inclusion.map Y.obj.obj.hom

/-- The structure map of an object of the small affine étale site of the limit `X`. -/
public abbrev limitAffineEtaleStructureMorphism
    (Y : AlgebraicGeometry.SmallAffineEtale B c.pt hX) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).obj Y ⟶ c.pt :=
  B.inclusion.map Y.obj.obj.hom

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The structure morphism of a small affine étale object is étale. -/
private lemma affineEtaleStructureMorphism_etale (i : Iᵒᵖ)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    Etale (affineEtaleStructureMorphism D B hD i Y) := Y.obj.property

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- An étale structure morphism is locally of finite presentation. -/
private lemma affineEtaleStructureMorphism_locallyFinitePresentation (i : Iᵒᵖ)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    LocallyOfFinitePresentation (affineEtaleStructureMorphism D B hD i Y) := by
  let := affineEtaleStructureMorphism_etale D B hD i Y
  infer_instance

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The structure morphism of a small affine étale object over the limit is étale. -/
private lemma limitAffineEtaleStructureMorphism_etale
    (Y : AlgebraicGeometry.SmallAffineEtale B c.pt hX) :
    Etale (limitAffineEtaleStructureMorphism D c B hX Y) := Y.obj.property

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The structure morphism of a small affine étale object over the limit is locally of finite
presentation. -/
private lemma limitAffineEtaleStructureMorphism_locallyFinitePresentation
    (Y : AlgebraicGeometry.SmallAffineEtale B c.pt hX) :
    LocallyOfFinitePresentation (limitAffineEtaleStructureMorphism D c B hX Y) := by
  let := limitAffineEtaleStructureMorphism_etale D c B hX Y
  infer_instance

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- An affine étale object over the limit has a quasi-compact source. -/
private lemma limitAffineEtaleSource_compact
    (Y : AlgebraicGeometry.SmallAffineEtale B c.pt hX) :
    CompactSpace ((AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).obj Y) := by
  infer_instance

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- An affine étale object over the limit has a quasi-separated source. -/
private lemma limitAffineEtaleSource_quasiSeparated
    (Y : AlgebraicGeometry.SmallAffineEtale B c.pt hX) :
    QuasiSeparatedSpace ((AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).obj Y) := by
  infer_instance

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- An affine étale object has a quasi-compact source. -/
private lemma affineEtaleSource_compact (i : Iᵒᵖ)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    CompactSpace ((AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).obj Y) := by
  infer_instance

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- An affine étale object has a quasi-separated source. -/
private lemma affineEtaleSource_quasiSeparated (i : Iᵒᵖ)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i)) :
    QuasiSeparatedSpace
      ((AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj i) (hD i)).obj Y) := by
  infer_instance

/-- Base change of an affine étale object along an affine transition map is affine. -/
private lemma pullback_affine_of_affineHom_right {X Y S : Scheme.{u}}
    (f : Y ⟶ S) (g : X ⟶ S) [IsAffineHom g] [IsAffine Y] :
    IsAffine (pullback f g) := by
  let : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom.{u}) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsAffineHom.{u}) f :=
    ⟨fun sq hf => AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback sq hf⟩
  have : IsAffineHom (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
  exact AlgebraicGeometry.isAffine_of_isAffineHom (pullback.fst f g)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Base change of an affine étale object along an affine transition map is affine. -/
private lemma transitionBaseChange_affine {i j : Iᵒᵖ} (a : i ⟶ j)
    [IsAffineHom (D.map a)] (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj j) (hD j)) :
    IsAffine (pullback (affineEtaleStructureMorphism D B hD j Y) (D.map a)) := by
  let : IsAffine ((AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj j) (hD j)).obj Y) :=
    Y.property
  exact pullback_affine_of_affineHom_right
    (affineEtaleStructureMorphism D B hD j Y) (D.map a)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Base change of an étale object along a transition map remains étale. -/
private lemma transitionBaseChange_etale {i j : Iᵒᵖ} (a : i ⟶ j)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj j) (hD j)) :
    Etale (pullback.snd (affineEtaleStructureMorphism D B hD j Y) (D.map a)) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (affineEtaleStructureMorphism D B hD j Y) (D.map a))
    (affineEtaleStructureMorphism_etale D B hD j Y)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The base-changed transition object is still locally of finite presentation. -/
private lemma transitionBaseChange_locallyFinitePresentation {i j : Iᵒᵖ} (a : i ⟶ j)
    (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj j) (hD j)) :
    LocallyOfFinitePresentation
      (pullback.snd (affineEtaleStructureMorphism D B hD j Y) (D.map a)) := by
  let := transitionBaseChange_etale D B hD a Y
  infer_instance

/-- The geometric pullback of a small affine étale object along a transition map is again an
object of the small affine étale site. -/
private noncomputable def affineEtaleBaseChangeObject (B : AlgebraicGeometry.BigEtaleSite.{u})
    {S T : Scheme.{u}}
    (hS : B.Contains S) (hT : B.Contains T) (f : T ⟶ S) [IsAffineHom f]
    (Y : AlgebraicGeometry.SmallAffineEtale B S hS) :
    AlgebraicGeometry.SmallAffineEtale B T hT := by
  let g := B.inclusion.map Y.obj.obj.hom
  let P := pullback g f
  have hP : B.Contains P := by
    apply Scheme.size_pullback_lt
    · change B.Contains
        ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Y)
      exact (Y.obj.obj.left).property
    · exact hT
  let q : AlgebraicGeometry.BigEtaleOver B T hT :=
    Over.mk (B.inclusion.preimage (show
      B.inclusion.obj (B.obj P hP) ⟶ B.inclusion.obj (B.obj T hT) from
        pullback.snd g f))
  have hq : Etale (B.inclusion.map q.hom) := by
    change Etale (B.inclusion.map (B.inclusion.preimage (show
      B.inclusion.obj (B.obj P hP) ⟶ B.inclusion.obj (B.obj T hT) from
        pullback.snd g f)))
    rw [B.inclusion.map_preimage]
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback g f) Y.obj.property
  have hqaff : IsAffine
      ((AlgebraicGeometry.BigEtaleOver.toScheme B T hT).obj q) := by
    change IsAffine P
    let : IsAffine (B.inclusion.obj Y.obj.obj.left) := by
      change IsAffine ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Y)
      exact Y.property
    exact pullback_affine_of_affineHom_right g f
  exact ⟨⟨q, hq⟩, hqaff⟩

/-- The structure map of the base-changed object is the second pullback projection. -/
private lemma affineEtaleBaseChangeObject_structureMap (B : AlgebraicGeometry.BigEtaleSite.{u})
    {S T : Scheme.{u}}
    (hS : B.Contains S) (hT : B.Contains T) (f : T ⟶ S) [IsAffineHom f]
    (Y : AlgebraicGeometry.SmallAffineEtale B S hS) :
    B.inclusion.map ((affineEtaleBaseChangeObject B hS hT f Y).obj.obj.hom) =
      pullback.snd (B.inclusion.map Y.obj.obj.hom) f := by
  dsimp [affineEtaleBaseChangeObject]
  exact B.inclusion.map_preimage _

/-- The base-change object's structure square is a pullback square in schemes. -/
private lemma affineEtaleBaseChangeObject_isPullback (B : AlgebraicGeometry.BigEtaleSite.{u})
    {S T : Scheme.{u}}
    (hS : B.Contains S) (hT : B.Contains T) (f : T ⟶ S) [IsAffineHom f]
    (Y : AlgebraicGeometry.SmallAffineEtale B S hS) :
    IsPullback (pullback.fst (B.inclusion.map Y.obj.obj.hom) f)
      (B.inclusion.map ((affineEtaleBaseChangeObject B hS hT f Y).obj.obj.hom))
      (B.inclusion.map Y.obj.obj.hom) f := by
  rw [affineEtaleBaseChangeObject_structureMap]
  exact IsPullback.of_hasPullback _ _

/-- The inverse image of an affine open along a scheme diagram. -/
private noncomputable def limitOpensDiagram {J : Type v} [Category.{v, v} J]
    (E : J ⥤ Scheme.{u}) (i : J) (U : (E.obj i).Opens) : Over i ⥤ Scheme.{u} where
  obj j := E.map j.hom ⁻¹ᵁ U
  map {j k} f := (E.map f.left).resLE _ _
    (by rw [← Scheme.Hom.comp_preimage, ← E.map_comp, Over.w f])
  map_id := by
    intro j
    apply (cancel_mono (E.map j.hom ⁻¹ᵁ U).ι).1
    simp [Scheme.Hom.resLE_comp_ι]
  map_comp := by
    intro j k l f g
    apply (cancel_mono (E.map l.hom ⁻¹ᵁ U).ι).1
    simp [Scheme.Hom.resLE_comp_ι]

private noncomputable def limitOpensDiagramι {J : Type v} [Category.{v, v} J]
    (E : J ⥤ Scheme.{u}) (i : J) (U : (E.obj i).Opens) :
    limitOpensDiagram E i U ⟶ Over.forget _ ⋙ E where
  app j := Scheme.Opens.ι _
  naturality {j k} f := by simp [limitOpensDiagram]

attribute [local simp] Scheme.Hom.resLE_comp_resLE

private noncomputable def limitOpensCone {J : Type v} [Category.{v, v} J]
    {E : J ⥤ Scheme.{u}} (d : Cone E) (i : J) (U : (E.obj i).Opens) :
    Cone (limitOpensDiagram E i U) where
  pt := d.π.app i ⁻¹ᵁ U
  π.app j := (d.π.app j.left).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, d.w])
  π.naturality {j k} f := by simp [limitOpensDiagram]

private lemma limitOpensDiagramι_isOpenImmersion {J : Type v} [Category.{v, v} J]
    (E : J ⥤ Scheme.{u}) (i : J) (U : (E.obj i).Opens) (j : Over i) :
    IsOpenImmersion ((limitOpensDiagramι E i U).app j) := by
  show IsOpenImmersion (Scheme.Opens.ι _)
  infer_instance

private lemma limitOpensDiagram_isAffineHom {J : Type v} [Category.{v, v} J]
    {E : J ⥤ Scheme.{u}} [∀ {i j : J} (f : i ⟶ j), IsAffineHom (E.map f)]
    {i : J} (U : (E.obj i).Opens) {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((limitOpensDiagram E i U).map f) := by
  show IsAffineHom ((E.map f.left).resLE (E.map k.hom ⁻¹ᵁ U)
    (E.map j.hom ⁻¹ᵁ U) _)
  refine ⟨fun V hV => ?_⟩
  convert!
    ((hV.image_of_isOpenImmersion (E.map k.hom ⁻¹ᵁ U).ι).preimage
          (E.map f.left)).preimage_of_isOpenImmersion
      (E.map j.hom ⁻¹ᵁ U).ι ?_
  · ext x
    show _ ∈ V ↔ _
    refine ⟨fun h => ⟨⟨(E.map f.left).base x.1, ?_⟩, ?_, rfl⟩, ?_⟩
    · show (E.map f.left ≫ E.map k.hom).base x.1 ∈ U
      rw [← E.map_comp, Over.w f]
      exact x.2
    · convert! h
      apply Iff.of_eq
      congr 1
      exact Subtype.ext (Scheme.Hom.coe_resLE_apply _ _ x).symm
    · rintro ⟨⟨_, hU⟩, hV, rfl⟩
      convert! hV
      apply Iff.of_eq
      congr 1
      exact Subtype.ext (Scheme.Hom.coe_resLE_apply _ _ x)
  · simp only [Scheme.Opens.opensRange_ι]
    rintro x ⟨⟨y, h₁ : (E.map k.hom).base y ∈ U⟩, h₂, e⟩
    obtain rfl : y = (E.map f.left).base x := congr($e)
    dsimp at h₁
    rw [← Scheme.Hom.comp_apply] at h₁
    rwa [← E.map_comp, Over.w f] at h₁

attribute [local instance] limitOpensDiagramι_isOpenImmersion limitOpensDiagram_isAffineHom
  CategoryTheory.isConnected_of_hasTerminal

private noncomputable def isLimitLimitOpensCone {J : Type v} [Category.{v, v} J]
    {E : J ⥤ Scheme.{u}} {d : Cone E} (hd : IsLimit d) [IsCofiltered J]
    (i : J) (U : (E.obj i).Opens) : IsLimit (limitOpensCone d i U) := by
  let : IsConnected (Over i) := CategoryTheory.isConnected_of_hasTerminal _
  let : IsCofiltered (Over i) := inferInstance
  let : IsOpenImmersion ((d.π.app i ⁻¹ᵁ U).ι) := inferInstance
  let dOpen := limitOpensCone d i U
  let dBase := (Cone.postcompose (limitOpensDiagramι E i U)).obj dOpen
  let m : ConeMorphism dBase (d.whisker (Over.forget i)) := {
    hom := (d.π.app i ⁻¹ᵁ U).ι
    w := by
      intro j
      change (d.π.app i ⁻¹ᵁ U).ι ≫ d.π.app j.left =
        (d.π.app j.left).resLE (E.map j.hom ⁻¹ᵁ U) (d.π.app i ⁻¹ᵁ U) _ ≫
          Scheme.Opens.ι (E.map j.hom ⁻¹ᵁ U)
      exact (Scheme.Hom.resLE_comp_ι (d.π.app j.left)
        (by rw [← Scheme.Hom.comp_preimage, d.w])).symm }
  have : IsOpenImmersion m.hom := by
    change IsOpenImmersion ((d.π.app i ⁻¹ᵁ U).ι)
    infer_instance
  exact isLimitOfIsPullbackOfIsConnected (limitOpensDiagramι E i U) dOpen
    (d.whisker (Over.forget i)) m
    (fun j => IsOpenImmersion.isPullback _ _ _ _ (m.w j)
      (by
        dsimp [limitOpensDiagramι, limitOpensCone, limitOpensDiagram, m]
        simp only [Scheme.Opens.opensRange_ι]
        rw [← Scheme.Hom.comp_preimage, d.w]
        exact (Scheme.Opens.opensRange_ι _).symm))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) d).symm hd)

private lemma limitProjection_affine {J : Type v} [Category.{v, v} J]
    {E : J ⥤ Scheme.{u}} {d : Cone E} (hd : IsLimit d) [IsCofiltered J]
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (E.map f)] (i : J) :
    IsAffineHom (d.π.app i) := by
  refine ⟨fun U hU => ?_⟩
  let F := limitOpensDiagram E i U
  have : ∀ j, IsAffine (F.obj j) := fun j => hU.preimage _
  exact Scheme.isAffine_of_isLimit (limitOpensCone d i U)
    (isLimitLimitOpensCone hd i U)

/-- Pullback of an affine scheme along an affine morphism is affine, including the chosen
pullback in the bounded big site. -/
private lemma bigSitePullbackSource_affine (B : AlgebraicGeometry.BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) [IsAffineHom (B.inclusion.map f)]
    (A : Over S) (hA : IsAffine (B.inclusion.obj A.left)) :
    IsAffine (B.inclusion.obj ((Over.pullback f).obj A).left) := by
  let := AlgebraicGeometry.preservesPullbacks_bigEtaleSiteInclusion B
  have hpb : IsPullback (B.inclusion.map (pullback.fst A.hom f))
      (B.inclusion.map (pullback.snd A.hom f))
      (B.inclusion.map A.hom) (B.inclusion.map f) :=
    Functor.map_isPullback B.inclusion (IsPullback.of_hasPullback A.hom f)
  have : IsAffineHom (B.inclusion.map (pullback.fst A.hom f)) :=
    MorphismProperty.of_isPullback hpb.flip
      (show IsAffineHom (B.inclusion.map f) from inferInstance)
  show IsAffine (B.inclusion.obj (pullback A.hom f))
  exact AlgebraicGeometry.isAffine_of_isAffineHom
    (B.inclusion.map (pullback.fst A.hom f))

/-- Transition base change as an object-valued map on the small affine étale sites. -/
private noncomputable abbrev transitionBaseChangeObject {i j : Iᵒᵖ} (a : i ⟶ j)
    [IsAffineHom (D.map a)] (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj j) (hD j)) :
    AlgebraicGeometry.SmallAffineEtale B (D.obj i) (hD i) :=
  affineEtaleBaseChangeObject B (hD j) (hD i) (D.map a) Y

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The structure map of a transition base change is the second projection of its defining
pullback. -/
private lemma transitionBaseChangeObject_structureMap {i j : Iᵒᵖ} (a : i ⟶ j)
    [IsAffineHom (D.map a)] (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj j) (hD j)) :
    affineEtaleStructureMorphism D B hD i (transitionBaseChangeObject D B hD a Y) =
      pullback.snd (affineEtaleStructureMorphism D B hD j Y) (D.map a) :=
  affineEtaleBaseChangeObject_structureMap B (hD j) (hD i) (D.map a) Y

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The transition base change has its canonical fibre-product square. -/
private lemma transitionBaseChangeObject_isPullback {i j : Iᵒᵖ} (a : i ⟶ j)
    [IsAffineHom (D.map a)] (Y : AlgebraicGeometry.SmallAffineEtale B (D.obj j) (hD j)) :
    IsPullback (pullback.fst (affineEtaleStructureMorphism D B hD j Y) (D.map a))
      (affineEtaleStructureMorphism D B hD i (transitionBaseChangeObject D B hD a Y))
      (affineEtaleStructureMorphism D B hD j Y) (D.map a) :=
  affineEtaleBaseChangeObject_isPullback B (hD j) (hD i) (D.map a) Y

/-- Coherent base-change data for the small affine étale sites of an inverse system of schemes.

The levels are a strict inverse system of small sites (Stacks 0A34) equivalent to the small
affine étale sites of the `X_i`. The functors to the small affine étale site of `X` are geometric
base change along `X → X_i`, with coherent fibre-product projections. -/
public structure AffineEtaleSiteColimit where
  /-- The strict inverse system of small sites with finite coverings, Stacks 0A34. -/
  system : InverseSystemOfFiniteSites.{v, v, max v ((max u v) + 1)}
  /-- Its index category is the opposite of the directed index set. -/
  indexEquiv : system.I ≌ Iᵒᵖ
  /-- Each level is equivalent to the small affine étale site of the corresponding `X_i`. -/
  levelEquiv : ∀ i : system.I,
    system.C i ≌ AlgebraicGeometry.SmallAffineEtale B (D.obj (indexEquiv.functor.obj i))
      (hD (indexEquiv.functor.obj i))
  /-- The canonical functors from the levels to the small affine étale site of `X`. -/
  toLimit : ∀ i : system.I, system.C i ⥤ AlgebraicGeometry.SmallAffineEtale B c.pt hX
  /-- **Stacks 09YL**, cocone compatibility: the functors are compatible with the transitions. -/
  toLimit_transition : ∀ {i j : system.I} (a : i ⟶ j),
    system.u a ⋙ toLimit i = toLimit j
  /-- The projection of a transition base change onto the object it is based from. -/
  transitionFst : ∀ {i j : system.I} (a : i ⟶ j),
    system.u a ⋙ (levelEquiv i).functor ⋙
      AlgebraicGeometry.SmallAffineEtale.toScheme B
        (D.obj (indexEquiv.functor.obj i)) (hD (indexEquiv.functor.obj i)) ⟶
      (levelEquiv j).functor ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B
        (D.obj (indexEquiv.functor.obj j)) (hD (indexEquiv.functor.obj j))
  /-- Each transition functor is geometric base change: its square is a fibre product. -/
  transition_isPullback : ∀ {i j : system.I} (a : i ⟶ j) (Y : system.C j),
    IsPullback ((transitionFst a).app Y)
      (affineEtaleStructureMorphism D B hD (indexEquiv.functor.obj i)
        ((levelEquiv i).functor.obj ((system.u a).obj Y)))
      (affineEtaleStructureMorphism D B hD (indexEquiv.functor.obj j)
        ((levelEquiv j).functor.obj Y))
      (D.map (indexEquiv.functor.map a))
  /-- The transition projections respect identity arrows. -/
  transitionFst_id : ∀ (i : system.I) (Y : system.C i),
    (transitionFst (𝟙 i)).app Y =
      ((levelEquiv i).functor ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B
        (D.obj (indexEquiv.functor.obj i)) (hD (indexEquiv.functor.obj i))).map
        (eqToHom (Functor.congr_obj (system.id_map i) Y))
  /-- The transition projections respect composition. -/
  transitionFst_comp : ∀ {i j k : system.I} (a : i ⟶ j) (b : j ⟶ k)
      (Y : system.C k),
    (transitionFst (a ≫ b)).app Y =
      ((levelEquiv i).functor ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B
        (D.obj (indexEquiv.functor.obj i)) (hD (indexEquiv.functor.obj i))).map
          (eqToHom (Functor.congr_obj (system.comp a b) Y)) ≫
        (transitionFst a).app ((system.u b).obj Y) ≫ (transitionFst b).app Y
  /-- The projection of a base change to `X` onto the object it is based from. -/
  toLimitFst : ∀ i : system.I,
    toLimit i ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX ⟶
      (levelEquiv i).functor ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B
        (D.obj (indexEquiv.functor.obj i)) (hD (indexEquiv.functor.obj i))
  /-- Each canonical functor is geometric base change along `X → X_i`: its square is a fibre
  product. -/
  toLimit_isPullback : ∀ (i : system.I) (Y : system.C i),
    IsPullback ((toLimitFst i).app Y)
      (limitAffineEtaleStructureMorphism D c B hX ((toLimit i).obj Y))
      (affineEtaleStructureMorphism D B hD (indexEquiv.functor.obj i)
        ((levelEquiv i).functor.obj Y))
      (c.π.app (indexEquiv.functor.obj i))
  /-- The projections to `X` are compatible with the transition projections. -/
  toLimitFst_transition : ∀ {i j : system.I} (a : i ⟶ j) (Y : system.C j),
    (toLimitFst j).app Y =
      (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map
        (eqToHom (Functor.congr_obj (toLimit_transition a) Y).symm) ≫
      (toLimitFst i).app ((system.u a).obj Y) ≫ (transitionFst a).app Y

/-- The fully faithful inclusion into the ordinary category of schemes over the base. -/
private abbrev affineEtaleToOver (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicGeometry.SmallAffineEtale B S hS ⥤ Over S :=
  AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
    AlgebraicGeometry.SmallEtale.inclusion B S hS ⋙ Over.post B.inclusion

private instance affineEtaleToOver_full (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) : (affineEtaleToOver B S hS).Full := by
  change ((AlgebraicGeometry.SmallEtale.IsAffine B S hS).ι ⋙
    (AlgebraicGeometry.BigEtaleOver.IsEtaleOver B S hS).ι ⋙
    Over.post (AlgebraicGeometry.schemeSizeBelow B.cutoff).ι).Full
  infer_instance

/-- Equality after a chosen pullback is equivalent to equality after the canonical pullback. -/
private lemma pullback_map_eq_of_comp_eq
    {C : Type*} [Category* C] [HasPullbacks C] {S T : C} (q : T ⟶ S)
    {A A' : Over S} {P : C} (p : P ⟶ A.left) (t : P ⟶ T)
    (h : IsPullback p t A.hom q) (f g : A ⟶ A') (hfg : p ≫ f.left = p ≫ g.left) :
    (Over.pullback q).map f = (Over.pullback q).map g := by
  have heq : pullback.fst A.hom q ≫ f.left = pullback.fst A.hom q ≫ g.left := by
    calc
      _ = h.isoPullback.inv ≫ p ≫ f.left := by simp
      _ = h.isoPullback.inv ≫ p ≫ g.left := by rw [hfg]
      _ = _ := by simp
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp [Over.pullback_map_left, heq]

/-- Equality after the canonical pullback can be tested on its first projections. -/
private lemma comp_eq_of_pullback_map_eq
    {C : Type*} [Category* C] [HasPullbacks C] {S T : C} (q : T ⟶ S)
    {A A' : Over S} (f g : A ⟶ A')
    (hfg : (Over.pullback q).map f = (Over.pullback q).map g) :
    pullback.fst A.hom q ≫ f.left = pullback.fst A.hom q ≫ g.left := by
  have h := congrArg (fun z => z.left ≫ pullback.fst A'.hom q) hfg
  simpa only [Over.pullback_map_left, pullback.lift_fst] using h

/-- The canonical pullback functor is compatible with the first projections. -/
private lemma pullback_map_left_fst
    {C : Type*} [Category* C] [HasPullbacks C] {S T : C} (q : T ⟶ S)
    {A A' : Over S} (g : A ⟶ A') :
    ((Over.pullback q).map g).left ≫ pullback.fst A'.hom q =
      pullback.fst A.hom q ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

/-- Transporting a base-change identification along an isomorphism `U ≅ π^* A` gives a map to the
doubly pulled-back object compatible with the projections. -/
private lemma comp_pullback_fst_eq_of_iso
    {C : Type*} [Category* C] [HasPullbacks C] {X Xj Xi : C} (π : X ⟶ Xi) (πj : X ⟶ Xj)
    (e : Xj ⟶ Xi) (A : Over Xi) (U : Over X) (eU : U ≅ (Over.pullback π).obj A)
    (α : (Over.pullback πj).obj ((Over.pullback e).obj A) ≅ (Over.pullback π).obj A)
    (hα : α.hom.left ≫ pullback.fst A.hom π =
      pullback.fst ((Over.pullback e).obj A).hom πj ≫ pullback.fst A.hom e) :
    ((eU.hom ≫ α.inv).left ≫ pullback.fst ((Over.pullback e).obj A).hom πj) ≫
        pullback.fst A.hom e = eU.hom.left ≫ pullback.fst A.hom π ∧
      ((eU.hom ≫ α.inv).left ≫ pullback.fst ((Over.pullback e).obj A).hom πj) ≫
        pullback.snd A.hom e = U.hom ≫ πj := by
  refine ⟨?_, ?_⟩
  · have hh := congrArg (fun z => α.inv.left ≫ z) hα
    have hh' : α.inv.left ≫ pullback.fst ((Over.pullback e).obj A).hom πj ≫
        pullback.fst A.hom e = pullback.fst A.hom π := by
      simpa using hh.symm
    simpa [Category.assoc] using congrArg (fun z => eU.hom.left ≫ z) hh'
  · dsimp
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun z => z ≫ πj) (Over.w (eU.hom ≫ α.inv))

/-- A morphism between two chosen geometric pullbacks descends together with its projections. -/
private lemma exists_hom_of_isPullback (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i : I) (A A' : Over (D.obj (Opposite.op i)))
    (hAqc : CompactSpace A.left) (hAqs : QuasiSeparatedSpace A.left)
    (hA'qc : CompactSpace A'.left) (hA'qs : QuasiSeparatedSpace A'.left)
    (hA : LocallyOfFinitePresentation A.hom) (hA' : LocallyOfFinitePresentation A'.hom)
    (U V : Over c.pt) (p : U.left ⟶ A.left) (q : V.left ⟶ A'.left)
    (hp : IsPullback p U.hom A.hom (c.π.app (Opposite.op i)))
    (hq : IsPullback q V.hom A'.hom (c.π.app (Opposite.op i))) (f : U ⟶ V) :
    ∃ (j : I) (hij : i ≤ j)
      (g : (Over.pullback (D.map (homOfLE hij).op)).obj A ⟶
        (Over.pullback (D.map (homOfLE hij).op)).obj A')
      (s : U.left ⟶ pullback A.hom (D.map (homOfLE hij).op))
      (t : V.left ⟶ pullback A'.hom (D.map (homOfLE hij).op)),
      s ≫ pullback.fst _ _ = p ∧
      s ≫ pullback.snd _ _ = U.hom ≫ c.π.app (Opposite.op j) ∧
      t ≫ pullback.fst _ _ = q ∧
      t ≫ pullback.snd _ _ = V.hom ≫ c.π.app (Opposite.op j) ∧
      s ≫ g.left = f.left ≫ t := by
  let eU : U ≅ (Over.pullback (c.π.app (Opposite.op i))).obj A :=
    Over.isoMk hp.isoPullback hp.isoPullback_hom_snd
  let eV : V ≅ (Over.pullback (c.π.app (Opposite.op i))).obj A' :=
    Over.isoMk hq.isoPullback hq.isoPullback_hom_snd
  obtain ⟨j, hij, g, α, β, hα, hβ, hfg⟩ :=
    AlgebraicGeometry.LimitDescent.exists_morphism_after_baseChange_of_small D c hc i A A'
      hAqc hAqs hA'qc hA'qs hA hA' (eU.inv ≫ f ≫ eV.hom)
  let e := (homOfLE hij).op
  let s := (eU.hom ≫ α.inv).left ≫
    pullback.fst ((Over.pullback (D.map e)).obj A).hom (c.π.app (Opposite.op j))
  let t := (eV.hom ≫ β.inv).left ≫
    pullback.fst ((Over.pullback (D.map e)).obj A').hom (c.π.app (Opposite.op j))
  have hU := comp_pullback_fst_eq_of_iso (c.π.app (Opposite.op i)) (c.π.app (Opposite.op j))
    (D.map e) A U eU α hα
  have hV := comp_pullback_fst_eq_of_iso (c.π.app (Opposite.op i)) (c.π.app (Opposite.op j))
    (D.map e) A' V eV β hβ
  refine ⟨j, hij, g, s, t, hU.1.trans hp.isoPullback_hom_fst, hU.2,
    hV.1.trans hq.isoPullback_hom_fst, hV.2, ?_⟩
  have h : (eU.hom ≫ α.inv) ≫ (Over.pullback (c.π.app (Opposite.op j))).map g =
      f ≫ (eV.hom ≫ β.inv) := by
    calc
      _ = eU.hom ≫ α.inv ≫
          ((Over.pullback (c.π.app (Opposite.op j))).map g ≫ β.hom) ≫ β.inv := by simp
      _ = _ := by rw [← hfg]; simp
  have h' := congrArg (fun z => z.left ≫
    pullback.fst ((Over.pullback (D.map e)).obj A').hom (c.π.app (Opposite.op j))) h
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (eU.hom ≫ α.inv).left ≫ z)
    (pullback_map_left_fst (c.π.app (Opposite.op j)) g).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine h'.trans ?_
  exact Category.assoc _ _ _

/-- A cone over a diagram induces a cone in the slice over any stage. -/
private def overStageCone {J : Type*} [Category* J] {C : Type*} [Category* C]
    (D : J ⥤ C) (c : Cone D) (i : J) : Cone (Over.post D : Over i ⥤ Over (D.obj i)) where
  pt := Over.mk (c.π.app i)
  π := {
    app j := Over.homMk (c.π.app j.left) (c.w j.hom)
    naturality j k a := by
      apply Over.OverMorphism.ext
      exact c.π.naturality a.left }

/-- The slice cone over a cofiltered diagram is a limit cone. -/
private def isLimitOverStageCone {J : Type*} [Category* J] [IsCofiltered J]
    {C : Type*} [Category* C] (D : J ⥤ C) (c : Cone D) (hc : IsLimit c) (i : J) :
    IsLimit (overStageCone D c i) :=
  isLimitOfReflects (Over.forget (D.obj i))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

/-- A map between two base changes is itself the base change of the original map. -/
private lemma isPullback_pullback_map {C : Type*} [Category* C] [HasPullbacks C]
    {S T : C} (f : T ⟶ S) {A A' : Over S} (g : A ⟶ A') :
    IsPullback ((Over.pullback f).map g).left (pullback.fst A.hom f)
      (pullback.fst A'.hom f) g.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd A'.hom f)
    (h₂₂ := A'.hom) (v₁₃ := f)
  · simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback A.hom f).flip
  · simp only [Over.pullback_map_left, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback A'.hom f).flip

/-- Affineness of a quasi-compact and quasi-separated model descends from the limit. -/
private lemma exists_affine_baseChange (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i : Iᵒᵖ) (A : Over (D.obj i)) [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [IsAffine ((Over.pullback (c.π.app i)).obj A).left] :
    ∃ j : Over i, IsAffine ((Over.pullback (D.map j.hom)).obj A).left := by
  let F := Over.post D ⋙ Over.pullback A.hom ⋙ Over.forget A.left
  let d := (Over.pullback A.hom ⋙ Over.forget A.left).mapCone (overStageCone D c i)
  have hd : IsLimit d := isLimitOfPreserves _ (isLimitOverStageCone D c hc i)
  have : IsAffine d.pt := by
    show IsAffine (pullback (c.π.app i) A.hom)
    have : IsAffine (pullback A.hom (c.π.app i)) :=
      ‹IsAffine ((Over.pullback (c.π.app i)).obj A).left›
    exact IsAffine.of_isIso (pullbackSymmetry (c.π.app i) A.hom).hom
  have (j : Over i) : IsAffineHom (pullback.snd (D.map j.hom) A.hom) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have (j : Over i) : CompactSpace (F.obj j) := by
    show CompactSpace ↥(pullback (D.map j.hom) A.hom)
    infer_instance
  have (j : Over i) : QuasiSeparatedSpace (F.obj j) := by
    show QuasiSeparatedSpace ↥(pullback (D.map j.hom) A.hom)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map j.hom) A.hom)
  have {j k : Over i} (a : j ⟶ k) : IsAffineHom (F.map a) :=
    MorphismProperty.of_isPullback
      (isPullback_pullback_map A.hom ((Over.post D).map a)).flip
      (show IsAffineHom (D.map a.left) from inferInstance)
  let E : AsSmall.{max u v} (Over i) ⥤ Over i := AsSmall.down
  have : IsCofiltered (AsSmall.{max u v} (Over i)) :=
    IsCofiltered.of_equivalence (AsSmall.equiv : Over i ≌ AsSmall.{max u v} (Over i))
  have : E.IsEquivalence :=
    (AsSmall.equiv : Over i ≌ AsSmall.{max u v} (Over i)).isEquivalence_inverse
  have {j k : AsSmall.{max u v} (Over i)} (a : j ⟶ k) :
      IsAffineHom ((E ⋙ F).map a) := by
    show IsAffineHom (F.map (E.map a))
    infer_instance
  have (j : AsSmall.{max u v} (Over i)) : CompactSpace ((E ⋙ F).obj j) :=
    show CompactSpace (F.obj (E.obj j)) from inferInstance
  have (j : AsSmall.{max u v} (Over i)) : QuasiSeparatedSpace ((E ⋙ F).obj j) :=
    show QuasiSeparatedSpace (F.obj (E.obj j)) from inferInstance
  have : IsAffine (d.whisker E).pt := ‹IsAffine d.pt›
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit (E ⋙ F) (d.whisker E)
    ((Functor.Initial.isLimitWhiskerEquiv E d).symm hd)
  refine ⟨E.obj j, ?_⟩
  let : IsAffine (pullback (D.map (E.obj j).hom) A.hom) := hj
  exact IsAffine.of_isIso (pullbackSymmetry A.hom (D.map (E.obj j).hom)).hom

/-- An affine scheme locally of finite presentation over the limit has an affine model. -/
private lemma exists_affine_model_of_locallyOfFinitePresentation (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (A : Over c.pt) [IsAffine A.left] (hA : LocallyOfFinitePresentation A.hom) :
    ∃ (i : Iᵒᵖ) (Aᵢ : Over (D.obj i)), IsAffine Aᵢ.left ∧
      LocallyOfFinitePresentation Aᵢ.hom ∧
      Nonempty (A ≅ (Over.pullback (c.π.app i)).obj Aᵢ) := by
  have : FinallySmall.{max u v} I := finallySmall_of_essentiallySmall I
  obtain ⟨i, Aᵢ, _, _, _, ⟨e⟩⟩ :=
    AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation D c hc A
      inferInstance inferInstance hA
  have : IsAffine ((Over.pullback (c.π.app (.op i))).obj Aᵢ).left :=
    @IsAffine.of_isIso _ _ ((Over.forget _).mapIso e).inv
      inferInstance (show IsAffine ((Over.forget _).obj A) from ‹IsAffine A.left›)
  obtain ⟨j, hj⟩ := exists_affine_baseChange D c hc (.op i) Aᵢ
  let Aⱼ := (Over.pullback (D.map j.hom)).obj Aᵢ
  refine ⟨j.left, Aⱼ, hj, ?_, ?_⟩
  · show LocallyOfFinitePresentation (pullback.snd Aᵢ.hom (D.map j.hom))
    infer_instance
  · exact ⟨e ≪≫ (eqToIso (congrArg (fun f => (Over.pullback f).obj Aᵢ)
      (c.w j.hom).symm)) ≪≫ (Over.pullbackComp (c.π.app j.left) (D.map j.hom)).app Aᵢ⟩

/-- Étaleness of a locally finitely presented model over a qcqs stage descends. -/
private lemma exists_etale_baseChange {J : Type u} [Category.{u} J] [IsCofiltered J]
    (F : J ⥤ Scheme.{u}) (d : Cone F) (hd : IsLimit d)
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (F.map a)]
    (i : J) [CompactSpace (F.obj i)] [QuasiSeparatedSpace (F.obj i)]
    (A : Over (F.obj i)) [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [LocallyOfFinitePresentation A.hom]
    [Etale ((Over.pullback (d.π.app i)).obj A).hom] :
    ∃ j : Over i, Etale ((Over.pullback (F.map j.hom)).obj A).hom := by
  let T : Over (F.obj i) := Over.mk (𝟙 (F.obj i))
  let f : A ⟶ T := Over.homMk A.hom (Category.comp_id _)
  have : CompactSpace T.left := ‹CompactSpace (F.obj i)›
  have : QuasiSeparatedSpace T.left := ‹QuasiSeparatedSpace (F.obj i)›
  have : IsIso T.hom := by change IsIso (𝟙 (F.obj i)); infer_instance
  have : LocallyOfFinitePresentation f.left := ‹LocallyOfFinitePresentation A.hom›
  have : Etale ((Over.pullback (d.π.app i)).map f).left := by
    apply (MorphismProperty.cancel_right_of_respectsIso (@Etale : MorphismProperty Scheme.{u})
      ((Over.pullback (d.π.app i)).map f).left
      (pullback.snd T.hom (d.π.app i))).mp
    rw [show ((Over.pullback (d.π.app i)).map f).left ≫
        pullback.snd T.hom (d.π.app i) =
        ((Over.pullback (d.π.app i)).obj A).hom from
      Over.w ((Over.pullback (d.π.app i)).map f)]
    infer_instance
  obtain ⟨j, hj⟩ := AlgebraicGeometry.exists_etale_pullback_of_isLimit F d hd i A T f
  refine ⟨j, ?_⟩
  have := hj
  have : Etale ((Over.pullback (F.map j.hom)).obj T).hom := by
    show Etale (pullback.snd T.hom (F.map j.hom))
    infer_instance
  rw [← Over.w ((Over.pullback (F.map j.hom)).map f)]
  exact Etale.etale_comp _ _

end Stacks.EtaleCohomology

end
