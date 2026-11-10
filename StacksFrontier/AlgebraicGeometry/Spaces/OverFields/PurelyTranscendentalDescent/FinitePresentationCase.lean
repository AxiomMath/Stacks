module

public import Mathlib
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SmallApproximationOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationInduction
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureFGSubalgebraDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Spaces.Flat
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFromEtaleCover
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.AlgebraMapSections
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.QuasiCompactReduction

/-!
# The finite presentation case of purely transcendental descent over a finite field

Over a finite field: closed points represented by finite field extensions, finite
presentation models of spaces whose base change is a scheme, field-valued points factoring
through open subschemes, fibres of base change along finite field extensions, and the case of a
space of finite presentation.

This is part of `StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace PurelyTranscendentalDescent

attribute [local instance] MorphismProperty.IsMultiplicative.toContainsIdentities
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private instance : MorphismProperty.ContainsIdentities
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun _ ↦ inferInstance⟩

private instance : MorphismProperty.ContainsIdentities
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun _ ↦ inferInstance⟩

private instance : MorphismProperty.RespectsIso
    (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private instance : MorphismProperty.RespectsIso
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private instance : MorphismProperty.RespectsIso
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private theorem isQuasiCompact_source
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS G)
    (hf : AlgebraicGeometry.Space.IsQuasiCompact B S hS f) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS F :=
  AlgebraicGeometry.Space.IsQuasiCompactSpace.of_iso B S hS (hf G hG hqc (𝟙 G))
    (asIso (pullback.snd (𝟙 G) f))

private theorem isDecent_of_isQuasiSeparated
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hqs : AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ F) :
    AlgebraicGeometry.Space.IsDecentSpace B S hS F :=
  AlgebraicGeometry.Space.isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS F hF hqs

private theorem presheaf_property_id
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities] [P.RespectsIso]
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    (MorphismProperty.inverseImage P (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (𝟙 (yoneda.obj U)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, fun A V g a p hp => ?_⟩
  have : IsIso (yoneda.map p) := hp.isIso_snd_of_isIso
  have : IsIso p := Yoneda.fullyFaithful.isIso_of_isIso_map p
  exact P.of_isIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p)

private theorem isQuasiCompact_yoneda_of_compactSpace
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    [CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)] :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (yoneda.obj U) :=
  ⟨U, 𝟙 _, inferInstance, presheaf_property_id B S hS _ U,
    isEtale_of_presheaf_etale B S hS _ (presheaf_property_id B S hS _ U)⟩

private theorem isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS f) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS f := by
  intro U V a b g ha hb hab
  have := hf U V a b g ha hb hab
  infer_instance

private theorem jacobson_of_locallyOfFiniteType_overField
    (k : Type u) [Field k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (f : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : AlgebraicGeometry.Space.IsLocallyOfFiniteType B (Spec (.of k)) hk f) :
    AlgebraicGeometry.Space.HasEtaleLocalProperty B (Spec (.of k)) hk F
      (fun T : Scheme.{u} => JacobsonSpace T) :=
  AlgebraicGeometry.Space.exists_jacobson_atlas_of_isLocallyOfFiniteType B (Spec (.of k)) hk
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk _) hF f hf
    ⟨Over.mk (𝟙 (B.obj hk)), 𝟙 _, presheaf_property_id B (Spec (.of k)) hk _ _,
    presheaf_property_id B (Spec (.of k)) hk _ _,
    inferInstanceAs (JacobsonSpace (Spec (.of k)))⟩

private theorem exists_finite_fieldRepresentative_of_closedPoint
    (k : Type u) [Field k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hdec : AlgebraicGeometry.Space.IsDecentSpace B (Spec (.of k)) hk F)
    (f : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hf : AlgebraicGeometry.Space.IsLocallyOfFiniteType B (Spec (.of k)) hk f)
    (x : AlgebraicGeometry.Space.points B (Spec (.of k)) hk F)
    (hx : @IsClosed _ (AlgebraicGeometry.Space.pointTopology B (Spec (.of k)) hk F) {x}) :
    ∃ p : AlgebraicGeometry.Space.FieldValuedPoint B (Spec (.of k)) hk F,
      p.class B (Spec (.of k)) hk F = x ∧ (Spec.preimage p.toBase).hom.Finite := by
  have hxt : AlgebraicGeometry.Space.IsFiniteTypePoint B (Spec (.of k)) hk F x := by
    change x ∈ AlgebraicGeometry.Space.finiteTypePoints B (Spec (.of k)) hk F
    rwa [AlgebraicGeometry.Space.finiteTypePoints_eq_setOf_isClosed_singleton B (Spec (.of k))
      hk hF hdec (jacobson_of_locallyOfFiniteType_overField k B hk F hF f hf)]
  obtain ⟨p, hpx, hp⟩ := hxt
  refine ⟨p, hpx, ?_⟩
  let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let g : p.siteObject ⟶ T := Over.homMk p.siteObject.hom
  have hcomp := AlgebraicGeometry.Space.isLocallyOfFiniteType_comp B (Spec (.of k)) hk
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk _) hF
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk T)
    (yonedaEquiv.symm p.value) f hp hf
  have hg : LocallyOfFiniteType p.toBase :=
    hcomp p.siteObject T (𝟙 _) (𝟙 _) g
      (presheaf_property_id B (Spec (.of k)) hk _ _)
      (presheaf_property_id B (Spec (.of k)) hk _ _)
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).hom_ext _ _)
  let : Algebra k p.carrier := (Spec.preimage p.toBase).hom.toAlgebra
  have : Algebra.FiniteType k p.carrier := by
    apply (RingHom.finiteType_algebraMap).mp
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rwa [Spec.map_preimage]
  exact RingHom.finite_algebraMap.mpr (finite_of_finite_type_of_isJacobsonRing k p.carrier)

private theorem pointsMap_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H) (x : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS G g (AlgebraicGeometry.Space.pointsMap B S hS F f x) =
      AlgebraicGeometry.Space.pointsMap B S hS F (f ≫ g) x := by
  induction x using Quot.inductionOn with | _ p => rfl

private theorem subsingleton_points_fieldSiteObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS F) :
    Subsingleton (AlgebraicGeometry.Space.points B S hS (yoneda.obj p.siteObject)) := by
  let q : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj p.siteObject) :=
    { carrier := p.carrier, contained := p.contained, toBase := p.toBase, value := 𝟙 _ }
  have h (x : AlgebraicGeometry.Space.points B S hS (yoneda.obj p.siteObject)) :
      x = q.class B S hS (yoneda.obj p.siteObject) := by
    induction x using Quot.inductionOn with | _ r =>
    apply AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension
    exact ⟨r, AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl B S hS _ r,
      r.value, by change 𝟙 _ ≫ r.value = r.value; simp⟩
  exact ⟨fun x y => (h x).trans (h y).symm⟩

private theorem isAlgebraicSpace_yoneda_prod
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (T : AlgebraicGeometry.BigFppfOver B S hS) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS (yoneda.obj T ⨯ F) :=
  (isAlgebraicSpace_prod_yoneda B S hS F hF T).of_iso (prod.braiding _ _)

private theorem presheaf_affine_prod_snd
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (hT : IsAffineHom (B.inclusion.map T.hom)) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (prod.snd : yoneda.obj T ⨯ F ⟶ F) := by
  let P := (MorphismProperty.inverseImage (@IsAffineHom.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
  let : P.RespectsIso := inferInstance
  simpa using MorphismProperty.RespectsIso.precomp P
    (prod.braiding (yoneda.obj T) F).hom prod.fst (presheaf_affine_prod_fst B S hS F T hT)

private theorem isAbsolutelyQuasiSeparated_yoneda_terminal
    (k : Type u) [CommRing k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k))) :
    AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal
      (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :=
  AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme
    B (Spec (.of k)) hk _ B.contains_terminal ⟨Over.mk (𝟙 (B.obj hk)),
      inferInstanceAs (QuasiSeparatedSpace (Spec (.of k))),
      ⟨Functor.RepresentableBy.yoneda (Over.mk (𝟙 (B.obj hk)))⟩⟩

private theorem preservesLimitsOfShape_prod_of_isDirected
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] :
    PreservesLimitsOfShape Iᵒᵖ (prod.functor.obj X) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  have : CategoryTheory.IsConnected (AsSmall.{u + 1} Iᵒᵖ) :=
    isConnected_of_equivalent AsSmall.equiv
  have := prod_preservesConnectedLimits (J := AsSmall.{u + 1} Iᵒᵖ) X
  exact preservesLimitsOfShape_of_equiv AsSmall.equiv.symm (prod.functor.obj X)

/-- Let `F` be an algebraic space over a field `k` which is the directed limit of algebraic spaces
`D i` of finite presentation over `k` with affine transition morphisms, and let `T` be affine over
`k` such that the base change of `F` to `T` is representable. Then there are an algebraic space `G`
of finite presentation over `k` and an affine morphism `F ⟶ G` such that the base change of `G` to
`T` is representable. -/
theorem exists_finitePresentation_model_of_isRepresentable_baseChange
    (k : Type u) [Field k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)
    (hT : IsAffineHom (B.inclusion.map T.hom))
    (hbase : ((OverShriek.relocalizeRestrict T.hom).obj F).IsRepresentable)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (hI : Cardinal.mk I < B.cutoff.ord.cof)
    (D : Iᵒᵖ ⥤ ((AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u))
    (p : (Functor.const Iᵒᵖ).obj F ⟶ D) (hp : IsLimit (Cone.mk F p))
    (hD : ∀ i, AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk (D.obj i))
    (hfp : ∀ i, AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of k)) hk
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from (D.obj i)))
    (haff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      AlgebraicGeometry.Space.IsAffineHom B (Spec (.of k)) hk (D.map g)) :
    ∃ (G : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u),
      AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk G ∧
      ∃ (f : G ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))) (g : F ⟶ G),
      AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of k)) hk f ∧
      AlgebraicGeometry.Space.IsAffineHom B (Spec (.of k)) hk g ∧
      ((OverShriek.relocalizeRestrict T.hom).obj G).IsRepresentable := by
  classical
  let hZ := B.contains_terminal
  let Z : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let Y := yoneda.obj Z
  have hY := AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk Z
  have hYqc := @isQuasiCompact_yoneda_of_compactSpace B (Spec (.of k)) hk Z
    (inferInstanceAs (CompactSpace (Spec (.of k))))
  let t : D ⟶ (Functor.const Iᵒᵖ).obj Y :=
    { app := fun i => (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from (D.obj i)
      naturality := fun _ _ _ =>
        (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).hom_ext _ _ }
  have hDqc (i : Iᵒᵖ) := isQuasiCompact_source B (Spec (.of k)) hk (t.app i) hY hYqc (hfp i).2.1
  have hDqs (i : Iᵒᵖ) := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B (Spec (.of k)) hk hZ (hD i) (isAbsolutelyQuasiSeparated_yoneda_terminal k B hk) (hfp i).2.2
  let P := prod.functor.obj (yoneda.obj T)
  let c := P.mapCone (Cone.mk F p)
  have : PreservesLimitsOfShape Iᵒᵖ P :=
    preservesLimitsOfShape_prod_of_isDirected B (Spec (.of k)) hk (yoneda.obj T) I
  have hprod (i : Iᵒᵖ) := isAlgebraicSpace_yoneda_prod B (Spec (.of k)) hk _ (hD i) T
  have hproj (i : Iᵒᵖ) := presheaf_affine_prod_snd B (Spec (.of k)) hk (D.obj i) T hT
  let E : AlgebraicGeometry.Space.DescentSituation B (Spec (.of k)) hk hZ I :=
    { system := D ⋙ P
      algebraicSpace i := hprod (Opposite.op i)
      transition_affine f := isAffineHom_of_isPullback B (Spec (.of k)) hk
        (isPullback_prod_snd_map _ (D.map f)) (haff f)
      quasiCompact i := isQuasiCompact_of_isAffineHom B (Spec (.of k)) hk
        prod.snd (hprod _) (hD _) (isAffineHom_of_presheaf_affine B (Spec (.of k)) hk _
          (hproj _)) (hDqc _)
      quasiSeparated i := isQuasiSeparated_of_presheaf_affine B (Spec (.of k)) hk hZ
        (hprod _) (hD _) prod.snd (hproj _) (hDqs _)
      limitCone := c
      isLimit := isLimitOfPreserves P hp
      limitAlgebraicSpace := isAlgebraicSpace_yoneda_prod B (Spec (.of k)) hk F hF T
      base := Classical.arbitrary I }
  have hTeq : Over.mk T.hom = T := by cases T; rfl
  have hswap {X Y : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
      (h : (X ⨯ Y).IsRepresentable) : (Y ⨯ X).IsRepresentable :=
    isRepresentable_of_natIso _ (prod.braiding _ _)
  have hcrep : c.pt.IsRepresentable := by
    have h := isRepresentable_prod_of_relocalizeRestrict T.hom F hbase
    rw [hTeq] at h
    exact hswap h
  obtain ⟨i, hi⟩ := E.exists_isRepresentable_system_obj_of_mk_lt hI hcrep
  refine ⟨D.obj (Opposite.op i), hD _, t.app _, p.app _, hfp _,
    isAffineHom_cone_projection B (Spec (.of k)) hk D hD haff _ hp hF _, ?_⟩
  apply isRepresentable_relocalizeRestrict_of_prod T.hom _
  rw [hTeq]
  exact hswap hi

private noncomputable def affineOpenObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.BigFppfOver B S hS)
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj X).affineOpens) :
    AlgebraicGeometry.BigFppfOver B S hS := by
  let Vsite : B.Schemes :=
    ⟨U.1.toScheme, (Scheme.size_coe_opens_le _ U.1).trans_lt X.left.2⟩
  let i : Vsite ⟶ X.left := ObjectProperty.homMk (Scheme.Opens.ι U.1)
  exact Over.mk (i ≫ X.hom)

private noncomputable def affineOpenInclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicGeometry.BigFppfOver B S hS)
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj X).affineOpens) :
    affineOpenObject B S hS X U ⟶ X := by
  let Vsite : B.Schemes :=
    ⟨U.1.toScheme, (Scheme.size_coe_opens_le _ U.1).trans_lt X.left.2⟩
  let i : Vsite ⟶ X.left := ObjectProperty.homMk (Scheme.Opens.ι U.1)
  exact Over.homMk i (by simp [affineOpenObject, Vsite, i])

/-- Let `j : V ⟶ U` be an open immersion and `p` a field-valued point of `U` whose underlying
point of the scheme `U` lies in the image of `j`. Then the class of `p` is the image of the class
of a field-valued point of `V`. -/
theorem fieldPoint_factors_through_open
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (j : V ⟶ U)
    [IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)]
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U))
    (hp : AlgebraicGeometry.Space.schemePoint B S hS U p ∈
      Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j)) :
    ∃ q : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj V),
      AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj V) (yoneda.map j)
        (q.class B S hS (yoneda.obj V)) = p.class B S hS (yoneda.obj U) := by
  classical
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let A := AlgebraicGeometry.Space.FieldValuedPoint.siteObject B S hS (yoneda.obj U) p
  let : Field p.carrier := p.field
  have hrange : Set.range (G.map p.value) ⊆ Set.range (G.map j) := by
    rintro x ⟨z, rfl⟩
    obtain rfl : z = IsLocalRing.closedPoint p.carrier :=
      (inferInstance : Subsingleton (PrimeSpectrum p.carrier)).elim _ _
    simpa [AlgebraicGeometry.Space.schemePoint, G] using hp
  let ψ : Spec (.of p.carrier) ⟶ G.obj V :=
    IsOpenImmersion.lift (G.map j) (G.map p.value) hrange
  have hψ : ψ ≫ G.map j = G.map p.value :=
    IsOpenImmersion.lift_fac _ _ _
  let k : A.left ⟶ V.left :=
    B.inclusion.preimage
      (show B.inclusion.obj A.left ⟶ B.inclusion.obj V.left from ψ)
  have hk : B.inclusion.map k = ψ := B.inclusion.map_preimage _
  let g : A ⟶ V := Over.homMk k (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp]
    have hj : G.map j ≫ B.inclusion.map U.hom = B.inclusion.map V.hom := by
      change B.inclusion.map j.left ≫ B.inclusion.map U.hom = B.inclusion.map V.hom
      rw [← B.inclusion.map_comp, j.w]
    have hpv : G.map p.value ≫ B.inclusion.map U.hom = B.inclusion.map A.hom := by
      change B.inclusion.map p.value.left ≫ B.inclusion.map U.hom = B.inclusion.map A.hom
      rw [← B.inclusion.map_comp, p.value.w]
      rfl
    rw [hk, ← hj, ← Category.assoc, hψ]
    exact hpv)
  have hg : g ≫ j = p.value := by
    apply Over.OverMorphism.ext
    change k ≫ j.left = p.value.left
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, hk]
  let q : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj V) :=
    ⟨p.carrier, p.contained, p.toBase, g⟩
  refine ⟨q, ?_⟩
  rw [AlgebraicGeometry.Space.pointsMap_class]
  have hmap : AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj V)
      (yoneda.map j) q = p := by
    cases p
    simp [q, AlgebraicGeometry.Space.FieldValuedPoint.map, hg]
  exact congrArg (AlgebraicGeometry.Space.FieldValuedPoint.class B S hS (yoneda.obj U)) hmap

private theorem presheaf_property_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.RespectsIso]
    {U V : AlgebraicGeometry.BigFppfOver B S hS} (f : U ⟶ V)
    (hf : P ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f)) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (yoneda.map f) := by
  let : HasPullbacks B.Schemes := inferInstance
  let := bigFppf_preservesPullbacks B
  let Q := P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : Q.IsStableUnderBaseChange := ⟨fun h hg =>
    MorphismProperty.of_isPullback (P := P)
      (h.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hg⟩
  exact (MorphismProperty.relative_map_iff (F := yoneda) (P := Q)).mpr hf

private theorem exists_affineOpen_of_isRepresentable
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) [F.IsRepresentable]
    (x : AlgebraicGeometry.Space.points B S hS F) :
    ∃ (U : AlgebraicGeometry.BigFppfOver B S hS) (i : yoneda.obj U ⟶ F),
      IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) ∧
      AlgebraicGeometry.Space.IsOpenImmersion B S hS i ∧
      x ∈ Set.range (AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj U) i) := by
  obtain ⟨y, hy⟩ :=
    AlgebraicGeometry.Space.pointsMap_surjective_of_isIso B S hS F.reprW.hom x
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  let X := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj F.reprX
  let z := AlgebraicGeometry.Space.schemePoint B S hS F.reprX p
  have hz : z ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  let j := affineOpenInclusion B S hS F.reprX U
  let A := affineOpenObject B S hS F.reprX U
  have : IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) :=
    inferInstanceAs (IsOpenImmersion U.val.ι)
  have hzj : z ∈ Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j) := by
    change z ∈ Set.range U.val.ι
    rwa [Scheme.Opens.range_ι]
  obtain ⟨r, hr⟩ := fieldPoint_factors_through_open B S hS j p hzj
  refine ⟨A, yoneda.map j ≫ F.reprW.hom, U.property, ?_, ?_⟩
  · let P := (MorphismProperty.inverseImage (@IsOpenImmersion.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
    let : P.RespectsIso := inferInstance
    exact MorphismProperty.RespectsIso.postcomp P F.reprW.hom _
      (presheaf_property_yoneda B S hS _ j inferInstance)
  · refine ⟨r.class B S hS _, ?_⟩
    rwa [← pointsMap_comp, hr]

private theorem presheaf_property_prod_fst
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.RespectsIso]
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : AlgebraicGeometry.BigFppfOver B S hS) (hT : P (B.inclusion.map T.hom)) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
      (prod.fst : F ⨯ yoneda.obj T ⟶ F) := by
  let Z : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let p : T ⟶ Z := Over.homMk T.hom (by simp [Z])
  have ht : IsTerminal (yoneda.obj Z) := IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  have hp := presheaf_property_yoneda B S hS P p hT
  have he : yoneda.map p = ht.from (yoneda.obj T) := ht.hom_ext _ _
  rw [he] at hp
  let Q := P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  exact MorphismProperty.of_isPullback
    (IsPullback.of_is_product (prodIsProd F (yoneda.obj T)) ht).flip hp

private theorem isFiniteLocallyFree_field_baseChange_projection
    (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (hL : B.Contains (Spec (.of L)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) :
    let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk :=
      Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
        B.obj hL ⟶ B.obj hk)
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (prod.fst : F ⨯ yoneda.obj T ⟶ F) := by
  intro T
  have hfin := presheaf_property_prod_fst B (Spec (.of k)) hk (@IsFinite.{u}) F T
    ((IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance))
  have hflat := presheaf_property_prod_fst B (Spec (.of k)) hk (@Flat.{u}) F T
    (inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
  have hlfp := presheaf_property_prod_fst B (Spec (.of k)) hk
    (@LocallyOfFinitePresentation.{u}) F T
    ((LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance)))
  exact ⟨hfin.1, fun U V g p q hpb =>
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨hfin.property g p q hpb, hflat.property g p q hpb, hlfp.property g p q hpb⟩⟩

private theorem isSurjective_field_baseChange_projection
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (hL : B.Contains (Spec (.of L)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F) :
    let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk :=
      Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
        B.obj hL ⟶ B.obj hk)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf
      (prod.fst : F ⨯ yoneda.obj T ⟶ F) ∧
    AlgebraicGeometry.Space.IsSurjective B (Spec (.of k)) hk
      (prod.fst : F ⨯ yoneda.obj T ⟶ F) := by
  intro T
  have hsur : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  have h := presheaf_property_prod_fst B (Spec (.of k)) hk (@Surjective.{u}) F T hsur
  exact ⟨h, (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective B (Spec (.of k)) hk
    (isAlgebraicSpace_prod_yoneda B (Spec (.of k)) hk F hF T) hF _ h.1).mp h⟩

private theorem isPullback_prod_lift_of_isPullback {C : Type v} [Category.{w} C]
    {W P T Z F : C} [HasBinaryProduct F T] {a : W ⟶ P} {b : W ⟶ T} {a₀ : P ⟶ Z} {b₀ : T ⟶ Z}
    (hab : IsPullback a b a₀ b₀) (hZ : IsTerminal Z) (f : P ⟶ F) :
    IsPullback a (prod.lift (a ≫ f) b) f prod.fst := by
  apply IsPullback.mk'
  · simp
  · intro V c d hc hd
    apply hab.hom_ext
    · exact hc
    · simpa using congrArg (fun v => v ≫ prod.snd) hd
  · intro V c d h
    let e := hab.lift c (d ≫ prod.snd) (hZ.hom_ext _ _)
    refine ⟨e, hab.lift_fst _ _ _, ?_⟩
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, IsPullback.lift_fst_assoc, e]
      exact h
    · simp [e]

private theorem pointsMap_class_siteObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value)
      (AlgebraicGeometry.Space.FieldValuedPoint.class B S hS (yoneda.obj p.siteObject)
        { carrier := p.carrier, contained := p.contained, toBase := p.toBase, value := 𝟙 _ }) =
      p.class B S hS F := by
  rw [AlgebraicGeometry.Space.pointsMap_class]
  congr 1
  cases p
  simp only [AlgebraicGeometry.Space.FieldValuedPoint.map]
  congr 1
  exact F.map_id_apply _ _

private theorem subsingleton_preimage_pointsMap_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W Z X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    [Subsingleton (AlgebraicGeometry.Space.points B S hS W)]
    {a : W ⟶ Z} {b : W ⟶ X} {c : Z ⟶ Y} {e : X ⟶ Y} (sq : IsPullback a b c e)
    (z : AlgebraicGeometry.Space.points B S hS Z) :
    Set.Subsingleton (AlgebraicGeometry.Space.pointsMap B S hS X e ⁻¹'
      {AlgebraicGeometry.Space.pointsMap B S hS Z c z}) := by
  let W' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Z' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let X' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
  have sq' : IsPullback (ObjectProperty.homMk a : W' ⟶ Z') (ObjectProperty.homMk b : W' ⟶ X')
      (ObjectProperty.homMk c : Z' ⟶ Y') (ObjectProperty.homMk e : X' ⟶ Y') :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq
  intro x hx y hy
  obtain ⟨wx, _, hwx⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS sq' z x hx.symm
  obtain ⟨wy, _, hwy⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS sq' z y hy.symm
  rw [← hwx, ← hwy, Subsingleton.elim wx wy]

private theorem subsingleton_fiber_field_baseChange
    (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (hL : B.Contains (Spec (.of L)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B (Spec (.of k)) hk F)
    [Algebra k p.carrier] [FiniteDimensional k p.carrier]
    (hp : Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) = p.toBase)
    (hfield : IsField (TensorProduct k p.carrier L)) :
    let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk :=
      Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
        B.obj hL ⟶ B.obj hk)
    Set.Subsingleton (AlgebraicGeometry.Space.pointsMap B (Spec (.of k)) hk
      (F ⨯ yoneda.obj T) prod.fst ⁻¹' {p.class B (Spec (.of k)) hk F}) := by
  classical
  intro T
  let : HasPullbacks B.Schemes := inferInstance
  let R := TensorProduct k p.carrier L
  let : Field R := hfield.toField
  have hR : B.Contains (Spec (.of R)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k R hk
  let Q : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k R))) :
      B.obj hR ⟶ B.obj hk)
  let a : Q ⟶ p.siteObject :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap p.carrier R)))) (by
        apply ObjectProperty.hom_ext
        change Spec.map (CommRingCat.ofHom (algebraMap p.carrier R)) ≫ p.toBase = _
        rw [← hp, ← Spec.map_comp]
        congr 1)
  let b : Q ⟶ T := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : L →+* R))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp)
  let Z : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk := Over.mk (𝟙 (B.obj hk))
  let a₀ : p.siteObject ⟶ Z := Over.homMk p.siteObject.hom
  let b₀ : T ⟶ Z := Over.homMk T.hom
  have hab : IsPullback a b a₀ b₀ := by
    apply IsPullback.of_map_of_faithful (Over.forget (B.obj hk))
    apply IsPullback.of_map_of_faithful B.inclusion
    change IsPullback (Spec.map (CommRingCat.ofHom (algebraMap p.carrier R)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : L →+* R)))
      p.toBase (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    rw [← hp]
    exact ((CommRingCat.isPushout_tensorProduct k p.carrier L).op.map Scheme.Spec).flip
  have : Subsingleton (AlgebraicGeometry.Space.points B (Spec (.of k)) hk (yoneda.obj Q)) :=
    subsingleton_points_fieldSiteObject B (Spec (.of k)) hk (F := F)
      { carrier := R, contained := hR, toBase := Spec.map (CommRingCat.ofHom (algebraMap k R)),
        value := F.map a.op p.value }
  rw [← pointsMap_class_siteObject B (Spec (.of k)) hk p]
  exact subsingleton_preimage_pointsMap_of_isPullback B (Spec (.of k)) hk
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk _)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk _)
    (isAlgebraicSpace_prod_yoneda B (Spec (.of k)) hk F hF T) hF
    (isPullback_prod_lift_of_isPullback (hab.map yoneda)
      (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal) (yonedaEquiv.symm p.value)) _

/-- Let `k` be a finite field, `K` a purely transcendental extension of `k`, and `A` a finitely
generated `k`-subalgebra of `K`. An algebraic space `F` of finite presentation over `k` whose base
change to `Spec A` is representable is itself representable. -/
theorem isRepresentable_of_fg_baseChange_of_finitePresentation
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [PurelyTranscendental k K] [Finite k]
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (A : Subalgebra k K) (hA : A.FG) (hAspec : B.Contains (Spec (.of A)))
    (F : (AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hF : AlgebraicGeometry.IsAlgebraicSpace B (Spec (.of k)) hk F)
    (f : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hfp : AlgebraicGeometry.Space.IsFinitePresentation B (Spec (.of k)) hk f)
    (hbase : ((OverShriek.relocalizeRestrict
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :
        B.obj hAspec ⟶ B.obj hk)).obj F).IsRepresentable) : F.IsRepresentable := by
  classical
  let hZ := B.contains_terminal
  have hqs := AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    B (Spec (.of k)) hk hZ hF (isAbsolutelyQuasiSeparated_yoneda_terminal k B hk) hfp.2.2
  have hdec := isDecent_of_isQuasiSeparated B (Spec (.of k)) hk hZ F hF hqs
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (Spec (.of k)) hk f hfp.1
  have hJac := jacobson_of_locallyOfFiniteType_overField k B hk F hF f hft
  apply isRepresentable_of_closedPoints_mem_schematicLocus B (Spec (.of k)) hk F hF
    ((AlgebraicGeometry.Space.exists_jacobson_atlas_iff_jacobsonSpace_points B (Spec (.of k)) hk hF
      hdec).mp hJac)
  intro x hx
  obtain ⟨p, hpx, hpf⟩ := exists_finite_fieldRepresentative_of_closedPoint
    k B hk F hF hdec f hft x hx
  let : Algebra k p.carrier := (Spec.preimage p.toBase).hom.toAlgebra
  have : FiniteDimensional k p.carrier := RingHom.finite_algebraMap.mp hpf
  obtain ⟨L, hLf, hLfin, hLa, hLg, hL, hfield, hLrep⟩ :=
    exists_finiteGalois_baseChange_with_isField_tensorProduct k K p.carrier B hk A hA hAspec F hbase
  let T : AlgebraicGeometry.BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k L))) :
      B.obj hL ⟶ B.obj hk)
  let H := F ⨯ yoneda.obj T
  have hH := isAlgebraicSpace_prod_yoneda B (Spec (.of k)) hk F hF T
  let : H.IsRepresentable := isRepresentable_prod_of_relocalizeRestrict T.hom F hLrep
  let X : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨F, hF⟩
  let X' : AlgebraicGeometry.AlgebraicSpaces B (Spec (.of k)) hk := ⟨H, hH⟩
  let π : X' ⟶ X := ObjectProperty.homMk prod.fst
  obtain ⟨hsp, hs⟩ := isSurjective_field_baseChange_projection k L B hk hL F hF
  have hfl := isFiniteLocallyFree_field_baseChange_projection k L B hk hL F
  apply (Space.mem_range_pointsMap_schematicLocus_iff_exists_isAffine_isOpenImmersion
    B (Spec (.of k)) hk π hsp hfl x).mpr
  obtain ⟨y, hy⟩ := hs x
  obtain ⟨U, i, hU, hi, hyU⟩ := exists_affineOpen_of_isRepresentable B (Spec (.of k)) hk H y
  refine ⟨U, i, hU, hi, fun z hz => ?_⟩
  have hfiber := subsingleton_fiber_field_baseChange k L B hk hL F hF p
    (Spec.map_preimage p.toBase) hfield
  have hzy : z = y := hfiber
    (hz.trans hpx.symm) (hy.trans hpx.symm)
  rwa [hzy]

end PurelyTranscendentalDescent

end AlgebraicGeometry

end
