module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# Open subobjects and elementary distinguished squares

Auxiliary material for the induction principle on quasi-compact quasi-separated algebraic
spaces, `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple`: the preimage of a
subfunctor along a fibre product, the elementary distinguished square attached to a reduced
closed complement, the open subspace attached to an open subscheme of a site object, the square
formed by the union of two open subspaces, and the open subobjects of a representable
presheaf cut out by open subschemes, with their quasi-compactness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The second projection of the fibre product of a subfunctor inclusion along a morphism
lands in the preimage subfunctor. -/
private theorem subfunctorPreimagePullback_range_le
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type u}
    (U : Subfunctor F) (f : G ⟶ F) :
    Subfunctor.range (pullback.snd U.ι f) ≤ U.preimage f := by
  rintro T x ⟨y, rfl⟩
  change f.app T ((pullback.snd U.ι f).app T y) ∈ U.obj T
  have heq : U.ι.app T ((pullback.fst U.ι f).app T y) =
      f.app T ((pullback.snd U.ι f).app T y) :=
    congrArg (fun k => k.app T y) (pullback.condition (f := U.ι) (g := f))
  rw [← heq]
  exact ((pullback.fst U.ι f).app T y).property

/-- The canonical morphism from the fibre product of a subfunctor inclusion along a morphism
to the preimage subfunctor. -/
private noncomputable def subfunctorPreimagePullbackMap
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type u}
    (U : Subfunctor F) (f : G ⟶ F) :
    pullback U.ι f ⟶ (U.preimage f).toFunctor :=
  Subfunctor.lift (pullback.snd U.ι f) (subfunctorPreimagePullback_range_le U f)

/-- That canonical morphism, followed by the inclusion of the preimage, is the second
projection. -/
private theorem subfunctorPreimagePullbackMap_ι
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type u}
    (U : Subfunctor F) (f : G ⟶ F) :
    subfunctorPreimagePullbackMap U f ≫ (U.preimage f).ι =
      pullback.snd U.ι f :=
  Subfunctor.lift_ι _ _

/-- The fibre product of a subfunctor inclusion along a morphism is the preimage subfunctor. -/
private noncomputable def subfunctorPreimagePullbackIso
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type u}
    (U : Subfunctor F) (f : G ⟶ F) :
    pullback U.ι f ≅ (U.preimage f).toFunctor := by
  let P := pullback U.ι f
  let Q := U.preimage f
  let h : P ⟶ Q.toFunctor := subfunctorPreimagePullbackMap U f
  have hcomm : U.fromPreimage f ≫ U.ι = Q.ι ≫ f := by
    rw [Subfunctor.fromPreimage_ι]
  let k : Q.toFunctor ⟶ P := pullback.lift (U.fromPreimage f) Q.ι hcomm
  have hh : h ≫ Q.ι = pullback.snd U.ι f :=
    subfunctorPreimagePullbackMap_ι U f
  have hk : k ≫ pullback.snd U.ι f = Q.ι :=
    pullback.lift_snd (U.fromPreimage f) Q.ι hcomm
  refine ⟨h, k, ?_, ?_⟩
  · apply pullback.hom_ext
    · apply (cancel_mono U.ι).1
      calc
        h ≫ k ≫ pullback.fst U.ι f ≫ U.ι = h ≫ U.fromPreimage f ≫ U.ι := by
          simp only [k, pullback.lift_fst_assoc]
        _ = h ≫ Q.ι ≫ f := by rw [Subfunctor.fromPreimage_ι]
        _ = pullback.snd U.ι f ≫ f := by rw [← Category.assoc, hh]
        _ = pullback.fst U.ι f ≫ U.ι := pullback.condition.symm
    · simp only [Category.assoc, Category.id_comp, hk, hh]
  · apply (cancel_mono Q.ι).1
    simp only [Category.assoc, Category.id_comp, hh, hk]

/-- The isomorphism with the preimage subfunctor is compatible with the inclusion of the
preimage. -/
private theorem subfunctorPreimagePullbackIso_hom_snd
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type u}
    (U : Subfunctor F) (f : G ⟶ F) :
    (subfunctorPreimagePullbackIso U f).hom ≫ (U.preimage f).ι =
      pullback.snd U.ι f :=
  subfunctorPreimagePullbackMap_ι U f

/-- The complement of the set of points of an open subspace is closed. -/
private theorem isClosed_compl_range_pointsMap_of_isOpenSubspace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U) :
    IsClosed (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ := by
  rw [isClosed_compl_iff, ← openSubspacesOrderIso_apply B S hS F hF ⟨U, hU⟩]
  exact (openSubspacesOrderIso B S hS F hF ⟨U, hU⟩).2

/-- A reduced closed subspace supported on the complement of an open subspace, over which an
étale morphism restricts to an isomorphism, exhibits an elementary distinguished square. -/
theorem elementarySquare_of_reduced_closed_complement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W)
    (hV : IsAlgebraicSpace B S hS V)
    (U : Subfunctor W) (hU : IsOpenSubspace B S hS U)
    (T : Subfunctor W) (hT : IsClosedSubspace B S hS T)
    (hTred : HasEtaleLocalProperty B S hS T.toFunctor
      (fun Y : Scheme.{u} => IsReduced Y))
    (hTsupport : Set.range (pointsMap B S hS T.toFunctor T.ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ)
    (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hpb : IsIso (pullback.fst T.ι f)) :
    IsElementaryDistinguishedSquare B S hS hW U f := by
  have hclosed := isClosed_compl_range_pointsMap_of_isOpenSubspace B S hS hW U hU
  have hDT : T = reducedClosedSubspace B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hclosed :=
    eq_reducedClosedSubspace B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hclosed T hT hTsupport hTred
  have hTpre : IsIso (T.fromPreimage f) := by
    let e : pullback T.ι f ≅ (T.preimage f).toFunctor :=
      subfunctorPreimagePullbackIso T f
    have hcomp : e.hom ≫ T.fromPreimage f = pullback.fst T.ι f := by
      apply (cancel_mono T.ι).1
      calc
        e.hom ≫ T.fromPreimage f ≫ T.ι = e.hom ≫ (T.preimage f).ι ≫ f := by
          rw [Subfunctor.fromPreimage_ι]
        _ = pullback.snd T.ι f ≫ f := by
          rw [← Category.assoc, subfunctorPreimagePullbackIso_hom_snd]
        _ = pullback.fst T.ι f ≫ T.ι := pullback.condition.symm
    have : IsIso (e.hom ≫ T.fromPreimage f) := by rwa [hcomp]
    exact IsIso.of_isIso_comp_left e.hom (T.fromPreimage f)
  subst hDT
  exact ⟨hV, hU, hf, hclosed, hTpre⟩

/-- The inclusion of an open of an object of the site into that object. -/
noncomputable def siteOpenObjectInclusion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    siteOpenObject B S hS T W ⟶ T := by
  let Vbase : B.Schemes := ⟨(↑W : Scheme),
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ W) T.left.2⟩
  let fscheme : B.inclusion.obj Vbase ⟶ B.inclusion.obj T.left := W.ι
  let fbase : Vbase ⟶ T.left := B.inclusion.preimage fscheme
  exact Over.homMk fbase

/-- The underlying morphism of schemes of that inclusion is the open immersion of the open. -/
private theorem siteOpenObjectInclusion_map (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    (BigFppfOver.toScheme B S hS).map
      (siteOpenObjectInclusion B S hS T W) = W.ι := by
  dsimp [siteOpenObjectInclusion, siteOpenObject]
  exact B.inclusion.map_preimage _

/-- A morphism of the site whose image lies in an open factors through that open. -/
private theorem siteOpenObject_factor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A T : BigFppfOver B S hS) (f : A ⟶ T)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hRange : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ W) :
    ∃ f' : A ⟶ siteOpenObject B S hS T W,
      f' ≫ siteOpenObjectInclusion B S hS T W = f := by
  let q := BigFppfOver.toScheme B S hS
  have hRange' : Set.range (q.map f) ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  let l : q.obj A ⟶ W.toScheme := IsOpenImmersion.lift W.ι (q.map f) hRange'
  let fl : A.left ⟶ (siteOpenObject B S hS T W).left := B.inclusion.preimage l
  have hfl : fl ≫ (siteOpenObjectInclusion B S hS T W).left = f.left := by
    apply B.inclusion.map_injective
    change B.inclusion.map fl ≫ q.map (siteOpenObjectInclusion B S hS T W) = q.map f
    rw [show B.inclusion.map fl = l from
      B.inclusion.map_preimage (X := A.left) (Y := (siteOpenObject B S hS T W).left) l,
      siteOpenObjectInclusion_map]
    exact IsOpenImmersion.lift_fac W.ι (q.map f) hRange'
  refine ⟨Over.homMk fl ?_, Over.OverMorphism.ext hfl⟩
  change fl ≫ (siteOpenObjectInclusion B S hS T W).left ≫ T.hom = A.hom
  rw [← Category.assoc, hfl, f.w]

/-- Two open subspaces of an algebraic space with the same set of points are equal. -/
theorem openSubspace_eq_of_pointsMap_range_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (U V : Subfunctor F)
    (hU : IsOpenSubspace B S hS U)
    (hV : IsOpenSubspace B S hS V)
    (h : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      Set.range (pointsMap B S hS V.toFunctor V.ι)) : U = V := by
  have hEq :
      openSubspacesOrderIso B S hS F hF ⟨U, hU⟩ =
    openSubspacesOrderIso B S hS F hF ⟨V, hV⟩ := by
    apply SetLike.ext
    intro x
    change x ∈ (openSubspacesOrderIso B S hS F hF
      ⟨U, hU⟩).1 ↔
      x ∈ (openSubspacesOrderIso B S hS F hF
        ⟨V, hV⟩).1
    rw [openSubspacesOrderIso_apply, openSubspacesOrderIso_apply]
    exact Set.ext_iff.mp h x
  exact congrArg Subtype.val ((openSubspacesOrderIso B S hS F hF).injective hEq)

/-- An étale morphism to `X` from an algebraic space, as an object of the spaces-étale site
of `X`. -/
def siteObjectOfEtaleMap (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (g : F ⟶ X.1) (hg : IsEtale B S hS g) :
    SpacesEtale B S hS X := by
  let Fobj : AlgebraicSpaces B S hS := ⟨F, hF⟩
  exact ⟨Over.mk (ObjectProperty.homMk g : Fobj ⟶ X), hg⟩

/-- An open immersion of algebraic spaces is étale. -/
theorem etale_of_openImmersion (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : IsOpenImmersion B S hS f) :
    IsEtale B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  let Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T
  have hQP : Q ≤ P := by
    intro A A' g (_ : AlgebraicGeometry.IsOpenImmersion (T.map g))
    exact (inferInstance : Etale (T.map g))
  have hfe : P.presheaf f := MorphismProperty.relative_monotone hQP _ hf
  have : P.IsStableUnderComposition := ⟨by
    intro A A' A'' g₁ g₂ (_ : Etale (T.map g₁)) (_ : Etale (T.map g₂))
    change Etale (T.map (g₁ ≫ g₂))
    rw [Functor.map_comp]
    infer_instance⟩
  intro U φ hφ
  exact MorphismProperty.IsStableUnderComposition.comp_mem φ f hφ hfe

/-- An open subspace together with the identity morphism is an elementary distinguished
square. -/
private theorem open_identity_isElementaryDistinguishedSquare
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U) :
    IsElementaryDistinguishedSquare B S hS hF U (𝟙 F) := by
  have hclosed := isClosed_compl_range_pointsMap_of_isOpenSubspace B S hS hF U hU
  refine ⟨hF, hU, ?_, hclosed, ?_⟩
  · exact etale_of_openImmersion B S hS (𝟙 F) (by
      change (MorphismProperty.presheaf
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) (𝟙 F)
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda (𝟙 F), ?_⟩
      intro A A' g f f' hpb
      have : IsIso (yoneda.map f') := hpb.isIso_snd_of_isIso
      have : IsIso f' := Yoneda.fullyFaithful.isIso_of_isIso_map f'
      change AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map f')
      infer_instance)
  · let D := reducedClosedSubspace B S hS F hF
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hclosed
    have (T : BigFppfOver B S hS) : IsIso ((D.fromPreimage (𝟙 F)).app (Opposite.op T)) :=
      (isIso_iff_bijective _).2 ⟨fun x y hxy => Subtype.ext (congrArg Subtype.val hxy),
        fun y => ⟨⟨y.val, by simpa using y.property⟩, Subtype.ext rfl⟩⟩
    exact NatIso.isIso_of_isIso_app (D.fromPreimage (𝟙 F))

/-- An open subspace together with the identity morphism is an elementary distinguished
square. -/
alias isElementaryDistinguishedSquare_id_of_isOpenSubspace :=
  open_identity_isElementaryDistinguishedSquare

/-- Two open subspaces lie in an open subspace whose set of points is their union, inside
which the first sits in an elementary distinguished square with the second. -/
theorem open_union_square
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (U V : Subfunctor F)
    (hU : IsOpenSubspace B S hS U)
    (hV : IsOpenSubspace B S hS V) :
    ∃ (W : Subfunctor F) (hW : IsOpenSubspace B S hS W)
      (hUW : U ≤ W) (f : V.toFunctor ⟶ W.toFunctor),
      Set.range (pointsMap B S hS W.toFunctor W.ι) =
        Set.range (pointsMap B S hS U.toFunctor U.ι) ∪
          Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      f ≫ W.ι = V.ι ∧
      IsElementaryDistinguishedSquare B S hS hW.1
        (Subfunctor.range (Subfunctor.homOfLe hUW)) f :=
  isElementaryDistinguishedSquare_openRestriction
    B S hS hF U (𝟙 F) (open_identity_isElementaryDistinguishedSquare B S hS hF U hU)
    V hV U hU le_rfl

/-- The subfunctor of a represented presheaf cut out by an open of the representing scheme. -/
noncomputable def representableOpenSubobject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Subfunctor (yoneda.obj T) :=
  Subfunctor.range (yoneda.map (siteOpenObjectInclusion B S hS T W))

/-- The Yoneda image of the inclusion of an open is an open immersion of algebraic spaces. -/
theorem siteOpenObjectInclusion_isOpenImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    IsOpenImmersion B S hS
      (yoneda.map (siteOpenObjectInclusion B S hS T W)) := by
  let q := BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) q
  let : Q.IsStableUnderBaseChange := ⟨by
    intro A A' A'' X' f g f' g' hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsOpenImmersion.{u}) (hs.map q) hg⟩
  change Q.relative yoneda (yoneda.map (siteOpenObjectInclusion B S hS T W))
  rw [MorphismProperty.relative_map_iff (F := yoneda) (P := Q)]
  change AlgebraicGeometry.IsOpenImmersion (q.map (siteOpenObjectInclusion B S hS T W))
  rw [siteOpenObjectInclusion_map]
  infer_instance

/-- The Yoneda image of a morphism of the site is a monomorphism as soon as it is an open
immersion of algebraic spaces. -/
theorem mono_yoneda_map_of_isOpenImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A T : BigFppfOver B S hS} (f : A ⟶ T)
    (hf : IsOpenImmersion B S hS (yoneda.map f)) :
    Mono (yoneda.map f) := by
  have hQmono :
      MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS) ≤
        MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
    intro A A' g (_ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g))
    constructor
    intro A₀ f₁ f₂ hcomp
    apply (BigFppfOver.toScheme B S hS).map_injective
    apply (cancel_mono
      ((BigFppfOver.toScheme B S hS).map g)).1
    simpa only [Functor.map_comp] using
      congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) hcomp
  exact MorphismProperty.presheaf_mono_of_le hQmono hf

/-- The presheaf represented by an open of an object of the site is the subfunctor that open
cuts out. -/
noncomputable def representableOpenSubobjectIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    yoneda.obj (siteOpenObject B S hS T W) ≅
      (representableOpenSubobject B S hS T W).toFunctor := by
  let j := siteOpenObjectInclusion B S hS T W
  let f := yoneda.map j
  let R : Subfunctor (yoneda.obj T) := Subfunctor.range f
  have hf : IsOpenImmersion B S hS f :=
    siteOpenObjectInclusion_isOpenImmersion B S hS T W
  have hmono : Mono f :=
    mono_yoneda_map_of_isOpenImmersion B S hS j hf
  letI : Mono f := hmono
  let e : yoneda.obj (siteOpenObject B S hS T W) ≅ R.toFunctor :=
    asIso (Subfunctor.toRange f)
  exact e

/-- The subfunctor cut out by an open of the representing scheme is an open subspace. -/
theorem representableOpenSubobject_isOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    IsOpenSubspace B S hS (representableOpenSubobject B S hS T W) := by
  let j := siteOpenObjectInclusion B S hS T W
  let f := yoneda.map j
  let R : Subfunctor (yoneda.obj T) := Subfunctor.range f
  have hf : IsOpenImmersion B S hS f :=
    siteOpenObjectInclusion_isOpenImmersion B S hS T W
  have : Mono f := mono_yoneda_map_of_isOpenImmersion B S hS j hf
  let e : yoneda.obj (siteOpenObject B S hS T W) ≅ R.toFunctor := asIso (Subfunctor.toRange f)
  have hRalg : IsAlgebraicSpace B S hS R.toFunctor :=
    IsAlgebraicSpace.of_iso (isAlgebraicSpace_yoneda B S hS (siteOpenObject B S hS T W)) e
  have he : Arrow.mk f ≅ Arrow.mk R.ι :=
    Arrow.isoMk e (Iso.refl _) (by
      simp [e, R, Subfunctor.toRange_ι])
  have hRopen : IsOpenImmersion B S hS R.ι :=
    (MorphismProperty.arrow_iso_iff
    (MorphismProperty.presheaf
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) he).mp hf
  exact ⟨hRalg, hRopen⟩

/-- A morphism of the site lies in the subfunctor cut out by an open exactly when the image of
its underlying morphism of schemes is contained in that open. -/
theorem mem_representableOpenSubobject_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T A : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (f : A ⟶ T) :
    f ∈ (representableOpenSubobject B S hS T W).obj (Opposite.op A) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ W := by
  change (∃ g, g ≫ siteOpenObjectInclusion B S hS T W = f) ↔ _
  refine ⟨?_, siteOpenObject_factor B S hS A T f W⟩
  rintro ⟨g, rfl⟩
  rw [Functor.map_comp, siteOpenObjectInclusion_map]
  rintro x ⟨y, rfl⟩
  exact ((BigFppfOver.toScheme B S hS).map g y).property

/-- The subfunctor cut out by an open is monotone in the open. -/
private theorem representableOpenSubobject_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    {U V : ((BigFppfOver.toScheme B S hS).obj T).Opens} (h : U ≤ V) :
    representableOpenSubobject B S hS T U ≤ representableOpenSubobject B S hS T V := by
  intro A f hf
  rw [mem_representableOpenSubobject_iff] at hf ⊢
  exact hf.trans h

/-- The set of points of a subfunctor is monotone in the subfunctor. -/
theorem pointsRange_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : Subfunctor F} (h : U ≤ V) :
    Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
      Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  rintro x ⟨y, rfl⟩
  refine ⟨pointsMap B S hS U.toFunctor (Subfunctor.homOfLe h) y, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS V.toFunctor V.ι),
    ← pointsMap_comp, Subfunctor.homOfLe_ι]

/-- The subfunctor cut out by a union of two opens has the union of their sets of points. -/
theorem representableOpenSubobject_sup_pointsRange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (U V : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Set.range (pointsMap B S hS
      (representableOpenSubobject B S hS T (U ⊔ V)).toFunctor
      (representableOpenSubobject B S hS T (U ⊔ V)).ι) =
    Set.range (pointsMap B S hS
      (representableOpenSubobject B S hS T U).toFunctor
      (representableOpenSubobject B S hS T U).ι) ∪
    Set.range (pointsMap B S hS
      (representableOpenSubobject B S hS T V).toFunctor
      (representableOpenSubobject B S hS T V).ι) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    induction y using Quot.inductionOn with | h p =>
      let q := BigFppfOver.toScheme B S hS
      have hp := (mem_representableOpenSubobject_iff B S hS T p.siteObject
        (U ⊔ V) p.value.val).mp p.value.property
      have hpt := hp ⟨IsLocalRing.closedPoint p.carrier, rfl⟩
      have liftPoint (A : ((BigFppfOver.toScheme B S hS).obj T).Opens)
          (hA : q.map p.value.val (IsLocalRing.closedPoint p.carrier) ∈ A) :
          pointsMap B S hS _
            (representableOpenSubobject B S hS T (U ⊔ V)).ι p.class ∈
          Set.range (pointsMap B S hS
            (representableOpenSubobject B S hS T A).toFunctor
            (representableOpenSubobject B S hS T A).ι) := by
        have hmem : p.value.val ∈ (representableOpenSubobject B S hS T A).obj
            (Opposite.op p.siteObject) := by
          rw [mem_representableOpenSubobject_iff]
          rintro z ⟨t, rfl⟩
          have ht : t = IsLocalRing.closedPoint p.carrier :=
            (inferInstance : Subsingleton (PrimeSpectrum p.carrier)).elim _ _
          rw [ht]
          exact hA
        let p' : FieldValuedPoint B S hS
            (representableOpenSubobject B S hS T A).toFunctor :=
          { carrier := p.carrier, contained := p.contained, toBase := p.toBase,
            value := ⟨p.value.val, hmem⟩ }
        exact ⟨p'.class, rfl⟩
      exact hpt.imp (liftPoint U) (liftPoint V)
  · exact Set.union_subset
      (pointsRange_mono B S hS (representableOpenSubobject_mono B S hS T le_sup_left))
      (pointsRange_mono B S hS (representableOpenSubobject_mono B S hS T le_sup_right))

/-- An object of the site whose represented presheaf is quasi-compact has quasi-compact
underlying scheme. -/
theorem compactSpace_of_isQuasiCompactSpace_yonedaObj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (hT : IsQuasiCompactSpace B S hS (yoneda.obj T)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := by
  rcases hT with ⟨U, p, hcompact, hsurj, hetale⟩
  let q := BigFppfOver.toScheme B S hS
  let m : U ⟶ T := yoneda.preimage p
  have hpm : yoneda.map m = p := yoneda.map_preimage p
  have hm : Surjective (q.map m) :=
    hsurj.property (𝟙 (yoneda.obj T)) (𝟙 (yoneda.obj U)) m (by
      simpa [hpm] using (IsPullback.of_id_fst : IsPullback (𝟙 (yoneda.obj U))
        (yoneda.map m) (yoneda.map m) (𝟙 (yoneda.obj T))))
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr hm.surj, ← Set.image_univ]
  exact isCompact_univ.image (by fun_prop : Continuous (q.map m).base)

/-- The presheaf represented by an object of the site with quasi-compact underlying scheme is
quasi-compact. -/
alias isQuasiCompactSpace_yonedaObj_of_compactSpace := isQuasiCompact_yoneda_of_compact

/-- The subfunctor cut out by an open with quasi-compact underlying scheme is quasi-compact. -/
theorem representableOpenSubobject_isQuasiCompact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hW : CompactSpace W.toScheme) :
    IsQuasiCompactSpace B S hS
      (representableOpenSubobject B S hS T W).toFunctor :=
  IsQuasiCompactSpace.of_iso B S hS
    (isQuasiCompactSpace_yonedaObj_of_compactSpace B S hS (siteOpenObject B S hS T W) hW)
    (representableOpenSubobjectIso B S hS T W)

/-- An open of an étale object of the site over `X`, as an object of the spaces-étale site
of `X`. -/
noncomputable def openEtaleObject (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ X.1) (hg : IsEtale B S hS g)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    SpacesEtale B S hS X := by
  let j := siteOpenObjectInclusion B S hS T W
  let F := yoneda.obj (siteOpenObject B S hS T W)
  have hj : IsOpenImmersion B S hS (yoneda.map j) :=
    siteOpenObjectInclusion_isOpenImmersion B S hS T W
  exact siteObjectOfEtaleMap B S hS X F
    (isAlgebraicSpace_yoneda B S hS (siteOpenObject B S hS T W))
    (yoneda.map j ≫ g)
    (isEtale_comp B S hS
      (etale_of_openImmersion B S hS (yoneda.map j) hj) hg)

end AlgebraicGeometry.Space

end
