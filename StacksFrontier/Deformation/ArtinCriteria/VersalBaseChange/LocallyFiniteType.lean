module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.InducedProperty
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonalEquiv
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSliceProduct
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation
public import StacksFrontier.Deformation.ArtinCriteria.Versality
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.DeformationLifting
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.ResidueFieldPoints
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.DeformationLifting

/-!
# Local finiteness of a base change of a versal object

Preparations for `Deformation.Artin.BaseChange.isSmoothAt_baseChange_of_isVersalAt`:
field-valued points of the projection from the two-fibre product, local finiteness of type of
the two-fibre product, and the identification of the big fppf site over `V ×_S U` with a
product over the big fppf site of `S`.

## References

* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin.BaseChange

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

-- The slice functor `Over.post`, fibres of a functor, their inclusion and formation, the
-- pullback functors of a choice of pullbacks and the slice functor of a 2-Yoneda lift are plain
-- `def`s, so goals mentioning an object of a fibre, or an object of the site read in `Over S`,
-- are not type-correct at `implicit` transparency.  Naming them here is what lets `rw`,
-- `simp only` and instance search see through exactly these and nothing else.
attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.Functor.TwoYoneda.liftBased
  CategoryTheory.Functor.TwoYoneda.liftFunctor
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.id
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.TwoFibreProductOver.snd
  CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc
  CategoryTheory.Pseudofunctor.CoGrothendieck.forget
  AlgebraicGeometry.Space.FieldValuedPoint.map
  AlgebraicGeometry.Space.schemePoint
  CategoryTheory.Bicategory.InducedBicategory

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
    (AlgebraicGeometry.BigFppfOver B S hS))

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

attribute [local instance] predeformationCarrierCategory

attribute [local instance] baseChangeProductCategory

section Projection

-- The structure map of the slice, read as a cocone on the forgetful functor, must be unfolded
-- for the statement of `baseChangeProjection_app` to be type-correct at `implicit`
-- transparency: the codomain of the whiskered transformation is `R ⋙ (Functor.const _).obj U`
-- with `U` spelled as the point of that cocone, and the codomain of the transformation being
-- defined is `(Functor.const _).obj U`.
attribute [local implicit_reducible] CategoryTheory.Over.forgetCocone

@[implicit_reducible] private def baseChangeProjection
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F) :
    (presheafOfCategories (F ⋙ typeToCat)).p ⋙ Over.map V.hom ⟶
      (Functor.const _).obj U := by
  let R := e.inv.functor ⋙ TwoFibreProductOver.snd (Over.map V.hom)
    (Over.forget U) 𝒳.val.p y
    (Functor.TwoYoneda.liftBased 𝒳.val.p
      𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor
  have hR : R ⋙ Over.forget U =
      (presheafOfCategories (F ⋙ typeToCat)).p ⋙ Over.map V.hom := by
    dsimp [R]
    rw [Functor.assoc, TwoFibreProductOver.snd_comp_eq,
      ← TwoFibreProductOver.fst_comp_eq, ← Functor.assoc, e.inv.w]
  exact eqToHom hR.symm ≫ Functor.whiskerLeft R (Over.forgetCocone U).ι

private lemma baseChangeProjection_app
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (a : (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hP : (e.inv.functor.obj a).x = a.base) :
    (baseChangeProjection B S hS 𝒳 U V x hx y F e).app a =
      eqToHom (congrArg (Over.map V.hom).obj hP.symm) ≫
        eqToHom ((e.inv.functor.obj a).hx.trans (e.inv.functor.obj a).hy.symm) ≫
          (e.inv.functor.obj a).y.hom := by
  dsimp only [baseChangeProjection]
  rw [NatTrans.comp_app, eqToHom_app, Functor.whiskerLeft_app]
  simp only [eqToHom_trans_assoc]
  rfl

end Projection

/-- Naturality of a transformation to a constant functor, read on points of the underlying
schemes. -/
private lemma projection_point_naturality
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (η : (presheafOfCategories (F ⋙ typeToCat)).p ⋙ Over.map V.hom ⟶
      (Functor.const _).obj U)
    {X Y : (presheafOfCategories (F ⋙ typeToCat)).obj} (f : X ⟶ Y)
    (z : B.inclusion.obj X.base.left) :
    B.inclusion.map (η.app Y).left (B.inclusion.map f.base.left z) =
      B.inclusion.map (η.app X).left z := by
  have hn := congrArg (fun k => B.inclusion.map k.left) (η.naturality f)
  change B.inclusion.map (f.base.left ≫ (η.app Y).left) =
    B.inclusion.map ((η.app X).left ≫ 𝟙 _) at hn
  simp only [Category.comp_id, Functor.map_comp] at hn
  exact congrArg (fun k => k z) hn

private lemma projection_point_eq_of_dominates
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (η : (presheafOfCategories (F ⋙ typeToCat)).p ⋙ Over.map V.hom ⟶
      (Functor.const _).obj U)
    (p q : AlgebraicGeometry.Space.FieldValuedPoint B V.left.1 V.left.2 F)
    (h : AlgebraicGeometry.Space.FieldValuedPoint.Dominates B V.left.1 V.left.2 F p q) :
    B.inclusion.map (η.app ⟨p.siteObject, Discrete.mk p.value⟩).left
        (IsLocalRing.closedPoint p.carrier) =
      B.inclusion.map (η.app ⟨q.siteObject, Discrete.mk q.value⟩).left
        (IsLocalRing.closedPoint q.carrier) := by
  obtain ⟨g, hg⟩ := h
  have hclosed : B.inclusion.map g.left (IsLocalRing.closedPoint p.carrier) =
      IsLocalRing.closedPoint q.carrier := by
    change (_ : Spec (.of q.carrier)) = _
    exact Subsingleton.elim _ _
  have happ := projection_point_naturality B S hS U V F η
    (X := ⟨p.siteObject, Discrete.mk p.value⟩) (Y := ⟨q.siteObject, Discrete.mk q.value⟩)
    ⟨g, Discrete.eqToHom' hg.symm⟩ (IsLocalRing.closedPoint p.carrier)
  rw [hclosed] at happ
  exact happ.symm


private lemma projection_point_eq_of_commonExtension
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (η : (presheafOfCategories (F ⋙ typeToCat)).p ⋙ Over.map V.hom ⟶
      (Functor.const _).obj U)
    (p q : AlgebraicGeometry.Space.FieldValuedPoint B V.left.1 V.left.2 F)
    (h : AlgebraicGeometry.Space.FieldValuedPoint.HasCommonExtension B V.left.1 V.left.2 F p q) :
    B.inclusion.map (η.app ⟨p.siteObject, Discrete.mk p.value⟩).left
        (IsLocalRing.closedPoint p.carrier) =
      B.inclusion.map (η.app ⟨q.siteObject, Discrete.mk q.value⟩).left
        (IsLocalRing.closedPoint q.carrier) := by
  obtain ⟨r, hrp, hrq⟩ := h
  exact (projection_point_eq_of_dominates B S hS U V F η r p hrp).symm.trans
    (projection_point_eq_of_dominates B S hS U V F η r q hrq)

private lemma projection_point_eq_chartPoint
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (η : (presheafOfCategories (F ⋙ typeToCat)).p ⋙ Over.map V.hom ⟶
      (Functor.const _).obj U)
    (W : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)
    (a : yoneda.obj W ⟶ F)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B V.left.1 V.left.2 (yoneda.obj W)) :
    let q := AlgebraicGeometry.Space.FieldValuedPoint.map B V.left.1 V.left.2 (yoneda.obj W) a p
    B.inclusion.map (η.app ⟨q.siteObject, Discrete.mk q.value⟩).left
        (IsLocalRing.closedPoint q.carrier) =
      B.inclusion.map (η.app ⟨W, Discrete.mk (a.app (Opposite.op W) (𝟙 W))⟩).left
        (B.inclusion.map p.value.left (IsLocalRing.closedPoint p.carrier)) := by
  intro q
  have heq : F.map p.value.op (a.app (Opposite.op W) (𝟙 W)) = q.value := by
    change F.map p.value.op (a.app (Opposite.op W) (𝟙 W)) =
      a.app (Opposite.op p.siteObject) p.value
    have h := congrArg (fun k => k (𝟙 W)) (a.naturality p.value.op)
    simpa [AlgebraicGeometry.Space.FieldValuedPoint.siteObject] using h.symm
  exact (projection_point_naturality B S hS U V F η
    (X := ⟨q.siteObject, Discrete.mk q.value⟩) (Y := ⟨W, Discrete.mk (a.app (Opposite.op W) (𝟙 W))⟩)
    ⟨p.value, Discrete.eqToHom' heq.symm⟩ (IsLocalRing.closedPoint p.carrier)).symm

private lemma baseChangeProjection_point
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B V.left.1 V.left.2 F)
    (hP : (e.inv.functor.obj ⟨p.siteObject, Discrete.mk p.value⟩).x = p.siteObject) :
    let P := e.inv.functor.obj ⟨p.siteObject, Discrete.mk p.value⟩
    B.inclusion.map
      ((baseChangeProjection B S hS 𝒳 U V x hx y F e).app
        ⟨p.siteObject, Discrete.mk p.value⟩).left
        (IsLocalRing.closedPoint p.carrier) =
      (B.inclusion.map ((eqToHom (P.hx.trans P.hy.symm) ≫ P.y.hom).left))
        ((B.inclusion.map (eqToHom (congrArg Over.left hP).symm))
          (IsLocalRing.closedPoint p.carrier)) := by
  dsimp only
  rw [baseChangeProjection_app B S hS 𝒳 U V x hx y F e _ hP]
  simp only [Over.comp_left, Over.eqToHom_left, Functor.map_comp, Scheme.Hom.comp_apply]
  rfl

/-- The inverse of a residue-field identification is the identification of the
reversed equality. -/
private lemma residueFieldCongr_inv {X : Scheme.{u}} {a b : X} (h : a = b) (h' : b = a) :
    (X.residueFieldCongr h).inv = (X.residueFieldCongr h').hom := rfl

/-- At a point inducing an isomorphism of residue fields, the canonical map from
the residue field of the image factors through the point. -/
private theorem specMap_residueIso_inv_comp
    {X Z : Scheme.{u}} (σ : Z ⟶ X) (z : Z)
    {t : X} (hpt : σ z = t) [IsIso (σ.residueFieldMap z)] :
    (Spec.map ((X.residueFieldCongr hpt.symm ≪≫ asIso (σ.residueFieldMap z)).inv) ≫
        Z.fromSpecResidueField z) ≫ σ = X.fromSpecResidueField t := by
  have key : Spec.map (inv (σ.residueFieldMap z)) ≫
      (Z.fromSpecResidueField z ≫ σ) = X.fromSpecResidueField (σ z) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  calc (Spec.map ((X.residueFieldCongr hpt.symm ≪≫ asIso (σ.residueFieldMap z)).inv) ≫
        Z.fromSpecResidueField z) ≫ σ
      = Spec.map (X.residueFieldCongr hpt).hom ≫
          (Spec.map (inv (σ.residueFieldMap z)) ≫ (Z.fromSpecResidueField z ≫ σ)) := by
        rw [Iso.trans_inv, Spec.map_comp, residueFieldCongr_inv _ hpt, asIso_inv]
        simp only [Category.assoc]
    _ = Spec.map (X.residueFieldCongr hpt).hom ≫ X.fromSpecResidueField (σ z) := by rw [key]
    _ = X.fromSpecResidueField t := Scheme.residueFieldCongr_fromSpecResidueField hpt

/-- The residue map of an Artinian local algebra with fixed residue field is
compatible with the morphisms of the category. -/
private lemma residueMap_comp {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {D A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (g : D ⟶ A) :
    (Deformation.Artin.residueMap A).comp g.hom.toRingHom = Deformation.Artin.residueMap D := by
  ext a
  exact g.residue_comm a

/-- Composing a deformation with a further arrow over a morphism of Artinian
local algebras gives a deformation. -/
private lemma deformationObject_arrow_base_comp
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀)
    {D : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (g : D ⟶ b.algebra)
    {pt : X} (arrow : b.point ⟶ pt)
    (base : q.obj pt = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ D)) ≫ iΛ))
    (harrow : eqToHom (congrArg Over.left b.base).symm ≫ (q.map arrow).left ≫
      eqToHom (congrArg Over.left base) =
        Spec.map (CommRingCat.ofHom g.hom.toRingHom)) :
    eqToHom (congrArg Over.left hx₀).symm ≫ (q.map (b.arrow ≫ arrow)).left ≫
        eqToHom (congrArg Over.left base) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap D)) := by
  rw [← residueMap_comp g, CommRingCat.ofHom_comp, Spec.map_comp, ← b.arrow_base,
    ← harrow, q.map_comp]
  simp only [Over.comp_left, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

/-- The field-valued point of a presheaf attached to the residue field of a point
of an étale chart. -/
@[implicit_reducible] private noncomputable def chartFieldPoint
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (W : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)
    (aW : yoneda.obj W ⟶ F) (tW : W.left.1)
    (htW : B.Contains (Spec (W.left.1.residueField tW))) :
    AlgebraicGeometry.Space.FieldValuedPoint B V.left.1 V.left.2 F :=
  AlgebraicGeometry.Space.FieldValuedPoint.map B V.left.1 V.left.2 (yoneda.obj W) aW
    (residueFieldRepresentative B V.left.1 V.left.2 W tW htW)

/-- The second component of the image of a morphism of elements under the chosen
equivalence lies over the base morphism of that morphism of elements. -/
private lemma baseChangeHom_b_forget
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {X₀ X₁ : (presheafOfCategories (F ⋙ typeToCat)).obj} (m : X₀ ⟶ X₁)
    (h₀ : (e.inv.functor.obj X₀).x = X₀.base)
    (h₁ : (e.inv.functor.obj X₁).x = X₁.base) :
    (Over.forget U).map (e.inv.functor.map m).b =
      eqToHom (e.inv.functor.obj X₀).hy ≫ eqToHom (e.inv.functor.obj X₀).hx.symm ≫
        (Over.map V.hom).map (eqToHom h₀ ≫
          (presheafOfCategories (F ⋙ typeToCat)).p.map m ≫ eqToHom h₁.symm) ≫
        eqToHom (e.inv.functor.obj X₁).hx ≫ eqToHom (e.inv.functor.obj X₁).hy.symm := by
  have ha : (e.inv.functor.map m).a = eqToHom h₀ ≫
      (presheafOfCategories (F ⋙ typeToCat)).p.map m ≫ eqToHom h₁.symm := by
    have h := Functor.congr_hom e.inv.w m
    simpa only [Functor.comp_map, TwoFibreProductOver.fst_map] using h
  let := (e.inv.functor.map m).hb
  have hfac : (Over.forget U).map (e.inv.functor.map m).b =
      eqToHom (e.inv.functor.obj X₀).hy ≫ (e.inv.functor.map m).hbase ≫
        eqToHom (e.inv.functor.obj X₁).hy.symm :=
    IsHomLift.fac' (Over.forget U) (e.inv.functor.map m).hbase (e.inv.functor.map m).b
  rw [hfac, (e.inv.functor.map m).hbase_eq, ha]
  simp only [Category.assoc]

/-- The underlying morphism of the second component of the image of a morphism of
elements is the morphism of site objects it lies over. -/
private lemma baseChangeHom_b_left
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {X₀ X₁ : (presheafOfCategories (F ⋙ typeToCat)).obj} (m : X₀ ⟶ X₁)
    (h₀ : (e.inv.functor.obj X₀).x = X₀.base)
    (h₁ : (e.inv.functor.obj X₁).x = X₁.base)
    (k₀ : (e.inv.functor.obj X₀).y.left.left = X₀.base.left)
    (k₁ : X₁.base.left = (e.inv.functor.obj X₁).y.left.left) :
    ((Over.forget U).map (e.inv.functor.map m).b).left =
      eqToHom k₀ ≫ ((presheafOfCategories (F ⋙ typeToCat)).p.map m).left ≫ eqToHom k₁ := by
  have h := congrArg Over.Hom.left
    (baseChangeHom_b_forget B S hS 𝒳 U V x hx y F e m h₀ h₁)
  simp only [Over.comp_left, Over.eqToHom_left, Over.map_map_left, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans] at h
  exact h


/-- The structural map of a presheaf over the big fppf site of `S` is locally of
finite type as soon as every étale chart of it is locally of finite type over `S`. -/
lemma isLocallyOfFiniteType_terminal_of_etaleCharts
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (h : ∀ (W : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj W ⟶ F),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a →
      LocallyOfFiniteType (B.inclusion.map W.hom)) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B S hS
      (terminal.from F : F ⟶ ⊤_ ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := by
  intro W T₀ a _b k ha _hb _hcomm
  have hW : LocallyOfFiniteType (B.inclusion.map W.hom) := h W a ha
  have hw : B.inclusion.map k.left ≫ B.inclusion.map T₀.hom = B.inclusion.map W.hom := by
    rw [← Functor.map_comp]
    exact congrArg B.inclusion.map (Over.w k)
  have : LocallyOfFiniteType (B.inclusion.map k.left ≫ B.inclusion.map T₀.hom) := by
    rw [hw]; exact hW
  exact locallyOfFiniteType_of_comp (B.inclusion.map k.left) (B.inclusion.map T₀.hom)

/-- If the presheaf `F` on the
big fppf site over `V` is the lower-shriek extension along `g : T ⟶ V` of a presheaf `G`
on the big fppf site over `T`, if `G` is locally of finite type over `T`, and if `g` is
locally of finite type, then `F` is locally of finite type over `V`. -/
private lemma isLocallyOfFiniteType_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T V : Scheme.{u})
    (hT : B.Contains T) (hV : B.Contains V) (g : B.obj hT ⟶ B.obj hV)
    (hg : LocallyOfFiniteType (B.inclusion.map g))
    (G : (AlgebraicGeometry.BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (hG : AlgebraicGeometry.Space.IsLocallyOfFiniteType B T hT
      (terminal.from G : G ⟶ ⊤_ ((AlgebraicGeometry.BigFppfOver B T hT)ᵒᵖ ⥤ Type u)))
    (F : (AlgebraicGeometry.BigFppfOver B V hV)ᵒᵖ ⥤ Type u)
    (κ : (OverShriek.relocalizePresheafFunctor g).obj G ≅ F) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B V hV
      (terminal.from F : F ⟶ ⊤_ ((AlgebraicGeometry.BigFppfOver B V hV)ᵒᵖ ⥤ Type u)) := by
  let _ := hg
  have h1 : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B T hT
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.Space.toYonedaId B T hT G) := by
    intro W' V' a b k ha hb _hsq
    exact hG W' V' a (b ≫ (terminalYonedaIso B T hT).hom) k ha
      (MorphismProperty.RespectsIso.postcomp _ (terminalYonedaIso B T hT).hom b hb)
      (terminalIsTerminal.hom_ext _ _)
  have h2 := (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff
    B T V hT hV g
    (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) G).mpr h1
  refine isLocallyOfFiniteType_terminal_of_etaleCharts B V hV F ?_
  intro W a ha
  have ha' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B V hV)).presheaf (a ≫ κ.inv) :=
    MorphismProperty.RespectsIso.postcomp _ κ.inv a ha
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B V hV)).presheaf
      (𝟙 (yoneda.obj (Over.mk g : AlgebraicGeometry.BigFppfOver B V hV))) :=
    schemeProperty_presheaf_id B V hV (@Etale.{u} : MorphismProperty Scheme.{u})
      (fun f hf => by let _ := hf; infer_instance) (Over.mk g)
  obtain ⟨k, hk⟩ : ∃ k : W ⟶ (Over.mk g : AlgebraicGeometry.BigFppfOver B V hV),
      yoneda.map k = (a ≫ κ.inv) ≫ OverShriek.relocalizeToYoneda g G :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hk' : LocallyOfFiniteType (B.inclusion.map k.left) :=
    h2 W (Over.mk g) (a ≫ κ.inv) (𝟙 _) k ha' hb
      ((Category.comp_id (yoneda.map k)).trans hk)
  let _ := hk'
  have hWg : B.inclusion.map W.hom = B.inclusion.map k.left ≫ B.inclusion.map g :=
    (congrArg B.inclusion.map (Over.w k).symm).trans (B.inclusion.map_comp k.left g)
  rw [hWg]
  infer_instance

/-- Local finiteness of type of the two-fibre product, reduced to its identification with an
isomorphism space.  Given the object `T₀ = V ×_S U` with its first projection `g`, the two
objects `a₀`, `b₀` of the fibre of `𝒳` over `T₀`, and the statement that every algebraic space
over `T₀` representing `Isom(a₀, b₀)` has `F` as its lower-shriek extension along `g`, the
two-fibre product is locally of finite type over `V`. -/
private lemma isLocallyOfFiniteType_of_isomSpaceRelocalizes
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hΔlft :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
        (a b : 𝒳.val.p.Fiber T)
        (G : (AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
        AlgebraicGeometry.IsAlgebraicSpace B T.left.1 T.left.2 G →
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
            uliftFunctor.{u, v}) →
        AlgebraicGeometry.Space.IsLocallyOfFiniteType B T.left.1 T.left.2
          (terminal.from G : G ⟶
            ⊤_ ((AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)))
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (T₀ : AlgebraicGeometry.BigFppfOver B S hS)
    (g : B.obj T₀.left.2 ⟶ B.obj V.left.2)
    (hg : LocallyOfFiniteType (B.inclusion.map g))
    (a₀ b₀ :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      𝒳.val.p.Fiber T₀)
    (hIsom :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (G : (AlgebraicGeometry.BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ ⥤ Type u),
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T₀).op ⋙ 𝒳.val.p.isomPresheaf a₀ b₀) ⋙
            uliftFunctor.{u, v}) →
        Nonempty ((OverShriek.relocalizePresheafFunctor g).obj G ≅ F)) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B V.left.1 V.left.2
      (terminal.from F : F ⟶
        ⊤_ ((AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨G, hG, hiso⟩ :=
    (AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf
      B S hS 𝒳).mp hΔ T₀ a₀ b₀
  obtain ⟨κ⟩ := hIsom G hiso
  exact isLocallyOfFiniteType_relocalize B T₀.left.1 V.left.1 T₀.left.2 V.left.2 g hg G
    (hΔlft T₀ a₀ b₀ G hG hiso) F κ

/-! ### `V ×_S U`, its first projection, and the two objects of the fibre of `𝒳` over it -/

/-- `V ×_S U`, as an object of the big fppf site over `S`. -/
@[implicit_reducible] private noncomputable def prodObj
    (U V : AlgebraicGeometry.BigFppfOver B S hS) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (pullback.fst V.hom U.hom ≫ V.hom)

/-- The first projection `V ×_S U ⟶ V`, as a morphism of the big fppf site. -/
@[implicit_reducible] private noncomputable def prodFst
    (U V : AlgebraicGeometry.BigFppfOver B S hS) :
    B.obj (prodObj B S hS U V).left.2 ⟶ B.obj V.left.2 :=
  pullback.fst V.hom U.hom

/-- The second projection `V ×_S U ⟶ U`, as a morphism over `S`. -/
@[implicit_reducible] private noncomputable def prodSnd
    (U V : AlgebraicGeometry.BigFppfOver B S hS) :
    prodObj B S hS U V ⟶ U :=
  Over.homMk (pullback.snd V.hom U.hom) pullback.condition.symm

/-- The first projection of `V ×_S U` is locally of finite type, being a base change of
the structure morphism of `U`. -/
private lemma locallyOfFiniteType_prodFst (U V : AlgebraicGeometry.BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)] :
    LocallyOfFiniteType (B.inclusion.map (prodFst B S hS U V)) := by
  have hpb : IsPullback (B.inclusion.map (pullback.fst V.hom U.hom))
      (B.inclusion.map (pullback.snd V.hom U.hom))
      (B.inclusion.map V.hom) (B.inclusion.map U.hom) :=
    (IsPullback.of_hasPullback V.hom U.hom).map B.inclusion
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip inferInstance

/-- `uliftFunctor.{u, u}` is trivial, so a presheaf of `Type u` is its own universe lift. -/
@[implicit_reducible] private def uliftTrivialIso {C : Type*} [Category C] (H : Cᵒᵖ ⥤ Type u) :
    H ⋙ uliftFunctor.{u, u} ≅ H :=
  Functor.isoWhiskerLeft H uliftFunctorTrivial ≪≫ Functor.rightUnitor H

open TwoFibreProductOver.DiagonalFibre in
/-- Local finiteness of type of the two-fibre product, reduced to a single comparison of
categories: it suffices to exhibit a scheme-valued point `Y` of `𝒳 ×_S 𝒳` with values in
`T₀ = V ×_S U`
whose 2-fibre product with the diagonal of `𝒳`, read over the big fppf site of `V` through
the first projection `T₀ ⟶ V`, is the category of elements of `F`. -/
private lemma isLocallyOfFiniteType_of_point
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hΔlft :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
        (a b : 𝒳.val.p.Fiber T)
        (G : (AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
        AlgebraicGeometry.IsAlgebraicSpace B T.left.1 T.left.2 G →
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
            uliftFunctor.{u, v}) →
        AlgebraicGeometry.Space.IsLocallyOfFiniteType B T.left.1 T.left.2
          (terminal.from G : G ⟶
            ⊤_ ((AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)))
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (Y : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1 (prodObj B S hS U V).left.2 ⥤
      Prod' 𝒳.val.p)
    (hY : Y ⋙ ProdP 𝒳.val.p = Over.map (prodObj B S hS U V).hom)
    (comparison : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map (prodObj B S hS U V).hom) 𝒳.val.p
          (ProdP 𝒳.val.p) Y (Diag 𝒳.val.p) ⋙
        Over.map (prodFst B S hS U V))
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B V.left.1 V.left.2
      (terminal.from F : F ⟶
        ⊤_ ((AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) := by
  have hfib : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  refine isLocallyOfFiniteType_of_isomSpaceRelocalizes B S hS 𝒳 hΔ hΔlft V F (prodObj B S hS U V)
    (prodFst B S hS U V) (locallyOfFiniteType_prodFst B S hS U V)
    (Functor.sliceValue 𝒳.val.p (prodObj B S hS U V) (Y₁' Y) (h1' hY))
    (Functor.sliceValue 𝒳.val.p (prodObj B S hS U V) (Y₂' Y) (h2' hY)) ?_
  intro G hGiso
  obtain ⟨i⟩ := hGiso
  have hvh := Functor.vertHomPresheafIsoIsomPresheafOfPoint 𝒳.val.p
    𝒳.isFiberedInGroupoids (prodObj B S hS U V) Y hY
  have hiso2 : vertHomPresheaf 𝒳.isFiberedInGroupoids hY ⋙ uliftFunctor.{u, v} ≅
      G ⋙ uliftFunctor.{v, u} :=
    Functor.isoWhiskerRight hvh uliftFunctor.{u, v} ≪≫ i.symm
  obtain ⟨E⟩ := (nonempty_equivalenceOver_fst_iff 𝒳.isFiberedInGroupoids hY G).2 ⟨hiso2⟩
  obtain ⟨j⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff
    ((OverShriek.relocalizePresheafFunctor (prodFst B S hS U V)).obj G) F).1
    ⟨(((E.compRight (Over.map (prodFst B S hS U V))).trans
      (PresheafOfCategories.relocalizeElementsEquivalenceOver
        (prodFst B S hS U V) G)).symm).trans comparison⟩
  exact ⟨(uliftTrivialIso _).symm ≪≫ j ≪≫ uliftTrivialIso _⟩


open TwoFibreProductOver.DiagonalFibre in
/-- Local finiteness of type of the two-fibre product, from the mere existence of the
comparison: it suffices to exhibit a scheme-valued point `Y` of `𝒳 ×_S 𝒳`
with values in `T₀ = V ×_S U` such that the 2-fibre product of `Y` with the diagonal of `𝒳`,
read over the big fppf site of `V` through the first projection `T₀ ⟶ V`, is the category of
elements of `F` — i.e. such that `(Sch/V) ×_𝒳 (Sch/U) = Isom_{T₀}(y|_{T₀}, x|_{T₀})`. -/
private lemma isLocallyOfFiniteType_of_exists_point
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hΔlft :
      letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
        (a b : 𝒳.val.p.Fiber T)
        (G : (AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
        AlgebraicGeometry.IsAlgebraicSpace B T.left.1 T.left.2 G →
        Nonempty (G ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
            uliftFunctor.{u, v}) →
        AlgebraicGeometry.Space.IsLocallyOfFiniteType B T.left.1 T.left.2
          (terminal.from G : G ⟶
            ⊤_ ((AlgebraicGeometry.BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)))
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    [LocallyOfFiniteType (B.inclusion.map U.hom)]
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (h : ∃ (Y : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
          (prodObj B S hS U V).left.2 ⥤ Prod' 𝒳.val.p)
        (_hY : Y ⋙ ProdP 𝒳.val.p = Over.map (prodObj B S hS U V).hom),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map (prodObj B S hS U V).hom) 𝒳.val.p
              (ProdP 𝒳.val.p) Y (Diag 𝒳.val.p) ⋙
            Over.map (prodFst B S hS U V))
          (presheafOfCategories (F ⋙ typeToCat)).p)) :
    AlgebraicGeometry.Space.IsLocallyOfFiniteType B V.left.1 V.left.2
      (terminal.from F : F ⟶
        ⊤_ ((AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)) := by
  obtain ⟨Y, hY, ⟨c⟩⟩ := h
  exact isLocallyOfFiniteType_of_point B S hS 𝒳 hΔ hΔlft U V F Y hY c

/-! ### The comparison `𝒞_{V ×_S U} ≃ 𝒞_V ×_{𝒞_S} (𝒞_S/U)` -/

/-- The first component of the comparison: `T ⟶ V ×_S U ⟶ V`, read over `S`, is `T ⟶ S`. -/
private lemma sliceProdCmp_hx (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (c : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2) :
    (Over.map V.hom).obj ((Over.map (prodFst B S hS U V)).obj c) =
      (Over.map (prodObj B S hS U V).hom).obj c :=
  (Functor.congr_obj (Over.mapComp_eq (prodFst B S hS U V) V.hom) c).symm

open TwoFibreProductOver in
/-- The first component of the comparison is a morphism over the big fppf site of `S`. -/
private lemma sliceProdCmp_ha (U V : AlgebraicGeometry.BigFppfOver B S hS)
    {c c' : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2} (f : c ⟶ c') :
    (Over.map V.hom).IsHomLift ((Over.map (prodObj B S hS U V).hom).map f)
      ((Over.map (prodFst B S hS U V)).map f) :=
  IsHomLift.of_fac' (Over.map V.hom) _ _ (sliceProdCmp_hx B S hS U V c)
    (sliceProdCmp_hx B S hS U V c') (by
      apply Over.OverMorphism.ext
      simp [Over.eqToHom_left])

/-- The second component of the comparison: `T ⟶ V ×_S U ⟶ U`, as an object of the slice of
the big fppf site of `S` at `U`. -/
@[implicit_reducible] private noncomputable def sliceProdCmpSnd
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (c : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2) : Over U :=
  Over.mk (Over.homMk (c.hom ≫ (prodSnd B S hS U V).left)
    (by rw [Category.assoc, Over.w]; rfl) :
      (Over.map (prodObj B S hS U V).hom).obj c ⟶ U)

/-- The second component of the comparison, on morphisms. -/
@[implicit_reducible] private noncomputable def sliceProdCmpSndMap
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    {c c' : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2} (f : c ⟶ c') :
    sliceProdCmpSnd B S hS U V c ⟶ sliceProdCmpSnd B S hS U V c' :=
  Over.homMk ((Over.map (prodObj B S hS U V).hom).map f)
    (by apply Over.OverMorphism.ext; simp [sliceProdCmpSnd, Over.w_assoc])

open TwoFibreProductOver in
/-- The second component of the comparison is a morphism over the big fppf site of `S`. -/
private lemma sliceProdCmp_hb (U V : AlgebraicGeometry.BigFppfOver B S hS)
    {c c' : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2} (f : c ⟶ c') :
    (Over.forget U).IsHomLift ((Over.map (prodObj B S hS U V).hom).map f)
      (sliceProdCmpSndMap B S hS U V f) :=
  IsHomLift.map (Over.forget U) (sliceProdCmpSndMap B S hS U V f)

open TwoFibreProductOver in
/-- **The big fppf site over `V ×_S U` is the product, over the big fppf site of `S`, of the
big fppf site over `V` with the slice at `U`.**  An object `c : T ⟶ V ×_S U` goes to the pair
of its two components, with the canonical comparison isomorphism. -/
@[implicit_reducible] private noncomputable def sliceProdCmp
    (U V : AlgebraicGeometry.BigFppfOver B S hS) :
    AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1 (prodObj B S hS U V).left.2 ⥤
      TwoFibreProductOver (Over.map V.hom) (Over.forget U)
        (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U) where
  obj c :=
    { base := (Over.map (prodObj B S hS U V).hom).obj c
      x := (Over.map (prodFst B S hS U V)).obj c
      y := sliceProdCmpSnd B S hS U V c
      hx := sliceProdCmp_hx B S hS U V c
      hy := rfl
      iso := eqToIso (sliceProdCmp_hx B S hS U V c)
      vertical := isHomLift_id_eqToHom (sliceProdCmp_hx B S hS U V c) rfl
        (sliceProdCmp_hx B S hS U V c) }
  map {c c'} f :=
    { hbase := (Over.map (prodObj B S hS U V).hom).map f
      a := (Over.map (prodFst B S hS U V)).map f
      b := sliceProdCmpSndMap B S hS U V f
      ha := sliceProdCmp_ha B S hS U V f
      hb := sliceProdCmp_hb B S hS U V f
      w := prodOver_w_eqToHom (p𝒴 := Over.forget U) (sliceProdCmp_hx B S hS U V c) rfl
        (sliceProdCmp_hx B S hS U V c') rfl (sliceProdCmp_ha B S hS U V f)
        (sliceProdCmp_hb B S hS U V f) }
  map_id c := by
    refine Hom.ext' ((Over.map (prodFst B S hS U V)).map_id c) ?_
    refine Over.OverMorphism.ext ?_
    exact (Over.map (prodObj B S hS U V).hom).map_id c
  map_comp f g := by
    refine Hom.ext' ((Over.map (prodFst B S hS U V)).map_comp f g) ?_
    refine Over.OverMorphism.ext ?_
    exact (Over.map (prodObj B S hS U V).hom).map_comp f g

open TwoFibreProductOver in
/-- The comparison functor is strictly a 1-morphism over the big fppf site of `S`. -/
private lemma sliceProdCmp_comp_structureFunctor (U V : AlgebraicGeometry.BigFppfOver B S hS) :
    sliceProdCmp B S hS U V ⋙ structureFunctor (Over.map V.hom) (Over.forget U)
        (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U) =
      Over.map (prodObj B S hS U V).hom := rfl

open TwoFibreProductOver in
/-- The first projection of the comparison functor is the first projection `V ×_S U ⟶ V`. -/
private lemma sliceProdCmp_comp_fst (U V : AlgebraicGeometry.BigFppfOver B S hS) :
    sliceProdCmp B S hS U V ⋙ fst (Over.map V.hom) (Over.forget U)
        (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U) =
      Over.map (prodFst B S hS U V) := rfl

open TwoFibreProductOver in
/-- The base of an object of the product and its first component have the same underlying
object. -/
private lemma sliceProdCmp_eP (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    P.x.left = P.base.left := congrArg Over.left P.hx

open TwoFibreProductOver in
/-- The base of an object of the product and its second component have the same underlying
object. -/
private lemma sliceProdCmp_eQ (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    P.y.left.left = P.base.left := congrArg Over.left P.hy

open TwoFibreProductOver in
/-- The first component of an object of the product factors its structure morphism to `S`. -/
private lemma sliceProdCmp_hPx (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    eqToHom (sliceProdCmp_eP B S hS U V P) ≫ P.base.hom = P.x.hom ≫ V.hom := by
  simpa [Over.eqToHom_left] using Over.w (eqToHom P.hx)

open TwoFibreProductOver in
/-- The second component of an object of the product factors its structure morphism to `S`. -/
private lemma sliceProdCmp_hPy (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    eqToHom (sliceProdCmp_eQ B S hS U V P) ≫ P.base.hom = P.y.left.hom := by
  simpa [Over.eqToHom_left] using Over.w (eqToHom P.hy)

open TwoFibreProductOver in
/-- The two components of an object of the product agree over `S`, so they induce a morphism
to the fibre product `V ×_S U`. -/
private lemma sliceProdCmp_cond (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    P.x.hom ≫ V.hom = (eqToHom ((sliceProdCmp_eP B S hS U V P).trans
      (sliceProdCmp_eQ B S hS U V P).symm) ≫ P.y.hom.left) ≫ U.hom :=
  calc P.x.hom ≫ V.hom = eqToHom (sliceProdCmp_eP B S hS U V P) ≫ P.base.hom :=
        (sliceProdCmp_hPx B S hS U V P).symm
    _ = eqToHom ((sliceProdCmp_eP B S hS U V P).trans
          (sliceProdCmp_eQ B S hS U V P).symm) ≫
        eqToHom (sliceProdCmp_eQ B S hS U V P) ≫ P.base.hom := by simp
    _ = eqToHom ((sliceProdCmp_eP B S hS U V P).trans
          (sliceProdCmp_eQ B S hS U V P).symm) ≫ P.y.left.hom := by
        rw [sliceProdCmp_hPy]
    _ = (eqToHom ((sliceProdCmp_eP B S hS U V P).trans
          (sliceProdCmp_eQ B S hS U V P).symm) ≫ P.y.hom.left) ≫ U.hom := by
        rw [Category.assoc, Over.w]

open TwoFibreProductOver in
/-- **The morphism to `V ×_S U` induced by an object of the product.** -/
@[implicit_reducible] private noncomputable def sliceProdCmpPoint
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2 :=
  Over.mk (pullback.lift P.x.hom (eqToHom ((sliceProdCmp_eP B S hS U V P).trans
    (sliceProdCmp_eQ B S hS U V P).symm) ≫ P.y.hom.left) (sliceProdCmp_cond B S hS U V P))

open TwoFibreProductOver in
/-- Its first component is the first component of `P`. -/
private lemma sliceProdCmpPoint_fst (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    (sliceProdCmpPoint B S hS U V P).hom ≫ prodFst B S hS U V = P.x.hom :=
  pullback.lift_fst _ _ _

open TwoFibreProductOver in
/-- Its second component is the second component of `P`. -/
private lemma sliceProdCmpPoint_snd (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    (sliceProdCmpPoint B S hS U V P).hom ≫ (prodSnd B S hS U V).left =
      eqToHom ((sliceProdCmp_eP B S hS U V P).trans
        (sliceProdCmp_eQ B S hS U V P).symm) ≫ P.y.hom.left :=
  pullback.lift_snd _ _ _

open TwoFibreProductOver in
/-- Its structure morphism to `S` is that of `P`. -/
private lemma sliceProdCmpPoint_base (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    eqToHom (sliceProdCmp_eP B S hS U V P) ≫ P.base.hom =
      (sliceProdCmpPoint B S hS U V P).hom ≫ (prodObj B S hS U V).hom :=
  (sliceProdCmp_hPx B S hS U V P).trans
    ((congrArg (· ≫ V.hom) (sliceProdCmpPoint_fst B S hS U V P)).symm.trans
      (Category.assoc _ _ _))

/-- Two objects of a slice whose structure morphisms agree after transport are equal. -/
private lemma over_mk_eq_of_eq {T : Type*} [Category T] {X A A' : T}
    (e : A = A') (f : A ⟶ X) (f' : A' ⟶ X) (h : f = eqToHom e ≫ f') :
    Over.mk f = Over.mk f' := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at h
  rw [h]

open TwoFibreProductOver in
/-- The comparison isomorphism of the image of an object is the canonical `eqToHom`. -/
private lemma sliceProdCmp_obj_iso_hom (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (c : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2) :
    ((sliceProdCmp B S hS U V).obj c).iso.hom =
      eqToHom (sliceProdCmp_hx B S hS U V c) := rfl

open TwoFibreProductOver in
/-- The base object of the induced morphism is the base of `P`. -/
private lemma sliceProdCmpPoint_obj (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (P : TwoFibreProductOver (Over.map V.hom) (Over.forget U)
      (𝟭 (AlgebraicGeometry.BigFppfOver B S hS)) (Over.map V.hom) (Over.forget U)) :
    (Over.map (prodObj B S hS U V).hom).obj (sliceProdCmpPoint B S hS U V P) = P.base :=
  (congrArg Over.mk ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ V.hom) (sliceProdCmpPoint_fst B S hS U V P)))).trans P.hx

open TwoFibreProductOver in
/-- The underlying morphism of the first component of a morphism of the product is the one the
base morphism induces. -/
private lemma sliceProdCmp_hom_a_left (U V : AlgebraicGeometry.BigFppfOver B S hS)
    {c c' : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2}
    (φ : (sliceProdCmp B S hS U V).obj c ⟶ (sliceProdCmp B S hS U V).obj c') :
    φ.a.left = φ.hbase.left := by
  have hfa : (Over.map V.hom).map φ.a = eqToHom (sliceProdCmp_hx B S hS U V c) ≫
      φ.hbase ≫ eqToHom (sliceProdCmp_hx B S hS U V c').symm := by
    have := φ.ha
    exact IsHomLift.fac' (Over.map V.hom) φ.hbase φ.a
  have h := congrArg Over.Hom.left hfa
  simp only [Over.map_map_left, Over.comp_left, Over.eqToHom_left, eqToHom_refl,
    Category.id_comp] at h
  exact h

open TwoFibreProductOver in
/-- The underlying morphism of the second component of a morphism of the product is the one the
base morphism induces. -/
private lemma sliceProdCmp_hom_b_left (U V : AlgebraicGeometry.BigFppfOver B S hS)
    {c c' : AlgebraicGeometry.BigFppfOver B (prodObj B S hS U V).left.1
      (prodObj B S hS U V).left.2}
    (φ : (sliceProdCmp B S hS U V).obj c ⟶ (sliceProdCmp B S hS U V).obj c') :
    φ.b.left = φ.hbase := by
  have hfb : (Over.forget U).map φ.b = eqToHom rfl ≫ φ.hbase ≫ eqToHom rfl := by
    have := φ.hb
    exact IsHomLift.fac' (Over.forget U) φ.hbase φ.b
  simpa using hfb

open TwoFibreProductOver in
/-- **The comparison functor is an equivalence.**  It is fully faithful because a morphism of
the product is determined by its base morphism, and essentially surjective because the two
components of an object of the product induce a morphism to the fibre product `V ×_S U`. -/
private lemma isEquivalence_sliceProdCmp (U V : AlgebraicGeometry.BigFppfOver B S hS) :
    (sliceProdCmp B S hS U V).IsEquivalence := by
  have hfaith : (sliceProdCmp B S hS U V).Faithful := by
    constructor
    intro c c' f g h
    exact Over.OverMorphism.ext (congrArg (fun φ => Over.Hom.left φ.hbase) h)
  have hfull : (sliceProdCmp B S hS U V).Full := by
    constructor
    intro c c' φ
    have ha := sliceProdCmp_hom_a_left B S hS U V φ
    have hb := sliceProdCmp_hom_b_left B S hS U V φ
    have hwa : φ.hbase.left ≫ c'.hom ≫ prodFst B S hS U V =
        c.hom ≫ prodFst B S hS U V := by
      rw [← ha]
      exact Over.w φ.a
    have hwb : φ.hbase.left ≫ c'.hom ≫ (prodSnd B S hS U V).left =
        c.hom ≫ (prodSnd B S hS U V).left := by
      have h0 : φ.b.left ≫ (sliceProdCmpSnd B S hS U V c').hom =
          (sliceProdCmpSnd B S hS U V c).hom := Over.w φ.b
      rw [hb] at h0
      exact congrArg Over.Hom.left h0
    refine ⟨Over.homMk φ.hbase.left (pullback.hom_ext
      ((Category.assoc _ _ _).trans hwa) ((Category.assoc _ _ _).trans hwb)), ?_⟩
    exact Hom.ext' (Over.OverMorphism.ext ha.symm) (Over.OverMorphism.ext hb.symm)
  have hess : (sliceProdCmp B S hS U V).EssSurj := by
    constructor
    intro P
    have hxx : ((sliceProdCmp B S hS U V).obj (sliceProdCmpPoint B S hS U V P)).x = P.x :=
      congrArg Over.mk (sliceProdCmpPoint_fst B S hS U V P)
    have hyy : ((sliceProdCmp B S hS U V).obj (sliceProdCmpPoint B S hS U V P)).y = P.y :=
      over_mk_eq_of_eq ((sliceProdCmpPoint_obj B S hS U V P).trans P.hy.symm) _ _ (by
        refine Over.OverMorphism.ext ?_
        simp only [Over.comp_left, Over.eqToHom_left]
        exact sliceProdCmpPoint_snd B S hS U V P)
    refine ⟨sliceProdCmpPoint B S hS U V P, ⟨TwoFibreProductOver.isoMkVertical
      (U := P.base) (eqToIso hxx) (eqToIso hyy) ?_ ?_ ?_⟩⟩
    · refine IsHomLift.of_fac' (Over.map V.hom) (𝟙 P.base) _
        (show (Over.map V.hom).obj ((sliceProdCmp B S hS U V).obj
            (sliceProdCmpPoint B S hS U V P)).x = P.base from
          (sliceProdCmp_hx B S hS U V (sliceProdCmpPoint B S hS U V P)).trans
            (sliceProdCmpPoint_obj B S hS U V P)) P.hx ?_
      simp only [eqToIso.hom, eqToHom_map, Category.id_comp]
      exact (eqToHom_trans _ _).symm
    · refine IsHomLift.of_fac' (Over.forget U) (𝟙 P.base) _
        (show (Over.forget U).obj ((sliceProdCmp B S hS U V).obj
            (sliceProdCmpPoint B S hS U V P)).y = P.base from
          sliceProdCmpPoint_obj B S hS U V P) P.hy ?_
      simp only [eqToIso.hom, eqToHom_map, Category.id_comp]
      exact (eqToHom_trans _ _).symm
    · rw [prodOver_iso_hom P]
      simp only [eqToIso.hom, sliceProdCmp_obj_iso_hom, eqToHom_map, eqToHom_trans]
  exact Functor.IsEquivalence.mk

end Deformation.Artin.BaseChange

end
