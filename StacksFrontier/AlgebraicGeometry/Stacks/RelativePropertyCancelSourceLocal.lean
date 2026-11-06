module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.SyntomicTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSectionIso
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeSnd
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.SectionBasedFunctor
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Checking a relative property after precomposition by a covering

Let a representable morphism of algebraic stacks be followed by another
representable morphism. If the first morphism is a surjective étale, smooth,
syntomic, or fppf cover, and the composite has a relative property local on
the source for that topology, then the second morphism has the property.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_cover` descends a relative
  property from a composite along a covering of the intermediate stack.

## Implementation notes

A covering morphism is tested on every algebraic-space representation of its
base change to a scheme-valued point, where it is surjective and has the
indicated étale, smooth, syntomic, or flat and locally finitely presented
property. Source locality is expressed with the corresponding precoverage.

## References

* [Stacks Project, Tag 06M2](https://stacks.math.columbia.edu/tag/06M2)
-/

public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

open Opposite

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_relativePropertyCancelSourceLocal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Limits.HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_relativePropertyCancelSourceLocal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  (hasPullbacks_presheaf_relativePropertyCancelSourceLocal B S hS).has_limit _

/- The arguments below reason about the fibre categories of the structure functors `𝒳.based.p`
and about 2-fibre products over them. Those spellings are built from definitions that the
`implicit` transparency level does not unfold -- `InducedBicategory`, so that the underlying
based category is a subtype at all; `BasedCategory.ofFunctor`; the 2-fibre product's structure
functor and its projections -- so the goals are not type-correct at that level and `rw`, `simp`
and instance synthesis decline to act on them. Naming the unfolding chain here is what lets the
ordinary tactics see through it. -/
attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  Bicategory.InducedBicategory Bicategory.InducedBicategory.categoryStruct
  Bicategory.InducedBicategory.bicategory
  BasedCategory.ofFunctor BasedCategory.instCategory BasedCategory.bicategory
  TwoFibreProductOver.structureFunctor TwoFibreProductOver.fst TwoFibreProductOver.snd
  Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.Fiber.mapOfComp Functor.Fiber.inducedFunctor
  CategoryTheory.instCategoryObj

universe u₁ v₁ u₂

/-- The element of `F(U)` named by an object of the category of elements of `F` lying over `U`,
that is, `CategoryTheory.PresheafOfCategories.elementsFiberEquiv` applied to the object together
with an identification of its base. -/
private def elementValue {C : Type u₁} [Category.{v₁} C]
    {F : Cᵒᵖ ⥤ Type u₂} {U : C}
    (x : (presheafOfCategories (F ⋙ typeToCat)).obj)
    (hx : x.base = U) : F.obj (op U) :=
  PresheafOfCategories.elementsFiberEquiv F U ⟨x, hx⟩

private lemma elementValue_congr {C : Type*} [Category C]
    {F : Cᵒᵖ ⥤ Type*} {U : C}
    {x y : (presheafOfCategories (F ⋙ typeToCat)).obj}
    (hx : x.base = U) (hy : y.base = U) (h : x = y) :
    elementValue x hx = elementValue y hy := by
  subst y
  rfl

private lemma elementValue_map {C : Type u₁} [Category.{v₁} C]
    {F : Cᵒᵖ ⥤ Type u₂} {U V : C}
    {x y : (presheafOfCategories (F ⋙ typeToCat)).obj}
    (hx : x.base = U) (hy : y.base = V) (k : U ⟶ V) (m : x ⟶ y)
    (hm : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift k m) :
    elementValue x hx = F.map k.op (elementValue y hy) :=
  PresheafOfCategories.elementsFiberEquiv_map_of_isHomLift F k ⟨y, hy⟩ ⟨x, hx⟩ m hm

private def presheafMapOfFunctor {C : Type u₁} [Category.{v₁} C]
    {F G : Cᵒᵖ ⥤ Type u₂}
    (H : (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hH : H ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p) : F ⟶ G where
  app U := ↾fun x => elementValue (H.obj ⟨U.unop, Discrete.mk x⟩)
    (Functor.congr_obj hH _)
  naturality {U V} k := by
    ext x
    let m : (⟨V.unop, Discrete.mk (F.map k x)⟩ :
        (presheafOfCategories (F ⋙ typeToCat)).obj) ⟶
      ⟨U.unop, Discrete.mk x⟩ := ⟨k.unop, 𝟙 _⟩
    have : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift k.unop m :=
      IsHomLift.map (presheafOfCategories (F ⋙ typeToCat)).p m
    exact elementValue_map (Functor.congr_obj hH ⟨V.unop, Discrete.mk (F.map k x)⟩)
      (Functor.congr_obj hH ⟨U.unop, Discrete.mk x⟩) k.unop (H.map m)
      (Functor.isHomLift_map_of_comp_eq hH k.unop m)


private def presheafMapOfFunctorOver
    {C : Type u₁} [Category.{v₁} C] {D : Type*} [Category D]
    (K : C ⥤ D) {F : Cᵒᵖ ⥤ Type u₂} {G : Dᵒᵖ ⥤ Type u₂}
    (H : (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hH : H ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p ⋙ K) : F ⟶ K.op ⋙ G where
  app U := ↾fun x => elementValue (F := G) (H.obj ⟨U.unop, Discrete.mk x⟩)
    (Functor.congr_obj hH _)
  naturality {U V} k := by
    ext x
    let m : (⟨V.unop, Discrete.mk (F.map k x)⟩ :
        (presheafOfCategories (F ⋙ typeToCat)).obj) ⟶
      ⟨U.unop, Discrete.mk x⟩ := ⟨k.unop, 𝟙 _⟩
    have : ((presheafOfCategories (F ⋙ typeToCat)).p ⋙ K).IsHomLift
        (K.map k.unop) m :=
      IsHomLift.map ((presheafOfCategories (F ⋙ typeToCat)).p ⋙ K) m
    exact elementValue_map (Functor.congr_obj hH ⟨V.unop, Discrete.mk (F.map k x)⟩)
      (Functor.congr_obj hH ⟨U.unop, Discrete.mk x⟩) (K.map k.unop) (H.map m)
      (Functor.isHomLift_map_of_comp_eq hH (K.map k.unop) m)

private lemma presheafMapOfFunctor_app {C : Type u₁} [Category.{v₁} C]
    {F G : Cᵒᵖ ⥤ Type u₂}
    (H : (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hH : H ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (x : (presheafOfCategories (F ⋙ typeToCat)).obj) :
    (presheafMapOfFunctor H hH).app (op x.base) x.fiber.as =
      elementValue (H.obj x) (Functor.congr_obj hH x) := by
  cases x
  rfl

private lemma presheafMapOfFunctor_app_elementValue
    {C : Type u₁} [Category.{v₁} C] {F G : Cᵒᵖ ⥤ Type u₂}
    (H : (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hH : H ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (x : (presheafOfCategories (F ⋙ typeToCat)).obj) (hx : x.base = U) :
    (presheafMapOfFunctor H hH).app (op U) (elementValue x hx) =
      elementValue (H.obj x) ((Functor.congr_obj hH x).trans hx) := by
  subst U
  exact presheafMapOfFunctor_app H hH x

private lemma elementValue_eq_of_vertical {C : Type u₁} [Category.{v₁} C]
    {F : Cᵒᵖ ⥤ Type u₂} {U : C}
    {x y : (presheafOfCategories (F ⋙ typeToCat)).obj}
    (hx : x.base = U) (hy : y.base = U) (m : x ⟶ y)
    [hm : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift (𝟙 U) m] :
    elementValue x hx = elementValue y hy := by
  simpa using elementValue_map hx hy (𝟙 U) m hm

private lemma presheafMapOfFunctor_eq_of_vertical {C : Type u₁} [Category.{v₁} C]
    {F G : Cᵒᵖ ⥤ Type u₂}
    (H K : (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hH : H ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hK : K ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (α : H ⟶ K)
    (hα : ∀ x, (presheafOfCategories (G ⋙ typeToCat)).p.IsHomLift
      (𝟙 x.base) (α.app x)) :
    presheafMapOfFunctor H hH = presheafMapOfFunctor K hK := by
  ext U x
  let a : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨U.unop, Discrete.mk x⟩
  have := hα a
  exact elementValue_eq_of_vertical (U := U.unop) (Functor.congr_obj hH a)
    (Functor.congr_obj hK a) (α.app a)


private lemma presheafMapOfFunctor_of_equivalence_apply
    {C : Type u₁} [Category.{v₁} C] {A : Type*} [Category A]
    {p : A ⥤ C} {F G : Cᵒᵖ ⥤ Type u₂}
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (T : A ⥤ (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hT : T ⋙ (presheafOfCategories (G ⋙ typeToCat)).p = p)
    (a : A) :
    (presheafMapOfFunctor (e.inv.functor ⋙ T)
      (by rw [Functor.assoc, hT, e.inv.w])).app (op (p.obj a))
        (elementValue (e.hom.functor.obj a) (Functor.congr_obj e.hom.w a)) =
      elementValue (T.obj a) (Functor.congr_obj hT a) := by
  refine (presheafMapOfFunctor_app_elementValue (e.inv.functor ⋙ T)
    (by rw [Functor.assoc, hT, e.inv.w]) (e.hom.functor.obj a)
    (Functor.congr_obj e.hom.w a)).trans ?_
  have := e.isHomLift_unitIso_inv_app a
  have := Functor.isHomLift_map_of_comp_eq hT (𝟙 (p.obj a)) (e.unitIso.inv.app a)
  exact elementValue_eq_of_vertical (U := p.obj a) _ _ (T.map (e.unitIso.inv.app a))

private lemma presheafMapOfFunctor_comp
    {C : Type u₁} [Category.{v₁} C]
    {F G I : Cᵒᵖ ⥤ Type u₂}
    (H : (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hH : H ⋙ (presheafOfCategories (G ⋙ typeToCat)).p =
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (K : (presheafOfCategories (G ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (I ⋙ typeToCat)).obj)
    (hK : K ⋙ (presheafOfCategories (I ⋙ typeToCat)).p =
      (presheafOfCategories (G ⋙ typeToCat)).p) :
    presheafMapOfFunctor (H ⋙ K)
      (by rw [Functor.assoc, hK, hH]) =
      presheafMapOfFunctor H hH ≫ presheafMapOfFunctor K hK := by
  ext U x
  let a : (presheafOfCategories (F ⋙ typeToCat)).obj :=
    ⟨U.unop, Discrete.mk x⟩
  show elementValue (K.obj (H.obj a)) _ =
    (presheafMapOfFunctor K hK).app U (elementValue (H.obj a) (Functor.congr_obj hH a))
  exact (presheafMapOfFunctor_app_elementValue K hK (H.obj a)
    (Functor.congr_obj hH a)).symm

private lemma presheafMapOfFunctor_id
    {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type u₂} :
    presheafMapOfFunctor (𝟭 (presheafOfCategories (F ⋙ typeToCat)).obj)
      (by rfl) = 𝟙 F := by
  ext U x
  rfl

private def presheafIsoOfEquivalenceOver
    {C : Type u₁} [Category.{v₁} C]
    {F G : Cᵒᵖ ⥤ Type u₂}
    (e : StacksRepresentableCFG.EquivalenceOver
      (presheafOfCategories (F ⋙ typeToCat)).p
      (presheafOfCategories (G ⋙ typeToCat)).p) : F ≅ G where
  hom := presheafMapOfFunctor e.hom.functor e.hom.w
  inv := presheafMapOfFunctor e.inv.functor e.inv.w
  hom_inv_id := by
    rw [← presheafMapOfFunctor_comp]
    have h := presheafMapOfFunctor_eq_of_vertical
      (𝟭 _) (e.hom.functor ⋙ e.inv.functor) (by rfl)
      (by rw [Functor.assoc, e.inv.w, e.hom.w]) e.unitIso.hom
      (fun x => e.isHomLift_unitIso_hom_app x)
    exact h.symm.trans presheafMapOfFunctor_id
  inv_hom_id := by
    rw [← presheafMapOfFunctor_comp]
    have h := presheafMapOfFunctor_eq_of_vertical
      (e.inv.functor ⋙ e.hom.functor) (𝟭 _)
      (by rw [Functor.assoc, e.hom.w, e.inv.w]) (by rfl)
      e.counitIso.hom (fun x => e.isHomLift_counitIso_hom_app x)
    exact h.trans presheafMapOfFunctor_id

private theorem isCovering_singleton_of_surjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (τ : AlgebraicGeometry.Space.Topology)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (hsurj : AlgebraicGeometry.Space.IsSurjective B S hS q.hom)
    (hq : match τ with
      | .etale => AlgebraicGeometry.Space.IsEtale B S hS q.hom
      | .smooth => AlgebraicGeometry.Space.IsSmooth B S hS q.hom
      | .syntomic => AlgebraicGeometry.Space.IsSyntomic B S hS q.hom
      | .fppf => AlgebraicGeometry.Space.IsFlat B S hS q.hom ∧
          AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS q.hom
      | .fpqc => False) :
    τ.IsCovering.{u, v} B S hS (fun _ : ULift.{v} Unit => X.obj)
      (fun _ => q.hom) := by
  have hrange : (⋃ _ : ULift.{v} Unit,
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS X.obj q.hom)) = Set.univ := by
    simpa only [Set.iUnion_const] using (Set.range_eq_univ.mpr hsurj)
  refine ⟨Y.property, fun _ => X.property, ?_⟩
  cases τ with
  | fpqc => exact hq.elim
  | fppf => exact ⟨Y.property, fun _ => X.property, fun _ => hq.1,
      fun _ => hq.2, hrange⟩
  | syntomic => exact ⟨Y.property, fun _ => X.property, fun _ => hq, hrange⟩
  | smooth => exact ⟨Y.property, fun _ => X.property, fun _ => hq, hrange⟩
  | etale => exact ⟨Y.property, fun _ => X.property, fun _ => hq, hrange⟩

private theorem isEtale_of_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y)
    (ha : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a) :
    AlgebraicGeometry.Space.IsEtale B S hS a := by
  intro T φ hφ
  let E := MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let _ : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) := by
    refine ⟨?_⟩
    intro X Y Z f g hf hg
    let _ : Etale f := hf
    let _ : Etale g := hg
    exact Etale.etale_comp f g
  let _ : E.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage
      (F := AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let _ : E.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition E
  exact MorphismProperty.comp_mem E.presheaf φ a hφ ha

/-- An étale surjective chart of a space, given by presheaf-level hypotheses, is surjective and
étale as a morphism of spaces. -/
private theorem isSurjective_and_isEtale_of_chart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y.obj)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a) :
    AlgebraicGeometry.Space.IsSurjective B S hS a ∧ AlgebraicGeometry.Space.IsEtale B S hS a :=
  ⟨(AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS Y.obj
      Y.property V a).mp haSurj, isEtale_of_chart B S hS V a haEtale⟩

private theorem isSurjective_of_surjective_chart_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y.obj)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (hbase : AlgebraicGeometry.Space.IsSurjective B S hS
      (CategoryTheory.Limits.pullback.snd q.hom a)) :
    AlgebraicGeometry.Space.IsSurjective B S hS q.hom := by
  apply ((AlgebraicGeometry.Space.isSurjective_tfae B S hS X.property Y.property q.hom).out 4 1).mp
  have h := isSurjective_and_isEtale_of_chart B S hS V a haSurj haEtale
  exact ⟨V, a, h.1, h.2, hbase⟩

private theorem isEtale_of_etale_chart_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y.obj)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (hbase : AlgebraicGeometry.Space.IsEtale B S hS (CategoryTheory.Limits.pullback.snd q.hom a)) :
    AlgebraicGeometry.Space.IsEtale B S hS q.hom :=
  (AlgebraicGeometry.Space.isEtale_iff_exists_target_chart B S hS X.property Y.property q.hom).mpr
    ⟨V, a, haSurj, haEtale, hbase⟩

private theorem isSmooth_of_smooth_chart_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y.obj)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (hbase : AlgebraicGeometry.Space.IsSmooth B S hS
      (CategoryTheory.Limits.pullback.snd q.hom a)) :
    AlgebraicGeometry.Space.IsSmooth B S hS q.hom := by
  apply ((AlgebraicGeometry.Space.isSmooth_tfae B S hS X.property Y.property q.hom).out 5 1).mp
  exact ⟨V, a, haSurj, haEtale, hbase⟩

private theorem isSyntomic_of_syntomic_chart_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y.obj)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (hbase : AlgebraicGeometry.Space.IsSyntomic B S hS
      (CategoryTheory.Limits.pullback.fst a q.hom)) :
    AlgebraicGeometry.Space.IsSyntomic B S hS q.hom := by
  have h := isSurjective_and_isEtale_of_chart B S hS V a haSurj haEtale
  apply ((AlgebraicGeometry.Space.isSyntomic_tfae B S hS X.property Y.property q.hom).out 5 1).mp
  exact ⟨V, a, h.1, h.2, hbase⟩

private theorem isFlat_of_flat_chart_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y.obj)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (hbase : AlgebraicGeometry.Space.IsFlat B S hS
      (CategoryTheory.Limits.pullback.fst a q.hom)) :
    AlgebraicGeometry.Space.IsFlat B S hS q.hom := by
  have h := isSurjective_and_isEtale_of_chart B S hS V a haSurj haEtale
  apply ((AlgebraicGeometry.Space.isFlat_tfae B S hS X.property Y.property q.hom).out 5 1).mp
  exact ⟨V, a, h.1, h.2, hbase⟩

private theorem isLocallyOfFinitePresentation_of_chart_pullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : X ⟶ Y)
    (V : AlgebraicGeometry.BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y.obj)
    (haSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf a)
    (hbase : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS
      (CategoryTheory.Limits.pullback.fst a q.hom)) :
    AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS q.hom := by
  have h := isSurjective_and_isEtale_of_chart B S hS V a haSurj haEtale
  apply ((AlgebraicGeometry.Space.isLocallyOfFinitePresentation_tfae B S hS
    X.property Y.property q.hom).out 5 1).mp
  exact ⟨V, a, h.1, h.2, hbase⟩

private theorem relativeProperty_of_covering_precomposition
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicGeometry.AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicGeometry.Space.Topology.fppf.precoverage B S hS)]
    (τ : AlgebraicGeometry.Space.Topology)
    [P.IsLocalAtSource (τ.precoverage.{u, v} B S hS)]
    {X Y Z : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (q : X ⟶ Y) (r : Y ⟶ Z)
    (hq : τ.IsCovering.{u, v} B S hS (fun _ : ULift.{v} Unit => X.obj)
      (fun _ => q.hom))
    (hP : P (q ≫ r)) : P r := by
  let Yi : ULift.{v} Unit → AlgebraicGeometry.AlgebraicSpaces B S hS := fun _ => X
  let qi : ∀ i, Yi i ⟶ Y := fun _ => q
  have hR : Presieve.ofArrows Yi qi ∈ τ.precoverage.{u, v} B S hS Y :=
    ⟨ULift.{v} Unit, Yi, qi, rfl, hq⟩
  apply (inferInstance : P.IsLocalAtSource (τ.precoverage.{u, v} B S hS)).of_forall_comp hR
  rintro X' q' ⟨i, hi⟩
  simpa [Yi, qi] using hP

private def equivalenceOverChangeProjection
    {C A D : Type*} [Category C] [Category A] [Category D]
    {p p' : A ⥤ C} {q : D ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) (h : p = p') :
    StacksRepresentableCFG.EquivalenceOver p' q where
  hom := ⟨e.hom.functor, e.hom.w.trans h⟩
  inv := ⟨e.inv.functor, by rw [← h, e.inv.w]⟩
  unitIso := e.unitIso
  counitIso := e.counitIso
  unit_over := by subst p'; exact e.unit_over
  counit_over := e.counit_over

private lemma element_eq {C : Type*} [Category C]
    {F : Cᵒᵖ ⥤ Type*} (x : (presheafOfCategories (F ⋙ typeToCat)).obj)
    {U : C} (hx : x.base = U) :
    x = ⟨U, Discrete.mk (elementValue x hx)⟩ := by
  subst U
  cases x
  rfl

private noncomputable def isoOfElementValueEq
    {C A : Type*} [Category C] [Category A] {p : A ⥤ C}
    {F : Cᵒᵖ ⥤ Type*}
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (x y : A) (hx : p.obj x = U) (hy : p.obj y = U)
    (h : elementValue (e.hom.functor.obj x) ((Functor.congr_obj e.hom.w x).trans hx) =
      elementValue (e.hom.functor.obj y) ((Functor.congr_obj e.hom.w y).trans hy)) :
    x ≅ y :=
  Functor.Fiber.fiberInclusion.mapIso
    (PresheafOfCategories.fiberIsoOfSectionOfObj_eq e hx hy h)

private lemma isoOfElementValueEq_over
    {C A : Type*} [Category C] [Category A] {p : A ⥤ C}
    {F : Cᵒᵖ ⥤ Type*}
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : C} (x y : A) (hx : p.obj x = U) (hy : p.obj y = U)
    (h : elementValue (e.hom.functor.obj x) ((Functor.congr_obj e.hom.w x).trans hx) =
      elementValue (e.hom.functor.obj y) ((Functor.congr_obj e.hom.w y).trans hy)) :
    p.IsHomLift (𝟙 U) (isoOfElementValueEq e x y hx hy h).hom :=
  (PresheafOfCategories.fiberIsoOfSectionOfObj_eq e hx hy h).hom.2

private lemma equivalence_inv_section
    {C A : Type*} [Category C] [Category A] {p : A ⥤ C}
    {F : Cᵒᵖ ⥤ Type*}
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (U : C) (s : F.obj (op U)) :
    elementValue (e.hom.functor.obj (e.inv.functor.obj ⟨U, Discrete.mk s⟩))
      ((Functor.congr_obj e.hom.w _).trans (Functor.congr_obj e.inv.w _)) = s := by
  have : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift (𝟙 U)
      (e.counitIso.hom.app ⟨U, Discrete.mk s⟩) :=
    e.isHomLift_counitIso_hom_app ⟨U, Discrete.mk s⟩
  exact elementValue_eq_of_vertical (U := U) _ rfl
    (e.counitIso.hom.app ⟨U, Discrete.mk s⟩)

private lemma presheafMapOfFunctorOver_of_equivalence_apply
    {C D A : Type*} [Category C] [Category D] [Category A]
    (K : C ⥤ D) {p : A ⥤ C} {F : Cᵒᵖ ⥤ Type u} {G : Dᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (T : A ⥤ (presheafOfCategories (G ⋙ typeToCat)).obj)
    (hT : T ⋙ (presheafOfCategories (G ⋙ typeToCat)).p = p ⋙ K)
    (a : A) :
    (presheafMapOfFunctorOver K (e.inv.functor ⋙ T)
      (by rw [Functor.assoc, hT, ← Functor.assoc, e.inv.w])).app (op (p.obj a))
        (elementValue (e.hom.functor.obj a) (Functor.congr_obj e.hom.w a)) =
      elementValue (T.obj a) (Functor.congr_obj hT a) := by
  let m := T.map (e.unitIso.inv.app a)
  have := e.isHomLift_unitIso_inv_app a
  have hm : (p ⋙ K).IsHomLift (𝟙 (K.obj (p.obj a))) (e.unitIso.inv.app a) := by
    apply IsHomLift.of_fac' (p ⋙ K) _ _
      (congrArg K.obj (IsHomLift.domain_eq p (𝟙 (p.obj a)) (e.unitIso.inv.app a))) rfl
    show K.map (p.map (e.unitIso.inv.app a)) = _
    rw [IsHomLift.fac' p (𝟙 (p.obj a)) (e.unitIso.inv.app a)]
    simp [eqToHom_map]
  have := Functor.isHomLift_map_of_comp_eq hT (𝟙 (K.obj (p.obj a))) (e.unitIso.inv.app a)
  have he := element_eq (e.hom.functor.obj a) (Functor.congr_obj e.hom.w a)
  show elementValue (T.obj (e.inv.functor.obj
    ⟨p.obj a, Discrete.mk (elementValue (e.hom.functor.obj a)
      (Functor.congr_obj e.hom.w a))⟩)) _ = _
  have hb : (T.obj (e.inv.functor.obj (e.hom.functor.obj a))).base = K.obj (p.obj a) :=
    IsHomLift.domain_eq (presheafOfCategories (G ⋙ typeToCat)).p
      (𝟙 (K.obj (p.obj a))) m
  exact (elementValue_congr _ hb
    (congrArg (fun b => T.obj (e.inv.functor.obj b)) he.symm)).trans
      (elementValue_eq_of_vertical (U := K.obj (p.obj a)) hb _ m)

private lemma faithful_of_represented
    {C A : Type*} [Category C] [Category A] {p : A ⥤ C}
    {F : Cᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) : p.Faithful := by
  let _ : e.hom.functor.Faithful := e.toEquivalence.faithful_functor
  refine ⟨fun {x y} f g h => e.hom.functor.map_injective ?_⟩
  apply presheaf_hom_ext F
  have hf := Functor.congr_hom e.hom.w f
  have hg := Functor.congr_hom e.hom.w g
  show (e.hom.functor.map f).base = _
  rw [h] at hf
  exact hf.trans hg.symm

section RepresentedFibre

variable {C D A B' : Type*} [Category C] [Category D] [Category A] [Category B']
    (K : D ⥤ C) (pA : A ⥤ C) (pB : B' ⥤ C)
    (y : D ⥤ B') (M : A ⥤ B')
    (hy : y ⋙ pB = K) (hM : M ⋙ pB = pA)
    {F G : Cᵒᵖ ⥤ Type u} {H : Dᵒᵖ ⥤ Type u}
    (eA : StacksRepresentableCFG.EquivalenceOver pA
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eB : StacksRepresentableCFG.EquivalenceOver pB
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst K pA pB y M)
      (presheafOfCategories (H ⋙ typeToCat)).p)

private def representedFibreMap : H ⟶ K.op ⋙ F :=
  presheafMapOfFunctorOver K
    (eH.inv.functor ⋙ TwoFibreProductOver.snd K pA pB y M ⋙ eA.hom.functor)
    (by rw [Functor.assoc, Functor.assoc, eA.hom.w,
          TwoFibreProductOver.snd_comp_eq, ← TwoFibreProductOver.fst_comp_eq,
          ← Functor.assoc, eH.inv.w])

private lemma representedFibreMap_apply
    (a : TwoFibreProductOver K pA pB y M) :
    (representedFibreMap K pA pB y M eA eH).app (op a.x)
      (elementValue (eH.hom.functor.obj a) (Functor.congr_obj eH.hom.w a)) =
    elementValue (eA.hom.functor.obj a.y)
      ((Functor.congr_obj eA.hom.w a.y).trans (a.hy.trans a.hx.symm)) :=
  presheafMapOfFunctorOver_of_equivalence_apply K eH
    (TwoFibreProductOver.snd K pA pB y M ⋙ eA.hom.functor)
    (by rw [Functor.assoc, eA.hom.w, TwoFibreProductOver.snd_comp_eq,
      TwoFibreProductOver.fst_comp_eq]) a

include hy hM eB in
private lemma representedFibreMap_injective (d : D) :
    Function.Injective ((representedFibreMap K pA pB y M eA eH).app (op d)) := by
  intro x₁ x₂ h
  let a := eH.inv.functor.obj ⟨d, Discrete.mk x₁⟩
  let b := eH.inv.functor.obj ⟨d, Discrete.mk x₂⟩
  have ha : a.x = d := Functor.congr_obj eH.inv.w _
  have hb : b.x = d := Functor.congr_obj eH.inv.w _
  have hya : pA.obj a.y = K.obj d := a.hy.trans (a.hx.symm.trans (congrArg K.obj ha))
  have hyb : pA.obj b.y = K.obj d := b.hy.trans (b.hx.symm.trans (congrArg K.obj hb))
  change elementValue (eA.hom.functor.obj a.y) _ =
    elementValue (eA.hom.functor.obj b.y) _ at h
  let j := isoOfElementValueEq eA a.y b.y hya hyb h
  have hj := isoOfElementValueEq_over eA a.y b.y hya hyb h
  let k : a.x ⟶ b.x := eqToHom (ha.trans hb.symm)
  have hk : K.IsHomLift (𝟙 (K.obj d)) k := by
    apply IsHomLift.of_fac' _ _ _ (congrArg K.obj ha) (congrArg K.obj hb)
    simp [k, eqToHom_map]
  let _ := faithful_of_represented eB
  let m : a ⟶ b := TwoFibreProductOver.Hom.mk' k j.hom (by
    rw [IsHomLift.fac' K (𝟙 (K.obj d)) k,
      IsHomLift.fac' pA (𝟙 (K.obj d)) j.hom]
    simp) (by
    apply pB.map_injective
    have := a.vertical
    have := b.vertical
    have hmj := Functor.isHomLift_map_of_comp_eq hM (𝟙 (K.obj d)) j.hom
    have hky := Functor.isHomLift_map_of_comp_eq hy (𝟙 (K.obj d)) k
    rw [pB.map_comp, pB.map_comp,
      IsHomLift.fac' pB (𝟙 (K.obj d)) (y.map k),
      IsHomLift.fac' pB (𝟙 b.base) b.iso.hom,
      IsHomLift.fac' pB (𝟙 a.base) a.iso.hom,
      IsHomLift.fac' pB (𝟙 (K.obj d)) (M.map j.hom)]
    simp)
  have hm : (TwoFibreProductOver.fst K pA pB y M).IsHomLift (𝟙 d) m := by
    apply IsHomLift.of_fac' _ _ _ ha hb
    show k = _
    simp [k]
  have := Functor.isHomLift_map_of_comp_eq eH.hom.w (𝟙 d) m
  have hh := elementValue_eq_of_vertical
    ((Functor.congr_obj eH.hom.w a).trans ha)
    ((Functor.congr_obj eH.hom.w b).trans hb) (eH.hom.functor.map m)
  exact (equivalence_inv_section eH d x₁).symm.trans
    (hh.trans (equivalence_inv_section eH d x₂))

/-- The compatibility `hq` of a map of presheaves with the representing equivalences, transported
along an identification of the base object. -/
private lemma representedFibreMap_hq_transport
    (q : F ⟶ G)
    (hq : ∀ a, q.app (op (pA.obj a))
      (elementValue (eA.hom.functor.obj a) (Functor.congr_obj eA.hom.w a)) =
      elementValue (eB.hom.functor.obj (M.obj a))
        ((Functor.congr_obj eB.hom.w _).trans (Functor.congr_obj hM a)))
    (a : A) (c : C) (hc : pA.obj a = c) :
    q.app (op c) (elementValue (eA.hom.functor.obj a)
        ((Functor.congr_obj eA.hom.w _).trans hc)) =
      elementValue (eB.hom.functor.obj (M.obj a))
        ((Functor.congr_obj eB.hom.w _).trans ((Functor.congr_obj hM _).trans hc)) := by
  subst c
  exact hq a

include hy hM eB in
private lemma representedFibreMap_condition
    (q : F ⟶ G)
    (hq : ∀ a, q.app (op (pA.obj a))
      (elementValue (eA.hom.functor.obj a) (Functor.congr_obj eA.hom.w a)) =
      elementValue (eB.hom.functor.obj (M.obj a))
        ((Functor.congr_obj eB.hom.w _).trans (Functor.congr_obj hM a)))
    (d : D) (x : H.obj (op d)) :
    q.app (op (K.obj d)) ((representedFibreMap K pA pB y M eA eH).app (op d) x) =
      elementValue (eB.hom.functor.obj (y.obj d))
        ((Functor.congr_obj eB.hom.w _).trans (Functor.congr_obj hy d)) := by
  let a := eH.inv.functor.obj ⟨d, Discrete.mk x⟩
  have ha : a.x = d := Functor.congr_obj eH.inv.w _
  have hya : pA.obj a.y = K.obj d := a.hy.trans (a.hx.symm.trans (congrArg K.obj ha))
  show q.app _ (elementValue (eA.hom.functor.obj a.y) _) = _
  rw [representedFibreMap_hq_transport pA pB M hM eA eB q hq a.y (K.obj d) hya]
  let k : d ⟶ a.x := eqToHom ha.symm
  have hk : K.IsHomLift (𝟙 (K.obj d)) k := by
    apply IsHomLift.of_fac' _ _ _ rfl (congrArg K.obj ha)
    simp [k, eqToHom_map]
  have hky := Functor.isHomLift_map_of_comp_eq hy (𝟙 (K.obj d)) k
  have hia : pB.IsHomLift (𝟙 (K.obj d)) a.iso.hom := by
    have h := a.vertical
    rwa [a.hx.symm.trans (congrArg K.obj ha)] at h
  have hj : pB.IsHomLift (𝟙 (K.obj d)) (y.map k ≫ a.iso.hom) := inferInstance
  have := Functor.isHomLift_map_of_comp_eq eB.hom.w (𝟙 (K.obj d))
    (y.map k ≫ a.iso.hom)
  exact (elementValue_eq_of_vertical (U := K.obj d) _ _
    (eB.hom.functor.map (y.map k ≫ a.iso.hom))).symm

include hy hM eB in
private lemma representedFibreMap_exists
    (q : F ⟶ G)
    (hq : ∀ a, q.app (op (pA.obj a))
      (elementValue (eA.hom.functor.obj a) (Functor.congr_obj eA.hom.w a)) =
      elementValue (eB.hom.functor.obj (M.obj a))
        ((Functor.congr_obj eB.hom.w _).trans (Functor.congr_obj hM a)))
    (d : D) (x : F.obj (op (K.obj d)))
    (hx : q.app (op (K.obj d)) x =
      elementValue (eB.hom.functor.obj (y.obj d))
        ((Functor.congr_obj eB.hom.w _).trans (Functor.congr_obj hy d))) :
    ∃ z, (representedFibreMap K pA pB y M eA eH).app (op d) z = x := by
  let a := eA.inv.functor.obj ⟨K.obj d, Discrete.mk x⟩
  have ha : pA.obj a = K.obj d := Functor.congr_obj eA.inv.w _
  have hval : elementValue (eA.hom.functor.obj a)
      ((Functor.congr_obj eA.hom.w _).trans ha) = x := equivalence_inv_section eA _ x
  have he := representedFibreMap_hq_transport pA pB M hM eA eB q hq a (K.obj d) ha
  rw [hval, hx] at he
  let j := isoOfElementValueEq eB (y.obj d) (M.obj a)
    (Functor.congr_obj hy d) ((Functor.congr_obj hM a).trans ha) he
  have hj := isoOfElementValueEq_over eB (y.obj d) (M.obj a)
    (Functor.congr_obj hy d) ((Functor.congr_obj hM a).trans ha) he
  let b : TwoFibreProductOver K pA pB y M :=
    ⟨K.obj d, d, a, rfl, ha, j, hj⟩
  refine ⟨elementValue (eH.hom.functor.obj b) (Functor.congr_obj eH.hom.w b), ?_⟩
  exact (representedFibreMap_apply K pA pB y M eA eH b).trans hval

end RepresentedFibre

private lemma relocalize_elementValue
    {C : Type*} [Category.{u} C] {U V : C} (f : V ⟶ U)
    {F : (Over V)ᵒᵖ ⥤ Type u}
    (x : (presheafOfCategories (F ⋙ typeToCat)).obj)
    (W : Over V) (hx : x.base = W) :
    elementValue ((PresheafOfCategories.relocalizeToElements f F).obj x)
      (congrArg ((Over.map f).obj) hx) =
      (⟨⟨W.hom, elementValue x hx⟩, rfl⟩ :
        ((OverShriek.relocalizePresheafFunctor f).obj F).obj
          (op ((Over.map f).obj W))) := by
  subst W
  rfl

private lemma relocalize_equivalence_compatible
    {C A B' : Type*} [Category.{u} C] [Category A] [Category B']
    {U V : C} (f : V ⟶ U) (pA : A ⥤ Over V) (pB : B' ⥤ Over V)
    (M : A ⥤ B') (hM : M ⋙ pB = pA)
    {F G : (Over V)ᵒᵖ ⥤ Type u}
    (eA : StacksRepresentableCFG.EquivalenceOver pA
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eB : StacksRepresentableCFG.EquivalenceOver pB
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (q : F ⟶ G)
    (hq : ∀ a, q.app (op (pA.obj a))
      (elementValue (eA.hom.functor.obj a) (Functor.congr_obj eA.hom.w a)) =
      elementValue (eB.hom.functor.obj (M.obj a))
        ((Functor.congr_obj eB.hom.w _).trans (Functor.congr_obj hM a)))
    (a : A) :
    let eA' := (eA.compRight (Over.map f)).trans
      (PresheafOfCategories.relocalizeElementsEquivalenceOver f F)
    let eB' := (eB.compRight (Over.map f)).trans
      (PresheafOfCategories.relocalizeElementsEquivalenceOver f G)
    ((OverShriek.relocalizePresheafFunctor f).map q).app
      (op ((pA ⋙ Over.map f).obj a))
      (elementValue (eA'.hom.functor.obj a) (Functor.congr_obj eA'.hom.w a)) =
      elementValue (eB'.hom.functor.obj (M.obj a))
        ((Functor.congr_obj eB'.hom.w _).trans
          (congrArg ((Over.map f).obj) (Functor.congr_obj hM a))) := by
  dsimp only
  show ((OverShriek.relocalizePresheafFunctor f).map q).app _
      (elementValue ((PresheafOfCategories.relocalizeToElements f F).obj
        (eA.hom.functor.obj a)) _) =
    elementValue ((PresheafOfCategories.relocalizeToElements f G).obj
      (eB.hom.functor.obj (M.obj a))) _
  rw [relocalize_elementValue f _ (pA.obj a) (Functor.congr_obj eA.hom.w a),
    relocalize_elementValue f _ (pA.obj a)
      ((Functor.congr_obj eB.hom.w _).trans (Functor.congr_obj hM a))]
  exact Subtype.ext (congrArg (Sigma.mk (pA.obj a).hom) (hq a))

private def relocalizeStructureMap
    {C : Type*} [Category.{u} C] {U V : C} (f : V ⟶ U)
    (H : (Over V)ᵒᵖ ⥤ Type u) :
    (OverShriek.relocalizePresheafFunctor f).obj H ⟶ yoneda.obj (Over.mk f) where
  app _ := ↾fun s => Over.homMk s.1.1 s.2
  naturality _ _ _ := by ext s; rfl

private lemma relocalize_isPullback
    {C : Type*} [Category.{u} C] {U V : C} (f : V ⟶ U)
    {F G : (Over U)ᵒᵖ ⥤ Type u} {H : (Over V)ᵒᵖ ⥤ Type u}
    (q : F ⟶ G) (a : yoneda.obj (Over.mk f) ⟶ G)
    (r : H ⟶ (Over.map f).op ⋙ F)
    (hr : ∀ W, Function.Injective (r.app (op W)))
    (hc : ∀ W x, q.app (op ((Over.map f).obj W)) (r.app (op W) x) =
      a.app (op ((Over.map f).obj W)) (Over.homMk W.hom rfl))
    (he : ∀ W x, q.app (op ((Over.map f).obj W)) x =
      a.app (op ((Over.map f).obj W)) (Over.homMk W.hom rfl) →
      ∃ z, r.app (op W) z = x) :
    IsPullback (OverShriek.relocalizeOfRestricted f r)
      (relocalizeStructureMap f H) q a := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨W⟩
  obtain ⟨W, φ, rfl⟩ := Over.mk_surjective W
  refine (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr ?_
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨⟨ψ, s⟩, hs⟩
    change W ⟶ V at ψ
    change ψ ≫ f = φ at hs
    subst φ
    show q.app _ (OverShriek.relocalizeDescend f r rfl s) = _
    rw [OverShriek.relocalizeDescend_self]
    exact hc (Over.mk ψ) s
  · intro x y h
    rcases x with ⟨⟨ψ, x⟩, hx⟩
    rcases y with ⟨⟨ψ', y⟩, hy⟩
    have hψ : ψ = ψ' := congrArg (fun k => k.left) h.2
    subst ψ'
    change W ⟶ V at ψ
    change ψ ≫ f = φ at hx
    subst φ
    apply Subtype.ext
    apply congrArg (Sigma.mk ψ)
    apply hr (Over.mk ψ)
    have hh := h.1
    change OverShriek.relocalizeDescend f r rfl x =
      OverShriek.relocalizeDescend f r rfl y at hh
    rw [OverShriek.relocalizeDescend_self, OverShriek.relocalizeDescend_self] at hh
    exact hh
  · intro x k hk
    obtain ⟨ψ, hψ, rfl⟩ := Over.homMk_surjective k
    change W ⟶ V at ψ
    change ψ ≫ f = φ at hψ
    subst φ
    obtain ⟨z, hz⟩ := he (Over.mk ψ) x hk
    refine ⟨⟨⟨ψ, z⟩, rfl⟩, ?_, rfl⟩
    show OverShriek.relocalizeDescend f r rfl z = x
    rw [OverShriek.relocalizeDescend_self]
    exact hz

private lemma isSurjective_iso_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X' ≅ X) (f : X ⟶ Y) (hf : AlgebraicGeometry.Space.IsSurjective B S hS f) :
    AlgebraicGeometry.Space.IsSurjective B S hS (e.hom ≫ f) := by
  intro y
  obtain ⟨x, hx⟩ := hf y
  refine ⟨AlgebraicGeometry.Space.pointsMap B S hS X e.inv x, ?_⟩
  rw [AlgebraicGeometry.Space.pointsMap_comp]
  show AlgebraicGeometry.Space.pointsMap B S hS X f
    ((AlgebraicGeometry.Space.pointsMap B S hS X' e.hom ∘
      AlgebraicGeometry.Space.pointsMap B S hS X e.inv) x) = y
  rw [← AlgebraicGeometry.Space.pointsMap_comp, e.inv_hom_id,
    AlgebraicGeometry.Space.pointsMap_id]
  exact hx

private lemma isEtale_iso_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X' ≅ X) (f : X ⟶ Y) (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    AlgebraicGeometry.Space.IsEtale B S hS (e.hom ≫ f) := by
  intro U a ha
  have he := MorphismProperty.RespectsIso.postcomp
    ((MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf) e.hom a ha
  simpa only [Category.assoc] using hf U (a ≫ e.hom) he

private lemma holdsOnEveryEtaleChart_iso_comp
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    {X X' Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X' ≅ X) (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P f) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P (e.hom ≫ f) := by
  intro U V a b k ha hb hk
  exact hf U V (a ≫ e.hom) b k (MorphismProperty.RespectsIso.postcomp
    ((MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf) e.hom a ha) hb
    (by simpa only [Category.assoc] using hk)

/-- A relative property local on the source descends along a representable
covering of the intermediate fibred category. -/
@[stacks 06M2]
public theorem hasRelativeProperty_of_comp_of_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicGeometry.AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicGeometry.Space.Topology.fppf.precoverage B S hS)]
    (τ : AlgebraicGeometry.Space.Topology)
    (hτ : τ = .etale ∨ τ = .smooth ∨ τ = .syntomic ∨ τ = .fppf)
    [P.IsLocalAtSource (τ.precoverage B S hS)]
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (AlgebraicGeometry.BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hcover :
      ∀ (U : AlgebraicGeometry.BigFppfOver B S hS)
        (y : AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.based.obj)
        (_hy : y ⋙ 𝒴.based.p = Over.map U.hom)
        (F : (AlgebraicGeometry.BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : AlgebraicGeometry.IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.based.p 𝒴.based.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        let a := AlgebraicGeometry.algebraicSpaceMap B S hS U
          ((AlgebraicGeometry.spacesOverSmallerBaseFunctor B U.left.1 S U.left.2
            hS U.hom).obj ⟨F, hF⟩)
        (AlgebraicGeometry.Space.IsSurjective B S hS a.hom ∧
          (match τ with
          | .etale => AlgebraicGeometry.Space.IsEtale B S hS a.hom
          | .smooth => AlgebraicGeometry.Space.IsSmooth B S hS a.hom
          | .syntomic => AlgebraicGeometry.Space.IsSyntomic B S hS a.hom
          | .fppf =>
              AlgebraicGeometry.Space.IsFlat B S hS a.hom ∧
                AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS a.hom
          | .fpqc => False)))
    (hcomp : AlgebraicGeometry.Stack.HasRelativeProperty B S hS P (f ≫ g)
      (AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp B S hS f g hf hg)) :
    AlgebraicGeometry.Stack.HasRelativeProperty B S hS P g hg := by
  classical
  dsimp only [AlgebraicGeometry.Stack.HasRelativeProperty] at hcomp ⊢
  intro U z hz Fg hFg hEg
  have hreprComp := AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp B S hS f g hf hg
  obtain ⟨Fcomp, hFcomp, eComp⟩ := hreprComp U z hz
  have hPcomp := hcomp U z hz Fcomp hFcomp eComp
  obtain ⟨eFg⟩ := hEg
  obtain ⟨eComp⟩ := eComp
  let M := TwoFibreProductOver.splitSndProjection (Over.map U.hom) 𝒳.based.p 𝒴.based.p
    𝒵.based.p z (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor g)
    (CatFiberedInGroupoids.homFunctor_comp_p f)
  have hMU : M ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒴.based.p 𝒵.based.p z
        (CatFiberedInGroupoids.homFunctor g) =
      TwoFibreProductOver.fst (Over.map U.hom) 𝒳.based.p 𝒵.based.p z
        (CatFiberedInGroupoids.homFunctor (f ≫ g)) :=
    TwoFibreProductOver.splitSndProjection_comp_fst (Over.map U.hom) 𝒳.based.p 𝒴.based.p
      𝒵.based.p z (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor g)
      (CatFiberedInGroupoids.homFunctor_comp_p f)
  let H := eComp.inv.functor ⋙ M ⋙ eFg.hom.functor
  have hH : H ⋙ (presheafOfCategories (Fg ⋙ typeToCat)).p =
      (presheafOfCategories (Fcomp ⋙ typeToCat)).p :=
    calc H ⋙ (presheafOfCategories (Fg ⋙ typeToCat)).p
        = eComp.inv.functor ⋙ M ⋙ eFg.hom.functor ⋙
            (presheafOfCategories (Fg ⋙ typeToCat)).p := rfl
      _ = eComp.inv.functor ⋙ M ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒴.based.p
            𝒵.based.p z (CatFiberedInGroupoids.homFunctor g) :=
          congrArg (fun L => eComp.inv.functor ⋙ M ⋙ L) eFg.hom.w
      _ = eComp.inv.functor ⋙ TwoFibreProductOver.fst (Over.map U.hom) 𝒳.based.p
            𝒵.based.p z (CatFiberedInGroupoids.homFunctor (f ≫ g)) :=
          congrArg (fun L => eComp.inv.functor ⋙ L) hMU
      _ = (presheafOfCategories (Fcomp ⋙ typeToCat)).p := eComp.inv.w
  let qU : (⟨Fcomp, hFcomp⟩ : AlgebraicGeometry.AlgebraicSpaces B U.left.1 U.left.2) ⟶
      ⟨Fg, hFg⟩ := ObjectProperty.homMk (presheafMapOfFunctor H hH)
  let E := AlgebraicGeometry.spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom
  let q : (⟨(E.obj ⟨Fcomp, hFcomp⟩).1.left,
      (E.obj ⟨Fcomp, hFcomp⟩).property⟩ :
      AlgebraicGeometry.AlgebraicSpaces B S hS) ⟶
    ⟨(E.obj ⟨Fg, hFg⟩).1.left,
      (E.obj ⟨Fg, hFg⟩).property⟩ :=
    ObjectProperty.homMk (E.map qU).hom.left
  have hqcomp : q ≫ AlgebraicGeometry.algebraicSpaceMap B S hS U
      (E.obj ⟨Fg, hFg⟩) =
      AlgebraicGeometry.algebraicSpaceMap B S hS U (E.obj ⟨Fcomp, hFcomp⟩) := by
    apply ObjectProperty.hom_ext
    exact Over.w (E.map qU).hom
  apply relativeProperty_of_covering_precomposition B S hS P τ q
    (AlgebraicGeometry.algebraicSpaceMap B S hS U (E.obj ⟨Fg, hFg⟩))
    ?_ (by rwa [hqcomp])
  obtain ⟨V, a, haSurj, haEtale⟩ :=
    (E.obj ⟨Fg, hFg⟩).property.exists_atlas
  let i := AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom
  let R := OverShriek.relocalizePresheafFunctor U.hom
  let aR := a ≫ (i.app ⟨Fg, hFg⟩).hom
  let eAS₀ := (eComp.compRight (Over.map U.hom)).trans
    (PresheafOfCategories.relocalizeElementsEquivalenceOver U.hom Fcomp)
  let eBS₀ := (eFg.compRight (Over.map U.hom)).trans
    (PresheafOfCategories.relocalizeElementsEquivalenceOver U.hom Fg)
  let pA := TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.based.p 𝒵.based.p z
    (CatFiberedInGroupoids.homFunctor (f ≫ g))
  let pB := TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒴.based.p 𝒵.based.p z
    (CatFiberedInGroupoids.homFunctor g)
  let eAS : StacksRepresentableCFG.EquivalenceOver pA
      (presheafOfCategories (R.obj Fcomp ⋙ typeToCat)).p :=
    equivalenceOverChangeProjection eAS₀ TwoFibreProductOver.fst_comp_eq
  let eBS : StacksRepresentableCFG.EquivalenceOver pB
      (presheafOfCategories (R.obj Fg ⋙ typeToCat)).p :=
    equivalenceOverChangeProjection eBS₀ TwoFibreProductOver.fst_comp_eq
  let K := Over.map V.hom
  let tR := sectionBasedFunctor (BasedCategory.ofFunctor K) (R.obj Fg)
    (fun W => aR.app (op (K.obj W)) (Over.homMk W.hom rfl)) (by
      intro W W' k
      have hm : K.map k ≫ Over.homMk W'.hom rfl = Over.homMk W.hom rfl :=
        Over.OverMorphism.ext k.w
      have hn := NatTrans.naturality_apply aR (K.map k).op (Over.homMk W'.hom rfl)
      change aR.app _ (K.map k ≫ Over.homMk W'.hom rfl) = _ at hn
      rwa [hm] at hn)
  let t := tR.toFunctor ⋙ eBS.inv.functor
  have ht : t ⋙ pB = K := by
    rw [Functor.assoc, eBS.inv.w, tR.w]
    rfl
  have hyt : (t ⋙ TwoFibreProductOver.snd (Over.map U.hom) 𝒴.based.p
      𝒵.based.p z (CatFiberedInGroupoids.homFunctor g)) ⋙ 𝒴.based.p = K := by
    rw [Functor.assoc, TwoFibreProductOver.snd_comp_eq, ht]
  obtain ⟨Fchart, hFchart, eChart⟩ := hf V
    (t ⋙ TwoFibreProductOver.snd (Over.map U.hom) 𝒴.based.p
      𝒵.based.p z (CatFiberedInGroupoids.homFunctor g)) hyt
  have hChartCover := hcover V
    (t ⋙ TwoFibreProductOver.snd (Over.map U.hom) 𝒴.based.p
      𝒵.based.p z (CatFiberedInGroupoids.homFunctor g)) hyt
    Fchart hFchart eChart
  have hM : M ⋙ pB = pA :=
    TwoFibreProductOver.splitSndProjection_comp_structureFunctor (Over.map U.hom)
      𝒳.based.p 𝒴.based.p 𝒵.based.p z (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor g) (CatFiberedInGroupoids.homFunctor_comp_p f)
  have hpA : pA.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids (Over.map U.hom) 𝒳.based.p 𝒵.based.p z
      (CatFiberedInGroupoids.homFunctor (f ≫ g))
      (Functor.IsFiberedInGroupoids.over_map U.hom) 𝒳.isFiberedInGroupoids
      𝒵.isFiberedInGroupoids hz (CatFiberedInGroupoids.homFunctor_comp_p (f ≫ g))
  have hpB : pB.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids (Over.map U.hom) 𝒴.based.p 𝒵.based.p z
      (CatFiberedInGroupoids.homFunctor g)
      (Functor.IsFiberedInGroupoids.over_map U.hom) 𝒴.isFiberedInGroupoids
      𝒵.isFiberedInGroupoids hz (CatFiberedInGroupoids.homFunctor_comp_p g)
  have hpR := TwoFibreProductOver.isFiberedInGroupoids pB 𝒳.based.p 𝒴.based.p
    (TwoFibreProductOver.snd (Over.map U.hom) 𝒴.based.p 𝒵.based.p z
      (CatFiberedInGroupoids.homFunctor g)) (CatFiberedInGroupoids.homFunctor f)
    hpB 𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids
    TwoFibreProductOver.snd_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p f)
  have h₁ := PresheafOfCategories.isFiberedInGroupoids_fst_overMap_of V.hom (G := t)
    (F := M) hpA hpB ht hM
  have h₂ := PresheafOfCategories.isFiberedInGroupoids_fst_overMap_of V.hom (G := t)
    (F := TwoFibreProductOver.fst pB 𝒳.based.p 𝒴.based.p
      (TwoFibreProductOver.snd (Over.map U.hom) 𝒴.based.p 𝒵.based.p z
        (CatFiberedInGroupoids.homFunctor g)) (CatFiberedInGroupoids.homFunctor f))
    hpR hpB ht TwoFibreProductOver.fst_comp_eq
  obtain ⟨ePull⟩ := TwoFibreProductOver.nonempty_equivalenceOver_baseChange_splitSnd
    (Over.map U.hom) 𝒳.based.p 𝒴.based.p 𝒵.based.p z
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor g)
    (CatFiberedInGroupoids.homFunctor_comp_p f) (Over.map V.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g) t ht
    (Functor.IsFiberedInGroupoids.over_map V.hom) hpA hpR h₁ h₂
  let eH := ePull.trans eChart.some
  let r := representedFibreMap K pA pB t M eAS eH
  have hqR : ∀ x, (R.map qU.hom).app (op (pA.obj x))
      (elementValue (eAS.hom.functor.obj x) (Functor.congr_obj eAS.hom.w x)) =
      elementValue (eBS.hom.functor.obj (M.obj x))
        ((Functor.congr_obj eBS.hom.w _).trans (Functor.congr_obj hM x)) := by
    intro x
    have hMe : (M ⋙ eFg.hom.functor) ⋙ (presheafOfCategories (Fg ⋙ typeToCat)).p =
        TwoFibreProductOver.fst (Over.map U.hom) 𝒳.based.p 𝒵.based.p z
          (CatFiberedInGroupoids.homFunctor (f ≫ g)) :=
      (congrArg (fun L => M ⋙ L) eFg.hom.w).trans hMU
    have hqU := fun x => presheafMapOfFunctor_of_equivalence_apply eComp
      (M ⋙ eFg.hom.functor) hMe x
    have hh := relocalize_equivalence_compatible U.hom _ _ M hMU
      eComp eFg qU.hom hqU x
    have htransport : ∀ W (hW : (Over.map U.hom).obj x.x = W),
        (R.map qU.hom).app (op W)
          (elementValue (eAS.hom.functor.obj x)
            ((Functor.congr_obj eAS₀.hom.w x).trans hW)) =
        elementValue (eBS.hom.functor.obj (M.obj x))
          ((Functor.congr_obj eBS₀.hom.w _).trans
            ((congrArg ((Over.map U.hom).obj) (Functor.congr_obj hMU x)).trans hW)) := by
      rintro W rfl
      exact hh
    exact htransport (pA.obj x) x.hx
  have htR : ∀ W,
      elementValue (eBS.hom.functor.obj (t.obj W))
        ((Functor.congr_obj eBS.hom.w _).trans (Functor.congr_obj ht W)) =
        aR.app (op (K.obj W)) (Over.homMk W.hom rfl) :=
    fun W => equivalence_inv_section eBS (K.obj W) _
  have hpb := relocalize_isPullback V.hom (R.map qU.hom) aR r
    (representedFibreMap_injective K pA pB t M ht hM eAS eBS eH)
    (fun W x => (representedFibreMap_condition K pA pB t M ht hM eAS eBS eH
      (R.map qU.hom) hqR W x).trans (htR W))
    (fun W x hx => representedFibreMap_exists K pA pB t M ht hM eAS eBS eH
      (R.map qU.hom) hqR W x (hx.trans (htR W).symm))
  let EV := AlgebraicGeometry.spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom
  let j := (AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso B V.left.1 S V.left.2
    hS V.hom).app ⟨Fchart, hFchart⟩
  let d := AlgebraicGeometry.algebraicSpaceMap B S hS V (EV.obj ⟨Fchart, hFchart⟩)
  let b := j.hom ≫ OverShriek.relocalizeOfRestricted V.hom r ≫
    (i.app ⟨Fcomp, hFcomp⟩).inv
  have hstruct : j.hom ≫ relocalizeStructureMap V.hom Fchart = d.hom := by
    ext W s
    have hh := AlgebraicGeometry.spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B V.left.1 S V.left.2 hS V.hom ⟨Fchart, hFchart⟩ W (j.hom.app W s)
    change d.hom.app W (j.inv.app W (j.hom.app W s)) = _ at hh
    have hj : j.inv.app W (j.hom.app W s) = s :=
      congrArg (fun k => k s) (NatTrans.congr_app j.hom_inv_id W)
    rw [hj] at hh
    exact hh.symm
  have hpbS : IsPullback b d.hom q.hom a := by
    apply hpb.of_iso' j (i.app ⟨Fcomp, hFcomp⟩) (Iso.refl _) (i.app ⟨Fg, hFg⟩)
    · simp only [b, Functor.comp_obj, ObjectProperty.ι_obj, Over.forget_obj, Iso.app_hom]
      exact (Category.comp_id _).symm
    · simpa only [Iso.refl_hom, Category.comp_id] using hstruct
    · exact (i.hom.naturality qU).symm
    · rfl
  let e := hpbS.isoPullback
  have he : e.inv ≫ d.hom = CategoryTheory.Limits.pullback.snd q.hom a :=
    hpbS.isoPullback_inv_snd
  let e₂ := hpbS.flip.isoPullback
  have he₂ : e₂.inv ≫ d.hom = CategoryTheory.Limits.pullback.fst a q.hom :=
    hpbS.flip.isoPullback_inv_fst
  have hsurj : AlgebraicGeometry.Space.IsSurjective B S hS
      (CategoryTheory.Limits.pullback.snd q.hom a) := by
    rw [← he]
    exact isSurjective_iso_comp B S hS e.symm d.hom hChartCover.1
  apply isCovering_singleton_of_surjective B S hS τ q
    (isSurjective_of_surjective_chart_pullback B S hS q V a haSurj haEtale hsurj)
  have hgeom := hChartCover.2
  cases τ with
  | fpqc => exact hgeom.elim
  | etale =>
    apply isEtale_of_etale_chart_pullback B S hS q V a haSurj haEtale
    rw [← he]
    exact isEtale_iso_comp B S hS e.symm d.hom hgeom
  | smooth =>
    apply isSmooth_of_smooth_chart_pullback B S hS q V a haSurj haEtale
    rw [← he]
    exact holdsOnEveryEtaleChart_iso_comp B S hS _ e.symm d.hom hgeom
  | syntomic =>
    apply isSyntomic_of_syntomic_chart_pullback B S hS q V a haSurj haEtale
    rw [← he₂]
    exact holdsOnEveryEtaleChart_iso_comp B S hS _ e₂.symm d.hom hgeom
  | fppf =>
    constructor
    · apply isFlat_of_flat_chart_pullback B S hS q V a haSurj haEtale
      rw [← he₂]
      exact holdsOnEveryEtaleChart_iso_comp B S hS _ e₂.symm d.hom hgeom.1
    · apply isLocallyOfFinitePresentation_of_chart_pullback B S hS q V a haSurj haEtale
      rw [← he₂]
      exact holdsOnEveryEtaleChart_iso_comp B S hS _ e₂.symm d.hom hgeom.2

end AlgebraicGeometry.Stack

end
