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
public import StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.ResidueFieldPoints
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange.ResidueFieldPoints

/-!
# Lifting sections of a base change of a versal object

Preparations for `Deformation.Artin.BaseChange.isSmoothAt_baseChange_of_isVersalAt`:
transport of deformation morphisms, invariance of smoothness under based equivalences, and the
lifting of sections of the two-fibre product from a smooth lift of deformations.

## Main definitions

* `Deformation.Artin.BaseChange.BaseChangeEquivalence` records an equivalence between the
  two-fibre product and a representing algebraic-space presheaf.

## Implementation notes

The smoothness statement is split so that no single declaration exhausts the elaborator's
budget: `exists_baseChange_section_of_deformation_objects` carries the passage between a
deformation object and the corresponding object of a predeformation category, which is where
`Deformation.Artin.predeformationCategory` has to be unfolded.

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
attribute [local implicit_reducible] CategoryTheory.Over.post
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

@[implicit_reducible] private def transportDeformationMorphism
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a a' b b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a = a') (hb : b = b') (f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a' b' := ha ▸ hb ▸ f

private lemma transportDeformationMorphism_arrow
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a a' b b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a = a') (hb : b = b') (f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    (transportDeformationMorphism ha hb f).arrow =
      eqToHom (congrArg Deformation.Artin.DeformationObject.point hb).symm ≫ f.arrow ≫
        eqToHom (congrArg Deformation.Artin.DeformationObject.point ha) := by
  cases ha
  cases hb
  simp [transportDeformationMorphism]

private lemma transportDeformationMorphism_ringHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a a' b b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a = a') (hb : b = b') (f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    (transportDeformationMorphism ha hb f).ringHom =
      eqToHom (congrArg Deformation.Artin.DeformationObject.algebra ha).symm ≫ f.ringHom ≫
        eqToHom (congrArg Deformation.Artin.DeformationObject.algebra hb) := by
  cases ha
  cases hb
  simp [transportDeformationMorphism]

private lemma transportDeformationMorphism_surjective
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a a' b b' : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (ha : a = a') (hb : b = b') (f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b)
    (hf : Function.Surjective f.ringHom.hom) :
    Function.Surjective (transportDeformationMorphism ha hb f).ringHom.hom := by
  cases ha
  cases hb
  exact hf

private lemma deformationMorphism_ringHom_of_homLift
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    {a b : P.carrier} (f : a ⟶ b)
    {A D : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (g : A ⟶ D) (hg : P.projection.IsHomLift g f)
    (ha : (P.objects a).algebra = A) (hb : (P.objects b).algebra = D) :
    (P.morphisms a b f).ringHom = eqToHom ha ≫ g ≫ eqToHom hb.symm := by
  rw [← P.morphism_projection f, IsHomLift.fac' P.projection g f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- Smoothness of the induced deformation functor supplies a compatible
lift of the underlying objects and arrows over the specified Artinian algebra. -/
private lemma exists_deformation_lift_of_isSmooth
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
    (qX : X ⥤ Over S) (qY : Y ⥤ Over S) (G : X ⥤ Y)
    (hG : G ⋙ qY = qX) (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hsmooth : Deformation.IsSmooth
      (Deformation.Artin.mapPredeformationCategory iΛ qX qY G hG x₀ hx₀).toBasedFunctor) :
    let PX := Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀
    let hy₀ := Deformation.Artin.imageBasePoint (qY := qY) iΛ qX G hG x₀ hx₀
    let PY := Deformation.Artin.predeformationCategory iΛ qY (G.obj x₀) hy₀
    ∀ (a : PX.carrier) (b : PY.carrier)
      (i : Deformation.Artin.DeformationMorphism iΛ qY (G.obj x₀) hy₀ (PY.objects b)
        (mapDeformationObject iΛ qX qY G hG x₀ hx₀ (PX.objects a))),
      Function.Surjective i.ringHom.hom →
      ∃ (c : PX.carrier) (hc : (PX.objects c).algebra = (PY.objects b).algebra)
        (h : Deformation.Artin.DeformationMorphism iΛ qX x₀ hx₀ (PX.objects c) (PX.objects a))
        (j : Deformation.Artin.DeformationMorphism iΛ qY (G.obj x₀) hy₀
          (mapDeformationObject iΛ qX qY G hG x₀ hx₀ (PX.objects c)) (PY.objects b)),
        h.ringHom = eqToHom hc ≫ i.ringHom ∧ j.ringHom = eqToHom hc ∧
          G.map h.arrow = i.arrow ≫ j.arrow := by
  let PX := Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀
  let hy₀ := Deformation.Artin.imageBasePoint (qY := qY) iΛ qX G hG x₀ hx₀
  let PY := Deformation.Artin.predeformationCategory iΛ qY (G.obj x₀) hy₀
  let H := Deformation.Artin.mapPredeformationCategory iΛ qX qY G hG x₀ hx₀
  dsimp only
  intro a b i hi
  have ho (c : PX.carrier) : PY.objects (H.toFunctor.obj c) =
      mapDeformationObject iΛ qX qY G hG x₀ hx₀ (PX.objects c) :=
    mapPredeformationCategory_objects iΛ qX qY G hG x₀ hx₀ c
  let i' := transportDeformationMorphism rfl (ho a).symm i
  let g : b ⟶ H.toFunctor.obj a := (PY.morphisms _ _).symm i'
  have hg : PY.projection.IsHomLift i'.ringHom g := by
    apply IsHomLift.of_fac _ _ _ (PY.object_projection b)
      (PY.object_projection (H.toFunctor.obj a))
    simpa only [g, Equiv.apply_symm_apply] using (PY.morphism_projection g).symm
  have hi' : Function.Surjective i'.ringHom.hom :=
    transportDeformationMorphism_surjective rfl (ho a).symm i hi
  dsimp only [Deformation.IsSmooth, Deformation.Artin.InducedPredeformationFunctor.toBasedFunctor,
    BasedCategory.ofFunctor] at hsmooth
  obtain ⟨c, h, j, hh, hj, hcomm⟩ := hsmooth i'.ringHom hi' b a g hg
  let : PX.projection.IsHomLift i'.ringHom h := hh
  have hc : (PX.objects c).algebra = (PY.objects b).algebra :=
    (PX.object_projection c).symm.trans (IsHomLift.domain_eq PX.projection i'.ringHom h)
  let h' := PX.morphisms c a h
  let j' := transportDeformationMorphism (ho c) rfl (PY.morphisms _ _ j)
  refine ⟨c, hc, h', j', ?_, ?_, ?_⟩
  · have hr := deformationMorphism_ringHom_of_homLift PX h i'.ringHom hh hc
      (congrArg Deformation.Artin.DeformationObject.algebra (ho a)).symm
    dsimp only [h']
    rw [hr]
    simp only [i', transportDeformationMorphism_ringHom, eqToHom_refl,
      Category.id_comp, Category.assoc, eqToHom_trans, Category.comp_id]
  · have hr := deformationMorphism_ringHom_of_homLift PY j
      (𝟙 (PY.objects b).algebra) hj
      ((congrArg Deformation.Artin.DeformationObject.algebra (ho c)).trans hc) rfl
    dsimp only [j']
    rw [transportDeformationMorphism_ringHom, hr]
    simp only [eqToHom_refl, Category.comp_id,
      eqToHom_trans]
  · have he := congrArg (fun f => (PY.morphisms _ _ f).arrow) hcomm
    change (PY.morphisms _ _ (H.toFunctor.map h)).arrow =
      (PY.morphisms _ _ (j ≫ g)).arrow at he
    rw [H.morphism_arrow, PY.reversed_composition] at he
    have hg' : (PY.morphisms _ _ g).arrow = eqToHom (H.object_point a) ≫ i.arrow := by
      simp only [g, Equiv.apply_symm_apply, i', transportDeformationMorphism_arrow,
        eqToHom_refl, Category.comp_id]
    rw [hg'] at he
    have hj' : j'.arrow = (PY.morphisms _ _ j).arrow ≫ eqToHom (H.object_point c) := by
      simp only [j', transportDeformationMorphism_arrow, eqToHom_refl, Category.id_comp]
      rfl
    rw [hj']
    apply (cancel_epi (eqToHom (H.object_point a))).mp
    have he' := congrArg (fun f => f ≫ eqToHom (H.object_point c)) he
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using he'

private lemma isHomLift_of_comp_of_injective_obj
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    (p : D ⥤ C) (Q : C ⥤ E) [Q.Faithful] (hQ : Function.Injective Q.obj)
    {A B : C} (f : A ⟶ B) {a b : D} (g : a ⟶ b)
    (hg : (p ⋙ Q).IsHomLift (Q.map f) g) : p.IsHomLift f g := by
  have ha : p.obj a = A := hQ (IsHomLift.domain_eq (p ⋙ Q) (Q.map f) g)
  have hb : p.obj b = B := hQ (IsHomLift.codomain_eq (p ⋙ Q) (Q.map f) g)
  apply IsHomLift.of_fac' p f g ha hb
  apply Q.map_injective
  simpa only [Functor.map_comp, eqToHom_map, Functor.comp_obj, Functor.comp_map] using
    (IsHomLift.fac' (p ⋙ Q) (Q.map f) g)

private lemma overPost_injective_obj
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Function.Injective (Over.post (X := B.obj hS) B.inclusion).obj := by
  intro A D h
  have hl : A.left = D.left := by
    ext1
    exact congrArg Over.left h
  rcases A with ⟨A, ⟨⟨⟩⟩, a⟩
  rcases D with ⟨D, ⟨⟨⟩⟩, d⟩
  cases hl
  congr 1
  apply B.inclusion.map_injective
  have hh := congrArg (fun z : Over (B.inclusion.obj (B.obj hS)) =>
    (⟨z.left, z.hom⟩ : Σ X : Scheme, X ⟶ B.inclusion.obj (B.obj hS))) h
  simpa [Over.post] using hh

private lemma reflectsIsomorphisms_of_isFiberedInGroupoids
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) : p.ReflectsIsomorphisms where
  reflects f hf := by
    let := hf
    let := hp.isStronglyCartesian_homLift (p.map f) f
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map f) f

private lemma isIso_specMap_artinian_eqToHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A D : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = D) :
    IsIso (Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom)) := by
  cases h
  show IsIso (Spec.map (𝟙 (CommRingCat.of A)))
  infer_instance

private lemma specMap_artinian_eqToHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A D : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (h : A = D) :
    Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) =
      eqToHom (congrArg (fun R : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k =>
        Spec (.of R)) h).symm := by
  cases h
  show Spec.map (𝟙 (CommRingCat.of A)) = eqToHom rfl
  simp

private lemma deformationMorphism_isHomLift_id_of_ringHom_eqToHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b)
    (h : a.algebra = b.algebra) (hf : f.ringHom = eqToHom h) :
    q.IsHomLift (𝟙 (q.obj b.point)) f.arrow := by
  have hq : q.obj a.point = q.obj b.point := a.base.trans
    ((congrArg (fun R : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k =>
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ)) h).trans
        b.base.symm)
  apply IsHomLift.of_fac' q (𝟙 (q.obj b.point)) f.arrow rfl hq
  apply Over.OverMorphism.ext
  have hm := f.arrow_base
  rw [hf, specMap_artinian_eqToHom] at hm
  have hm' := congrArg (fun g => eqToHom (congrArg Over.left b.base) ≫ g ≫
    eqToHom (congrArg Over.left a.base).symm) hm
  simpa only [Over.comp_left, Over.id_left, Over.eqToHom_left,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id] using hm'

/-- A deformation arrow over an identification of Artinian algebras is an
isomorphism whenever the original category reflects base isomorphisms. -/
private lemma isIso_deformationMorphism_arrow_of_ringHom_eqToHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} [q.ReflectsIsomorphisms]
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (f : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b)
    (h : a.algebra = b.algebra) (hf : f.ringHom = eqToHom h) : IsIso f.arrow := by
  have hi : IsIso (Spec.map (CommRingCat.ofHom f.ringHom.hom.toRingHom)) := by
    rw [hf]
    exact isIso_specMap_artinian_eqToHom h
  have hmap : (q.map f.arrow).left = eqToHom (congrArg Over.left b.base) ≫
      Spec.map (CommRingCat.ofHom f.ringHom.hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm := by
    rw [← f.arrow_base]
    simp only [← Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  let : IsIso (q.map f.arrow).left := by rw [hmap]; infer_instance
  let : IsIso ((Over.forget S).map (q.map f.arrow)) :=
    show IsIso (q.map f.arrow).left from inferInstance
  let : IsIso (q.map f.arrow) := isIso_of_reflects_iso (q.map f.arrow) (Over.forget S)
  exact isIso_of_reflects_iso f.arrow q

/-- A vertical natural isomorphism preserves the infinitesimal lifting property. -/
private lemma isSmooth_of_basedIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓧 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓨 : BasedCategory.{v₂, u₂} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {F G : BasedFunctor 𝓧 𝓨} (e : F ≅ G) (hF : Deformation.IsSmooth F) :
    Deformation.IsSmooth G := by
  intro B A f hf y x g hg
  have hx : 𝓧.p.obj x = A :=
    (G.w_obj x).symm.trans (IsHomLift.codomain_eq 𝓨.p f g)
  have hei : 𝓨.p.IsHomLift (𝟙 A) (e.inv.app x) := e.inv.isHomLift hx
  let := hg
  let := hei
  have hg' : 𝓨.p.IsHomLift f (g ≫ e.inv.app x) :=
    IsHomLift.comp_lift_id_right 𝓨.p f g (e.inv.app x)
  obtain ⟨x', h, a, hh, ha, hcomm⟩ := hF f hf y x (g ≫ e.inv.app x) hg'
  have hx' : 𝓧.p.obj x' = B := IsHomLift.domain_eq 𝓧.p f h
  have hei' : 𝓨.p.IsHomLift (𝟙 B) (e.inv.app x') := e.inv.isHomLift hx'
  have ha' : 𝓨.p.IsHomLift (𝟙 B) (e.inv.app x' ≫ a) := by
    let := hei'
    let := ha
    infer_instance
  refine ⟨x', h, e.inv.app x' ≫ a, hh, ha', ?_⟩
  have hn := e.inv.toNatTrans.naturality h
  change G.map h ≫ e.inv.app x = e.inv.app x' ≫ F.map h at hn
  apply (cancel_mono (e.inv.app x)).mp
  rw [hn, hcomm]
  simp only [Category.assoc]

private theorem isSmooth_comp_basedEquivalence
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓧 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓨 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓩 : BasedCategory.{v₃, u₃} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (E : BasedCategory.Equivalence 𝓧 𝓨)
    (g : BasedFunctor 𝓨 𝓩)
    (hg : Deformation.IsSmooth g) :
    Deformation.IsSmooth (BasedFunctor.comp E.functor g) := by
  dsimp [Deformation.IsSmooth] at hg ⊢
  intro B A f₀ hf y x h hlift
  obtain ⟨z, hz, a, hhz, haz, hcomm⟩ := hg f₀ hf y (E.functor.obj x) h hlift
  have hzB : 𝓨.p.obj z = B := IsHomLift.domain_eq 𝓨.p f₀ hz
  let i : E.functor.obj (E.inverse.obj z) ⟶ z := E.counitIso.hom.app z
  have hi : 𝓨.p.IsHomLift (𝟙 B) i := E.counitIso.hom.isHomLift hzB
  let m : E.functor.obj (E.inverse.obj z) ⟶ E.functor.obj x := i ≫ hz
  let h' : E.inverse.obj z ⟶ x := E.equiv.functor.preimage m
  have hmap : E.functor.map h' = m := by
    show E.equiv.functor.map h' = m
    simpa only [h'] using E.equiv.functor.map_preimage m
  have hm : 𝓧.p.IsHomLift f₀ h' := by
    let : 𝓨.p.IsHomLift f₀ (E.functor.map h') := by rw [hmap]; infer_instance
    exact E.functor.isHomLift_map f₀ h'
  let a' := g.map i ≫ a
  have ha' : 𝓩.p.IsHomLift (𝟙 B) a' := by
    let : 𝓩.p.IsHomLift (𝟙 B) (g.map i) := g.preserves_isHomLift (𝟙 B) i
    let : 𝓩.p.IsHomLift (𝟙 B) a := haz
    dsimp [a']
    infer_instance
  refine ⟨E.inverse.obj z, h', a', hm, ha', ?_⟩
  show g.map (E.functor.map h') = (g.map i ≫ a) ≫ h
  rw [hmap]
  dsimp [m]
  rw [Functor.map_comp, hcomm]
  simp only [Category.assoc]
  rfl

private theorem isSmooth_of_comp_basedEquivalence
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓧 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓨 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓩 : BasedCategory.{v₃, u₃} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (E : BasedCategory.Equivalence 𝓧 𝓨)
    (g : BasedFunctor 𝓨 𝓩)
    (h : Deformation.IsSmooth (BasedFunctor.comp E.functor g)) :
    Deformation.IsSmooth g := by
  dsimp [Deformation.IsSmooth, BasedFunctor.comp] at h ⊢
  intro B A f hf z x kx hkx
  let i : E.functor.obj (E.inverse.obj x) ⟶ x := E.counitIso.hom.app x
  let iInv : x ⟶ E.functor.obj (E.inverse.obj x) := E.counitIso.inv.app x
  have hxA : 𝓨.p.obj x = A := (g.w_obj x).symm.trans (IsHomLift.codomain_eq 𝓩.p f kx)
  have hiA : 𝓨.p.IsHomLift (𝟙 A) i := E.counitIso.hom.isHomLift hxA
  let k' := kx ≫ g.map iInv
  have hk' : 𝓩.p.IsHomLift f k' := by
    let : 𝓨.p.IsHomLift (𝟙 A) iInv := E.counitIso.inv.isHomLift hxA
    let : 𝓩.p.IsHomLift (𝟙 A) (g.map iInv) :=
      g.preserves_isHomLift (𝟙 A) iInv
    exact IsHomLift.comp_lift_id_right 𝓩.p f kx (g.map iInv)
  obtain ⟨x', l, a, hl, ha, he⟩ := h f hf z (E.inverse.obj x) k' hk'
  let l' := E.functor.map l ≫ i
  have hl' : 𝓨.p.IsHomLift f l' := by
    let : 𝓨.p.IsHomLift f (E.functor.map l) := E.functor.preserves_isHomLift f l
    let : 𝓨.p.IsHomLift (𝟙 A) i := hiA
    exact IsHomLift.comp_lift_id_right 𝓨.p f (E.functor.map l) i
  refine ⟨E.functor.obj x', l', a, hl', ha, ?_⟩
  show g.map (E.functor.map l ≫ i) = a ≫ kx
  have he' : g.map (E.functor.map l) = a ≫
      (kx ≫ g.map iInv) := by
    change g.map (E.functor.map l) = a ≫ k' at he
    simpa [k'] using he
  rw [Functor.map_comp, he']
  simp only [Category.assoc, ← Functor.map_comp]
  have hcancel : iInv ≫ i = 𝟙 x := by
    show E.equiv.counitIso.inv.app x ≫ E.equiv.counitIso.hom.app x = 𝟙 x
    exact E.equiv.counitIso.inv_hom_id_app x
  rw [hcancel]
  have hmap_id : g.map (𝟙 x) = 𝟙 (g.obj x) := g.toFunctor.map_id x
  rw [hmap_id, Category.comp_id]

private theorem isSmooth_id_basedCategory
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓧 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    Deformation.IsSmooth (BasedFunctor.id 𝓧) := by
  intro B A f hf y x g hg
  have hy : 𝓧.p.obj y = B := IsHomLift.domain_eq 𝓧.p f g
  exact ⟨y, g, 𝟙 y, hg, IsHomLift.id hy, (Category.id_comp g).symm⟩

private theorem isSmooth_basedEquivalence
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓧 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓨 : BasedCategory.{v₁, u₁} (Deformation.ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (E : BasedCategory.Equivalence 𝓧 𝓨) : Deformation.IsSmooth E.functor := by
  simpa only [BasedFunctor.comp_id] using
    isSmooth_comp_basedEquivalence E (BasedFunctor.id 𝓨)
      (isSmooth_id_basedCategory 𝓨)

/-- A representation of the two-fibre product over the second base. -/
public abbrev BaseChangeEquivalence
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u) :=
  letI : Category (TwoFibreProductOver (Over.map V.hom)
    (Over.forget U) 𝒳.val.p y
    (Functor.TwoYoneda.liftBased 𝒳.val.p
      𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor) :=
      TwoFibreProductOver.instCategory
  StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map V.hom)
      (Over.forget U) 𝒳.val.p y
      (Functor.TwoYoneda.liftBased 𝒳.val.p
        𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor)
    (presheafOfCategories (F ⋙ typeToCat)).p

@[instance_reducible] private def baseChangeProductCategory
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj) :
    Category (TwoFibreProductOver (Over.map V.hom) (Over.forget U) 𝒳.val.p y
      (Functor.TwoYoneda.liftBased 𝒳.val.p
        𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor) :=
  TwoFibreProductOver.instCategory

attribute [local instance] baseChangeProductCategory

/-- An arrow in the category of elements over a prescribed base map is
exactly a restriction of sections along that map. -/
private lemma exists_section_of_homLift
    {C : Type u₁} [Category.{v₁} C] (F : Cᵒᵖ ⥤ Type u₂)
    {A D : C} (f : A ⟶ D) (a : F.obj (Opposite.op A))
    (z : (presheafOfCategories (F ⋙ typeToCat)).obj)
    (g : (⟨A, Discrete.mk a⟩ : (presheafOfCategories (F ⋙ typeToCat)).obj) ⟶ z)
    (hg : (presheafOfCategories (F ⋙ typeToCat)).p.IsHomLift f g) :
    ∃ b : F.obj (Opposite.op D), F.map f.op b = a := by
  have hz : z.base = D := IsHomLift.codomain_eq
    (presheafOfCategories (F ⋙ typeToCat)).p f g
  subst D
  have hf : f = g.base := IsHomLift.eq_of_isHomLift
    (presheafOfCategories (F ⋙ typeToCat)).p
    (a := ⟨A, Discrete.mk a⟩) (b := z) f g
  subst f
  exact ⟨z.fiber.as, (Discrete.eq_of_hom g.fiber).symm⟩

/-- A lift through a category representing a presheaf gives a lift of its
sections, independently of the chosen equivalence. -/
private lemma exists_section_of_equivalenceOver_lift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type u₃)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    {A B : C} (f : A ⟶ B) (a : F.obj (Opposite.op A)) (z : D)
    (g : e.inv.functor.obj ⟨A, Discrete.mk a⟩ ⟶ z)
    (hg : p.IsHomLift f g) :
    ∃ b : F.obj (Opposite.op B), F.map f.op b = a := by
  let q := (presheafOfCategories (F ⋙ typeToCat)).p
  let E : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q) :=
    ⟨e.hom.functor, e.hom.w⟩
  let t : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨A, Discrete.mk a⟩
  have hε : q.IsHomLift (𝟙 A) (e.counitIso.hom.app t) :=
    e.isHomLift_counitIso_hom_app t
  have hε' : q.IsHomLift (𝟙 A) (e.counitIso.inv.app t) := by
    rw [show e.counitIso.inv.app t = inv (e.counitIso.hom.app t) by simp]
    exact IsHomLift.lift_id_inv_isIso q A (e.counitIso.hom.app t)
  let : (BasedCategory.ofFunctor p).p.IsHomLift f g := hg
  have hEg : q.IsHomLift f (e.hom.functor.map g) := E.preserves_isHomLift f g
  exact exists_section_of_homLift F f a (e.hom.functor.obj z)
    (e.counitIso.inv.app t ≫ e.hom.functor.map g)
    (by
      let := hε'
      let := hEg
      exact IsHomLift.comp_lift_id_left q f (e.hom.functor.map g)
        (e.counitIso.inv.app t))

/-- Compatible lifts of the two components of a fibre-product point give a
lift in its representing presheaf. -/
private lemma exists_baseChange_section_of_lift
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {A D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2}
    (f : A ⟶ D) (a : F.obj (Opposite.op A))
    (R : Over U) (hR : R.left = (Over.map V.hom).obj D)
    (j : y.obj D ≅ (Functor.TwoYoneda.liftBased 𝒳.val.p
      𝒳.isFiberedInGroupoids U ⟨x, hx⟩).obj R)
    (hj : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D)) j.hom)
    (r : (e.inv.functor.obj ⟨A, Discrete.mk a⟩).y ⟶ R)
    (hbase :
      let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
      let hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
      eqToHom P.hy.symm ≫ r.left ≫ eqToHom hR =
        eqToHom P.hx.symm ≫ (Over.map V.hom).map (eqToHom hP ≫ f))
    (hcomm :
      let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
      let hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
      y.map (eqToHom hP ≫ f) ≫ j.hom = P.iso.hom ≫
        (Functor.TwoYoneda.liftBased 𝒳.val.p
          𝒳.isFiberedInGroupoids U ⟨x, hx⟩).map r) :
    ∃ b : F.obj (Opposite.op D), F.map f.op b = a := by
  let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
  have hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
  let Q : TwoFibreProductOver (Over.map V.hom) (Over.forget U) 𝒳.val.p y
      (Functor.TwoYoneda.liftBased 𝒳.val.p
        𝒳.isFiberedInGroupoids U ⟨x, hx⟩).toFunctor :=
    ⟨(Over.map V.hom).obj D, D, R, rfl, hR, j, hj⟩
  let g : P ⟶ Q := TwoFibreProductOver.Hom.mk' (eqToHom hP ≫ f) r
    (by
      show eqToHom P.hy.symm ≫ r.left ≫ eqToHom hR =
        eqToHom P.hx.symm ≫ (Over.map V.hom).map (eqToHom hP ≫ f) ≫ eqToHom rfl
      simpa only [eqToHom_refl, Category.comp_id] using hbase) hcomm
  apply exists_section_of_equivalenceOver_lift _ F e f a Q g
  exact IsHomLift.of_fac' _ f g hP rfl (by
    show eqToHom hP ≫ f = eqToHom hP ≫ f ≫ eqToHom rfl
    simp)

/-- The commuting comparison square already forces compatibility of the
base maps in a fibre-product lift. -/
private lemma exists_baseChange_section_of_commuting_lift
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    {A D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2}
    (f : A ⟶ D) (a : F.obj (Opposite.op A)) (R : Over U)
    (j : y.obj D ≅ (Functor.TwoYoneda.liftBased 𝒳.val.p
      𝒳.isFiberedInGroupoids U ⟨x, hx⟩).obj R)
    (hj : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D)) j.hom)
    (r : (e.inv.functor.obj ⟨A, Discrete.mk a⟩).y ⟶ R)
    (hcomm :
      let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
      let hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
      y.map (eqToHom hP ≫ f) ≫ j.hom = P.iso.hom ≫
        (Functor.TwoYoneda.liftBased 𝒳.val.p
          𝒳.isFiberedInGroupoids U ⟨x, hx⟩).map r) :
    ∃ b : F.obj (Opposite.op D), F.map f.op b = a := by
  let L := Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩
  let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
  have hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
  have hR : R.left = (Over.map V.hom).obj D :=
    (L.w_obj R).symm.trans (IsHomLift.codomain_eq 𝒳.val.p (𝟙 ((Over.map V.hom).obj D)) j.hom)
  apply exists_baseChange_section_of_lift B S hS 𝒳 U V x hx y F e f a R hR j hj r
    (hcomm := hcomm)
  let k := eqToHom P.hx.symm ≫ (Over.map V.hom).map (eqToHom hP ≫ f)
  have hya : 𝒳.val.p.IsHomLift k (y.map (eqToHom hP ≫ f)) := by
    apply IsHomLift.of_fac' 𝒳.val.p k _
      ((Functor.congr_obj hy P.x).trans P.hx) (Functor.congr_obj hy D)
    have hm := Functor.congr_hom hy (eqToHom hP ≫ f)
    change 𝒳.val.p.map (y.map (eqToHom hP ≫ f)) = _ at hm
    rw [hm]
    simp only [k, Category.assoc, eqToHom_trans_assoc]
  have hLr : L.map r = P.iso.inv ≫ y.map (eqToHom hP ≫ f) ≫ j.hom := by
    change y.map (eqToHom hP ≫ f) ≫ j.hom = P.iso.hom ≫ L.map r at hcomm
    rw [hcomm]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let := P.vertical
  let := hj
  let := hya
  have hmap : 𝒳.val.p.IsHomLift k (L.map r) := by
    rw [hLr]
    infer_instance
  let : (BasedCategory.ofFunctor 𝒳.val.p).p.IsHomLift k (L.map r) := hmap
  have hr : (Over.forget U).IsHomLift k r := L.isHomLift_map k r
  let := hr
  exact (IsHomLift.fac (Over.forget U) k r).symm

private lemma exists_baseChange_section_of_slice_lift
    (U V : AlgebraicGeometry.BigFppfOver B S hS)
    (x : 𝒳.val.obj) (hx : 𝒳.val.p.obj x = U)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U V x hx y F)
    (c : 𝒳.val.p.ChoiceOfPullbacks)
    {A D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2}
    (f : A ⟶ D) (a : F.obj (Opposite.op A)) (R : Over U)
    (j : y.obj D ≅ (c.sliceFunctor ⟨x, hx⟩).obj R)
    (hj : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D)) j.hom)
    (r : (e.inv.functor.obj ⟨A, Discrete.mk a⟩).y ⟶ R)
    (hcomm :
      let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
      let hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
      let α := twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids c U ⟨x, hx⟩
      y.map (eqToHom hP ≫ f) ≫ j.hom =
        (P.iso ≪≫ α.app P.y).hom ≫ (c.sliceFunctor ⟨x, hx⟩).map r) :
    ∃ b : F.obj (Opposite.op D), F.map f.op b = a := by
  let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
  have hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
  let α := twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids c U ⟨x, hx⟩
  have hR : R.left = (Over.map V.hom).obj D :=
    (Functor.congr_obj (c.sliceFunctor_comp ⟨x, hx⟩) R).symm.trans
      (IsHomLift.codomain_eq 𝒳.val.p (𝟙 ((Over.map V.hom).obj D)) j.hom)
  have hα : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D)) (α.app R).inv := by
    rw [← hR]
    let : 𝒳.val.p.IsHomLift (Iso.refl R.left).hom (α.app R).hom := by
      show 𝒳.val.p.IsHomLift (𝟙 R.left)
        ((twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids
          c U ⟨x, hx⟩).hom.app R)
      exact twoYonedaLiftIsoSliceFunctor_vertical 𝒳.val.p
        𝒳.isFiberedInGroupoids c U ⟨x, hx⟩ R
    exact IsHomLift.inv_lift_inv 𝒳.val.p (Iso.refl R.left) (α.app R)
  let := hα
  let := hj
  have hjα : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D))
      (j ≪≫ (α.app R).symm).hom := by
    show 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D))
      (j.hom ≫ (α.app R).inv)
    infer_instance
  apply exists_baseChange_section_of_commuting_lift B S hS 𝒳 U V x hx y hy F e f a R
    (j ≪≫ (α.app R).symm) hjα r
  show y.map (eqToHom hP ≫ f) ≫ (j.hom ≫ (α.app R).inv) =
    P.iso.hom ≫ (Functor.TwoYoneda.liftBased 𝒳.val.p
      𝒳.isFiberedInGroupoids U ⟨x, hx⟩).map r
  apply (cancel_mono (α.app R).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := α.hom.naturality r
  show y.map (eqToHom hP ≫ f) ≫ j.hom =
    P.iso.hom ≫ ((Functor.TwoYoneda.liftBased 𝒳.val.p
      𝒳.isFiberedInGroupoids U ⟨x, hx⟩).map r ≫ α.hom.app R)
  rw [hn]
  convert hcomm using 1
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  rfl

/-- A smooth lift of the pointed slice functor solves the corresponding
lifting problem in the presheaf representing the base change. -/
private lemma exists_baseChange_section_of_deformation_lift
    (V : AlgebraicGeometry.BigFppfOver B S hS) (x : 𝒳.val.obj)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 (𝒳.val.p.obj x) V x rfl y F)
    (c : 𝒳.val.p.ChoiceOfPullbacks)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (t : Over (𝒳.val.p.obj x))
    (ht : (Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion).obj t =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hsmooth : Deformation.IsSmooth (Deformation.Artin.mapPredeformationCategory iΛ
      (Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion)
      (𝒳.val.p ⋙ Over.post B.inclusion) (c.sliceFunctor ⟨x, rfl⟩)
      (Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p c x) t ht).toBasedFunctor)
    {A D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2}
    (f : A ⟶ D) (a : F.obj (Opposite.op A)) :
    let qU := Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion
    let qX := 𝒳.val.p ⋙ Over.post B.inclusion
    let G := c.sliceFunctor ⟨x, rfl⟩
    let hG := Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p c x
    let PU := Deformation.Artin.predeformationCategory iΛ qU t ht
    let hx₀ := Deformation.Artin.imageBasePoint (qY := qX) iΛ qU G hG t ht
    let PX := Deformation.Artin.predeformationCategory iΛ qX (G.obj t) hx₀
    let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
    let hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
    let α := twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids
      c (𝒳.val.p.obj x) ⟨x, rfl⟩
    ∀ (aU : PU.carrier) (bX : PX.carrier)
      (i : Deformation.Artin.DeformationMorphism iΛ qX (G.obj t) hx₀ (PX.objects bX)
        (mapDeformationObject iΛ qU qX G hG t ht (PU.objects aU)))
      (_hi : Function.Surjective i.ringHom.hom)
      (haU : (PU.objects aU).point = P.y) (hbX : (PX.objects bX).point = y.obj D),
      i.arrow = G.map (eqToHom haU) ≫ (P.iso ≪≫ α.app P.y).inv ≫
        y.map (eqToHom hP ≫ f) ≫ eqToHom hbX.symm →
      ∃ b : F.obj (Opposite.op D), F.map f.op b = a := by
  let qU := Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion
  let qX := 𝒳.val.p ⋙ Over.post B.inclusion
  let G := c.sliceFunctor ⟨x, rfl⟩
  let hG := Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p c x
  let PU := Deformation.Artin.predeformationCategory iΛ qU t ht
  let hx₀ := Deformation.Artin.imageBasePoint (qY := qX) iΛ qU G hG t ht
  let PX := Deformation.Artin.predeformationCategory iΛ qX (G.obj t) hx₀
  let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
  have hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
  let α := twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids
    c (𝒳.val.p.obj x) ⟨x, rfl⟩
  dsimp only
  intro aU bX i hi haU hbX hiarrow
  obtain ⟨cU, hc, h, j, hh, hj, hcomm⟩ := exists_deformation_lift_of_isSmooth
    iΛ qU qX G hG t ht hsmooth aU bX i hi
  let : 𝒳.val.p.ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_isFiberedInGroupoids 𝒳.val.p 𝒳.isFiberedInGroupoids
  let : qX.ReflectsIsomorphisms := inferInstance
  let : IsIso j.arrow := isIso_deformationMorphism_arrow_of_ringHom_eqToHom j hc hj
  let jiso : y.obj D ≅ G.obj (PU.objects cU).point := eqToIso hbX.symm ≪≫ asIso j.arrow
  have hjq : qX.IsHomLift (𝟙 (qX.obj (PX.objects bX).point)) j.arrow :=
    deformationMorphism_isHomLift_id_of_ringHom_eqToHom j hc hj
  have hjp : 𝒳.val.p.IsHomLift (𝟙 (𝒳.val.p.obj (PX.objects bX).point)) j.arrow :=
    isHomLift_of_comp_of_injective_obj 𝒳.val.p (Over.post B.inclusion)
      (overPost_injective_obj B S hS) (𝟙 _) j.arrow
      (by
        show qX.IsHomLift ((Over.post B.inclusion).map
          (𝟙 (𝒳.val.p.obj (PX.objects bX).point))) j.arrow
        show qX.IsHomLift (𝟙 (qX.obj (PX.objects bX).point)) j.arrow
        exact hjq)
  have hbase : 𝒳.val.p.obj (PX.objects bX).point = (Over.map V.hom).obj D :=
    (congrArg 𝒳.val.p.obj hbX).trans (Functor.congr_obj hy D)
  have hjD : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D)) j.arrow := by
    rw [← hbase]
    exact hjp
  have heq : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D)) (eqToHom hbX.symm) :=
    IsHomLift.eqToHom_domain_lift_id hbX.symm (Functor.congr_obj hy D)
  let := hjD
  let := heq
  have hjiso : 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D)) jiso.hom := by
    show 𝒳.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj D))
      (eqToHom hbX.symm ≫ j.arrow)
    infer_instance
  let r : P.y ⟶ (PU.objects cU).point := eqToHom haU.symm ≫ h.arrow
  apply exists_baseChange_section_of_slice_lift B S hS 𝒳 (𝒳.val.p.obj x) V x rfl
    y hy F e c f a (PU.objects cU).point jiso hjiso r
  show y.map (eqToHom hP ≫ f) ≫ jiso.hom =
    (P.iso ≪≫ α.app P.y).hom ≫ G.map r
  dsimp only [r]
  rw [G.map_comp, hcomm, hiarrow]
  simp only [Category.assoc]
  simp [jiso, P, G, α]

/-- The lifting conclusion of `exists_baseChange_section_of_deformation_lift`, stated for the
deformation objects themselves rather than for objects of the predeformation categories.

Keeping the two apart matters: reading an object of a predeformation category as a deformation
object unfolds `Deformation.Artin.predeformationCategory`, and doing that inside the proof of the
smoothness statement below exhausts the elaborator's budget. -/
private lemma exists_baseChange_section_of_deformation_objects
    (V : AlgebraicGeometry.BigFppfOver B S hS) (x : 𝒳.val.obj)
    (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
    (hy : y ⋙ 𝒳.val.p = Over.map V.hom)
    (F : (AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 (𝒳.val.p.obj x) V x rfl y F)
    (c : 𝒳.val.p.ChoiceOfPullbacks)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (t : Over (𝒳.val.p.obj x))
    (ht : (Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion).obj t =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hsmooth : Deformation.IsSmooth (Deformation.Artin.mapPredeformationCategory iΛ
      (Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion)
      (𝒳.val.p ⋙ Over.post B.inclusion) (c.sliceFunctor ⟨x, rfl⟩)
      (Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p c x) t ht).toBasedFunctor)
    {A D : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2}
    (f : A ⟶ D) (a : F.obj (Opposite.op A)) :
    let qU := Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion
    let qX := 𝒳.val.p ⋙ Over.post B.inclusion
    let G := c.sliceFunctor ⟨x, rfl⟩
    let hG := Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p c x
    let hx₀ := Deformation.Artin.imageBasePoint (qY := qX) iΛ qU G hG t ht
    let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
    let hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
    let α := twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids
      c (𝒳.val.p.obj x) ⟨x, rfl⟩
    ∀ (aU : Deformation.Artin.DeformationObject iΛ qU t ht)
      (bX : Deformation.Artin.DeformationObject iΛ qX (G.obj t) hx₀)
      (i : Deformation.Artin.DeformationMorphism iΛ qX (G.obj t) hx₀ bX
        (mapDeformationObject iΛ qU qX G hG t ht aU))
      (_hi : Function.Surjective i.ringHom.hom)
      (haU : aU.point = P.y) (hbX : bX.point = y.obj D),
      i.arrow = G.map (eqToHom haU) ≫ (P.iso ≪≫ α.app P.y).inv ≫
        y.map (eqToHom hP ≫ f) ≫ eqToHom hbX.symm →
      ∃ b : F.obj (Opposite.op D), F.map f.op b = a := by
  let qU := Over.forget (𝒳.val.p.obj x) ⋙ Over.post B.inclusion
  let qX := 𝒳.val.p ⋙ Over.post B.inclusion
  let G := c.sliceFunctor ⟨x, rfl⟩
  let hG := Deformation.Artin.sliceFunctor_comp_post B S hS 𝒳.val.p c x
  let hx₀ := Deformation.Artin.imageBasePoint (qY := qX) iΛ qU G hG t ht
  let PU := Deformation.Artin.predeformationCategory iΛ qU t ht
  let PX := Deformation.Artin.predeformationCategory iΛ qX (G.obj t) hx₀
  let P := e.inv.functor.obj ⟨A, Discrete.mk a⟩
  have hP : P.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
  let α := twoYonedaLiftIsoSliceFunctor 𝒳.val.p 𝒳.isFiberedInGroupoids
    c (𝒳.val.p.obj x) ⟨x, rfl⟩
  dsimp only
  intro aU bX i hi haU hbX hiarrow
  have hau : PU.objects (PU.objects.symm aU) = aU := PU.objects.apply_symm_apply _
  have hbx : PX.objects (PX.objects.symm bX) = bX := PX.objects.apply_symm_apply _
  have haU' : (PU.objects (PU.objects.symm aU)).point = P.y :=
    (congrArg Deformation.Artin.DeformationObject.point hau).trans haU
  have hbX' : (PX.objects (PX.objects.symm bX)).point = y.obj D :=
    (congrArg Deformation.Artin.DeformationObject.point hbx).trans hbX
  let i' := transportDeformationMorphism hbx.symm
    (congrArg (mapDeformationObject iΛ qU qX G hG t ht) hau.symm) i
  have hi' : Function.Surjective i'.ringHom.hom :=
    transportDeformationMorphism_surjective _ _ i hi
  have hiarrow' : i'.arrow = G.map (eqToHom haU') ≫ (P.iso ≪≫ α.app P.y).inv ≫
      y.map (eqToHom hP ≫ f) ≫ eqToHom hbX'.symm := by
    rw [transportDeformationMorphism_arrow, hiarrow]
    simp only [eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  exact exists_baseChange_section_of_deformation_lift B S hS 𝒳 V x y hy F e c iΛ t ht hsmooth
    f a (PU.objects.symm aU) (PX.objects.symm bX) i' hi' haU' hbX' hiarrow'

end Deformation.Artin.BaseChange

end
