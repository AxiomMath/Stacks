module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.Versality.Openness.Basic

/-!
# Base change of smoothness on predeformation categories

The explicit presentation of a predeformation category on deformation objects, the transport
of smoothness along full surjective presentations, and stability of smoothness on
predeformation categories under base change of categories fibred in groupoids (Tag 07XV).
-/

@[expose] public section

namespace Deformation.Artin

/-! ### Base change of smoothness on predeformation categories

The predeformation category of a point is specified up to equivalence over `𝒞_Λ` by
`Deformation.Artin.PredeformationConstruction`, so smoothness of an induced functor is read
off the *explicit* presentation on `Deformation.Artin.DeformationObject`, to which any
construction is equivalent over `𝒞_Λ`. On that presentation the lifting problem defining
smoothness can be solved componentwise in the 2-fibre product: the comparison arrow supplied
by smoothness of `f` is vertical, hence invertible because the target is fibred in groupoids,
and its inverse is the comparison isomorphism of the new object of `𝒳 ×_𝒴 𝒵`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v' w w' vX vY vZ wX wY wZ

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.TwoFibreProductOver.fst CategoryTheory.TwoFibreProductOver.snd

section Explicit

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
variable (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S) (x₀ : X)
variable (hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The category structure on the explicit deformation objects, with reversed arrows. -/
abbrev explicitDeformationCategory : Category (DeformationObject iΛ q x₀ hx₀) where
  Hom a b := DeformationMorphism iΛ q x₀ hx₀ a b
  id a :=
    { ringHom := 𝟙 a.algebra
      arrow := 𝟙 a.point
      triangle := by simp
      arrow_base := by simp }
  comp f g :=
    { ringHom := f.ringHom ≫ g.ringHom
      arrow := g.arrow ≫ f.arrow
      triangle := by rw [← Category.assoc, g.triangle, f.triangle]
      arrow_base := by
        rw [Functor.map_comp, Over.comp_left]
        have H := congrArg₂ (fun a b => a ≫ b) g.arrow_base f.arrow_base
        have H' : CommRingCat.ofHom (f.ringHom ≫ g.ringHom).hom.toRingHom =
            CommRingCat.ofHom f.ringHom.hom.toRingHom ≫
              CommRingCat.ofHom g.ringHom.hom.toRingHom := by ext; rfl
        rw [H']
        simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
          ← Spec.map_comp] using H }
  id_comp f := by apply DeformationMorphism.ext_of_components <;> simp
  comp_id f := by apply DeformationMorphism.ext_of_components <;> simp
  assoc f g h := by
    apply DeformationMorphism.ext_of_components <;> simp [Category.assoc]

attribute [local instance] explicitDeformationCategory

/-- The projection of the explicit presentation to `𝒞_Λ`. -/
abbrev explicitProjection :
    DeformationObject iΛ q x₀ hx₀ ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k where
  obj a := a.algebra
  map f := f.ringHom

lemma map_left_of_comp_eq {Y : Type v'} [Category.{w'} Y]
    (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = q) {a b : X} (f : a ⟶ b) :
    (qY.map (F.map f)).left =
      eqToHom (congrArg Over.left (Functor.congr_obj hF a)) ≫
        (q.map f).left ≫ eqToHom (congrArg Over.left (Functor.congr_obj hF b)).symm := by
  simpa using congrArg (fun t => t.left) (Functor.congr_hom hF f)

/-- The functor of explicit presentations induced by a morphism over the base. -/
abbrev explicitMap {Y : Type v'} [Category.{w'} Y]
    (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = q) :
    DeformationObject iΛ q x₀ hx₀ ⥤
      DeformationObject iΛ qY (F.obj x₀) (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀) where
  obj a :=
    { algebra := a.algebra
      point := F.obj a.point
      arrow := F.map a.arrow
      base := (Functor.congr_obj hF a.point).trans a.base
      arrow_base := by
        rw [map_left_of_comp_eq q qY F hF]
        simpa using a.arrow_base }
  map f :=
    { ringHom := f.ringHom
      arrow := F.map f.arrow
      triangle := by simpa only [← Functor.map_comp] using congrArg F.map f.triangle
      arrow_base := by simpa [map_left_of_comp_eq q qY F hF] using f.arrow_base }
  map_id a := DeformationMorphism.ext_of_components _ _ _ _ rfl (F.map_id _)
  map_comp f g := DeformationMorphism.ext_of_components _ _ _ _ rfl (F.map_comp _ _)

private lemma explicit_eqToHom_arrow {a b : DeformationObject iΛ q x₀ hx₀} (h : a = b) :
    (eqToHom h : a ⟶ b).arrow = eqToHom (congrArg DeformationObject.point h).symm := by
  cases h
  rfl

private lemma explicit_eqToHom_ringHom {a b : DeformationObject iΛ q x₀ hx₀} (h : a = b) :
    (eqToHom h : a ⟶ b).ringHom = eqToHom (congrArg DeformationObject.algebra h) := by
  cases h
  rfl

/-- The category structure carried by a construction of the predeformation category, as a
term one can turn into a local instance: the field `category` of
`Deformation.Artin.PredeformationConstruction` is instance-implicit, so without this it is not
found by instance search on `P.carrier`. -/
public abbrev categoryOfConstruction (P : PredeformationConstruction iΛ q x₀ hx₀) :
    Category P.carrier := P.category

attribute [local instance] categoryOfConstruction

/-- The object and morphism descriptions identify a construction of the predeformation
category with the explicit category on deformation objects. -/
private abbrev explicitPresentation (P : PredeformationConstruction iΛ q x₀ hx₀) :
    P.carrier ⥤ DeformationObject iΛ q x₀ hx₀ where
  obj := P.objects
  map := P.morphisms _ _
  map_id a := by
    apply DeformationMorphism.ext_of_components
    · change (P.morphisms a a (𝟙 a)).ringHom = 𝟙 (P.objects a).algebra
      simpa using (P.morphism_projection (𝟙 a)).symm
    · exact P.reversed_identity a
  map_comp f g := by
    apply DeformationMorphism.ext_of_components
    · change (P.morphisms _ _ (f ≫ g)).ringHom =
        (P.morphisms _ _ f).ringHom ≫ (P.morphisms _ _ g).ringHom
      simp [← P.morphism_projection, Category.assoc]
    · exact P.reversed_composition f g

private lemma explicitPresentation_projection (P : PredeformationConstruction iΛ q x₀ hx₀) :
    explicitPresentation iΛ q x₀ hx₀ P ⋙ explicitProjection iΛ q x₀ hx₀ = P.projection := by
  refine CategoryTheory.Functor.ext (fun a => (P.object_projection a).symm) ?_
  intro a b f
  exact (P.morphism_projection f).symm

private lemma explicitPresentation_full (P : PredeformationConstruction iΛ q x₀ hx₀) :
    (explicitPresentation iΛ q x₀ hx₀ P).Full where
  map_surjective f := P.morphisms _ _ |>.surjective f

private lemma explicitPresentation_faithful (P : PredeformationConstruction iΛ q x₀ hx₀) :
    (explicitPresentation iΛ q x₀ hx₀ P).Faithful where
  map_injective h := (P.morphisms _ _).injective h

-- Deformation objects agreeing on algebra and point, with arrows agreeing after transport, are
-- equal: `Deformation.Artin.deformationObject_ext_of_arrow`, public beside the structure in
-- `StacksFrontier.Deformation.Artin.Predeformation`. A `private` re-declaration stood here.

private lemma explicitPresentation_map {Y : Type v'} [Category.{w'} Y]
    (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = q)
    (M : InducedPredeformationFunctor iΛ q qY F hF x₀ hx₀) :
    M.toFunctor ⋙ explicitPresentation iΛ qY (F.obj x₀)
        (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀)
        (predeformationCategory iΛ qY (F.obj x₀)
          (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀)) =
      explicitPresentation iΛ q x₀ hx₀ (predeformationCategory iΛ q x₀ hx₀) ⋙
        explicitMap iΛ q x₀ hx₀ qY F hF := by
  let P := predeformationCategory iΛ q x₀ hx₀
  let Q := predeformationCategory iΛ qY (F.obj x₀)
    (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀)
  have ho (a : P.carrier) :
      Q.objects (M.toFunctor.obj a) = (explicitMap iΛ q x₀ hx₀ qY F hF).obj (P.objects a) := by
    refine deformationObject_ext_of_arrow ?_ (M.object_point a) (M.object_arrow a)
    exact (Q.object_projection _).symm.trans
      ((Functor.congr_obj M.projection_comm a).trans (P.object_projection a))
  refine CategoryTheory.Functor.ext ho ?_
  intro a b f
  apply DeformationMorphism.ext_of_components
  · have H := Functor.congr_hom M.projection_comm f
    dsimp only [Functor.comp_map] at H
    change (Q.morphisms _ _ (M.toFunctor.map f)).ringHom =
      (eqToHom (ho a)).ringHom ≫
        (P.morphisms _ _ f).ringHom ≫ (eqToHom (ho b).symm).ringHom
    rw [explicit_eqToHom_ringHom, explicit_eqToHom_ringHom,
      ← P.morphism_projection, ← Q.morphism_projection, H]
    simp
    rfl
  · change (Q.morphisms _ _ (M.toFunctor.map f)).arrow =
      ((eqToHom (ho b).symm).arrow ≫ F.map (P.morphisms _ _ f).arrow) ≫ (eqToHom (ho a)).arrow
    simpa only [explicit_eqToHom_arrow, Category.assoc] using M.morphism_arrow f

/-- The explicit presentation of a construction, as a morphism of categories over `𝒞_Λ`. -/
private def explicitPresentationBased (P : PredeformationConstruction iΛ q x₀ hx₀) :
    BasedFunctor (BasedCategory.ofFunctor P.projection)
      (BasedCategory.ofFunctor (explicitProjection iΛ q x₀ hx₀)) where
  toFunctor := explicitPresentation iΛ q x₀ hx₀ P
  w := explicitPresentation_projection iΛ q x₀ hx₀ P

/-- The induced functor of explicit presentations lies over `𝒞_Λ`: both projections read off
the Artinian local algebra of a deformation, which the induced functor leaves unchanged. -/
lemma explicitMap_comp_explicitProjection {Y : Type v'} [Category.{w'} Y]
    (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = q) :
    explicitMap iΛ q x₀ hx₀ qY F hF ⋙
        explicitProjection iΛ qY (F.obj x₀)
          (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀) =
      explicitProjection iΛ q x₀ hx₀ := by
  refine CategoryTheory.Functor.ext (fun a => rfl) ?_
  intro a b f
  simp

/-- The induced functor of explicit presentations, as a morphism of categories over
`𝒞_Λ`. -/
def explicitMapBased {Y : Type v'} [Category.{w'} Y]
    (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = q) :
    BasedFunctor (BasedCategory.ofFunctor (explicitProjection iΛ q x₀ hx₀))
      (BasedCategory.ofFunctor (explicitProjection iΛ qY (F.obj x₀)
        (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀))) where
  toFunctor := explicitMap iΛ q x₀ hx₀ qY F hF
  w := explicitMap_comp_explicitProjection iΛ q x₀ hx₀ qY F hF

/-- Changing the distinguished point along a vertical isomorphism, on explicit
presentations. -/
abbrev rebaseExplicit (x₁ : X)
    (hx₁ : q.obj x₁ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (e : x₀ ≅ x₁) (he : q.IsHomLift (𝟙 (q.obj x₀)) e.hom) :
    DeformationObject iΛ q x₁ hx₁ ⥤ DeformationObject iΛ q x₀ hx₀ where
  obj a :=
    { algebra := a.algebra
      point := a.point
      arrow := e.hom ≫ a.arrow
      base := a.base
      arrow_base := by
        have := he
        rw [Functor.map_comp, Over.comp_left, IsHomLift.fac' q (𝟙 (q.obj x₀)) e.hom]
        simpa using a.arrow_base }
  map f :=
    { ringHom := f.ringHom
      arrow := f.arrow
      triangle := by simpa only [Category.assoc] using congrArg (e.hom ≫ ·) f.triangle
      arrow_base := f.arrow_base }
  map_id a := rfl
  map_comp f g := rfl

-- A vertical reversed arrow between deformations over one algebra is a morphism of
-- deformations: `Deformation.Artin.verticalDeformationMorphism_of_isHomLift`, public in
-- `StacksFrontier.Deformation.Artin.Predeformation.FibreProduct` (closure 9; +2 modules here).
-- A `private` re-declaration stood here, with `U` of the lifted identity fixed at
-- `q.obj b.point` where the canonical leaves it free, and with the factorization and the
-- lift hypotheses in the opposite order.

/-- A reversed arrow of the explicit presentation lying over an identity of `𝒞_Λ` is
vertical over the base. -/
private lemma explicit_vertical {a b : DeformationObject iΛ q x₀ hx₀}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (m : a ⟶ b)
    (hm : (explicitProjection iΛ q x₀ hx₀).IsHomLift (𝟙 A) m) :
    q.IsHomLift (𝟙 (q.obj b.point)) m.arrow := by
  have := hm
  have ha := IsHomLift.domain_eq (explicitProjection iΛ q x₀ hx₀) (𝟙 A) m
  have hb := IsHomLift.codomain_eq (explicitProjection iΛ q x₀ hx₀) (𝟙 A) m
  obtain ⟨Aa, xa, ar, ba, aa⟩ := a
  obtain ⟨Ab, xb, br, bb, ab⟩ := b
  change Aa = A at ha
  change Ab = A at hb
  subst Aa Ab
  have hr := IsHomLift.eq_of_isHomLift (explicitProjection iΛ q x₀ hx₀) (𝟙 A) m
  change 𝟙 A = m.ringHom at hr
  have H := m.arrow_base
  rw [← hr] at H
  simp only [ArtinianLocalAlgCat.id_hom] at H
  refine IsHomLift.of_fac' q _ _ rfl (ba.trans bb.symm) ?_
  apply Over.OverMorphism.ext
  simpa using congrArg (fun t => eqToHom (congrArg Over.left bb) ≫ t ≫
    eqToHom (congrArg Over.left ba).symm) H

end Explicit

section Transport

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
variable {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, u, u} Λ k)}
variable {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, u, u} Λ k)}

/-- Smoothness of a composite is smoothness of the second factor when the first is full and
surjective on objects. -/
private lemma isSmooth_comp_left_iff (F : BasedFunctor 𝓕 𝓖) (G : BasedFunctor 𝓖 𝓗)
    [F.toFunctor.Full] (hs : Function.Surjective F.obj) :
    Deformation.IsSmooth (BasedFunctor.comp F G) ↔ Deformation.IsSmooth G := by
  constructor
  · intro h B A f hf y x g hg
    obtain ⟨x, rfl⟩ := hs x
    obtain ⟨x', l, a, hl, ha, he⟩ := h f hf y x g hg
    have := hl
    exact ⟨F.obj x', F.map l, a, BasedFunctor.preserves_isHomLift F f l, ha, he⟩
  · intro h B A f hf y x g hg
    obtain ⟨x', l, a, hl, ha, he⟩ := h f hf y (F.obj x) g hg
    obtain ⟨x', rfl⟩ := hs x'
    obtain ⟨l, rfl⟩ := F.toFunctor.map_surjective l
    have := hl
    exact ⟨x', l, a, BasedFunctor.isHomLift_map F f l, ha, he⟩

/-- Smoothness of a composite is smoothness of the first factor when the second is fully
faithful and surjective on objects. -/
private lemma isSmooth_comp_right_iff (F : BasedFunctor 𝓕 𝓖) (G : BasedFunctor 𝓖 𝓗)
    [G.toFunctor.Full] [G.toFunctor.Faithful] (hs : Function.Surjective G.obj) :
    Deformation.IsSmooth (BasedFunctor.comp F G) ↔ Deformation.IsSmooth F := by
  constructor
  · intro h B A f hf y x g hg
    have := hg
    obtain ⟨x', l, a, hl, ha, he⟩ := h f hf (G.obj y) x (G.map g)
      (BasedFunctor.preserves_isHomLift G f g)
    obtain ⟨a, rfl⟩ := G.toFunctor.map_surjective a
    have : 𝓗.p.IsHomLift (𝟙 B) (G.map a) := ha
    refine ⟨x', l, a, hl, BasedFunctor.isHomLift_map G (𝟙 B) a, ?_⟩
    apply G.toFunctor.map_injective
    simpa only [Functor.map_comp, BasedFunctor.comp, Functor.comp_map] using he
  · intro h B A f hf y x g hg
    obtain ⟨y, rfl⟩ := hs y
    obtain ⟨g, rfl⟩ := G.toFunctor.map_surjective g
    have : 𝓗.p.IsHomLift f (G.map g) := hg
    obtain ⟨x', l, a, hl, ha, he⟩ := h f hf y x g (BasedFunctor.isHomLift_map G f g)
    have := ha
    refine ⟨x', l, G.map a, hl, BasedFunctor.preserves_isHomLift G (𝟙 B) a, ?_⟩
    simpa only [Functor.map_comp, BasedFunctor.comp, Functor.comp_map] using congrArg G.map he

/-- **Cancelling the first factor of a composite on the left.** Smoothness of `F ⋙ G` is
smoothness of `G` as soon as `F` is full and surjective on objects.

This is the public form of the two-out-of-three cancellation used inside this file. It is
exposed because the chain of **Stacks 0DZF** recovers each of its three arrows from composites:
the source establishes the conclusion for the composites and then cancels. -/
public alias isSmooth_comp_iff_right_of_full_of_surjective := isSmooth_comp_left_iff

/-- **Cancelling the second factor of a composite on the right.** Smoothness of `F ⋙ G` is
smoothness of `F` as soon as `G` is fully faithful and surjective on objects.

The public form of the companion cancellation; see
`Deformation.Artin.isSmooth_comp_iff_right_of_full_of_surjective`. When the second factor is
fully faithful but *not* surjective on objects — which is the case for the comparison
`∏ 𝓓_{R i} ⟶ 𝓓_{∏ R i}` of **Stacks 0DZF** — use `Deformation.isSmooth_of_comp_fullyFaithful`
instead, which drops the surjectivity. -/
public alias isSmooth_comp_iff_left_of_fullyFaithful_of_surjective := isSmooth_comp_right_iff

end Transport

section BaseChange

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
variable (iΛ : Spec (.of Λ) ⟶ S)

attribute [local instance] explicitDeformationCategory

/-- Smoothness is unchanged on passing to the explicit presentation of deformations. -/
lemma isSmooth_explicitMap_iff {X : Type v} [Category.{w} X]
    (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {Y : Type v'} [Category.{w'} Y] (qY : Y ⥤ Over S) (F : X ⥤ Y) (hF : F ⋙ qY = q)
    (M : InducedPredeformationFunctor iΛ q qY F hF x₀ hx₀) :
    Deformation.IsSmooth (explicitMapBased iΛ q x₀ hx₀ qY F hF) ↔
      Deformation.IsSmooth M.toBasedFunctor := by
  let P := predeformationCategory iΛ q x₀ hx₀
  let Q := predeformationCategory iΛ qY (F.obj x₀)
    (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀)
  let L := explicitPresentationBased iΛ q x₀ hx₀ P
  let R := explicitPresentationBased iΛ qY (F.obj x₀)
    (imageBasePoint (qY := qY) iΛ q F hF x₀ hx₀) Q
  let _ : L.toFunctor.Full := explicitPresentation_full iΛ q x₀ hx₀ P
  let _ : R.toFunctor.Full := explicitPresentation_full iΛ qY _ _ Q
  let _ : R.toFunctor.Faithful := explicitPresentation_faithful iΛ qY _ _ Q
  have H : BasedFunctor.comp M.toBasedFunctor R =
      BasedFunctor.comp L (explicitMapBased iΛ q x₀ hx₀ qY F hF) := by
    apply BasedCategory.BasedFunctor.ext'
    exact explicitPresentation_map iΛ q x₀ hx₀ qY F hF M
  rw [← isSmooth_comp_left_iff L _ P.objects.surjective, ← H]
  exact isSmooth_comp_right_iff _ R Q.objects.surjective

private lemma post_faithful (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (Over.post B.inclusion : BigFppfOver B S hS ⥤ Over S).Faithful where
  map_injective h := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    exact congrArg Over.Hom.left h

private lemma post_obj_injective (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Function.Injective (Over.post B.inclusion : BigFppfOver B S hS ⥤ Over S).obj := by
  intro U V h
  have hl : U.left = V.left := ObjectProperty.FullSubcategory.ext (congrArg Over.left h)
  apply CostructuredArrow.obj_ext U V hl
  apply B.inclusion.map_injective
  have hw : (eqToHom h).left ≫ ((Over.post B.inclusion).obj V).hom =
      ((Over.post B.inclusion).obj U).hom := Over.w (eqToHom h)
  rw [Over.eqToHom_left] at hw
  simpa [Over.post] using hw

-- A morphism lying over `f` for `p` lies over `u(f)` for `p ⋙ u`:
-- `CategoryTheory.Functor.isHomLift_comp_functor`, public in
-- `StacksFrontier.CategoryTheory.FiberedCategory.HomLift` (closure 1; already in this file's
-- closure, so no import edge). A `private` re-declaration stood here.

private lemma isHomLift_of_postcomp {C D E : Type*} [Category C] [Category D] [Category E]
    (p : C ⥤ D) (Q : D ⥤ E) [Q.Faithful] (hi : Function.Injective Q.obj)
    {x y : C} {U V : D} (f : U ⟶ V) (a : x ⟶ y)
    (h : (p ⋙ Q).IsHomLift (Q.map f) a) : p.IsHomLift f a := by
  have := h
  refine IsHomLift.of_fac' p f a
    (hi (IsHomLift.domain_eq (p ⋙ Q) (Q.map f) a))
    (hi (IsHomLift.codomain_eq (p ⋙ Q) (Q.map f) a)) ?_
  apply Q.map_injective
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using
    IsHomLift.fac' (p ⋙ Q) (Q.map f) a

lemma comp_over_eq {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] {F : C₁ ⥤ C₂} {p : C₂ ⥤ C₃} {r : C₁ ⥤ C₃}
    (h : F ⋙ p = r) (Q : C₃ ⥤ C₄) : F ⋙ p ⋙ Q = r ⋙ Q := by
  rw [← Functor.assoc, h]

/-- Base change of the lifting property, computed in a faithfully embedded base. The
comparison arrow supplied by smoothness is vertical, hence invertible in the target fibred
category, and its inverse supplies the comparison isomorphism of the new object of the
2-fibre product. -/
private lemma isSmooth_explicitMap_baseChange {C : Type*} [Category C]
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (Q : C ⥤ Over S) [Q.Faithful] (hi : Function.Injective Q.obj)
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C) (f : X ⥤ Y) (g : Z ⥤ Y)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ)
    (w₀ : TwoFibreProductOver pX pZ pY f g)
    (hw₀ : (TwoFibreProductOver.structureFunctor pX pZ pY f g ⋙ Q).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hpY : pY.IsFiberedInGroupoids)
    (hs : Deformation.IsSmooth
      (explicitMapBased (k := k) iΛ (pX ⋙ Q) w₀.x ((congrArg Q.obj w₀.hx).trans hw₀)
        (pY ⋙ Q) f (comp_over_eq hf Q))) :
    Deformation.IsSmooth
      (explicitMapBased (k := k) iΛ
        (TwoFibreProductOver.structureFunctor pX pZ pY f g ⋙ Q) w₀ hw₀
        (pZ ⋙ Q) (TwoFibreProductOver.snd pX pZ pY f g)
        (comp_over_eq TwoFibreProductOver.snd_comp_eq Q)) := by
  let hx₀ := (congrArg Q.obj w₀.hx).trans hw₀
  let hz₀ := (congrArg Q.obj w₀.hy).trans hw₀
  let hy₀ := imageBasePoint (qY := pY ⋙ Q) iΛ (pX ⋙ Q) f (comp_over_eq hf Q) w₀.x hx₀
  let hg₀ := imageBasePoint (qY := pY ⋙ Q) iΛ (pZ ⋙ Q) g (comp_over_eq hg Q) w₀.y hz₀
  let fx := explicitMap (k := k) iΛ (pX ⋙ Q) w₀.x hx₀ (pY ⋙ Q) f (comp_over_eq hf Q)
  let wx := explicitMap (k := k) iΛ
    (TwoFibreProductOver.structureFunctor pX pZ pY f g ⋙ Q) w₀ hw₀
    (pX ⋙ Q) (TwoFibreProductOver.fst pX pZ pY f g)
    (comp_over_eq TwoFibreProductOver.fst_comp_eq Q)
  let wz := explicitMap (k := k) iΛ
    (TwoFibreProductOver.structureFunctor pX pZ pY f g ⋙ Q) w₀ hw₀
    (pZ ⋙ Q) (TwoFibreProductOver.snd pX pZ pY f g)
    (comp_over_eq TwoFibreProductOver.snd_comp_eq Q)
  have hvert (u : TwoFibreProductOver pX pZ pY f g) :
      (pY ⋙ Q).IsHomLift (𝟙 ((pY ⋙ Q).obj (f.obj u.x))) u.iso.hom := by
    have H := Functor.isHomLift_comp_functor (p := pY) Q (𝟙 u.base) u.iso.hom u.vertical
    change (pY ⋙ Q).IsHomLift (𝟙 (Q.obj (pY.obj (f.obj u.x)))) _
    have hbase : pY.obj (f.obj u.x) = u.base := (Functor.congr_obj hf u.x).trans u.hx
    rw [hbase]
    simpa only [Q.map_id] using H
  let gy := explicitMap (k := k) iΛ (pZ ⋙ Q) w₀.y hz₀ (pY ⋙ Q) g (comp_over_eq hg Q) ⋙
    rebaseExplicit iΛ (pY ⋙ Q) (f.obj w₀.x) hy₀ (g.obj w₀.y) hg₀ w₀.iso (hvert w₀)
  intro B A ρ hρ z w gz hgz
  change z ⟶ wz.obj w at gz
  change (explicitProjection (k := k) iΛ (pZ ⋙ Q) w₀.y hz₀).IsHomLift ρ gz at hgz
  cases hgz
  let x := wx.obj w
  let y := gy.obj z
  let c : gy.obj (wz.obj w) ⟶ fx.obj x :=
    verticalDeformationMorphism_of_isHomLift iΛ (q := pY ⋙ Q) (x₀ := f.obj w₀.x)
      (hx₀ := hy₀) rfl w.point.iso.hom (by exact w.arrow.w) (hvert w.point)
  let β : y ⟶ fx.obj x := gy.map gz ≫ c
  have hβ : (explicitProjection (k := k) iΛ (pY ⋙ Q) (f.obj w₀.x) hy₀).IsHomLift
      gz.ringHom β := by
    have hb : β.ringHom = gz.ringHom := by
      change gz.ringHom ≫ 𝟙 _ = gz.ringHom
      simp
    rw [← hb]
    exact IsHomLift.map _ β
  obtain ⟨x', l, a, hl, ha, he⟩ := hs gz.ringHom hρ y x β hβ
  change x' ⟶ x at l
  change fx.obj x' ⟶ y at a
  change (explicitProjection (k := k) iΛ (pX ⋙ Q) w₀.x hx₀).IsHomLift gz.ringHom l at hl
  have := hl
  have hA := IsHomLift.domain_eq
    (explicitProjection (k := k) iΛ (pX ⋙ Q) w₀.x hx₀) gz.ringHom l
  obtain ⟨Ax, xp, xa, xb, xab⟩ := x'
  change Ax = z.algebra at hA
  subst Ax
  let x' : DeformationObject iΛ (pX ⋙ Q) w₀.x hx₀ := ⟨z.algebra, xp, xa, xb, xab⟩
  change x' ⟶ x at l
  change fx.obj x' ⟶ y at a
  have hAlg : x'.algebra = z.algebra := rfl
  have hr : l.ringHom = gz.ringHom :=
    (IsHomLift.eq_of_isHomLift
      (explicitProjection (k := k) iΛ (pX ⋙ Q) w₀.x hx₀) gz.ringHom l).symm
  have hav := explicit_vertical iΛ (pY ⋙ Q) (f.obj w₀.x) hy₀ a ha
  change (pY ⋙ Q).IsHomLift (𝟙 (Q.obj (pY.obj (g.obj z.point)))) a.arrow at hav
  have hav' : pY.IsHomLift (𝟙 (pY.obj (g.obj z.point))) a.arrow :=
    isHomLift_of_postcomp pY Q hi _ _ (by simpa only [Q.map_id] using hav)
  have := hav'
  have : IsIso a.arrow := by
    have := hpY.isStronglyCartesian_homLift (𝟙 (pY.obj (g.obj z.point))) a.arrow
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso pY
      (𝟙 (pY.obj (g.obj z.point))) a.arrow
  have hx' : pX.obj x'.point = pZ.obj z.point :=
    (Functor.congr_obj hf x'.point).symm.trans
      ((IsHomLift.codomain_eq pY (𝟙 (pY.obj (g.obj z.point))) a.arrow).trans
        (Functor.congr_obj hg z.point))
  let t : TwoFibreProductOver pX pZ pY f g :=
    { base := pZ.obj z.point
      x := x'.point
      y := z.point
      hx := hx'
      hy := rfl
      iso := (asIso a.arrow).symm
      vertical := by
        have hv : pY.IsHomLift (𝟙 (pY.obj (g.obj z.point))) (inv a.arrow) := inferInstance
        change pY.IsHomLift (𝟙 (pZ.obj z.point)) (inv a.arrow)
        rw [← Functor.congr_obj hg z.point]
        exact hv }
  have ht : f.map x'.arrow ≫ t.iso.hom = w₀.iso.hom ≫ g.map z.arrow := by
    change f.map x'.arrow ≫ inv a.arrow = _
    have H := a.triangle
    change (w₀.iso.hom ≫ g.map z.arrow) ≫ a.arrow = f.map x'.arrow at H
    rw [← H]
    simp
  have bt := (congrArg Q.obj t.hx.symm).trans x'.base
  have hBase : eqToHom w₀.hy.symm ≫ pZ.map z.arrow ≫ eqToHom t.hy =
      eqToHom w₀.hx.symm ≫ pX.map x'.arrow ≫ eqToHom t.hx := by
    apply Q.map_injective
    apply Over.OverMorphism.ext
    apply (cancel_epi (eqToHom (congrArg Over.left hw₀).symm)).1
    apply (cancel_mono (eqToHom (congrArg Over.left bt))).1
    simpa [Functor.comp_map, Functor.map_comp, eqToHom_map, Category.assoc]
      using z.arrow_base.trans x'.arrow_base.symm
  let ar : w₀ ⟶ t := TwoFibreProductOver.Hom.mk' x'.arrow z.arrow hBase ht
  let w' : DeformationObject iΛ
      (TwoFibreProductOver.structureFunctor pX pZ pY f g ⋙ Q) w₀ hw₀ :=
    { algebra := x'.algebra
      point := t
      arrow := ar
      base := (congrArg Q.obj t.hx.symm).trans x'.base
      arrow_base := by
        change eqToHom _ ≫ (Q.map ar.hbase).left ≫ eqToHom _ = _
        dsimp only [ar, TwoFibreProductOver.Hom.mk'_hbase]
        simpa [Functor.map_comp, eqToHom_map, Category.assoc] using x'.arrow_base }
  have hbl : eqToHom w.point.hy.symm ≫ pZ.map gz.arrow ≫ eqToHom t.hy =
      eqToHom w.point.hx.symm ≫ pX.map l.arrow ≫ eqToHom t.hx := by
    apply Q.map_injective
    apply Over.OverMorphism.ext
    apply (cancel_epi (eqToHom (congrArg Over.left w.base).symm)).1
    apply (cancel_mono (eqToHom (congrArg Over.left bt))).1
    have H := l.arrow_base
    rw [hr] at H
    simpa [Functor.comp_map, Functor.map_comp, eqToHom_map, Category.assoc]
      using gz.arrow_base.trans H.symm
  have htl : f.map l.arrow ≫ t.iso.hom = w.point.iso.hom ≫ g.map gz.arrow := by
    change f.map l.arrow ≫ inv a.arrow = _
    have H := congrArg DeformationMorphism.arrow he
    change f.map l.arrow = (w.point.iso.hom ≫ g.map gz.arrow) ≫ a.arrow at H
    rw [H]
    simp
  let lr : w.point ⟶ t := TwoFibreProductOver.Hom.mk' l.arrow gz.arrow hbl htl
  let ll : w' ⟶ w :=
    { ringHom := l.ringHom
      arrow := lr
      triangle := by
        apply TwoFibreProductOver.Hom.ext'
        · exact l.triangle
        · exact gz.triangle
      arrow_base := by
        change eqToHom _ ≫ (Q.map lr.hbase).left ≫ eqToHom _ = _
        dsimp only [lr, TwoFibreProductOver.Hom.mk'_hbase]
        simpa [Functor.map_comp, eqToHom_map, Category.assoc] using l.arrow_base }
  let aa : wz.obj w' ⟶ z :=
    { ringHom := eqToHom hAlg
      arrow := 𝟙 z.point
      triangle := by simp [wz, w', ar]
      arrow_base := by simp; rfl }
  refine ⟨w', ll, aa, ?_, ?_, ?_⟩
  · apply IsHomLift.of_fac' _ _ _ rfl rfl
    change l.ringHom = 𝟙 _ ≫ gz.ringHom ≫ 𝟙 _
    simpa using hr
  · apply IsHomLift.of_fac' _ _ _ rfl rfl
    change (eqToHom hAlg) = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp
  · apply DeformationMorphism.ext_of_components
    · change l.ringHom = (eqToHom hAlg) ≫ gz.ringHom
      simpa using hr
    · change gz.arrow = gz.arrow ≫ 𝟙 z.point
      simp

end BaseChange

/-- **Stacks 07XV.** Smoothness on predeformation categories is stable under base change of
categories fibred in groupoids: if `f : 𝒳 ⟶ 𝒴` is smooth on predeformation categories, so is
the projection `𝒳 ×_𝒴 𝒵 ⟶ 𝒵`. -/
@[stacks 07XV]
public theorem isSmoothOnPredeformationCategories_twoFibreProductSnd
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS) (f : X ⥤ Y) (g : Z ⥤ Y)
    (_hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (_hpZ : pZ.IsFiberedInGroupoids)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ)
    (h : IsSmoothOnPredeformationCategories B S hS pX pY f hf) :
    IsSmoothOnPredeformationCategories B S hS
      (TwoFibreProductOver.structureFunctor pX pZ pY f g) pZ
      (TwoFibreProductOver.snd pX pZ pY f g)
      (by exact TwoFibreProductOver.snd_comp_eq) := by
  let Q : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let _ : Q.Faithful := post_faithful B S hS
  dsimp [IsSmoothOnPredeformationCategories] at h ⊢
  intro Λ k _ _ _ iΛ w₀ hw₀ hLFT hQC hOpen
  let pW := TwoFibreProductOver.structureFunctor pX pZ pY f g
  let s := TwoFibreProductOver.snd pX pZ pY f g
  have hbase : (pW ⋙ Q).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := hw₀
  have hs : s ⋙ pZ ⋙ Q = pW ⋙ Q := comp_over_eq TwoFibreProductOver.snd_comp_eq Q
  apply (isSmooth_explicitMap_iff iΛ (pW ⋙ Q) w₀ hbase (pZ ⋙ Q) s hs
    (mapPredeformationCategory iΛ (pW ⋙ Q) (pZ ⋙ Q) s hs w₀ hbase)).mp
  apply isSmooth_explicitMap_baseChange (k := k) iΛ Q
    (post_obj_injective B S hS) pX pY pZ f g hf hg w₀ hbase hpY
  have hx : (pX ⋙ Q).obj w₀.x =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    (congrArg Q.obj w₀.hx).trans hbase
  exact (isSmooth_explicitMap_iff iΛ (pX ⋙ Q) w₀.x hx (pY ⋙ Q) f (comp_over_eq hf Q)
    (mapPredeformationCategory iΛ (pX ⋙ Q) (pY ⋙ Q) f (comp_over_eq hf Q) w₀.x hx)).mpr
    (h iΛ w₀.x hx hLFT hQC hOpen)
end

end Deformation.Artin
