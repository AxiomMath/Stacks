module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Slice
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension.ResidueFieldPoint
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension.StalkChart
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension.ChangeOfFieldSquare
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.ResidueField.Comparison
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Versality after a finite extension of the residue field

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian
scheme `S`, let `x` be an object of `𝒳` over a scheme `U` locally of finite type over `S`, and
let `u₀` be a finite type point of `U`. For a finite extension `l` of the residue field
`κ(u₀)` this file shows that versality of `x` at `u₀` together with the Rim-Schlessinger
condition (RS) makes the morphism of predeformation categories
`𝓕_{(Sch/U)_fppf, l, u_{l,0}} ⟶ 𝓕_{𝒳, l, x_{l,0}}` smooth.

## Main results

* `Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt`: the statement above.

The argument is the one in the Stacks project: `(Sch/U)_fppf` satisfies (RS), so the morphism
in question is the change-of-fields morphism along `l/κ(u₀)` of the morphism of predeformation
categories at the residue field itself, and change of fields preserves smoothness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

-- `CategoryTheory.Functor.Fiber` is a plain `def`, so a term whose type mentions the underlying
-- object of a fibre -- such as the chosen cartesian lift `c.map f x`, whose source is
-- `(c.obj f x).1` where `(c.sliceFunctor x).obj f` is expected -- is not type-correct at
-- `implicit` transparency. Making it implicit-reducible here is what
-- `StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf` does for the same reason.
attribute [local implicit_reducible]
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.BasedFunctor.comp
  Deformation.changeOfFieldsBasedFunctor

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)

variable (x : X)
variable {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
variable (iΛ : Spec (.of Λ) ⟶ S) (uₗ₀ : Over (p.obj x))
variable (huₗ₀ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))

attribute [local instance] PredeformationConstruction.category

private theorem predeformation_morphism_ext
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (C : PredeformationConstruction i q y₀ hy₀)
    {a b : C.carrier} (f g : @Quiver.Hom C.carrier C.category.toQuiver a b)
    (hr : C.projection.map f = C.projection.map g)
    (ha : (C.morphisms a b f).arrow = (C.morphisms a b g).arrow) : f = g := by
  apply (C.morphisms a b).injective
  have hring : (C.morphisms a b f).ringHom = (C.morphisms a b g).ringHom := by
    rw [← C.morphism_projection f, ← C.morphism_projection g, hr]
  cases hf : C.morphisms a b f
  cases hg : C.morphisms a b g
  simp only [hf, hg] at hring ha
  cases hring
  cases ha
  rfl

private theorem predeformation_isHomLift_iff
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (C : PredeformationConstruction i q y₀ hy₀)
    {a b : C.carrier} (g : @Quiver.Hom C.carrier C.category.toQuiver a b)
    {D A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l} (f : D ⟶ A) :
    C.projection.IsHomLift f g ↔
      ∃ (ha : (C.objects a).algebra = D) (hb : (C.objects b).algebra = A),
        (C.morphisms a b g).ringHom = eqToHom ha ≫ f ≫ eqToHom hb.symm := by
  let : Category C.carrier := C.category
  constructor
  · intro hg
    let := hg
    refine ⟨(C.object_projection a).symm.trans (IsHomLift.domain_eq C.projection f g),
      (C.object_projection b).symm.trans (IsHomLift.codomain_eq C.projection f g), ?_⟩
    rw [← C.morphism_projection g, IsHomLift.fac' C.projection f g]
    simp
  · rintro ⟨ha, hb, hg⟩
    apply IsHomLift.of_fac C.projection f g
      ((C.object_projection a).trans ha) ((C.object_projection b).trans hb)
    have h := C.morphism_projection g
    rw [hg] at h
    simpa using congrArg
      (fun z => eqToHom ha.symm ≫ z ≫ eqToHom hb) h.symm

private theorem induced_predeformation_algebra_eq
    {Y : Type v} [Category.{w} Y] {Z : Type*} [Category Z]
    (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S)
    (F : Y ⥤ Z) (hF : F ⋙ qZ = qY)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : qY.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (G : InducedPredeformationFunctor i qY qZ F hF y₀ hy₀)
    (a : (predeformationCategory i qY y₀ hy₀).carrier) :
    ((predeformationCategory i qZ (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀)).objects (G.toFunctor.obj a)).algebra =
      ((predeformationCategory i qY y₀ hy₀).objects a).algebra := by
  rw [← (predeformationCategory i qZ (F.obj y₀) _).object_projection,
    ← (predeformationCategory i qY y₀ hy₀).object_projection]
  exact congrArg (fun H => H.obj a) G.projection_comm

private def mapDeformationObject
    {Y : Type v} [Category.{w} Y] {Z : Type*} [Category Z]
    (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S)
    (F : Y ⥤ Z) (hF : F ⋙ qZ = qY)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : qY.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (a : DeformationObject i qY y₀ hy₀) :
    DeformationObject i qZ (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀) := by
  exact
    { algebra := a.algebra
      point := F.obj a.point
      arrow := F.map a.arrow
      base := (congrArg (fun H : Y ⥤ Over S => H.obj a.point) hF).trans a.base
      arrow_base := by
        subst qY
        exact a.arrow_base }

private theorem deformationObject_ext
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (a b : DeformationObject i q y₀ hy₀)
    (hA : a.algebra = b.algebra) (hx : a.point = b.point)
    (ha : a.arrow = b.arrow ≫ eqToHom hx.symm) : a = b := by
  cases a
  cases b
  dsimp at hA hx ha
  cases hA
  cases hx
  simpa using ha

private theorem induced_predeformation_object_eq
    {Y : Type v} [Category.{w} Y] {Z : Type*} [Category Z]
    (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S)
    (F : Y ⥤ Z) (hF : F ⋙ qZ = qY)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : qY.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (G : InducedPredeformationFunctor i qY qZ F hF y₀ hy₀)
    (a : (predeformationCategory i qY y₀ hy₀).carrier) :
    (predeformationCategory i qZ (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀)).objects (G.toFunctor.obj a) =
      mapDeformationObject S qY qZ F hF i y₀ hy₀
        ((predeformationCategory i qY y₀ hy₀).objects a) := by
  subst qY
  exact deformationObject_ext S _ i _ _ _ _
    (induced_predeformation_algebra_eq S _ _ F rfl i y₀ hy₀ G a)
    (G.object_point a) (G.object_arrow a)

/-- A surjective morphism of Artinian local algebras stays surjective after transport along
equalities of its source and target. -/
public theorem surjective_artinianHom_transport
    {A B A' B' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l}
    (e : A' = A) (e' : B' = B) (f : A ⟶ B) (hf : Function.Surjective f.hom) :
    Function.Surjective (eqToHom e ≫ f ≫ eqToHom e'.symm).hom := by
  cases e
  cases e'
  simpa using hf

private theorem deformationMorphism_cast_ringHom
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    {a b c d : DeformationObject i q y₀ hy₀}
    (e : a = c) (e' : b = d) (g : DeformationMorphism i q y₀ hy₀ a b) :
    (e' ▸ e ▸ g).ringHom =
      eqToHom (congrArg DeformationObject.algebra e).symm ≫
        g.ringHom ≫ eqToHom (congrArg DeformationObject.algebra e') := by
  cases e
  cases e'
  simp

private theorem deformationMorphism_cast_arrow
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    {a b c d : DeformationObject i q y₀ hy₀}
    (e : a = c) (e' : b = d) (g : DeformationMorphism i q y₀ hy₀ a b) :
    (e' ▸ e ▸ g).arrow =
      eqToHom (congrArg DeformationObject.point e').symm ≫
        g.arrow ≫ eqToHom (congrArg DeformationObject.point e) := by
  cases e
  cases e'
  simp

attribute [local implicit_reducible] Functor.Fiber BasedCategory.ofFunctor
  InducedPredeformationFunctor.toBasedFunctor mapDeformationObject

private theorem isSmooth_induced_of_deformation_lifting
    {Y : Type v} [Category.{w} Y] {Z : Type*} [Category Z]
    (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S) (F : Y ⥤ Z)
    (hF : F ⋙ qZ = qY) (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : qY.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (G : InducedPredeformationFunctor i qY qZ F hF y₀ hy₀)
    (hLift : ∀ (a : DeformationObject i qY y₀ hy₀)
      (b : DeformationObject i qZ (F.obj y₀)
        (imageBasePoint i qY qZ F hF y₀ hy₀))
      (g : DeformationMorphism i qZ (F.obj y₀)
        (imageBasePoint i qY qZ F hF y₀ hy₀) b
          (mapDeformationObject S qY qZ F hF i y₀ hy₀ a)),
      Function.Surjective g.ringHom.hom →
      ∃ (a' : DeformationObject i qY y₀ hy₀)
        (h : DeformationMorphism i qY y₀ hy₀ a' a)
        (α : DeformationMorphism i qZ (F.obj y₀)
          (imageBasePoint i qY qZ F hF y₀ hy₀)
          (mapDeformationObject S qY qZ F hF i y₀ hy₀ a') b)
        (hA : a'.algebra = b.algebra),
        h.ringHom = eqToHom hA ≫ g.ringHom ∧ α.ringHom = eqToHom hA ∧
          F.map h.arrow = g.arrow ≫ α.arrow) :
    Deformation.IsSmooth G.toBasedFunctor := by
  let C := predeformationCategory i qY y₀ hy₀
  let D := predeformationCategory i qZ (F.obj y₀)
    (imageBasePoint i qY qZ F hF y₀ hy₀)
  change ∀ ⦃B A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l⦄ (f : B ⟶ A),
    Function.Surjective f.hom → ∀ (y : D.carrier) (z : C.carrier)
      (g : y ⟶ G.toFunctor.obj z), D.projection.IsHomLift f g →
      ∃ (z' : C.carrier) (h : z' ⟶ z) (α : G.toFunctor.obj z' ⟶ y),
        C.projection.IsHomLift f h ∧ D.projection.IsHomLift (𝟙 B) α ∧
          G.toFunctor.map h = α ≫ g
  intro B A f hf y z g hg
  have hobj : D.objects (G.toFunctor.obj z) =
      mapDeformationObject S qY qZ F hF
        i y₀ hy₀ (C.objects z) :=
    induced_predeformation_object_eq S qY qZ
      F hF i y₀ hy₀ G z
  let a := C.objects z
  let b := D.objects y
  let gm : DeformationMorphism i qZ (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀) b
      (mapDeformationObject S qY qZ F hF
        i y₀ hy₀ a) :=
    hobj ▸ D.morphisms y (G.toFunctor.obj z) g
  obtain ⟨hB, hA, he⟩ :=
    (predeformation_isHomLift_iff S qZ i (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀) D g f).mp hg
  have haA : a.algebra = A :=
    (congrArg DeformationObject.algebra hobj).symm.trans hA
  have hgmRing : gm.ringHom = eqToHom hB ≫ f ≫ eqToHom haA.symm := by
    have hc := deformationMorphism_cast_ringHom S qZ i (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀) rfl hobj
      (D.morphisms y (G.toFunctor.obj z) g)
    dsimp only at hc
    rw [he] at hc
    simpa [gm, Category.assoc] using hc
  have hgm : Function.Surjective gm.ringHom.hom := by
    rw [hgmRing]
    exact surjective_artinianHom_transport hB haA f hf
  obtain ⟨b', hm, am, hbalg, hhmring, hamring, hcomm⟩ := hLift a b gm hgm
  let z' := C.objects.symm b'
  have hz' : C.objects z' = b' := C.objects.apply_symm_apply b'
  let h : z' ⟶ z := (C.morphisms z' z).symm (hz'.symm ▸ hm)
  have hh : (C.morphisms z' z h) = hz'.symm ▸ hm := Equiv.apply_symm_apply _ _
  have hzG : D.objects (G.toFunctor.obj z') =
      mapDeformationObject S qY qZ F hF i y₀ hy₀ b' := by
    rw [induced_predeformation_object_eq S qY qZ F hF i y₀ hy₀ G z', hz']
  let α : G.toFunctor.obj z' ⟶ y :=
    (D.morphisms (G.toFunctor.obj z') y).symm (hzG.symm ▸ am)
  have hα : D.morphisms (G.toFunctor.obj z') y α = hzG.symm ▸ am :=
    Equiv.apply_symm_apply _ _
  have hhlift : C.projection.IsHomLift f h := by
    apply (predeformation_isHomLift_iff S qY i y₀ hy₀ C h f).mpr
    refine ⟨(congrArg DeformationObject.algebra hz').trans (hbalg.trans hB), haA, ?_⟩
    rw [hh]
    have hc := deformationMorphism_cast_ringHom S qY i
      y₀ hy₀ hz'.symm rfl hm
    simpa [hhmring, hgmRing, Category.assoc] using hc
  have hαlift : D.projection.IsHomLift (𝟙 B) α := by
    apply (predeformation_isHomLift_iff S qZ i (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀) D α (𝟙 B)).mpr
    refine ⟨(congrArg DeformationObject.algebra hzG).trans (hbalg.trans hB), hB, ?_⟩
    rw [hα]
    have hc := deformationMorphism_cast_ringHom S qZ i (F.obj y₀)
      (imageBasePoint i qY qZ F hF y₀ hy₀) hzG.symm rfl am
    simpa [hamring, Category.assoc] using hc
  refine ⟨z', h, α, hhlift, hαlift, ?_⟩
  apply predeformation_morphism_ext S qZ i (F.obj y₀) (imageBasePoint i qY qZ F hF y₀ hy₀) D
  · let := hhlift
    let := hαlift
    let := hg
    have hmap : D.projection.IsHomLift f (G.toFunctor.map h) :=
      (BasedFunctor.isHomLift_iff G.toBasedFunctor f h).mpr hhlift
    let := hmap
    have hcomp : D.projection.IsHomLift f (α ≫ g) :=
      IsHomLift.comp_lift_id_left D.projection f g α
    let := hcomp
    rw [IsHomLift.fac' D.projection f (G.toFunctor.map h),
      IsHomLift.fac' D.projection f (α ≫ g)]
  · rw [D.reversed_composition]
    have hGarrow : (D.morphisms _ _ (G.toFunctor.map h)).arrow =
        eqToHom (G.object_point z) ≫
          F.map (C.morphisms _ _ h).arrow ≫
            eqToHom (G.object_point z').symm := G.morphism_arrow h
    have hharrow : (C.morphisms _ _ h).arrow = hm.arrow ≫
        eqToHom (congrArg DeformationObject.point hz').symm := by
      rw [hh]
      simpa using deformationMorphism_cast_arrow S qY i
        y₀ hy₀ hz'.symm rfl hm
    have hαarrow : (D.morphisms _ _ α).arrow =
        am.arrow ≫ eqToHom (congrArg DeformationObject.point hzG).symm := by
      rw [hα]
      simpa using deformationMorphism_cast_arrow S qZ i (F.obj y₀)
        (imageBasePoint i qY qZ F hF y₀ hy₀) hzG.symm rfl am
    have hgmarrow : gm.arrow =
        eqToHom (congrArg DeformationObject.point hobj).symm ≫
          (D.morphisms _ _ g).arrow := by
      simpa [gm] using deformationMorphism_cast_arrow S qZ i (F.obj y₀)
        (imageBasePoint i qY qZ F hF y₀ hy₀) rfl hobj
        (D.morphisms y (G.toFunctor.obj z) g)
    rw [hGarrow, hharrow, hαarrow]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc]
    rw [hcomm, hgmarrow]
    simp [Category.assoc]


private theorem isSmooth_slice_of_deformation_lifting
    (c : p.ChoiceOfPullbacks)
    (G : InducedPredeformationFunctor iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀)
    (hLift : ∀
      (a : DeformationObject iΛ
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀)
      (b : DeformationObject iΛ (p ⋙ Over.post B.inclusion)
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
        (imageBasePoint iΛ _ _ _
          (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀))
      (g : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion)
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
        (imageBasePoint iΛ _ _ _
          (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀) b
        (mapDeformationObject S _ _ _ (sliceFunctor_comp_post B S hS p c x)
          iΛ uₗ₀ huₗ₀ a)),
      Function.Surjective g.ringHom.hom →
      ∃ v : b.point ⟶ x,
        g.arrow ≫ v = c.map a.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))) :
    Deformation.IsSmooth G.toBasedFunctor := by
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  apply isSmooth_induced_of_deformation_lifting S _ _ _ _ _ _ _ G
  intro a b g hg
  obtain ⟨v, hv⟩ := hLift a b g hg
  have h₀ : p.obj (F.obj uₗ₀) = uₗ₀.left := (c.obj uₗ₀.hom ⟨x, rfl⟩).property
  have ha : p.obj (F.obj a.point) = a.point.left :=
    (c.obj a.point.hom ⟨x, rfl⟩).property
  have hb : b.arrow ≫ v = c.map uₗ₀.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)) := by
    rw [← g.triangle, Category.assoc, hv]
    exact c.sliceFunctor_map_fac _ a.arrow
  let z : Over (p.obj x) := Over.mk (p.map v)
  let r : uₗ₀.left ⟶ p.obj b.point := eqToHom h₀.symm ≫ p.map b.arrow
  have hr : r ≫ z.hom = uₗ₀.hom := by
    dsimp [r, z]
    rw [Category.assoc, ← p.map_comp, hb]
    let := c.isStronglyCartesian uₗ₀.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
    rw [IsHomLift.fac' p uₗ₀.hom (c.map uₗ₀.hom ⟨x, rfl⟩)]
    simp
  let b' : DeformationObject iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀ :=
    { algebra := b.algebra
      point := z
      arrow := Over.homMk r hr
      base := b.base
      arrow_base := by
        simpa [r, Functor.comp_map, Over.comp_left, Over.eqToHom_left,
          eqToHom_map, Category.assoc, eqToHom_trans_assoc] using b.arrow_base }
  let v' := c.map z.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let := c.isStronglyCartesian z.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let : p.IsCartesian (p.map v) v' := by
    dsimp [v', z]
    infer_instance
  let α : b.point ⟶ F.obj z := Functor.IsCartesian.map p (p.map v) v' v
  have hα : α ≫ v' = v := Functor.IsCartesian.fac p (p.map v) v' v
  have hαlift : p.IsHomLift (𝟙 (p.obj b.point)) α :=
    Functor.IsCartesian.map_isHomLift p (p.map v) v' v
  let := hαlift
  have hbarr : b.arrow ≫ α = F.map b'.arrow := by
    let : p.IsHomLift r (F.map b'.arrow) :=
      c.sliceFunctor_map_isHomLift (⟨x, rfl⟩ : p.Fiber (p.obj x)) b'.arrow
    have hbr : p.IsHomLift r b.arrow :=
      IsHomLift.of_fac' p r b.arrow h₀ rfl (by simp [r])
    let := hbr
    have hbrα : p.IsHomLift r (b.arrow ≫ α) :=
      IsHomLift.comp_lift_id_right p r b.arrow α
    let := hbrα
    apply Functor.IsStronglyCartesian.ext p z.hom v' r
    rw [Category.assoc, hα, hb]
    exact (c.sliceFunctor_map_fac _ b'.arrow).symm
  let am : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion)
      (F.obj uₗ₀) (imageBasePoint iΛ _ _ F
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀)
      (mapDeformationObject S _ _ F (sliceFunctor_comp_post B S hS p c x)
        iΛ uₗ₀ huₗ₀ b') b :=
    { ringHom := 𝟙 b.algebra
      arrow := α
      triangle := hbarr
      arrow_base := by
        have hmap := IsHomLift.fac' p (𝟙 (p.obj b.point)) α
        simp only [Over.mk_left, ObjectProperty.ι_obj, Functor.comp_obj, Functor.comp_map, hmap,
          Functor.ChoiceOfPullbacks.sliceFunctor_obj, eqToHom_refl, Category.id_comp, Over.post_map,
          ObjectProperty.ι_map, Over.eqToHom_left, ObjectProperty.eqToHom_hom, Over.homMk_left,
          eqToHom_trans, ArtinianLocalAlgCat.id_hom, AlgHom.toRingHom_eq_coe]
        change 𝟙 _ = Spec.map (𝟙 _)
        simp }
  let t : a.point.left ⟶ p.obj b.point := eqToHom ha.symm ≫ p.map g.arrow
  have ht : t ≫ z.hom = a.point.hom := by
    dsimp [t, z]
    rw [Category.assoc, ← p.map_comp, hv]
    let := c.isStronglyCartesian a.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
    rw [IsHomLift.fac' p a.point.hom (c.map a.point.hom ⟨x, rfl⟩)]
    simp
  let hm : DeformationMorphism iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀ b' a :=
    { ringHom := g.ringHom
      arrow := Over.homMk t ht
      triangle := by
        apply Over.OverMorphism.ext
        change a.arrow.left ≫ t = r
        have hm := IsHomLift.fac' p a.arrow.left (F.map a.arrow)
        have htri := congrArg p.map g.triangle
        change p.map (F.map a.arrow ≫ g.arrow) = p.map b.arrow at htri
        simp only [Functor.map_comp] at htri
        simpa [t, r, hm, Category.assoc] using
          congrArg (fun f => eqToHom h₀.symm ≫ f) htri
      arrow_base := by
        simpa [t, Functor.comp_map, Over.comp_left, Over.eqToHom_left,
          eqToHom_map, Category.assoc, eqToHom_trans_assoc] using g.arrow_base }
  refine ⟨b', hm, am, rfl, by simp [hm], by rfl, ?_⟩
  change F.map hm.arrow = g.arrow ≫ α
  let : p.IsHomLift t (F.map hm.arrow) :=
    c.sliceFunctor_map_isHomLift (⟨x, rfl⟩ : p.Fiber (p.obj x)) hm.arrow
  have hgt : p.IsHomLift t g.arrow :=
    IsHomLift.of_fac' p t g.arrow ha rfl (by simp [t])
  let := hgt
  have hgtα : p.IsHomLift t (g.arrow ≫ α) :=
    IsHomLift.comp_lift_id_right p t g.arrow α
  let := hgtα
  apply Functor.IsStronglyCartesian.ext p z.hom v' t
  rw [Category.assoc, hα, hv]
  exact c.sliceFunctor_map_fac _ hm.arrow

private theorem deformation_lifting_of_isSmooth_slice
    (c : p.ChoiceOfPullbacks)
    (G : InducedPredeformationFunctor iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀)
    (hs : Deformation.IsSmooth G.toBasedFunctor)
    (a : DeformationObject iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀)
    (b : DeformationObject iΛ (p ⋙ Over.post B.inclusion)
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
      (imageBasePoint iΛ _ _ _
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀))
    (g : DeformationMorphism iΛ (p ⋙ Over.post B.inclusion)
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
      (imageBasePoint iΛ _ _ _
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀) b
      (mapDeformationObject S _ _ _ (sliceFunctor_comp_post B S hS p c x)
        iΛ uₗ₀ huₗ₀ a))
    (hg : Function.Surjective g.ringHom.hom) :
    ∃ v : b.point ⟶ x,
      g.arrow ≫ v = c.map a.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)) := by
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let q := p ⋙ Over.post B.inclusion
  let C := predeformationCategory iΛ
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀
  let D := predeformationCategory iΛ q (F.obj uₗ₀)
    (imageBasePoint iΛ _ q F (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀)
  let z := C.objects.symm a
  let y := D.objects.symm b
  have hz : C.objects z = a := C.objects.apply_symm_apply a
  have hy : D.objects y = b := D.objects.apply_symm_apply b
  have hzG : D.objects (G.toFunctor.obj z) =
      mapDeformationObject S _ q F (sliceFunctor_comp_post B S hS p c x)
        iΛ uₗ₀ huₗ₀ a := by
    rw [induced_predeformation_object_eq S _ q F
      (sliceFunctor_comp_post B S hS p c x) iΛ uₗ₀ huₗ₀ G z, hz]
  let g' : y ⟶ G.toFunctor.obj z :=
    (D.morphisms y (G.toFunctor.obj z)).symm (hzG.symm ▸ hy.symm ▸ g)
  have hg' : D.morphisms _ _ g' = hzG.symm ▸ hy.symm ▸ g :=
    (D.morphisms _ _).apply_symm_apply _
  have hglift : D.projection.IsHomLift g.ringHom g' := by
    apply (predeformation_isHomLift_iff S q iΛ _ _ D g' g.ringHom).mpr
    refine ⟨congrArg DeformationObject.algebra hy,
      congrArg DeformationObject.algebra hzG, ?_⟩
    rw [hg']
    simpa using deformationMorphism_cast_ringHom S q iΛ _ _ hy.symm hzG.symm g
  obtain ⟨z', h, α, _, _, hcomp⟩ := hs g.ringHom hg y z g' hglift
  have hcomp' := congrArg (fun f => (D.morphisms _ _ f).arrow) hcomp
  rw [D.reversed_composition] at hcomp'
  have hmap := G.morphism_arrow h
  have hgarrow : (D.morphisms _ _ g').arrow =
      eqToHom (congrArg DeformationObject.point hzG) ≫ g.arrow ≫
        eqToHom (congrArg DeformationObject.point hy).symm := by
    rw [hg']
    simpa using deformationMorphism_cast_arrow S q iΛ _ _ hy.symm hzG.symm g
  change (D.morphisms _ _ (G.toFunctor.map h)).arrow =
    (D.morphisms _ _ g').arrow ≫ (D.morphisms _ _ α).arrow at hcomp'
  change (D.morphisms _ _ (G.toFunctor.map h)).arrow = _ at hmap
  rw [hmap, hgarrow] at hcomp'
  let t := eqToHom (congrArg DeformationObject.point hy).symm ≫
    (D.morphisms _ _ α).arrow ≫ eqToHom (G.object_point z')
  have ht : F.map (eqToHom (congrArg DeformationObject.point hz).symm ≫
      (C.morphisms _ _ h).arrow) = g.arrow ≫ t := by
    have he := congrArg (fun f =>
      eqToHom (congrArg DeformationObject.point hzG).symm ≫ f ≫
        eqToHom (G.object_point z')) hcomp'
    simpa [t, Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc] using he
  refine ⟨t ≫ c.map (C.objects z').point.hom ⟨x, rfl⟩, ?_⟩
  rw [← Category.assoc, ← ht]
  exact c.sliceFunctor_map_fac _ _

private theorem isSmooth_slice_of_isSmooth_stalk
    (c : p.ChoiceOfPullbacks)
    (s : S) [Algebra (S.presheaf.stalk s) l]
    (iR : Spec (.of (S.presheaf.stalk s : Type u)) ⟶ S) (hiR : iR = S.fromSpecStalk s)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) l)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)
    (hs : (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) l)) ≫ iR)
      (IsLocalRing.closedPoint l) = s)
    (huR : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) l)) ≫ iR))
    (hsm : Deformation.IsSmooth
      (mapPredeformationCategory iR
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
        (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huR).toBasedFunctor) :
    Deformation.IsSmooth
      (mapPredeformationCategory iΛ
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
        (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀).toBasedFunctor := by
  apply isSmooth_slice_of_deformation_lifting B S hS p x iΛ uₗ₀ huₗ₀ c
  intro a b g hg
  let gl := Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) l)) ≫ iR
  have hglR : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) l)) ≫
      S.fromSpecStalk s = gl := by rw [← hiR]
  let A := chartArtinObjectOverStalk S a.algebra iΛ gl s hs hglR hpoint.symm
  let D := chartArtinObjectOverStalk S b.algebra iΛ gl s hs hglR hpoint.symm
  let f : D ⟶ A := chartArtinHomOverStalk S b.algebra a.algebra g.ringHom
    iΛ gl s hs hglR hpoint.symm
  have hA : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ a.algebra)) ≫ iΛ := by
    rw [hiR]
    exact chartArtin_base_eq_stalk S a.algebra iΛ gl s hs hpoint.symm
  have hD : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) D)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ b.algebra)) ≫ iΛ := by
    rw [hiR]
    exact chartArtin_base_eq_stalk S b.algebra iΛ gl s hs hpoint.symm
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let aR : DeformationObject iR
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huR :=
    { algebra := A
      point := a.point
      arrow := a.arrow
      base := a.base.trans (congrArg Over.mk hA.symm)
      arrow_base := a.arrow_base }
  let bR : DeformationObject iR (p ⋙ Over.post B.inclusion)
      (F.obj uₗ₀) (imageBasePoint iR _ _ F
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huR) :=
    { algebra := D
      point := b.point
      arrow := b.arrow
      base := b.base.trans (congrArg Over.mk hD.symm)
      arrow_base := b.arrow_base }
  let gR : DeformationMorphism iR (p ⋙ Over.post B.inclusion)
      (F.obj uₗ₀) (imageBasePoint iR _ _ F
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huR) bR
      (mapDeformationObject S _ _ F (sliceFunctor_comp_post B S hS p c x)
        iR uₗ₀ huR aR) :=
    { ringHom := f
      arrow := g.arrow
      triangle := g.triangle
      arrow_base := g.arrow_base }
  exact deformation_lifting_of_isSmooth_slice B S hS p x iR
    uₗ₀ huR c _ hsm aR bR gR hg

private theorem isSmooth_of_basedIso
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat Λ k)}
    {𝓖 : BasedCategory (Deformation.ArtinianLocalAlgCat Λ k)}
    {φ ψ : BasedFunctor 𝓕 𝓖} (e : φ ≅ ψ)
    (hψ : Deformation.IsSmooth ψ) : Deformation.IsSmooth φ := by
  intro B A f hf y x g hg
  let := hg
  have hg' : 𝓖.p.IsHomLift f (g ≫ e.hom.app x) := by
    let := e.hom.isHomLift ((BasedFunctor.w_obj φ x).symm.trans
      (IsHomLift.codomain_eq 𝓖.p f g))
    exact inferInstance
  obtain ⟨x', h, a, hh, ha, hfac⟩ := hψ f hf y x (g ≫ e.hom.app x) hg'
  let := hh
  let := ha
  refine ⟨x', h, e.hom.app x' ≫ a, hh, ?_, ?_⟩
  · let := e.hom.isHomLift (IsHomLift.domain_eq 𝓕.p f h)
    exact inferInstance
  · apply (cancel_mono (e.hom.app x)).1
    rw [e.hom.naturality h, hfac]
    simp [Category.assoc]

private theorem predeformation_hom_of_pointHom
    {Y : Type*} [Category Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (C : PredeformationConstruction i q y₀ hy₀)
    (a b : C.carrier) (hA : (C.objects a).algebra = (C.objects b).algebra)
    (e : q.obj (C.objects b).point = q.obj (C.objects a).point)
    (t : (C.objects b).point ⟶ (C.objects a).point)
    (ht : q.map t = eqToHom e) (htri : (C.objects b).arrow ≫ t = (C.objects a).arrow) :
    ∃ f : a ⟶ b, C.projection.IsHomLift (𝟙 (C.projection.obj a)) f ∧
      (C.morphisms a b f).arrow = t := by
  let m : DeformationMorphism i q y₀ hy₀ (C.objects a) (C.objects b) :=
    { ringHom := eqToHom hA
      arrow := t
      triangle := htri
      arrow_base := by
        rw [ht, Over.eqToHom_left]
        have hh : ∀ {A D : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l} (h : A = D),
            Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) =
              eqToHom (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l =>
                Spec (.of A)) h).symm := by
          intro A D h
          cases h
          change Spec.map (𝟙 _) = 𝟙 _
          simp
        rw [hh]
        simp }
  refine ⟨(C.morphisms a b).symm m, ?_, by simp [m]⟩
  apply (predeformation_isHomLift_iff S q i y₀ hy₀ C _ _).mpr
  refine ⟨(C.object_projection a).symm,
    hA.symm.trans (C.object_projection a).symm, ?_⟩
  simp [m]

private theorem basedIso_of_deformation_maps
    {Y : Type*} [Category Y] (q : Y ⥤ Over S)
    (hq : ∀ {a b c : Y} (f : a ⟶ c) (g : b ⟶ c) (h : q.obj b ⟶ q.obj a),
      h ≫ q.map f = q.map g → ∃! t : b ⟶ a, q.map t = h ∧ t ≫ f = g)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (C : PredeformationConstruction i q y₀ hy₀)
    (hC : Deformation.IsCofiberedInGroupoids C.projection)
    {E : BasedCategory (Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)}
    (H K : BasedFunctor E (BasedCategory.ofFunctor C.projection)) (x : Y)
    (vH : ∀ a, (C.objects (H.obj a)).point ⟶ x)
    (vK : ∀ a, (C.objects (K.obj a)).point ⟶ x)
    (e : ∀ a, q.obj (C.objects (K.obj a)).point = q.obj (C.objects (H.obj a)).point)
    (hbase : ∀ a, eqToHom (e a) ≫ q.map (vH a) = q.map (vK a))
    (htri : ∀ a, (C.objects (K.obj a)).arrow ≫ vK a =
      (C.objects (H.obj a)).arrow ≫ vH a)
    (hnH : ∀ {a b} (f : a ⟶ b), (C.morphisms _ _ (H.map f)).arrow ≫ vH a = vH b)
    (hnK : ∀ {a b} (f : a ⟶ b), (C.morphisms _ _ (K.map f)).arrow ≫ vK a = vK b) :
    Nonempty (H ≅ K) := by
  have hA (a) : (C.objects (H.obj a)).algebra = (C.objects (K.obj a)).algebra :=
    (C.object_projection _).symm.trans ((H.w_obj a).trans
      ((K.w_obj a).symm.trans (C.object_projection _)))
  choose t ht hu using fun a => hq (vH a) (vK a) (eqToHom (e a)) (hbase a)
  have htriangle (a) : (C.objects (K.obj a)).arrow ≫ t a =
      (C.objects (H.obj a)).arrow := by
    apply (hq (vH a) ((C.objects (H.obj a)).arrow ≫ vH a)
      (q.map (C.objects (H.obj a)).arrow) (by simp)).unique
    · refine ⟨?_, ?_⟩
      · rw [q.map_comp, (ht a).1]
        exact deformation_arrow_map_eq S q i y₀ hy₀ _ _ (hA a) (e a)
      · rw [Category.assoc, (ht a).2, htri]
    · exact ⟨rfl, rfl⟩
  choose α hαlift hα using fun a => predeformation_hom_of_pointHom S q i y₀ hy₀ C
    (H.obj a) (K.obj a) (hA a) (e a) (t a) (ht a).1 (htriangle a)
  have hlift (a) : C.projection.IsHomLift (𝟙 (E.p.obj a)) (α a) :=
    H.w_obj a ▸ hαlift a
  let n : H ⟶ K :=
    { app := α
      isHomLift' := hlift
      naturality := by
        intro a b f
        have heq : C.projection.map (H.map f ≫ α b) = C.projection.map (α a ≫ K.map f) := by
          let := hlift a
          let := hlift b
          let : C.projection.IsHomLift (E.p.map f) (H.map f) :=
            BasedFunctor.preserves_isHomLift H _ _
          let : C.projection.IsHomLift (E.p.map f) (K.map f) :=
            BasedFunctor.preserves_isHomLift K _ _
          rw [IsHomLift.fac' C.projection (E.p.map f) (H.map f ≫ α b),
            IsHomLift.fac' C.projection (E.p.map f) (α a ≫ K.map f)]
        apply predeformation_morphism_ext S q i y₀ hy₀ C _ _ heq
        apply (hq (vH a) ((C.morphisms _ _ (H.map f ≫ α b)).arrow ≫ vH a)
          (q.map (C.morphisms _ _ (H.map f ≫ α b)).arrow) (by simp)).unique
        · exact ⟨rfl, rfl⟩
        · refine ⟨(predeformation_map_eq_of_projection_eq S q i y₀ hy₀ C _ _ heq).symm, ?_⟩
          rw [C.reversed_composition, C.reversed_composition, hα a, hα b]
          rw [Category.assoc, (ht a).2, hnK, Category.assoc, hnH, (ht b).2] }
  have hi (a) : IsIso (α a) := by
    have hh := hlift a
    have hop : C.projection.op.IsHomLift (𝟙 (Opposite.op (E.p.obj a))) (α a).op := by
      let := hh
      apply IsHomLift.of_fac' _ _ _
        (congrArg Opposite.op (IsHomLift.codomain_eq C.projection (𝟙 (E.p.obj a)) (α a)))
        (congrArg Opposite.op (IsHomLift.domain_eq C.projection (𝟙 (E.p.obj a)) (α a)))
      simpa [Functor.op_map] using congrArg Quiver.Hom.op
        (IsHomLift.fac' C.projection (𝟙 (E.p.obj a)) (α a))
    let := hop
    let := hC.isStronglyCartesian_homLift (𝟙 (Opposite.op (E.p.obj a))) (α a).op
    have := Functor.IsStronglyCartesian.isIso_of_base_isIso C.projection.op
      (𝟙 (Opposite.op (E.p.obj a))) (α a).op
    exact isIso_of_op (α a)
  let : ∀ a, IsIso (n.toNatTrans.app a) := hi
  let : IsIso n.toNatTrans := NatIso.isIso_of_isIso_app _
  let : IsIso n := BasedNatIso.isIso_of_toNatTrans_isIso n
  exact ⟨asIso n⟩

private theorem deformationProjection_map
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
    (i : Spec (.of T.Λ) ⟶ S)
    {Y : Type*} [Category Y] (pY : Y ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (F : Y ⥤ X) (hF : F ⋙ (p ⋙ Over.post B.inclusion) = pY ⋙ Over.post B.inclusion)
    (y₀ : Y) (hy₀ : (pY ⋙ Over.post B.inclusion).obj y₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ i))
    (G : InducedPredeformationFunctor i
      (pY ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion) F hF y₀ hy₀)
    (a : Deformation.ChangeOfFieldsCategory T
      (predeformationCategory i (pY ⋙ Over.post B.inclusion) y₀ hy₀).projection) :
    Site.deformationProjection T i B hS p (F.obj y₀)
      (imageBasePoint i _ _ F hF y₀ hy₀)
      ((Deformation.changeOfFieldsBasedFunctor T G.toBasedFunctor).obj a) =
    (Site.deformationProjection T i B hS pY y₀ hy₀ a).comp
      (eqToHom (induced_predeformation_algebra_eq S _ _ F hF i y₀ hy₀ G a.fst)).hom.toRingHom := by
  let C := predeformationCategory i (pY ⋙ Over.post B.inclusion) y₀ hy₀
  let D := predeformationCategory i (p ⋙ Over.post B.inclusion) (F.obj y₀)
    (imageBasePoint i _ _ F hF y₀ hy₀)
  let M := Deformation.changeOfFieldsBasedFunctor T G.toBasedFunctor
  have he := induced_predeformation_algebra_eq S _ _ F hF i y₀ hy₀ G a.fst
  have hh : eqToHom (D.object_projection (G.toFunctor.obj a.fst)).symm ≫
      (M.obj a).iso.hom =
      eqToHom he ≫ (eqToHom (C.object_projection a.fst).symm ≫ a.iso.hom) := by
    simp [M, Deformation.changeOfFieldsBasedFunctor,
      CategoryTheory.Limits.CategoricalPullback.map_obj_iso_hom]
  unfold Site.deformationProjection
  change (Site.comparisonProjection T a.snd).comp
    (eqToHom (D.object_projection (G.toFunctor.obj a.fst)).symm ≫
      (M.obj a).iso.hom).hom.toRingHom = _
  rw [hh]
  rfl

/-- Two morphisms out of objects identified with a common third one agree once both have been
normalised against a single morphism out of that third object. -/
private theorem eqToHom_comp_left_eq {𝒞 : Type*} [Category 𝒞] {P Q N Z : 𝒞}
    (eP : P = N) (eQ : Q = N) {u : Q ⟶ Z} {v : P ⟶ Z} {R : N ⟶ Z}
    (hu : eqToHom eQ.symm ≫ u = R) (hv : eqToHom eP.symm ≫ v = R) :
    eqToHom (eP.trans eQ.symm) ≫ u = v := by
  subst eP
  subst eQ
  simp only [eqToHom_refl, Category.id_comp] at hu hv ⊢
  exact hu.trans hv.symm

/-- The structure morphism to `x` of the object obtained by mapping to `𝒳` first and then
restricting, read off over the base of the `k`-level deformation. The other half of the
base-compatibility input of `basedIso_changeOfFieldFunctor`. -/
private theorem basedIso_changeOfFieldFunctor_baseTarget
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u}) (iT : Spec (.of T.Λ) ⟶ S)
    (c : p.ChoiceOfPullbacks)
    (uκ uₗ : Over (p.obj x))
    (huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uκ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (δ : uₗ ⟶ uκ)
    (hxκ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uκ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (hxₗ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (Gκs : InducedPredeformationFunctor iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uκ huκ)
    (Et : Site.ChangeOfFieldFunctor T iT B hS p
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uκ)
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) hxκ hxₗ
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).map δ))
    (a : Deformation.ChangeOfFieldsCategory T
      (predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).projection)
    (bK : (p ⋙ Over.post B.inclusion).obj
        ((predeformationCategory iT (p ⋙ Over.post B.inclusion)
            ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) hxₗ).objects
          (Et.toFunctor.obj
            ((Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor).obj a))).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iT)) :
    eqToHom (congrArg Over.left bK).symm ≫
      ((p ⋙ Over.post B.inclusion).map
        (Et.restriction ((Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor).obj a) ≫
          eqToHom (Gκs.object_point a.fst) ≫
          c.map ((predeformationCategory iT
              (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).objects
            a.fst).point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))).left =
    Spec.map (CommRingCat.ofHom (Site.deformationProjection T iT B hS
      (Over.forget (p.obj x)) uκ huκ a)) ≫
      eqToHom (congrArg Over.left ((predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).objects a.fst).base).symm ≫
      ((Over.post B.inclusion).map ((predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).objects
          a.fst).point.hom).left := by
  let q := p ⋙ Over.post B.inclusion
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let Cs := predeformationCategory iT
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ
  let Ct := predeformationCategory iT q (F.obj uκ) hxκ
  let M := Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor
  let s := Cs.objects a.fst
  have ht := restriction_base_changed_algebra B S hS p
    T iT (F.obj uκ) (F.obj uₗ) hxκ hxₗ (F.map δ) Et (M.obj a) bK
  have hpj := deformationProjection_map B S hS p T iT (Over.forget (p.obj x))
    F (sliceFunctor_comp_post B S hS p c x) uκ huκ Gκs a
  have hsmap := IsHomLift.fac' p s.point.hom
    (c.map s.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))
  rw [hpj] at ht
  replace ht := ht.trans (specMap_comp_eqToHom _ _)
  have hvK : (q.map (Et.restriction (M.obj a) ≫ eqToHom (Gκs.object_point a.fst) ≫
        c.map s.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))).left =
      (q.map (Et.restriction (M.obj a))).left ≫
        (q.map (eqToHom (show (Ct.objects (M.obj a).fst).point =
              (c.obj s.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))).1 from
            Gκs.object_point a.fst) ≫
          c.map s.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))).left := by
    rw [← Over.comp_left, ← q.map_comp]
  rw [hvK]
  dsimp only [q, Functor.comp_map] at ht
  dsimp only [s] at hsmap
  simp only [q, s, Functor.comp_map, Functor.map_comp, Over.comp_left, Over.eqToHom_left,
    eqToHom_map, hsmap, eqToHom_trans_assoc, eqToHom_refl, Category.comp_id]
  exact comp_eqToHom_tail_eq ht

/-- The two routes around the change-of-residue-field square send an object of the `l/k`-change
of fields to objects of the `l`-level predeformation category lying over the same scheme, and the
two structure morphisms to `x` agree once that identification is made. This is the
base-compatibility input of `basedIso_of_deformation_maps` for `basedIso_changeOfFieldFunctor`. -/
private theorem basedIso_changeOfFieldFunctor_base
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u}) (iT : Spec (.of T.Λ) ⟶ S)
    (c : p.ChoiceOfPullbacks)
    (uκ uₗ : Over (p.obj x))
    (huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uκ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (huₗ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (δ : uₗ ⟶ uκ)
    (hxκ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uκ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (hxₗ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (Gκs : InducedPredeformationFunctor iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uκ huκ)
    (Gₗ : InducedPredeformationFunctor iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ huₗ)
    (Es : Site.ChangeOfFieldFunctor T iT B hS (Over.forget (p.obj x)) uκ uₗ huκ huₗ δ)
    (Et : Site.ChangeOfFieldFunctor T iT B hS p
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uκ)
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) hxκ hxₗ
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).map δ))
    (a : Deformation.ChangeOfFieldsCategory T
      (predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).projection)
    (bH : (p ⋙ Over.post B.inclusion).obj
        ((predeformationCategory iT (p ⋙ Over.post B.inclusion)
            ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) hxₗ).objects
          (Gₗ.toFunctor.obj (Es.toFunctor.obj a))).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iT))
    (bK : (p ⋙ Over.post B.inclusion).obj
        ((predeformationCategory iT (p ⋙ Over.post B.inclusion)
            ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) hxₗ).objects
          (Et.toFunctor.obj
            ((Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor).obj a))).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iT)) :
    eqToHom (bK.trans bH.symm) ≫
      (p ⋙ Over.post B.inclusion).map
        (eqToHom (Gₗ.object_point (Es.toFunctor.obj a)) ≫
          c.map ((predeformationCategory iT
              (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ).objects
            (Es.toFunctor.obj a)).point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))) =
    (p ⋙ Over.post B.inclusion).map
      (Et.restriction ((Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor).obj a) ≫
        eqToHom (Gκs.object_point a.fst) ≫
        c.map ((predeformationCategory iT
            (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).objects
          a.fst).point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.eqToHom_left]
  exact eqToHom_comp_left_eq (congrArg Over.left bK) (congrArg Over.left bH)
    (basedIso_changeOfFieldFunctor_baseSource B S hS p x T iT c uκ uₗ huκ huₗ δ hxₗ
      Gₗ Es a bH)
    (basedIso_changeOfFieldFunctor_baseTarget B S hS p x T iT c uκ uₗ huκ δ hxκ hxₗ
      Gκs Et a bK)


/-- The comparison isomorphism behind the change-of-residue-field step: the two routes from
the `l/k`-change of fields of the `k`-level predeformation category to the `l`-level one --
restrict the slice first and then map to `𝒳`, or map first and then restrict -- agree up to a
canonical isomorphism over `𝒞_{Λ,l}`. -/
private theorem basedIso_changeOfFieldFunctor
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u}) (iT : Spec (.of T.Λ) ⟶ S)
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (uκ uₗ : Over (p.obj x))
    (huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uκ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (huₗ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (δ : uₗ ⟶ uκ)
    (hxκ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uκ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (hxₗ : (p ⋙ Over.post B.inclusion).obj
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (Gκs : InducedPredeformationFunctor iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uκ huκ)
    (Gₗ : InducedPredeformationFunctor iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ huₗ)
    (Es : Site.ChangeOfFieldFunctor T iT B hS (Over.forget (p.obj x)) uκ uₗ huκ huₗ δ)
    (Et : Site.ChangeOfFieldFunctor T iT B hS p
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uκ)
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ) hxκ hxₗ
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).map δ)) :
    letI q := p ⋙ Over.post B.inclusion
    letI F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
    Nonempty (
      (BasedFunctor.comp
        (⟨Es.toFunctor, Es.projection_comm⟩ : BasedFunctor
          (BasedCategory.ofFunctor (Deformation.changeOfFieldsProjection T
            (predeformationCategory iT
              (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).projection))
          (BasedCategory.ofFunctor
            (predeformationCategory iT
              (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ).projection))
        Gₗ.toBasedFunctor) ≅
      (BasedFunctor.comp (Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor)
        (⟨Et.toFunctor, Et.projection_comm⟩ : BasedFunctor
          (BasedCategory.ofFunctor (Deformation.changeOfFieldsProjection T
            (predeformationCategory iT q (F.obj uκ) hxκ).projection))
          (BasedCategory.ofFunctor
            (predeformationCategory iT q (F.obj uₗ) hxₗ).projection)))) := by
  let q := p ⋙ Over.post B.inclusion
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let xκ := F.obj uκ
  let Esb : BasedFunctor
      (BasedCategory.ofFunctor (Deformation.changeOfFieldsProjection T
        (predeformationCategory iT
          (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).projection))
      (BasedCategory.ofFunctor
        (predeformationCategory iT
          (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ).projection) :=
    ⟨Es.toFunctor, Es.projection_comm⟩
  let Etb : BasedFunctor
      (BasedCategory.ofFunctor (Deformation.changeOfFieldsProjection T
        (predeformationCategory iT q xκ hxκ).projection))
      (BasedCategory.ofFunctor
        (predeformationCategory iT q (F.obj uₗ) hxₗ).projection) :=
    ⟨Et.toFunctor, Et.projection_comm⟩
  change Nonempty (Esb.comp Gₗ.toBasedFunctor ≅
    (Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor).comp Etb)
  let Cs := predeformationCategory iT
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ
  let Ds := predeformationCategory iT
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ
  let Ct := predeformationCategory iT q xκ hxκ
  let Dt := predeformationCategory iT q (F.obj uₗ) hxₗ
  let M := Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor
  let H := Esb.comp Gₗ.toBasedFunctor
  let K := M.comp Etb
  let vH (a) : (Dt.objects (H.obj a)).point ⟶ x :=
    eqToHom (Gₗ.object_point (Es.toFunctor.obj a)) ≫
      c.map (Ds.objects (Es.toFunctor.obj a)).point.hom ⟨x, rfl⟩
  let vK (a) : (Dt.objects (K.obj a)).point ⟶ x :=
    Et.restriction (M.obj a) ≫
      eqToHom (Gκs.object_point a.fst) ≫
      c.map (Cs.objects a.fst).point.hom ⟨x, rfl⟩
  have hHalg (a) : (Dt.objects (H.obj a)).algebra = a.snd :=
    (induced_predeformation_algebra_eq S _ q F
      (sliceFunctor_comp_post B S hS p c x) iT uₗ huₗ Gₗ _).trans
        (Es.algebra_eq a)
  have hKalg (a) : (Dt.objects (K.obj a)).algebra = a.snd := Et.algebra_eq (M.obj a)
  have bH (a) : q.obj (Dt.objects (H.obj a)).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iT) :=
    (Dt.objects (H.obj a)).base.trans
      (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l =>
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iT)) (hHalg a))
  have bK (a) : q.obj (Dt.objects (K.obj a)).point =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iT) :=
    (Dt.objects (K.obj a)).base.trans
      (congrArg (fun A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l =>
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iT)) (hKalg a))
  apply basedIso_of_deformation_maps S q (unique_lift_post p hp (Over.post B.inclusion))
    iT (F.obj uₗ) hxₗ Dt
    (predeformationCategory_isPredeformationCategory B hS iT p _ hxₗ hp).cofibered
    H K x vH vK (fun a => (bK a).trans (bH a).symm)
  · intro a
    exact basedIso_changeOfFieldFunctor_base B S hS p x T iT c uκ uₗ huκ huₗ δ hxκ hxₗ
      Gκs Gₗ Es Et a (bH a) (bK a)
  · intro a
    have hEt := Et.arrow_comm (M.obj a)
    have hCt : (Ct.objects (M.obj a).fst).arrow =
        F.map (Cs.objects a.fst).arrow ≫
          eqToHom (show F.obj (Cs.objects a.fst).point =
              (Ct.objects (M.obj a).fst).point from (Gκs.object_point a.fst).symm) :=
      Gκs.object_arrow a.fst
    have hDt : (Dt.objects (Gₗ.toFunctor.obj (Es.toFunctor.obj a))).arrow =
        F.map (Ds.objects (Es.toFunctor.obj a)).arrow ≫
          eqToHom (show F.obj (Ds.objects (Es.toFunctor.obj a)).point =
              (Dt.objects (Gₗ.toFunctor.obj (Es.toFunctor.obj a))).point from
            (Gₗ.object_point (Es.toFunctor.obj a)).symm) :=
      Gₗ.object_arrow (Es.toFunctor.obj a)
    change (Dt.objects (Et.toFunctor.obj (M.obj a))).arrow ≫
        (Et.restriction (M.obj a) ≫
          eqToHom (show (Ct.objects (M.obj a).fst).point =
              F.obj (Cs.objects a.fst).point from Gκs.object_point a.fst) ≫
          c.map (Cs.objects a.fst).point.hom ⟨x, rfl⟩) =
      (Dt.objects (Gₗ.toFunctor.obj (Es.toFunctor.obj a))).arrow ≫
        (eqToHom (Gₗ.object_point (Es.toFunctor.obj a)) ≫
          c.map (Ds.objects (Es.toFunctor.obj a)).point.hom ⟨x, rfl⟩)
    have hs : F.map (Cs.objects a.fst).arrow ≫
        c.map (Cs.objects a.fst).point.hom ⟨x, rfl⟩ = c.map uκ.hom ⟨x, rfl⟩ :=
      c.sliceFunctor_map_fac _ (Cs.objects a.fst).arrow
    have hl : F.map (Ds.objects (Es.toFunctor.obj a)).arrow ≫
        c.map (Ds.objects (Es.toFunctor.obj a)).point.hom ⟨x, rfl⟩ =
        c.map uₗ.hom ⟨x, rfl⟩ :=
      c.sliceFunctor_map_fac _ (Ds.objects (Es.toFunctor.obj a)).arrow
    rw [← Category.assoc, hEt, hCt, hDt]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hs, hl]
    exact c.sliceFunctor_map_fac _ δ
  · intro a b f
    have hm := Gₗ.morphism_arrow (Es.toFunctor.map f)
    change (Dt.morphisms (Gₗ.toFunctor.obj (Es.toFunctor.obj a))
          (Gₗ.toFunctor.obj (Es.toFunctor.obj b))
          (Gₗ.toFunctor.map (Es.toFunctor.map f))).arrow ≫
        (eqToHom (Gₗ.object_point (Es.toFunctor.obj a)) ≫
          c.map (Ds.objects (Es.toFunctor.obj a)).point.hom ⟨x, rfl⟩) =
      eqToHom (Gₗ.object_point (Es.toFunctor.obj b)) ≫
        c.map (Ds.objects (Es.toFunctor.obj b)).point.hom ⟨x, rfl⟩
    have hfac : F.map (Ds.morphisms (Es.toFunctor.obj a) (Es.toFunctor.obj b)
          (Es.toFunctor.map f)).arrow ≫
        c.map (Ds.objects (Es.toFunctor.obj a)).point.hom ⟨x, rfl⟩ =
        c.map (Ds.objects (Es.toFunctor.obj b)).point.hom ⟨x, rfl⟩ :=
      c.sliceFunctor_map_fac _ (Ds.morphisms _ _ (Es.toFunctor.map f)).arrow
    rw [hm]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hfac]
  · intro a b f
    have hm := Et.restriction_natural (M.map f)
    have hκ : (Ct.morphisms (M.obj a).fst (M.obj b).fst (M.map f).fst).arrow =
        eqToHom (show (Ct.objects (M.obj b).fst).point =
            F.obj (Cs.objects b.fst).point from Gκs.object_point b.fst) ≫
          F.map (Cs.morphisms a.fst b.fst f.fst).arrow ≫
          eqToHom (show F.obj (Cs.objects a.fst).point =
            (Ct.objects (M.obj a).fst).point from (Gκs.object_point a.fst).symm) :=
      Gκs.morphism_arrow f.fst
    change (Dt.morphisms (Et.toFunctor.obj (M.obj a)) (Et.toFunctor.obj (M.obj b))
          (Et.toFunctor.map (M.map f))).arrow ≫
        (Et.restriction (M.obj a) ≫
          eqToHom (show (Ct.objects (M.obj a).fst).point =
              F.obj (Cs.objects a.fst).point from Gκs.object_point a.fst) ≫
          c.map (Cs.objects a.fst).point.hom ⟨x, rfl⟩) =
      Et.restriction (M.obj b) ≫
        eqToHom (Gκs.object_point b.fst) ≫
        c.map (Cs.objects b.fst).point.hom ⟨x, rfl⟩
    have hfac : F.map (Cs.morphisms a.fst b.fst f.fst).arrow ≫
        c.map (Cs.objects a.fst).point.hom ⟨x, rfl⟩ =
        c.map (Cs.objects b.fst).point.hom ⟨x, rfl⟩ :=
      c.sliceFunctor_map_fac _ (Cs.morphisms a.fst b.fst f.fst).arrow
    rw [← Category.assoc, hm, Category.assoc, hκ]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hfac]

/-- The change-of-residue-field step in the proof of Stacks 07XG, at the level of the slice.
The restriction functors of Stacks 07WX along `l/k` are equivalences, and change of residue
field (Stacks 07WD) preserves smoothness, so smoothness of the morphism of predeformation
categories at a `k`-valued point of `U` transfers to the `l`-valued point above it. -/
private theorem isSmooth_slice_of_isSmooth_residueField [IsLocallyNoetherian S]
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u}) (iT : Spec (.of T.Λ) ⟶ S)
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (uκ uₗ : Over (p.obj x))
    (huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uκ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (huₗ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT))
    (δ : uₗ ⟶ uκ)
    (hδ : eqToHom (congrArg Over.left huₗ).symm ≫
        ((Over.post B.inclusion).map δ.left).left ≫ eqToHom (congrArg Over.left huκ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT))
    (hRS : SatisfiesRS B S hS p hp)
    (hGκ : Deformation.IsSmooth (mapPredeformationCategory iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uκ huκ).toBasedFunctor) :
    Deformation.IsSmooth (mapPredeformationCategory iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ huₗ).toBasedFunctor := by
  let q := p ⋙ Over.post B.inclusion
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let xκ := F.obj uκ
  have hxκ : q.obj xκ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iT) :=
    imageBasePoint iT (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
      (sliceFunctor_comp_post B S hS p c x) uκ huκ
  have hxₗ : q.obj (F.obj uₗ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iT) :=
    imageBasePoint iT (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
      (sliceFunctor_comp_post B S hS p c x) uₗ huₗ
  let hps := Functor.IsFiberedInGroupoids.over_forget (p.obj x)
  have hδcart : (Over.forget (p.obj x)).IsCartesian
      ((Over.forget (p.obj x)).map δ) δ := by
    let := hps.isStronglyCartesian δ
    infer_instance
  have hηcart : p.IsCartesian (p.map (F.map δ)) (F.map δ) := by
    let := hp.isStronglyCartesian (F.map δ)
    infer_instance
  have hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      (q.map (F.map δ)).left ≫ eqToHom (congrArg Over.left hxκ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) := by
    rw [map_pointMorphism_base S _ q F
      (sliceFunctor_comp_post B S hS p c x) δ huκ huₗ hxκ hxₗ]
    exact hδ
  let Gκs := mapPredeformationCategory iT
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
    (sliceFunctor_comp_post B S hS p c x) uκ huκ
  have hchangedS := Deformation.isSmooth_changeOfFields T Gκs.toBasedFunctor hGκ
  let : Category.{u, u + 1} (predeformationCategory iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ).carrier :=
    (predeformationCategory iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ).category
  let : Category.{max u w, max (max (u + 1) v) w}
      (predeformationCategory iT (p ⋙ Over.post B.inclusion)
        (F.obj uₗ) hxₗ).carrier :=
    (predeformationCategory iT (p ⋙ Over.post B.inclusion)
      (F.obj uₗ) hxₗ).category
  let : Category.{max u w, max (max (u + 1) v) w}
      (predeformationCategory iT (p ⋙ Over.post B.inclusion) xκ hxκ).carrier :=
    (predeformationCategory iT (p ⋙ Over.post B.inclusion) xκ hxκ).category
  let : Category.{u, u + 1}
      (predeformationCategory iT
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).carrier :=
    (predeformationCategory iT
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).category
  let Es := Site.changeOfFieldFunctor T iT B hS (Over.forget (p.obj x))
    uκ uₗ huκ huₗ δ hps hδcart hδ
  have hEs : Es.toFunctor.IsEquivalence :=
    Site.changeOfFieldFunctor_isEquivalence T iT B hS (Over.forget (p.obj x))
      uκ uₗ huκ huₗ δ hps hδcart hδ hfinite
      (satisfiesRS_over_forget B S hS (p.obj x))
  let Et := Site.changeOfFieldFunctor T iT B hS p
    xκ (F.obj uₗ) hxκ hxₗ (F.map δ) hp hηcart hηbase
  have hEt : Et.toFunctor.IsEquivalence :=
    Site.changeOfFieldFunctor_isEquivalence T iT B hS p
      xκ (F.obj uₗ) hxκ hxₗ (F.map δ) hp hηcart hηbase hfinite hRS
  let Etb : BasedFunctor
      (BasedCategory.ofFunctor (Deformation.changeOfFieldsProjection T
        (predeformationCategory iT q xκ hxκ).projection))
      (BasedCategory.ofFunctor
        (predeformationCategory iT q (F.obj uₗ) hxₗ).projection) :=
    ⟨Et.toFunctor, Et.projection_comm⟩
  let : Etb.toFunctor.IsEquivalence := hEt
  have hEtSmooth : Deformation.IsSmooth Etb :=
    isSmooth_of_equivalence Etb
      (Deformation.changeOfFieldsProjection_isCofiberedInGroupoids T _
        (predeformationCategory_isPredeformationCategory B hS iT p xκ hxκ hp).cofibered)
  have hComposite := Deformation.isSmooth_comp
    (Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor) Etb hchangedS hEtSmooth
  let Gₗ := mapPredeformationCategory iT
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
    (sliceFunctor_comp_post B S hS p c x) uₗ huₗ
  let Esb : BasedFunctor
      (BasedCategory.ofFunctor (Deformation.changeOfFieldsProjection T
        (predeformationCategory iT
          (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uκ huκ).projection))
      (BasedCategory.ofFunctor
        (predeformationCategory iT
          (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ huₗ).projection) :=
    ⟨Es.toFunctor, Es.projection_comm⟩
  let : Esb.toFunctor.IsEquivalence := hEs
  apply Deformation.isSmooth_of_essSurj_comp Esb Gₗ.toBasedFunctor
  suffices e : Esb.comp Gₗ.toBasedFunctor ≅
      (Deformation.changeOfFieldsBasedFunctor T Gκs.toBasedFunctor).comp Etb from
    isSmooth_of_basedIso e hComposite
  exact Classical.choice (basedIso_changeOfFieldFunctor B S hS p x T iT hp c uκ uₗ huκ huₗ δ
    hxκ hxₗ Gκs Gₗ Es Et)

/-- **Stacks 07XG.** Let `𝒳` be a category fibred in groupoids over the big fppf site of a
locally Noetherian scheme `S`, let `x` be an object of `𝒳` over a scheme `U` locally of
finite type over `S`, and let `u₀` be a finite type point of `U`. Let `l` be a finite
extension of `κ(u₀)` and let `u_{l,0} : Spec l ⟶ U` be the induced `l`-valued point of `U`.
If `𝒳` satisfies (RS) and `x` is versal at `u₀`, then the morphism of predeformation
categories `𝓕_{(Sch/U)_fppf, l, u_{l,0}} ⟶ 𝓕_{𝒳, l, x_{l,0}}` is smooth. -/
@[stacks 07XG]
public theorem isSmooth_mapPredeformationCategory_of_isVersalAt
    [IsLocallyNoetherian S] (hp : p.IsFiberedInGroupoids)
    (hU : LocallyOfFiniteType ((p ⋙ Over.post B.inclusion).obj x).hom)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    [Algebra (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l]
    [Module.Finite (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l]
    (hfieldPoint : fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ =
      Spec.map (CommRingCat.ofHom (algebraMap
          (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l)) ≫
        ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀)
    (hversal : IsVersalAt ((p ⋙ Over.post B.inclusion).obj x)
      (p ⋙ Over.post B.inclusion) u₀ x rfl)
    (hRS : SatisfiesRS B S hS p hp) :
  letI : p.IsFibered := hp.isFibered
  Deformation.IsSmooth
    (mapPredeformationCategory iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion)
      (p ⋙ Over.post B.inclusion)
      (p.chosenPullbacks.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p p.chosenPullbacks x) uₗ₀ huₗ₀).toBasedFunctor := by
  let : p.IsFibered := hp.isFibered
  let q := p ⋙ Over.post B.inclusion
  let U := q.obj x
  let k := U.left.residueField u₀
  let : Algebra k l := inferInstanceAs
    (Algebra (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀) l)
  let R := S.presheaf.stalk (basePoint U u₀)
  let : Algebra R k := residueFieldAlgebra U u₀
  let iR : Spec (.of R) ⟶ S := S.fromSpecStalk (basePoint U u₀)
  have hiR : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR =
      residueFieldBasePoint U u₀ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (residueFieldBasePoint U u₀)
  let hκ := residueFieldPoint_site_contains B S hS p x u₀
  let uκ := residueFieldSlicePoint B S hS p x u₀ hκ
  have huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uκ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    residueFieldSlicePoint_base_eq_stalk B S hS p x u₀ hκ
  let F := p.chosenPullbacks.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let xκ := F.obj uκ
  let aκ : xκ ⟶ x := p.chosenPullbacks.map uκ.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
  have hxκ : q.obj xκ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    imageBasePoint iR (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
      (sliceFunctor_comp_post B S hS p p.chosenPullbacks x) uκ huκ
  have haκ : eqToHom (congrArg Over.left hxκ).symm ≫ (q.map aκ).left ≫
      eqToHom (congrArg Over.left (show q.obj x = U from rfl)) =
        U.left.fromSpecResidueField u₀ := by
    simp only [eqToHom_refl, Category.comp_id]
    exact
      (chosenPullback_fieldPointMap B S hS p x iR uκ huκ p.chosenPullbacks hxκ).trans
        (residueFieldSlicePoint_fieldPointMap B S hS p x iR u₀ hκ huκ)
  let Gκs := mapPredeformationCategory iR
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
    (sliceFunctor_comp_post B S hS p p.chosenPullbacks x) uκ huκ
  have hGκs : Deformation.IsSmooth Gκs.toBasedFunctor := by
    apply isSmooth_slice_of_deformation_lifting B S hS p x iR uκ huκ
      p.chosenPullbacks Gκs
    intro a b g hg
    let ma := mapDeformationObject S
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
      (sliceFunctor_comp_post B S hS p p.chosenPullbacks x) iR uκ huκ a
    apply isVersalAt_lift_of_base_eq S q U x rfl u₀ hversal iR hiR
      a.algebra b.algebra g.ringHom hg (F.obj a.point) b.point ma.base b.base
      g.arrow g.arrow_base (p.chosenPullbacks.map a.point.hom ⟨x, rfl⟩)
    calc
      _ = eqToHom (congrArg Over.left hxκ).symm ≫
          (q.map (ma.arrow ≫ p.chosenPullbacks.map a.point.hom ⟨x, rfl⟩)).left := by
        have hab := ma.arrow_base
        change eqToHom (congrArg Over.left hxκ).symm ≫ (q.map ma.arrow).left ≫
          eqToHom (congrArg Over.left ma.base) =
          Spec.map (CommRingCat.ofHom (residueMap a.algebra)) at hab
        rw [q.map_comp, Over.comp_left, ← hab]
        simp [Category.assoc]
      _ = U.left.fromSpecResidueField u₀ := by
        change eqToHom (congrArg Over.left hxκ).symm ≫
          (q.map (F.map a.arrow ≫ p.chosenPullbacks.map a.point.hom ⟨x, rfl⟩)).left = _
        rw [p.chosenPullbacks.sliceFunctor_map_fac]
        simpa only [eqToHom_refl, Category.comp_id] using haκ
  let T := stalkChangeOfFieldsSituation B S hS p x (l := l) hU u₀ hu₀
  have hchangedS := Deformation.isSmooth_changeOfFields T Gκs.toBasedFunctor hGκs
  have hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) := by
    rw [hiR]
    exact residueFieldMap_finiteType B S hS p x hU u₀ hu₀
  let : Algebra R l := T.algebraΛL
  have hlR : Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
    calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫
          residueFieldBasePoint U u₀ :=
        stalk_map_fieldExtension S (k := k) (l := l)
          (residueFieldBasePoint U u₀)
      _ = _ := (residueFieldPoint_comp_hom B S hS p x iΛ uₗ₀ huₗ₀ u₀ hfieldPoint).symm
  have huₗR : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR) :=
    huₗ₀.trans (congrArg Over.mk hlR.symm)
  obtain ⟨δ, hδ⟩ := exists_sliceArrow_of_fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀
    (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) uκ huκ
    (Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (by rw [hiR]; exact
      (residueFieldPoint_comp_hom B S hS p x iΛ uₗ₀ huₗ₀ u₀ hfieldPoint).symm)
    (by
      rw [← Category.assoc]
      change fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ =
        Spec.map (CommRingCat.ofHom (algebraMap k l)) ≫
          fieldPointMap B S hS p x iR uκ huκ
      rw [residueFieldSlicePoint_fieldPointMap B S hS p x iR u₀ hκ huκ]
      exact hfieldPoint)
  have hGₗ : Deformation.IsSmooth (mapPredeformationCategory iR
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
      (sliceFunctor_comp_post B S hS p p.chosenPullbacks x) uₗ₀ huₗR).toBasedFunctor :=
    isSmooth_slice_of_isSmooth_residueField B S hS p x T iR hp
      p.chosenPullbacks uκ uₗ₀ huκ huₗR δ hδ hfinite hRS hGκs
  have hc : Spec.map (CommRingCat.ofHom (algebraMap k l))
      (IsLocalRing.closedPoint l) = IsLocalRing.closedPoint k :=
    AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom (algebraMap k l))
  have hclosed : (Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR)
      (IsLocalRing.closedPoint l) = basePoint U u₀ := by
    have he := stalk_map_fieldExtension S (k := k) (l := l)
      (residueFieldBasePoint U u₀)
    change Spec.map (CommRingCat.ofHom (algebraMap R l)) ≫ iR = _ at he
    rw [he]
    change (residueFieldBasePoint U u₀)
      (Spec.map (CommRingCat.ofHom (algebraMap k l)) (IsLocalRing.closedPoint l)) = _
    rw [hc]
  exact isSmooth_slice_of_isSmooth_stalk B S hS p x iΛ uₗ₀ huₗ₀
    p.chosenPullbacks (basePoint U u₀) iR rfl hlR hclosed huₗR hGₗ

end Deformation.Artin

end
