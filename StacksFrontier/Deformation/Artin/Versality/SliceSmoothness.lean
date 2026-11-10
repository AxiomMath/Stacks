module

public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.Deformation.Artin.ChangeOfField.Equivalence
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityAffineOpenBase
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Versality at a point is smoothness of the induced map of predeformation categories

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `x` be an
object of `𝒳` over a scheme `U` and let `u₀ ∈ U`. Artin's Axioms, Definition 07XF, calls `x`
*versal at `u₀`* when the map
`x̂ : 𝓕_{(Sch/U)_{fppf}, k, u₀} ⟶ 𝓕_{𝒳, k, x₀}` of predeformation categories induced by the
2-Yoneda morphism `x : (Sch/U)_{fppf} ⟶ 𝒳` at `k = κ(u₀)` is smooth. In this library
`Deformation.Artin.IsVersalAt` is that smoothness written out as a lifting property over the
local ring of `S` at the image of `u₀`. This file proves that the written-out lifting property
*is* smoothness of `x̂` in the sense of Stacks 06HG, so that the sentence of Stacks 0DQZ "the
equivalence of (1) and (2) is the definition of `x` being versal at `u₀`" is a theorem here.

## Main results

* `Deformation.Artin.isSmooth_mapPredeformationCategory_iff_liftsAtResiduePoint`: at any
  field-valued point `uₗ₀` of the slice `(Sch/U)_{fppf}`, smoothness of the map of
  predeformation categories induced by the 2-Yoneda morphism `c.sliceFunctor x` (for a choice
  of pullbacks `c`) is the lifting property `Deformation.Artin.LiftsAtResiduePoint` at the
  underlying point `Spec l ⟶ U`.
* `Deformation.Artin.isVersalAt_iff_isSmooth_mapPredeformationCategory`: `x` is versal at `u₀`
  exactly when `x̂` is smooth, with the deformation base the ring of an affine open of `S`
  through which `Spec κ(u₀) ⟶ S` factors.
* `Deformation.Artin.residueFieldSlicePoint_base`: the residue point `Spec κ(u₀) ⟶ U` as an
  object of the slice of the site at `U` (`Deformation.Artin.residueFieldSlicePoint`) lies over
  `Spec κ(u₀) ⟶ Spec Λ ⟶ S`.

## Implementation notes

The 2-Yoneda morphism is `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` for an
arbitrary choice of pullbacks, and the map of predeformation categories is
`Deformation.Artin.mapPredeformationCategory` (Stacks 07WJ) for it. The construction
`Deformation.Artin.hatX` of Stacks 07XE asks for the category to be fibred in groupoids over
the category of *all* schemes over `S`, which a category over a bounded big fppf site never is
(`Deformation.Artin.not_isFiberedInGroupoids_comp_post`); so the site-level map is used here.

The proofs translate between deformations and lifting problems. A lifting problem for `x`
along `B ⟶ A` gives a deformation of the point in the slice from the morphism `y ⟶ x` over
`Spec A`, a deformation of the image point from the object over `Spec B`, and a morphism of
deformations from the arrow between them; conversely a deformation of the point in the slice
is a morphism `Spec A ⟶ U`, whose chosen pullback of `x` is the object over `Spec A`. All
arrows of `𝒳` being cartesian, the comparison between a chosen pullback and a given one is an
isomorphism, which is what lets the solution of one problem be read as a solution of the
other. The change of deformation base from the local ring of `S` to the ring of an affine open
is `Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen`.

## References

* [Stacks Project, Tag 06HG](https://stacks.math.columbia.edu/tag/06HG)
* [Stacks Project, Tag 07WJ](https://stacks.math.columbia.edu/tag/07WJ)
* [Stacks Project, Tag 07XE](https://stacks.math.columbia.edu/tag/07XE)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

section Generic

variable (S : Scheme.{u}) {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]

attribute [local instance] Deformation.Artin.PredeformationConstruction.category

private theorem predeformation_morphism_ext
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (C : Deformation.Artin.PredeformationConstruction i q y₀ hy₀)
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
    (C : Deformation.Artin.PredeformationConstruction i q y₀ hy₀)
    {a b : C.carrier} (g : @Quiver.Hom C.carrier C.category.toQuiver a b)
    {D A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l} (f : D ⟶ A) :
    C.projection.IsHomLift f g ↔
      ∃ (ha : (C.objects a).algebra = D) (hb : (C.objects b).algebra = A),
        (C.morphisms a b g).ringHom = eqToHom ha ≫ f ≫ eqToHom hb.symm := by
  let : Category C.carrier := C.category
  constructor
  · intro hg
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
    (G : Deformation.Artin.InducedPredeformationFunctor i qY qZ F hF y₀ hy₀)
    (a : (Deformation.Artin.predeformationCategory i qY y₀ hy₀).carrier) :
    ((Deformation.Artin.predeformationCategory i qZ (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀)).objects (G.toFunctor.obj a)).algebra =
      ((Deformation.Artin.predeformationCategory i qY y₀ hy₀).objects a).algebra := by
  rw [← (Deformation.Artin.predeformationCategory i qZ (F.obj y₀) _).object_projection,
    ← (Deformation.Artin.predeformationCategory i qY y₀ hy₀).object_projection]
  exact congrArg (fun H => H.obj a) G.projection_comm

private def mapDeformationObject
    {Y : Type v} [Category.{w} Y] {Z : Type*} [Category Z]
    (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S)
    (F : Y ⥤ Z) (hF : F ⋙ qZ = qY)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : qY.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (a : Deformation.Artin.DeformationObject i qY y₀ hy₀) :
    Deformation.Artin.DeformationObject i qZ (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) where
  algebra := a.algebra
  point := F.obj a.point
  arrow := F.map a.arrow
  base := (congrArg (fun H : Y ⥤ Over S => H.obj a.point) hF).trans a.base
  arrow_base := by
    subst qY
    exact a.arrow_base

private theorem deformationObject_ext
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (a b : Deformation.Artin.DeformationObject i q y₀ hy₀)
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
    (G : Deformation.Artin.InducedPredeformationFunctor i qY qZ F hF y₀ hy₀)
    (a : (Deformation.Artin.predeformationCategory i qY y₀ hy₀).carrier) :
    (Deformation.Artin.predeformationCategory i qZ (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀)).objects (G.toFunctor.obj a) =
      mapDeformationObject S qY qZ F hF i y₀ hy₀
        ((Deformation.Artin.predeformationCategory i qY y₀ hy₀).objects a) := by
  subst qY
  exact deformationObject_ext S _ i _ _ _ _
    (induced_predeformation_algebra_eq S _ _ F rfl i y₀ hy₀ G a)
    (G.object_point a) (G.object_arrow a)

private theorem deformationMorphism_cast_ringHom
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    {a b c d : Deformation.Artin.DeformationObject i q y₀ hy₀}
    (e : a = c) (e' : b = d) (g : Deformation.Artin.DeformationMorphism i q y₀ hy₀ a b) :
    (e' ▸ e ▸ g).ringHom =
      eqToHom (congrArg Deformation.Artin.DeformationObject.algebra e).symm ≫
        g.ringHom ≫ eqToHom (congrArg Deformation.Artin.DeformationObject.algebra e') := by
  cases e
  cases e'
  simp

private theorem deformationMorphism_cast_arrow
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : q.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    {a b c d : Deformation.Artin.DeformationObject i q y₀ hy₀}
    (e : a = c) (e' : b = d) (g : Deformation.Artin.DeformationMorphism i q y₀ hy₀ a b) :
    (e' ▸ e ▸ g).arrow =
      eqToHom (congrArg Deformation.Artin.DeformationObject.point e').symm ≫
        g.arrow ≫ eqToHom (congrArg Deformation.Artin.DeformationObject.point e) := by
  cases e
  cases e'
  simp

attribute [local implicit_reducible] Functor.Fiber BasedCategory.ofFunctor
  Deformation.Artin.InducedPredeformationFunctor.toBasedFunctor mapDeformationObject


private theorem isSmooth_induced_of_deformation_lifting
    {Y : Type v} [Category.{w} Y] {Z : Type*} [Category Z]
    (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S) (F : Y ⥤ Z)
    (hF : F ⋙ qZ = qY) (i : Spec (.of Λ) ⟶ S) (y₀ : Y)
    (hy₀ : qY.obj y₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ i))
    (G : Deformation.Artin.InducedPredeformationFunctor i qY qZ F hF y₀ hy₀)
    (hLift : ∀ (a : Deformation.Artin.DeformationObject i qY y₀ hy₀)
      (b : Deformation.Artin.DeformationObject i qZ (F.obj y₀)
        (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀))
      (g : Deformation.Artin.DeformationMorphism i qZ (F.obj y₀)
        (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) b
          (mapDeformationObject S qY qZ F hF i y₀ hy₀ a)),
      Function.Surjective g.ringHom.hom →
      ∃ (a' : Deformation.Artin.DeformationObject i qY y₀ hy₀)
        (h : Deformation.Artin.DeformationMorphism i qY y₀ hy₀ a' a)
        (α : Deformation.Artin.DeformationMorphism i qZ (F.obj y₀)
          (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀)
          (mapDeformationObject S qY qZ F hF i y₀ hy₀ a') b)
        (hA : a'.algebra = b.algebra),
        h.ringHom = eqToHom hA ≫ g.ringHom ∧ α.ringHom = eqToHom hA ∧
          F.map h.arrow = g.arrow ≫ α.arrow) :
    Deformation.IsSmooth G.toBasedFunctor := by
  let C := Deformation.Artin.predeformationCategory i qY y₀ hy₀
  let D := Deformation.Artin.predeformationCategory i qZ (F.obj y₀)
    (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀)
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
  let gm : Deformation.Artin.DeformationMorphism i qZ (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) b
      (mapDeformationObject S qY qZ F hF
        i y₀ hy₀ a) :=
    hobj ▸ D.morphisms y (G.toFunctor.obj z) g
  obtain ⟨hB, hA, he⟩ :=
    (predeformation_isHomLift_iff S qZ i (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) D g f).mp hg
  have haA : a.algebra = A :=
    (congrArg Deformation.Artin.DeformationObject.algebra hobj).symm.trans hA
  have hgmRing : gm.ringHom = eqToHom hB ≫ f ≫ eqToHom haA.symm := by
    have hc := deformationMorphism_cast_ringHom S qZ i (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) rfl hobj
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
    refine ⟨(congrArg Deformation.Artin.DeformationObject.algebra hz').trans (hbalg.trans hB),
      haA, ?_⟩
    rw [hh]
    have hc := deformationMorphism_cast_ringHom S qY i
      y₀ hy₀ hz'.symm rfl hm
    simpa [hhmring, hgmRing, Category.assoc] using hc
  have hαlift : D.projection.IsHomLift (𝟙 B) α := by
    apply (predeformation_isHomLift_iff S qZ i (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) D α (𝟙 B)).mpr
    refine ⟨(congrArg Deformation.Artin.DeformationObject.algebra hzG).trans (hbalg.trans hB),
      hB, ?_⟩
    rw [hα]
    have hc := deformationMorphism_cast_ringHom S qZ i (F.obj y₀)
      (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) hzG.symm rfl am
    simpa [hamring, Category.assoc] using hc
  refine ⟨z', h, α, hhlift, hαlift, ?_⟩
  apply predeformation_morphism_ext S qZ i (F.obj y₀)
    (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) D
  · have : D.projection.IsHomLift f (G.toFunctor.map h) :=
      (BasedFunctor.isHomLift_iff G.toBasedFunctor f h).mpr hhlift
    have : D.projection.IsHomLift f (α ≫ g) :=
      IsHomLift.comp_lift_id_left D.projection f g α
    rw [IsHomLift.fac' D.projection f (G.toFunctor.map h),
      IsHomLift.fac' D.projection f (α ≫ g)]
  · rw [D.reversed_composition]
    have hGarrow : (D.morphisms _ _ (G.toFunctor.map h)).arrow =
        eqToHom (G.object_point z) ≫
          F.map (C.morphisms _ _ h).arrow ≫
            eqToHom (G.object_point z').symm := G.morphism_arrow h
    have hharrow : (C.morphisms _ _ h).arrow = hm.arrow ≫
        eqToHom (congrArg Deformation.Artin.DeformationObject.point hz').symm := by
      rw [hh]
      simpa using deformationMorphism_cast_arrow S qY i
        y₀ hy₀ hz'.symm rfl hm
    have hαarrow : (D.morphisms _ _ α).arrow =
        am.arrow ≫ eqToHom (congrArg Deformation.Artin.DeformationObject.point hzG).symm := by
      rw [hα]
      simpa using deformationMorphism_cast_arrow S qZ i (F.obj y₀)
        (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) hzG.symm rfl am
    have hgmarrow : gm.arrow =
        eqToHom (congrArg Deformation.Artin.DeformationObject.point hobj).symm ≫
          (D.morphisms _ _ g).arrow := by
      simpa [gm] using deformationMorphism_cast_arrow S qZ i (F.obj y₀)
        (Deformation.Artin.imageBasePoint i qY qZ F hF y₀ hy₀) rfl hobj
        (D.morphisms y (G.toFunctor.obj z) g)
    rw [hGarrow, hharrow, hαarrow]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc]
    rw [hcomm, hgmarrow]
    simp [Category.assoc]
end Generic

/-- The underlying morphism of schemes of a morphism precomposed with a transport. -/
private theorem left_map_eqToHom_comp {C : Type*} [Category C] {T : Scheme.{u}}
    (Q : C ⥤ Over T) {a a' b : C} (h : a' = a) (f : a ⟶ b) {A Bo : Over T}
    (ha' : Q.obj a' = A) (ha : Q.obj a = A) (hb : Q.obj b = Bo) :
    eqToHom (congrArg Over.left ha').symm ≫ (Q.map (eqToHom h ≫ f)).left ≫
        eqToHom (congrArg Over.left hb) =
      eqToHom (congrArg Over.left ha).symm ≫ (Q.map f).left ≫
        eqToHom (congrArg Over.left hb) := by
  subst h
  simp

/-- A composite of three transports is the identity. -/
private theorem eqToHom_comp_eqToHom_comp_eqToHom {C : Type*} [Category C] {a b c : C}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = a) :
    eqToHom h₁ ≫ eqToHom h₂ ≫ eqToHom h₃ = 𝟙 a := by
  subst h₁ h₂
  simp


section Slice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

variable (x : X)
variable {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
variable (iΛ : Spec (.of Λ) ⟶ S) (uₗ₀ : Over (p.obj x))
variable (huₗ₀ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))

attribute [local implicit_reducible] Functor.Fiber BasedCategory.ofFunctor
  Deformation.Artin.InducedPredeformationFunctor.toBasedFunctor mapDeformationObject
  Functor.ChoiceOfPullbacks.sliceFunctor

attribute [local instance] Deformation.Artin.PredeformationConstruction.category

private theorem isSmooth_slice_of_deformation_lifting
    (_hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (G : Deformation.Artin.InducedPredeformationFunctor iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀)
    (hLift : ∀
      (a : Deformation.Artin.DeformationObject iΛ
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀)
      (b : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion)
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
        (Deformation.Artin.imageBasePoint iΛ _ _ _
          (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀))
      (g : Deformation.Artin.DeformationMorphism iΛ (p ⋙ Over.post B.inclusion)
        ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
        (Deformation.Artin.imageBasePoint iΛ _ _ _
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
  have hlift (u : Over (p.obj x)) : p.obj (F.obj u) = u.left :=
    (c.obj u.hom ⟨x, rfl⟩).property
  have h₀ := hlift uₗ₀
  have ha := hlift a.point
  have hb : b.arrow ≫ v = c.map uₗ₀.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)) := by
    rw [← g.triangle, Category.assoc, hv]
    exact c.sliceFunctor_map_fac _ a.arrow
  let z : Over (p.obj x) := Over.mk (p.map v)
  let r : uₗ₀.left ⟶ p.obj b.point := eqToHom h₀.symm ≫ p.map b.arrow
  have hproj (u : Over (p.obj x)) (ψ : F.obj u ⟶ b.point)
      (hψ : ψ ≫ v = c.map u.hom ⟨x, rfl⟩) :
      (eqToHom (hlift u).symm ≫ p.map ψ) ≫ z.hom = u.hom := by
    dsimp [z]
    rw [Category.assoc, ← p.map_comp, hψ]
    let := c.isStronglyCartesian u.hom ⟨x, rfl⟩
    rw [IsHomLift.fac' p u.hom (c.map u.hom ⟨x, rfl⟩)]
    simp
  let b' : Deformation.Artin.DeformationObject iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀ :=
    { algebra := b.algebra
      point := z
      arrow := Over.homMk r (hproj uₗ₀ b.arrow hb)
      base := b.base
      arrow_base := by
        rw [← b.arrow_base]
        exact left_map_eqToHom_comp (Over.post B.inclusion) h₀.symm (p.map b.arrow) huₗ₀
          (Deformation.Artin.imageBasePoint iΛ _ _ F (sliceFunctor_comp_post B S hS p c x) uₗ₀
            huₗ₀) b.base }
  let v' := c.map z.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let := c.isStronglyCartesian z.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let : p.IsCartesian (p.map v) v' := by
    dsimp [v', z]
    infer_instance
  let α : b.point ⟶ F.obj z := Functor.IsCartesian.map p (p.map v) v' v
  have hα : α ≫ v' = v := Functor.IsCartesian.fac p (p.map v) v' v
  have hαlift : p.IsHomLift (𝟙 (p.obj b.point)) α :=
    Functor.IsCartesian.map_isHomLift p (p.map v) v' v
  have hfac (u : Over (p.obj x)) (ψ : F.obj u ⟶ b.point) (φ : u ⟶ z)
      (hψ : ψ ≫ v = c.map u.hom ⟨x, rfl⟩)
      (hφ : φ.left = eqToHom (hlift u).symm ≫ p.map ψ) : ψ ≫ α = F.map φ := by
    let : p.IsHomLift φ.left (F.map φ) :=
      c.sliceFunctor_map_isHomLift ⟨x, rfl⟩ φ
    have hψl : p.IsHomLift φ.left ψ :=
      IsHomLift.of_fac' p φ.left ψ (hlift u) rfl (by simp [hφ])
    have hψα : p.IsHomLift φ.left (ψ ≫ α) :=
      IsHomLift.comp_lift_id_right p φ.left ψ α
    apply Functor.IsStronglyCartesian.ext p z.hom v' φ.left
    rw [Category.assoc, hα, hψ]
    exact (c.sliceFunctor_map_fac _ φ).symm
  have hbarr : b.arrow ≫ α = F.map b'.arrow := hfac uₗ₀ b.arrow b'.arrow hb rfl
  let am : Deformation.Artin.DeformationMorphism iΛ (p ⋙ Over.post B.inclusion)
      (F.obj uₗ₀) (Deformation.Artin.imageBasePoint iΛ _ _ F
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
          ArtinianLocalAlgCat.id_hom, AlgHom.toRingHom_eq_coe]
        exact (eqToHom_comp_eqToHom_comp_eqToHom _ _ _).trans (Spec.map_id _).symm }
  let t : a.point.left ⟶ p.obj b.point := eqToHom ha.symm ≫ p.map g.arrow
  let hm : Deformation.Artin.DeformationMorphism iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀ b' a :=
    { ringHom := g.ringHom
      arrow := Over.homMk t (hproj a.point g.arrow hv)
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
        rw [← g.arrow_base]
        exact left_map_eqToHom_comp (Over.post B.inclusion) ha.symm (p.map g.arrow) a.base
          (mapDeformationObject S _ _ F (sliceFunctor_comp_post B S hS p c x) iΛ uₗ₀ huₗ₀
            a).base b.base }
  refine ⟨b', hm, am, rfl, by simp [hm], by rfl, ?_⟩
  change F.map hm.arrow = g.arrow ≫ α
  exact (hfac a.point g.arrow hm.arrow hv rfl).symm

private theorem deformation_lifting_of_isSmooth_slice
    (c : p.ChoiceOfPullbacks)
    (G : Deformation.Artin.InducedPredeformationFunctor iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
      (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
      (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀)
    (hs : Deformation.IsSmooth G.toBasedFunctor)
    (a : Deformation.Artin.DeformationObject iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀)
    (b : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion)
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
      (Deformation.Artin.imageBasePoint iΛ _ _ _
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀))
    (g : Deformation.Artin.DeformationMorphism iΛ (p ⋙ Over.post B.inclusion)
      ((c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))).obj uₗ₀)
      (Deformation.Artin.imageBasePoint iΛ _ _ _
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀) b
      (mapDeformationObject S _ _ _ (sliceFunctor_comp_post B S hS p c x)
        iΛ uₗ₀ huₗ₀ a))
    (hg : Function.Surjective g.ringHom.hom) :
    ∃ v : b.point ⟶ x,
      g.arrow ≫ v = c.map a.point.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)) := by
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  let q := p ⋙ Over.post B.inclusion
  let C := Deformation.Artin.predeformationCategory iΛ
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀
  let D := Deformation.Artin.predeformationCategory iΛ q (F.obj uₗ₀)
    (Deformation.Artin.imageBasePoint iΛ _ q F (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀)
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
    refine ⟨congrArg Deformation.Artin.DeformationObject.algebra hy,
      congrArg Deformation.Artin.DeformationObject.algebra hzG, ?_⟩
    rw [hg']
    simpa using deformationMorphism_cast_ringHom S q iΛ _ _ hy.symm hzG.symm g
  obtain ⟨z', h, α, _, _, hcomp⟩ := hs g.ringHom hg y z g' hglift
  have hcomp' := congrArg (fun f => (D.morphisms _ _ f).arrow) hcomp
  rw [D.reversed_composition] at hcomp'
  have hmap := G.morphism_arrow h
  have hgarrow : (D.morphisms _ _ g').arrow =
      eqToHom (congrArg Deformation.Artin.DeformationObject.point hzG) ≫ g.arrow ≫
        eqToHom (congrArg Deformation.Artin.DeformationObject.point hy).symm := by
    rw [hg']
    simpa using deformationMorphism_cast_arrow S q iΛ _ _ hy.symm hzG.symm g
  change (D.morphisms _ _ (G.toFunctor.map h)).arrow =
    (D.morphisms _ _ g').arrow ≫ (D.morphisms _ _ α).arrow at hcomp'
  change (D.morphisms _ _ (G.toFunctor.map h)).arrow = _ at hmap
  rw [hmap, hgarrow] at hcomp'
  let t := eqToHom (congrArg Deformation.Artin.DeformationObject.point hy).symm ≫
    (D.morphisms _ _ α).arrow ≫ eqToHom (G.object_point z')
  have ht : F.map (eqToHom (congrArg Deformation.Artin.DeformationObject.point hz).symm ≫
      (C.morphisms _ _ h).arrow) = g.arrow ≫ t := by
    have he := congrArg (fun f =>
      eqToHom (congrArg Deformation.Artin.DeformationObject.point hzG).symm ≫ f ≫
        eqToHom (G.object_point z')) hcomp'
    simpa [t, Functor.map_comp, eqToHom_map, Category.assoc] using he
  refine ⟨t ≫ c.map (C.objects z').point.hom ⟨x, rfl⟩, ?_⟩
  rw [← Category.assoc, ← ht]
  exact c.sliceFunctor_map_fac _ _


/-- A morphism of the site lying over an identity has the identity as underlying morphism of
schemes, once both ends are presented over the same scheme. -/
private theorem schemeMap_of_isHomLift_id {y y' : X} (φ : y ⟶ y')
    (hφ : p.IsHomLift (𝟙 (p.obj y')) φ) {Y : Over S}
    (hy : (p ⋙ Over.post B.inclusion).obj y = Y)
    (hy' : (p ⋙ Over.post B.inclusion).obj y' = Y) :
    schemeMap (p ⋙ Over.post B.inclusion) hy hy' φ = 𝟙 Y.left := by
  have hobj : p.obj y = p.obj y' := IsHomLift.domain_eq p (𝟙 (p.obj y')) φ
  have hm : p.map φ = eqToHom hobj := by
    rw [IsHomLift.fac' p (𝟙 (p.obj y')) φ]
    simp
  subst hy
  simp only [schemeMap, Functor.comp_map, hm, eqToHom_map, Over.eqToHom_left, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- **Smoothness of `x̂` from the lifting property at the residue point.** If every lifting
problem for `x` at the point `uₗ₀` along a surjection of Artinian local `Λ`-algebras has a
solution, then the map of predeformation categories induced by the 2-Yoneda morphism of `x`
is smooth. -/
public theorem isSmooth_mapPredeformationCategory_of_liftsAtResiduePoint
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (hl : LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion)
      ((p ⋙ Over.post B.inclusion).obj x) x rfl (fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀)) :
    Deformation.IsSmooth
      (Deformation.Artin.mapPredeformationCategory iΛ
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
        (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀).toBasedFunctor := by
  let q := p ⋙ Over.post B.inclusion
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  have hxκ : q.obj (F.obj uₗ₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) :=
    Deformation.Artin.imageBasePoint iΛ (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
      (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀
  apply isSmooth_slice_of_deformation_lifting B S hS p x iΛ uₗ₀ huₗ₀ hp c
  intro a b g hg
  let ma := mapDeformationObject S
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
    (sliceFunctor_comp_post B S hS p c x) iΛ uₗ₀ huₗ₀ a
  apply hl a.algebra b.algebra g.ringHom hg (F.obj a.point) b.point ma.base b.base
    g.arrow g.arrow_base (c.map a.point.hom ⟨x, rfl⟩)
  calc
    _ = eqToHom (congrArg Over.left hxκ).symm ≫
        (q.map (ma.arrow ≫ c.map a.point.hom ⟨x, rfl⟩)).left := by
      have hab := ma.arrow_base
      change eqToHom (congrArg Over.left hxκ).symm ≫ (q.map ma.arrow).left ≫
        eqToHom (congrArg Over.left ma.base) =
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.algebra)) at hab
      rw [q.map_comp, Over.comp_left, ← hab]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _)
    _ = fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ := by
      change eqToHom (congrArg Over.left hxκ).symm ≫
        (q.map (F.map a.arrow ≫ c.map a.point.hom ⟨x, rfl⟩)).left = _
      rw [c.sliceFunctor_map_fac]
      exact chosenPullback_fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀ c hxκ


/-- **The lifting property at the residue point from smoothness of `x̂`.** If the map of
predeformation categories induced by the 2-Yoneda morphism of `x` at the point `uₗ₀` is smooth,
then every lifting problem for `x` at that point along a surjection of Artinian local
`Λ`-algebras has a solution. -/
public theorem liftsAtResiduePoint_of_isSmooth_mapPredeformationCategory
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (hs : Deformation.IsSmooth
      (Deformation.Artin.mapPredeformationCategory iΛ
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
        (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀).toBasedFunctor) :
    LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion)
      ((p ⋙ Over.post B.inclusion).obj x) x rfl (fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀) := by
  let q := p ⋙ Over.post B.inclusion
  let F := c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x))
  have img : q.obj (F.obj uₗ₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ) :=
    Deformation.Artin.imageBasePoint iΛ (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
      (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀
  intro A A' f hf y z hy hz i hi a ha
  let w : Over (p.obj x) := Over.mk (p.map a)
  have hw : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj w =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := hy
  obtain ⟨δ, hδ⟩ := exists_sliceArrow_of_fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) w hw
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)))
    (specMap_residueMap_comp_self A iΛ) (by
      rw [← ha]
      simp only [schemeMap, eqToHom_refl, Category.comp_id]
      rfl)
  let aU : Deformation.Artin.DeformationObject iΛ
      (Over.forget (p.obj x) ⋙ Over.post B.inclusion) uₗ₀ huₗ₀ :=
    { algebra := A
      point := w
      arrow := δ
      base := hw
      arrow_base := hδ }
  have : p.IsStronglyCartesian (p.map a) a := hp.isStronglyCartesian_homLift (p.map a) a
  have : p.IsStronglyCartesian (p.map a) (c.map w.hom (⟨x, rfl⟩ : p.Fiber (p.obj x))) :=
    c.isStronglyCartesian w.hom _
  let ψ : F.obj w ⟶ y :=
    Functor.IsCartesian.map p (p.map a) a (c.map w.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)))
  have hψ : ψ ≫ a = c.map w.hom (⟨x, rfl⟩ : p.Fiber (p.obj x)) :=
    Functor.IsCartesian.fac p (p.map a) a _
  have hψlift : p.IsHomLift (𝟙 (p.obj y)) ψ := Functor.IsCartesian.map_isHomLift p _ _ _
  have : p.IsStronglyCartesian (𝟙 (p.obj y)) ψ := hp.isStronglyCartesian_homLift _ ψ
  have : IsIso ψ := Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p.obj y)) ψ
  let ma := mapDeformationObject S
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion) q F
    (sliceFunctor_comp_post B S hS p c x) iΛ uₗ₀ huₗ₀ aU
  have hψb : schemeMap q ma.base hy ψ = 𝟙 _ :=
    schemeMap_of_isHomLift_id B S hS p ψ hψlift ma.base hy
  have hma : schemeMap q img ma.base ma.arrow =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) := ma.arrow_base
  let bZ : Deformation.Artin.DeformationObject iΛ q (F.obj uₗ₀) img :=
    { algebra := A'
      point := z
      arrow := ma.arrow ≫ ψ ≫ i
      base := hz
      arrow_base := by
        change schemeMap q img hz (ma.arrow ≫ ψ ≫ i) = _
        rw [schemeMap_comp q img ma.base hz, schemeMap_comp q ma.base hy hz, hma, hψb, hi,
          Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          Deformation.Artin.residueMap_comp] }
  let gZ : Deformation.Artin.DeformationMorphism iΛ q (F.obj uₗ₀) img bZ ma :=
    { ringHom := f
      arrow := ψ ≫ i
      triangle := rfl
      arrow_base := by
        change schemeMap q ma.base hz (ψ ≫ i) = _
        rw [schemeMap_comp q ma.base hy hz, hψb, hi, Category.id_comp] }
  obtain ⟨v, hv⟩ := deformation_lifting_of_isSmooth_slice B S hS p x iΛ uₗ₀ huₗ₀ c _ hs
    aU bZ gZ hf
  refine ⟨v, (cancel_epi ψ).mp ?_⟩
  rw [← Category.assoc]
  exact hv.trans hψ.symm

/-- **Smoothness of `x̂` is the lifting property at the residue point.** For an object `x` of
a category fibred in groupoids over the big fppf site, the map of predeformation categories
induced at the point `uₗ₀` by the 2-Yoneda morphism of `x` is smooth exactly when every lifting
problem for `x` at that point along a surjection of Artinian local `Λ`-algebras has a
solution. -/
public theorem isSmooth_mapPredeformationCategory_iff_liftsAtResiduePoint
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks) :
    Deformation.IsSmooth
      (Deformation.Artin.mapPredeformationCategory iΛ
        (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
        (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
        (sliceFunctor_comp_post B S hS p c x) uₗ₀ huₗ₀).toBasedFunctor ↔
      LiftsAtResiduePoint iΛ (p ⋙ Over.post B.inclusion)
        ((p ⋙ Over.post B.inclusion).obj x) x rfl (fieldPointMap B S hS p x iΛ uₗ₀ huₗ₀) :=
  ⟨liftsAtResiduePoint_of_isSmooth_mapPredeformationCategory B S hS p x iΛ uₗ₀ huₗ₀ hp c,
    isSmooth_mapPredeformationCategory_of_liftsAtResiduePoint B S hS p x iΛ uₗ₀ huₗ₀ hp c⟩

/-! ### The residue point of `u₀` as an object of the slice -/

/-- The canonical residue point lies over `Spec κ(u₀) ⟶ Spec Λ ⟶ S` whenever the residue field
point of `u₀` factors that way. -/
public theorem residueFieldSlicePoint_base
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    (hκ : B.Contains (Spec (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀)))
    [Algebra Λ (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀)]
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ
        (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀))) ≫ iΛ =
      ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom) :
    (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj
        (residueFieldSlicePoint B S hS p x u₀ hκ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ
        (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀))) ≫ iΛ) := by
  have hm := B.inclusion.map_preimage (X := B.obj hκ) (Y := (p.obj x).left)
    (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀)
  change Over.mk (B.inclusion.map (B.inclusion.preimage (X := B.obj hκ) (Y := (p.obj x).left)
    (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀)) ≫
      ((p ⋙ Over.post B.inclusion).obj x).hom) = _
  exact congrArg Over.mk ((congrArg (· ≫ ((p ⋙ Over.post B.inclusion).obj x).hom) hm).trans
    hcompat.symm)

/-! ### Versality is smoothness of `x̂` -/

/-- **Versality at `u₀` is smoothness of `x̂`.** Let `x` be an object of a category fibred in
groupoids over the big fppf site of `S`, lying over `U`, and let `u₀` be a point of `U` whose
image in `S` lies in the affine open `Spec Λ`. Then `x` is versal at `u₀` exactly when the map
`x̂ : 𝓕_{(Sch/U), κ(u₀), u₀} ⟶ 𝓕_{𝒳, κ(u₀), x₀}` of predeformation categories over `𝒞_Λ`,
induced by the 2-Yoneda morphism of `x` for any choice of pullbacks, is smooth. The point
`uₗ₀` is any object of the slice over `Spec κ(u₀)` whose underlying morphism is the residue
field point of `u₀`. -/
public theorem isVersalAt_iff_isSmooth_mapPredeformationCategory
    (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (u₀ : ((p ⋙ Over.post B.inclusion).obj x).left)
    [Algebra Λ (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀)]
    [IsOpenImmersion iΛ] (t : Spec (.of Λ))
    (ht : iΛ t = basePoint ((p ⋙ Over.post B.inclusion).obj x) u₀)
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ
        (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀))) ≫ iΛ =
      ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
        ((p ⋙ Over.post B.inclusion).obj x).hom)
    (uκ : Over (p.obj x))
    (huκ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uκ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ
        (((p ⋙ Over.post B.inclusion).obj x).left.residueField u₀))) ≫ iΛ))
    (hpt : fieldPointMap B S hS p x iΛ uκ huκ =
      ((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀) :
    IsVersalAt ((p ⋙ Over.post B.inclusion).obj x) (p ⋙ Over.post B.inclusion) u₀ x rfl ↔
      Deformation.IsSmooth
        (Deformation.Artin.mapPredeformationCategory iΛ
          (Over.forget (p.obj x) ⋙ Over.post B.inclusion) (p ⋙ Over.post B.inclusion)
          (c.sliceFunctor (⟨x, rfl⟩ : p.Fiber (p.obj x)))
          (sliceFunctor_comp_post B S hS p c x) uκ huκ).toBasedFunctor := by
  rw [isSmooth_mapPredeformationCategory_iff_liftsAtResiduePoint B S hS p x iΛ uκ huκ hp c,
    hpt]
  exact isVersalAt_iff_liftsAtResiduePoint_affineOpen iΛ _ _ u₀ x rfl t ht hcompat

end Slice

end Deformation.Artin

end
