module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.Openness
public import StacksFrontier.Deformation.ArtinCriteria.Versality
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.RingTheory.EssentialFiniteness.ArtinianTarget

/-!
# Smoothness from the deformation condition, for a morphism of schemes

The deformation criterion for smoothness runs in the direction opposite to Stacks 07XW: a
1-morphism of categories fibred in groupoids over the big fppf site which satisfies the
smoothness condition on predeformation categories (**Stacks 07XS**) is smooth, given
representability and limit preservation. This file proves that implication for the 1-morphism
induced by a morphism `g : W ⟶ V` of schemes over the base, which is the step the source calls
the key ingredient of its proof of **Stacks 07XX** — its appeal to More on Morphisms,
Lemma 02HX.

## Main results

* `Deformation.Artin.smooth_of_isSmoothOnPredeformationCategories` — the case of **Stacks 07XX**
  for a morphism of schemes: if `W` and `V` are locally of finite type over a locally Noetherian
  `S` and the induced functor on slices satisfies Stacks 07XS, then `g` is smooth.

## Implementation notes

The argument is pointwise. At a finite type point `w` of `W` the deformation condition is
converted into versality of `g` at `w`, and `Deformation.Artin.smoothAt_iff_isVersalAt`
(Stacks 0CXL, which packages the infinitesimal lifting criterion of Stacks 02HX) turns that
into `InfinitesimalLifting.SmoothAt g w`. Smoothness at every finite type point gives
smoothness: the smooth locus is open, so its complement is locally closed, and a nonempty
locally closed subset of a scheme contains a finite type point (Stacks 02J4).

Converting the deformation condition into a lifting statement about schemes is the bulk of the
file. A lifting problem for `g` along a surjection `A' ⟶ A` of Artinian local algebras is
packaged as a morphism of `Deformation.Artin.DeformationObject`s, solved by the smoothness of
`Deformation.Artin.mapPredeformationCategory`, and unpackaged again; the deformation condition
is stated over a local ring of `S`, while the lifting problem presents itself over an affine
neighbourhood, so the coefficient ring is restricted along the germ map. The Artinian tests
belong to the chosen big site because they are of finite type over the base.

Several rewrites produce `eqToHom` casts between schemes that are equal only definitionally —
for instance `Over.mk`ed base points, and the Artinian algebra of an image deformation, which
is a structure field. `CategoryTheory.eqToHom_refl` and `CategoryTheory.eqToHom_trans` fire
only on syntactically equal endpoints, so these casts are discharged either by making
`Deformation.Artin.mapDeformationObject` reducible for unification, or in term mode, where the
endpoints are compared at default transparency.

The reduction of the general 1-morphism of Stacks 07XX to this case — through an étale atlas
of the algebraic space representing the 2-fibre product `𝒳 ×_𝒴 (Sch/V)_fppf`, which is locally
of finite presentation over `S` by Stacks 06CX — is carried out in
`StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSliceAtlas`, as
`AlgebraicGeometry.Stack.isRelativelySmooth_of_isSmoothOnPredeformationCategories`.

## References

* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
* [Stacks Project, Tag 02J4](https://stacks.math.columbia.edu/tag/02J4)
* [Stacks Project, Tag 07XS](https://stacks.math.columbia.edu/tag/07XS)
* [Stacks Project, Tag 07XX](https://stacks.math.columbia.edu/tag/07XX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.Artin

universe u v w vX vY wX wY

private theorem smooth_of_smoothAt_finiteTypePoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (h : ∀ x : X, AlgebraicGeometry.IsFiniteTypePoint x →
      InfinitesimalLifting.SmoothAt f x) : Smooth f := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x hx
  by_contra hx'
  obtain ⟨y, hy, hyft⟩ := AlgebraicGeometry.inter_finiteTypePoints_nonempty
    f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed ⟨x, hx'⟩
  exact hy (Scheme.Hom.mem_smoothLocus.mpr
    ((h y hyft).formallySmooth_stalkMap f y))

attribute [local instance] PredeformationConstruction.category

private def mapDeformationObject
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type vX} [Category.{wX} X] (qX : X ⥤ Over S)
    {Y : Type vY} [Category.{wY} Y] (qY : Y ⥤ Over S)
    (F : X ⥤ Y) (hF : F ⋙ qY = qX)
    (x₀ : X) (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a : DeformationObject iΛ qX x₀ hx₀) :
    DeformationObject iΛ qY (F.obj x₀)
      (imageBasePoint iΛ qX qY F hF x₀ hx₀) where
  algebra := a.algebra
  point := F.obj a.point
  arrow := F.map a.arrow
  base := (congrArg (fun H : X ⥤ Over S => H.obj a.point) hF).trans a.base
  arrow_base := by subst qX; exact a.arrow_base

-- The Artinian local algebra and the underlying object of `mapDeformationObject` are *fields*,
-- so the projections reduce only by unfolding the definition. Several rewrites below produce
-- `eqToHom` terms whose two endpoints agree only after that unfolding, and `eqToHom_refl`
-- fires only on syntactically equal endpoints; making the definition reducible for unification
-- is what lets them close.
attribute [local implicit_reducible] mapDeformationObject

-- Deformation objects agreeing on algebra and point, with arrows agreeing after transport, are
-- equal: `Deformation.Artin.deformationObject_ext_of_arrow_comp`, public beside the structure in
-- `StacksFrontier.Deformation.Artin.Predeformation`. A `private` re-declaration stood here.

private theorem mapPredeformationCategory_objects
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type vX} [Category.{wX} X] (qX : X ⥤ Over S)
    {Y : Type vY} [Category.{wY} Y] (qY : Y ⥤ Over S)
    (F : X ⥤ Y) (hF : F ⋙ qY = qX)
    (x₀ : X) (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a : (Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀).carrier) :
    let DY := Deformation.Artin.predeformationCategory iΛ qY (F.obj x₀)
      (imageBasePoint iΛ qX qY F hF x₀ hx₀)
    let G := Deformation.Artin.mapPredeformationCategory iΛ qX qY F hF x₀ hx₀
    DY.objects (G.toFunctor.obj a) =
      mapDeformationObject iΛ qX qY F hF x₀ hx₀
        ((Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀).objects a) := by
  subst qX
  let DX := Deformation.Artin.predeformationCategory iΛ (F ⋙ qY) x₀ hx₀
  let DY := Deformation.Artin.predeformationCategory iΛ qY (F.obj x₀)
    (imageBasePoint iΛ (F ⋙ qY) qY F rfl x₀ hx₀)
  let G := Deformation.Artin.mapPredeformationCategory iΛ (F ⋙ qY) qY F rfl x₀ hx₀
  refine Deformation.Artin.deformationObject_ext_of_arrow_comp ?_ (G.object_point a) ?_
  · change (DY.objects (G.toFunctor.obj a)).algebra = (DX.objects a).algebra
    rw [← DY.object_projection, ← DX.object_projection]
    exact congrArg (fun H => H.obj a) G.projection_comm
  · change (DY.objects (G.toFunctor.obj a)).arrow ≫ eqToHom _ =
      F.map (DX.objects a).arrow
    rw [G.object_arrow]
    simp [DX]

private theorem deformationMorphism_cast_target_ringHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type vX} [Category.{wX} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b c : DeformationObject iΛ q x₀ hx₀} (e : b = c)
    (g : DeformationMorphism iΛ q x₀ hx₀ a b) :
    (e ▸ g : DeformationMorphism iΛ q x₀ hx₀ a c).ringHom =
      g.ringHom ≫ eqToHom (congrArg DeformationObject.algebra e) := by
  cases e
  simp

private theorem deformationMorphism_cast_target_arrow
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type vX} [Category.{wX} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b c : DeformationObject iΛ q x₀ hx₀} (e : b = c)
    (g : DeformationMorphism iΛ q x₀ hx₀ a b) :
    (e ▸ g : DeformationMorphism iΛ q x₀ hx₀ a c).arrow =
      eqToHom (congrArg DeformationObject.point e).symm ≫ g.arrow := by
  cases e
  simp

private theorem deformationMorphism_cast_source_ringHom
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type vX} [Category.{wX} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b c : DeformationObject iΛ q x₀ hx₀} (e : a = c)
    (g : DeformationMorphism iΛ q x₀ hx₀ a b) :
    (e ▸ g : DeformationMorphism iΛ q x₀ hx₀ c b).ringHom =
      eqToHom (congrArg DeformationObject.algebra e).symm ≫ g.ringHom := by
  cases e
  simp

private theorem deformationMorphism_cast_source_arrow
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type vX} [Category.{wX} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b c : DeformationObject iΛ q x₀ hx₀} (e : a = c)
    (g : DeformationMorphism iΛ q x₀ hx₀ a b) :
    (e ▸ g : DeformationMorphism iΛ q x₀ hx₀ c b).arrow =
      g.arrow ≫ eqToHom (congrArg DeformationObject.point e) := by
  cases e
  simp

private theorem predeformation_ringHom_of_homLift
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type vX} [Category.{wX} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (D : PredeformationConstruction iΛ q x₀ hx₀)
    {a b : D.carrier} {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ B) (g : a ⟶ b) (hg : D.projection.IsHomLift f g)
    (ha : (D.objects a).algebra = A) (hb : (D.objects b).algebra = B) :
    (D.morphisms a b g).ringHom = eqToHom ha ≫ f ≫ eqToHom hb.symm := by
  let := hg
  rw [← D.morphism_projection, IsHomLift.fac' D.projection f g]
  simp

private theorem exists_raw_deformation_lift_of_isSmooth
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type vX} [Category.{wX} X] (qX : X ⥤ Over S)
    {Y : Type vY} [Category.{wY} Y] (qY : Y ⥤ Over S)
    (F : X ⥤ Y) (hF : F ⋙ qY = qX)
    (x₀ : X) (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hs : Deformation.IsSmooth
      (Deformation.Artin.mapPredeformationCategory iΛ qX qY F hF x₀ hx₀).toBasedFunctor)
    (a : DeformationObject iΛ qX x₀ hx₀)
    (b : DeformationObject iΛ qY (F.obj x₀)
      (imageBasePoint iΛ qX qY F hF x₀ hx₀))
    (g : DeformationMorphism iΛ qY (F.obj x₀)
      (imageBasePoint iΛ qX qY F hF x₀ hx₀) b
      (mapDeformationObject iΛ qX qY F hF x₀ hx₀ a))
    (hg : Function.Surjective g.ringHom.hom) :
    ∃ (a' : DeformationObject iΛ qX x₀ hx₀)
      (ha' : a'.algebra = b.algebra)
      (h : DeformationMorphism iΛ qX x₀ hx₀ a' a)
      (t : DeformationMorphism iΛ qY (F.obj x₀)
        (imageBasePoint iΛ qX qY F hF x₀ hx₀)
        (mapDeformationObject iΛ qX qY F hF x₀ hx₀ a') b),
      h.ringHom = eqToHom ha' ≫ g.ringHom ∧
      t.ringHom = eqToHom ha' ∧ F.map h.arrow = g.arrow ≫ t.arrow := by
  let DX := Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀
  let DY := Deformation.Artin.predeformationCategory iΛ qY (F.obj x₀)
    (imageBasePoint iΛ qX qY F hF x₀ hx₀)
  let G := Deformation.Artin.mapPredeformationCategory iΛ qX qY F hF x₀ hx₀
  obtain ⟨a, rfl⟩ := DX.objects.surjective a
  obtain ⟨b, rfl⟩ := DY.objects.surjective b
  have hobj := mapPredeformationCategory_objects iΛ qX qY F hF x₀ hx₀ a
  change DY.objects (G.toFunctor.obj a) = _ at hobj
  let gg : DeformationMorphism iΛ qY (F.obj x₀)
      (imageBasePoint iΛ qX qY F hF x₀ hx₀)
      (DY.objects b) (DY.objects (G.toFunctor.obj a)) := hobj.symm ▸ g
  let γ := (DY.morphisms b (G.toFunctor.obj a)).symm gg
  have hγ : DY.projection.IsHomLift g.ringHom γ := by
    have hp : DY.projection.obj (G.toFunctor.obj a) = (DX.objects a).algebra :=
      (congrArg (fun H => H.obj a) G.projection_comm).trans (DX.object_projection a)
    apply IsHomLift.of_fac' _ _ _ (DY.object_projection b) hp
    have H' : (DY.morphisms b (G.toFunctor.obj a) γ).ringHom =
        g.ringHom ≫ eqToHom (congrArg DeformationObject.algebra hobj).symm := by
      simp only [γ, Equiv.apply_symm_apply, gg, deformationMorphism_cast_target_ringHom]
    calc
      _ = eqToHom (DY.object_projection b) ≫
          (DY.morphisms b (G.toFunctor.obj a) γ).ringHom ≫
          eqToHom (DY.object_projection (G.toFunctor.obj a)).symm := by
        rw [← DY.morphism_projection]
        simp
      _ = _ := by rw [H']; simp
  obtain ⟨a', h, t, hh, ht, heq⟩ := hs g.ringHom hg b a γ hγ
  change DX.carrier at a'
  change G.toFunctor.obj a' ⟶ b at t
  have hobj' := mapPredeformationCategory_objects iΛ qX qY F hF x₀ hx₀ a'
  change DY.objects (G.toFunctor.obj a') = _ at hobj'
  let hraw := DX.morphisms a' a h
  let traw : DeformationMorphism iΛ qY (F.obj x₀)
      (imageBasePoint iΛ qX qY F hF x₀ hx₀)
      (mapDeformationObject iΛ qX qY F hF x₀ hx₀ (DX.objects a'))
      (DY.objects b) := hobj' ▸ (DY.morphisms (G.toFunctor.obj a') b t)
  have ha' : (DX.objects a').algebra = (DY.objects b).algebra := by
    rw [← DX.object_projection]
    let : DX.projection.IsHomLift g.ringHom h := hh
    exact IsHomLift.domain_eq DX.projection g.ringHom h
  refine ⟨DX.objects a', ha', hraw, traw, ?_, ?_, ?_⟩
  · simpa only [Category.comp_id, eqToHom_refl] using
      predeformation_ringHom_of_homLift DX g.ringHom h hh ha' rfl
  · have halg : (DY.objects (G.toFunctor.obj a')).algebra = (DY.objects b).algebra :=
      (congrArg DeformationObject.algebra hobj').trans ha'
    have hring : traw.ringHom =
        eqToHom (congrArg DeformationObject.algebra hobj').symm ≫
          (DY.morphisms (G.toFunctor.obj a') b t).ringHom := by
      simp only [traw, deformationMorphism_cast_source_ringHom]
    rw [hring,
      predeformation_ringHom_of_homLift DY (𝟙 (DY.objects b).algebra) t ht halg rfl]
    simp
  · have heq' : G.toFunctor.map h = t ≫ γ := heq
    have H := (G.morphism_arrow h).symm.trans
      ((congrArg (fun k => (DY.morphisms _ _ k).arrow) heq').trans
        (DY.reversed_composition t γ))
    have hgArrow : (DY.morphisms b (G.toFunctor.obj a) γ).arrow =
        eqToHom (G.object_point a) ≫ g.arrow := by
      simp only [γ, Equiv.apply_symm_apply, gg, deformationMorphism_cast_target_arrow]
    have htArrow : traw.arrow = (DY.morphisms (G.toFunctor.obj a') b t).arrow ≫
        eqToHom (G.object_point a') := by
      simp only [traw, deformationMorphism_cast_source_arrow]
    rw [hgArrow] at H
    rw [htArrow]
    apply (cancel_epi (eqToHom (G.object_point a))).mp
    simpa [Category.assoc, hraw, DX] using
      (congrArg (fun k => k ≫ eqToHom (G.object_point a')) H)

/-- Two casts compose to one: `f ≫ eqToHom e = g ≫ eqToHom e'` gives `f ≫ eqToHom _ = g`. -/
private theorem comp_eqToHom_trans_of_comp_eqToHom_eq {C : Type*} [Category C]
    {X Y Z P : C} (f : X ⟶ Y) (g : X ⟶ Z) (e : Y = P) (e' : Z = P)
    (h : f ≫ eqToHom e = g ≫ eqToHom e') : f ≫ eqToHom (e.trans e'.symm) = g := by
  subst e e'
  simpa using h

private theorem artinianLocalAlg_finiteType
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Algebra.FiniteType Λ k] (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Algebra.FiniteType Λ A := by
  have hres : Algebra.FiniteType Λ (IsLocalRing.ResidueField A) :=
    Algebra.FiniteType.of_surjective A.residueEquiv.symm.toAlgHom A.residueEquiv.symm.surjective
  exact RingHom.finiteType_algebraMap.mp
    ((finiteType_iff_residue_finiteType (algebraMap Λ A)).mpr
      (show (algebraMap Λ (IsLocalRing.ResidueField A)).FiniteType from
        RingHom.finiteType_algebraMap.mpr hres))

/-- The Artinian tests at a finite-type field-valued point belong to the chosen big site. -/
private theorem contains_spec_artinianLocalAlg
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    B.Contains (Spec (.of A)) := by
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k))) :=
    locallyOfFiniteType_of_comp _ iΛ
  have hft' : (algebraMap Λ k).FiniteType := HasRingHomProperty.Spec_iff.mp hft
  let : Algebra.FiniteType Λ k := RingHom.finiteType_algebraMap.mp hft'
  let : Algebra.FiniteType Λ A := artinianLocalAlg_finiteType A
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr ‹Algebra.FiniteType Λ A›)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hS


private theorem exists_scheme_lift_of_isSmoothOnPredeformationCategories
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W V : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ V)
    (hs : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map W.hom) (Over.map V.hom) (Over.map g.left)
      (by rw [← Over.mapComp_eq, g.w]))
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)]
    [QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)]
    (w₀ : Spec (.of k) ⟶ W.left.1)
    (hw₀ : w₀ ≫ W.hom.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)
    (A' A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (φ : A' ⟶ A) (hφ : Function.Surjective φ.hom)
    (α : Spec (.of A) ⟶ W.left.1) (β : Spec (.of A') ⟶ V.left.1)
    (hα : α ≫ W.hom.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
    (hβ : β ≫ V.hom.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ)
    (hα₀ : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ α = w₀)
    (hβ₀ : Spec.map (CommRingCat.ofHom (residueMap A')) ≫ β =
      w₀ ≫ g.left.hom)
    (hcomm : α ≫ g.left.hom = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ β) :
    ∃ γ : Spec (.of A') ⟶ W.left.1,
      Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ γ = α ∧
      γ ≫ g.left.hom = β := by
  let qW := Over.map W.hom ⋙ Over.post B.inclusion
  let qV := Over.map V.hom ⋙ Over.post B.inclusion
  let G := Over.map g.left
  have hG : G ⋙ qV = qW := by
    dsimp [G, qV, qW]
    rw [← Functor.assoc, ← Over.mapComp_eq, g.w]
  have hk : B.Contains (Spec (.of k)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hS
  have hA := contains_spec_artinianLocalAlg B S hS iΛ A
  have hA' := contains_spec_artinianLocalAlg B S hS iΛ A'
  let x₀ : Over W.left := Over.mk (ObjectProperty.homMk (X := B.obj hk) w₀)
  have hx₀ : qW.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    congrArg Over.mk hw₀
  let a : DeformationObject iΛ qW x₀ hx₀ := {
    algebra := A
    point := Over.mk (ObjectProperty.homMk (X := B.obj hA) α)
    arrow := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (residueMap A))))
      (ObjectProperty.hom_ext _ hα₀)
    base := congrArg Over.mk hα
    arrow_base := by rfl }
  let b : DeformationObject iΛ qV (G.obj x₀)
      (imageBasePoint iΛ qW qV G hG x₀ hx₀) := {
    algebra := A'
    point := Over.mk (ObjectProperty.homMk (X := B.obj hA') β)
    arrow := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (residueMap A'))))
      (ObjectProperty.hom_ext _ hβ₀)
    base := congrArg Over.mk hβ
    arrow_base := by rfl }
  let d : DeformationMorphism iΛ qV (G.obj x₀)
      (imageBasePoint iΛ qW qV G hG x₀ hx₀) b
      (mapDeformationObject iΛ qW qV G hG x₀ hx₀ a) := {
    ringHom := φ
    arrow := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)))
      (ObjectProperty.hom_ext _ hcomm.symm)
    triangle := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (residueMap A)) ≫
        Spec.map (CommRingCat.ofHom φ.hom.toRingHom) =
        Spec.map (CommRingCat.ofHom (residueMap A'))
      rw [← Spec.map_comp]
      congr 1
      ext z
      exact φ.residue_comm z
    arrow_base := by rfl }
  have hsm : Deformation.IsSmooth
      (Deformation.Artin.mapPredeformationCategory iΛ qW qV G hG x₀ hx₀).toBasedFunctor :=
    hs iΛ x₀ hx₀ inferInstance inferInstance inferInstance
  obtain ⟨a', ha', h, t, hh, ht, heq⟩ :=
    exists_raw_deformation_lift_of_isSmooth iΛ qW qV G hG x₀ hx₀
      hsm a b d hφ
  have hbase : a'.point.left.1 = Spec (.of A') := by
    exact (congrArg Over.left a'.base).trans
      (congrArg (fun R : Deformation.ArtinianLocalAlgCat Λ k => Spec (.of R)) ha')
  let γ : Spec (.of A') ⟶ W.left.1 := eqToHom hbase.symm ≫ a'.point.hom.hom
  refine ⟨γ, ?_, ?_⟩
  · have ha := h.arrow_base
    have hw := congrArg (fun z => z.hom) h.arrow.w
    change h.arrow.left.hom ≫ a'.point.hom.hom = α at hw
    change eqToHom (congrArg Over.left a.base).symm ≫ h.arrow.left.hom ≫
      eqToHom (congrArg Over.left a'.base) =
        Spec.map (CommRingCat.ofHom h.ringHom.hom.toRingHom) at ha
    have he : Spec.map (CommRingCat.ofHom h.ringHom.hom.toRingHom) =
        Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫
          eqToHom (congrArg (fun R : Deformation.ArtinianLocalAlgCat Λ k =>
            Spec (.of R)) ha').symm := by
      rw [hh]
      cases ha'
      simp only [eqToHom_refl, Category.id_comp]
      rfl
    rw [he] at ha
    -- The structural equality of `a` identifies two definitionally equal schemes, so the
    -- `eqToHom` it induces is definitionally an identity. `eqToHom_refl` cannot see this —
    -- its endpoints must agree syntactically — but a term-mode cast does, since term
    -- elaboration compares the two at default transparency.
    have ha2 : h.arrow.left.hom ≫ eqToHom (congrArg Over.left a'.base) =
        Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫
          eqToHom (congrArg (fun R : Deformation.ArtinianLocalAlgCat Λ k =>
            Spec (.of R)) ha').symm :=
      (Category.id_comp _).symm.trans ha
    -- `comp_eqToHom_trans_of_comp_eqToHom_eq` is applied in term mode, where the endpoints of the
    -- casts are compared at default transparency.
    have ha'' : h.arrow.left.hom ≫ eqToHom hbase =
        Spec.map (CommRingCat.ofHom φ.hom.toRingHom) :=
      comp_eqToHom_trans_of_comp_eqToHom_eq _ _ _ _ ha2
    change Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫
      (eqToHom hbase.symm ≫ a'.point.hom.hom) = α
    rw [← ha'']
    simpa [Category.assoc] using hw
  · have htbase := t.arrow_base
    have htw := congrArg (fun z => z.hom) t.arrow.w
    change t.arrow.left.hom ≫ (a'.point.hom.hom ≫ g.left.hom) = β at htw
    change eqToHom (congrArg Over.left b.base).symm ≫ t.arrow.left.hom ≫
      eqToHom (congrArg Over.left
        (mapDeformationObject iΛ qW qV G hG x₀ hx₀ a').base) =
        Spec.map (CommRingCat.ofHom t.ringHom.hom.toRingHom) at htbase
    have he : Spec.map (CommRingCat.ofHom t.ringHom.hom.toRingHom) =
        eqToHom (congrArg (fun R : Deformation.ArtinianLocalAlgCat Λ k =>
          Spec (.of R)) ha').symm := by
      rw [ht]
      cases ha'
      change Spec.map (𝟙 _) = 𝟙 _
      exact Spec.map_id _
    rw [he] at htbase
    -- As in the first component, the leading `eqToHom` is definitionally an identity.
    have htbase2 : t.arrow.left.hom ≫ eqToHom (congrArg Over.left
        (mapDeformationObject iΛ qW qV G hG x₀ hx₀ a').base) =
        eqToHom (congrArg (fun R : Deformation.ArtinianLocalAlgCat Λ k =>
          Spec (.of R)) ha').symm :=
      (Category.id_comp _).symm.trans htbase
    have ht' : t.arrow.left.hom = eqToHom hbase.symm := by
      have hkey : t.arrow.left.hom ≫ eqToHom hbase = 𝟙 (Spec (.of A')) :=
        comp_eqToHom_trans_of_comp_eqToHom_eq _ _ _ _
          (htbase2.trans (Category.id_comp _).symm)
      exact ((comp_eqToHom_iff hbase _ _).mp hkey).trans (Category.id_comp _)
    simpa [γ, ht', Category.assoc] using htw

private theorem isSmoothOnPredeformationCategories_congr
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    (p p' : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (q : Y ⥤ AlgebraicGeometry.BigFppfOver B S hS) (F F' : X ⥤ Y)
    (h : F ⋙ q = p) (h' : F' ⋙ q = p') (hp : p = p') (hF : F = F') :
    Deformation.Artin.IsSmoothOnPredeformationCategories B S hS p q F h ↔
      Deformation.Artin.IsSmoothOnPredeformationCategories B S hS p' q F' h' := by
  cases hp
  cases hF
  rfl

/-- Restriction of the coefficient ring preserves Artinian deformation algebras. -/
private noncomputable def restrictArtinianLocalAlg
    {Λ R k : Type u} [CommRing Λ] [CommRing R] [Field k] [Algebra R k]
    (r : Λ →+* R) (A : Deformation.ArtinianLocalAlgCat.{u, u, u} R k) :
    letI : Algebra Λ k := ((algebraMap R k).comp r).toAlgebra
    Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k := by
  letI : Algebra Λ k := ((algebraMap R k).comp r).toAlgebra
  letI : Algebra Λ A := ((algebraMap R A).comp r).toAlgebra
  exact { carrier := A
          residueEquiv := {
            __ := A.residueEquiv.toRingEquiv
            commutes' := fun x => A.residueEquiv.commutes (r x) } }

private noncomputable def restrictArtinianLocalAlgHom
    {Λ R k : Type u} [CommRing Λ] [CommRing R] [Field k] [Algebra R k]
    (r : Λ →+* R) {A' A : Deformation.ArtinianLocalAlgCat.{u, u, u} R k}
    (φ : A' ⟶ A) :
    letI : Algebra Λ k := ((algebraMap R k).comp r).toAlgebra
    restrictArtinianLocalAlg r A' ⟶ restrictArtinianLocalAlg r A := by
  letI : Algebra Λ k := ((algebraMap R k).comp r).toAlgebra
  exact {
  hom := { __ := φ.hom.toRingHom
           commutes' := fun x => φ.hom.commutes (r x) }
  isLocal := φ.isLocal
  residue_comm := φ.residue_comm }

/-- Changing coefficients from a local ring to an affine neighborhood does not
change a scheme lifting problem. -/
private theorem exists_scheme_lift_of_affine_factorization
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (W V : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ V)
    (hs : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map W.hom) (Over.map V.hom) (Over.map g.left)
      (by rw [← Over.mapComp_eq, g.w]))
    {Λ R k : Type u} [CommRing Λ] [CommRing R] [Field k] [Algebra R k]
    (r : Λ →+* R) (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (iR : Spec (.of R) ⟶ S) (hi : Spec.map (CommRingCat.ofHom r) ≫ iΛ = iR)
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR)]
    [QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR)]
    (w₀ : Spec (.of k) ⟶ W.left.1)
    (hw₀ : w₀ ≫ W.hom.hom = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR)
    (A' A : Deformation.ArtinianLocalAlgCat.{u, u, u} R k)
    (φ : A' ⟶ A) (hφ : Function.Surjective φ.hom)
    (α : Spec (.of A) ⟶ W.left.1) (β : Spec (.of A') ⟶ V.left.1)
    (hα : α ≫ W.hom.hom = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR)
    (hβ : β ≫ V.hom.hom = Spec.map (CommRingCat.ofHom (algebraMap R A')) ≫ iR)
    (hα₀ : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ α = w₀)
    (hβ₀ : Spec.map (CommRingCat.ofHom (residueMap A')) ≫ β = w₀ ≫ g.left.hom)
    (hcomm : α ≫ g.left.hom = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ β) :
    ∃ γ : Spec (.of A') ⟶ W.left.1,
      Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ γ = α ∧ γ ≫ g.left.hom = β := by
  let : Algebra Λ k := ((algebraMap R k).comp r).toAlgebra
  have hbase (T : Type u) [CommRing T] [Algebra R T] :
      Spec.map (CommRingCat.ofHom ((algebraMap R T).comp r)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ iR := by
    rw [show CommRingCat.ofHom ((algebraMap R T).comp r) =
      CommRingCat.ofHom r ≫ CommRingCat.ofHom (algebraMap R T) from rfl,
      Spec.map_comp, Category.assoc, hi]
  have hk : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR := hbase k
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    hk.symm ▸ inferInstance
  let : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    hk.symm ▸ inferInstance
  exact exists_scheme_lift_of_isSmoothOnPredeformationCategories B S hS W V g hs
    iΛ w₀ (hw₀.trans hk.symm)
    (restrictArtinianLocalAlg r A') (restrictArtinianLocalAlg r A)
    (restrictArtinianLocalAlgHom r φ) hφ α β
    (hα.trans (hbase A).symm) (hβ.trans (hbase A').symm) hα₀ hβ₀ hcomm

private theorem smoothAt_of_isSmoothOnPredeformationCategories
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (W V : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ V)
    [LocallyOfFiniteType W.hom.hom] [LocallyOfFiniteType V.hom.hom]
    (hs : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map W.hom) (Over.map V.hom) (Over.map g.left)
      (by rw [← Over.mapComp_eq, g.w]))
    (w : W.left.1) (hw : AlgebraicGeometry.IsFiniteTypePoint w) :
    InfinitesimalLifting.SmoothAt g.left.hom w := by
  have hg : g.left.hom ≫ V.hom.hom = W.hom.hom :=
    congrArg (fun z => z.hom) g.w
  have : LocallyOfFiniteType (g.left.hom ≫ V.hom.hom) := hg.symm ▸ inferInstance
  let : IsLocallyNoetherian (B.obj hS).obj := ‹IsLocallyNoetherian S›
  apply (Deformation.Artin.smoothAt_iff_isVersalAt (S := S) g.left.hom V.hom.hom w hw).mpr
  let U : Over S := Over.mk (g.left.hom ≫ V.hom.hom)
  let s : S := basePoint U w
  let R := S.presheaf.stalk s
  let : Algebra R (W.left.1.residueField w) := residueFieldAlgebra U w
  obtain ⟨O, hO, hsO, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s ∈ (⊤ : S.Opens) from trivial)
  let r : Γ(S, O) →+* R := (S.presheaf.germ O s hsO).hom
  have hi : Spec.map (CommRingCat.ofHom r) ≫ hO.fromSpec = S.fromSpecStalk s :=
    hO.fromSpecStalk_eq_fromSpecStalk hsO
  have hwbase : W.left.1.fromSpecResidueField w ≫ W.hom.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (W.left.1.residueField w))) ≫
        S.fromSpecStalk s := by
    rw [← hg]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk
      (residueFieldBasePoint U w)).symm
  let : LocallyOfFiniteType (W.left.1.fromSpecResidueField w) := hw.1
  let : QuasiCompact (W.left.1.fromSpecResidueField w) := hw.2
  let : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R (W.left.1.residueField w))) ≫
        S.fromSpecStalk s) := hwbase ▸ inferInstance
  let : QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap R (W.left.1.residueField w))) ≫
        S.fromSpecStalk s) := by
    rw [← hwbase]
    infer_instance
  change Deformation.Artin.IsVersalAt U (Over.forget (Over.mk V.hom.hom)) w
    (Over.mk (Over.homMk (U := U) g.left.hom (by rfl))) rfl
  dsimp only [Deformation.Artin.IsVersalAt]
  intro A A' φ hφ y z hy hz i hi' a ha
  let : Algebra (S.presheaf.stalk (basePoint U w))
      (U.left.residueField w) := residueFieldAlgebra U w
  let α : Spec (.of A) ⟶ W.left.1 :=
    eqToHom (congrArg Over.left hy).symm ≫ a.left.left
  let β : Spec (.of A') ⟶ V.left.1 :=
    eqToHom (congrArg Over.left hz).symm ≫ z.hom.left
  have hα : α ≫ W.hom.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ S.fromSpecStalk s := by
    rw [← hg]
    dsimp only [α]
    rw [Category.assoc]
    change eqToHom _ ≫ (a.left.left ≫ (Over.mk
      (g.left.hom ≫ V.hom.hom) : Over S).hom) = _
    exact (congrArg (fun f => eqToHom (congrArg Over.left hy).symm ≫ f)
      a.left.w).trans (by
        simpa only [Over.eqToHom_left, Over.forget_obj, Over.mk_left, Over.mk_hom,
          AlgebraicGeometry.BigFppfSite.obj, R, s] using (eqToHom hy.symm).w)
  have hβ : β ≫ V.hom.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A')) ≫ S.fromSpecStalk s := by
    dsimp only [β]
    rw [Category.assoc]
    exact (congrArg (fun f => eqToHom (congrArg Over.left hz).symm ≫ f)
      z.hom.w).trans (by
        simpa only [Over.eqToHom_left, Over.forget_obj, Over.mk_left, Over.mk_hom,
          AlgebraicGeometry.BigFppfSite.obj, R, s] using (eqToHom hz.symm).w)
  change eqToHom (congrArg Over.left hy).symm ≫ i.left.left ≫
    eqToHom (congrArg Over.left hz) = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) at hi'
  have hcomm : α ≫ g.left.hom =
      Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ β := by
    rw [← hi']
    simp only [α, β, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    change eqToHom _ ≫ a.left.left ≫ g.left.hom =
      eqToHom _ ≫ i.left.left ≫ z.hom.left
    have ha' := congrArg (fun f => f.left) a.w
    have hi'' := congrArg (fun f => f.left) i.w
    change a.left.left ≫ g.left.hom = y.hom.left at ha'
    change i.left.left ≫ z.hom.left = y.hom.left at hi''
    rw [ha', hi'']
  have hα₀ : Spec.map (CommRingCat.ofHom (residueMap A)) ≫ α =
      W.left.1.fromSpecResidueField w := by
    simpa [α, U, Category.assoc] using ha
  have hβ₀ : Spec.map (CommRingCat.ofHom (residueMap A')) ≫ β =
      W.left.1.fromSpecResidueField w ≫ g.left.hom := by
    have hres : CommRingCat.ofHom φ.hom.toRingHom ≫
        CommRingCat.ofHom (residueMap A) =
        CommRingCat.ofHom (residueMap A') := by
      ext x
      exact φ.residue_comm x
    rw [← hres, Spec.map_comp, Category.assoc, ← hcomm, ← Category.assoc, hα₀]
  obtain ⟨γ, hγ, hγg⟩ := exists_scheme_lift_of_affine_factorization
    B S hS W V g hs (k := U.left.residueField w) r hO.fromSpec (S.fromSpecStalk s) hi
    (W.left.1.fromSpecResidueField w) hwbase A' A φ hφ α β hα hβ hα₀ hβ₀ hcomm
  let b : z ⟶ Over.mk (Over.homMk (U := U) g.left.hom (by rfl)) :=
    Over.homMk (Over.homMk (eqToHom (congrArg Over.left hz) ≫ γ) (by
      change (eqToHom (congrArg Over.left hz) ≫ γ) ≫
        (g.left.hom ≫ V.hom.hom) = z.left.hom
      rw [Category.assoc, ← Category.assoc γ, hγg]
      simp only [β, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      exact z.hom.w)) (by
      apply Over.OverMorphism.ext
      change (eqToHom _ ≫ γ) ≫ g.left.hom = z.hom.left
      rw [Category.assoc, hγg]
      simp [β])
  refine ⟨b, ?_⟩
  apply Over.OverMorphism.ext
  apply Over.OverMorphism.ext
  change i.left.left ≫ (eqToHom _ ≫ γ) = a.left.left
  apply (cancel_epi (eqToHom (congrArg Over.left hy).symm)).mp
  rw [← Category.assoc, ← Category.assoc]
  change (eqToHom _ ≫ i.left.left ≫ eqToHom _) ≫ γ = _
  rw [hi', hγ]

/-- A morphism `g : W ⟶ V` of schemes locally of finite type over a locally Noetherian base `S`
whose induced 1-morphism of slice categories satisfies the deformation-theoretic smoothness
condition of Stacks 07XS is a smooth morphism of schemes.

This is the case of Stacks 07XX in which the 1-morphism is the one induced by a morphism of
schemes over `S`. It is the step the source calls the key ingredient of its proof, namely its
appeal to More on Morphisms, Lemma 02HX; here that appeal is routed through the scheme-level
criterion `Deformation.Artin.smoothAt_iff_isVersalAt` (Stacks 0CXL), which is 02HX in versality
form, together with openness of the smooth locus and density of finite type points
(Stacks 02J4). The general statement of Stacks 07XX, for an arbitrary 1-morphism, is
`AlgebraicGeometry.Stack.isRelativelySmooth_of_isSmoothOnPredeformationCategories`, which reduces
to this lemma through an étale atlas of the 2-fibre product. -/
public theorem smooth_of_isSmoothOnPredeformationCategories
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (W V : AlgebraicGeometry.BigFppfOver B S hS) (g : W ⟶ V)
    [LocallyOfFiniteType W.hom.hom] [LocallyOfFiniteType V.hom.hom]
    (hs : Deformation.Artin.IsSmoothOnPredeformationCategories B S hS
      (Over.map W.hom) (Over.map V.hom) (Over.map g.left)
      (by rw [← Over.mapComp_eq, g.w])) : Smooth g.left.hom := by
  let : IsLocallyNoetherian (B.obj hS).obj := ‹IsLocallyNoetherian S›
  let : IsLocallyNoetherian V.left.1 :=
    LocallyOfFiniteType.isLocallyNoetherian V.hom.hom
  have hg : g.left.hom ≫ V.hom.hom = W.hom.hom := congrArg (fun z => z.hom) g.w
  let : LocallyOfFiniteType (g.left.hom ≫ V.hom.hom) := hg.symm ▸ inferInstance
  let : LocallyOfFiniteType g.left.hom := locallyOfFiniteType_of_comp _ V.hom.hom
  exact smooth_of_smoothAt_finiteTypePoints g.left.hom
    (smoothAt_of_isSmoothOnPredeformationCategories B S hS W V g hs)


end Deformation.Artin

end
