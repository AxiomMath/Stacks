module

public import StacksFrontier.Deformation.Artin.Versality.DualNumbersIsomorphismClasses

/-!
# Condition (a) of Stacks 06IU, from the lifting statement at the closed fibre alone

`Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase` derives
condition (a) of [Stacks, Tag 06IU] from `Deformation.Artin.ExtendsAtArtinianBase`, which
quantifies over *every* lift of *every* object over the residue field together with *every*
arrow of it to `x`. Its proof applies that hypothesis at a single instance: the source of the
arrow is the fixed closed fibre `x₀` and the arrow to `x` is the fixed `r₀`.

The direction `(2) ⇒ (1)` of [Stacks, Tag 07YM] produces exactly that single instance and no
more — `Deformation.Artin.extendsDeformation_of_exists_extends` is where it comes out — so
this file restates the condition under the weaker hypothesis.

## Main definitions

* `Deformation.Artin.ExtendsDeformationAtArtinianBase` — every deformation of `x₀` over a
  given object of `𝒞_Λ` extends `r₀` to `x`. This is
  `Deformation.Artin.ExtendsAtArtinianBase` with the source of the arrow and the arrow to `x`
  pinned to `x₀` and `r₀`, and it is implied by it.

## Main results

* `Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsDeformation` — condition (a)
  of [Stacks, Tag 06IU] from the weaker hypothesis, for an arbitrary morphism out of the
  category of elements.
* `Deformation.Artin.surjective_mapIsomorphismClasses_associatedMorphism_of_extendsDeformation`
  — the same for the associated morphism of a formal object, with the cone presented
  levelwise, which is the shape
  `Deformation.isVersal_iff_differential_surjective_and_base_lifts` consumes.

## Implementation notes

The proof is the one of
`Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase`, with the one
application of the hypothesis rewritten. Nothing else changes: the class over `A` is the class
of a deformation `y` of `x₀` (`Deformation.classOf_surjective`), whose closed-point arrow lies
over the augmentation by `Deformation.Artin.deformationObject_residueMap`, and
`Deformation.Artin.restriction_lifts_deformationObject` exhibits `y`, up to a vertical arrow,
as a value of the morphism.

## References

* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

section Condition

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F] (p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {iΛ : Spec (.of Λ) ⟶ S} {x₀ : F}
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (C : Deformation.Artin.PredeformationConstruction iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hpC : Deformation.IsCofiberedInGroupoids C.projection)
    {x : F} (U : Over S) (hx : (p ⋙ Over.post B.inclusion).obj x = U) (r₀ : x₀ ⟶ x)

/-- Every deformation of `x₀` over the object `A` of `𝒞_Λ` extends `r₀` to `x`: for an arrow
`i : x₀ ⟶ z` lying over the augmentation `A ⟶ k`, there is an arrow `z ⟶ x` composing with
`i` to give `r₀`.

This is `Deformation.Artin.ExtendsAtArtinianBase` with the source of the arrow pinned to `x₀`
and the arrow to `x` pinned to `r₀` — the only instance of it that condition (a) of
[Stacks, Tag 06IU] uses. -/
public abbrev ExtendsDeformationAtArtinianBase
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) : Prop :=
  ∀ (z : F) (hz : (p ⋙ Over.post B.inclusion).obj z = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (i : x₀ ⟶ z),
    schemeMap (p ⋙ Over.post B.inclusion) hx₀ hz i =
        Spec.map (CommRingCat.ofHom (residuePointMorphism A).hom.toRingHom) →
    ∃ b : z ⟶ x, i ≫ b = r₀

/-- The hypothesis of
`Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase`
implies the weaker one used here: it is that hypothesis at `y = x₀` and `a = r₀`. -/
public theorem extendsDeformationAtArtinianBase_of_extendsAtArtinianBase
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hext : ExtendsAtArtinianBase iΛ (p ⋙ Over.post B.inclusion) hx₀ U hx r₀ A) :
    ExtendsDeformationAtArtinianBase B S hS p hx₀ r₀ A := by
  intro z hz i hi
  refine hext x₀ z hx₀ hz i hi r₀ ?_
  show Spec.map (𝟙 (CommRingCat.of k)) ≫
      schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ =
    schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀
  simp

/-- **`ExtendsAtArtinianBase` depends on the closed fibre and its arrow to `x` only through
the morphism of schemes they induce.** Reading the definition, `hx₀` and `r₀` occur in it at
exactly one place, inside `schemeMap q hx₀ hx r₀`; so two pairs inducing the same morphism
give the same statement.

This is what matches the closed fibre the degree-`0` half of [Stacks, Tag 07YM] produces --
the chosen pullback of `x` along `Spec κ(u₀) ⟶ Spec A` -- with the one the criterion of
[Stacks, Tag 06IU] is applied at, the level `0` of the approximation formal object. No
cartesian lifting is involved: the two induce the same morphism, and that is all the
statement sees. -/
public theorem extendsAtArtinianBase_congr
    {x₀' : F} (hx₀' : (p ⋙ Over.post B.inclusion).obj x₀' = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (r₀' : x₀' ⟶ x)
    (hr : schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ =
      schemeMap (p ⋙ Over.post B.inclusion) hx₀' hx r₀')
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    ExtendsAtArtinianBase iΛ (p ⋙ Over.post B.inclusion) hx₀ U hx r₀ A ↔
      ExtendsAtArtinianBase iΛ (p ⋙ Over.post B.inclusion) hx₀' U hx r₀' A := by
  unfold ExtendsAtArtinianBase
  rw [hr]

include hp in
/-- **The lifting statement at the closed fibre depends on the closed fibre only through its
arrow to `x`.** Two objects over the residue point carrying arrows to `x` with the same
underlying morphism of schemes are isomorphic over the identity, compatibly with those arrows,
because `p` is fibred in groupoids; so the statement transports.

This is what matches the closed fibre the degree-`0` half of [Stacks, Tag 07YM] produces --
the chosen pullback of `x` along `Spec κ(u₀) ⟶ Spec A` -- with the one the criterion of
[Stacks, Tag 06IU] is applied at, the level `0` of the approximation formal object. -/
public theorem extendsDeformationAtArtinianBase_congr
    {x₀' : F} (hx₀' : (p ⋙ Over.post B.inclusion).obj x₀' = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (r₀' : x₀' ⟶ x)
    (hr : schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ =
      schemeMap (p ⋙ Over.post B.inclusion) hx₀' hx r₀')
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hext : ExtendsDeformationAtArtinianBase B S hS p hx₀ r₀ A) :
    ExtendsDeformationAtArtinianBase B S hS p hx₀' r₀' A := by
  obtain ⟨e, ⟨he, her⟩, -⟩ := factor_through_cartesian_schemeMap B S hS p hp hx₀' hx₀ hx r₀ r₀'
    (𝟙 _) (Category.id_comp _) (by rw [Category.id_comp]; exact hr)
  have : IsIso e := schemeMap_id_isIso B S hS p hp hx₀' hx₀ e he
  have hid : ∀ {Y : Over S} {y : F} (hy : (p ⋙ Over.post B.inclusion).obj y = Y),
      schemeMap (p ⋙ Over.post B.inclusion) hy hy (𝟙 y) = 𝟙 Y.left := by
    intro Y y hy
    subst hy
    simp only [schemeMap, eqToHom_refl, Category.comp_id, Category.id_comp]
    exact congrArg Over.Hom.left ((p ⋙ Over.post B.inclusion).map_id y)
  have hinv : schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx₀' (inv e) = 𝟙 _ := by
    apply (cancel_mono (schemeMap (p ⋙ Over.post B.inclusion) hx₀' hx₀ e)).mp
    rw [← schemeMap_comp (p ⋙ Over.post B.inclusion) hx₀ hx₀' hx₀, IsIso.inv_hom_id, he,
      hid hx₀, Category.comp_id]
  intro z hz i hi
  have hside : schemeMap (p ⋙ Over.post B.inclusion) hx₀ hz (inv e ≫ i) =
      Spec.map (CommRingCat.ofHom (residuePointMorphism A).hom.toRingHom) := by
    rw [schemeMap_comp (p ⋙ Over.post B.inclusion) hx₀ hx₀' hz, hinv, Category.id_comp, hi]
  obtain ⟨b, hb⟩ := hext z hz (inv e ≫ i) hside
  exact ⟨b, by rw [← her, ← hb, ← Category.assoc, ← Category.assoc, IsIso.hom_inv_id,
    Category.id_comp]⟩

section General

variable (R : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (H : BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (Deformation.restrictedCoyoneda R)))
      (BasedCategory.ofFunctor C.projection))
    (r : H.toFunctor.op ⋙ deformationForget C ⟶ (Functor.const _).obj x)
    (g : Spec (.of R) ⟶ U.left)
    (hbase : ∀ α, schemeMap (p ⋙ Over.post B.inclusion)
      (deformationPointBase C (H.obj α) α.1 (H.w_obj α)) hx (r.app (.op α)) =
        Spec.map (CommRingCat.ofHom α.2.hom.toRingHom) ≫ g)
    (hclosed : ∀ α, (C.objects (H.obj α)).arrow ≫ r.app (.op α) = r₀)
    (hpoints : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left),
      f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (residueMap A)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ →
      ∃ α : R ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f)

include hp hbase hclosed hpoints in
/-- **Condition (a) of Stacks 06IU, from the lifting statement at the closed fibre alone.**
This is `Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase` with
its hypothesis weakened to the single instance the proof uses: the deformations whose arrow
out of `x₀` has to be extended are the ones the classes over `A` are represented by, and the
arrow to `x` to be matched is always `r₀`. -/
public theorem surjective_mapIsomorphismClasses_of_extendsDeformation
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hext : ExtendsDeformationAtArtinianBase B S hS p hx₀ r₀ A) :
    Function.Surjective (Deformation.mapIsomorphismClasses
      (Deformation.categoryOfElements_projection_isCofibered
        (Deformation.restrictedCoyoneda R))
      hpC H A) := by
  classical
  intro z
  obtain ⟨y, rfl⟩ := Deformation.classOf_surjective
    (BasedCategory.ofFunctor C.projection) hpC A z
  have hyA : C.projection.obj y.1 = A := y.2
  obtain ⟨b, hb⟩ := hext (C.objects y.1).point
    (deformationPointBase C y.1 A hyA) (C.objects y.1).arrow
    (deformationObject_residueMap C y.1 A hyA)
  obtain ⟨β, a, ha, -⟩ := restriction_lifts_deformationObject B S hS p hp hx₀ C R H U hx r r₀ g
    hbase hclosed hpoints y.1 b hb
  have hβ : β.1 = A :=
    (H.w_obj β).symm.trans
      ((IsHomLift.domain_eq C.projection (𝟙 (C.projection.obj y.1)) a).trans hyA)
  refine ⟨Deformation.classOf _ (Deformation.categoryOfElements_projection_isCofibered
    (Deformation.restrictedCoyoneda R)) ⟨β, hβ⟩, ?_⟩
  have ha' : C.projection.IsHomLift (𝟙 A) a :=
    (congrArg (fun T => C.projection.IsHomLift (𝟙 T) a) hyA).mp ha
  refine (Deformation.mapIsomorphismClasses_classOf _ hpC H ⟨β, hβ⟩).trans ?_
  simpa using @Deformation.map_classOf _ _ (BasedCategory.ofFunctor C.projection) hpC
    A A (𝟙 A) ((Deformation.fiberFunctor H A).obj ⟨β, hβ⟩) y a ha'

end General

section Associated

variable (η : Deformation.FormalObject C.projection)
    {P : Deformation.ChosenPushforwards C.projection}
    (Hm : Deformation.AssociatedMorphism η P)
    (restriction : ∀ n, (deformationForget C).obj (.op (η.level n)) ⟶ x)
    (restriction_transition : ∀ n,
      (deformationForget C).map (η.transition n).op ≫ restriction (n + 1) = restriction n)
    (g : Spec (.of η.base) ⟶ U.left)
    (hbase : ∀ n, schemeMap (p ⋙ Over.post B.inclusion)
        (deformationPointBase C (η.level n)
          (Deformation.AdicTruncation.obj η.base n) (η.level_eq n)) hx (restriction n) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Deformation.AdicTruncation.ideal η.base n))) ≫ g)
    (hclosed : ∀ n, (C.objects (η.level n)).arrow ≫ restriction n = r₀)
    (hpoints : ∀ (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : Spec (.of A) ⟶ U.left),
      f ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ →
      Spec.map (CommRingCat.ofHom (residueMap A)) ≫ f =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ →
      ∃ α : η.base ⟶ Deformation.artinianToComplete.obj A,
        Spec.map (CommRingCat.ofHom α.hom.toRingHom) ≫ g = f)

include hp restriction_transition hbase hclosed hpoints in
/-- **Condition (a) of Stacks 06IU for the associated morphism of a formal object**, from the
lifting statement at the closed fibre alone. The cone on the associated morphism is
`Deformation.Artin.associatedMorphismRestriction`, exactly as in
`Deformation.Artin.surjective_mapIsomorphismClasses_associatedMorphism`. -/
public theorem surjective_mapIsomorphismClasses_associatedMorphism_of_extendsDeformation
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hext : ExtendsDeformationAtArtinianBase B S hS p hx₀ r₀ A) :
    Function.Surjective (Deformation.mapIsomorphismClasses
      (Deformation.categoryOfElements_projection_isCofibered
        (Deformation.restrictedCoyoneda η.base))
      hpC Hm.toBasedFunctor A) :=
  surjective_mapIsomorphismClasses_of_extendsDeformation B S hS p hp hx₀ C hpC U hx r₀
    η.base Hm.toBasedFunctor
    (associatedMorphismRestriction η Hm (deformationForget C) restriction
      restriction_transition)
    g
    (associatedMorphismRestriction_base C η Hm restriction restriction_transition U hx g hbase)
    (associatedMorphismRestriction_closedPoint C η Hm restriction restriction_transition r₀
      hclosed)
    hpoints A hext

end Associated

end Condition

end Deformation.Artin

end
