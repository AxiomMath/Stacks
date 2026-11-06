module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldVersalLift
public import StacksFrontier.Deformation.FormalObject.VersalCriterion
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# The differential of the associated morphism is surjective at the dual numbers

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `x` an object of `𝒳` over
`U`, and `x₀` its restriction to a residue-field point. Write `𝓕` for the predeformation
category of `x₀` over `𝒞_Λ` — `Deformation.Artin.PredeformationConstruction` realizes it —
and let `η` be a formal object of `𝓕` whose complete local base `R` is presented over `U` by
a morphism `g : Spec R ⟶ U`.

The versality criterion of **Stacks 06IU** characterizes versality of `η` by two conditions.
The first of them, condition (a), is the surjectivity of `Deformation.mapIsomorphismClasses`
for the associated morphism of `η` at the dual numbers `k[ε]` — in the source's words, that
the differential of the associated morphism is surjective. This file proves that condition
from the geometric statement it corresponds to: that every lift of `x₀` over `k[ε]` extends
to `x`.

That geometric statement is one instance of the lifting property
`Deformation.Artin.LiftsAtResiduePoint` defining versality at a point: the instance at the
augmentation `k[ε] ⟶ k`. Versality itself quantifies the property over *every* surjection of
`𝒞_Λ`, and the degree-`0` half of **Stacks 07YM** delivers only this one instance, which is
why the condition is isolated here rather than obtained from
`Deformation.Artin.isVersalAt_iff_isVersal`.

## Main definitions

* `Deformation.Artin.residuePointMorphism` — the augmentation of an object of `𝒞_Λ` onto its
  residue field, read as a morphism to `Deformation.Artin.fieldArtinianObj`. Its underlying
  ring map is `Deformation.Artin.residueMap`, so it is the arrow of `𝒞_Λ` that the
  closed-point map of a deformation lies over.
* `Deformation.Artin.ExtendsAtArtinianBase` — the geometric hypothesis: every lift of `x₀`
  over a given object of `𝒞_Λ` extends to `x`. Taken at
  `Deformation.artinianDualNumbers`, this is the dual-numbers statement.

## Main results

* `Deformation.surjective_mapIsomorphismClasses_of_iso` — surjectivity of
  `Deformation.mapIsomorphismClasses` depends on the Artinian point only through its
  isomorphism class.
* `Deformation.Artin.surjective_mapIsomorphismClasses_of_extendsAtArtinianBase` — the
  condition for an arbitrary morphism out of the category of elements of the restricted
  coyoneda functor of the complete local base, under the data that makes it a cone over `x`.
* `Deformation.Artin.surjective_mapIsomorphismClasses_associatedMorphism` — the same for the
  associated morphism of a formal object of the predeformation category, with the cone
  presented levelwise, and
  `Deformation.Artin.surjective_mapIsomorphismClasses_artinianDualNumbers` its value at the
  dual numbers, which is condition (a) in the shape Stacks 06IU states it.
* `Deformation.Artin.extendsAtArtinianBase_of_liftsAtResiduePoint` — the hypothesis is
  implied by the full lifting property, so these are consequences of versality at the point
  as well.

## Implementation notes

Nothing in the argument is special to the dual numbers: the lifting property at the
augmentation of an object `A` of `𝒞_Λ` gives surjectivity at `A`, and `A` is taken arbitrary
for that reason. The named dual-numbers case is the instance at
`Deformation.artinianDualNumbers`, the square-zero extension of `k` by `k` lifted into the
carrier universe, which is the object Stacks 06IU evaluates
`Deformation.mapIsomorphismClasses` at. Since the two presentations of `k[ε]` the tree uses —
that one and the site's `Deformation.Artin.squareZeroArtinianObj` at `ModuleCat.of k k`,
whose carrier is not universe-lifted — are isomorphic rather than equal,
`Deformation.surjective_mapIsomorphismClasses_of_iso` is proved to move the conclusion
between them; it is a statement about `𝒞_Λ` alone and asks nothing of the site.

The residue field is presented as `Deformation.Artin.fieldArtinianObj`, whose carrier is `k`
itself and whose algebra map is therefore the structure map of `k`; this is what makes the
identification of the closed fibre of a deformation with the base of `x₀` an equality rather
than an isomorphism, so that `hx₀` serves directly as the hypothesis the lifting property
asks about the source of the arrow.

The surjectivity is proved on representatives. Every class over `A` is the class of an object
`y` of the predeformation category (`Deformation.classOf_surjective`), that is of a
deformation of `x₀` over `A`, whose closed-point arrow lies over the augmentation
`Deformation.Artin.residuePointMorphism` by
`Deformation.Artin.deformationObject_residueMap`; the hypothesis therefore extends the arrow
`x₀ ⟶ x` across it, and `Deformation.Artin.restriction_lifts_deformationObject` then exhibits
`y`, up to a vertical arrow, as a value of the morphism on an Artinian point of the complete
local base. A vertical arrow does not have to be inverted: `Deformation.map_classOf` along
the identity of `A` already identifies the two classes.

That the conclusion really is condition (a) of the criterion is pinned by a machine check
rather than by inspection: the private `isVersal_of_extendsAtDualNumbers_of_base_lifts` at
the end of the file feeds the result into
`Deformation.isVersal_iff_differential_surjective_and_base_lifts`, taking condition (b) of
the tag — the lifting of the map of complete local algebras along a small extension — as a
hypothesis spelled out in full, since it is not proved here. If either statement drifts, that
check stops compiling.

## References

* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation

universe u v w uC vC u₁ v₁ u₂ v₂

/-! ### Changing the Artinian point by an isomorphism -/

/-- Surjectivity of `Deformation.mapIsomorphismClasses` depends on the Artinian point only
through its isomorphism class: the functors of fibrewise isomorphism classes send an
isomorphism of the base to a bijection, and `Deformation.mapIsomorphismClasses_naturality`
makes the resulting square commute. -/
public theorem surjective_mapIsomorphismClasses_of_iso
    {C : Type uC} [Category.{vC} C]
    {𝓕 : BasedCategory.{v₁, u₁} C} {𝓖 : BasedCategory.{v₂, u₂} C}
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) (h𝓖 : IsCofiberedInGroupoids 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) {A A' : C} (e : A ≅ A')
    (h : Function.Surjective (mapIsomorphismClasses h𝓕 h𝓖 φ A)) :
    Function.Surjective (mapIsomorphismClasses h𝓕 h𝓖 φ A') := by
  intro z
  obtain ⟨t, ht⟩ := h ((isomorphismClasses 𝓖 h𝓖).map e.inv z)
  refine ⟨(isomorphismClasses 𝓕 h𝓕).map e.hom t, ?_⟩
  rw [mapIsomorphismClasses_naturality h𝓕 h𝓖 φ e.hom t, ht,
    ← Functor.map_comp_apply, e.inv_hom_id, Functor.map_id_apply]

namespace Artin

/-! ### The augmentation onto the residue field -/

section Augmentation

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The augmentation of an object of `𝒞_Λ` onto its residue field, read as a morphism to
`Deformation.Artin.fieldArtinianObj`: the residue map followed by the chosen identification
of the residue field with `k`. -/
public def residuePointMorphism (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    A ⟶ fieldArtinianObj Λ k where
  hom := A.residueEquiv.toAlgHom.comp (IsScalarTower.toAlgHom Λ A (ResidueField A))
  isLocal := IsLocalHom.of_surjective _
    (A.residueEquiv.surjective.comp (residue_surjective (R := A)))
  residue_comm _ := rfl

/-- The ring map underlying the augmentation is `Deformation.Artin.residueMap`, which is the
map a deformation's closed-point arrow lies over. -/
public theorem residuePointMorphism_hom_toRingHom
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (residuePointMorphism A).hom.toRingHom = residueMap A := rfl

/-- The augmentation onto the residue field is surjective, being a residue map. -/
public theorem surjective_residuePointMorphism
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Function.Surjective (residuePointMorphism A).hom :=
  A.residueEquiv.surjective.comp (residue_surjective (R := A))

end Augmentation

/-! ### Lifts of `x₀` over an Artinian base -/

section Extends

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {F : Type v} [Category.{w} F] (q : F ⥤ Over S)
    {x₀ : F} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (U : Over S) {x : F} (hx : q.obj x = U) (r₀ : x₀ ⟶ x)

/-- Every lift of `x₀` over the object `A` of `𝒞_Λ` extends to `x`: for an arrow `i : y ⟶ z`
lying over the augmentation `A ⟶ k`, whose source carries an arrow `a` to `x` with the same
underlying morphism of schemes as `r₀`, there is an arrow `z ⟶ x` composing with `i` to give
`a`.

This is the instance of `Deformation.Artin.LiftsAtResiduePoint` at the single surjection
`Deformation.Artin.residuePointMorphism` of `A`, written out. At
`Deformation.artinianDualNumbers` it is the dual-numbers statement that the degree-`0` half
of Stacks 07YM supplies. -/
public abbrev ExtendsAtArtinianBase
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) : Prop :=
  ∀ (y z : F)
    (hy : q.obj y = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ (fieldArtinianObj Λ k))) ≫ iΛ))
    (hz : q.obj z = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (i : y ⟶ z),
    schemeMap q hy hz i =
        Spec.map (CommRingCat.ofHom (residuePointMorphism A).hom.toRingHom) →
    ∀ a : y ⟶ x,
      Spec.map (CommRingCat.ofHom (residueMap (fieldArtinianObj Λ k))) ≫
          schemeMap q hy hx a =
        schemeMap q hx₀ hx r₀ →
      ∃ b : z ⟶ x, i ≫ b = a

/-- The lifting property defining versality at the residue point of `r₀` extends, in
particular, every lift of `x₀` over a single object of `𝒞_Λ`. -/
public theorem extendsAtArtinianBase_of_liftsAtResiduePoint
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hl : LiftsAtResiduePoint iΛ q U x hx (schemeMap q hx₀ hx r₀)) :
    ExtendsAtArtinianBase iΛ q hx₀ U hx r₀ A :=
  hl (fieldArtinianObj Λ k) A (residuePointMorphism A) (surjective_residuePointMorphism A)

end Extends

/-! ### Condition (a) of the versality criterion -/

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
/-- **Condition (a) of Stacks 06IU, from the lifting property at one Artinian base.** Let `H`
be a morphism from the category of elements of the restricted coyoneda functor of a complete
local algebra `R` to the predeformation category of `x₀`, let `r` be a cone on it over `x`
whose components lie over the points of `R` picked out by `g` (`hbase`) and restrict to `r₀`
on the closed fibre (`hclosed`), and let every Artinian point of `U` compatible with `r₀`
factor through `g` (`hpoints`). If every lift of `x₀` over the object `A` of `𝒞_Λ` extends to
`x`, then `Deformation.mapIsomorphismClasses` for `H` is surjective at `A`.

Surjectivity is checked on representatives. A class over `A` is the class of a deformation
`y` of `x₀` over `A`, whose closed-point arrow lies over the augmentation
`Deformation.Artin.residuePointMorphism` by `Deformation.Artin.deformationObject_residueMap`;
the hypothesis therefore extends `r₀` across it, and
`Deformation.Artin.restriction_lifts_deformationObject` produces an Artinian point `β` of `R`
and a vertical arrow `H(β) ⟶ y`, whence the two classes agree by `Deformation.map_classOf`
along the identity of `A`. -/
public theorem surjective_mapIsomorphismClasses_of_extendsAtArtinianBase
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hext : ExtendsAtArtinianBase iΛ (p ⋙ Over.post B.inclusion) hx₀ U hx r₀ A) :
    Function.Surjective (Deformation.mapIsomorphismClasses
      (Deformation.categoryOfElements_projection_isCofibered
        (Deformation.restrictedCoyoneda R))
      hpC H A) := by
  classical
  intro z
  obtain ⟨y, rfl⟩ := Deformation.classOf_surjective
    (BasedCategory.ofFunctor C.projection) hpC A z
  have hyA : C.projection.obj y.1 = A := y.2
  obtain ⟨b, hb⟩ := hext x₀ (C.objects y.1).point hx₀
    (deformationPointBase C y.1 A hyA) (C.objects y.1).arrow
    (deformationObject_residueMap C y.1 A hyA)
    r₀ (by
      show Spec.map (𝟙 (CommRingCat.of k)) ≫
          schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀ =
        schemeMap (p ⋙ Over.post B.inclusion) hx₀ hx r₀
      simp)
  obtain ⟨β, a, ha, -⟩ := restriction_lifts_deformationObject B S hS p hp hx₀ C R H U hx r r₀ g
    hbase hclosed hpoints y.1 b hb
  have := ha
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
/-- **Condition (a) of Stacks 06IU for the associated morphism of a formal object.** Let `η`
be a formal object of the predeformation category of `x₀`, with a compatible family of arrows
`restriction` from its levels to `x` lying over the thickenings of `η.base` cut out by `g`
and restricting to `r₀` on the closed fibre, and let every Artinian point of `U` compatible
with `r₀` factor through `g`. If every lift of `x₀` over the object `A` of `𝒞_Λ` extends to
`x`, then `Deformation.mapIsomorphismClasses` for the associated morphism of `η` is
surjective at `A`.

The cone on the associated morphism is `Deformation.Artin.associatedMorphismRestriction`, the
one Stacks 0CXK builds from the same levelwise data; its two compatibilities are
`Deformation.Artin.associatedMorphismRestriction_base` and
`Deformation.Artin.associatedMorphismRestriction_closedPoint`. -/
public theorem surjective_mapIsomorphismClasses_associatedMorphism
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hext : ExtendsAtArtinianBase iΛ (p ⋙ Over.post B.inclusion) hx₀ U hx r₀ A) :
    Function.Surjective (Deformation.mapIsomorphismClasses
      (Deformation.categoryOfElements_projection_isCofibered
        (Deformation.restrictedCoyoneda η.base))
      hpC Hm.toBasedFunctor A) :=
  surjective_mapIsomorphismClasses_of_extendsAtArtinianBase B S hS p hp hx₀ C hpC U hx r₀
    η.base Hm.toBasedFunctor
    (associatedMorphismRestriction η Hm (deformationForget C) restriction
      restriction_transition)
    g
    (associatedMorphismRestriction_base C η Hm restriction restriction_transition U hx g hbase)
    (associatedMorphismRestriction_closedPoint C η Hm restriction restriction_transition r₀
      hclosed)
    hpoints A hext

include hp restriction_transition hbase hclosed hpoints in
/-- **Condition (a) of Stacks 06IU.** Specialization of
`Deformation.Artin.surjective_mapIsomorphismClasses_associatedMorphism` to the dual numbers:
if every lift of `x₀` over `k[ε]` extends to `x`, then the differential of the associated
morphism of `η` is surjective, which is the first of the two conditions of the versality
criterion. -/
public theorem surjective_mapIsomorphismClasses_artinianDualNumbers
    (hext : ExtendsAtArtinianBase iΛ (p ⋙ Over.post B.inclusion) hx₀ U hx r₀
      (Deformation.artinianDualNumbers.{u, u, u} Λ k)) :
    Function.Surjective (Deformation.mapIsomorphismClasses
      (Deformation.categoryOfElements_projection_isCofibered
        (Deformation.restrictedCoyoneda η.base))
      hpC Hm.toBasedFunctor (Deformation.artinianDualNumbers.{u, u, u} Λ k)) :=
  surjective_mapIsomorphismClasses_associatedMorphism B S hS p hp hx₀ C hpC U hx r₀ η Hm
    restriction restriction_transition g hbase hclosed hpoints _ hext

include hp restriction_transition hbase hclosed hpoints in
/-- The previous result is condition (a) of Stacks 06IU verbatim: together with condition (b)
of that tag, which is assumed here and is not proved in this file, it closes the criterion
and gives versality of the formal object.

This exists to pin the shape of
`Deformation.Artin.surjective_mapIsomorphismClasses_artinianDualNumbers` against
`Deformation.isVersal_iff_differential_surjective_and_base_lifts`: nothing is proved here
beyond feeding that result into the criterion, so a drift in either statement breaks the
file. -/
private theorem isVersal_of_extendsAtDualNumbers_of_base_lifts
    (hpre : Deformation.IsPredeformationCategory
      (BasedCategory.ofFunctor C.projection).p)
    (hS1 : Deformation.SchlessingerConditionS1 (BasedCategory.ofFunctor C.projection).p)
    (hS2 : Deformation.SchlessingerConditionS2 (BasedCategory.ofFunctor C.projection).p)
    (Q : Deformation.ChosenPushforwards C.projection)
    (hext : ExtendsAtArtinianBase iΛ (p ⋙ Over.post B.inclusion) hx₀ U hx r₀
      (Deformation.artinianDualNumbers.{u, u, u} Λ k))
    (hlifts : ∀ ⦃A₂ A₁ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k⦄ (f : A₂ ⟶ A₁),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ ⦃y₂ y₁ : Deformation.FormalObject
          (BasedCategory.ofFunctor C.projection).p⦄ (g₂ : y₂ ⟶ y₁),
        (Deformation.FormalObject.projection
            (p := (BasedCategory.ofFunctor C.projection).p)).IsHomLift
          (Deformation.artinianToComplete.map f) g₂ →
        ∀ a₂ : η ⟶ y₁, ∃ b₂ : η.base ⟶ y₂.base, b₂ ≫ g₂.base = a₂.base) :
    Deformation.IsVersal hpre.cofibered η :=
  (Deformation.isVersal_iff_differential_surjective_and_base_lifts
      (BasedCategory.ofFunctor C.projection) hpre hS1 hS2 η Q).mpr
    ⟨surjective_mapIsomorphismClasses_artinianDualNumbers B S hS p hp hx₀ C
      hpre.cofibered U hx r₀ η (Deformation.associatedMorphism hpre.cofibered η Q)
      restriction restriction_transition g hbase hclosed hpoints hext, hlifts⟩

end Associated

end Condition

end Artin

end Deformation

end
