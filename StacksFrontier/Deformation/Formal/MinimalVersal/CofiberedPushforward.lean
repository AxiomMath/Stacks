module

public import StacksFrontier.Deformation.Formal.MinimalVersal.MinimalStages
public import StacksFrontier.Deformation.FormalObject.AdicQuotient

/-!
# Chosen pushforwards in a category cofibered in groupoids

A category cofibered in groupoids has a pushforward along every morphism of the base. This file
fixes one such pushforward for every object and every morphism, records that the resulting arrow
is strongly cocartesian, and derives the arrow it induces out of a pushforward.

## Main definitions

* `Deformation.cofiberedPushforwardData`: a chosen pushforward of an object along a morphism of
  the base, packaged as the target object, the arrow to it and the proof that the arrow lies over
  the given morphism.
* `Deformation.cofiberedPushforwardObj`: the chosen pushforward of an object along a morphism of
  the base.
* `Deformation.cofiberedPushforwardMap`: the chosen arrow from an object to its pushforward along
  a morphism of the base.
* `Deformation.cofiberedPushforwardDesc`: the arrow out of a chosen pushforward induced, by the
  cocartesian property, from an arrow lying over a composite.

## Main results

* `Deformation.cofibered_nonemptyPushforwardData`: a pushforward of an object along a morphism of
  the base exists, as data.
* `Deformation.cofiberedPushforwardMap_lift`: the chosen pushforward arrow lies over the given
  morphism of the base.
* `Deformation.cofiberedPushforwardObj_eq`: the chosen pushforward lies over the target of the
  given morphism of the base.
* `Deformation.cofibered_pushforward_isCocartesian`: the chosen pushforward arrow is strongly
  cocartesian over the given morphism of the base.
* `Deformation.cofiberedPushforwardDesc_lift`: the induced arrow out of a chosen pushforward lies
  over the second factor of the composite.
* `Deformation.cofiberedPushforwardDesc_fac`: the induced arrow out of a chosen pushforward
  recovers the given arrow after composing with the pushforward arrow.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- A pushforward of an object along a morphism of the base exists, as data. -/
theorem cofibered_nonemptyPushforwardData
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B : C} (f : A ⟶ B) (x : G) (hx : q.obj x = A) :
    Nonempty (PSigma fun y : G => PSigma fun g : x ⟶ y => q.IsHomLift f g) := by
  obtain ⟨y, g, hg⟩ := exists_pushforward hq f x hx
  exact ⟨⟨y, ⟨g, hg⟩⟩⟩

/-- A chosen pushforward of an object along a morphism of the base, packaged as the target object,
the arrow to it and the proof that the arrow lies over the given morphism. -/
@[irreducible]
noncomputable def cofiberedPushforwardData
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B : C} (f : A ⟶ B) (x : G) (hx : q.obj x = A) :
    PSigma fun y : G => PSigma fun g : x ⟶ y => q.IsHomLift f g :=
  Classical.choice (cofibered_nonemptyPushforwardData hq f x hx)

/-- The chosen pushforward of an object along a morphism of the base. -/
noncomputable def cofiberedPushforwardObj
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B : C} (f : A ⟶ B) (x : G) (hx : q.obj x = A) : G :=
  (cofiberedPushforwardData hq f x hx).1

/-- The chosen arrow from an object to its pushforward along a morphism of the base. -/
noncomputable def cofiberedPushforwardMap
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B : C} (f : A ⟶ B) (x : G) (hx : q.obj x = A) :
    x ⟶ cofiberedPushforwardObj hq f x hx :=
  (cofiberedPushforwardData hq f x hx).2.1

/-- The chosen pushforward arrow lies over the given morphism of the base. -/
theorem cofiberedPushforwardMap_lift
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B : C} (f : A ⟶ B) (x : G) (hx : q.obj x = A) :
    q.IsHomLift f (cofiberedPushforwardMap hq f x hx) :=
  (cofiberedPushforwardData hq f x hx).2.2

/-- The chosen pushforward lies over the target of the given morphism of the base. -/
theorem cofiberedPushforwardObj_eq
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B : C} (f : A ⟶ B) (x : G) (hx : q.obj x = A) :
    q.obj (cofiberedPushforwardObj hq f x hx) = B := by
  let := cofiberedPushforwardMap_lift hq f x hx
  exact IsHomLift.codomain_eq q f (cofiberedPushforwardMap hq f x hx)

/-- The chosen pushforward arrow is strongly cocartesian over the given morphism of the base. -/
theorem cofibered_pushforward_isCocartesian
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B : C} (f : A ⟶ B) (x : G) (hx : q.obj x = A) :
    q.IsStronglyCocartesian f (cofiberedPushforwardMap hq f x hx) :=
  isStronglyCocartesian_of_isCofiberedInGroupoids hq f (cofiberedPushforwardMap hq f x hx)
    (cofiberedPushforwardMap_lift hq f x hx)

/-- The arrow out of a chosen pushforward induced, by the cocartesian property, from an arrow lying
over a composite. -/
noncomputable def cofiberedPushforwardDesc
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (x z : G)
    (hx : q.obj x = A) (ψ : x ⟶ z) (hψ : q.IsHomLift (f ≫ g) ψ) :
    cofiberedPushforwardObj hq f x hx ⟶ z := by
  letI := cofiberedPushforwardMap_lift hq f x hx
  letI := cofibered_pushforward_isCocartesian hq f x hx
  letI := hψ
  exact Functor.IsStronglyCocartesian.map q f (cofiberedPushforwardMap hq f x hx)
    (g := g) (f' := f ≫ g) rfl ψ

/-- The induced arrow out of a chosen pushforward lies over the second factor of the composite. -/
theorem cofiberedPushforwardDesc_lift
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (x z : G)
    (hx : q.obj x = A) (ψ : x ⟶ z) (hψ : q.IsHomLift (f ≫ g) ψ) :
    q.IsHomLift g (cofiberedPushforwardDesc hq f g x z hx ψ hψ) := by
  let := cofibered_pushforward_isCocartesian hq f x hx
  let := hψ
  change q.IsHomLift g
    (Functor.IsStronglyCocartesian.map q f (cofiberedPushforwardMap hq f x hx)
      (g := g) (f' := f ≫ g) rfl ψ)
  infer_instance

/-- The induced arrow out of a chosen pushforward recovers the given arrow after composing with the
pushforward arrow. -/
theorem cofiberedPushforwardDesc_fac
    {C : Type u} [Category.{v} C] {G : Type uF} [Category.{vF} G]
    {q : G ⥤ C} (hq : IsCofiberedInGroupoids q)
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (x z : G)
    (hx : q.obj x = A) (ψ : x ⟶ z) (hψ : q.IsHomLift (f ≫ g) ψ) :
    cofiberedPushforwardMap hq f x hx ≫
      cofiberedPushforwardDesc hq f g x z hx ψ hψ = ψ := by
  let := cofibered_pushforward_isCocartesian hq f x hx
  let := hψ
  exact Functor.IsStronglyCocartesian.fac q f (cofiberedPushforwardMap hq f x hx)
    (g := g) (f' := f ≫ g) rfl ψ

end

end Deformation

end
