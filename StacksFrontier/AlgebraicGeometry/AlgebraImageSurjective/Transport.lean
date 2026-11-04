module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Transporting surjectivity and local surjectivity along a factorisation

`CategoryTheory.Limits.image` is reached through `Classical.choice`: the field
`CategoryTheory.Limits.HasImage.exists_image` is a `Nonempty`, so the chosen image of a morphism
is *not* definitionally the image that any particular construction builds, even when that
construction is the one supplying the instance.  Every statement about the corestriction
`CategoryTheory.Limits.factorThruImage` therefore has to be transported from the explicit
factorisation along an isomorphism, and this file is the three transports that are needed:
elementwise surjectivity in a concrete category, and local surjectivity of a morphism of
presheaves and of sheaves.

All three have the same shape.  A property `P` of morphisms which is stable under composition
and holds of every isomorphism is transported along `CategoryTheory.Limits.IsImage.isoExt`,
whose defining property `CategoryTheory.Limits.IsImage.e_isoExt_hom` says exactly that the
corestriction to the explicit image, followed by the comparison isomorphism, *is* the
corestriction to the chosen image.

## Main results

* `Stacks.AlgebraImageSurjective.surjective_of_fac`: `u ≫ a = v` with `u` and `a` surjective
  makes `v` surjective, and `Stacks.AlgebraImageSurjective.surjective_of_fac_of_isIso`, the case
  of an isomorphism `a`.
* `Stacks.AlgebraImageSurjective.surjective_factorThruImage`: if some explicit image
  factorisation has surjective corestriction, so does `CategoryTheory.Limits.factorThruImage`.
* `Stacks.AlgebraImageSurjective.isLocallySurjective_of_fac` and
  `Stacks.AlgebraImageSurjective.sheaf_isLocallySurjective_of_fac`: the same transport for local
  surjectivity of presheaves and of sheaves.

## Implementation notes

`CategoryTheory.Limits.IsImage.e_isoExt_hom` concludes about `(Image.monoFactorisation f).e`,
which is `CategoryTheory.Limits.factorThruImage f` by definition but not syntactically.  The
identity is therefore introduced with an explicit type ascription and `IsImage.e_isoExt_hom _ _`
as the term: `rw` does not find the pattern `(Image.monoFactorisation f).e` in a
goal written with `factorThruImage f`, while term elaboration identifies the two at default
transparency without complaint.

`surjective_of_fac` takes surjectivity of `a` as an *explicit hypothesis*, and
`surjective_of_fac_of_isIso` -- which supplies it from `IsIso a` -- is a separate lemma rather
than the only form.  This is not redundancy.  With `[IsIso a]` as an
instance argument the lemma is unusable at the spelling that
`StacksFrontier/AlgebraicGeometry/AlgebraImageSurjective/CommRing.lean` needs, namely `a` the
component at an object of the `hom` of an isomorphism of functors: instance search reports
`failed to synthesize IsIso (... .hom.app j)` at the application, while a `haveI` of *that very
instance*, stated by hand immediately above it, succeeds.  So the instance exists
(`CategoryTheory.NatIso.isIso_app_of_isIso` over `CategoryTheory.Iso.isIso_hom`) and is found
when the expected type is given, but is not found when it has to be discovered from the
instance argument of the application.  Passing `Function.Surjective a` explicitly, obtained at
the call site through `CategoryTheory.ConcreteCategory.bijective_of_isIso` against a stated
expected type, goes through.

The two local-surjectivity transports are one-liners from the composition instances
`CategoryTheory.Presheaf.isLocallySurjective_comp` and
`CategoryTheory.Sheaf.isLocallySurjective_comp`; they are stated as named lemmas because the
rewriting step (`h ▸`) is what fails to fire inside an `infer_instance` at the use sites.  Their
two local-surjectivity premises are explicit hypotheses rather than instance arguments, for the
same reason as in `surjective_of_fac`: at the use sites one of the two morphisms is the `hom` of
an isomorphism produced by `CategoryTheory.Limits.IsImage.isoExt`, and an instance argument
asked to discover that is not reliable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w₂ v' u' v u

namespace Stacks.AlgebraImageSurjective

section Concrete

variable {C : Type u} [Category.{v} C] {FC : C → C → Type w₂} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- **Surjectivity transports along a factorisation.**  If `u ≫ a = v` in a concrete category
and both `u` and `a` are surjective on elements, then so is `v`. -/
theorem surjective_of_fac {X Y Z : C} {u : X ⟶ Y} {a : Y ⟶ Z} {v : X ⟶ Z}
    (h : u ≫ a = v) (hu : Function.Surjective u) (ha : Function.Surjective a) :
    Function.Surjective v := fun y => by
  obtain ⟨z, hz⟩ := ha y
  obtain ⟨x, hx⟩ := hu z
  exact ⟨x, by rw [← ConcreteCategory.congr_hom h x, CategoryTheory.comp_apply, hx, hz]⟩

/-- **Surjectivity transports along an isomorphism on the right.**  The case of
`surjective_of_fac` in which `a` is an isomorphism, so that its surjectivity is automatic. -/
theorem surjective_of_fac_of_isIso {X Y Z : C} {u : X ⟶ Y} {a : Y ⟶ Z} {v : X ⟶ Z} [IsIso a]
    (h : u ≫ a = v) (hu : Function.Surjective u) : Function.Surjective v :=
  surjective_of_fac h hu (ConcreteCategory.bijective_of_isIso a).2

/-- **If some explicit image factorisation of `f` has surjective corestriction, then so does the
corestriction to the chosen image.**  The two differ by
`CategoryTheory.Limits.IsImage.isoExt`. -/
theorem surjective_factorThruImage {X Y : C} {f : X ⟶ Y} [HasImage f]
    {F' : MonoFactorisation f} (hF' : IsImage F') (he : Function.Surjective F'.e) :
    Function.Surjective (factorThruImage f) :=
  have h : F'.e ≫ (IsImage.isoExt hF' (Image.isImage f)).hom = factorThruImage f :=
    IsImage.e_isoExt_hom _ _
  surjective_of_fac_of_isIso h he

end Concrete

section Sites

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type w₂} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]

/-- **Local surjectivity of a morphism of presheaves transports along a factorisation.** -/
theorem isLocallySurjective_of_fac {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {u : F₁ ⟶ F₂} {a : F₂ ⟶ F₃}
    {v : F₁ ⟶ F₃} (h : u ≫ a = v) (hu : Presheaf.IsLocallySurjective J u)
    (ha : Presheaf.IsLocallySurjective J a) : Presheaf.IsLocallySurjective J v :=
  have := hu
  have := ha
  h ▸ Presheaf.isLocallySurjective_comp J u a

/-- **Local surjectivity of a morphism of sheaves transports along a factorisation.** -/
theorem sheaf_isLocallySurjective_of_fac {F₁ F₂ F₃ : Sheaf J A} {u : F₁ ⟶ F₂} {a : F₂ ⟶ F₃}
    {v : F₁ ⟶ F₃} (h : u ≫ a = v) (hu : Sheaf.IsLocallySurjective u)
    (ha : Sheaf.IsLocallySurjective a) : Sheaf.IsLocallySurjective v :=
  have := hu
  have := ha
  h ▸ Sheaf.isLocallySurjective_comp u a

end Sites

end Stacks.AlgebraImageSurjective
