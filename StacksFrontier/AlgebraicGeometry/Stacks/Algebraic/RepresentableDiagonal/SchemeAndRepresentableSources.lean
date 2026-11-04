module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.MorphismRepresentableBySpaces.Basic
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Scheme-valued and representable sources test representability by algebraic spaces

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`. Two of the
eight equivalent conditions of Stacks 045G are

* (3) every 1-morphism to `𝒳` from the category fibred in groupoids represented by an object
  of the site is representable by algebraic spaces, and
* (5) every 1-morphism to `𝒳` from a *representable* category fibred in groupoids is
  representable by algebraic spaces.

The two are equivalent. One direction is the observation that a slice category is a
representable category fibred in groupoids, represented by the object it is sliced over. The
other is invariance of representability by algebraic spaces under equivalences (Stacks 0457):
a representable source is equivalent over the site to a slice, so a 1-morphism out of it fits
into a 2-commutative square whose other vertical arrow has a slice as its source.

## Main definitions

* `AlgebraicGeometry.schemeFibredCategory`: the category fibred in groupoids represented by an
  object of the big fppf site over `S`, namely the slice of the site over that object.
* `AlgebraicGeometry.IsRepresentableFromSchemes`: condition (3) of Stacks 045G.
* `AlgebraicGeometry.IsRepresentableFromRepresentableCategories`: condition (5) of
  Stacks 045G.

## Main results

* `AlgebraicGeometry.isRepresentableCFG_schemeFibredCategory`: a slice of the site is a
  representable category fibred in groupoids over the site.
* `AlgebraicGeometry.isRepresentableFromRepresentableCategories_of_isRepresentableFromSchemes`:
  condition (3) implies condition (5) for sources in *any* pair of universes.
* `AlgebraicGeometry.isRepresentableFromSchemes_iff_isRepresentableFromRepresentableCategories`:
  conditions (3) and (5) of Stacks 045G are equivalent.

## Implementation notes

The total category of `𝒳` is allowed object and hom universes independent of the site's, as in
`AlgebraicGeometry.IsRepresentableByAlgebraicSpaces`, and so is the source quantified over by
condition (5); its universe parameters are therefore explicit in
`AlgebraicGeometry.IsRepresentableFromRepresentableCategories`. The implication from (3) to (5)
holds for every choice of them, because Stacks 0457 as formalized allows the two sources of the
square independent universes. The reverse implication instantiates (5) at the site's own
universes, which is where the slice categories of condition (3) live; stated for a source in a
strictly larger universe it would require a universe lift of the slice, which changes the
category rather than the condition.

A representable category fibred in groupoids is one equivalent over the site to a slice in the
sense of `CategoryTheory.IsFibredEquivalence`
(`Stacks.RepresentableMorphism.IsRepresentableCFG`, Stacks 02Y3).
The quasi-inverse needed to build the square is not read off that structure directly but
obtained from `CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over` (Stacks 003Z),
which delivers the unit with its components already in the `IsHomLift` form that a based
natural transformation requires.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u v w v₁ w₁

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The category fibred in groupoids over the big fppf site of `S` represented by an object `U`
of that site: the slice of the site over `U`, with its forgetful functor. -/
public abbrev schemeFibredCategory (U : BigFppfOver B S hS) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor.{u, u + 1, u, u + 1} (Over.forget.{u, u + 1} U))
    (Functor.IsFiberedInGroupoids.over_forget.{u, u + 1} U)

/-- A slice of the big fppf site of `S` is a representable category fibred in groupoids over
that site, represented by the object it is sliced over: the identity functor is an equivalence
over the site between the slice and itself. -/
public theorem isRepresentableCFG_schemeFibredCategory (U : BigFppfOver B S hS) :
    Stacks.RepresentableMorphism.IsRepresentableCFG (schemeFibredCategory B S hS U).val.p := by
  have hid : IsCartesianFunctorStrict (Over.forget U) (Over.forget U) (𝟭 (Over U)) :=
    ⟨rfl, by intros; assumption⟩
  exact ⟨U, 𝟭 (Over U),
    { isCartesianFunctor := hid
      exists_inverse :=
        ⟨𝟭 (Over U), hid,
          ⟨Iso.refl _, fun _ => ⟨rfl, by simp⟩⟩, ⟨Iso.refl _, fun _ => ⟨rfl, by simp⟩⟩⟩ }⟩

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **Stacks 045G, condition (3).** Every 1-morphism to `𝒳` from the category fibred in
groupoids represented by an object of the big fppf site of `S` is representable by algebraic
spaces. -/
public abbrev IsRepresentableFromSchemes : Prop :=
  ∀ (U : BigFppfOver B S hS) (x : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val),
    IsRepresentableByAlgebraicSpaces B S hS x

/-- **Stacks 045G, condition (5).** Every 1-morphism to `𝒳` from a representable category
fibred in groupoids over the big fppf site of `S` is representable by algebraic spaces. The
source is allowed object and hom universes of its own. -/
public abbrev IsRepresentableFromRepresentableCategories : Prop :=
  ∀ 𝒯 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS),
    Stacks.RepresentableMorphism.IsRepresentableCFG 𝒯.val.p →
      ∀ x : 𝒯.val ⥤ᵇ 𝒳.val, IsRepresentableByAlgebraicSpaces B S hS x

/-- **Stacks 045G, (3) implies (5).** If every 1-morphism to `𝒳` out of a slice of the big fppf
site is representable by algebraic spaces, then so is every 1-morphism out of a representable
category fibred in groupoids, in any universes.

A representable source `𝒯` comes with an equivalence `E : 𝒯 ⥤ 𝒞/X` over the site; Stacks 003Z
supplies a quasi-inverse `F : 𝒞/X ⥤ 𝒯` over the site together with a unit `η : E ⋙ F ≅ 𝟭` whose
components are vertical. Whiskering `η` by the given `x : 𝒯 ⥤ᵇ 𝒳` makes the square with
verticals `F ⋙ x` and `x` and horizontals `E` and the identity 2-commutative, so Stacks 0457
transports representability of `F ⋙ x` — an instance of the hypothesis at `X` — to `x`. -/
public theorem isRepresentableFromRepresentableCategories_of_isRepresentableFromSchemes
    (h : IsRepresentableFromSchemes B S hS 𝒳) :
    IsRepresentableFromRepresentableCategories.{u, v, w, v₁, w₁} B S hS 𝒳 := by
  intro 𝒯 h𝒯 x
  obtain ⟨X, E, hE⟩ := h𝒯
  have hEequiv : E.IsEquivalence :=
    Stacks.RepresentableMorphism.SliceEquivalence.isEquivalence_of_isEquivalenceOver
      𝒯.val.p X E hE
  obtain ⟨F, hF, η, _, hη, _⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒯.val.p (Over.forget X)
      𝒯.isFiberedInGroupoids (Functor.IsFiberedInGroupoids.over_forget X) E
      hE.isCartesianFunctor.comm hEequiv
  let a : 𝒯.val ⥤ᵇ (schemeFibredCategory B S hS X).val :=
    { toFunctor := E, w := hE.isCartesianFunctor.comm }
  let g : (schemeFibredCategory B S hS X).val ⥤ᵇ 𝒯.val := { toFunctor := F, w := hF }
  have hae : Functor.IsEquivalence a.toFunctor := hEequiv
  have hbe : Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))
  let α : BasedFunctor.comp a (BasedFunctor.comp g x) ≅
      BasedFunctor.comp x (BasedFunctor.id 𝒳.val) :=
    BasedNatIso.mkNatIso (Functor.isoWhiskerRight η x.toFunctor) fun b => by
      have := hη b
      exact BasedFunctor.preserves_isHomLift x _ (η.hom.app b)
  exact (Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS x
    (BasedFunctor.comp g x) a (BasedFunctor.id 𝒳.val) α).1 (h X (BasedFunctor.comp g x))

/-- **Stacks 045G, (5) implies (3).** A slice of the big fppf site is a representable category
fibred in groupoids, so condition (5) applies to it. -/
public theorem isRepresentableFromSchemes_of_isRepresentableFromRepresentableCategories
    (h : IsRepresentableFromRepresentableCategories.{u, v, w, u, u + 1} B S hS 𝒳) :
    IsRepresentableFromSchemes B S hS 𝒳 := fun U x =>
  h (schemeFibredCategory B S hS U) (isRepresentableCFG_schemeFibredCategory B S hS U) x

/-- **Stacks 045G, conditions (3) and (5).** For a category fibred in groupoids `𝒳` over the big
fppf site of `S`, every 1-morphism to `𝒳` out of a slice of the site is representable by
algebraic spaces if and only if every 1-morphism to `𝒳` out of a representable category fibred
in groupoids is. -/
@[stacks 045G "parts (3) and (5)"]
public theorem isRepresentableFromSchemes_iff_isRepresentableFromRepresentableCategories :
    IsRepresentableFromSchemes B S hS 𝒳 ↔
      IsRepresentableFromRepresentableCategories.{u, v, w, u, u + 1} B S hS 𝒳 :=
  ⟨isRepresentableFromRepresentableCategories_of_isRepresentableFromSchemes B S hS 𝒳,
    isRepresentableFromSchemes_of_isRepresentableFromRepresentableCategories B S hS 𝒳⟩

end AlgebraicGeometry

end
