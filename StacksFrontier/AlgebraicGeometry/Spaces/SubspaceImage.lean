module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Subfunctor.Image
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Images of subfunctors along a monomorphism

Mathlib's `CategoryTheory.Subfunctor.image` is the pointwise image, so for a monomorphism
`f : F ⟶ F'` of type-valued functors the image of a subfunctor `Z` of `F` is a faithful copy of
`Z` inside `F'`. This file records the comparison morphism `Z.toFunctor ⟶ (Z.image f).toFunctor`
as a morphism with a body — the factorization of `Z.ι ≫ f` through its range, which is the image
— and proves that it is an isomorphism when `f` is a monomorphism, so that properties of
`Z.ι ≫ f` transport to the inclusion of the image.

Alongside it are the two compatibilities an image subfunctor has with inverse images: the
Beck–Chevalley equality saying that image and inverse image commute across a cartesian square,
and the fact that taking the image along a monomorphism is injective on subfunctors.

## Main definitions

* `CategoryTheory.Subfunctor.toImage` is the comparison morphism from a subfunctor to its image.

## Main results

* `CategoryTheory.Subfunctor.image_eq_range`: the image of `Z` along `f` is the range of `Z.ι ≫ f`.
* `CategoryTheory.Subfunctor.isIso_toImage`: the comparison is an isomorphism for `f` a
  monomorphism.
* `CategoryTheory.Subfunctor.image_preimage_of_isPullback`: image and inverse image commute
  across a cartesian square.
* `CategoryTheory.Subfunctor.image_injective_of_mono`: taking images along a monomorphism is
  injective.
* `CategoryTheory.Subfunctor.factorsThrough_iff_le_range`: a subfunctor's inclusion factors
  through a monomorphism exactly when the subfunctor is contained in its range.

## Implementation notes

The comparison morphism is `CategoryTheory.Subfunctor.lift` of `Z.ι ≫ f`, available because the
range of `Z.ι ≫ f` is the image of `Z`; it is therefore a construction rather than a choice of an
isomorphism from an existence statement, and `CategoryTheory.Subfunctor.toImage_ι` holds by
definition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F F' : C ⥤ Type w}

/-- The image of a subfunctor along a morphism is the range of the composite of its inclusion
with that morphism. -/
theorem image_eq_range (Z : Subfunctor F) (f : F ⟶ F') :
    Z.image f = Subfunctor.range (Z.ι ≫ f) := by
  rw [range_comp, range_ι]

/-- The comparison morphism from a subfunctor to its image along a morphism: the factorization
of `Z.ι ≫ f` through the image, which contains its range. -/
def toImage (Z : Subfunctor F) (f : F ⟶ F') : Z.toFunctor ⟶ (Z.image f).toFunctor :=
  Subfunctor.lift (Z.ι ≫ f) (image_eq_range Z f).ge

/-- The comparison morphism to the image followed by the inclusion of the image is the inclusion
of the subfunctor followed by the morphism. -/
@[reassoc (attr := simp)]
theorem toImage_ι (Z : Subfunctor F) (f : F ⟶ F') :
    Z.toImage f ≫ (Z.image f).ι = Z.ι ≫ f := rfl

/-- The comparison morphism from a subfunctor to its image along a monomorphism is an
isomorphism. -/
instance isIso_toImage (Z : Subfunctor F) (f : F ⟶ F') [Mono f] : IsIso (Z.toImage f) := by
  have hm : Mono (Z.toImage f) := by
    have : Mono (Z.ι ≫ f) := mono_comp _ _
    exact mono_of_mono_fac (Z.toImage_ι f)
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hm i), ?_⟩
  rintro ⟨z, x, hx, hxz⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩

/-- **Beck–Chevalley for subfunctors.** Across a cartesian square of type-valued functors,
taking the image along one pair of parallel edges agrees with taking the inverse image along
the other: the pointwise statement is that a section of the bottom right corner lying in the
image of the subfunctor comes from the corner of the square. -/
theorem image_preimage_of_isPullback {A A' D E : C ⥤ Type w}
    {a : A ⟶ A'} {b : A ⟶ D} {c : A' ⟶ E} {d : D ⟶ E}
    (sq : IsPullback a b c d) (Z : Subfunctor A') :
    (Z.preimage a).image b = (Z.image c).preimage d := by
  ext T z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨a.app T x, hx, types_congr_hom (congr_app sq.w T) x⟩
  · rintro ⟨y, hy, h⟩
    obtain ⟨x, hx, hz⟩ := Types.exists_of_isPullback (sq.map ((evaluation _ _).obj T)) y z h
    exact ⟨x, (hx ▸ hy : a.app T x ∈ Z.obj T), hz⟩

/-- Taking the image of a subfunctor along a monomorphism is injective: the pointwise image
along an injection determines its source. -/
theorem image_injective_of_mono (f : F ⟶ F') [Mono f] :
    Function.Injective (fun Z : Subfunctor F ↦ Z.image f) := fun _ _ h ↦
  Subfunctor.ext <| funext fun T ↦ Set.image_injective.mpr (injective_of_mono (f.app T))
    (congrArg (fun U : Subfunctor F' ↦ U.obj T) h)

/-- A subfunctor contained in the range of a morphism is the image of its inverse image. -/
theorem image_preimage_eq_of_le_range (Z : Subfunctor F') (f : F ⟶ F')
    (hZ : Z ≤ Subfunctor.range f) : (Z.preimage f).image f = Z := by
  ext T z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    obtain ⟨x, hx⟩ := hZ T hz
    exact ⟨x, by rwa [← hx] at hz, hx⟩

/-- For a monomorphism `f` and a subfunctor of its target contained in its range, the morphism
from the inverse image of that subfunctor to the subfunctor itself is an isomorphism. -/
theorem isIso_fromPreimage_of_le_range (Z : Subfunctor F') (f : F ⟶ F') [Mono f]
    (hZ : Z ≤ Subfunctor.range f) : IsIso (Z.fromPreimage f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨fun x y h ↦ Subtype.ext (injective_of_mono (f.app T) (congrArg Subtype.val h)),
    fun z ↦ ?_⟩
  obtain ⟨x, hx, hxz⟩ := (image_preimage_eq_of_le_range Z f hZ).ge T z.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩

/-- The inclusion of a subfunctor factors through a monomorphism into the ambient functor
exactly when the subfunctor is contained in the range of that monomorphism. -/
theorem factorsThrough_iff_le_range (Z : Subfunctor F') (f : F ⟶ F') [Mono f] :
    (∃ l : Z.toFunctor ⟶ F, l ≫ f = Z.ι) ↔ Z ≤ Subfunctor.range f := by
  constructor
  · rintro ⟨l, hl⟩ T z hz
    exact ⟨l.app T ⟨z, hz⟩, types_congr_hom (congr_app hl T) ⟨z, hz⟩⟩
  · intro hZ
    refine ⟨Subfunctor.homOfLe hZ ≫ inv (Subfunctor.toRange f), ?_⟩
    have hinv : inv (Subfunctor.toRange f) ≫ f = (Subfunctor.range f).ι := by
      apply (cancel_epi (Subfunctor.toRange f)).1
      simp
    simpa only [Category.assoc, hinv] using Subfunctor.homOfLe_ι hZ

/-- A morphism of the index category lies in a subfunctor of a representable functor exactly
when the morphism it represents factors through that subfunctor. -/
@[sga "3 IV 4.1.1" "special case"]
theorem mem_yoneda_iff {T T' : C} (W : Subfunctor (yoneda.obj T)) (g : T' ⟶ T) :
    g ∈ W.obj (Opposite.op T') ↔
      ∃ l : yoneda.obj T' ⟶ W.toFunctor, l ≫ W.ι = yoneda.map g := by
  constructor
  · intro hg
    have hr : Subfunctor.range (yoneda.map g) ≤ W := by
      rintro U x ⟨k, rfl⟩
      exact W.map k.op hg
    exact ⟨Subfunctor.lift _ hr, Subfunctor.lift_ι _ _⟩
  · rintro ⟨l, hl⟩
    have h1 : ((l.app (Opposite.op T')) (𝟙 T') : (yoneda.obj T).obj (Opposite.op T')) = g := by
      simpa using types_congr_hom (congr_app hl (Opposite.op T')) (𝟙 T')
    exact h1 ▸ (l.app (Opposite.op T') (𝟙 T')).2

end CategoryTheory.Subfunctor

end
