module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits

/-!
# A morphism out of a coproduct of schemes is étale when its components are

## Main results

* `AlgebraicGeometry.etale_isZariskiLocalAtSource`: being étale is Zariski-local at the source.
* `AlgebraicGeometry.etale_coprod`: `coprod.desc f g` is étale as soon as `f` and `g` are.

## Implementation notes

Being étale has the ring-homomorphism property
`AlgebraicGeometry.HasRingHomProperty`, hence is Zariski-local at the source, and the two
coprojections of a binary coproduct of schemes form an open cover
(`AlgebraicGeometry.coprodOpenCover`); on each member the restriction of `coprod.desc f g` is
one of `f`, `g`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Being étale is Zariski-local at the source. -/
instance etale_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

/-- A morphism out of a binary coproduct of schemes is étale as soon as both of its components
are. -/
theorem etale_coprod {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (hf : Etale f)
    (hg : Etale g) : Etale (coprod.desc f g) := by
  have : Etale f := hf
  have : Etale g := hg
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (coprodOpenCover.{u, u} A B)]
  intro i
  cases i with
  | inl a =>
    cases a
    change Etale (coprod.inl ≫ coprod.desc f g)
    rw [coprod.inl_desc]
    exact inferInstance
  | inr b =>
    cases b
    change Etale (coprod.inr ≫ coprod.desc f g)
    rw [coprod.inr_desc]
    exact inferInstance

end AlgebraicGeometry

end
