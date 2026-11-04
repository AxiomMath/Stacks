module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.InducedProperty
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom

/-!
# Detecting an étale-local property on morphisms of germs of schemes

A property of morphisms of schemes which is étale local on the source and target holds for a
morphism exactly when the induced morphism of germs has the associated property at every point
of the source.

## Main definitions

No new definitions are introduced. The morphism of germs induced by a morphism of schemes at
a point of its source is `AlgebraicGeometry.MorphismOfGerms.ofSchemeHom` of
`StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom`.

## Main results

* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_forall_hasRepresentativeWithProperty`:
  **Stacks 04R7**.

## Implementation notes

The induced morphism of germs is represented on the whole source scheme, regarded as its top
open subset through `AlgebraicGeometry.Scheme.topIso`. The associated property of morphisms of
germs is the one of Tag 04R6, requiring a representative with the original property.

The forward direction restricts the given morphism along that top open subset. The converse
uses the étale-neighbourhood field of Tag 04QZ: a representative of the induced germ morphism
with the property agrees with the given morphism on an open neighbourhood of the point, and
that neighbourhood, with the identity of the target, is the required étale square.

## References

* [Stacks Project, Tag 04R7](https://stacks.math.columbia.edu/tag/04R7)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- A property of morphisms of schemes which is étale local on the source and target holds for
a morphism exactly when the associated property of morphisms of germs holds for every induced
morphism of germs. -/
@[stacks 04R7]
theorem IsEtaleLocalOnSourceAndTarget.iff_forall_hasRepresentativeWithProperty
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∀ x : X, MorphismOfGerms.HasRepresentativeWithProperty P
      (MorphismOfGerms.ofSchemeHom f x) := by
  refine ⟨fun hf x => ⟨⟨⊤, (by simp), X.topIso.hom ≫ f, (by change f x = f x; rfl)⟩,
    rfl, hP.precomp.precomp X.topIso.hom inferInstance f hf⟩, fun hq => ?_⟩
  refine (hP.iff_forall_exists_etale_neighborhood f).mpr fun x => ?_
  obtain ⟨g, hg, hPg⟩ := hq x
  obtain ⟨W, hxW, hWg, hW₀, hAgree⟩ := MorphismOfGerms.mk_eq_mk_iff.mp hg
  exact ⟨W.toScheme, Y, W.ι, 𝟙 Y, X.homOfLE hWg ≫ g.hom, ⟨x, hxW⟩, inferInstance, inferInstance,
    (by simp), (by simpa [Category.assoc] using hAgree),
    hP.precomp.precomp (X.homOfLE hWg) inferInstance g.hom hPg⟩

end AlgebraicGeometry

end
