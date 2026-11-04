module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete

/-!
# An algebraic space affine over a scheme is a scheme

Let `S` be a scheme in a big fppf site `B`, let `T` be an object of the site and let `F` be an
algebraic space over `S` with an **affine** morphism `π : F ⟶ T`, in the sense of Stacks 03WF.
Then `F` is representable by an object of the site, and `π` is an affine morphism of schemes.

This is the statement that lets the *scheme*-level theory be applied to a base change of an
algebraic space affine over an algebraic space `X` along an étale scheme chart of `X`: that base
change is affine over the chart's scheme, hence a scheme.

## Main results

* `AlgebraicGeometry.Space.exists_representing_over_of_isAffineHom`: an algebraic space with an
  affine morphism to a representable presheaf is representable, by an object of the site whose
  projection is an affine morphism of schemes.
* `AlgebraicGeometry.Space.isAffineHom_representing_over_of_isAffineHom`: the same with the
  representability discarded, as the affineness of the represented projection.

## Implementation notes

Both are
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`
— relative Tag 03JH with the containment hypothesis discharged — at the property
`AlgebraicGeometry.IsAffineHom` of morphisms of schemes.  Two inputs make that specialisation
immediate: affineness of a morphism of algebraic spaces *is* the general affine-base-change
pattern at Mathlib's `AlgebraicGeometry.IsAffineHom`
(`AlgebraicGeometry.Space.isAffineHom_iff_holdsOnAffineBaseChange`), and being an affine
morphism of schemes is Zariski local at the target
(`AlgebraicGeometry.Space.isZariskiLocalAtTarget_isAffineHom`).

No `stacks` attribute is carried.  Stacks 03WG is the equivalence of the five local criteria for
an affine morphism and is formalized as `AlgebraicGeometry.Space.isAffineHom_tfae`; the statement
here is the special case of its implication (2) ⇒ (1) in which the *target* is already
representable, so that relative representability of `π` becomes absolute representability of its
source.  Stacks 03WF is the definition of affineness being used, which
`AlgebraicGeometry.Space.IsAffineHom` already carries.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space affine over a scheme is a scheme.**  If `F` is an algebraic space over
`S` and `π : F ⟶ T` is an affine morphism to a representable presheaf, then `F` is isomorphic to
a representable presheaf by an isomorphism carrying `π` to a morphism `P` of the site, and
`P` is an affine morphism of schemes. -/
theorem exists_representing_over_of_isAffineHom
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (π : F ⟶ yoneda.obj T)
    (hπ : IsAffineHom B S hS π) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map P) :=
  exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS
    isZariskiLocalAtTarget_isAffineHom hF π
    ((isAffineHom_iff_holdsOnAffineBaseChange π).1 hπ)

/-- The represented projection of an algebraic space affine over a scheme is an affine morphism
of schemes.  This is `AlgebraicGeometry.Space.exists_representing_over_of_isAffineHom` with the
isomorphism named and the affineness read off it. -/
theorem isAffineHom_representing_over_of_isAffineHom
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (π : F ⟶ yoneda.obj T)
    (hπ : IsAffineHom B S hS π) :
    ∃ (Y : BigFppfOver B S hS) (P : Y ⟶ T),
      Nonempty (F ≅ yoneda.obj Y) ∧
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map P) := by
  obtain ⟨Y, e, P, _, hP⟩ := exists_representing_over_of_isAffineHom B S hS hF π hπ
  exact ⟨Y, P, ⟨e⟩, hP⟩

end AlgebraicGeometry.Space

end
