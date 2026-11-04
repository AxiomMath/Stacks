module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.Modification.InvertibleFiltration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso

/-!
# A section over an open extends when its image is affine over the base

Let `X` be an integral normal scheme, `p : P ⟶ X` a proper morphism, `U ⊆ X` a nonempty open and
`s : U ⟶ P` a section of `p` over `U`. If the scheme theoretic image of `s` is affine over `X`,
then `s` extends to a section of `p` over all of `X`.

The scheme theoretic image `X' = s.image` is proper and birational over `X`, so if it is also
affine over `X` it is finite over `X` ([Stacks, Tag 01WN]), hence an isomorphism onto `X` because
`X` is normal and integral ([Stacks, Tag 0AB1]). Inverting it produces the extension.

## Main results

* `AlgebraicGeometry.isIso_imageι_comp_of_isAffineHom`: the projection from the scheme theoretic
  image to the base is an isomorphism.
* `AlgebraicGeometry.exists_section_comp_eq_of_isAffineHom_imageι_comp`: the section extends, and
  the extension restricts to it on `U`.

## Implementation notes

This is one paragraph of the proof of [Stacks, Tag 0AXB]: there `P = 𝐏(ℰ)` for the extension `ℰ`
of `𝒪_X` by `𝒪_X` attached to a class in `H¹(X, 𝒪_X)`, `U = f⁻¹(V)` for `V` the punctured
spectrum of the base, `s = σ'` is the second section coming from a splitting over `U`, and the
affineness hypothesis holds when the image is disjoint from `σ(X)`, because
`𝐏(ℰ) ∖ σ(X) ⟶ X` is affine. The conclusion is then a contradiction: the extension of `σ'`
disjoint from `σ` would split the class, which was assumed nonzero.

Affineness cannot be dropped: a proper birational morphism onto a normal integral scheme is an
isomorphism only once it is also affine.

That the image is proper and birational over `X` is
`Stacks.Divisors.isModification_imageι_comp`, which holds for any section of a proper morphism
over a nonempty open of an integral scheme.

## References

* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 01WN](https://stacks.math.columbia.edu/tag/01WN)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 01R7](https://stacks.math.columbia.edu/tag/01R7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The projection from the scheme theoretic image of a section to the base is an isomorphism
when it is affine.** For `X` integral and normal, `p : P ⟶ X` proper and `s` a section of `p`
over a nonempty open `U ⊆ X`, the image of `s` is proper and birational over `X`; if it is affine
over `X` as well then it is finite over `X` ([Stacks, Tag 01WN]) and therefore an isomorphism
([Stacks, Tag 0AB1]). -/
theorem isIso_imageι_comp_of_isAffineHom {X P : Scheme.{u}} [IsIntegral X] [IsNormal X]
    (p : P ⟶ X) [IsProper p] (U : X.Opens) [Nonempty U] (s : U.toScheme ⟶ P)
    (hs : s ≫ p = U.ι) (haff : IsAffineHom (s.imageι ≫ p)) :
    IsIso (s.imageι ≫ p) := by
  have hmod : IsModification (s.imageι ≫ p) :=
    Stacks.Divisors.isModification_imageι_comp p U s hs
  have : IsIntegral s.image := hmod.source_isIntegral
  have : IsFinite (s.imageι ≫ p) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hmod.isProper, haff⟩
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal (s.imageι ≫ p) hmod.isBirational

/-- **A section over an open whose image is affine over the base extends to the whole base.** The
extension is the inverse of `isIso_imageι_comp_of_isAffineHom` followed by the closed immersion
of the scheme theoretic image, and it restricts to the given section on `U`. -/
theorem exists_section_comp_eq_of_isAffineHom_imageι_comp {X P : Scheme.{u}} [IsIntegral X]
    [IsNormal X] (p : P ⟶ X) [IsProper p] (U : X.Opens) [Nonempty U] (s : U.toScheme ⟶ P)
    (hs : s ≫ p = U.ι) (haff : IsAffineHom (s.imageι ≫ p)) :
    ∃ σ : X ⟶ P, σ ≫ p = 𝟙 X ∧ U.ι ≫ σ = s := by
  have := isIso_imageι_comp_of_isAffineHom p U s hs haff
  have hfac : s.toImage ≫ (s.imageι ≫ p) = U.ι := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hs]
  refine ⟨inv (s.imageι ≫ p) ≫ s.imageι, ?_, ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [← hfac, Category.assoc, IsIso.hom_inv_id_assoc, Scheme.Hom.toImage_imageι]

end AlgebraicGeometry

end
