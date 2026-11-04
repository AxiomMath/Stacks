module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAlgebraicFromCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSitePresheafCanonicalModel

/-!
# The Hilbert functor is an algebraic space (Stacks 0D01)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` which is of finite
presentation and separated. Then `Hilb_{X/B}` is an algebraic space locally of finite
presentation over `B`. Here `Hilb_{X/B} = Quot_{𝒪_X/X/B}` over `B` (Stacks 0D00), and
`Quot_{𝒪_X/X/B}` is an algebraic space locally of finite presentation over `B` by Stacks 09TU for
the finitely presented module `𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.exists_hilbertPresheafModel_isAlgebraicSpace_of_isSeparated`: for `f`
  of finite presentation and separated, `Hilb_{X/Y}` is an algebraic space locally of finite
  presentation over `Y`.

## Implementation notes

As in `AlgebraicGeometry.Space.exists_hilbertPresheafModel_isAlgebraicSpace`, the conclusion is
about an `AlgebraicGeometry.Space.HilbertPresheafModel`: the Hilbert presheaf takes values one
universe above the sections of an algebraic space, and a model is a presheaf in the universe of
the site whose universe lift is the Hilbert presheaf, exactly as in Stacks 0CZY.

## References

* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S`. If `f` is of
finite presentation and separated, then the Hilbert functor `Hilb_{X/Y}` of Stacks 0CZY is an
algebraic space locally of finite presentation over `Y`: it has a model in the universe of the
site which is an algebraic space whose canonical morphism to `Y` is locally of finite
presentation. -/
@[stacks 0D01]
theorem exists_hilbertPresheafModel_isAlgebraicSpace_of_isSeparated
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfp : IsFinitePresentation B S hS f.hom) (hsep : IsSeparated B S hS f.hom) :
    ∃ M : HilbertPresheafModel f,
      IsAlgebraicSpace B S hS M.presheaf ∧ IsLocallyOfFinitePresentation B S hS M.toBase := by
  obtain ⟨e, he⟩ := exists_hilbertPresheafIso_quotSitePresheaf f hfp
  obtain ⟨halg, hlfp⟩ :=
    (structureSheafQuotSituation f hfp).isLocallyOfFinitePresentation_toBase_of_isSeparated hsep
      SheafOfModules.isFinitePresentationOnSite_unit
      (structureSheafQuotSituation f hfp).quotSitePresheafModel
  exact exists_hilbertPresheafModel_isAlgebraicSpace (structureSheafQuotSituation f hfp) f hfp hsep
    _ halg hlfp e he

end AlgebraicGeometry.Space

end
