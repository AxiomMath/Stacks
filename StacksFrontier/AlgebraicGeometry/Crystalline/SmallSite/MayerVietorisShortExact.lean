module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Cohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.MayerVietorisCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris

/-!
# The Mayer--Vietoris sequence of an open covering on the small crystalline site

Let `X = X' ∪ X''` be an open covering, `X''' = X' ∩ X''`, and `(U, T, δ)` an object of
`Cris(X/S)`. For an injective abelian sheaf `I` on `Cris(X/S)` the Mayer--Vietoris sequence of
sections over the restrictions of `(U, T, δ)`

`0 ⟶ I(U, T, δ) ⟶ I' ⊕ I'' ⟶ I''' ⟶ 0`

is short exact. Exactness on the left and in the middle is the sheaf condition for the covering
pair, `...CrystallineThickening.isPullback_sections_openCoverSquare`; surjectivity on the right
holds because the left edge `A|_{X'''} ⟶ A|_{X'}` of the square is a monomorphism of `Cris(X/S)`,
and restriction of sections of an injective abelian sheaf along a monomorphism of a site is
surjective.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.openCoverShortComplex`:
  the Mayer--Vietoris short complex `F(U, T, δ) ⟶ F' ⊕ F'' ⟶ F'''` of sections of an abelian
  sheaf over the square of an open covering.

## Main results

* `...CrystallineThickening.mono_restrictOpenLE`: the morphism between the restrictions of an
  object of `Cris(X/S)` to two nested opens of its ambient scheme is a monomorphism.
* `...CrystallineThickening.openCoverShortComplex_shortExact`: the Mayer--Vietoris sequence of
  an injective abelian sheaf is short exact.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 0EYK](https://stacks.math.columbia.edu/tag/0EYK)
* [Stacks Project, Tag 01D5](https://stacks.math.columbia.edu/tag/01D5)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}}

/-- **The morphism between the restrictions of an object of `Cris(X/S)` to two nested opens of its
ambient scheme is a monomorphism.** -/
instance mono_restrictOpenLE (A : CrystallineThickening S)
    {V V' : A.obj.thickening.target.scheme.Opens} (h : V ≤ V') : Mono (restrictOpenLE A h) :=
  (CrystallineThickening.ι S).mono_of_mono_map
    (inferInstanceAs (Mono (A.obj.restrictOpenLE h)))

/-- The left edge of the Mayer--Vietoris square of a pair of opens of `X` is a monomorphism. -/
instance mono_openCoverSquare_f₁₂ (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens) :
    Mono (openCoverSquare A V₁ V₂).f₁₂ :=
  inferInstanceAs (Mono
    (restrictOpenLE A (ambientOpen_le_ambientOpen A (inf_le_left : V₁ ⊓ V₂ ≤ V₁))))

/-- **The Mayer--Vietoris short complex of an open covering `X = X' ∪ X''` at an object
`(U, T, δ)` of `Cris(X/S)`**: the sections of an abelian sheaf `F` over `(U, T, δ)`, over the
restrictions to `X'` and `X''`, and over the restriction to `X''' = X' ∩ X''`, with the difference
of the two restriction maps as its second arrow. -/
def openCoverShortComplex (A : CrystallineThickening S) (V₁ V₂ : S.X.Opens)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : ShortComplex AddCommGrpCat.{u + 1} :=
  Stacks.EtaleCohomology.RelativeMayerVietoris.sectionShortComplex (smallTopology S)
    (openCoverSquare A V₁ V₂) F

/-- **The Mayer--Vietoris sequence of an injective abelian sheaf on `Cris(X/S)` for an open
covering `X = X' ∪ X''` is short exact**:

`0 ⟶ I(U, T, δ) ⟶ I' ⊕ I'' ⟶ I''' ⟶ 0`. -/
@[stacks 07ML "the Mayer-Vietoris sequence of the covering on Cris(X/S), short exact at an \
  injective sheaf, which is the form a derived functor consumes.  NOT the remark's triangle: \
  that is openCoverTriangle_distinguished of SmallSite/MayerVietorisTriangle.lean, at a fixed \
  object of the site, and identifying its terms with RGamma of the four sites is still open"]
theorem openCoverShortComplex_shortExact (A : CrystallineThickening S) {V₁ V₂ : S.X.Opens}
    (hV : V₁ ⊔ V₂ = ⊤) (I : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective I] :
    (openCoverShortComplex A V₁ V₂ I).ShortExact :=
  Stacks.EtaleCohomology.RelativeMayerVietoris.sectionShortComplex_shortExact
    (smallTopology S) (openCoverSquare A V₁ V₂) (isPullback_openCoverSquare A V₁ V₂)
    (ofTwoArrows_openCoverSquare_mem_smallTopology A hV) I

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
