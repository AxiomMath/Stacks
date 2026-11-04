module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Colimit
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalEssSurj
public import StacksFrontier.CategoryTheory.Limits.Finite.Nonempty

/-!
# Nonempty finite limits in the chaotic subsite of thickenings of an affine space

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine.  The chaotic
subsite `𝒞 ⊆ Cris(X/S)` of [Stacks, Tag 07JK] is anti-equivalent to the little affine crystalline
category `Cris(Γ(X, ⊤)/Γ(S, ⊤))` of [Stacks, Tag 07HM], by
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`.  That category has all
nonempty finite *colimits* ([Stacks, Tag 07HN], formalized as
`Crystalline.DividedPowerThickening.instHasNonemptyFiniteColimits`), so `𝒞` has all nonempty
finite *limits*; in particular it has binary products and equalizers.

## Main results

* `Crystalline.GlobalCrystallineSituation.wholeSpaceOpEquivLittleAffineOp` — the equivalence
  `𝒞 ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))ᵒᵖ` obtained from the bridge by taking opposites.
* **`Crystalline.GlobalCrystallineSituation.hasNonemptyFiniteLimits_wholeSpaceThickening`** — the
  chaotic subsite `𝒞` has all nonempty finite limits.
* `Crystalline.GlobalCrystallineSituation.hasBinaryProducts_wholeSpaceThickening` and
  `Crystalline.GlobalCrystallineSituation.hasEqualizers_wholeSpaceThickening` — in particular it
  has binary products and equalizers.

## What is and is not proved

No tag attribute is placed in this file.  **This is not [Stacks, Tag 07I9]**, which asserts that
the whole of `CRIS(X/S)` has nonempty finite limits for an arbitrary global crystalline
situation.  What is proved here is the restriction of that statement to the chaotic subsite `𝒞`
of thickenings of the whole space, and only when `X` and `S` are affine — strictly weaker on both
counts, so tagging it 07I9 would misstate the source.

`𝒞` has **no terminal object** supplied here, and none is expected: a weakly terminal object of
`𝒞` would be a weakly initial object of `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, and the generator of
[Stacks, Tag 07KI] is an object of the *completed* category `Cris^∧(Γ(X, ⊤)/Γ(S, ⊤))` — the
divided power envelope of a polynomial presentation, in which `p` is not nilpotent — so it is not
an object of `Cris(Γ(X, ⊤)/Γ(S, ⊤))` at all.  This is why
`Stacks.Cohomology.nonempty_addEquiv_sheafH_homology_powerCechComplex` ([Stacks, Tag 07JM]),
which needs a weakly terminal object, does not apply to `𝒞` directly.

## References

* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- **The chaotic subsite `𝒞` is equivalent to the opposite of the little affine crystalline
category.**  This is the equivalence `Crystalline.GlobalCrystallineSituation.
wholeSiteEquivLittleAffine` read in the other direction: `𝒞ᵒᵖ ≌ Cris(C/A)` gives
`𝒞 ≌ Cris(C/A)ᵒᵖ`. -/
def wholeSpaceOpEquivLittleAffineOp :
    SmallSite.WholeSpaceThickening S ≌ (affineIsCrystalline hp).FullSubcategoryᵒᵖ :=
  (opOpEquivalence (SmallSite.WholeSpaceThickening S)).symm.trans
    (wholeSiteEquivLittleAffine hp).op

include hp in
/-- **The chaotic subsite `𝒞` of thickenings of the whole of an affine `X` over an affine base has
all nonempty finite limits.**  It is anti-equivalent to the little affine crystalline category
`Cris(Γ(X, ⊤)/Γ(S, ⊤))`, which has all nonempty finite colimits by [Stacks, Tag 07HN]. -/
theorem hasNonemptyFiniteLimits_wholeSpaceThickening :
    HasNonemptyFiniteLimits (SmallSite.WholeSpaceThickening S) := by
  refine ⟨fun J _ _ _ => ?_⟩
  have h1 : HasColimitsOfShape Jᵒᵖ (affineIsCrystalline hp).FullSubcategory :=
    HasNonemptyFiniteColimits.out Jᵒᵖ
  have h2 : HasLimitsOfShape J (affineIsCrystalline hp).FullSubcategoryᵒᵖ :=
    hasLimitsOfShape_op_of_hasColimitsOfShape
  exact Adjunction.hasLimitsOfShape_of_equivalence
    (wholeSpaceOpEquivLittleAffineOp hp).functor

include hp in
/-- **The chaotic subsite `𝒞` has binary products.** -/
theorem hasBinaryProducts_wholeSpaceThickening :
    HasBinaryProducts (SmallSite.WholeSpaceThickening S) :=
  have := hasNonemptyFiniteLimits_wholeSpaceThickening hp
  hasBinaryProducts_of_hasNonemptyFiniteLimits _

include hp in
/-- **The chaotic subsite `𝒞` has equalizers.** -/
theorem hasEqualizers_wholeSpaceThickening :
    HasEqualizers (SmallSite.WholeSpaceThickening S) :=
  have := hasNonemptyFiniteLimits_wholeSpaceThickening hp
  hasEqualizers_of_hasNonemptyFiniteLimits _

end Crystalline.GlobalCrystallineSituation

end

end
