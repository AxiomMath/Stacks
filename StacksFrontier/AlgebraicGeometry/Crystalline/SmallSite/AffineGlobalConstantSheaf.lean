module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalConnected
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineSubsiteCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChaoticSubsite
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.FinalFunctor

/-!
# Lower shriek carries the constant sheaf of the chaotic subsite to the constant sheaf

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] with `X` and `S`
affine, and let `u = wholeToAffineSubsite : 𝒞 ⥤ AffineCris(X/S)` be the inclusion of the chaotic
subsite of thickenings of the whole space.

`SmallSite.final_wholeToAffineSubsite` says that `u` is final — its comma categories
`I^u_{(U,T,δ)}` are nonempty and connected — which is step 3 of the proof of [Stacks, Tag 07JK].
This file reads off the consequence that step 5 of that proof consumes: the comparison of
constant abelian sheaves

`g_! ℤ_𝒞 ≅ ℤ_{AffineCris(X/S)}`.

The chaotic subsite has **no terminal object** (see `AffineGlobalLimits`), so every route to this
comparison that passes through one is closed; the terminal-object-free route is
`Stacks.ConstantSheaf.constantSheafCompSheafPullbackIsoOfFinal`, which asks exactly for finality.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.instIsContinuousWholeToAffineSubsite` — the
  inclusion `𝒞 ⥤ AffineCris(X/S)` is continuous for the chaotic topology on `𝒞`, so restriction
  along it carries abelian sheaves on `AffineCris(X/S)` to abelian sheaves on `𝒞`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.constantSheafCompLowerShriekIso` —
  **`C_𝒞 ⋙ g_! ≅ C_{AffineCris(X/S)}`**, naturally in the coefficient group.
* `Crystalline.GlobalCrystallineSituation.SmallSite.lowerShriekConstantSheafIntegerIso` —
  **`g_! ℤ_𝒞 ≅ ℤ_{AffineCris(X/S)}`**, the single isomorphism which is the datum `e` of
  `Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic`.

## What is and is not proved

No tag attribute is placed in this file.  [Stacks, Tag 07JK] is a statement about *cohomology*
and what is proved here is one of the inputs of its proof, not the tag; the isomorphism below is
moreover the degree-zero case of 07JK's own conclusion, so it could not carry that tag even as a
hypothesis of something else.

[Stacks, Tag 07JK] is **not** proved.  What remains of its proof is its step 5: with `f` the
morphism of topoi that finality provides, one has `f_* F = F|_𝒞` and must show
`R^p f_* F = 0` for `p > 0` and locally quasi-coherent `F`, which the source reduces, by
Cohomology on Sites, Lemma 21.7.4, to the vanishing of `H^p` over an object of
`AffineCris(X/S)` — that is [Stacks, Tag 07JJ].  Two things are missing for that: the
localisation of the small crystalline site at an object, which the library does not construct
(only the big-site `Thickening.restrictOpenOverFunctor` exists), and 07JJ itself, of which the
library has only the fragment `SmallSite.isZero_cohomology_restriction_of_isAffine`.

The alternative route through `Stacks.Cohomology.BiggerSiteGlobal.
sheafCohomologyIsoOfConstantSheafIsoOfAcyclic` — the Čech acyclicity of the restriction of an
injective sheaf, [Stacks, Tag 0D6X] — is *not* the source's and is strictly harder here: it would
prove the comparison for every abelian sheaf, whereas 07JK asserts it only for locally
quasi-coherent modules, and it additionally asks for
`PreservesFiniteColimits` of the restriction to `𝒞`, which is not available (restriction to a
subsite with the chaotic topology is not right exact in general, the sheafification of a
presheaf cokernel differing from the cokernel on the objects of `𝒞`).

## References

* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- **The inclusion `𝒞 ⥤ AffineCris(X/S)` is continuous** for the chaotic topology on `𝒞`, so
restriction along it carries abelian sheaves on `AffineCris(X/S)` to abelian sheaves on `𝒞`.  On
the chaotic topology only the maximal sieve covers, so there is nothing to check.

This is `instIsContinuousWholeι` for the inclusion into the affine subsite rather than into the
whole of `Cris(X/S)`. -/
instance instIsContinuousWholeToAffineSubsite :
    (wholeToAffineSubsite (S := S)).IsContinuous (chaoticTopology S) (affineTopology S) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _ rfl

include hp in
/-- **Lower shriek along the inclusion of the chaotic subsite carries the constant abelian sheaf
to the constant abelian sheaf**: `C_𝒞 ⋙ g_! ≅ C_{AffineCris(X/S)}`, naturally in the coefficient
group.

The inclusion `u` is continuous and, by `SmallSite.final_wholeToAffineSubsite`, final; that is
exactly the hypothesis of `Stacks.ConstantSheaf.constantSheafCompSheafPullbackIsoOfFinal`.  No
terminal object of `𝒞` is used, and `𝒞` has none. -/
def constantSheafCompLowerShriekIso :
    constantSheaf (chaoticTopology S) AddCommGrpCat.{u + 1} ⋙
        (wholeToAffineSubsite (S := S)).sheafPullback AddCommGrpCat.{u + 1}
          (chaoticTopology S) (affineTopology S) ≅
      constantSheaf (affineTopology S) AddCommGrpCat.{u + 1} :=
  haveI := SmallSite.final_wholeToAffineSubsite hp
  Stacks.ConstantSheaf.constantSheafCompSheafPullbackIsoOfFinal
    (wholeToAffineSubsite (S := S)) (chaoticTopology S) (affineTopology S)
    AddCommGrpCat.{u + 1}

include hp in
/-- **`g_! ℤ_𝒞 ≅ ℤ_{AffineCris(X/S)}`.**  This is `constantSheafCompLowerShriekIso` at the
coefficient group `ℤ`, which is the datum `e` of
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic` and the
degree-zero content of the comparison asserted by [Stacks, Tag 07JK]. -/
def lowerShriekConstantSheafIntegerIso :
    ((wholeToAffineSubsite (S := S)).sheafPullback AddCommGrpCat.{u + 1}
        (chaoticTopology S) (affineTopology S)).obj
        ((constantSheaf (chaoticTopology S) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅
      (constantSheaf (affineTopology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (constantSheafCompLowerShriekIso hp).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
