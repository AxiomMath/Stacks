module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreEtaleSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ShortExactExtension
import StacksCore.Tactic.StacksAttribute

/-!
# All eight assertions for torsion sheaves on curves pass to extensions

Let `k` be an algebraically closed field, let `X` be a separated scheme of finite type over `k`
whose underlying space has dimension at most one, and let `0 → F₁ → F → F₂ → 0` be a short exact
sequence of torsion abelian sheaves on the small étale site of `X`. Stacks Project Tag 0A5C
asserts that if the eight statements of Situation 0A52 hold for `F₁` and `F₂` then they hold for
`F`. The eight statements are the vanishing of `H^q(X, F)` above degree two, its vanishing above
degree one when `X` is affine and when `F` is torsion of characteristic-primary exponent, the
finiteness of `H^q(X, F)` for constructible `F` of torsion prime to the characteristic and for
constructible `F` on a proper `X`, the bijectivity of the restriction map
`H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` along an extension `k'/k` of algebraically closed fields
in those same two cases, and the surjectivity of `H²(X, F) → H²(U, F|_U)` for an open `U ⊆ X`.

This file assembles the eight into the single assertion the tag makes. The conjunction of the
eight is `Stacks.EtaleCohomology.CurveCohomologyStatements`, which is also what Tag 0A5D
transfers along a finite direct image; the eight transfers along a short exact sequence are the
eight theorems of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/ShortExactExtension.lean`.

## Main results

* `Stacks.EtaleCohomology.curveCohomologyStatements_X₂_of_shortExact`: the eight statements pass
  to the middle term of a short exact sequence, for a coefficient condition that descends to the
  sub- and the quotient sheaf.
* `Stacks.EtaleCohomology.curveCohomologyStatements_X₂_of_shortExact_isConstructible`: **Tag
  0A5C.** The same with the coefficient condition taken to be constructibility of an abelian
  sheaf, where that descent is Stacks 09BH (2).
* `finite_etaleCohomology_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion_isConstructible`
  and `finite_etaleCohomology_X₂_of_shortExact_of_isProper_isConstructible`, both in the namespace
  `Stacks.EtaleCohomology`:
  **statements (4) and (5) of Situation 0A52 on their own**, at constructibility of an abelian
  sheaf, with the two descents of Stacks 09BH (2) discharged rather than assumed. The other six
  statements are registered individually in
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/ShortExactExtension.lean`;
  their side conditions constrain only the scheme or are torsion conditions proved there, so they
  need no such instantiation, whereas statements (4) and (5) are the two whose transfer consumes
  an auxiliary result.

## Implementation notes

**The constructibility condition.** Statements (4) and (5) are conditional on the coefficient
sheaf being constructible, so for the middle term of `0 → F₁ → F → F₂ → 0` they need `F₁` and
`F₂` to be constructible whenever `F` is. That is Proposition 09BH (2), the strong Serre property
of the constructible abelian sheaves on a Noetherian scheme, and it is what Tag 0A5C cites at
exactly this point. Here it enters as
`AlgebraicGeometry.isConstructibleEtaleSiteAbelianSheaf_of_mono` and
`AlgebraicGeometry.isConstructibleEtaleSiteAbelianSheaf_of_epi`, applied to the monomorphism
`S.f` and the epimorphism `S.g` of the short exact sequence. The library's constructibility
predicate is stated for the small étale site of Stacks 021B, which is a dense subsite of the site
`AlgebraicGeometry.Scheme.smallEtaleTopology` on which the cohomology of the eight statements is
computed, so it is read across that identification; hence the big étale site `B` and the object
`X` of it in the statement. That choice is no restriction: every scheme lies in a big étale site.

**Hypotheses of Situation 0A52 that are absent.** The transfer uses neither the base field being
algebraically closed, nor the separatedness or the dimension bound on `X`, nor the standing
assumption that `F` is torsion in the sense of `Stacks.Torsion.torsionSheafProperty`. Of the
finite type hypothesis it uses only that `X` is Noetherian, which finite type over a field
implies — `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` together with
quasi-compactness of `X`. None of the others appears, which makes the statement below stronger
than the one Tag 0A5C makes and so implies it.

**What the Noetherian hypothesis is for.** It is used only through Stacks 09BH (2), that is, only
by statements (4) and (5); the other six transfers are unconditional on the scheme.

The coefficient universe is `AddCommGrpCat.{u + 1}` for `X.obj : Scheme.{u}`, the universe at
which 09BH (2) is available on this site, obtained from the family `AddCommGrpCat.{max (u + 1) v}`
in which this library computes étale cohomology by taking `v` to be `u + 1`.

## References

* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section General

variable {Z Z' : Scheme.{u}} (i : Z' ⟶ Z)
  [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- **The eight statements of Situation 0A52 pass to the middle term of a short exact sequence.**
Let `0 → S.X₁ → S.X₂ → S.X₃ → 0` be a short exact sequence of abelian sheaves on the small étale
site of `Z`. If the eight statements hold for `S.X₁` and for `S.X₃`, and the coefficient
condition `constructible` of statements (4) and (5) descends from `S.X₂` to `S.X₁` and to `S.X₃`,
then the eight statements hold for `S.X₂`.

The eight components are the eight theorems of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionSheavesCurves/ShortExactExtension.lean`.
The two descents `hsub` and `hquot` are Stacks 09BH (2) when `constructible` is constructibility
of an abelian sheaf; that instance of this theorem is
`Stacks.EtaleCohomology.curveCohomologyStatements_X₂_of_shortExact_isConstructible`. -/
theorem curveCohomologyStatements_X₂_of_shortExact {k : Type u} [Field k]
    (π : Z ⟶ Spec (.of k)) (l p : ℕ)
    {constructible : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
    (hS : S.ShortExact)
    (hsub : constructible S.X₂ → constructible S.X₁)
    (hquot : constructible S.X₂ → constructible S.X₃)
    (h₁ : CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₁)
    (h₃ : CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₃) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible S.X₂ where
  vanishing :=
    subsingleton_etaleCohomology_X₂_of_shortExact hS h₁.vanishing h₃.vanishing
  vanishing_of_isAffine :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isAffine hS
      h₁.vanishing_of_isAffine h₃.vanishing_of_isAffine
  vanishing_of_isPrimePowerTorsion :=
    subsingleton_etaleCohomology_X₂_of_shortExact_of_isPrimePowerTorsion l hS
      h₁.vanishing_of_isPrimePowerTorsion h₃.vanishing_of_isPrimePowerTorsion
  finite_of_isPrimeToCharacteristicTorsion :=
    finite_etaleCohomology_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion p hS hsub hquot
      h₁.finite_of_isPrimeToCharacteristicTorsion h₃.finite_of_isPrimeToCharacteristicTorsion
  finite_of_isProper :=
    finite_etaleCohomology_X₂_of_shortExact_of_isProper π hS hsub hquot
      h₁.finite_of_isProper h₃.finite_of_isProper
  bijective_restriction_of_isPrimeToCharacteristicTorsion :=
    bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion
      i p hS h₁.bijective_restriction_of_isPrimeToCharacteristicTorsion
      h₃.bijective_restriction_of_isPrimeToCharacteristicTorsion
  bijective_restriction_of_isProper :=
    bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isProper i π hS
      h₁.bijective_restriction_of_isProper h₃.bijective_restriction_of_isProper
  surjective_restriction :=
    surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_vanishing i hS
      h₁.vanishing h₁.surjective_restriction h₃.surjective_restriction

end General

section Constructible

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (AlgebraicGeometry.SmallEtale.topology B S.obj S.property)
      (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
    HasWeakSheafify
      ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
      AddCommGrpCat.{u + 1}]
  (X : B.Scheme) {Z' : Scheme.{u}} (i : Z' ⟶ X.obj)
  [HasExt.{w} (Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1})]
  {S : ShortComplex (Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1})}

/-- Constructibility of an abelian sheaf descends to the sub- and the quotient sheaf of a short
exact sequence. -/
private theorem isConstructible_descent_of_shortExact (Y : B.Scheme) [IsNoetherian Y.obj]
    {T : ShortComplex (Sheaf Y.obj.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hT : T.ShortExact) :
    (IsConstructibleEtaleSiteAbelianSheaf B Y T.X₂ →
        IsConstructibleEtaleSiteAbelianSheaf B Y T.X₁) ∧
      (IsConstructibleEtaleSiteAbelianSheaf B Y T.X₂ →
        IsConstructibleEtaleSiteAbelianSheaf B Y T.X₃) :=
  have := hT.mono_f
  have := hT.epi_g
  ⟨isConstructibleEtaleSiteAbelianSheaf_of_mono B Y T.f,
    isConstructibleEtaleSiteAbelianSheaf_of_epi B Y T.g⟩

/-- **Stacks Project, Tag 0A5C.** Let `X` be a Noetherian scheme, let `π` be a morphism from `X`
to the spectrum of a field, let `i` be a morphism of schemes to `X`, and let
`0 → S.X₁ → S.X₂ → S.X₃ → 0` be a short exact sequence of abelian sheaves on the small étale site
of `X`. If the eight statements of Situation 0A52 hold for `S.X₁` and for `S.X₃`, then they hold
for `S.X₂`.

The eight statements, bundled as `Stacks.EtaleCohomology.CurveCohomologyStatements`, are: the
vanishing of `H^q(X, -)` above degree two; its vanishing above degree one over an affine `X`; its
vanishing above degree one for coefficients of `l`-power torsion; the finiteness of `H^q(X, -)`
for constructible coefficients of torsion prime to `p`; its finiteness for constructible
coefficients over a proper `X`; the bijectivity of restriction along `i` for coefficients of
torsion prime to `p`; the bijectivity of restriction along `i` over a proper `X`; and the
surjectivity of restriction along `i` in degree two. In the source `l` and `p` are the
characteristic and the exponential characteristic of the base field, and `i` is the projection of
a scalar extension along an extension of algebraically closed fields in statements (6) and (7)
and the inclusion of an open subscheme in statement (8); none of those identifications is imposed
here, so this statement is stronger than the one the source makes.

Constructibility of an abelian sheaf is `AlgebraicGeometry.IsConstructibleEtaleSiteAbelianSheaf`,
read on the small étale site of Stacks 021B across its dense subsite comparison with the site
`AlgebraicGeometry.Scheme.smallEtaleTopology` that carries the cohomology. Its descent to the sub-
and the quotient sheaf of a short exact sequence, which statements (4) and (5) need, is
Proposition 09BH (2) and is what the Noetherian hypothesis is for; the other six transfers use no
hypothesis on `X` at all. Situation 0A52 asks `X` to be separated of finite type over an
algebraically closed field and of dimension at most one, and asks the sheaves to be torsion;
finite type over a field makes `X` Noetherian, and the remaining hypotheses are not used and so do
not appear. -/
@[stacks 0A5C "the eight statements of Situation 0A52 pass to the middle term of a short exact \
sequence of abelian sheaves, with constructibility of the sub- and the quotient sheaf supplied by \
Proposition 09BH (2)"]
theorem curveCohomologyStatements_X₂_of_shortExact_isConstructible [IsNoetherian X.obj]
    {k : Type u} [Field k] (π : X.obj ⟶ Spec (.of k)) (l p : ℕ) (hS : S.ShortExact)
    (h₁ : CurveCohomologyStatements.{u, u + 1, w} i π l p
      (IsConstructibleEtaleSiteAbelianSheaf B X) S.X₁)
    (h₃ : CurveCohomologyStatements.{u, u + 1, w} i π l p
      (IsConstructibleEtaleSiteAbelianSheaf B X) S.X₃) :
    CurveCohomologyStatements.{u, u + 1, w} i π l p
      (IsConstructibleEtaleSiteAbelianSheaf B X) S.X₂ :=
  curveCohomologyStatements_X₂_of_shortExact.{u, u + 1, w} i π l p hS
    (isConstructible_descent_of_shortExact B X hS).1
    (isConstructible_descent_of_shortExact B X hS).2 h₁ h₃

/-- **Statement (4) of Situation 0A52 passes to extensions, for constructible coefficients.** Let
`X` be a Noetherian scheme, let `p` be a natural number — the characteristic of the base field in
the source — and let `0 → S.X₁ → S.X₂ → S.X₃ → 0` be a short exact sequence of abelian sheaves on
the small étale site of `X`. If the finiteness of étale cohomology for coefficients that are
constructible and torsion prime to `p` holds for the sub- and the quotient sheaf, then it holds
for the middle sheaf.

This is `finite_etaleCohomology_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion` with the
coefficient condition taken to be constructibility of an abelian sheaf and its descent to the sub-
and the quotient sheaf *discharged*, by Proposition 09BH (2), rather than assumed: that descent is
what Tag 0A5C cites at this point, and it is the only use of the Noetherian hypothesis. -/
@[stacks 0A5C "statement (4): the finiteness of etale cohomology for constructible coefficients \
of torsion prime to the characteristic passes to the middle term of a short exact sequence, with \
the constructibility of the sub- and the quotient sheaf supplied by Proposition 09BH (2)"]
theorem finite_etaleCohomology_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion_isConstructible
    [IsNoetherian X.obj] (p : ℕ) (hS : S.ShortExact)
    (h₁ : IsConstructibleEtaleSiteAbelianSheaf B X S.X₁ →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p S.X₁ →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₁ q))
    (h₃ : IsConstructibleEtaleSiteAbelianSheaf B X S.X₃ →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p S.X₃ →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₃ q))
    (hc : IsConstructibleEtaleSiteAbelianSheaf B X S.X₂)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.obj.smallEtaleTopology p S.X₂)
    (q : ℕ) :
    Finite (Sheaf.H.{w} S.X₂ q) :=
  finite_etaleCohomology_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion.{u, u + 1, w} p hS
    (isConstructible_descent_of_shortExact B X hS).1
    (isConstructible_descent_of_shortExact B X hS).2
    h₁ h₃ hc ht q

/-- **Statement (5) of Situation 0A52 passes to extensions, for constructible coefficients.** Let
`X` be a Noetherian scheme, let `π` be its structure morphism to the spectrum of a field, and let
`0 → S.X₁ → S.X₂ → S.X₃ → 0` be a short exact sequence of abelian sheaves on the small étale site
of `X`. If the finiteness of étale cohomology for constructible coefficients over a proper `X`
holds for the sub- and the quotient sheaf, then it holds for the middle sheaf.

This is `Stacks.EtaleCohomology.finite_etaleCohomology_X₂_of_shortExact_of_isProper` with the
coefficient condition taken to be constructibility of an abelian sheaf and its descent to the sub-
and the quotient sheaf discharged by Proposition 09BH (2), exactly as in statement (4). The
properness condition constrains the scheme and is passed to the outer terms unchanged. -/
@[stacks 0A5C "statement (5): the finiteness of etale cohomology for constructible coefficients \
over a proper scheme passes to the middle term of a short exact sequence, with the \
constructibility of the sub- and the quotient sheaf supplied by Proposition 09BH (2)"]
theorem finite_etaleCohomology_X₂_of_shortExact_of_isProper_isConstructible
    [IsNoetherian X.obj] {k : Type u} [Field k] (π : X.obj ⟶ Spec (.of k)) (hS : S.ShortExact)
    (h₁ : IsConstructibleEtaleSiteAbelianSheaf B X S.X₁ → IsProper π →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₁ q))
    (h₃ : IsConstructibleEtaleSiteAbelianSheaf B X S.X₃ → IsProper π →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₃ q))
    (hc : IsConstructibleEtaleSiteAbelianSheaf B X S.X₂) (hπ : IsProper π) (q : ℕ) :
    Finite (Sheaf.H.{w} S.X₂ q) :=
  finite_etaleCohomology_X₂_of_shortExact_of_isProper.{u, u + 1, w} π hS
    (isConstructible_descent_of_shortExact B X hS).1
    (isConstructible_descent_of_shortExact B X hS).2
    h₁ h₃ hc hπ q

end Constructible

end Stacks.EtaleCohomology

end
