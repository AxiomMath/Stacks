module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTriple

/-!
# Derived pullback commutes with derived décalage for a triple as in Situation 0F8S

Let `(X, D, M)` be a triple as in Situation 0F8S — a scheme, an effective Cartier divisor on it
with ideal sheaf `I = ℐ_D`, and a perfect object `M` of `D(𝒪_X)` — and let `h : Y ⟶ X` be a
morphism of schemes for which the pullback `E = h^{-1}D` is defined, with ideal sheaf
`J = ℐ_E`.  [Stacks, Tag 0F9X] asserts that if `(X, D, M)` is a good triple then

`Lh^*(Lη_I M) = Lη_J(Lh^* M)`

in `D(𝒪_Y)`.  This file states that as an isomorphism of the two objects, for a **flat** `h`.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.standardObject`: the perfect object of the
  situation, carried from the situation's own model of the derived category to the standard one.
* `AlgebraicGeometry.ComplexAndDivisorSituation.derivedEtaPullbackIso`: **[Stacks, Tag 0F9X] for
  a flat `h`**, as an isomorphism `Lh^*(Lη_I M) ≅ Lη_J(Lh^* M)`.

## What is assumed

**Flatness is assumed and goodness is not used.**  The source proves tag 0F9X from goodness of
the triple, by the affine computation of More on Algebra, Section 15.98, which uses principality
of the determinantal ideals.  The route taken here instead uses exactness of flat pullback; so
the statement below carries flatness, which the source does not, and it does **not** carry
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodTriple`, which the source does — nothing in
this route consumes goodness, so carrying it would only weaken the result.  The restriction to
flat `h` is named in the attribute.

**[Stacks, Tag 0F8Q] is not carried.**  Unlike tag 0GTW
(`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj`), which takes the
functor `Lη_I` as a hypothesis `Stacks.Divisors.Eta.DerivedEta S.D`, nothing here is
hypothetical: `Stacks.IdealTorsion.Eta.derivedEta` is the functor and
`Stacks.Divisors.Eta.derivedEtaData` shows it discharges tag 0F8Q unconditionally for the ideal
sheaf of an effective Cartier divisor on a scheme.  Neither is the second assertion of
[Stacks, Tag 0GTV] needed: no affine chart appears in this route.

**The presentation of `M` is data, and always exists.**  `Lη_I` is compared with the chain-level
décalage on complexes of `I`-torsion-free modules, so the comparison is written at an object
presented that way; the presentation `K` together with `hKM` is therefore part of the input.  It
is no loss of generality: every object of `D(𝒪_X)` admits one, by
`Stacks.Divisors.Eta.exists_torsionFreeComplex_iso`.

## Implementation notes

The situation carries its own model of the derived category of `𝒪_X`-modules as an
instance-implicit field, while `Stacks.IdealTorsion.Eta.derivedEta` and the left derived pullback
are written at `CategoryTheory.HasDerivedCategory.standard`.
`AlgebraicGeometry.ComplexAndDivisorSituation.standardObject` moves `S.M` across by
`CategoryTheory.Localization.uniq`, the canonical equivalence of two localizations at the
quasi-isomorphisms — the same transport that
`AlgebraicGeometry.ComplexAndDivisorSituation.derivedPullbackObject` already performs, so that
`S.derivedPullbackObject h` is `Lh^*` of `S.standardObject` by definition and the right-hand side
of the comparison is the pulled-back triple's object on the nose.

The three instance hypotheses of the scheme-level comparison — left and right exactness of `h^*`
and monomorphy of `h^*I ⟶ 𝒪_Y` — are discharged here from flatness.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 01WV](https://stacks.math.columbia.edu/tag/01WV)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Divisors.Eta (idealSheaf idealSheafι hasTorsionFreeResolutions)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

/-- Sheaves of modules on a ringed space form an abelian category, restated at the `OXMod`
spelling of the structure sheaf that Situation 0F8S is written in.  Instance search finds
`SheafOfModules.instAbelian` at this spelling in isolation but stops once the décalage files are
in scope, which the imports above bring in; this is the same restatement, for the same reason, as
the ones in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackDerived` and
`StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackComparison`. -/
instance abelianOXMod (W : RingedSpace.{u, u}) : Abelian (OXMod.{u, u} W) :=
  SheafOfModules.instAbelian _

/-- The perfect object of a triple as in Situation 0F8S, carried from the situation's own model of
the derived category of `𝒪_X`-modules to the standard model, by the canonical equivalence of two
localizations at the quasi-isomorphisms.  This is the transport already performed inside
`AlgebraicGeometry.ComplexAndDivisorSituation.derivedPullbackObject`, named so that the two
sides of the comparison below can be written at one model. -/
def standardObject (S : ComplexAndDivisorSituation.{u, d}) :
    DerivedCategory (OXMod.{u, u} S.X.toRingedSpace) :=
  (Localization.uniq
      (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
      (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
        (OXMod.{u, u} S.X.toRingedSpace)))
      (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
        (ComplexShape.up ℤ))).functor.obj S.M

/-- The derived pullback of the object of a triple is the left derived pullback of
`AlgebraicGeometry.ComplexAndDivisorSituation.standardObject`, by definition. -/
theorem derivedPullbackObject_eq (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) :
    S.derivedPullbackObject h =
      (derivedPullback h.toLRSHom.toShHom).obj S.standardObject :=
  rfl

/-- **[Stacks, Tag 0F9X] for a flat morphism.**  Let `X`, `D`, `I`, `M` be as in Situation 0F8S,
let `h : Y ⟶ X` be a flat morphism of schemes such that the pullback `E = h^{-1}D` is defined,
and let `J = ℐ_E`.  Then

`Lh^*(Lη_I M) ≅ Lη_J(Lh^* M)`

in `D(𝒪_Y)`, where the right-hand side is the object of the pulled-back triple
`AlgebraicGeometry.ComplexAndDivisorSituation.pullback`.

The isomorphism is `Stacks.Divisors.Eta.derivedEtaPullbackIso`, conjugated by the presentation
`hKM` of `M` by a complex of `I`-torsion-free modules on each side.

The source's hypothesis that `(X, D, M)` is a good triple is **not** needed by this route and is
therefore not carried: the statement below is the flat case of tag 0F9X *without* goodness, which
is strictly stronger than the flat case of the source's statement.  Flatness, which the source
does not assume, is named in the attribute. -/
@[stacks 0F9X "the case of a flat h, with no goodness hypothesis, which is therefore neither \
weaker nor stronger than the source's statement. the general case, for an arbitrary h and a good \
triple, is AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullback_derivedEta_iso"]
def derivedEtaPullbackIso (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) [AlgebraicGeometry.Flat h]
    [hD : Stacks.Divisors.IsPullbackDefined h S.D]
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule S.X.toRingedSpace (idealSheafι S.D)) ℤ)
    (hKM : DerivedCategory.Q.obj
      ((Stacks.IdealTorsion.Eta.torsionFreeComplex S.X.toRingedSpace
        (idealSheafι S.D)).obj K) ≅ S.standardObject) :
    (derivedPullback h.toLRSHom.toShHom).obj
        ((@Stacks.IdealTorsion.Eta.derivedEta S.X.toRingedSpace (idealSheaf S.D)
          (idealSheafι S.D) (Stacks.Divisors.Eta.mono_idealSheafι S.D)
          (Stacks.Divisors.Eta.isInvertible_idealSheaf S.D)
          (hasTorsionFreeResolutions S.D)).obj S.standardObject) ≅
      (@Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (S.D.comap h))
          (idealSheafι (S.D.comap h)) (Stacks.Divisors.Eta.mono_idealSheafι (S.D.comap h))
          (Stacks.Divisors.Eta.isInvertible_idealSheaf (S.D.comap h))
          (hasTorsionFreeResolutions (S.D.comap h))).obj
        (S.derivedPullbackObject h) :=
  have hflat : AlgebraicGeometry.IsFlat h.toLRSHom.toShHom :=
    fun x => AlgebraicGeometry.Flat.stalkMap h x
  letI : PreservesFiniteLimits
      (Stacks.IdealTorsion.Eta.etaPullbackModules h.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat
      h.toLRSHom.toShHom hflat
  letI : PreservesColimits (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesColimits_modulePullback h.toLRSHom.toShHom
  letI : PreservesFiniteColimits
      (Stacks.IdealTorsion.Eta.etaPullbackModules h.toLRSHom.toShHom) :=
    inferInstanceAs (PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom))
  letI : Mono (Stacks.IdealTorsion.Eta.pullbackIdealIncl h.toLRSHom.toShHom
      (idealSheaf S.D) (idealSheafι S.D)) :=
    @Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl _ _ h.toLRSHom.toShHom hflat
      (idealSheaf S.D) (idealSheafι S.D) (Stacks.Divisors.Eta.mono_idealSheafι S.D)
  (derivedPullback h.toLRSHom.toShHom).mapIso
      ((@Stacks.IdealTorsion.Eta.derivedEta S.X.toRingedSpace (idealSheaf S.D)
        (idealSheafι S.D) (Stacks.Divisors.Eta.mono_idealSheafι S.D)
        (Stacks.Divisors.Eta.isInvertible_idealSheaf S.D)
        (hasTorsionFreeResolutions S.D)).mapIso hKM.symm) ≪≫
    Stacks.Divisors.Eta.derivedEtaPullbackIso h S.D hflat K ≪≫
    (@Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (S.D.comap h))
        (idealSheafι (S.D.comap h)) (Stacks.Divisors.Eta.mono_idealSheafι (S.D.comap h))
        (Stacks.Divisors.Eta.isInvertible_idealSheaf (S.D.comap h))
        (hasTorsionFreeResolutions (S.D.comap h))).mapIso
      ((derivedPullback h.toLRSHom.toShHom).mapIso hKM)

end AlgebraicGeometry.ComplexAndDivisorSituation

end
