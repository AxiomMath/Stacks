module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedUnitAfterAnExactFaithfulFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ForgettingTheModuleStructureForTheDirectImage
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Unbounded base change over a square of sites, under the source's condition (6)

Let
```
  (Sh(C'), O_{C'}) --g'--> (Sh(C), O_C)
        |                      |
        f'                     f
        v                      v
  (Sh(D'), O_{D'}) --g-->  (Sh(D), O_D)
```
be the commutative square of ringed topoi of Stacks 0FN7: `u : D ⥤ C` and `u' : D' ⥤ C'`
continuous, giving `f`, `f'` with `f_* = u^s` and `f'_* = (u')^s`; `v : D' ⥤ D` and
`v' : C' ⥤ C` continuous as well as cocontinuous, giving `g`, `g'` whose inverse images are
restriction; `v ⋙ u = u' ⋙ v'`; and `g^{-1} O_D = O_{D'}`, `(g')^{-1} O_C = O_{C'}`. The tag's
second conclusion is `Rf'_* ∘ (g')^* = g^* ∘ Rf_*` on the *unbounded* derived categories, under
its condition (6): exactness of `g'_! : Ab(C') ⥤ Ab(C)`.

`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/BaseChangeOverASquareOfSites.lean`
proves that conclusion at four unrelated universes, but with condition (6) read on sheaves of
*modules* — left exactness of `Stacks.SheafOfModules.lowerShriek` — because that is where it
applies Stacks 08BJ, and by Stacks 0798 the two lower shrieks differ. This file proves it with
the source's own condition (6), for four sites at one universe.

## Main results

All in the namespace `Stacks.Cohomology.DerivedBaseChange`:

* `inverseImageCompTotalDerivedPushforwardIsoOfExactLowerShriek`:
  Stacks 0FN7, second conclusion, with condition (6) as the source states it.
* `isKInjective_mapHomologicalComplex_sheafPushforwardContinuous`:
  Stacks 08BJ on abelian sheaves — condition (6) makes `(g')^{-1}` preserve K-injectivity there.
* `isIso_totalRightDerivedOfAdditiveUnit_at_inverseImage`:
  the inverse image of a K-injective complex of `O_C`-modules computes `Rf'_*`.

## The argument

The source's proof opens by reducing to abelian sheaves through Stacks 0D6J, and that is what
is done here. Abstractly, the base change isomorphism needs exactly one thing beyond the
underived identity of Stacks 0FN4: that `(g')^* I` compute `Rf'_*` for every K-injective
complex `I` of `O_C`-modules — this is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit`. The module-level
substitution gets it by making `(g')^*I` K-injective again; the source gets it, from the
weaker abelian condition (6), in three steps:

* `(g')^{-1}` of abelian sheaves preserves K-injectivity (Stacks 08BJ for the adjunction
  `g'_! ⊣ (g')^{-1}` of Stacks 00XR), so if `I_ab ⟶ J^•` is a K-injective resolution of the
  underlying abelian complex of `I` then `(g')^{-1}I_ab ⟶ (g')^{-1}J^•` is one as well;
* its direct image `f'_*(g')^{-1}(I_ab ⟶ J^•)` is `g^{-1}f_*(I_ab ⟶ J^•)` by the first
  conclusion of Stacks 0FN2, and `f_*(I_ab ⟶ J^•)` is a quasi-isomorphism by Stacks 0D6J,
  which the exact `g^{-1}` preserves; so `(g')^{-1}I_ab` computes the abelian `Rf'_*`;
* the forgetful functor to abelian sheaves is exact and reflects isomorphisms, and carries
  `f'_*` to the degreewise direct image of abelian sheaves, so a comparison of right derived
  functors of modules may be checked after it
  (`Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget`), where the other
  half of what is needed — the abelian comparison at the underlying complex of *any*
  K-injective complex of `O_{C'}`-modules — is again Stacks 0D6J.

## Implementation notes

*One universe.* Stacks 0D6J is available in this library for a site whose objects, morphisms,
sheaf sections and module sections lie in a single universe, so all four sites here do. The
`HasSheafify` and `WEqualsLocallyBijective` hypotheses are then automatic; they are carried as
section variables only so that instance search finds them locally, as in the file above.

*Condition (6) is the only hypothesis.* The existence of `g'_!` is not assumed: for a continuous
`v'` the adjunction `g'_! ⊣ (g')^{-1}` is `Functor.sheafAdjunctionContinuous`, available from the
`HasSheafify` instances alone, so left exactness of `v'.sheafPullback` is the whole of condition
(6) and no adjointness hypothesis accompanies it.

## References

* [Stacks Project, Tag 0FN7](https://stacks.math.columbia.edu/tag/0FN7)
* [Stacks Project, Tag 0FN2](https://stacks.math.columbia.edu/tag/0FN2)
* [Stacks Project, Tag 0FN4](https://stacks.math.columbia.edu/tag/0FN4)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedBaseChange

open Stacks.SheafOfModules

universe u

section AbelianInverseImage

variable {C' : Type u} [Category.{u} C'] {C : Type u} [Category.{u} C]
  (J' : GrothendieckTopology C') (J : GrothendieckTopology C) (v' : C' ⥤ C)
  [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]

/-- The inverse image `(g')^{-1}` of abelian sheaves along a continuous and cocontinuous functor
of sites preserves finite colimits: it is itself a left adjoint, its right adjoint being the
direct image `{}_s v'` of the cocontinuous functor. -/
@[sga "4 IV 3.1.2" "partial, special case"]
instance preservesFiniteColimits_sheafPushforwardContinuous_of_isCocontinuous :
    PreservesFiniteColimits (v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J) :=
  have := (v'.sheafAdjunctionCocontinuous AddCommGrpCat.{u} J' J).isLeftAdjoint
  inferInstance

/-- **Stacks 08BJ on abelian sheaves.** If `g'_! : Ab(C') ⥤ Ab(C)` — the left adjoint of the
inverse image `(g')^{-1} = (v')^p` of Stacks 00XR — is exact, then `(g')^{-1}` carries
K-injective complexes of abelian sheaves on `C` to K-injective complexes of abelian sheaves on
`C'`. Right exactness of `g'_!` is automatic, it being a left adjoint, so the hypothesis is its
left exactness. -/
theorem isKInjective_mapHomologicalComplex_sheafPushforwardContinuous
    [PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat.{u} J' J)]
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have hadj := v'.sheafAdjunctionContinuous AddCommGrpCat.{u} J' J
  have : (v'.sheafPullback AddCommGrpCat.{u} J' J).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesColimitsOfSize.{0, 0} (v'.sheafPullback AddCommGrpCat.{u} J' J) :=
    hadj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (v'.sheafPullback AddCommGrpCat.{u} J' J) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _
    (v'.sheafPullback AddCommGrpCat.{u} J' J) hadj I

end AbelianInverseImage

section Square

attribute [local instance] HasDerivedCategory.standard

variable {C' : Type u} [Category.{u} C'] {C : Type u} [Category.{u} C] {D' : Type u}
  [Category.{u} D'] {D : Type u} [Category.{u} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u : D ⥤ C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ C) [u.IsContinuous K J]
  [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v.IsCocontinuous K' K] [v'.IsContinuous J' J]
  [v'.IsCocontinuous J' J] [HasSheafify J AddCommGrpCat.{u}] [HasSheafify J' AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [HasSheafify K' AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [K'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction along two composable continuous functors of sites is restriction along the
composite, so a quasi-isomorphy statement about the one is the statement about the other. -/
private theorem quasiIso_sheafPushforwardContinuous_comp_iff {E : Type u} [Category.{u} E]
    {F : Type u} [Category.{u} F] {G : Type u} [Category.{u} G] (JE : GrothendieckTopology E)
    (JF : GrothendieckTopology F) (JG : GrothendieckTopology G) (a : F ⥤ E) (b : G ⥤ F)
    (c : G ⥤ E) [a.IsContinuous JF JE] [b.IsContinuous JG JF] [c.IsContinuous JG JE]
    (h : b ⋙ a = c) {M N : CochainComplex (Sheaf JE AddCommGrpCat.{u}) ℤ} (φ : M ⟶ N) :
    QuasiIso (((b.sheafPushforwardContinuous AddCommGrpCat.{u} JG JF).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      (((a.sheafPushforwardContinuous AddCommGrpCat.{u} JF JE).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ)) ↔
      QuasiIso (((c.sheafPushforwardContinuous AddCommGrpCat.{u} JG JE).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) := by
  subst h
  exact Iff.rfl

/-- Equal continuous functors of sites restrict a morphism of complexes to the same morphism. -/
private theorem quasiIso_sheafPushforwardContinuous_congr {E : Type u} [Category.{u} E]
    {G : Type u} [Category.{u} G] (JE : GrothendieckTopology E) (JG : GrothendieckTopology G)
    {w w' : G ⥤ E} [w.IsContinuous JG JE] [w'.IsContinuous JG JE] (h : w = w')
    {M N : CochainComplex (Sheaf JE AddCommGrpCat.{u}) ℤ} (φ : M ⟶ N)
    (hq : QuasiIso (((w.sheafPushforwardContinuous AddCommGrpCat.{u} JG JE).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ)) :
    QuasiIso (((w'.sheafPushforwardContinuous AddCommGrpCat.{u} JG JE).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) := by
  subst h
  exact hq

omit [J.WEqualsLocallyBijective AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [K.WEqualsLocallyBijective AddCommGrpCat] [K'.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The first conclusion of Stacks 0FN2 on complexes of abelian sheaves**:
`f'_* ∘ (g')^{-1} = g^{-1} ∘ f_*`, both sides being restriction along one of the two sides of
the square. -/
private theorem quasiIso_inverseImage_pushforward_of_square
    {M N : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} (φ : M ⟶ N) (hsq : v ⋙ u = u' ⋙ v')
    (hq : QuasiIso (((v.sheafPushforwardContinuous AddCommGrpCat.{u} K' K).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (((u.sheafPushforwardContinuous AddCommGrpCat.{u} K J).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ))) :
    QuasiIso (((u'.sheafPushforwardContinuous AddCommGrpCat.{u} K' J').mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ)) := by
  have : (v ⋙ u).IsContinuous K' J := Functor.isContinuous_comp v u K' K J
  have : (u' ⋙ v').IsContinuous K' J := Functor.isContinuous_comp u' v' K' J' J
  exact (quasiIso_sheafPushforwardContinuous_comp_iff J J' K' v' u' (u' ⋙ v') rfl φ).mpr
    (quasiIso_sheafPushforwardContinuous_congr J K' hsq φ
      ((quasiIso_sheafPushforwardContinuous_comp_iff J K K' u v (v ⋙ u) rfl φ).mp hq))

variable (OC : Sheaf J RingCat.{u})

omit [J'.WEqualsLocallyBijective AddCommGrpCat] [K.WEqualsLocallyBijective AddCommGrpCat]
  [K'.WEqualsLocallyBijective AddCommGrpCat] in
include K in
/-- **The inverse image of the underlying abelian complex of a K-injective complex of modules
computes `Rf'_*` on abelian sheaves.** This is the whole of the source's proof of the second
conclusion of Stacks 0FN7, read on abelian sheaves: choose a K-injective resolution
`I_ab ⟶ J^•` on `C`; condition (6) and Stacks 08BJ make `(g')^{-1}J^•` K-injective, so it is a
K-injective resolution of `(g')^{-1}I_ab`; its direct image `f'_*(g')^{-1}J^•` is
`g^{-1}f_*J^•` by Stacks 0FN2, and `f_*(I_ab ⟶ J^•)` is a quasi-isomorphism by Stacks 0D6J,
which `g^{-1}` preserves, being exact. -/
theorem isIso_derivedAbelianPushforwardUnit_at_inverseImage
    [PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat.{u} J' J)]
    (hsq : v ⋙ u = u' ⋙ v') (I : CochainComplex (SheafOfModules.{u} OC) ℤ) [I.IsKInjective] :
    IsIso ((ForgetModule.derivedAbelianPushforwardUnit J' K' u').app
      ((HomotopyCategory.quotient (Sheaf J' AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
        (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf OC).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
  set Iab : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ :=
    ((SheafOfModules.toSheaf OC).mapHomologicalComplex (ComplexShape.up ℤ)).obj I with hIab
  set qI := (Stacks.Injectives.kInjectiveResolutionInclusion (Sheaf J AddCommGrpCat.{u})).app Iab
    with hqI
  have := isKInjective_mapHomologicalComplex_sheafPushforwardContinuous J' J v'
    ((Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf J AddCommGrpCat.{u})).obj Iab)
  have : QuasiIso (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J'
      J).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology qI _
  have huq : QuasiIso (((u.sheafPushforwardContinuous AddCommGrpCat.{u} K
      J).mapHomologicalComplex (ComplexShape.up ℤ)).map qI) :=
    ForgetModule.quasiIso_abelianPushforward_map_of_isKInjective J K u OC I qI
  exact ForgetModule.rightDerivedUnit_isIso_of_quasiIso_resolution_degreewise _ _ _
    (((v'.sheafPushforwardContinuous AddCommGrpCat.{u} J' J).mapHomologicalComplex
      (ComplexShape.up ℤ)).map qI)
    (quasiIso_inverseImage_pushforward_of_square J' J K' K u u' v v' qI hsq
      (HomologicalComplex.quasiIso_map_of_preservesHomology _ _))

variable (OD : Sheaf K RingCat.{u})
  (f'Sharp : inverseImageRing K' K v OD ⟶
    (u'.sheafPushforwardContinuous RingCat.{u} K' J').obj (inverseImageRing J' J v' OC))

omit [K.WEqualsLocallyBijective AddCommGrpCat] in
include K in
/-- **The inverse image of a K-injective complex of `O_C`-modules computes `Rf'_*`.** The
module-level statement that the second conclusion of Stacks 0FN7 needs, and the one the source
reaches through Stacks 0D6J: the forgetful functor to abelian sheaves is exact and reflects
isomorphisms, it carries `f'_*` to the degreewise direct image of abelian sheaves, and the
abelian comparison is invertible both at the underlying complex of any K-injective complex of
`O_{C'}`-modules — which is Stacks 0D6J — and at this one, which is
`isIso_derivedAbelianPushforwardUnit_at_inverseImage`. -/
theorem isIso_totalRightDerivedOfAdditiveUnit_at_inverseImage
    [PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat.{u} J' J)]
    (hsq : v ⋙ u = u' ⋙ v') (I : CochainComplex (SheafOfModules.{u} OC) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((UnboundedComplexes.totalRightDerivedOfAdditiveUnit
        (_root_.SheafOfModules.pushforward.{u} f'Sharp)).app
      (((inverseImage.{u} J' J v' OC).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} OC) (ComplexShape.up ℤ)).obj I))) := by
  have := hI
  exact UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    (_root_.SheafOfModules.pushforward.{u} f'Sharp)
    (ForgetModule.abelianPushforward J' K' u')
    (_root_.SheafOfModules.toSheaf (inverseImageRing J' J v' OC))
    (_root_.SheafOfModules.toSheaf (inverseImageRing K' K v OD)) (Iso.refl _) _
    (ForgetModule.derivedAbelianPushforward J' K' u') _
    (ForgetModule.derivedAbelianPushforwardUnit J' K' u')
    (fun I' hI' => have := hI'
      ForgetModule.abelianPushforwardUnit_isIso_at_underlying_kInjective J' K' u'
        (inverseImageRing J' J v' OC) I')
    _ (isIso_derivedAbelianPushforwardUnit_at_inverseImage J' J K' K u u' v v' OC hsq I)

include K in
/-- **Stacks 0FN7**, second conclusion, under the source's own condition (6). For a commutative
square of ringed topoi whose horizontal functors `u : D ⥤ C`, `u' : D' ⥤ C'` are continuous —
giving `f`, `f'` with `f_* = u^s`, `f'_* = (u')^s` — whose vertical functors `v : D' ⥤ D`,
`v' : C' ⥤ C` are continuous as well as cocontinuous — giving `g`, `g'` with `g^{-1}`,
`(g')^{-1}` restriction — with `v ⋙ u = u' ⋙ v'`, with `g^{-1} O_D = O_{D'}` and
`(g')^{-1} O_C = O_{C'}`, and with `g'_! : Ab(C') ⥤ Ab(C)` exact, we have
`Rf'_* ∘ (g')^* = g^* ∘ Rf_*` as functors `D(O_C) ⥤ D(O_{D'})`.

Condition (6) is the hypothesis `PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat J' J)`:
`v'.sheafPullback` is the left adjoint `g'_! = (v')_s` of the inverse image `(g')^{-1} = (v')^p`
of abelian sheaves, which Stacks 00XR produces for a continuous and cocontinuous `v'`, and
right exactness of a left adjoint is automatic, so left exactness is the whole of the condition.

Both `Rf_*` and `Rf'_*` are the total right derived functors of the degreewise direct images;
nothing about them is assumed. The source's proof is followed exactly: condition (6) and
Stacks 08BJ make `(g')^{-1}` preserve K-injectivity *of abelian sheaves*, Stacks 0FN2 gives the
underived identity there, and Stacks 0D6J carries the resulting statement — that the inverse
image of a K-injective complex of `O_C`-modules computes `Rf'_*` — back to modules. -/
@[stacks 0FN7 "the second conclusion, at the source's full statement of it:
  `Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` on the *unbounded* derived categories `D(O_C) → D(O_{D'})`, for
  a commutative square of ringed topoi whose horizontal functors `u`, `u'` are continuous and
  whose vertical functors `v`, `v'` are continuous as well as cocontinuous, with
  `v ⋙ u = u' ⋙ v'`, `g^{-1} O_D = O_{D'}` and `(g')^{-1} O_C = O_{C'}`, and with the tag's
  condition (6) as the source states it — exactness of `g'_! : Ab(C') → Ab(C)`, written
  `PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat J' J)`, right exactness of a left
  adjoint being automatic. Nothing else is assumed: in particular NOT the module-level
  substitution for condition (6) that
  `Stacks.Cohomology.DerivedBaseChange.inverseImageCompDerivedPushforwardIso` and
  `Stacks.Cohomology.DerivedBaseChange.inverseImageCompTotalDerivedPushforwardIso` grant in its
  place, those two adding four independent universes instead. The price here is that the four
  sites lie in one universe, which is where Stacks 0D6J, the transport from abelian sheaves to
  modules that the source's proof opens with, is available. `Rf_*` and `Rf'_*` are
  *constructed*, as the total right derived functors of the degreewise direct images, and
  nothing about them is assumed. An isomorphism rather than an equality, a right derived functor
  being determined only up to a canonical isomorphism. The first conclusion of the tag, the same
  identity on `D^+` without condition (6), is
  `Stacks.Cohomology.DerivedBaseChange.inverseImageCompDerivedPushforwardPlusIsoOfRingedSite`."]
def inverseImageCompTotalDerivedPushforwardIsoOfExactLowerShriek
    [PreservesFiniteLimits (v'.sheafPullback AddCommGrpCat.{u} J' J)]
    (fSharp : OD ⟶ (u.sheafPushforwardContinuous RingCat.{u} K J).obj OC)
    (hsq : v ⋙ u = u' ⋙ v')
    (hcomm : f'Sharp = restrictStructureMap J' J K' K u u' v v' OC OD fSharp hsq) :
    (inverseImage.{u} J' J v' OC).mapDerivedCategory ⋙
        UnboundedComplexes.totalRightDerivedOfAdditive
          (_root_.SheafOfModules.pushforward.{u} f'Sharp) ≅
      UnboundedComplexes.totalRightDerivedOfAdditive
          (_root_.SheafOfModules.pushforward.{u} fSharp) ⋙
        (inverseImage.{u} K' K v OD).mapDerivedCategory :=
  UnboundedComplexes.derivedBaseChangeIsoOfUnit (inverseImage.{u} J' J v' OC)
    (inverseImage.{u} K' K v OD) (_root_.SheafOfModules.pushforward.{u} fSharp)
    (_root_.SheafOfModules.pushforward.{u} f'Sharp)
    (UnboundedComplexes.totalRightDerivedOfAdditive
      (_root_.SheafOfModules.pushforward.{u} fSharp))
    (UnboundedComplexes.totalRightDerivedOfAdditive
      (_root_.SheafOfModules.pushforward.{u} f'Sharp))
    (UnboundedComplexes.totalRightDerivedOfAdditiveUnit
      (_root_.SheafOfModules.pushforward.{u} fSharp))
    (UnboundedComplexes.totalRightDerivedOfAdditiveUnit
      (_root_.SheafOfModules.pushforward.{u} f'Sharp))
    (eqToIso (inverseImage_comp_pushforward_eq.{u} J' J K' K u u' v v' OC OD fSharp f'Sharp hsq
      hcomm))
    fun I hI => isIso_totalRightDerivedOfAdditiveUnit_at_inverseImage J' J K' K u u' v v' OC OD
      f'Sharp hsq I hI

end Square

end Stacks.Cohomology.DerivedBaseChange

end
