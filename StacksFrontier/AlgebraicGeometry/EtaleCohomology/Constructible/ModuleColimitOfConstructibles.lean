module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafPresentationColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
import StacksCore.Tactic.StacksAttribute

/-!
# Étale sheaves of sets and of modules as filtered colimits of constructible ones

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site. Every sheaf of sets on
the small étale site of `X` is a filtered colimit of constructible sheaves of sets, and for a
Noetherian ring `Λ` every sheaf of `Λ`-modules is a filtered colimit of constructible sheaves of
`Λ`-modules. These are parts (1) and (3) of Stacks 03SA, with nothing granted. The same is done
here for one of the two inclusions of Stacks 09YT: the cokernels it displays, of maps between
finite direct sums of the sheaves `j_{U!}(Z/nZ)`, are constructible abelian sheaves.

The statements are the ones of
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf`,
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf`,
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation` and
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_affineZModShriekPresentation`, which carry the
inputs of the source's proof as explicit hypotheses because the library did not have them. All of
them are available now:

* `h093C` of part (1), Stacks 093C part (1) in the coequalizer spelling, is
  `AlgebraicGeometry.setSheavesAreFilteredColimitsOfPresentations`;
* `h03S0` of part (1), the stratification of an étale object into strata on which it becomes
  finite étale, is `AlgebraicGeometry.etaleFiniteStratificationExists`;
* `h093C` of part (3), Stacks 093C part (2) in the shriek spelling, is
  `AlgebraicGeometry.moduleSheavesAreFilteredColimitsOfPresentations`;
* `hshriek` of part (3), Stacks 03S8 for sheaves of modules, is
  `AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`;
* `h03S8` of the two Stacks 09YT statements, Stacks 03S8 part (2) at the finite groups `Z/nZ`, is
  `AlgebraicGeometry.abelianShriekZModIsConstructible`.

Stacks 03RZ and Stacks 03S8 (1) — constructibility is a weak Serre condition, so the coequalizers
and cokernels appearing in the presentations are constructible — were already discharged in the
conditional forms. So the only assumptions left are the ones of the tags themselves: `X`
quasi-compact and quasi-separated, and `Λ` Noetherian.

This module is therefore where Stacks 03SA parts (1) and (3) and Stacks 09YT are registered
unconditionally;
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles` proves the
four statements under their binders.

Part (2) of Stacks 03SA, for torsion abelian sheaves, is
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs` of the module
`LocalTorsionColimitOfConstructibles` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible`, which reduces it to part (3) here.

The reverse inclusion of Stacks 09YT — every constructible abelian sheaf has such a
presentation — is not here either; what it needs is listed on
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`.

## Main results

* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf_of_qcqs` —
  **Stacks 03SA part (1)**, unconditionally.
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs` —
  **Stacks 03SA part (3)**, unconditionally.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation_of_qcqs` and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_of_affineZModShriekPresentation_of_qcqs` —
  **one inclusion of Stacks 09YT**, unconditionally, at the quasi-compact quasi-separated and at
  the affine form of the displayed cokernels.

## References

* [Stacks, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks, Tag 09YT](https://stacks.math.columbia.edu/tag/09YT)
* [Stacks, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (u + 1)) [CommRing Λ]
  [IsNoetherianRing Λ] [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]

/-- **Stacks 03SA, part (1).** Let `X` be a quasi-compact and quasi-separated scheme and `F` a
sheaf of sets on `X_étale`. Then `F` is a filtered colimit of constructible sheaves of sets.

This is `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf` with both of its
hypotheses discharged: Stacks 093C (1) by
`AlgebraicGeometry.setSheavesAreFilteredColimitsOfPresentations` and Stacks 03S0 by
`AlgebraicGeometry.etaleFiniteStratificationExists`. -/
@[stacks 03SA "part (1), sheaves of sets, with 093C (1) and 03S0 discharged"]
public theorem exists_isFilteredColimit_isConstructibleSetSheaf_of_qcqs
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleSetSheaf B X (D.obj i) :=
  exists_isFilteredColimit_isConstructibleSetSheaf B X
    (setSheavesAreFilteredColimitsOfPresentations B X) (etaleFiniteStratificationExists B)
    ‹CompactSpace X.obj› ‹QuasiSeparatedSpace X.obj› F

/-- **Stacks 03SA, part (3).** Let `X` be a quasi-compact and quasi-separated scheme, `Λ` a
Noetherian ring and `F` a sheaf of `Λ`-modules on `X_étale`. Then `F` is a filtered colimit of
constructible sheaves of `Λ`-modules.

This is `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf` with both of its
hypotheses discharged: Stacks 093C (2) by
`AlgebraicGeometry.moduleSheavesAreFilteredColimitsOfPresentations` and Stacks 03S8 for sheaves of
modules by `AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`. -/
@[stacks 03SA "part (3), sheaves of modules, with 093C (2) and 03S8 discharged",
  sga "4 XVII 5.5.25.4" "more general"]
public theorem exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleModuleSheaf B X Λ (D.obj i) :=
  exists_isFilteredColimit_isConstructibleModuleSheaf B X Λ
    (moduleSheavesAreFilteredColimitsOfPresentations B X Λ)
    (fun U hU => by
      have hc : CompactSpace U.obj.left.obj := hU.1
      have hq : QuasiSeparatedSpace U.obj.left.obj := hU.2
      exact isConstructibleModuleSheaf_moduleShriekConstant B X Λ U)
    F

/-- **Stacks 09YT**, the inclusion of the displayed cokernels into the constructible abelian
sheaves. Let `X` be quasi-compact and quasi-separated. Every abelian sheaf of the form
`Coker(⨁_j j_{V_j!}(Z/m_jZ) → ⨁_i j_{U_i!}(Z/n_iZ))`, with the `V_j` and `U_i` quasi-compact
quasi-separated objects of `X_étale` and the `m_j`, `n_i` positive, is a constructible abelian
sheaf.

This is `AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation` with
its one hypothesis discharged: Stacks 03S8 (2) at the finite groups `Z/nZ` by
`AlgebraicGeometry.abelianShriekZModIsConstructible`.

The reverse inclusion — every constructible abelian sheaf has such a presentation — is the other
half of the tag and is not proved; the three things it needs, and which two of them this library
has, are listed on
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`. -/
@[stacks 09YT "the inclusion of the displayed cokernels at quasi-compact quasi-separated etale \
  objects into the constructible abelian sheaves, with Stacks 03S8 (2) at the finite groups Z/nZ \
  discharged; the reverse inclusion needs Stacks 095N at Lambda = Z/nZ and is not proved here"]
public theorem isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation_of_qcqs
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : HasFiniteZModShriekPresentation B X (IsQCQSEtaleObject B X) F) :
    IsConstructibleAbelianSheaf B X F :=
  isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation B X
    (abelianShriekZModIsConstructible B) ‹CompactSpace X.obj› ‹QuasiSeparatedSpace X.obj› hF

/-- **Stacks 09YT, the affine form of the same inclusion.** "In fact, we can even assume `U_i` and
`V_j` affine": for this inclusion that is a weakening of the hypothesis, since an affine scheme is
quasi-compact and quasi-separated.

This is `AlgebraicGeometry.isConstructibleAbelianSheaf_of_affineZModShriekPresentation` with its
one hypothesis discharged, by `AlgebraicGeometry.abelianShriekZModIsConstructible`. -/
@[stacks 09YT "the same inclusion for the affine form of the displayed cokernels (the tag's \
  concluding sentence), with Stacks 03S8 (2) at the finite groups Z/nZ discharged"]
public theorem isConstructibleAbelianSheaf_of_affineZModShriekPresentation_of_qcqs
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : HasFiniteZModShriekPresentation B X (SmallEtale.IsAffine B X.obj X.property) F) :
    IsConstructibleAbelianSheaf B X F :=
  isConstructibleAbelianSheaf_of_affineZModShriekPresentation B X
    (abelianShriekZModIsConstructible B) ‹CompactSpace X.obj› ‹QuasiSeparatedSpace X.obj› hF

end AlgebraicGeometry

end
