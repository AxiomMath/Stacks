module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine

/-!
# Discharging the affine-open hypothesis of Stacks 09T6

[Stacks, Tag 09T6] is a criterion: *if* for every affine open `U ⊆ X` the right derived functor
`Φ` of `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)` fits into the commutative square
`i_X ∘ Φ ≅ Rj_* ∘ i_U`, *then* the comparison functor of [Stacks, Tag 06VT] is an equivalence with
quasi-inverse `RQ_X`. That hypothesis is recorded in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/CoheratorQuasiInverse.lean` as
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible`. This file **proves** it, so that the
criterion is not vacuous.

The source discharges the hypothesis in the proof of [Stacks, Tag 08DB]: for an affine open
`U ⊆ X` the open immersion `j : U ⟶ X` is an *affine* morphism as soon as `X` has affine diagonal,
and for an affine morphism the square is [Stacks, Tag 08D7]. Both halves are available in the
library — affineness of `j` is
`Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source`, and the square is
`AlgebraicGeometry.derivedQuasicoherentComparisonSquare` — so the work here is to read 08D7's
square at an arbitrary model of the derived categories and to exhibit the two derived functors
together with the derivation units that
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` demands.

**The affine-diagonal hypothesis is not removable.** The hypothesis of [Stacks, Tag 09T6] is
*false* for a general quasi-compact quasi-separated scheme: an affine open immersion into such a
scheme need not be an affine morphism, and `R^1 j_*` of a quasi-coherent module need not vanish,
so no square `i_X ∘ Φ ≅ Rj_* ∘ i_U` can exist. Affine diagonal — equivalently, the condition that
pairwise intersections of affine opens be affine — is exactly what the source assumes when it
verifies the hypothesis, and it is the hypothesis assumed here.

## Main definitions

* `Stacks.DerivedQCoh.derivedPushforwardCochainUnit` — the derivation unit of
  `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` read on *cochain* complexes rather than on the homotopy category,
  which is the shape `Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` asks for.
* `Stacks.DerivedQCoh.comparisonPushforwardSquare` — the commuting square of
  [Stacks, Tag 08D7] at an arbitrary model of the derived categories, after composing with the
  fully faithful inclusions `D_QCoh ⥤ D`.

## Main results

* `Stacks.DerivedQCoh.derivedPushforward_isRightDerivedFunctor` — the derived direct image at an
  arbitrary model is a total right derived functor of `f_*` for the quasi-isomorphisms of cochain
  complexes.
* `Stacks.DerivedQCoh.affineOpenPushforwardCompatible` — **the hypothesis of
  [Stacks, Tag 09T6] holds for every scheme with affine diagonal.**

## Implementation notes

**Why 08D7's square is re-derived here.**
`AlgebraicGeometry.mapDerivedCategoryQuasicoherentPushforwardCompιIso` and
`AlgebraicGeometry.derivedQuasicoherentComparisonSquare` carry no `HasDerivedCategory` binder, so
instance search reads them at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. The hypothesis
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` quantifies over the model of the derived
categories of `U` — it has to, since the two derived categories of `X` are binders of the
statement and the ones of `U` appear only inside it — so the square is needed at an arbitrary
model. Every input to the proof in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffineDerivedPushforward.lean` is already
stated at an arbitrary model, in the `AlgebraicGeometry.AnyModel` namespace of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean`, so
`Stacks.DerivedQCoh.isIso_whiskerLeft_derivedPushforwardUnit` and
`Stacks.DerivedQCoh.mapDerivedCategoryQuasicoherentPushforwardCompιIso` repeat those two proofs
with the model a binder and nothing else changed.

**Why the derivation unit is rebuilt on cochain complexes.**
`AlgebraicGeometry.AnyModel.derivedPushforward` is a total right derived functor along the
localization `CategoryTheory.DerivedCategory.Qh` of the *homotopy* category, whereas
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` — following [Stacks, Tag 08D8] in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/FlatPushforward.lean` — asks for the unit
along the localization `CategoryTheory.DerivedCategory.Q` of the cochain complexes. The same
functor serves both: `Stacks.DerivedQCoh.derivedPushforwardCochainUnit` is the homotopy-category
unit restricted along `CategoryTheory.HomotopyCategory.quotient`, and it is recognised as a
cochain-level derived functor by Spaltenstein's criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`,
whose hypothesis is exactly the invertibility of the homotopy-category unit at the K-injective
complexes.

On the quasi-coherent side no such work is needed: `f_*` is exact on quasi-coherent modules for an
affine `f`, so `CategoryTheory.Functor.mapDerivedCategory` is its derived functor with
`CategoryTheory.Functor.mapDerivedCategoryFactors` for a unit.

**The two spellings of the module category.** `AlgebraicGeometry.pushforwardSheafOfModules` and
`Stacks.DerivedQCoh.modulesPushforward` are definitionally equal; the first is the spelling the
arbitrary-model results are stated in and the second the one
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` is stated in, and the terms below are
accepted at either type.

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentDerived
open AlgebraicGeometry.AnyModel (derivedPushforward derivedPushforwardUnit)

universe w u

namespace Stacks.DerivedQCoh

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} Y.ringCatSheaf)]

/-! ### The derived direct image as a derived functor on cochain complexes -/

/-- The composite of degreewise direct image with the localization of the target inverts the
quasi-isomorphisms between K-injective complexes.

An additive functor carries a quasi-isomorphism between K-injective complexes to a homotopy
equivalence, hence to a quasi-isomorphism, which the localization inverts. No affineness of `f` is
involved: this is the hypothesis under which the right derived functor *exists*. -/
theorem invertsQuasiIsoOfIsKInjective_pushforward :
    Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective
      ((pushforwardSheafOfModules f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf)) :=
  fun s hK hL hs =>
    Localization.inverts (DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf))
      (HomologicalComplex.quasiIso (SheafOfModules.{u} Y.ringCatSheaf) (ComplexShape.up ℤ)) _
      ((HomologicalComplex.mem_quasiIso_iff _).2
        (Stacks.Injectives.KInjectiveResolution.quasiIso_mapHomologicalComplex_map_of_isKInjective
          (pushforwardSheafOfModules f) s hK hL hs))

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- Restricting the degreewise direct image of homotopy categories along
`CategoryTheory.HomotopyCategory.quotient` gives back the degreewise direct image of cochain
complexes followed by the localization `CategoryTheory.DerivedCategory.Q`.

This is `CategoryTheory.Functor.mapHomotopyCategoryFactors` followed by
`CategoryTheory.DerivedCategory.quotientCompQhIso`, with the associators. -/
def pushforwardQuotientIsoLeft :
    HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ) ⋙
        AnyModel.pushforwardToDerivedCategory.{w} f ≅
      (pushforwardSheafOfModules f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((pushforwardSheafOfModules f).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} Y.ringCatSheaf))

/-- Restricting `Qh ⋙ Rf_*` along `CategoryTheory.HomotopyCategory.quotient` gives back
`Q ⋙ Rf_*`, by `CategoryTheory.DerivedCategory.quotientCompQhIso`. -/
def pushforwardQuotientIsoRight :
    HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙ derivedPushforward.{w} f ≅
      DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ derivedPushforward.{w} f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} X.ringCatSheaf))
      (derivedPushforward.{w} f)

/-- **The derivation unit of `Rf_*` on cochain complexes.** The comparison
`f_*K ⟶ Rf_*K` of `AlgebraicGeometry.AnyModel.derivedPushforwardUnit` lives on the homotopy
category; restricting it along `CategoryTheory.HomotopyCategory.quotient` and rewriting both ends
with `Stacks.DerivedQCoh.pushforwardQuotientIsoLeft` and
`Stacks.DerivedQCoh.pushforwardQuotientIsoRight` presents it as a natural transformation
`f_* ⋙ Q ⟶ Q ⋙ Rf_*` out of the cochain complexes, which is the shape
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` asks for. -/
def derivedPushforwardCochainUnit :
    (pushforwardSheafOfModules f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ derivedPushforward.{w} f :=
  (pushforwardQuotientIsoLeft.{w} f).inv ≫
    Functor.whiskerLeft
      (HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))
      (derivedPushforwardUnit.{w} f) ≫
    (pushforwardQuotientIsoRight.{w} f).hom

/-- The cochain-level derivation unit is invertible at every K-injective complex: it is the
homotopy-category unit conjugated by isomorphisms, and that unit is invertible at a K-injective
complex by `AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isKInjective`. -/
theorem isIso_derivedPushforwardCochainUnit_app_of_isKInjective
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (hK : K.IsKInjective) :
    IsIso ((derivedPushforwardCochainUnit.{w} f).app K) := by
  have := AnyModel.isIso_derivedPushforwardUnit_app_of_isKInjective.{w} f K hK
  dsimp only [derivedPushforwardCochainUnit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

/-- **The derived direct image is a total right derived functor of `f_*` on cochain complexes.**
Spaltenstein's criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`
reduces this to the invertibility of the unit at the K-injective complexes, which is
`Stacks.DerivedQCoh.isIso_derivedPushforwardCochainUnit_app_of_isKInjective`. -/
instance derivedPushforward_isRightDerivedFunctor :
    (derivedPushforward.{w} f).IsRightDerivedFunctor (derivedPushforwardCochainUnit.{w} f)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  (Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective
      (DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf)) _ _
      (invertsQuasiIsoOfIsKInjective_pushforward f)).2
    fun K hK => isIso_derivedPushforwardCochainUnit_app_of_isKInjective.{w} f K hK

/-! ### The commuting square of Stacks 08D7 at an arbitrary model -/

section Affine

variable [IsAffineHom f]

/-- **The comparison `f_* ⟶ Rf_*` is invertible on the whole image of `K(QCoh(𝒪_X))`**, at an
arbitrary model of the two derived categories.

This is `AlgebraicGeometry.isIso_whiskerLeft_derivedPushforwardUnit` with the model a binder; the
proof is the same, since its input
`AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom` — [Stacks, Tag 0G9N]
for an affine morphism — is already stated at an arbitrary model. -/
theorem isIso_whiskerLeft_derivedPushforwardUnit :
    IsIso (Functor.whiskerLeft
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPushforwardUnit.{w} f)) := by
  have hcomp : ∀ L, IsIso ((Functor.whiskerLeft
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory
        (ComplexShape.up ℤ)) (derivedPushforwardUnit.{w} f)).app L) := by
    intro L
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    exact (NatTrans.isIso_app_iff_of_iso (derivedPushforwardUnit.{w} f)
      (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app M)).2
      (AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom.{w} f
        (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) (fun n => (M.X n).2))
  exact NatIso.isIso_of_isIso_app _

variable [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory]

/-- **The functor induced by `f_*` on `D(QCoh(𝒪_X))` is a total right derived functor of it.**
Direct image is exact on quasi-coherent modules for an affine `f`, so no resolutions are involved
and `CategoryTheory.Functor.mapDerivedCategoryFactors` is the derivation unit. This is the first
assertion of [Stacks, Tag 08D7], read along the localization of the cochain complexes rather than
of the homotopy category. -/
instance quasicoherentPushforward_mapDerivedCategory_isRightDerivedFunctor :
    (quasicoherentPushforward f).mapDerivedCategory.IsRightDerivedFunctor
      (quasicoherentPushforward f).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (quasicoherentPushforward f).mapDerivedCategoryFactors

/-- **[Stacks, Tag 0G9N] for an affine morphism, as an isomorphism of functors on
`D(QCoh(𝒪_X))`**, at an arbitrary model of the derived categories.

This is `AlgebraicGeometry.mapDerivedCategoryQuasicoherentPushforwardCompιIso` with the model a
binder; the proof is the same. Both sides lift one functor on `K(QCoh(𝒪_X))` through the
localization `CategoryTheory.DerivedCategory.Qh`, and on `K(QCoh(𝒪_X))` the two differ exactly by
the comparison `f_* ⟶ Rf_*`, which is invertible there by
`Stacks.DerivedQCoh.isIso_whiskerLeft_derivedPushforwardUnit`. -/
def mapDerivedCategoryQuasicoherentPushforwardCompιIso :
    (quasicoherentPushforward f).mapDerivedCategory ⋙
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⋙
        derivedPushforward.{w} f :=
  haveI := isIso_whiskerLeft_derivedPushforwardUnit.{w} f
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory (ComplexShape.up ℤ))
    (((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory)
    (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ derivedPushforward.{w} f)
    _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (quasicoherentPushforward f ⋙
              (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι)) (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (quasicoherentPushforwardCompιIso f).symm
            (ComplexShape.up ℤ)).symm)
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      asIso (Functor.whiskerLeft
        ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory
          (ComplexShape.up ℤ)) (derivedPushforwardUnit.{w} f)) ≪≫
      (Functor.associator _ _ _).symm)

/-- **The commuting square of [Stacks, Tag 08D7], after the inclusions `D_QCoh ⥤ D`.** For an
affine morphism `f : X ⟶ Y` of schemes and an arbitrary model of the four derived categories, the
functor induced by `f_*` on `D(QCoh(𝒪_X))`, followed by the comparison functor of
[Stacks, Tag 06VT] over `Y` and the inclusion of the complexes with quasi-coherent cohomology,
agrees with the comparison functor over `X`, the inclusion, and the derived direct image.

This is the square of the hypothesis of [Stacks, Tag 09T6]. Composing with the inclusions is what
avoids having to choose a factorisation of `Rf_*` through `D_QCoh(𝒪_Y)`: the comparison functor
followed by the inclusion is the derived inclusion of the quasi-coherent modules
(`Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonCompι`), and in that
form the square is
`Stacks.DerivedQCoh.mapDerivedCategoryQuasicoherentPushforwardCompιIso`. -/
def comparisonPushforwardSquare :
    (quasicoherentPushforward f).mapDerivedCategory ⋙ derivedQuasicoherentComparison.{w} Y ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ≅
      derivedQuasicoherentComparison.{w} X ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ derivedPushforward.{w} f :=
  Functor.isoWhiskerLeft _ (derivedQuasicoherentComparisonCompι.{w} Y) ≪≫
    mapDerivedCategoryQuasicoherentPushforwardCompιIso.{w} f ≪≫
    Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι.{w} X).symm
      (derivedPushforward.{w} f) ≪≫
    Functor.associator _ _ _

end Affine

/-! ### The hypothesis of Stacks 09T6 on a scheme with affine diagonal -/

/-- **The hypothesis of [Stacks, Tag 09T6] holds for every scheme with affine diagonal.** Let `X`
be a scheme whose diagonal over the terminal scheme is an affine morphism — equivalently, a scheme
whose pairwise intersections of affine opens are affine; separated schemes and affine schemes are
examples. Then for every affine open `U ⊆ X` there are a total right derived functor
`Rj_* : D(𝒪_U) ⥤ D(𝒪_X)` of pushforward of all modules and a total right derived functor
`Φ : D(QCoh(𝒪_U)) ⥤ D(QCoh(𝒪_X))` of `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)` fitting into the commutative
square `i_X ∘ Φ ≅ Rj_* ∘ i_U` of [Stacks, Tag 09T6]; that is,
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible X` holds.

This is the source's own verification, in the proof of [Stacks, Tag 08DB]: the inclusion
`j : U ⟶ X` of an affine open is an affine morphism, because `U` is affine and `X` has affine
diagonal (`Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source`), and for
an affine morphism the square is the commuting square of [Stacks, Tag 08D7], here
`Stacks.DerivedQCoh.comparisonPushforwardSquare`. The witnesses are
`AlgebraicGeometry.AnyModel.derivedPushforward` with the derivation unit
`Stacks.DerivedQCoh.derivedPushforwardCochainUnit`, and
`CategoryTheory.Functor.mapDerivedCategory` of `j_*` with the derivation unit
`CategoryTheory.Functor.mapDerivedCategoryFactors`.

Affine diagonal cannot be dropped: an affine open immersion into a quasi-compact quasi-separated
scheme need not be an affine morphism, and the square then fails. -/
theorem affineOpenPushforwardCompatible (X : Scheme.{u})
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory] :
    AffineOpenPushforwardCompatible X := by
  intro U hU _ _ _ _
  have : IsAffine U.toScheme := hU
  have : IsAffineHom U.ι :=
    Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source U.ι
  exact ⟨derivedPushforward.{w} U.ι, derivedPushforwardCochainUnit.{w} U.ι,
    (quasicoherentPushforward U.ι).mapDerivedCategory,
    (quasicoherentPushforward U.ι).mapDerivedCategoryFactors.inv,
    derivedPushforward_isRightDerivedFunctor.{w} U.ι,
    quasicoherentPushforward_mapDerivedCategory_isRightDerivedFunctor.{w} U.ι,
    ⟨comparisonPushforwardSquare.{w} U.ι⟩⟩

/-- **The hypothesis of [Stacks, Tag 09T6] holds for every separated scheme.** A separated scheme
has a closed, hence affine, diagonal, so
`Stacks.DerivedQCoh.affineOpenPushforwardCompatible` applies.

This records that `Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` is not vacuous at a
recognisable class of schemes larger than the affine ones. -/
theorem affineOpenPushforwardCompatible_of_isSeparated (X : Scheme.{u})
    [IsSeparated (Limits.terminal.from X)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory] :
    AffineOpenPushforwardCompatible X :=
  affineOpenPushforwardCompatible.{w} X

end Stacks.DerivedQCoh

end
