module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# The derived coherator as quasi-inverse of the comparison functor

Let `X` be a scheme. The inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` of the quasi-coherent modules is
exact and has a right adjoint, the coherator `Q_X` ([Stacks, Tag 077P]); write `RQ_X` for a total
right derived functor of `Q_X`. [Stacks, Tag 06VT] provides the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`. This file proves the *second* clause of
[Stacks, Tag 09T6]: **once `i_X` is known to be an equivalence, its quasi-inverse is `RQ_X`**,
restricted to the complexes with quasi-coherent cohomology — and this for an arbitrary scheme and
an arbitrary right-derived model of `Q_X`.

The argument is the formal one. The adjunction `ι ⊣ Q_X` derives to an adjunction between the
functor of derived categories induced by the exact `ι` and the derived functor `RQ_X`
([Stacks, Tag 09T5], available at arbitrary chosen models as
`Stacks.DerivedModel.adjunctionOfExact`). Composing `i_X` with the inclusion
`J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` recovers that induced functor, so restricting the derived adjunction
along the fully faithful `J` exhibits `J ⋙ RQ_X` as a right adjoint of `i_X`. A right adjoint is
unique up to a unique natural isomorphism, and the inverse of an equivalence is one of its right
adjoints.

## Main definitions

* `Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` — the *hypothesis* of
  [Stacks, Tag 09T6]: for every affine open `U ⊆ X` the right derived functor `Φ` of
  `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)` fits into the source's commutative square
  `i_X ∘ Φ ≅ Rj_* ∘ i_U`.
* `Stacks.DerivedQCoh.comparisonDerivedCoheratorAdjunction` — the comparison functor of
  [Stacks, Tag 06VT] is left adjoint to the restricted derived coherator.

## Main results

* `Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory` — the functor of derived
  categories induced by an exact functor at the chosen models of
  `Stacks.DerivedModel.derivedFunctorOfExact` agrees with Mathlib's
  `CategoryTheory.Functor.mapDerivedCategory` when the chosen localizations are
  `CategoryTheory.DerivedCategory.Q`.
* `Stacks.DerivedQCoh.derivedCoherator_isoInv` — **[Stacks, Tag 09T6], quasi-inverse clause**:
  if the comparison functor is an equivalence, then `J ⋙ RQ_X` is its inverse.
* `Stacks.DerivedQCoh.affineDerivedCoherator_isoInv` — the same conclusion on `Spec R`, where
  the equivalence is already available; this exhibits a scheme at which every hypothesis of
  `Stacks.DerivedQCoh.derivedCoherator_isoInv` is satisfied.

## Implementation notes

**What is proved and what is not.** [Stacks, Tag 09T6] asserts, under
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible`, that `i_X` *is an equivalence* and that its
quasi-inverse *is* `RQ_X`. Only the second clause is established here, and it is established from
the equivalence rather than from the affine-open hypothesis: the first clause is the source's
induction on the number of affine opens needed to cover the support, and it is not carried out in
this file. Accordingly the tag on `Stacks.DerivedQCoh.derivedCoherator_isoInv` carries the
qualifier `"quasi-inverse clause, given the equivalence"`, and
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` is recorded but **not** consumed: it is the
input of the clause that is missing, written out so that the missing clause has a statement.

The derived categories are instance arguments, as in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/WeakSerre/DerivedComparison.lean` and
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/FlatPushforward.lean`: the standard model
puts the morphisms of `D(𝒪_X)` a universe above its objects, so no statement about `D(𝒪_X)` may
pin it. The chosen localization of the cochain complexes is `CategoryTheory.DerivedCategory.Q` at
those free instances, which is what `CategoryTheory.Functor.mapDerivedCategory` — and hence the
comparison functor of [Stacks, Tag 06VT] — is built from; the bridge
`Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory` is what connects that choice to
the arbitrary-model machinery of
`StacksFrontier/Homology/Injectives/DerivedCategory/ArbitraryModel.lean`.

The commutative square of the hypothesis is stated after composing with the fully faithful
inclusions `J : D_QCoh ⥤ D`, i.e. as `Φ ⋙ i_X ⋙ J_X ≅ i_U ⋙ J_U ⋙ Rj_*` with
`Rj_* : D(𝒪_U) ⥤ D(𝒪_X)` on the ambient derived categories. This is the source's square: `J` is
fully faithful and `Rj_*` carries quasi-coherent cohomology to quasi-coherent cohomology for a
quasi-compact quasi-separated `j`, so a square over the ambient categories is the same datum as
one over the subcategories, and this spelling avoids having to choose the factorisation of `Rj_*`
through `D_QCoh(𝒪_X)` as part of the hypothesis.

`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` quantifies over the affine opens of `X` and
asserts the *existence* of the two derived functors together with their derivation units, rather
than naming a particular model: the source says "the right derived functor", and a right derived
functor is unique only up to canonical isomorphism. The derivation units are stated at the
cochain-complex level, matching [Stacks, Tag 08D8] in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/FlatPushforward.lean`.

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe w v u

namespace Stacks.DerivedQCoh

/-! ### Pushforward of modules in the `SheafOfModules` spelling -/

/-- Pushforward of all modules along a morphism of schemes, with domain and codomain spelled
`SheafOfModules.{u} X.ringCatSheaf` rather than `AlgebraicGeometry.Scheme.Modules X`.

The two spellings of the module category are definitionally equal but carry separately declared
`Category` instances, hence separately declared `HasDerivedCategory` instances; this ascription
moves pushforward to the spelling in which the comparison functor of [Stacks, Tag 06VT] is
stated, so that one derived category of modules serves both. This is the same device as
`AlgebraicGeometry.quasicoherentModulesι`. -/
def modulesPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} Y.ringCatSheaf :=
  Scheme.Modules.pushforward f

/-- `Stacks.DerivedQCoh.modulesPushforward` is additive, being pushforward of all modules. -/
instance modulesPushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modulesPushforward f).Additive :=
  inferInstanceAs ((Scheme.Modules.pushforward f).Additive)

/-- The coherator `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` of [Stacks, Tag 077P], with domain spelled
`SheafOfModules.{u} X.ringCatSheaf`, for the reason recorded at
`Stacks.DerivedQCoh.modulesPushforward`. -/
def modulesCoherator (X : Scheme.{u}) :
    SheafOfModules.{u} X.ringCatSheaf ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  coherator X

/-- `Stacks.DerivedQCoh.modulesCoherator` is additive, being a right adjoint of an additive
functor. -/
instance modulesCoherator_additive (X : Scheme.{u}) : (modulesCoherator X).Additive :=
  inferInstanceAs ((coherator X).Additive)

/-- **The coherator adjunction** of [Stacks, Tag 077P] in the `SheafOfModules` spelling: the
inclusion of the quasi-coherent modules is left adjoint to the coherator. -/
def modulesCoheratorAdjunction (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⊣ modulesCoherator X :=
  coheratorAdjunction X

/-! ### The induced functor of chosen derived categories at the standard localization -/

section Bridge

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [CategoryWithHomology A]

/-- At the chosen localization `CategoryTheory.DerivedCategory.Q`, the factorisation
`Stacks.DerivedModel.homotopyLocalization` of the cochain complexes through the homotopy category
is `CategoryTheory.DerivedCategory.Qh`.

By construction the factorisation is `Qh` followed by the comparison equivalence between the
standard model and the chosen one, and for the chosen model *equal* to the standard one that
comparison lifts the identity: both it and `𝟭` lift `Q` along `Q`, and a lift is unique up to a
unique natural isomorphism. -/
def homotopyLocalizationQIso :
    Stacks.DerivedModel.homotopyLocalization (DerivedCategory.Q (C := A)) ≅
      DerivedCategory.Qh (C := A) := by
  letI : Localization.Lifting (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory.Q (C := A))
      (Localization.uniq (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor :=
    ⟨Localization.compUniqFunctor _ _ _⟩
  letI : Localization.Lifting (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory.Q (C := A))
      (𝟭 (DerivedCategory A)) := ⟨Functor.rightUnitor _⟩
  have hU : (Localization.uniq (DerivedCategory.Q (C := A)) (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).functor ≅ 𝟭 _ :=
    Localization.liftNatIso (DerivedCategory.Q (C := A))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (DerivedCategory.Q (C := A))
      (DerivedCategory.Q (C := A)) _ _ (Iso.refl _)
  exact Functor.isoWhiskerLeft (DerivedCategory.Qh (C := A)) hU ≪≫ Functor.rightUnitor _

variable {A} {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
  [CategoryWithHomology B] (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G]

/-- **The arbitrary-model induced functor of an exact functor agrees with Mathlib's.** At the
chosen localizations `CategoryTheory.DerivedCategory.Q`, the functor
`Stacks.DerivedModel.derivedFunctorOfExact G` coincides with
`CategoryTheory.Functor.mapDerivedCategory`.

Both lift the degreewise functor followed by `Qh` along the localization `Qh` of the homotopy
category, the first by `Stacks.DerivedModel.derivedFunctorOfExactFac` composed with
`Stacks.DerivedQCoh.homotopyLocalizationQIso`, the second by
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, and a lift is unique up to a unique natural
isomorphism. -/
def derivedFunctorOfExactIsoMapDerivedCategory :
    Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
      (DerivedCategory.Q (C := B)) ≅ G.mapDerivedCategory := by
  letI : Localization.Lifting (DerivedCategory.Qh (C := B))
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := A))
      (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
        (DerivedCategory.Q (C := B))) :=
    ⟨Functor.isoWhiskerRight (homotopyLocalizationQIso B).symm _ ≪≫
      Stacks.DerivedModel.derivedFunctorOfExactFac G _ _ ≪≫
      Functor.isoWhiskerLeft _ (homotopyLocalizationQIso A)⟩
  letI : Localization.Lifting (DerivedCategory.Qh (C := B))
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := A))
      G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactorsh⟩
  exact Localization.liftNatIso (DerivedCategory.Qh (C := B))
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := A))
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := A))
    (Stacks.DerivedModel.derivedFunctorOfExact G (DerivedCategory.Q (C := A))
      (DerivedCategory.Q (C := B))) G.mapDerivedCategory (Iso.refl _)

end Bridge

/-! ### The hypothesis of Stacks 09T6 -/

/-- **The hypothesis of [Stacks, Tag 09T6].** For every affine open `U ⊆ X` the right derived
functor `Φ : D(QCoh(𝒪_U)) ⥤ D(QCoh(𝒪_X))` of the left exact
`j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)` fits into the commutative diagram

```
D(QCoh(𝒪_U)) --i_U--> D_QCoh(𝒪_U)
     | Φ                  | Rj_*
     v                     v
D(QCoh(𝒪_X)) --i_X--> D_QCoh(𝒪_X)
```

where `i_U`, `i_X` are the comparison functors of [Stacks, Tag 06VT] and `Rj_*` is a total right
derived functor of pushforward of all modules along `j : U ⟶ X`.

Both derived functors are asserted to *exist*, each together with its derivation unit relative to
`CategoryTheory.DerivedCategory.Q`, rather than fixed: the source says "the right derived
functor", which is determined only up to canonical isomorphism. The square is stated after
composing with the fully faithful inclusions of `D_QCoh` into the ambient derived categories, so
that no factorisation of `Rj_*` through `D_QCoh(𝒪_X)` has to be chosen as part of the
hypothesis. -/
def AffineOpenPushforwardCompatible (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory] :
    Prop :=
  ∀ (U : X.Opens), IsAffineOpen U →
    ∀ [QuasiCompact U.ι] [QuasiSeparated U.ι]
      [HasDerivedCategory.{w} (SheafOfModules.{u} U.toScheme.ringCatSheaf)]
      [HasDerivedCategory.{w}
        (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory],
      ∃ (Rj : DerivedCategory (SheafOfModules.{u} U.toScheme.ringCatSheaf) ⥤
          DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
        (ηj : (modulesPushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⟶
          DerivedCategory.Q (C := SheafOfModules.{u} U.toScheme.ringCatSheaf) ⋙ Rj)
        (Φ : DerivedCategory
            (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
          DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
        (ηΦ : (quasicoherentPushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q
              (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
          DerivedCategory.Q
              (C := (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory) ⋙
            Φ),
        Rj.IsRightDerivedFunctor ηj
            (HomologicalComplex.quasiIso (SheafOfModules.{u} U.toScheme.ringCatSheaf)
              (ComplexShape.up ℤ)) ∧
          Φ.IsRightDerivedFunctor ηΦ
            (HomologicalComplex.quasiIso
              (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory
              (ComplexShape.up ℤ)) ∧
          Nonempty (Φ ⋙ derivedQuasicoherentComparison.{w} X ⋙
              (DerivedCategoryB.derivedCategoryB
                (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
            derivedQuasicoherentComparison.{w} U.toScheme ⋙
              (DerivedCategoryB.derivedCategoryB
                (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι ⋙ Rj)

/-! ### The quasi-inverse clause -/

section QuasiInverse

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]
  (RQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
    DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
  (RQUnit : (modulesCoherator X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q
        (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) ⟶
    DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf) ⋙ RQ)
  [RQ.IsRightDerivedFunctor RQUnit
    (HomologicalComplex.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))]

/-- The derived form of the coherator adjunction: the functor of chosen derived categories induced
by the exact inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is left adjoint to any total right derived
functor of the coherator. This is [Stacks, Tag 09T5] for `ι ⊣ Q_X`. -/
def derivedCoheratorAdjunction :
    Stacks.DerivedModel.derivedFunctorOfExact
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
        (DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf))
        (DerivedCategory.Q
          (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)) ⊣ RQ :=
  Stacks.DerivedModel.adjunctionOfExact
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
    (DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf))
    (DerivedCategory.Q
      (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory))
    (modulesCoheratorAdjunction X) RQ RQUnit

/-- Composing the comparison functor of [Stacks, Tag 06VT] with the inclusion of the complexes
with quasi-coherent cohomology gives the functor of derived categories induced by the exact
inclusion of the quasi-coherent modules, in the arbitrary-model spelling. -/
def comparisonCompιIsoDerivedFunctorOfExact :
    derivedQuasicoherentComparison.{w} X ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
      Stacks.DerivedModel.derivedFunctorOfExact
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
        (DerivedCategory.Q (C := SheafOfModules.{u} X.ringCatSheaf))
        (DerivedCategory.Q
          (C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)) :=
  derivedQuasicoherentComparisonCompι.{w} X ≪≫
    (derivedFunctorOfExactIsoMapDerivedCategory
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).symm

/-- **The comparison functor of [Stacks, Tag 06VT] is left adjoint to the restricted derived
coherator.** For an arbitrary scheme `X` and an arbitrary total right derived functor `RQ_X` of
the coherator, `i_X ⊣ J ⋙ RQ_X`, where `J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)`.

This is `Stacks.DerivedQCoh.derivedCoheratorAdjunction` restricted along the identity of
`D(QCoh(𝒪_X))` and along the fully faithful `J`, which is legitimate because `i_X ⋙ J` is the
left adjoint of that adjunction. -/
def comparisonDerivedCoheratorAdjunction :
    derivedQuasicoherentComparison.{w} X ⊣
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RQ :=
  (derivedCoheratorAdjunction X RQ RQUnit).restrictFullyFaithful
    (Functor.FullyFaithful.id _)
    (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι)
    (Functor.leftUnitor _ ≪≫ (comparisonCompιIsoDerivedFunctorOfExact X).symm)
    (Functor.rightUnitor _).symm

/-- **[Stacks, Tag 09T6], quasi-inverse clause.** Let `X` be a scheme whose comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT] is an equivalence, and let `RQ_X` be any
total right derived functor of the coherator `Q_X`. Then the quasi-inverse of `i_X` is `RQ_X`
restricted to the complexes with quasi-coherent cohomology.

`Stacks.DerivedQCoh.comparisonDerivedCoheratorAdjunction` exhibits that restriction as a right
adjoint of `i_X`, the inverse of an equivalence is another, and a right adjoint is unique up to a
unique natural isomorphism.

This is the second clause of the conclusion of [Stacks, Tag 09T6], deduced from the first clause
rather than from the tag's affine-open hypothesis
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible`; the first clause — that the comparison
functor is an equivalence — is the source's induction on the number of affine opens covering the
support, and is not proved here. -/
@[stacks 09T6 "quasi-inverse clause, given the equivalence"]
def derivedCoherator_isoInv [(derivedQuasicoherentComparison.{w} X).IsEquivalence] :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RQ ≅
      (derivedQuasicoherentComparison.{w} X).inv :=
  Adjunction.rightAdjointUniq (comparisonDerivedCoheratorAdjunction X RQ RQUnit)
    (derivedQuasicoherentComparison.{w} X).asEquivalence.toAdjunction

end QuasiInverse

/-! ### The affine case: the hypotheses are satisfiable -/

section Affine

open Stacks.Injectives.KInjectiveResolution (hasRightDerivedFunctor_mapHomologicalComplex_comp_Q)

variable (R : CommRingCat.{u})

/-- **The derived coherator of `Spec R`** at the cochain-complex level: the total right derived
functor of `Q_{Spec R}` relative to `CategoryTheory.DerivedCategory.Q`. It exists because
`Mod(𝒪_{Spec R})` is Grothendieck abelian, so every cochain complex has a K-injective
resolution. -/
def affineDerivedCoherator :
    DerivedCategory (SheafOfModules.{u} (Spec R).ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator (Spec R))
  ((modulesCoherator (Spec R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Spec R).ringCatSheaf)
        (ComplexShape.up ℤ))

/-- The derivation unit of `Stacks.DerivedQCoh.affineDerivedCoherator`. -/
def affineDerivedCoheratorUnit :
    (modulesCoherator (Spec R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q
          (C := (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} (Spec R).ringCatSheaf) ⋙
        affineDerivedCoherator R :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator (Spec R))
  ((modulesCoherator (Spec R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Spec R).ringCatSheaf)
        (ComplexShape.up ℤ))

/-- `Stacks.DerivedQCoh.affineDerivedCoherator` is a total right derived functor of the coherator
of `Spec R`, which is the universal property characterising it. -/
instance affineDerivedCoherator_isRightDerivedFunctor :
    (affineDerivedCoherator R).IsRightDerivedFunctor (affineDerivedCoheratorUnit R)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Spec R).ringCatSheaf)
        (ComplexShape.up ℤ)) :=
  haveI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (modulesCoherator (Spec R))
  inferInstanceAs ((((modulesCoherator (Spec R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Spec R).ringCatSheaf)
        (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((modulesCoherator (Spec R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Spec R).ringCatSheaf)
        (ComplexShape.up ℤ)))
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Spec R).ringCatSheaf)
      (ComplexShape.up ℤ)))

/-- **The quasi-inverse clause holds on an affine scheme.** On `X = Spec R` the comparison functor
is an equivalence by `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`, so
`Stacks.DerivedQCoh.derivedCoherator_isoInv` applies and identifies its inverse with the derived
coherator restricted to the complexes with quasi-coherent cohomology.

This records that the hypotheses of `Stacks.DerivedQCoh.derivedCoherator_isoInv` are
simultaneously satisfiable: a scheme, a total right derived functor of its coherator with its
derivation unit, and the equivalence. It is the conclusion of [Stacks, Tag 09T6] for an affine
scheme, where the tag's affine-open hypothesis is not needed because the equivalence is already
available. -/
theorem affineDerivedCoherator_isoInv :
    letI := derivedQuasicoherentComparison_isEquivalence R
    Nonempty ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
          affineDerivedCoherator R ≅
      (derivedQuasicoherentComparison.{u} (Spec R)).inv) :=
  let := derivedQuasicoherentComparison_isEquivalence R
  ⟨derivedCoherator_isoInv (Spec R) (affineDerivedCoherator R) (affineDerivedCoheratorUnit R)⟩

end Affine

end Stacks.DerivedQCoh

end
