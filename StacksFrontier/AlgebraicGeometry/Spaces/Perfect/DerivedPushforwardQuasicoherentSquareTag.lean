module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardQuasicoherentSquare
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0CSR: the derived direct image on quasi-coherent modules is `Rf_*`

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, with `X` and `Y`
quasi-compact with affine diagonal over `ℤ`, and let `Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` be the
right derived functor of `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`.  [Stacks, Tag 0CSR] says that the square

`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X) ⟶^{Rf_*} D_QCoh(𝒪_Y)`,
`D(QCoh(𝒪_X)) ⟶^{Φ} D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y)`

commutes, its rows being the comparison functors of [Stacks, Tag 08F1].

## Main results

* `AlgebraicGeometry.Space.derivedQuasicoherentPushforwardSquare` — **[Stacks, Tag 0CSR]**.
* `pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isQuasiCompactWithAffineDiagonal`
  — the property `P(X)` of the source's proof, for every quasi-compact `X` with affine diagonal.

## Implementation notes

The square is constructed by `derivedQuasicoherentPushforwardSquareOfComputes`, which runs the
source's induction given that the derived inclusions `D(QCoh(𝒪_W)) ⥤ D(𝒪_W)` are fully faithful
for the quasi-compact `W` with affine diagonal; this is where the source uses [Stacks, Tag 08H1],
and here it is discharged by
`AlgebraicGeometry.Space.quasicoherentDerivedComparison_isEquivalence_of_isAffineHom_diag`.

As for [Stacks, Tag 08GY], the square is stated inside `D(𝒪_Y)`, after the fully faithful
inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` on both corners of the right-hand column, which is an
equivalent assertion: the right edge inside `D_QCoh` is the restriction of `Rf_*`, and the source's
`Rf_*` is any right derived functor of the direct image of all modules, here the binders `Rf`, `α`.
The isomorphism is the canonical comparison `Stacks.DerivedCoherator.pushforwardSquareComparison`
read through the comparison functors.

`HasDerivedCategory.standard` is a local instance: it is the model of the derived categories in
which the comparison functor of [Stacks, Tag 08F1] is stated.

## References

* [Stacks Project, Tag 0CSR](https://stacks.math.columbia.edu/tag/0CSR)
* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **[Stacks, Tag 08H1] as full faithfulness.**  For a quasi-compact algebraic space `W` with
affine diagonal over `ℤ`, the derived inclusion `D(QCoh(𝒪_W)) ⥤ D(𝒪_W)` is fully faithful. -/
theorem full_faithful_mapDerivedCategory_of_isQuasiCompactWithAffineDiagonal
    (W : AlgebraicSpaces B S hS) (hW : IsQuasiCompactWithAffineDiagonal B S hS hZ W.1) :
    ((quasicoherentSheavesι B S hS W).mapDerivedCategory).Full ∧
      ((quasicoherentSheavesι B S hS W).mapDerivedCategory).Faithful :=
  have : (quasicoherentDerivedComparisonSchemeUniverse B S hS W.1 W.2).IsEquivalence :=
    quasicoherentDerivedComparison_isEquivalence_of_isAffineHom_diag B S hS W hZ hW.1 hW.2
  full_faithful_mapDerivedCategory_of_isEquivalence B S hS W

/-- **The property `P(X)` of the proof of [Stacks, Tag 0CSR].**  For a quasi-compact algebraic
space `X` with affine diagonal over `ℤ`, every `g : X ⟶ Z` to a quasi-compact algebraic space with
affine diagonal, and every K-injective complex `I` of `QCoh(𝒪_X)`, `g_* I` computes `Rg_* I`. -/
theorem pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isQuasiCompactWithAffineDiagonal
    (X : AlgebraicSpaces B S hS) (hX : IsQuasiCompactWithAffineDiagonal B S hS hZ X.1) :
    PushforwardComputesDerivedOnQuasicoherentKInjectives B S hS hZ X :=
  pushforwardComputesDerivedOnQuasicoherentKInjectives_of_fullyFaithful B S hS hZ
    (full_faithful_mapDerivedCategory_of_isQuasiCompactWithAffineDiagonal B S hS hZ) X hX

/-- **[Stacks, Tag 0CSR].**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`,
with `X` and `Y` quasi-compact with affine diagonal over `ℤ`.  Let `Φ` be a right derived functor
of `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` with unit `αΦ`, and `Rf_*` a right derived functor of the
direct image of all modules with unit `α`.  Then the square

`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X) ⟶^{Rf_*} D_QCoh(𝒪_Y)`,
`D(QCoh(𝒪_X)) ⟶^{Φ} D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y)`

commutes, its rows being the comparison functors of [Stacks, Tag 08F1]; it is stated after the
fully faithful inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`, as for [Stacks, Tag 08GY].

`f_*` preserves quasi-coherence because `f` is quasi-compact and quasi-separated
([Stacks, Tag 03M9]), by
`AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_isQuasiCompactWithAffineDiagonal`.
The isomorphism is the canonical comparison of the two right derived functors. -/
@[stacks 0CSR]
def derivedQuasicoherentPushforwardSquare {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X.1)))
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ Y.1)))
    (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2))
    (αΦ : (quasicoherentPushforward B S hS f
        (pushforwardPreservesQuasicoherence_of_isQuasiCompactWithAffineDiagonal B S hS hZ f
          ⟨hXqc, hXdiag⟩ ⟨hYqc, hYdiag⟩)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Φ)
    [Φ.IsRightDerivedFunctor αΦ
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    Φ ⋙ quasicoherentDerivedComparisonSchemeUniverse B S hS Y.1 Y.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι ≅
      quasicoherentDerivedComparisonSchemeUniverse B S hS X.1 X.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⋙ Rf :=
  derivedQuasicoherentPushforwardSquareOfComputes B S hS hZ f ⟨hXqc, hXdiag⟩ ⟨hYqc, hYdiag⟩ Φ αΦ
    Rf α (pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isQuasiCompactWithAffineDiagonal
      B S hS hZ X ⟨hXqc, hXdiag⟩)

end AlgebraicGeometry.Space

end
