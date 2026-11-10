module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QuasicoherentDerivedEquivalenceCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardQuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
import StacksCore.Tactic.StacksAttribute

/-!
# The derived category of quasi-coherent modules: Stacks 09TG and 08H1

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` contained in a
big fppf site `B`.

* **[Stacks, Tag 09TG], equivalence clause.**  If for every étale `j : V ⟶ W` with `W ⊆ X` a
  quasi-compact open and `V` affine the right derived functor `Φ` of
  `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` fits into the commutative square with `Rj_*` and the comparison
  functors (`AlgebraicGeometry.Space.ExistsAffineEtaleDerivedPushforwardSquare`), then the
  comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence.
  The quasi-inverse clause is `AlgebraicGeometry.Space.derivedCoherator_isoInv`.
* **[Stacks, Tag 08H1].**  If `X` is quasi-compact with affine diagonal over `ℤ`, then `i_X` is an
  equivalence with quasi-inverse `RQ_X`.

## Main results

* `quasicoherentDerivedComparison_isEquivalence_of_affineEtaleDerivedPushforwardSquareCommutes`
  (in `AlgebraicGeometry.Space`) — Stacks 09TG, the equivalence.
* `AlgebraicGeometry.Space.affineEtaleDerivedPushforwardSquareCommutes_of_isAffineHom_diag` —
  the hypothesis of 09TG on a quasi-compact space with affine diagonal.
* `AlgebraicGeometry.Space.quasicoherentDerivedComparison_isEquivalence_of_isAffineHom_diag` —
  Stacks 08H1, the equivalence.
* `AlgebraicGeometry.Space.exists_equivalence_functor_eq_and_inverse_eq_derivedCoherator` —
  Stacks 08H1: an equivalence whose functor is `i_X` and whose inverse is `RQ_X` on
  `D_QCoh(𝒪_X)`, realised by
  `AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsAffineHomDiag`.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### Stacks 09TG -/

section Criterion

/-- The direct image along an étale morphism from an affine algebraic space to a quasi-separated
one preserves quasi-coherence (Stacks 03M9). -/
theorem pushforwardPreservesQuasicoherence_of_isAffineSpace_of_isAbsolutelyQuasiSeparated
    {V : AlgebraicSpaces B S hS} (g : V ⟶ X) (hV : IsAffineSpace B S hS V.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    PushforwardPreservesQuasicoherence B S hS g := fun M hM =>
  isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS g
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs hV.isQuasiCompactSpace g.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ V.2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hV) g.hom) M hM

/-- Let `X` be a quasi-compact and quasi-separated algebraic space over `S`.  Suppose that for
every étale morphism `j : V ⟶ W` with `W ⊆ X` a quasi-compact open and `V` affine, the right
derived functor `Φ` of `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` fits into the commutative square
`i_W ∘ Φ ≅ Rj_* ∘ i_V` (`AlgebraicGeometry.Space.ExistsAffineEtaleDerivedPushforwardSquare`).
Then the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an
equivalence. -/
@[stacks 09TG "equivalence clause"]
theorem quasicoherentDerivedComparison_isEquivalence_of_affineEtaleDerivedPushforwardSquareCommutes
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (h : ExistsAffineEtaleDerivedPushforwardSquare B S hS X.1 X.2) :
    (quasicoherentDerivedComparison B S hS X.1 X.2).IsEquivalence := by
  refine quasicoherentDerivedComparison_isEquivalence_of_forall_affineEtale B S hS X hZ
    hXqc hXqs fun V g hg hV => ?_
  have hpush := pushforwardPreservesQuasicoherence_of_isAffineSpace_of_isAbsolutelyQuasiSeparated
    B S hS X hZ g hV hXqs
  obtain ⟨Φ, βΦ, hΦ, Rj, βj, hRj, hsq⟩ := h X (𝟙 _)
    (isOpenImmersion_of_isIso B S hS _) hXqc V g hg hV hpush
  exact ⟨hpush, Rj, βj, hRj,
    (derivedPushforwardSquareCommutes_iff B S hS g hpush Φ βΦ hΦ Rj βj).1 hsq⟩

end Criterion

/-! ### Stacks 08H1 -/

section AffineDiagonal

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for the binary product behind `diag (viewOverIntegers ..)` needs more time.
/-- **The hypothesis of [Stacks, Tag 09TG] holds on a quasi-compact algebraic space with affine
diagonal over `ℤ`.** -/
theorem affineEtaleDerivedPushforwardSquareCommutes_of_isAffineHom_diag
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X.1))) :
    ExistsAffineEtaleDerivedPushforwardSquare B S hS X.1 X.2 := by
  refine affineEtaleDerivedPushforwardSquareCommutes_of_kInjectives B S hS X.1 X.2
    fun W jW hjW hWqc V j _ hV _ => ?_
  have hW : IsQuasiCompactWithAffineDiagonal B S hS hZ W.1 :=
    IsQuasiCompactWithAffineDiagonal.of_openImmersion B S hS hZ X
      ⟨Over.mk (𝟙 X), by intro T φ hφ; simpa using hφ⟩ W.1 jW.hom ⟨hXqc, hXdiag⟩ W.2 hjW hWqc
  exact ⟨derivedModulePushforwardTotal B S hS j, derivedModulePushforwardTotalUnit B S hS j,
    inferInstance, fun I hI => (pushforwardComputesDerived_iff_isIso B S hS j _ _ _).1
      (pushforwardComputesDerivedOnQuasicoherentKInjectives_of_isAffineSpace B S hS hZ V hV W hW
        j I hI)⟩

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for the binary product behind `diag (viewOverIntegers ..)` needs more time.
/-- On a quasi-compact algebraic space with affine diagonal over `ℤ` the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence. -/
@[stacks 08H1 "equivalence"]
theorem quasicoherentDerivedComparison_isEquivalence_of_isAffineHom_diag
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X.1))) :
    (quasicoherentDerivedComparison B S hS X.1 X.2).IsEquivalence :=
  quasicoherentDerivedComparison_isEquivalence_of_affineEtaleDerivedPushforwardSquareCommutes
    B S hS X hZ hXqc
    (isAbsolutelyQuasiSeparated_of_isQuasiCompactWithAffineDiagonal B S hS hZ X ⟨hXqc, hXdiag⟩)
    (affineEtaleDerivedPushforwardSquareCommutes_of_isAffineHom_diag B S hS X hZ hXqc hXdiag)

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for the binary product behind `diag (viewOverIntegers ..)` needs more time.
/-- The equivalence of Stacks 08H1: its functor is the comparison functor `i_X`
(`AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsAffineHomDiag_functor`) and its
inverse is `RQ_X` on `D_QCoh(𝒪_X)`
(`AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsAffineHomDiag_inverse`). -/
def quasicoherentDerivedEquivalenceOfIsAffineHomDiag
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X.1)))
    (CF : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ CF)
    [CF.Additive]
    (RQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (RQUnit : CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ≌
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  have := quasicoherentDerivedComparison_isEquivalence_of_isAffineHom_diag B S hS X hZ hXqc
    hXdiag
  (quasicoherentDerivedComparison B S hS X.1 X.2).asEquivalence.changeInverse
    (derivedCoherator_isoInv B S hS X.1 X.2 CF adjF RQ RQUnit).symm

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for the binary product behind `diag (viewOverIntegers ..)` needs more time.
/-- The functor of the equivalence of Stacks 08H1 is the comparison functor `i_X`. -/
lemma quasicoherentDerivedEquivalenceOfIsAffineHomDiag_functor
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X.1)))
    (CF : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ CF)
    [CF.Additive]
    (RQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (RQUnit : CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    (quasicoherentDerivedEquivalenceOfIsAffineHomDiag B S hS X hZ hXqc hXdiag CF adjF RQ
      RQUnit).functor = quasicoherentDerivedComparison B S hS X.1 X.2 :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for the binary product behind `diag (viewOverIntegers ..)` needs more time.
/-- The inverse of the equivalence of Stacks 08H1 is `RQ_X` on `D_QCoh(𝒪_X)`. -/
lemma quasicoherentDerivedEquivalenceOfIsAffineHomDiag_inverse
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X.1)))
    (CF : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ CF)
    [CF.Additive]
    (RQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (RQUnit : CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    (quasicoherentDerivedEquivalenceOfIsAffineHomDiag B S hS X hZ hXqc hXdiag CF adjF RQ
      RQUnit).inverse =
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))).ι ⋙
        RQ :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for the binary product behind `diag (viewOverIntegers ..)` needs more time.
/-- Let `X` be a quasi-compact algebraic space with affine diagonal over `ℤ`, `C_X` a coherator
of `X` and `RQ_X` a total right derived functor of it.  Then the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence with quasi-inverse `RQ_X`
restricted to `D_QCoh(𝒪_X)`: there is an equivalence whose functor is `i_X` and whose inverse is
`J ⋙ RQ_X`, for `J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` the inclusion. -/
@[stacks 08H1 "equivalence with quasi-inverse RQ_X"]
theorem exists_equivalence_functor_eq_and_inverse_eq_derivedCoherator
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXdiag : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ X.1)))
    (CF : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ CF)
    [CF.Additive]
    (RQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (RQUnit : CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    ∃ e : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ≌
        QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      e.functor = quasicoherentDerivedComparison B S hS X.1 X.2 ∧
        e.inverse =
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X.1 X.2).O)))).ι ⋙ RQ :=
  ⟨quasicoherentDerivedEquivalenceOfIsAffineHomDiag B S hS X hZ hXqc hXdiag CF adjF RQ RQUnit,
    quasicoherentDerivedEquivalenceOfIsAffineHomDiag_functor B S hS X hZ hXqc hXdiag CF adjF RQ
      RQUnit,
    quasicoherentDerivedEquivalenceOfIsAffineHomDiag_inverse B S hS X hZ hXqc hXdiag CF adjF RQ
      RQUnit⟩

end AffineDiagonal

end AlgebraicGeometry.Space

end
