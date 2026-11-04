module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.NoetherianExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.NoetherianDerivedEquivalence

/-!
# The derived category of quasi-coherent modules on a Noetherian algebraic space

**[Stacks, Tag 09TN]**: on a Noetherian algebraic space `X` the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 08F1] is an equivalence with quasi-inverse
`RQ_X`.  As in the source, the proof combines Lemmas 09TM and 09TG: for an étale `j : V ⟶ W`
with `V` affine and `W ⊆ X` a quasi-compact open, `V` and `W` are Noetherian, so by
[Stacks, Tag 09TM] the derived direct image along `j` is computed by `j_*` on K-injective
complexes of quasi-coherent modules, which is the hypothesis of [Stacks, Tag 09TG]; the two
clauses of [Stacks, Tag 09TG] then give the equivalence and identify its quasi-inverse.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedComparison_isEquivalence_of_isNoetherian` —
  **[Stacks, Tag 09TN], the equivalence**: on a Noetherian algebraic space the comparison
  functor `i_X` of Stacks 08F1 is an equivalence.
* `exists_equivalence_functor_eq_and_inverse_eq_derivedCoherator_of_isNoetherian` —
  **[Stacks, Tag 09TN], the quasi-inverse**: there is an equivalence whose functor is `i_X` and
  whose inverse is `RQ_X` on `D_QCoh(𝒪_X)`, for every coherator `C_X` and every total right
  derived functor `RQ_X` of it.
* `AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsNoetherian` — that equivalence,
  as data: its functor is `i_X`
  (`AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsNoetherian_functor`) and its
  inverse is `RQ_X` on `D_QCoh(𝒪_X)`
  (`AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsNoetherian_inverse`).
* `AlgebraicGeometry.Space.derivedPushforwardComputedOnKInjectives_of_isNoetherian` — Stacks
  09TM read on K-injective complexes of quasi-coherent modules.

## Implementation notes

The statements are about a bundled algebraic space `X : AlgebraicSpaces B S hS`, at the module
universe of the schemes and in the standard model of the derived categories, which is where the
comparison functor of Stacks 08F1 and the two clauses of Stacks 09TG are stated.  For a
bundled space the closure of quasi-coherence under kernels and cokernels, which the comparison
functor needs, are instances, so `quasicoherentDerivedComparison B S hS X.1 X.2` is the tagged
comparison `AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse` with no
binder.  Noetherianity is `AlgebraicGeometry.Space.IsNoetherian` (Stacks 03EA), which needs the
terminal scheme `hZ` in the site because quasi-separatedness is taken over `Spec ℤ`.

The coherator and `RQ_X` are arbitrary, as in the source's "the" right adjoint and "the" right
derived functor; the additivity of the coherator, which its derived functor needs, is read off
its adjunction (`CategoryTheory.Adjunction.right_adjoint_additive`) inside the statement rather
than asked for.  That such data exist is
`AlgebraicGeometry.Space.exists_coheratorAdjunction_smallEtale` and
`AlgebraicGeometry.Space.exists_rightDerivedCoherator`.

`SheafOfModules.instAbelian` is raised and the chaotic-comparison model of the derived category
of modules is removed locally, so that the derived categories of modules are elaborated at the
standard model in which Stacks 09TG and Stacks 09TM are stated.

## References

* [Stacks Project, Tag 09TN](https://stacks.math.columbia.edu/tag/09TN)
* [Stacks Project, Tag 09TM](https://stacks.math.columbia.edu/tag/09TM)
* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### Stacks 09TN -/

section Equivalence

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)

/-- **[Stacks, Tag 09TM], read on K-injective complexes.**  For a morphism `j : V ⟶ W` of
Noetherian algebraic spaces, every right derived functor `Rj_*` of the direct image of all modules
is computed by `j_*` on the K-injective complexes of quasi-coherent `𝒪_V`-modules. -/
theorem derivedPushforwardComputedOnKInjectives_of_isNoetherian {V W : AlgebraicSpaces B S hS}
    (hV : IsNoetherian B S hS hZ V.1) (hW : IsNoetherian B S hS hZ W.1) (j : V ⟶ W)
    (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor βj
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ))) :
    DerivedPushforwardComputedOnKInjectives B S hS j Rj βj := by
  intro I hI
  have h := fun K => NatTrans.isIso_app_iff_of_iso βj
    (((quasicoherentSheavesι B S hS V).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)
  exact (h I).1 <| isIso_app_quotient_quasicoherentSheaves_of_isKInjective_of_termwise_injective
    B S hS V (Functor.whiskerLeft
      ((quasicoherentSheavesι B S hS V).mapHomotopyCategory (ComplexShape.up ℤ)) βj)
    (fun K hK => (h K).2 (isIso_app_quotient_of_termwise_injective_of_isNoetherian B S hS hZ hV hW
      j Rj βj K hK)) I hI

include hN in
/-- **[Stacks, Tag 09TN], the equivalence.**  Let `X` be a Noetherian algebraic space over `S`.
Then the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an
equivalence. -/
@[stacks 09TN "equivalence"]
theorem quasicoherentDerivedComparison_isEquivalence_of_isNoetherian :
    (quasicoherentDerivedComparison B S hS X.1 X.2).IsEquivalence :=
  quasicoherentDerivedComparison_isEquivalence_of_affineEtaleDerivedPushforwardSquareCommutes
    B S hS X hZ hN.1 hN.2.1
    (affineEtaleDerivedPushforwardSquareCommutes_of_isNoetherian_of_computedOnKInjectives
      B S hS hZ X hN fun _ _ hV hW j Rj βj hRj =>
        derivedPushforwardComputedOnKInjectives_of_isNoetherian B S hS hZ hV hW j Rj βj hRj)

/-- **The equivalence of [Stacks, Tag 09TN], with inverse `RQ_X`.**  Let `X` be a Noetherian
algebraic space over `S`, `C_X` a coherator of `X` and `RQ_X` a total right derived functor of
it.  Then the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence with quasi-inverse `RQ_X`
restricted to `D_QCoh(𝒪_X)`: this is an equivalence whose functor is `i_X`
(`AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsNoetherian_functor`) and whose
inverse is `RQ_X` on `D_QCoh(𝒪_X)`
(`AlgebraicGeometry.Space.quasicoherentDerivedEquivalenceOfIsNoetherian_inverse`). -/
def quasicoherentDerivedEquivalenceOfIsNoetherian
    (CF : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ CF)
    (RQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (RQUnit : letI := adjF.right_adjoint_additive
      CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQ)
    (hRQ : letI := adjF.right_adjoint_additive
      RQ.IsRightDerivedFunctor RQUnit
        (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))) :
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ≌
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  let := adjF.right_adjoint_additive
  have := hRQ
  have := quasicoherentDerivedComparison_isEquivalence_of_isNoetherian B S hS hZ X hN
  (quasicoherentDerivedComparison B S hS X.1 X.2).asEquivalence.changeInverse
    (derivedCoherator_isoInv B S hS X.1 X.2 CF adjF RQ RQUnit).symm

section

variable (CF : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
  (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ CF)
  (RQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
  (RQUnit : letI := adjF.right_adjoint_additive
    CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⟶
    DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQ)
  (hRQ : letI := adjF.right_adjoint_additive
    RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)))

/-- The functor of the equivalence of Stacks 09TN is the comparison functor `i_X` of
Stacks 08F1. -/
lemma quasicoherentDerivedEquivalenceOfIsNoetherian_functor :
    (quasicoherentDerivedEquivalenceOfIsNoetherian B S hS hZ X hN CF adjF RQ RQUnit
      hRQ).functor = quasicoherentDerivedComparison B S hS X.1 X.2 :=
  rfl

/-- The inverse of the equivalence of Stacks 09TN is `RQ_X` on `D_QCoh(𝒪_X)`. -/
lemma quasicoherentDerivedEquivalenceOfIsNoetherian_inverse :
    (quasicoherentDerivedEquivalenceOfIsNoetherian B S hS hZ X hN CF adjF RQ RQUnit
      hRQ).inverse =
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))).ι ⋙
        RQ :=
  rfl


end

end Equivalence

/-! ### Stacks 09TN, the quasi-inverse -/

section QuasiInverse

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 09TN].**  Let `X` be a Noetherian algebraic space over `S`, `C_X` a coherator
of `X` and `RQ_X` a total right derived functor of it.  Then the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence with quasi-inverse `RQ_X`
restricted to `D_QCoh(𝒪_X)`: there is an equivalence whose functor is `i_X` and whose inverse is
`J ⋙ RQ_X`, for `J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` the inclusion. -/
@[stacks 09TN "equivalence with quasi-inverse RQ_X"]
theorem exists_equivalence_functor_eq_and_inverse_eq_derivedCoherator_of_isNoetherian
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (CF : Modules.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ CF)
    (RQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2))
    (RQUnit : letI := adjF.right_adjoint_additive
      CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2) ⋙ RQ)
    (hRQ : letI := adjF.right_adjoint_additive
      RQ.IsRightDerivedFunctor RQUnit
        (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))) :
    ∃ e : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ≌
        QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      e.functor = quasicoherentDerivedComparison B S hS X.1 X.2 ∧
        e.inverse =
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X.1 X.2).O)))).ι ⋙ RQ :=
  ⟨quasicoherentDerivedEquivalenceOfIsNoetherian B S hS hZ X hN CF adjF RQ RQUnit hRQ,
    quasicoherentDerivedEquivalenceOfIsNoetherian_functor B S hS hZ X hN CF adjF RQ RQUnit hRQ,
    quasicoherentDerivedEquivalenceOfIsNoetherian_inverse B S hS hZ X hN CF adjF RQ RQUnit hRQ⟩

end QuasiInverse

end AlgebraicGeometry.Space

end
