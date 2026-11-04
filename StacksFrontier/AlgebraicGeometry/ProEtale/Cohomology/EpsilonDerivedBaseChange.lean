module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.EpsilonBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SuccUniverseCoefficients
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional

/-!
# The pro-étale base change map at a torsion sheaf coming from the étale site

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` proper. For a torsion abelian sheaf `𝒢` on `X_étale`,
the base change map `g⁻¹ Rf_* ε⁻¹𝒢 ⟶ Rf'_* (g')⁻¹ ε⁻¹𝒢` of pro-étale abelian sheaves is an
isomorphism. Indeed, at a bounded below complex `I` of injective abelian sheaves on `X_étale`, the
pro-étale base change map at `ε⁻¹I` is `ε⁻¹` of the étale base change map at `I`
(`AlgebraicGeometry.ProEtale.epsilon_baseChange_cube`), because `ε⁻¹` of an injective sheaf is
acyclic for the pro-étale direct image along a quasi-compact quasi-separated morphism
(Stacks 09A6); and the étale base change map at a torsion sheaf is an isomorphism by the proper
base change theorem (Stacks 095T).

## Main results

* `AlgebraicGeometry.ProEtale.isIso_proetaleAbelianDerivedBaseChange_app_epsilon_iff`.
* `AlgebraicGeometry.ProEtale.isIso_proetaleAbelianDerivedBaseChange_app_singleFunctor_epsilon`.

Standard model: uses `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`, which exists only
there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasSheafify_proetale_addCommGrpCat_succ
  isGrothendieckAbelian_proetale_ab_succ enoughInjectives_proetale_ab_succ

/-- The category of sheaves of `AddCommGrpCat.{u + 1}` on the small étale site of `X` is a
Grothendieck abelian category. -/
local instance isGrothendieckAbelian_etale_ab₄ (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X

/-- The category of sheaves of `AddCommGrpCat.{u + 1}` on the small étale site of `X` has enough
injectives. -/
local instance enoughInjectives_etale_ab₄ (X : Scheme.{u}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  enoughInjectives_sheaf_smallEtale.{u, 0} X

/-- The image under `ε⁻¹` of a bounded below complex of injective abelian sheaves on `X_étale`
computes the derived pro-étale direct image along a quasi-compact quasi-separated morphism
(Stacks 09A6 and Leray's acyclicity lemma). -/
theorem isIso_proetaleAbelianDerivedDirectImageUnit_app_epsilon {Z W : Scheme.{u}} (h : Z ⟶ W)
    [QuasiCompact h] [QuasiSeparated h]
    (I : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (n : ℤ)
    [I.IsStrictlyGE n] [∀ k, Injective (I.X k)] :
    IsIso ((proetaleAbelianDerivedDirectImageUnit h).app ((HomotopyCategory.quotient _ _).obj
      (((epsilonInverseImage.{u, 0} Z).mapHomologicalComplex _).obj I))) := by
  have := isStrictlyGE_mapHomologicalComplex_obj (epsilonInverseImage.{u, 0} Z) I n
  refine Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic (proetaleAbelianDirectImage h)
    (proetaleAbelianDerivedDirectImage h) (proetaleAbelianDerivedDirectImageUnit h) _ ⟨n, this⟩
    fun k => ?_
  exact rightAcyclic_epsilonInverseImage_of_isZero.{u, 0} h (I.X k) fun V hV q hq =>
    isZero_rightDerived_sheafSections_proetaleBaseChange_epsilonInverseImage.{u, 0} h (I.X k) V hV
      q hq

section BaseChange

/-- The étale derived direct image unit is invertible at a bounded below complex of injectives. -/
private theorem isIso_etaleAbelianDerivedDirectImageUnit_app_of_injective {A B : Scheme.{u}}
    (k : A ⟶ B) (K : CochainComplex (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (n : ℤ)
    [K.IsStrictlyGE n] [∀ i, Injective (K.X i)] :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, 0} k).app
      ((HomotopyCategory.quotient _ _).obj K)) :=
  Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (etaleAbelianPushforwardToDerivedCategory.{u, 0} k) DerivedCategory.Qh
    (etaleAbelianDerivedDirectImage.{u, 0} k) (etaleAbelianDerivedDirectImageUnit.{u, 0} k) K
    (CochainComplex.isKInjective_of_injective K n)

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']

/-- **The pro-étale base change map at `ε⁻¹I` is `ε⁻¹` of the étale base change map at `I`**,
for a bounded below complex `I` of injective abelian sheaves on `X_étale`: one is invertible if
and only if the other is. -/
theorem isIso_proetaleAbelianDerivedBaseChange_app_epsilon_iff
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (n : ℤ)
    [I.IsStrictlyGE n] [∀ k, Injective (I.X k)] :
    IsIso ((proetaleAbelianDerivedBaseChange f g f' g' h.symm).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
          (((epsilonInverseImage.{u, 0} X).mapHomologicalComplex _).obj I)))) ↔
      IsIso ((epsilonInverseImage.{u, 0} Y').mapDerivedCategory.map
        ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' h).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)))) := by
  rw [etaleAbelianDerivedBaseChange_eq_derivedBaseChangeMap]
  have := isStrictlyGE_mapHomologicalComplex_obj (etaleAbelianInverseImage.{u, 0} g') I n
  obtain ⟨J, t, ht, hJ, hJge⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
    (((etaleAbelianInverseImage.{u, 0} g').mapHomologicalComplex _).obj I) n
  exact Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_of_cube_of_isIso
    (etaleAbelianInverseImage.{u, 0} g') (etaleAbelianInverseImage.{u, 0} g)
    (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDirectImage.{u, 0} f')
    (etaleAbelianDerivedDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f')
    (etaleAbelianDerivedDirectImageUnit.{u, 0} f) (etaleAbelianDerivedDirectImageUnit.{u, 0} f')
    (etaleAbelianBaseChange.{u, 0} f g g' f' h)
    (proetaleAbelianInverseImage g') (proetaleAbelianInverseImage g)
    (proetaleAbelianDirectImage f) (proetaleAbelianDirectImage f')
    (proetaleAbelianDerivedDirectImage f) (proetaleAbelianDerivedDirectImage f')
    (proetaleAbelianDerivedDirectImageUnit f) (proetaleAbelianDerivedDirectImageUnit f')
    (proetaleAbelianBaseChange f g f' g' h.symm)
    (epsilonInverseImage.{u, 0} X) (epsilonInverseImage.{u, 0} X')
    (epsilonInverseImage.{u, 0} Y) (epsilonInverseImage.{u, 0} Y')
    (inv (epsilonInverseImageSquareInv g')) (epsilonInverseImageSquare g)
    (epsilonDirectImageComparison f).natTrans (inv (epsilonDirectImageComparison f').natTrans)
    (epsilon_baseChange_cube f g g' f' h) I
    (isIso_etaleAbelianDerivedDirectImageUnit_app_of_injective f I n)
    (isIso_proetaleAbelianDerivedDirectImageUnit_app_epsilon f I n) t
    (isIso_etaleAbelianDerivedDirectImageUnit_app_of_injective f' J n)
    (isIso_proetaleAbelianDerivedDirectImageUnit_app_epsilon f' J n)

end BaseChange

/-- **The pro-étale base change map at a torsion sheaf coming from the étale site.** For a
cartesian square with `f` proper and a torsion abelian sheaf `𝒢` on `X_étale`, the base change
map `g⁻¹ Rf_* ε⁻¹𝒢 ⟶ Rf'_* (g')⁻¹ ε⁻¹𝒢` of pro-étale abelian sheaves is an isomorphism: it is
`ε⁻¹` of the étale base change map at `𝒢`, computed on an injective resolution, which is an
isomorphism by the proper base change theorem (Stacks 095T). -/
theorem isIso_proetaleAbelianDerivedBaseChange_app_singleFunctor_epsilon
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) :
    IsIso ((proetaleAbelianDerivedBaseChange f g f' g' sq.w.symm).app
      ((DerivedCategory.singleFunctor _ 0).obj ((epsilonInverseImage.{u, 0} X).obj G))) := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq ‹_›
  obtain ⟨I, i, hi, hinj, hge⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
    ((CochainComplex.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj G) 0
  have : IsIso (DerivedCategory.Q.map i) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ i).2 hi
  let e₁ : (DerivedCategory.singleFunctor _ 0).obj G ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app G ≪≫ asIso (DerivedCategory.Q.map i) ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app I
  have het : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' sq.w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) :=
    (NatTrans.isIso_app_iff_of_iso _ e₁).1
      (isIso_etaleAbelianSheafDerivedBaseChange_of_isProper f g g' f' sq G hG)
  have : UniversallyClosed f := IsProper.toUniversallyClosed
  have : IsSeparated f := IsProper.toIsSeparated
  have : UniversallyClosed f' := IsProper.toUniversallyClosed
  have : IsSeparated f' := IsProper.toIsSeparated
  have : QuasiCompact f := AlgebraicGeometry.instQuasiCompactOfUniversallyClosed f
  have : QuasiSeparated f := AlgebraicGeometry.IsSeparated.instQuasiSeparated f
  have : QuasiCompact f' := AlgebraicGeometry.instQuasiCompactOfUniversallyClosed f'
  have : QuasiSeparated f' := AlgebraicGeometry.IsSeparated.instQuasiSeparated f'
  have hpro := (isIso_proetaleAbelianDerivedBaseChange_app_epsilon_iff f g g' f' sq.w I 0).2
    (Functor.map_isIso _ _)
  let e₂ : (DerivedCategory.singleFunctor _ 0).obj ((epsilonInverseImage.{u, 0} X).obj G) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((epsilonInverseImage.{u, 0} X).mapHomologicalComplex _).obj I)) :=
    ((epsilonInverseImage.{u, 0} X).mapDerivedCategorySingleFunctor 0).symm.app G ≪≫
      (epsilonInverseImage.{u, 0} X).mapDerivedCategory.mapIso e₁ ≪≫
      (epsilonInverseImage.{u, 0} X).mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ _).obj I)
  exact (NatTrans.isIso_app_iff_of_iso _ e₂).2 hpro


end AlgebraicGeometry.ProEtale

end
