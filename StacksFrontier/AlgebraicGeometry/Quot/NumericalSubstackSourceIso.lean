module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProductsBaseChange

/-!
# `Coh^P_{X/Y}` along an isomorphism of the source over `Y`

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces, the standing data of
Stacks 08KB, and let `e : X' ≅ X` be an isomorphism of algebraic spaces with `f' = e ≫ f`.  For a
test scheme `T` over `Y` the base changes `X'_T` and `X_T` are identified by the isomorphism
`e_T : X'_T ≅ X_T` induced by `e`, and an object `(T, 𝓕)` of `Coh_{X'/Y}` gives the object
`(T, (e_T⁻¹)^*𝓕)` of `Coh_{X/Y}` with the same test scheme; a morphism of `Coh_{X'/Y}` gives a
morphism of `Coh_{X/Y}` with the same morphism of test schemes.  Consequently a condition on
`Coh_{X'/Y}` which agrees object by object with an open and closed condition on `Coh_{X/Y}` is
open and closed.

For perfect objects `E_1, …, E_r` of `D(𝒪_X)` the numerical invariants of Stacks 0DNE of
`(T, 𝓕)` for the perfect objects `Le^*E_j` on `X'` are those of `(T, (e_T⁻¹)^*𝓕)` for the `E_j`:
the objects `K_n` agree up to isomorphism.  So if `Coh^P_{X/Y} ⊆ Coh_{X/Y}` is open and closed,
so is `Coh^P_{X'/Y} ⊆ Coh_{X'/Y}`.  In the proof of Stacks 0DNE this identifies the given
morphism `X ⟶ B` with the base change `X_i ×_{Spec Λ_i} Spec Λ` of its Noetherian model.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.numericalDirectImageSourceIsoIso`: `K_n ≅ K_n'`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition.of_sourceIso`: open and
  closed conditions are transported along the isomorphism.
* `AlgebraicGeometry.Space.NumericalSituation.hasNumericalInvariants_sourceIso_iff` and
  `AlgebraicGeometry.Space.NumericalSituation.isOpenAndClosedCondition_sourceIso`.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable {D : CoherentSituation B S hS} {X' : AlgebraicSpaces B S hS} {f' : X' ⟶ D.Y}
  (hf' : IsFinitePresentation B S hS f'.hom) (e : X' ≅ D.X) (he : e.hom ≫ D.f = f')
  (hst : ModulePullbackStabilityOfFinitePresentation B S hS)

/-- **Open and closed conditions are transported along an isomorphism of the source.**  If a
condition `Q'` on `Coh_{X'/Y}` agrees, object by object, with an open and closed condition `Q` on
`Coh_{X/Y}` evaluated at the transported object, then `Q'` is open and closed. -/
theorem IsOpenAndClosedCondition.of_sourceIso {Q : CoherentObject D → Prop}
    (hQ : IsOpenAndClosedCondition D Q)
    {Q' : CoherentObject (isoSituation D f' hf') → Prop}
    (hQQ' : ∀ A, Q' A ↔ Q (isoObject hf' e he hst A)) :
    IsOpenAndClosedCondition (isoSituation D f' hf') Q' := by
  intro A
  obtain ⟨U, hU, h⟩ := hQ (isoObject hf' e he hst A)
  exact ⟨U, hU, fun A' φ => (hQQ' A').trans (h _ (isoHom hf' e he hst φ))⟩

end CoherentSituation

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

namespace NumericalSituation

open CoherentSituation

variable {D : CoherentSituation B S hS} {X' : AlgebraicSpaces B S hS} {f' : X' ⟶ D.Y}
  (hf' : IsFinitePresentation B S hS f'.hom) (e : X' ≅ D.X) (he : e.hom ≫ D.f = f')
  (hs : IsSeparated B S hS D.f.hom) (hs' : IsSeparated B S hS f'.hom)
  {r : ℕ} (E : Fin r → @DerivedCategory (Modules.{u, u} B S hS D.X.1 D.X.2) _ _
    (HasDerivedCategory.standard _))
  (hE : ∀ j, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
    (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E j))
  (P : (Fin r → ℤ) → ℤ)

/-- The perfect objects `Le^*E_j` on `X'`. -/
abbrev sourceIsoObjects :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
    Fin r → @DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2) _ _
      (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  fun j => (smallEtaleDerivedModulePullback B S hS e.hom).obj (E j)

omit hf' he in
include hE in
/-- The objects `Le^*E_j` are perfect (Stacks 08H6). -/
theorem isPerfect_sourceIsoObjects (j : Fin r) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
    (smallEtaleRingedSite B S hS X'.1 X'.2).IsPerfect (sourceIsoObjects e E j) :=
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  isPerfect_smallEtaleDerivedModulePullback _ _ (hE j)

/-- **The objects `(E^{⊗ n})_T ⊗^𝐋 𝓕` along the comparison `e_T`**: the object on `X'_T` for the
perfect objects `Le^*E_j` is the derived pullback along `e_T` of the object on `X_T` for the
transported object and the perfect objects `E_j`. -/
def numericalTensorSourceIsoIso (A : CoherentObject (isoSituation D f' hf'))
    (n : Fin r → ℤ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (baseChangeSpace f' A.T).1 (baseChangeSpace f' A.T).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
    (ofDerivedTensorPowerProducts (D := isoSituation D f' hf') hs' (sourceIsoObjects e E)
        (isPerfect_sourceIsoObjects e E hE) P).numericalTensor A n ≅
      (smallEtaleDerivedModulePullback B S hS (isoSpaceIso e he A.T).hom).obj
        ((ofDerivedTensorPowerProducts hs E hE P).numericalTensor
          (isoObject hf' e he (modulePullbackStabilityOfFinitePresentation B S hS) A) n) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (baseChangeSpace f' A.T).1 (baseChangeSpace f' A.T).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
  let ι := isoSpaceIso e he A.T
  let eE : (smallEtaleDerivedModulePullback B S hS (baseChangeProjection f' A.T)).obj
        (derivedTensorPowerProduct B S hS _ _ (sourceIsoObjects e E) n) ≅
      (smallEtaleDerivedModulePullback B S hS ι.hom).obj
        ((smallEtaleDerivedModulePullback B S hS (baseChangeProjection D.f A.T)).obj
            (derivedTensorPowerProduct B S hS _ _ E n)) :=
    (smallEtaleDerivedModulePullback B S hS (baseChangeProjection f' A.T)).mapIso
        (smallEtaleDerivedModulePullbackDerivedTensorPowerProductIso e.hom E hE n).symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _ ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (isoSpaceIso_hom_projection e he A.T).symm).app _ ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _).symm
  ((smallEtaleDerivedTensor B S hS (baseChangeSpace f' A.T)).mapIso eE).app _ ≪≫
    ((smallEtaleDerivedTensor B S hS (baseChangeSpace f' A.T)).obj _).mapIso
      (smallEtaleDerivedModulePullbackSingleInvIsoOfIso ι A.F).symm ≪≫
    ((smallEtaleDerivedPullbackTensorIso ι.hom).app (_, _)).symm

/-- **`K_n ≅ K_n'`** along an isomorphism of the source: the object `K_n` of `(T, 𝓕)` for the
perfect objects `Le^*E_j` is isomorphic to the object `K_n` of `(T, (e_T⁻¹)^*𝓕)` for the `E_j`. -/
def numericalDirectImageSourceIsoIso (A : CoherentObject (isoSituation D f' hf'))
    (n : Fin r → ℤ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (baseChangeSpace f' A.T).1 (baseChangeSpace f' A.T).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
    (ofDerivedTensorPowerProducts (D := isoSituation D f' hf') hs' (sourceIsoObjects e E)
        (isPerfect_sourceIsoObjects e E hE) P).numericalDirectImage A n ≅
      (ofDerivedTensorPowerProducts hs E hE P).numericalDirectImage
        (isoObject hf' e he (modulePullbackStabilityOfFinitePresentation B S hS) A) n :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (baseChangeSpace f' A.T).1 (baseChangeSpace f' A.T).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
  (Stacks.DerivedFunctor.totalRightDerived
      (modulePushforward B S hS ((isoSituation D f' hf').projection A.T))).mapIso
      (numericalTensorSourceIsoIso hf' e he hs hs' E hE P A n) ≪≫
    (eqToIso (congrArg (fun k => (Stacks.DerivedFunctor.totalRightDerived
      (modulePushforward B S hS k) : DerivedCategory (Modules.{u, u} B S hS
        (baseChangeSpace f' A.T).1 (baseChangeSpace f' A.T).2) ⥤
          DerivedCategory (Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1
            ((schemeSpaceFunctor B S hS).obj A.T.left).2)))
      (isoSpaceIso_hom_inclusion e he A.T).symm)).app _ ≪≫
    derivedModulePushforwardCompPullbackIsoOfIso (isoSpaceIso e he A.T)
      (D.projection A.T) _

/-- **The numerical invariants agree along an isomorphism of the source.** -/
theorem numericalEuler_sourceIso (A : CoherentObject (isoSituation D f' hf'))
    (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts (D := isoSituation D f' hf') hs' (sourceIsoObjects e E)
        (isPerfect_sourceIsoObjects e E hE) P).numericalEuler A n =
      (ofDerivedTensorPowerProducts hs E hE P).numericalEuler
        (isoObject hf' e he (modulePullbackStabilityOfFinitePresentation B S hS) A) n :=
  derivedFibreEuler_congr _ (numericalDirectImageSourceIsoIso hf' e he hs hs' E hE P A n)

/-- **`Coh^P_{X'/Y}` is the inverse image of `Coh^P_{X/Y}`** along an isomorphism of the
source. -/
theorem hasNumericalInvariants_sourceIso_iff (A : CoherentObject (isoSituation D f' hf')) :
    (ofDerivedTensorPowerProducts (D := isoSituation D f' hf') hs' (sourceIsoObjects e E)
        (isPerfect_sourceIsoObjects e E hE) P).HasNumericalInvariants A ↔
      (ofDerivedTensorPowerProducts hs E hE P).HasNumericalInvariants
        (isoObject hf' e he (modulePullbackStabilityOfFinitePresentation B S hS) A) := by
  refine forall_congr' fun n => forall_congr' fun t => ?_
  rw [numericalEuler_sourceIso hf' e he hs hs' E hE P A n]
  rfl

include he in
/-- **Open-and-closedness of `Coh^P` is transported along an isomorphism of the source.** -/
theorem isOpenAndClosedCondition_sourceIso
    (h : IsOpenAndClosedCondition D
      (ofDerivedTensorPowerProducts hs E hE P).HasNumericalInvariants) :
    IsOpenAndClosedCondition (isoSituation D f' hf')
      (ofDerivedTensorPowerProducts (D := isoSituation D f' hf') hs' (sourceIsoObjects e E)
        (isPerfect_sourceIsoObjects e E hE) P).HasNumericalInvariants :=
  h.of_sourceIso hf' e he (modulePullbackStabilityOfFinitePresentation B S hS)
    (hasNumericalInvariants_sourceIso_iff hf' e he hs hs' E hE P)

end NumericalSituation

end AlgebraicGeometry.Space

end
