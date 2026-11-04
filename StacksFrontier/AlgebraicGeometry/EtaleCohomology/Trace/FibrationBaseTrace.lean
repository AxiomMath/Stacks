module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperFibrationTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectImageSectionsRestrictScalarsUnit

/-!
# The base of a fibration in the proof of the trace formula

In the proof of [Stacks, Tag 03V3] by fibration into curves, the base of the fibration is an open
`A` of a proper scheme `P` over the finite field `k`, the total space a proper `X̄' ⟶ P`, and the
coefficient complex `b_! L` is extended by zero from the preimage `X̄'_A` of `A`. Proper base
change along the open immersion `i : A ⟶ P` (the open immersion case of [Stacks, Tag 0F7B],
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper`) gives
`R f̄_* b_! L ≅ i_! R f'_* L`, so the trace formula on `P` for `f̄_* T` (`T` an injective
resolution of `b_! L`) is the trace formula on `P` for `i_! f'_* T_A` (`T_A` an injective
resolution of `L`), an object extended by zero from `A`.

The trace formula only depends on the class of a complex in the derived category
(`Stacks.EtaleCohomology.cohomologicalTraceFormula_iff_of_Q_iso`): an isomorphism in the derived
category is a zigzag of quasi-isomorphisms through a complex of injectives
(`CochainComplex.exists_quasiIso_zigzag_of_Q_iso`).

The standard model `HasDerivedCategory.standard` is used because the traced objects are defined
there.

## Main results

* `Stacks.EtaleCohomology.hasPerfectStalks_iff_of_Q_iso`,
  `Stacks.EtaleCohomology.cohomologicalTraceFormula_iff_of_Q_iso`.
* `Stacks.EtaleCohomology.directImageExtensionByZeroResolutionIso`: `Q(f̄_* T) ≅ Q(i_! f'_* T_A)`.
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_directImage_of_isPullback`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

section QIso

omit [Finite Λ] in
/-- **Perfect stalks only depend on the class in the derived category.** -/
theorem hasPerfectStalks_iff_of_Q_iso {X : Scheme.{u}}
    {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)}
    (e : DerivedCategory.Q.obj C.obj ≅ DerivedCategory.Q.obj C'.obj) :
    HasPerfectStalks Λ C ↔ HasPerfectStalks Λ C' := by
  have := etaleModules_enoughInjectives.{u, 0} Λ X
  obtain ⟨I, s, t, _, _⟩ := CochainComplex.exists_quasiIso_zigzag_of_Q_iso C C' e
  exact (hasPerfectStalks_iff_of_quasiIso s).trans (hasPerfectStalks_iff_of_quasiIso t).symm

omit [Finite Λ] in
/-- **The trace formula only depends on the class in the derived category**: for bounded below
complexes `C`, `C'` on a scheme `Y` over `k` with `Q(C) ≅ Q(C')`, `T''(Y, C) = T'(Y, C)` exactly
when `T''(Y, C') = T'(Y, C')`. -/
theorem cohomologicalTraceFormula_iff_of_Q_iso {Y : Over (Spec (.of k))}
    {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)}
    (e : DerivedCategory.Q.obj C.obj ≅ DerivedCategory.Q.obj C'.obj)
    (hC : HasPerfectStalks Λ C) (hC' : HasPerfectStalks Λ C') :
    CohomologicalTraceFormula Λ kbar p q hcard Y C hC ↔
      CohomologicalTraceFormula Λ kbar p q hcard Y C' hC' := by
  have := etaleModules_enoughInjectives.{u, 0} Λ Y.left
  obtain ⟨I, s, t, _, _⟩ := CochainComplex.exists_quasiIso_zigzag_of_Q_iso C C' e
  have hI := (hasPerfectStalks_iff_of_quasiIso s).1 hC
  exact (cohomologicalTraceFormula_iff_of_quasiIso kbar p q hcard s hC hI).trans
    (cohomologicalTraceFormula_iff_of_quasiIso kbar p q hcard t hC' hI).symm

end QIso

section Base

variable {Y : Over (Spec (.of k))} {Ts A Pa : Scheme.{u}} (fb : Ts ⟶ Y.left) [IsProper fb]
  (i : A ⟶ Y.left) [IsOpenImmersion i] (b : Pa ⟶ Ts) [IsOpenImmersion b] (f' : Pa ⟶ A)

omit [Finite Λ] in
/-- `DerivedCategory.Plus.Q` inverts quasi-isomorphisms. -/
theorem isIso_plusQ_map_of_quasiIso {X : Scheme.{u}}
    {M N : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (φ : M ⟶ N) (hφ : QuasiIso φ.hom) :
    IsIso (DerivedCategory.Plus.Q.map φ) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map φ)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ φ.hom).2 hφ
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

/-- **`Q(f̄_* T) ≅ Q(i_! f'_* T_A)`** for a cartesian square `b ≫ f̄ = f' ≫ i` with `f̄` proper and
`i`, `b` open immersions, an injective resolution `T` of `b_! L` and an injective resolution `T_A`
of `L`: `R f̄_* b_! L ≅ i_! R f'_* L` (the open immersion case of [Stacks, Tag 0F7B]), the
extensions by zero being exact and the direct images computed on injectives. -/
def directImageExtensionByZeroResolutionIso (sq : IsPullback b f' fb i)
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ Pa))
    (T : CochainComplex.Plus (EtaleModules.{u, 0} Λ Ts))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ b).mapCochainComplexPlus.obj L ⟶ T)
    (hψ : QuasiIso ψ.hom) (hT : ∀ n, Injective (T.obj.X n))
    (TA : CochainComplex.Plus (EtaleModules.{u, 0} Λ Pa)) (ψA : L ⟶ TA) (hψA : QuasiIso ψA.hom)
    (hTA : ∀ n, Injective (TA.obj.X n)) :
    DerivedCategory.Plus.Q.obj ((etaleModuleDirectImage.{u, 0} Λ fb).mapCochainComplexPlus.obj T) ≅
      DerivedCategory.Plus.Q.obj ((etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ f').mapCochainComplexPlus.obj TA)) :=
  haveI := etaleModules_enoughInjectives.{u, 0} Λ Ts
  haveI := etaleModules_enoughInjectives.{u, 0} Λ Pa
  haveI := etaleModules_enoughInjectives.{u, 0} Λ A
  haveI := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleDirectImage.{u, 0} Λ fb) T
    (fun n => have := hT n; Functor.rightAcyclic_of_injective _ _)
  haveI := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleDirectImage.{u, 0} Λ f') TA
    (fun n => have := hTA n; Functor.rightAcyclic_of_injective _ _)
  haveI := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleExtensionByZero.{u, 0} Λ b) L (fun _ => Functor.rightAcyclic_of_exact _ _)
  haveI := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleExtensionByZero.{u, 0} Λ i)
    ((etaleModuleDirectImage.{u, 0} Λ f').mapCochainComplexPlus.obj TA)
    (fun _ => Functor.rightAcyclic_of_exact _ _)
  haveI := isIso_plusQ_map_of_quasiIso Λ ψ hψ
  haveI := isIso_plusQ_map_of_quasiIso Λ ψA hψA
  asIso ((etaleModuleDirectImage.{u, 0} Λ fb).mapCochainComplexPlusDerivedUnit.app T) ≪≫
    (etaleModuleDerivedDirectImage.{u, 0} Λ fb).mapIso
      ((asIso (DerivedCategory.Plus.Q.map ψ)).symm ≪≫
        asIso ((etaleModuleExtensionByZero.{u, 0} Λ b).mapCochainComplexPlusDerivedUnit.app L)) ≪≫
    (etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper Λ fb i b f' sq).app
      ⟨DerivedCategory.Plus.Q.obj L, isTorsionPlus_of_finite Λ Pa _⟩ ≪≫
    (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ f').mapIso (asIso (DerivedCategory.Plus.Q.map ψA)) ≪≫
        (asIso ((etaleModuleDirectImage.{u, 0} Λ
          f').mapCochainComplexPlusDerivedUnit.app TA)).symm) ≪≫
    (asIso ((etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlusDerivedUnit.app
      ((etaleModuleDirectImage.{u, 0} Λ f').mapCochainComplexPlus.obj TA))).symm

/-- **The trace formula on the base of a fibration.** In the situation of
`Stacks.EtaleCohomology.directImageExtensionByZeroResolutionIso`, if `f'_* T_A` has perfect stalks
and `T''(Y, i_! f'_* T_A) = T'(Y, i_! f'_* T_A)`, then `f̄_* T` has perfect stalks and
`T''(Y, f̄_* T) = T'(Y, f̄_* T)`. -/
theorem cohomologicalTraceFormula_directImage_of_isPullback (sq : IsPullback b f' fb i)
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ Pa))
    (T : CochainComplex.Plus (EtaleModules.{u, 0} Λ Ts))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ b).mapCochainComplexPlus.obj L ⟶ T)
    (hψ : QuasiIso ψ.hom) (hT : ∀ n, Injective (T.obj.X n))
    (TA : CochainComplex.Plus (EtaleModules.{u, 0} Λ Pa)) (ψA : L ⟶ TA) (hψA : QuasiIso ψA.hom)
    (hTA : ∀ n, Injective (TA.obj.X n))
    (hDA : HasPerfectStalks Λ ((etaleModuleDirectImage.{u, 0} Λ f').mapCochainComplexPlus.obj TA))
    (h : CohomologicalTraceFormula Λ kbar p q hcard Y
      ((etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ f').mapCochainComplexPlus.obj TA))
      (hasPerfectStalks_extensionByZero Λ i _ hDA)) :
    ∃ hD : HasPerfectStalks Λ ((etaleModuleDirectImage.{u, 0} Λ fb).mapCochainComplexPlus.obj T),
      CohomologicalTraceFormula Λ kbar p q hcard Y
        ((etaleModuleDirectImage.{u, 0} Λ fb).mapCochainComplexPlus.obj T) hD := by
  let e := DerivedCategory.Plus.ι.mapIso
    (directImageExtensionByZeroResolutionIso Λ fb i b f' sq L T ψ hψ hT TA ψA hψA hTA)
  have hD := (hasPerfectStalks_iff_of_Q_iso Λ e).2 (hasPerfectStalks_extensionByZero Λ i _ hDA)
  exact ⟨hD, (cohomologicalTraceFormula_iff_of_Q_iso Λ kbar p q hcard e hD _).2 h⟩

end Base

end Stacks.EtaleCohomology

end
