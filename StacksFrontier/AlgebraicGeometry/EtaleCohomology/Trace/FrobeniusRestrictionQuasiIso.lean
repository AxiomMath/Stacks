module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalTraceFormula

/-!
# `T''` only depends on the complex up to quasi-isomorphism

For a quasi-isomorphism `φ : C ⟶ C'` of bounded below complexes of sheaves of `Λ`-modules on a
scheme `Y` over a finite field, `RΓ(Y_k̄, C|_{Y_k̄}) ≅ RΓ(Y_k̄, C'|_{Y_k̄})` compatibly with the
canonical geometric Frobenius, restriction to `Y_k̄` being exact. So one complex is perfect exactly
when the other is, with the same trace `T''`. The morphism is taken on the underlying complexes,
the form in which base change quasi-isomorphisms are produced in the proof of
[Stacks, Tag 03V3]; `Stacks.EtaleCohomology.cohomologicalTraceFormula_iff_of_quasiIso` is the
corresponding statement for the whole trace formula.

The standard model `HasDerivedCategory.standard` is used because the traced objects are defined
there.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso`.
* `Stacks.EtaleCohomology.isPerfect_frobeniusRestriction_of_quasiIso`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

omit [Fintype k] [IsAlgClosed kbar] in
/-- A quasi-isomorphism of bounded below complexes becomes an isomorphism of `D⁺(Y_k̄)` after
restriction to `Y_k̄`. -/
theorem isIso_fieldBaseChangeRestrictionFunctor_map (Y : Over (Spec (.of k)))
    {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : C ⟶ C') (hφ : QuasiIso φ.hom) :
    IsIso ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ) := by
  let ψ :=
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map φ
  have : QuasiIso ψ.hom :=
    inferInstanceAs (QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom))
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ψ)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 ‹_›
  change IsIso (DerivedCategory.Plus.Q.map ψ)
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

omit [IsAlgClosed kbar] [CharP kbar p] in
/-- **`T''` transports along a quasi-isomorphism**: if `RΓ(Y_k̄, C|_{Y_k̄})` is perfect, so is
`RΓ(Y_k̄, C'|_{Y_k̄})`, and the canonical geometric Frobenius endomorphisms have the same
trace. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso
    {Y : Over (Spec (.of k))} {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)}
    (φ : C.obj ⟶ C'.obj) (hφ : QuasiIso φ)
    (hp : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar C))))) :
    ∃ hp' : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar C')))),
      perfectDerivedTrace.{0, u + 1} Λ ⟨_, hp⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard C)) =
        perfectDerivedTrace.{0, u + 1} Λ ⟨_, hp'⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard C')) := by
  let φp : C ⟶ C' := ObjectProperty.homMk φ
  have := isIso_fieldBaseChangeRestrictionFunctor_map Λ kbar Y φp hφ
  let E := (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
      (asIso ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φp)))
  have hp' := StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso E).symm hp
  refine ⟨hp',
    perfectDerivedTrace_congr Λ ⟨_, hp⟩ ⟨_, hp'⟩ (DerivedCategory.Plus.ι.mapIso E) _ _ ?_⟩
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Plus.ι.map
    (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) Y kbar p q hcard φp).symm

omit [Fintype k] [IsAlgClosed kbar] in
/-- **Perfectness of `RΓ(Y_k̄, -)` descends along a quasi-isomorphism.** -/
theorem isPerfect_frobeniusRestriction_of_quasiIso {Y : Over (Spec (.of k))}
    {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : C.obj ⟶ C'.obj)
    (hφ : QuasiIso φ)
    (hp' : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar C'))))) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar C)))) := by
  have := isIso_fieldBaseChangeRestrictionFunctor_map Λ kbar Y (ObjectProperty.homMk φ) hφ
  exact StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (asIso ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map
          (ObjectProperty.homMk φ)))))) hp'

end Stacks.EtaleCohomology

end
